(ns org.replikativ.spindel.effects.await
  "await effect - suspend until spin or deferred completes.

  Supports:
  - Spin: awaits completion, tracks dependency
  - Deferred: async callback-based suspension
  - SignalRef: error (use track instead)"
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.protocols :as rtp]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.impl.simple :as simple]
            [org.replikativ.spindel.spin.protocols :as tp]
            [org.replikativ.spindel.spin.continuation :as cont]
            [org.replikativ.spindel.spin.result :as result]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.effects.core :as eff]
            [org.replikativ.spindel.effects.track :as track]
            [org.replikativ.spindel.log :as log]
            [is.simm.partial-cps.async :as pcps-async])
  #?(:clj (:import [org.replikativ.spindel.spin.core Spin])))

;; =============================================================================
;; Public API Shim
;; =============================================================================

(defn await
  "Suspend until value available from spin or deferred.

  Must only be called inside a spin; outside, this throws."
  [& _]
  (throw (ex-info "await called outside of spin context (should be CPS-transformed)" {})))

;; =============================================================================
;; Direct Handler Implementations
;; =============================================================================

(defn- await-spin
  "Direct await handler for Spin.

  Fast path: If spin already completed, resolve immediately from cache.
  Slow path: Register continuation and start child spin.

  NOTE: In rebuild mode, we SKIP the fast path to ensure child spin bodies execute
  (for side effects like nested spin creation and continuation registration)."
  [^Spin spin-ref spin-id source-loc resolve reject]
  (let [awaited-spin-id (tp/spin-id spin-ref)
        noop (fn [& _] nil)
        ctx (rtc/current-execution-context)
        rebuild? (ctx/rebuild-mode? ctx)]

    ;; Track spin dependency
    (rtc/deps-track-spin! spin-id awaited-spin-id)

    ;; Check if spin value available via protocol
    (let [cached (rtc/spin-current-result awaited-spin-id)
          ;; CRITICAL: Disable fast path during batch mode to prevent glitches
          ;; UNLESS the spin has already been processed in this batch (cache is fresh)
          ;; Batch is now in context state, not dynamic binding
          batch (rtp/get-state ctx [:engine/current-batch])
          in-batch-mode? (some? batch)
          spin-processed? (when batch
                           (contains? @(:processed batch) awaited-spin-id))
          allow-fast-path? (and (some? cached)
                                (not rebuild?)
                                (not (simple/dirty? ctx awaited-spin-id))
                                (or (not in-batch-mode?)  ;; Not in batch - allow
                                    spin-processed?))]    ;; In batch but cache fresh - allow
      (cond
        ;; Fast path: Spin has result AND (not in batch OR spin already processed)
        allow-fast-path?
        (do
          ;; NEW: Record await dependency even on fast-path (Design 1)
          ;; Dependencies must be recorded for dirty propagation to work correctly
          (simple/record-await-dependency! ctx spin-id awaited-spin-id)
          (result/match cached
            #(cont/resume resolve %)
            #(cont/resume reject %)))

        ;; Rebuild mode: Execute child for side effects, then immediately resume with cached value
        ;; We need to execute child body (to create nested spins, register continuations)
        ;; but continue synchronously instead of suspending
        rebuild?
        (do
          ;; Execute child spin for side effects
          (spin-ref noop noop)
          (log/debug! {:event :await/rebuild-child-executed
                       :data {:parent-id spin-id :awaited-id awaited-spin-id}})
          ;; Get cached result (should exist after child execution)
          (let [child-cached (rtc/spin-current-result awaited-spin-id)]
            (if child-cached
              (result/match child-cached
                #(cont/resume resolve %)
                #(cont/resume reject %))
              ;; No cache? Shouldn't happen in rebuild mode
              (cont/resume reject
                (ex-info "No cached result for child in rebuild mode"
                         {:parent-id spin-id :child-id awaited-spin-id})))))

        ;; Normal slow path: Start child, check if completed synchronously
        :else
        (do
          ;; Try DIRECT execution of child's spin-fn (bypasses invoke overhead).
          ;; This avoids the full invoke machinery: cache writes, deps tracking,
          ;; enqueue-completion-event!, and trigger-drain! — none of which are needed
          ;; when the value is consumed inline by the parent.
          ;;
          ;; CRITICAL: Bind *in-trampoline* to false so the child's CPS function
          ;; creates its own trampoline and runs to completion.
          ;;
          ;; The resolve/reject callbacks handle BOTH sync and async completion:
          ;; - Always cache the result
          ;; - In async mode (after sync phase ends), also fire completion events
          ;;   so the parent's continuation gets resumed via the event queue
          (let [child-spin-fn (.-spin-fn ^Spin spin-ref)
                child-value (volatile! nil)
                child-error (volatile! nil)
                child-completed? (volatile! false)
                in-sync-phase (volatile! true)
                child-resolve (fn [v]
                                (vreset! child-value v)
                                (vreset! child-completed? true)
                                (rtc/spin-cache-result! awaited-spin-id (result/ok v))
                                ;; Commit deps so child registers as signal observer
                                (rtc/graph-commit-deps! awaited-spin-id)
                                (when-not @in-sync-phase
                                  ;; Async completion: fire event so parent continuation resumes
                                  (simple/enqueue-completion-event! ctx awaited-spin-id))
                                v)
                child-reject (fn [e]
                               (vreset! child-error e)
                               (vreset! child-completed? true)
                               (rtc/spin-cache-result! awaited-spin-id (result/error e))
                               (rtc/graph-commit-deps! awaited-spin-id)
                               (when-not @in-sync-phase
                                 (simple/enqueue-completion-event! ctx awaited-spin-id))
                               nil)
                _raw-result (binding [rtc/*spin-id* awaited-spin-id
                                      pcps-async/*in-trampoline* false]
                              (child-spin-fn child-resolve child-reject))]
            ;; End sync phase — any future callback invocation is async
            (vreset! in-sync-phase false)
            (cond
              ;; Synchronous completion — resume parent directly.
              ;; Cache already written by child-resolve/child-reject above.
              ;; Skip events/deps/drain (parent consumes value inline).
              @child-completed?
              (do
                (simple/record-await-dependency! ctx spin-id awaited-spin-id)
                (if @child-error
                  (cont/resume reject @child-error)
                  (cont/resume resolve @child-value)))

              ;; Async — child returned ::incomplete. Don't call invoke (would
              ;; double-execute). child-resolve/child-reject will fire completion
              ;; events when the child eventually completes.
              :else
              (do
                (let [is-reactive-spin (satisfies? tp/PSpin spin-ref)
                      cont-map {:event-key [:spin/complete awaited-spin-id]
                                :resolve-fn resolve
                                :reject-fn reject
                                :source-loc source-loc
                                :ephemeral-await? (not is-reactive-spin)
                                :on-resume (fn [_rt]
                                             (let [res (rtc/spin-current-result awaited-spin-id)]
                                               (result/match res identity identity)))}]
                  (rtc/continuation-add! spin-id cont-map)
                  (log/debug! {:event :await/registered-continuation
                               :data {:parent-id spin-id :awaited-id awaited-spin-id}})
                  (simple/record-await-dependency! ctx spin-id awaited-spin-id))
                spin-core/incomplete))))))))

(defn- await-deferred
  "Direct await handler for Deferred.

  Deferred implements IFn with 2-arity: (deferred resolve reject)
  Returns ::incomplete to suspend parent until deferred resolves."
  [deferred _spin-id _source-loc resolve reject]
  ;; Call the deferred, it will invoke resolve/reject when ready
  (deferred resolve reject)
  ;; Suspend parent
  spin-core/incomplete)

(defn reactive-spin?
  "Check if value is a Spin. Works across CLJ/CLJS."
  [x]
  (instance? #?(:clj Spin :cljs spin-core/Spin) x))

(defn await-handler
  "Unified direct await handler - dispatches based on type.

  This is the entry point called from CPS-transformed code.
  Handles Spin, Deferred, and errors for SignalRef."
  [awaitable spin-id source-loc resolve reject]
  (try
    ;; Check cancellation at await point
    (eff/check-cancellation! spin-id)

    ;; Type dispatch
    (cond
      (reactive-spin? awaitable)
      (await-spin awaitable spin-id source-loc resolve reject)

      ;; Check Deferred by class name (avoids circular dependency)
      (and awaitable
           (= "org.replikativ.spindel.spin.sync.Deferred"
              #?(:clj (.getName (class awaitable))
                 :cljs (.-name (type awaitable)))))
      (await-deferred awaitable spin-id source-loc resolve reject)

      ;; Check Mailbox by class name (avoids circular dependency)
      ;; Works like Deferred: mailbox calls cont/resume internally if message available
      (and awaitable
           (= "org.replikativ.spindel.spin.sync.Mailbox"
              #?(:clj (.getName (class awaitable))
                 :cljs (.-name (type awaitable)))))
      (do
        (awaitable resolve reject)
        spin-core/incomplete)

      ;; SignalRef is an error
      (track/signal-ref? awaitable)
      (reject (eff/type-error 'await "Spin or Deferred (use track for signals)" awaitable))

      ;; Plain function - treat as async thunk (e.g., from partial-cps async)
      ;; Simple passthrough - effect handlers inside async are responsible for
      ;; registering with spindel runtime if they need to suspend
      (ifn? awaitable)
      (awaitable resolve reject)

      :else
      (reject (eff/type-error 'await "Spin, Deferred, or async thunk" awaitable)))

    (catch #?(:clj Throwable :cljs js/Error) t
      (reject t))))

;; =============================================================================
;; Registration
;; =============================================================================

(eff/register-effect-by-symbol!
  'org.replikativ.spindel.effects.await/await
  ::await-handler
  'org.replikativ.spindel.effects.core/one-arg->awaitable-map
  'org.replikativ.spindel.effects.await/await-handler)
