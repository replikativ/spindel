(ns org.replikativ.spindel.effects.await
  "await effect - suspend until spin or deferred completes.

  Supports:
  - Spin: awaits completion, tracks dependency
  - Deferred: async callback-based suspension
  - SignalRef: error (use track instead)"
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.bindings :as bindings]
            [org.replikativ.spindel.runtime.impl.simple :as simple]  ;; For *completion-queue*
            [org.replikativ.spindel.spin.protocols :as tp]
            [org.replikativ.spindel.spin.continuation :as cont]
            [org.replikativ.spindel.spin.result :as result]
            [org.replikativ.spindel.spin.core :as spin-core]       ;; For Spin import
            [org.replikativ.spindel.state.signal :as sig]    ;; For SignalRef import
            [org.replikativ.spindel.effects.core :as eff]
            [org.replikativ.spindel.log :as log])
  #?(:clj (:import [org.replikativ.spindel.spin.core Spin]
                   [org.replikativ.spindel.state.signal SignalRef])))

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

(defn- rebuild-mode?
  "Check if current execution context is in rebuild mode."
  [context]
  (when (and context (map? context))
    (= :rebuild (get-in context [:bindings :execution-mode]))))

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
        rebuild? (rebuild-mode? ctx)]

    ;; Track spin dependency
    (rtc/deps-track-spin! spin-id awaited-spin-id)

    ;; Check if spin value available via protocol
    (let [cached (rtc/spin-current-result awaited-spin-id)
          ;; CRITICAL: Disable fast path during batch mode to prevent glitches
          ;; UNLESS the spin has already been processed in this batch (cache is fresh)
          in-batch-mode? (some? simple/*completion-queue*)
          spin-processed? (when-let [processed-set simple/*processed-spins*]
                           (contains? @processed-set awaited-spin-id))
          allow-fast-path? (and (some? cached)
                                (not rebuild?)
                                (not (simple/dirty? ctx awaited-spin-id))  ;; NEW: Check dirty flag
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

        ;; Normal slow path: Register continuation and start spin, then suspend
        :else
        (do
          ;; Register continuation for spin completion event
          ;; IMPORTANT: Capture bindings so they're restored when continuation resumes
          ;; This ensures dynamic vars like *yield-handler* are available after suspension
          ;;
          ;; For reactive spins (PSpin), mark continuation as persistent so it survives
          ;; signal-change boundaries. This allows combinators like `parallel` to notify
          ;; their awaiters when children update reactively.
          ;; For non-reactive spins (deferreds), mark as ephemeral.
          (let [captured-bindings (bindings/capture-bindings)
                is-reactive-spin (satisfies? tp/PSpin spin-ref)
                cont-map {:event-key [:spin/complete awaited-spin-id]
                          :resolve-fn resolve
                          :reject-fn reject
                          :source-loc source-loc
                          :bindings captured-bindings
                          ;; Reactive spins (like parallel) may update during batch processing
                          ;; Their awaiters need persistent continuations to receive updates
                          :ephemeral-await? (not is-reactive-spin)
                          :on-resume (fn [_rt]
                                       (let [res (rtc/spin-current-result awaited-spin-id)]
                                         (result/match res identity identity)))}]
            (rtc/continuation-add! spin-id cont-map)
            (log/debug! {:event :await/registered-continuation
                         :data {:parent-id spin-id :awaited-id awaited-spin-id}})

            ;; NEW: Record await dependency for dirty propagation (Design 1)
            ;; When child completes dirty, we'll propagate dirty flag to this parent
            (simple/record-await-dependency! ctx spin-id awaited-spin-id))

          ;; Start child spin (uses noop callbacks, parent resumes via continuation)
          (spin-ref noop noop)
          (log/debug! {:event :await/started-child
                       :data {:parent-id spin-id :awaited-id awaited-spin-id}})

          ;; Suspend parent until continuation resumes
          :org.replikativ.spindel.spin/incomplete)))))

(defn- await-deferred
  "Direct await handler for Deferred.

  Deferred implements IFn with 2-arity: (deferred resolve reject)
  Returns ::incomplete to suspend parent until deferred resolves."
  [deferred _spin-id _source-loc resolve reject]
  ;; Call the deferred, it will invoke resolve/reject when ready
  (deferred resolve reject)
  ;; Suspend parent
  :org.replikativ.spindel.spin/incomplete)

(defn reactive-spin?
  "Check if value is a Spin. Works across CLJ/CLJS."
  [x]
  (instance? #?(:clj Spin :cljs spin-core/Spin) x))

(defn signal-ref?
  "Check if value is a SignalRef. Works across CLJ/CLJS."
  [x]
  (instance? #?(:clj SignalRef :cljs sig/SignalRef) x))

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
        :org.replikativ.spindel.spin/incomplete)

      ;; SignalRef is an error
      (signal-ref? awaitable)
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
