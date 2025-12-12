(ns is.simm.spindel.effects.await
  "await effect - suspend until spin or deferred completes.

  Supports:
  - Spin: awaits completion, tracks dependency
  - Deferred: async callback-based suspension
  - SignalRef: error (use track instead)"
  (:refer-clojure :exclude [await])
  (:require [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.runtime.bindings :as bindings]
            [is.simm.spindel.spin.protocols :as tp]
            [is.simm.spindel.spin.continuation :as cont]
            [is.simm.spindel.spin.result :as result]
            [is.simm.spindel.spin.core :as spin-core]       ;; For Spin import
            [is.simm.spindel.state.signal :as sig]    ;; For SignalRef import
            [is.simm.spindel.effects.core :as eff]
            [is.simm.spindel.log :as log])
  #?(:clj (:import [is.simm.spindel.spin.core Spin]
                   [is.simm.spindel.state.signal SignalRef])))

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
    (let [cached (rtc/spin-current-result awaited-spin-id)]
      (cond
        ;; Fast path: Spin already has result AND not in rebuild mode
        (and (some? cached) (not rebuild?))
        (result/match cached
          #(cont/resume resolve %)
          #(cont/resume reject %))

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
          (let [captured-bindings (bindings/capture-bindings)
                cont-map {:event-key [:spin/complete awaited-spin-id]
                          :resolve-fn resolve
                          :reject-fn reject
                          :source-loc source-loc
                          :bindings captured-bindings
                          :on-resume (fn [_rt]
                                       (let [res (rtc/spin-current-result awaited-spin-id)]
                                         (result/match res identity identity)))}]
            (rtc/continuation-add! spin-id cont-map)
            (log/debug! {:event :await/registered-continuation
                         :data {:parent-id spin-id :awaited-id awaited-spin-id}}))

          ;; Start child spin (uses noop callbacks, parent resumes via continuation)
          (spin-ref noop noop)
          (log/debug! {:event :await/started-child
                       :data {:parent-id spin-id :awaited-id awaited-spin-id}})

          ;; Suspend parent until continuation resumes
          :is.simm.spindel.spin/incomplete)))))

(defn- await-deferred
  "Direct await handler for Deferred.

  Deferred implements IFn with 2-arity: (deferred resolve reject)
  Returns ::incomplete to suspend parent until deferred resolves."
  [deferred _spin-id _source-loc resolve reject]
  ;; Call the deferred, it will invoke resolve/reject when ready
  (deferred resolve reject)
  ;; Suspend parent
  :is.simm.spindel.spin/incomplete)

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
           (= "is.simm.spindel.spin.sync.Deferred"
              #?(:clj (.getName (class awaitable))
                 :cljs (.-name (type awaitable)))))
      (await-deferred awaitable spin-id source-loc resolve reject)

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
  'is.simm.spindel.effects.await/await
  ::await-handler
  'is.simm.spindel.effects.core/one-arg->awaitable-map
  'is.simm.spindel.effects.await/await-handler)
