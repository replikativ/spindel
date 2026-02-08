(ns org.replikativ.spindel.spin.core
  "Core Spin deftype - stateless spin execution"
  (:require [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.cache :as cache]
            [org.replikativ.spindel.runtime.impl.simple :as simple]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.spin.protocols :as tp]
            [org.replikativ.spindel.spin.continuation :as cont]
            [org.replikativ.spindel.spin.result :as result]
            [org.replikativ.spindel.log :as log]
            [is.simm.partial-cps.runtime])
  #?(:clj (:import [is.simm.partial_cps.runtime Thunk]
                    [java.util.concurrent ForkJoinPool]
                    [java.util.concurrent.locks LockSupport]
                    [java.lang.ref WeakReference])))

;; =============================================================================
;; Automatic Spin Cleanup via Finalizers
;; =============================================================================

#?(:clj
   (def ^:private spin-cleaner
     "Global cleaner for automatic spin cleanup when spins are GC'd.
      Uses Java 9+ Cleaner API for deterministic cleanup."
     (delay (java.lang.ref.Cleaner/create))))

#?(:cljs
   (def ^:private spin-registry
     "Global FinalizationRegistry for automatic spin cleanup when spins are GC'd.
      Only available in modern JS runtimes (Node 14+, Chrome 84+).
      Degrades gracefully if not available.

      Each registration holds a WeakRef to the ExecutionContext so cleanup
      works even when *execution-context* is not dynamically bound (GC
      callbacks run outside user code)."
     (when (exists? js/FinalizationRegistry)
       (js/FinalizationRegistry.
        (fn [held-value]
          (try
            (if-let [cleanup-fn (.-cleanup_fn held-value)]
              ;; Generic cleanup callback (from register-cleanup!)
              (cleanup-fn)
              ;; Spin-specific cleanup via WeakRef to context
              (let [spin-id (.-spin_id held-value)
                    weak-ctx (.-weak_ctx held-value)]
                (when-let [ctx (and weak-ctx (.deref weak-ctx))]
                  (simple/try-gc-cleanup-spin! ctx spin-id))))
            (catch :default _
              ;; Silently ignore errors during GC cleanup
              nil)))))))

;; =============================================================================
;; Spin - Pure CPS Interface (Fork-Safe!)
;; =============================================================================
;;
;; Key design:
;; - NO internal atoms (dirty?, result, cancelled?, initialized?) - all state in runtime
;; - Implements IFn (standard CPS): (spin resolve reject) → result
;;   Runtime and spin-id obtained from dynamic bindings (*execution-context*, *spin-id*)
;; - Implements IDeref for backward compat: @spin blocks until complete
;;   IMPORTANT: Never call @spin internally! Always use IFn interface (pure CPS, non-blocking)
;; - Returns ::incomplete when spin is running (for trampoline suspension)
;; - Populates :spin-outputs for non-blocking spin-to-spin await

;; Forward declaration for error handling
(declare abort-spin-chain!)

;; =============================================================================
;; Trampoline Helper - Removed, now using cont/resume
;; =============================================================================
;; The trampoline-thunk function has been replaced with cont/resume which
;; provides the same functionality through invoke-continuation from partial-cps.

;; spin-fn now arity-2 (resolve reject) relying on dynamic bindings (*execution-context*, *spin-id*).
;; Spin is STATELESS - no runtime reference, uses dynamic *execution-context* binding.

#?(:clj
   (defn- deref-spin
     "Core deref logic for Spin. Blocks until spin completes.

     timeout-ms: 0 means block indefinitely, >0 means timeout after that many ms.
     timeout-val: value returned on timeout (only used when timeout-ms > 0)."
     [this spin-id spin-fn timeout-ms timeout-val]
     (let [cached (rtc/spin-current-result spin-id)
           runtime (rtc/current-execution-context)
           rebuild-mode? (and (instance? org.replikativ.spindel.runtime.context.ExecutionContext runtime)
                              (ctx/rebuild-mode? runtime))
           wait-on-promise (fn [result-promise]
                             (if (pos? timeout-ms)
                               (let [res (deref result-promise timeout-ms ::timeout)]
                                 (if (= res ::timeout)
                                   timeout-val
                                   (result/unwrap res)))
                               (result/unwrap @result-promise)))]
       (cond
         ;; Rebuild mode with cache hit - execute body but return cached value
         (and cached (rtc/spin-result-clean? spin-id) rebuild-mode?)
         (do
           (log/debug! {:event :deref/rebuild-mode :data {:spin-id spin-id}})
           (binding [rtc/*execution-context* runtime
                     rtc/*spin-id* spin-id]
             (spin-fn (fn [_] nil) (fn [_] nil)))
           (result/unwrap cached))

         ;; Normal cache hit - return cached result
         (and cached (rtc/spin-result-clean? spin-id))
         (result/unwrap cached)

         ;; Not completed or dirty - check if already running
         :else
         (if (simple/running? runtime spin-id)
           ;; Spin is executing or suspended - wait for completion via promise callback
           (do
             (log/trace! {:event :spin/deref-wait-running :data {:spin-id spin-id}})
             (let [result-promise (promise)]
               (simple/add-pending-callback! runtime spin-id
                 {:resolve (fn [v] (deliver result-promise (result/ok v)))
                  :reject (fn [e] (deliver result-promise (result/error e)))})
               ;; Double-check: spin might have completed between running? check and callback registration
               (let [cached-now (rtc/spin-current-result spin-id)]
                 (if (and cached-now (rtc/spin-result-clean? spin-id))
                   (result/unwrap cached-now)
                   (do
                     (log/trace! {:event :spin/deref-done-wait :data {:spin-id spin-id}})
                     (wait-on-promise result-promise))))))
           ;; Not running - enqueue spin execution
           (let [result-promise (promise)]
             (log/trace! {:event :spin/deref-start :data {:spin-id spin-id}})
             (rtc/enqueue-event! {:type :spin-execution
                                  :id spin-id
                                  :spin this
                                  :resolve-fn (fn [value]
                                                (deliver result-promise (result/ok value)))
                                  :reject-fn (fn [error]
                                               (deliver result-promise (result/error error)))})
             (log/trace! {:event :spin/deref-done :data {:spin-id spin-id}})
             (wait-on-promise result-promise)))))))

(deftype Spin [spin-id spin-fn]
  tp/PSpin
  (spin-id [_] spin-id)

  #?(:clj clojure.lang.IFn :cljs IFn)
  (#?(:clj invoke :cljs -invoke) [this resolve reject]
    ;; DEBUG: Track invoke depth in CLJS
    ;; Standard CPS signature: (spin resolve reject)
    ;; Runtime and spin-id obtained from dynamic bindings
    (let [runtime (rtc/current-execution-context)
          local-cached (rtc/spin-current-result spin-id)
          ;; NEW: Check global content-addressed cache
          deps-hash (simple/get-deps-hash runtime spin-id)
          global-cached (when deps-hash
                          (cache/lookup spin-id deps-hash nil))
          ;; Check if we're in rebuild mode
          rebuild-mode? (and (instance? org.replikativ.spindel.runtime.context.ExecutionContext runtime)
                             (ctx/rebuild-mode? runtime))]
      (cond
          ;; Case 1a: Cache hit + rebuild mode - execute body for side effects, return cached value
          ;; Rebuild mode is used after deserialization to re-create nested spins and
          ;; re-register continuations, while returning the previously cached values.
          (and local-cached (rtc/spin-result-clean? spin-id) rebuild-mode?)
          (do
            (log/debug! {:event :cache/rebuild-mode :data {:spin-id spin-id}})
            ;; Execute spin body for side effects (nested spin creation, continuation registration)
            (binding [rtc/*execution-context* runtime
                      rtc/*spin-id* spin-id]
              ;; Execute with dummy callbacks - we'll use cached value anyway
              (spin-fn (fn [_] nil) (fn [_] nil)))
            ;; Return cached value
            (result/match local-cached
              (fn [value]
                (cont/resume resolve value)
                value)
              (fn [error]
                (cont/resume reject error)
                (when-not (= ::spin-cancelled (:type (ex-data error)))
                  (throw error)))))

          ;; Case 1b: Local cache hit (normal mode) - resolve from local cache (fastest!)
          (and local-cached (rtc/spin-result-clean? spin-id))
          (do
            (log/trace! {:event :cache/local-hit :data {:spin-id spin-id}})
            ;; CRITICAL: Enqueue completion event even for cache hits
            ;; This ensures awaiting spins' continuations are resumed
            (simple/enqueue-completion-event! runtime spin-id)
            (result/match local-cached
              ;; Success case
              (fn [value]
                ;; Call resolve via cont/resume to handle Thunk returns
                (cont/resume resolve value)
                ;; Return the spin's value (not the callback result)
                value)
              ;; Error case
              (fn [error]
                ;; Call reject via cont/resume to handle Thunk returns
                (cont/resume reject error)
                ;; Re-throw the error UNLESS it's a cancellation error
                ;; (cancellation errors are handled via callbacks, not exceptions)
                (when-not (= ::spin-cancelled (:type (ex-data error)))
                  (throw error)))))

          ;; Case 2: Global cache hit - only if no local cache (first execution)
          ;; If local cache exists but is dirty, skip to re-execution
          (and (not local-cached) global-cached)
          (do
            (log/debug! {:event :cache/global-hit
                         :data {:spin-id spin-id :deps-hash deps-hash}})
            ;; Update local cache from global cache
            (rtc/spin-cache-result! spin-id global-cached)
            (result/match global-cached
              ;; Success case
              (fn [value]
                (cont/resume resolve value)
                value)
              ;; Error case
              (fn [error]
                (cont/resume reject error)
                (when-not (= ::spin-cancelled (:type (ex-data error)))
                  (throw error)))))

          ;; Case 3: Cache miss - execute spin
          :else
          (let [;; Local execution state (ephemeral, not in runtime)
                callbacks-atom (atom [{:resolve resolve :reject reject}])
                executing? (atom true)]

            (log/debug! {:event :spin/start :data {:spin-id spin-id}})
            (log/trace! {:event :spin/executing-body :data {:spin-id spin-id :thread #?(:clj (.getName (Thread/currentThread)) :cljs "js")}})

            ;; CRITICAL: Invalidate spins created during previous execution
            ;; Their closures captured values from the old run - now stale
            (simple/invalidate-created-spins! runtime spin-id)

            ;; Execute spin-fn with dynamic bindings
            ;; Phase 2: Bind both *execution-context* and *execution-context* for compatibility
            (binding [rtc/*execution-context* runtime
                      rtc/*spin-id* spin-id]
              (let [result (spin-fn
                            ;; Resolve continuation
                            (fn [value]
                              ;; CRITICAL: Get CURRENT runtime, not captured one!
                              ;; When continuation is resumed in a fork context,
                              ;; we need to write to the fork's state, not the parent's.
                              (let [current-rt (rtc/current-execution-context)]
                                ;; Cache result via protocol (uses current-rt via dynamic binding)
                                (rtc/spin-cache-result! spin-id (result/ok value))

                                ;; Store for non-blocking await
                                (rtc/swap-state! [:spin-outputs spin-id] (constantly value))

                                ;; Record dependencies (computes deps-hash)
                                (rtc/graph-commit-deps! spin-id)

                                ;; NEW: Store in global content-addressed cache
                                (let [deps-hash (simple/get-deps-hash current-rt spin-id)]
                                  (when deps-hash
                                    (cache/store! spin-id deps-hash nil (result/ok value))
                                    (log/debug! {:event :cache/global-store
                                                 :data {:spin-id spin-id :deps-hash deps-hash}})))

                                ;; Emit spin-completion event for engine
                                ;; CRITICAL: Use enqueue-completion-event! for glitch-free batching
                                (simple/enqueue-completion-event! current-rt spin-id)
                                (log/debug! {:event :spin/completed
                                             :data {:spin-id spin-id :enqueued :spin-completion}})

                                ;; Call all pending callbacks from local state
                                (let [callbacks @callbacks-atom]
                                  (doseq [{:keys [resolve]} callbacks]
                                    ;; Call resolve via cont/resume to handle Thunk returns
                                    (cont/resume resolve value)))

                                ;; CRITICAL: Also call any pending callbacks from shared state
                                ;; These are from duplicate :spin-execution events that were skipped
                                (let [pending (simple/take-pending-callbacks! current-rt spin-id)]
                                  (when (seq pending)
                                    (log/trace! {:event :spin/pending-callbacks
                                                 :data {:spin-id spin-id :count (count pending)}})
                                    (doseq [{:keys [resolve]} pending]
                                      (resolve value))))  ; Direct call, not cont/resume

                                (reset! executing? false)
                                value))  ; Return for trampoline - closes (let [current-rt ...])

                            ;; Reject continuation
                            (fn [error]
                              ;; CRITICAL: Get CURRENT runtime, not captured one!
                              ;; When continuation is resumed in a fork context,
                              ;; we need to write to the fork's state, not the parent's.
                              (let [_current-rt (rtc/current-execution-context)]
                                ;; Cache error via protocol (uses current-rt via dynamic binding)
                                (rtc/spin-cache-result! spin-id (result/error error))

                                ;; Store error marker for non-blocking await
                                (rtc/swap-state! [:spin-outputs spin-id] (constantly [:error error]))

                                ;; Record dependencies even on error
                                (rtc/graph-commit-deps! spin-id)

                                ;; Notify dependents just like success path
                                ;; CRITICAL: Use enqueue-completion-event! for glitch-free batching
                                (simple/enqueue-completion-event! _current-rt spin-id)
                                (log/debug! {:event :spin/errored
                                             :data {:spin-id spin-id :enqueued :spin-completion}})

                                ;; Abort downstream spins
                                (abort-spin-chain! spin-id error)

                                ;; Call all pending callbacks from local state
                                (let [callbacks @callbacks-atom]
                                  (doseq [{:keys [reject]} callbacks]
                                    ;; Call reject via cont/resume to handle Thunk returns
                                    (cont/resume reject error)))

                                ;; CRITICAL: Also call any pending callbacks from shared state
                                ;; These are from duplicate :spin-execution events that were skipped
                                (let [current-rt (rtc/current-execution-context)
                                      pending (simple/take-pending-callbacks! current-rt spin-id)]
                                  (when (seq pending)
                                    (log/trace! {:event :spin/pending-callbacks-error
                                                 :data {:spin-id spin-id :count (count pending)}})
                                    (doseq [{:keys [reject]} pending]
                                      (reject error))))  ; Direct call, not cont/resume

                                (reset! executing? false)
                                ;; Don't re-throw! Error already recorded in spin state.
                                nil)))]  ; Return nil instead of throwing - closes (let [_current-rt ...]) and (fn [error] ...) and (spin-fn ...)

                ;; Check if another caller arrived while we were starting
                ;; If so, they couldn't have registered (we didn't expose the atom)
                ;; This is safe because spin execution is idempotent via caching

                ;; CRITICAL: If spin returned incomplete (suspended awaiting deferred),
                ;; clear running? flag so deref doesn't poll-wait forever
                (when (= result :org.replikativ.spindel.spin/incomplete)
                  (simple/mark-not-running! runtime spin-id))

                ;; Return result (could be value or ::incomplete from nested await)
                result))))))

  #?(:clj clojure.lang.IDeref :cljs IDeref)
  (#?(:clj deref :cljs -deref) [this]
    ;; Blocks until spin completes, then returns cached value.
    ;; Requires *execution-context* to be bound by the caller.
    #?(:clj (deref-spin this spin-id spin-fn 0 nil)
       :cljs (throw (ex-info "@Spin not supported in CLJS runtime" {}))))

  #?@(:clj
      [clojure.lang.IBlockingDeref
       (deref [this timeout-ms timeout-val]
         (deref-spin this spin-id spin-fn timeout-ms timeout-val))])

  Object
  (toString [_this]
    (str "#<Spin " spin-id ">")))

;; =============================================================================
;; Spin Creation
;; =============================================================================

(defn make-spin
  "Create a stateless Spin.

   Spins are STATELESS - they don't hold runtime references.
   Runtime is bound dynamically via *execution-context* when spins are invoked.

   Automatic cleanup: When the spin is GC'd, it's automatically removed from the runtime.
   Uses Cleaner (Java 9+) or FinalizationRegistry (JS).

   Usage:
     (binding [rtc/*execution-context* my-runtime]
       (def my-reactive (make-spin my-spin-fn :my-spin))
       @my-reactive)  ; Runs spin, caches result

   The spin-id is used to track dependencies in the runtime's graph."
  ([spin-fn]
   (make-spin spin-fn (keyword (gensym "spin-"))))
  ([spin-fn spin-id]
   (let [reactive-spin (->Spin spin-id spin-fn)]

     ;; Register spin with runtime via protocol (uses dynamic *execution-context*)
     (rtc/spin-register! spin-id {:provides #{}})

     ;; Register automatic cleanup when spin is GC'd
     ;; Both platforms: capture a WeakRef to the ExecutionContext so cleanup
     ;; can find the context even when *execution-context* is not bound.
     #?(:clj
        (let [ctx (rtc/current-execution-context)
              weak-ctx (WeakReference. ctx)
              sid spin-id]
          (.register ^java.lang.ref.Cleaner @spin-cleaner
                     reactive-spin
                     (reify Runnable
                       (run [_]
                         (try
                           (when-let [c (.get weak-ctx)]
                             (simple/try-gc-cleanup-spin! c sid))
                           (catch Exception _
                             ;; Silently ignore errors during GC cleanup
                             nil))))))
        :cljs
        (when spin-registry
          (let [ctx (rtc/current-execution-context)]
            (.register spin-registry
                       reactive-spin
                       #js {:spin_id spin-id
                            :weak_ctx (js/WeakRef. ctx)}))))

     reactive-spin)))

(defn ^:no-doc register-cleanup!
  "Register cleanup for an object when it's GC'd.

   This is a public helper that allows other namespaces (like sequence.cljc)
   to register cleanup without accessing private spin-cleaner/spin-registry.

   Parameters:
   - obj: The object to watch for GC (e.g., DFlow, Spin)
   - cleanup-fn: Function to call when obj is GC'd (takes no args)"
  [obj cleanup-fn]
  #?(:clj
     (.register ^java.lang.ref.Cleaner @spin-cleaner
                obj
                (reify Runnable
                  (run [_]
                    (try
                      (cleanup-fn)
                      (catch Exception _
                        nil)))))
     :cljs
     (when spin-registry
       (.register spin-registry
                  obj
                  #js {:cleanup_fn cleanup-fn}))))

;; =============================================================================
;; Helper Functions (used by lifecycle.cljc)
;; =============================================================================

(defn abort-spin-chain!
  "Abort a spin and all its observers due to upstream error or cancellation.

   This implements eager error abortion: when a spin fails or is cancelled,
   immediately propagate the cancellation through the entire dependency chain.

   Uses PSpinLifecycle protocol for fork-safe operation.
   Requires *execution-context* to be bound (happens automatically in spin context).

   Parameters:
     spin-id - ID of the spin to abort
     error - The error/exception that caused the abortion"
  [spin-id error]
  (rtc/spin-cache-result! spin-id (result/error error))
  ;; TODO: Propagate to observers via PGraph/ordered-observers protocol
  ;; For now, observers are handled by engine events
  )

;; Export the ::spin-cancelled constant for use by other namespaces
(def spin-cancelled ::spin-cancelled)

;; Sentinel value returned when a spin suspends (awaiting deferred/child)
;; NOTE: Uses explicit keyword to ensure consistency across all namespaces.
;; All code comparing against this value must use spin-core/incomplete.
(def incomplete :org.replikativ.spindel.spin/incomplete)
