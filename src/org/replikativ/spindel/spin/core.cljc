(ns org.replikativ.spindel.spin.core
  "Core Spin deftype - stateless spin execution.

  Includes spin protocols, result types, continuation helpers,
  lifecycle management, and error combinators."
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [replikativ.logging :as log]
            [is.simm.partial-cps.async :as pcps-async]
            [is.simm.partial-cps.runtime])
  #?(:clj (:import [java.lang.ref WeakReference])))

;; =============================================================================
;; PSpin Protocol (from spin/protocols.cljc)
;; =============================================================================

(defprotocol PSpin
  (spin-id [_] "Spin id of this spin."))

;; =============================================================================
;; Result Type (from spin/result.cljc)
;; =============================================================================

(defprotocol PResult
  "Protocol for spin execution results."
  (ok? [this]
    "Returns true if this is a success result, false if error.")
  (error? [this]
    "Returns true if this is an error result, false if success.")
  (unwrap [this]
    "Returns the value if success, throws the error if failure.")
  (match [this ok-fn error-fn]
    "Pattern match on result without throwing.
    Calls ok-fn with value if success, error-fn with error if failure."))

(defrecord Result [variant payload]
  PResult
  (ok? [_]
    (= variant :ok))

  (error? [_]
    (= variant :error))

  (unwrap [_]
    (if (= variant :ok)
      payload
      (throw payload)))

  (match [_ ok-fn error-fn]
    (if (= variant :ok)
      (ok-fn payload)
      (error-fn payload))))

(defn ok
  "Create a success result with the given value.
  Value can be nil."
  [value]
  (->Result :ok value))

(defn error
  "Create an error result with the given throwable."
  [err]
  (->Result :error err))

;; =============================================================================
;; Continuation Helpers (from spin/continuation.cljc)
;; =============================================================================

(defn resume
  "Resume a CPS continuation (resolve or reject callback) with a value.

  This is the universal wrapper for calling any continuation in the system.
  It ensures that if the continuation returns a Thunk (as happens in loop/recur),
  that Thunk is properly trampolined to prevent stack overflow.

  Usage:
    (resume resolve value)
    (resume reject error)

  ALWAYS use this function instead of calling continuations directly.
  Direct calls will fail in loop/recur contexts."
  [cont-fn value]
  (pcps-async/invoke-continuation cont-fn value))

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
            ;; ^js suppresses :infer-warning on direct property access;
            ;; held-value is the JS object passed to .register at the
            ;; registration site below.
            (if-let [cleanup-fn (.-cleanup_fn ^js held-value)]
              ;; Generic cleanup callback (from register-cleanup!)
              (cleanup-fn)
              ;; Spin-specific cleanup via WeakRef to context
              (let [spin-id (.-spin_id ^js held-value)
                    weak-ctx (.-weak_ctx ^js held-value)]
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
;;   (Note: :spin-outputs top-level state was previously written here but
;;   never read; removed in the unified-subscription cleanup. The spin's
;;   result lives on the SpinNode in :nodes[spin-id]:result.)

;; Forward declaration for error handling
(declare abort-spin-chain!)

;; spin-fn now arity-2 (resolve reject) relying on dynamic bindings (*execution-context*, *spin-id*).
;; Spin is STATELESS - no runtime reference, uses dynamic *execution-context* binding.

#?(:clj
   (defn- deref-spin
     "Core deref logic for Spin. Blocks until spin completes.

     timeout-ms: 0 means block indefinitely, >0 means timeout after that many ms.
     timeout-val: value returned on timeout (only used when timeout-ms > 0)."
     [this spin-id spin-fn timeout-ms timeout-val]
     (when simple/*in-drain?*
       (throw (ex-info "Cannot deref @(spin ...) from inside a drain context (would deadlock). Use spawn! for fire-and-forget or await for spin-to-spin coordination."
                       {:spin-id spin-id})))
     (let [cached (ec/spin-current-result spin-id)
           runtime (ec/current-execution-context)
           rebuild-mode? (and (instance? org.replikativ.spindel.engine.context.ExecutionContext runtime)
                              (ctx/rebuild-mode? runtime))
           wait-on-promise (fn [result-promise]
                             (if (pos? timeout-ms)
                               (let [res (deref result-promise timeout-ms ::timeout)]
                                 (if (= res ::timeout)
                                   timeout-val
                                   (unwrap res)))
                               (unwrap @result-promise)))]
       (cond
         ;; Rebuild mode with cache hit - execute body but return cached value
         (and cached (ec/spin-result-clean? spin-id) rebuild-mode?)
         (do
           (log/debug :deref/rebuild-mode {:spin-id spin-id})
           ;; Seed the per-spin chain-head slot before invoking spin-fn.
           ;; See addressing.cljc — the cursor lives in ctx state, not a
           ;; dynamic var, so it follows fork/snapshot semantics.
           (addressing/seed-body-chain-head! runtime spin-id)
           (binding [ec/*execution-context* runtime
                     ec/*spin-id* spin-id]
             (spin-fn (fn [_] nil) (fn [_] nil)))
           (unwrap cached))

         ;; Normal cache hit - return cached result
         (and cached (ec/spin-result-clean? spin-id))
         (unwrap cached)

         ;; Not completed or dirty - check if already running
         :else
         (if (simple/running? runtime spin-id)
           ;; Spin is executing or suspended - wait for completion via promise callback
           (do
             (log/trace :spin/deref-wait-running {:spin-id spin-id})
             (let [result-promise (promise)]
               (simple/add-pending-callback! runtime spin-id
                                             {:resolve (fn [v] (deliver result-promise (ok v)))
                                              :reject (fn [e] (deliver result-promise (error e)))})
               ;; Double-check: spin might have completed between running? check and callback registration
               (let [cached-now (ec/spin-current-result spin-id)]
                 (if (and cached-now (ec/spin-result-clean? spin-id))
                   (unwrap cached-now)
                   (do
                     (log/trace :spin/deref-done-wait {:spin-id spin-id})
                     (wait-on-promise result-promise))))))
           ;; Not running - enqueue spin execution
           (let [result-promise (promise)]
             (log/trace :spin/deref-start {:spin-id spin-id})
             (ec/enqueue-event! {:type :spin-execution
                                 :id spin-id
                                 :spin this
                                 :resolve-fn (fn [value]
                                               (deliver result-promise (ok value)))
                                 :reject-fn (fn [e]
                                              (deliver result-promise (error e)))})
             (log/trace :spin/deref-done {:spin-id spin-id})
             (wait-on-promise result-promise)))))))

(deftype Spin [spin-id spin-fn]
  PSpin
  (spin-id [_] spin-id)

  #?(:clj clojure.lang.IFn :cljs IFn)
  (#?(:clj invoke :cljs -invoke) [this resolve reject]
    ;; Standard CPS signature: (spin resolve reject)
    ;; Runtime and spin-id obtained from dynamic bindings
    (let [runtime (ec/current-execution-context)
          local-cached (ec/spin-current-result spin-id)
          ;; Check if we're in rebuild mode
          rebuild-mode? (and (instance? org.replikativ.spindel.engine.context.ExecutionContext runtime)
                             (ctx/rebuild-mode? runtime))]
      (cond
          ;; Case 1a: Cache hit + rebuild mode - execute body for side effects, return cached value
          ;; Rebuild mode is used after deserialization to re-create nested spins and
          ;; re-register continuations, while returning the previously cached values.
        (and local-cached (ec/spin-result-clean? spin-id) rebuild-mode?)
        (do
          (log/debug :cache/rebuild-mode {:spin-id spin-id})
            ;; Execute spin body for side effects (nested spin creation, continuation registration).
            ;; Fresh per-spin chain-head slot = nested spin minting reproduces the same id
            ;; sequence as the original run (rebuild's whole purpose).
            ;; Drop the prior body's ephemeral await conts: in rebuild mode
            ;; await-spin resolves synchronously and does NOT overwrite the
            ;; cont, so without this an :await-once cont from the original
            ;; run survives, fires on the next :spin-completion, and
            ;; re-invokes the prior body's CPS chain (which closes over
            ;; prior-run Spin instances). See clear-ephemeral-await-conts!.
          (simple/clear-prior-body-conts! runtime spin-id)
          (addressing/seed-body-chain-head! runtime spin-id)
          (binding [ec/*execution-context* runtime
                    ec/*spin-id* spin-id]
              ;; Execute with dummy callbacks - we'll use cached value anyway
            (spin-fn (fn [_] nil) (fn [_] nil)))
            ;; Return cached value
          (match local-cached
            (fn [value]
              (resume resolve value)
              value)
            (fn [error]
              (resume reject error)
              (when-not (= ::spin-cancelled (:type (ex-data error)))
                (throw error)))))

          ;; Case 1b: Local cache hit (normal mode) - resolve from local cache.
          ;; SpinNode :result is the single-slot cache for "deps unchanged since last run."
          ;; Dirty propagation + topological re-execution handle invalidation.
        (and local-cached (ec/spin-result-clean? spin-id))
        (do
          (log/trace :cache/local-hit {:spin-id spin-id})
            ;; CRITICAL: Enqueue completion event even for cache hits
            ;; This ensures awaiting spins' continuations are resumed
          (simple/enqueue-completion-event! runtime spin-id)
          (match local-cached
              ;; Success case
            (fn [value]
                ;; Call resolve via resume to handle Thunk returns
              (resume resolve value)
                ;; Return the spin's value (not the callback result)
              value)
              ;; Error case
            (fn [error]
                ;; Call reject via resume to handle Thunk returns
              (resume reject error)
                ;; Re-throw the error UNLESS it's a cancellation error
                ;; (cancellation errors are handled via callbacks, not exceptions)
              (when-not (= ::spin-cancelled (:type (ex-data error)))
                (throw error)))))

          ;; Case 2: Cache miss - execute spin
        :else
        (let [;; Local execution state (ephemeral, not in runtime)
              callbacks-atom (atom [{:resolve resolve :reject reject}])
              executing? (atom true)]

          (log/debug :spin/start {:spin-id spin-id})

            ;; Mark in-flight. With the unified-queue design, :running? denotes
            ;; "body invocation has begun but has not yet resolved" — covering
            ;; both actively-executing slices and suspensions on async resources
            ;; (Deferred, Mailbox, executor tasks). It is cleared only when
            ;; cache-result! fires (body resolved). This lets `running?` /
            ;; `await-drain-complete` / `deref` correctly detect in-flight work
            ;; without requiring a special Phase 2 wait.
          (simple/mark-running! runtime spin-id)
          (log/trace :spin/executing-body {:spin-id spin-id :thread #?(:clj (.getName (Thread/currentThread)) :cljs "js")})

            ;; Reset :created-spins for this body run; children are re-registered
            ;; as the body runs, and register-spin! re-runs any whose captured
            ;; environment changed (B) — no blanket invalidation needed.
          (simple/clear-created-spins! runtime spin-id)

            ;; Drop the prior body's ephemeral await conts at the same time.
            ;; The new body run will register fresh conts at each (await …)
            ;; via the slow path (deterministic cont-id would overwrite
            ;; anyway in normal mode); clearing here keeps the rebuild path
            ;; correct too (where the sync rebuild branch doesn't register).
            ;; Persistent :await-reactive conts (parallel/race) are kept.
          (simple/clear-prior-body-conts! runtime spin-id)

            ;; Seed this body slice's per-spin chain-head slot with
            ;; `body-start-chain-head spin-id` before invoking spin-fn —
            ;; see addressing.cljc.
          (addressing/seed-body-chain-head! runtime spin-id)
          (binding [ec/*execution-context* runtime
                    ec/*spin-id* spin-id]
            (let [result (spin-fn
                            ;; Resolve continuation
                          (fn [value]
                              ;; CRITICAL: Get CURRENT runtime, not captured one!
                              ;; When continuation is resumed in a fork context,
                              ;; we need to write to the fork's state, not the parent's.
                            (let [current-rt (ec/current-execution-context)]
                                ;; Cache result via protocol (uses current-rt via dynamic binding)
                              (ec/spin-cache-result! spin-id (ok value))

                                ;; Record dependencies on the SpinNode
                              (ec/graph-commit-deps! spin-id)

                                ;; Emit spin-completion event for engine
                                ;; CRITICAL: Use enqueue-completion-event! for glitch-free batching
                              (simple/enqueue-completion-event! current-rt spin-id)
                              (log/debug :spin/completed {:spin-id spin-id :enqueued :spin-completion})

                                ;; Call all pending callbacks from local state
                              (let [callbacks @callbacks-atom]
                                (doseq [{:keys [resolve]} callbacks]
                                    ;; Call resolve via resume to handle Thunk returns
                                  (resume resolve value)))

                                ;; CRITICAL: Also call any pending callbacks from shared state
                                ;; These are from duplicate :spin-execution events that were skipped
                              (let [pending (simple/take-pending-callbacks! current-rt spin-id)]
                                (when (seq pending)
                                  (log/trace :spin/pending-callbacks {:spin-id spin-id :count (count pending)})
                                  (doseq [{:keys [resolve]} pending]
                                    (resolve value))))  ; Direct call, not resume

                              (reset! executing? false)
                              value))  ; Return for trampoline - closes (let [current-rt ...])

                            ;; Reject continuation
                          (fn [err]
                              ;; CRITICAL: Get CURRENT runtime, not captured one!
                              ;; When continuation is resumed in a fork context,
                              ;; we need to write to the fork's state, not the parent's.
                            (let [_current-rt (ec/current-execution-context)]
                                ;; Cache error via protocol (uses current-rt via dynamic binding)
                              (ec/spin-cache-result! spin-id (error err))

                                ;; Record dependencies even on error
                              (ec/graph-commit-deps! spin-id)

                                ;; Notify dependents just like success path
                                ;; CRITICAL: Use enqueue-completion-event! for glitch-free batching
                              (simple/enqueue-completion-event! _current-rt spin-id)
                              (log/debug :spin/errored {:spin-id spin-id :enqueued :spin-completion})

                                ;; Abort downstream spins
                              (abort-spin-chain! spin-id err)

                                ;; Call all pending callbacks from local state
                              (let [callbacks @callbacks-atom]
                                (doseq [{:keys [reject]} callbacks]
                                    ;; Call reject via resume to handle Thunk returns
                                  (resume reject err)))

                                ;; CRITICAL: Also call any pending callbacks from shared state
                                ;; These are from duplicate :spin-execution events that were skipped
                              (let [current-rt (ec/current-execution-context)
                                    pending (simple/take-pending-callbacks! current-rt spin-id)]
                                (when (seq pending)
                                  (log/trace :spin/pending-callbacks-error {:spin-id spin-id :count (count pending)})
                                  (doseq [{:keys [reject]} pending]
                                    (reject err))))  ; Direct call, not resume

                              (reset! executing? false)
                                ;; Don't re-throw! Error already recorded in spin state.
                              nil)))]  ; Return nil instead of throwing

                ;; Body suspended (returned ::incomplete). We do NOT clear
                ;; :running? here — the body is still in-flight, just waiting
                ;; on an async resource (Deferred, executor task, etc.). It
                ;; will be cleared when the body resolves via cache-result!.
                ;; See `mark-running!` call above for rationale.

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
     (binding [ec/*execution-context* my-runtime]
       (def my-reactive (make-spin my-spin-fn :my-spin))
       @my-reactive)  ; Runs spin, caches result

   The spin-id is used to track dependencies in the runtime's graph."
  ([spin-fn]
   (make-spin spin-fn (keyword (gensym "spin-")) nil :resource))
  ([spin-fn spin-id]
   (make-spin spin-fn spin-id nil :resource))
  ([spin-fn spin-id captured-locals]
   (make-spin spin-fn spin-id captured-locals :computation))
  ([spin-fn spin-id captured-locals kind]
   (let [reactive-spin (->Spin spin-id spin-fn)]

     ;; Register spin with runtime via protocol (uses dynamic *execution-context*).
     ;; captured-locals — {sym value} of the body's free variables — lets
     ;; register-spin! detect (identical?) whether a re-registered spin's
     ;; captured environment changed. nil for non-macro callers.
     ;; kind — :computation (deterministic id, replayable, B-gated; minted by
     ;; the `spin`/`effect` macro's 3-arity call) or :resource (gensym id,
     ;; effectful one-shot body; the 1-/2-arity used by sleep/parallel/race/
     ;; deferred/mailbox/… combinators, which are not replayable).
     (ec/spin-register! spin-id {:provides #{}
                                 :captured-locals captured-locals
                                 :kind kind})

     ;; Snapshot this spin's lexical scope — the registered spin-scope
     ;; binding keys (see engine.bindings) — from the construction-time
     ;; execution context onto the spin's node. The engine re-applies the
     ;; snapshot on every COLD body start (the :spin-execution handler in
     ;; engine/impl/simple.cljc and the await-spin slow/rebuild child
     ;; invocation in effects/await.cljc), giving spins closure semantics
     ;; over the scope they were constructed under. Continuation resumes
     ;; instead restore the suspend-time scope via the cont's
     ;; `:slice-state` snapshot. Which keys count as scope is
     ;; supplied entirely by the registry — e.g. dom.addressing registers
     ;; :dom/parent-addr / :dom/current-slot — so spin/core stays domain-
     ;; agnostic. Spins constructed at root scope capture nothing, so this
     ;; is a no-op there.
     (when-let [ctx (ec/current-execution-context)]
       (let [spin-scope (select-keys (:bindings ctx)
                                     (bindings/spin-scope-keys))]
         (when (seq spin-scope)
           (rtp/swap-state! ctx [:nodes spin-id :spin-scope]
                            (constantly spin-scope)))))

     ;; Register automatic cleanup when spin is GC'd
     ;; Both platforms: capture a WeakRef to the ExecutionContext so cleanup
     ;; can find the context even when *execution-context* is not bound.
     #?(:clj
        (let [ctx (ec/current-execution-context)
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
          (let [ctx (ec/current-execution-context)]
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
;; Helper Functions
;; =============================================================================

(defn abort-spin-chain!
  "Abort a spin and all its observers due to upstream error or cancellation.

   This implements eager error abortion: when a spin fails or is cancelled,
   immediately propagate the cancellation through the entire dependency chain.

   Uses PSpinLifecycle protocol for fork-safe operation.
   Requires *execution-context* to be bound (happens automatically in spin context).

   Parameters:
     spin-id - ID of the spin to abort
     err - The error/exception that caused the abortion"
  [spin-id err]
  (ec/spin-cache-result! spin-id (error err))
  ;; Propagate error to track observers: mark them dirty so they re-execute
  ;; and discover the error via their track continuation.
  ;; NOTE: We only mark OBSERVERS dirty, not the failed spin itself.
  ;; The caller (reject continuation or cancel-spin!) handles the spin's own
  ;; completion event and cache state.
  (let [ctx (ec/current-execution-context)
        observers (ec/get-state [:observers spin-id])]
    (doseq [observer-id observers]
      (simple/mark-dirty! ctx observer-id))))

;; Export the ::spin-cancelled constant for use by other namespaces
(def spin-cancelled ::spin-cancelled)

;; Sentinel value returned when a spin suspends (awaiting deferred/child)
;; NOTE: Uses explicit keyword to ensure consistency across all namespaces.
;; All code comparing against this value must use spin-core/incomplete.
(def incomplete :org.replikativ.spindel.spin/incomplete)

;; =============================================================================
;; Spin Lifecycle (from spin/lifecycle.cljc)
;; =============================================================================

(defn spin-cancelled?
  "Check if a spin has been cancelled by user.

   Uses PSpin protocol and PSpinLifecycle to check error state.
   Requires *execution-context* to be bound."
  [spin]
  (let [cached (ec/spin-current-result (spin-id spin))]
    (when (and cached (error? cached))
      (match cached
        (fn [_] false)
        (fn [e] (= "Spin cancelled by user" (.getMessage ^Throwable e)))))))

(defn spin-failed?
  "Check if a spin has failed (either due to error or cancellation).

   Uses PSpin protocol and PSpinLifecycle to check cached error.
   Requires *execution-context* to be bound.
   This includes both user-initiated cancellation and error propagation."
  [spin]
  (let [cached (ec/spin-current-result (spin-id spin))]
    (boolean (and cached (error? cached)))))

(defn ^:no-doc set-owned-spins!
  "Record the child spins a fan-out combinator (`race`/`parallel`) owns during
   its initial concurrent fan-out, so an external `cancel-spin!` of the
   combinator cascades into those still-in-flight children.

   The children are started via manual `make-spin` callbacks, NOT `await`, so
   they sit outside the await-cont graph that `cancel-spin!` normally walks —
   without this edge an external cancel can't reach them (the structured-
   concurrency gap).

   Stored ON the combinator's own node (`:nodes[sid]:owned-spins`), so it is
   reclaimed for free when `full-cleanup-spin!` drops the node — no separate
   top-level registry to keep in sync across cleanup/fork/GC sites. `spins`
   nil/empty CLEARS the edge (called when the combinator's `done?` flips: a
   resolved `race` is terminal, and a completed `parallel` has by then
   registered its children as `:await-reactive` conts which the normal cascade
   covers)."
  [sid spins]
  (when-let [ctx (ec/current-execution-context)]
    (rtp/swap-state! ctx [:nodes sid :owned-spins]
                     (constantly (when (seq spins) (vec spins))))))

(defn cancel-spin!
  "Cancel a spin and all its observers (cooperative cancellation).

   Spins will check cancellation at await points (cooperative, not preemptive).

   Parameters:
     spin - The Spin to cancel (not spin-id!)

   Returns:
     nil"
  [spin]
  (let [sid (spin-id spin)
        err (ex-info "Spin cancelled by user"
                     {:type spin-cancelled
                      :spin-id sid
                      :cancelled-at #?(:clj (java.util.Date.)
                                       :cljs (js/Date.))})
        ;; Requires *execution-context* to be bound by caller
        ctx   (ec/current-execution-context)
        conts (ec/get-state [:await-conts sid])]
    ;; (1) Cache the cancel result + dirty observers. Makes `spin-is-cancelled?`
    ;; true, so a RUNNING spin rejects at its next await (cooperative), and any
    ;; awaiting parents are re-notified.
    (abort-spin-chain! sid err)
    ;; (2) A SUSPENDED spin will never reach another await on its own, so step (1)
    ;; alone strands it: its body never resumes and its `try/finally` cleanup never
    ;; runs (and the parked continuation + external reader leak). Actively unwind it
    ;; by delivering the cancellation into its parked await continuation — the
    ;; structured-concurrency contract (`finally`/`ensure` runs on cancel).
    (doseq [[cont-id cont] conts]
      (case (:kind cont)
        ;; Parked on a Deferred / Mailbox / async-thunk: invoking the cont's reject
        ;; continuation resumes the body into its reject path so catch/finally run.
        ;; Then arm the external-resource cancellation gate (so a later delivery on
        ;; the abandoned reader is a no-op) and drop the now-spent cont.
        :external-await
        (do (try
              (binding [ec/*execution-context* ctx
                        ec/*spin-id*          sid
                        pcps-async/*in-trampoline* false]
                (when-let [rj (:reject-fn cont)] (rj err)))
              (catch #?(:clj Throwable :cljs :default) _ nil))
            (when-let [c! (:cancel! cont)]
              (try (c! ctx) (catch #?(:clj Throwable :cljs :default) _ nil)))
            (ec/swap-state! [:await-conts sid] (fn [m] (dissoc m cont-id))))
        ;; Parked awaiting a child spin (incl. a reactive aseq/PSpin): resume THIS
        ;; parent into reject directly — the cont's :reject-fn is the parent body's
        ;; raw reject continuation, so invoking it unwinds the parent's try/finally
        ;; without depending on the child driving a :spin-completion resume (which a
        ;; reactive await won't, on cancel). Then cascade-cancel the awaited child so
        ;; it terminates too, and drop the spent cont.
        (:await-once :await-reactive)
        (do (try
              (binding [ec/*execution-context* ctx
                        ec/*spin-id*          sid
                        pcps-async/*in-trampoline* false]
                (when-let [rj (:reject-fn cont)] (rj err)))
              (catch #?(:clj Throwable :cljs :default) _ nil))
            (when-let [child (:awaited-spin cont)]
              (cancel-spin! child))
            (ec/swap-state! [:await-conts sid] (fn [m] (dissoc m cont-id))))
        nil))
    ;; (3) Cascade into combinator-owned children. A fan-out combinator
    ;; (`race`/`parallel`) starts its children via manual `make-spin` callbacks,
    ;; so during the initial fan-out window they are held outside the await-cont
    ;; graph — steps (1)/(2) never reach them and they (plus any `finally` they
    ;; guard) leak on an external cancel. The combinator records them on its node
    ;; via `set-owned-spins!`; cancel each that is still in flight. The
    ;; cached-result guard skips a child that already terminated (e.g. a race
    ;; winner), so we never overwrite a completed result — and the combinator
    ;; clears this edge when `done?` flips, so post-completion cancels find it
    ;; empty regardless.
    (doseq [child (ec/get-state [:nodes sid :owned-spins])]
      (when (and child (nil? (ec/spin-current-result (spin-id child))))
        (cancel-spin! child)))))

(defn cleanup-spin!
  "Manually clean up a spin, removing it from the runtime.

   This is useful when you want explicit cleanup without waiting for GC.
   The spin will be removed from:
   - All signal observer lists
   - All spin observer lists
   - The dependency graph

   After cleanup, the spin should not be dereferenced again.

   Parameters:
     spin - The Spin to clean up (not spin-id!)

   Returns:
     nil"
  [spin]
  (let [sid (spin-id spin)]
    ;; Cancel the spin first (stops any running computation)
    (cancel-spin! spin)
    ;; Clean up dependencies and remove from runtime
    (ec/graph-clear-deps! sid)))

;; =============================================================================
;; Error Handling Combinators (from spin/error.cljc)
;; =============================================================================

(defn attempt
  "Wrap spin result in a zero-argument function that returns result or throws error.

   Always succeeds - errors are captured as throwable functions."
  ([spin]
   (make-spin
    ;; spin-fn is the arity-2 CPS continuation `(resolve reject)` — the
    ;; signature `Spin`'s invoke calls. The wrapped spin is itself a
    ;; `Spin`, also invoked `(spin on-ok on-err)`.
    (fn [resolve _reject]
      ;; Always succeed with a thunk capturing either value or error
      (let [on-ok (fn [v] (resolve (fn [] v)))
            on-err (fn [e] (resolve (fn [] (throw e))))]
        (spin on-ok on-err)
        incomplete)))))

(defn absolve
  "Unwrap a spin returning a zero-argument function, calling it and returning result.

   Inverse of attempt - converts wrapped errors back to thrown errors."
  ([spin]
   (make-spin
    ;; arity-2 CPS continuation `(resolve reject)`; the wrapped spin is
    ;; a `Spin`, invoked `(spin on-ok on-err)`.
    (fn [resolve reject]
      (let [on-ok (fn [thunk]
                    (try
                      (resolve (thunk))
                      (catch #?(:clj Throwable :cljs :default) e
                        (reject e))))
            on-err (fn [e] (reject e))]
        (spin on-ok on-err)
        incomplete)))))
