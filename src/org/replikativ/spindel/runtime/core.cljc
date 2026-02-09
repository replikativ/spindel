(ns org.replikativ.spindel.runtime.core
	"Core runtime context and protocol facades.

	This namespace defines dynamic binding for the active runtime (*execution-context*) and
	thin facades that dispatch to runtime subprotocols in
	org.replikativ.spindel.runtime.protocols. Concrete implementations live under
	org.replikativ.spindel.runtime.impl.* (e.g., atoms, sequential, stm)."
	(:require [org.replikativ.spindel.runtime.protocols :as rtp]
	          [org.replikativ.spindel.runtime.bindings :as bindings]))

;; =============================================================================
;; Dynamic runtime execution context
;; =============================================================================

(def ^:dynamic *execution-context*
	"Dynamically bound execution context for fork-safe computation.

	ExecutionContext wraps runtime state and enables lightweight forking.
	Bind using `with-context` or `binding` for fork operations."
	nil)

(def ^:dynamic *spin-id*
	"Optionally bound current spin id during execution." nil)

(def ^:dynamic *worker-id*
	"Optionally bound worker id inside engine workers." nil)

(def ^:dynamic *yield-handler*
	"Dynamically bound yield handler for async sequence generation.

	Bound by gen-aseq to handle yield breakpoints during CPS execution." nil)

;; =============================================================================
;; CLJS Binding Registration
;; =============================================================================

;; In CLJS, we register our dynamic vars with the bindings module so they can
;; be captured/restored across async boundaries (setTimeout callbacks).
;; This avoids circular dependencies since bindings can't require core.
;;
;; NOTE: *execution-context* is NOT registered - it's bound
;; explicitly by event handlers when resuming continuations. Capturing it
;; would create circular references and cause StackOverflow.

#?(:cljs
   (do
     (bindings/register-var! #'*spin-id*)
     (bindings/register-var! #'*worker-id*)
     (bindings/register-var! #'*yield-handler*)))

;; ExecutionContext binding macros
#?(:clj
		 (defmacro with-context [ctx & body]
			 `(binding [*execution-context* ~ctx]
					~@body))
		 :cljs
		 (defn with-context [ctx f]
			 (binding [*execution-context* ctx]
				 (f))))



;; =============================================================================
;; Facades: dispatch to runtime protocols
;; =============================================================================

;; ----------------------------------------------------------------------------
;; Accessors
;; ----------------------------------------------------------------------------

(defn current-execution-context
  "Return dynamically bound execution context.

	Throws if neither is bound.

	Returns: Runtime instance (AtomsRuntime, StmRuntime) or ExecutionContext."
  []
  (or *execution-context*
      (throw (ex-info "No execution context bound. Use with-context."
                      {:hint "Bind *execution-context* using with-context"}))))

(defn execution-context-bound?
	"Check if a runtime is currently bound.

	Returns true if *execution-context* is bound, false otherwise.

	Useful for cleanup callbacks that may run after test teardown."
	[]
	(boolean *execution-context*))


;; ----------------------------------------------------------------------------
;; Graph operation helpers (dispatch to protocol when available)
;; ----------------------------------------------------------------------------

(defn graph-commit-deps!
  "Commit tracked dependencies for spin-id using the bound runtime via PGraph."
  [spin-id]
  (let [ctx (current-execution-context)]
    (rtp/record-deps! ctx spin-id)))

(defn graph-clear-deps!
  "Clear spin-id from graph using the bound runtime via PGraph."
  [spin-id]
  (let [ctx (current-execution-context)]
    (rtp/clear-deps! ctx spin-id)))

(defn graph-ordered-observers
  "Return ordered observer spin-ids for a signal-id via PGraph."
  [signal-id]
  (let [ctx (current-execution-context)]
    (rtp/ordered-observers ctx signal-id)))

;; ----------------------------------------------------------------------------
;; Transient dependency tracking (PDepsTracking)
;; ----------------------------------------------------------------------------

(defn deps-track-signal!
  "Record that the current spin observed signal-id during this turn."
  [spin-id signal-id]
  (let [ctx (current-execution-context)]
    (rtp/track-signal-dep! ctx spin-id signal-id)))

(defn deps-track-spin!
  "Record that parent spin observed child spin during this turn."
  [parent-spin-id child-spin-id]
  (let [ctx (current-execution-context)]
    (rtp/track-spin-dep! ctx parent-spin-id child-spin-id)))

;; ----------------------------------------------------------------------------
;; Spin operation facades (PSpin protocol)
;; ----------------------------------------------------------------------------

(defn spin-register! [spin-id spin-meta]
  (let [ctx (current-execution-context)]
    (rtp/register-spin! ctx spin-id spin-meta)))

(defn spin-mark-dirty! [spin-id]
  (let [ctx (current-execution-context)]
    (rtp/mark-dirty! ctx spin-id)))

(defn spin-cache-result! [spin-id result]
  (let [ctx (current-execution-context)]
    (rtp/cache-result! ctx spin-id result)))

(defn spin-current-result [spin-id]
  (let [ctx (current-execution-context)]
    (rtp/current-result ctx spin-id)))

(defn spin-result-clean?
  "Check if a spin's cached result is clean.
	Returns true if clean, false if dirty or uncached."
  [spin-id]
  (let [ctx (current-execution-context)]
    (rtp/clean? ctx spin-id)))

(defn spin-result-dirty?
  "Check if a spin's cached result is dirty.
	Returns true if dirty, false if clean or uncached."
  [spin-id]
  (let [ctx (current-execution-context)]
    (rtp/dirty? ctx spin-id)))

(defn current-spin-id
  "Get the current spin ID from dynamic binding.
	Returns nil if called outside spin context."
  []
  *spin-id*)

(defn spin-is-cancelled?
  "Check if a spin has been cancelled.
	0-arity: Check current spin via *spin-id*
	1-arity: Check specific spin-id
	Returns false if spin not found or not cancelled."
  ([]
   (when-let [spin-id *spin-id*]
     (spin-is-cancelled? spin-id)))
  ([spin-id]
   (when spin-id
     (when-let [result (spin-current-result spin-id)]
       ;; Result is a Result record with :variant and :payload
       ;; Check for cancellation error type from lifecycle/cancel-spin!
       (and (= :error (:variant result))
            (let [error (:payload result)]
              (= :org.replikativ.spindel.spin.core/spin-cancelled
                 (:type (ex-data error)))))))))

;; ----------------------------------------------------------------------------
;; Continuation facades (PContinuation)
;; ----------------------------------------------------------------------------

(defn continuation-add! [spin-id cont]
  (let [ctx (current-execution-context)
        ;; Auto-capture bindings when adding continuation
        captured-bindings (bindings/capture-bindings)
        cont-with-bindings (assoc cont :bindings captured-bindings)]
    (rtp/add-continuation! ctx spin-id cont-with-bindings)))

(defn continuation-remove! [spin-id cont-id]
  (let [ctx (current-execution-context)]
    (rtp/remove-continuation! ctx spin-id cont-id)))

(defn continuation-earliest [spin-id signal-id]
  (let [ctx (current-execution-context)]
    (rtp/earliest-continuation ctx spin-id signal-id)))

(defn continuation-resume! [spin-id cont resume-fn]
  (let [ctx (current-execution-context)]
    (rtp/resume-continuation! ctx spin-id cont resume-fn)))

;; ----------------------------------------------------------------------------
;; Engine ingress facade (PEngine)
;; ----------------------------------------------------------------------------

;; Alias for ergonomics
(defn enqueue-event!
  "Enqueue an event into the runtime engine.

  Uses current-execution-context from dynamic binding (*execution-context*).

  Events are processed by the engine's event handler, which dispatches based on :type.

  Example:
    (enqueue-event! {:type :deferred-delivery :deferred d :value 42})"
  [event]
  (let [ctx (current-execution-context)]
    (rtp/enqueue! ctx event)))

;; ----------------------------------------------------------------------------
;; General state management facades (PState)
;; ----------------------------------------------------------------------------

(defn swap-state!
  "Atomically update state at path using function f.

	Equivalent to: (swap! atom update-in path f)

	Automatically retries on conflict (like atom's swap!).
	Returns the new value at path.

	Example:
		(swap-state! [:signals sig-id]
			(fn [old-signal]
				(assoc old-signal :snapshot new-value)))"
  [path f]
  (let [ctx (current-execution-context)]
    (rtp/swap-state! ctx path f)))

(defn swap-state-args!
  "Atomically update state at path with function and args.

	Equivalent to: (apply swap! atom update-in path f args)

	Returns the new value at path.

	Example:
		(swap-state-args! [:state :atoms id :value] conj [item])"
  [path f & args]
  (let [ctx (current-execution-context)]
    (rtp/swap-state-args! ctx path f args)))

(defn get-state
  "Non-transactional read of state at path.

	For atomic read-modify-write, use swap-state! instead.

	Returns the value at path, or nil if path doesn't exist.

	Example:
		(get-state [:signals sig-id]) => {:snapshot 42 :deltas []}"
  [path]
  (let [ctx (current-execution-context)]
    (rtp/get-state ctx path)))

(defn cas-state!
  "Low-level compare-and-set for advanced CAS patterns.

	Most code should use swap-state! instead.

	Returns true if successful, false otherwise.

	Example (semaphore pattern):
		(loop []
			(let [old-state (get-state path)]
				(if (cas-state! path old-state new-state)
					:success
					(recur))))"
  [path old-val new-val]
  (let [ctx (current-execution-context)]
    (rtp/cas-state! ctx path old-val new-val)))

;; ----------------------------------------------------------------------------
;; PScheduler facades - Runtime-level scheduling control
;; ----------------------------------------------------------------------------

(defn get-executor
  "Get the executor used by this runtime for running spin functions.

	The executor determines WHERE code runs (thread pool, event loop, immediate).
	Returns an object implementing PExecutor from runtime.scheduler namespace.

	Uses current-execution-context if no runtime provided."
  ([]
   (get-executor (current-execution-context)))
  ([rt]
   (rtp/get-executor rt)))

(defn schedule-spin-execution!
  "Schedule a spin function for execution using this runtime's strategy.

	The runtime controls WHEN and WHAT to execute (scheduling strategy), while
	the executor controls WHERE it runs (thread pool, event loop, etc.).

	Uses current-execution-context if no runtime provided."
  ([spin-fn]
   (schedule-spin-execution! (current-execution-context) spin-fn))
  ([ctx spin-fn]
   (rtp/schedule-spin-execution! ctx spin-fn)))

(defn schedule-delayed-execution!
  "Schedule a spin function to execute after delay-ms milliseconds.

	Used by sleep, timeout, and other time-based operations.
	Delegates to the executor's execute-after! method.

	Uses current-execution-context if no runtime provided."
  ([delay-ms spin-fn]
   (schedule-delayed-execution! (current-execution-context) delay-ms spin-fn))
  ([ctx delay-ms spin-fn]
   (rtp/schedule-delayed-execution! ctx delay-ms spin-fn)))

;; =============================================================================
;; Event Handler Helpers
;; =============================================================================

(defn make-handler
  "Create an event handler function that auto-binds the execution context.

  Usage:
    (.addEventListener el \"click\" (make-handler ctx on-click))

  Args:
    ctx - ExecutionContext to bind
    handler-fn - Function that takes the event as argument

  Returns: Function that binds context before calling handler"
  [ctx handler-fn]
  (fn [event]
    (binding [*execution-context* ctx]
      (handler-fn event))))

