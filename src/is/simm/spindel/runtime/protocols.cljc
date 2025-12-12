(ns is.simm.spindel.runtime.protocols
  "Granular runtime subprotocols used by higher-level subsystems.

  Implementations (e.g., :atoms, :seq-volatile, :stm) can mix and match
  consistency and performance by providing these protocols. High-level code
  should call through facades in `is.simm.spindel.runtime.core`.
  ")

;; ----------------------------------------------------------------------------
;; Dependency graph and observer management
;; ----------------------------------------------------------------------------

(defprotocol PGraph
  "Operations on the dependency graph and observer sets. Implementations must
  ensure their own consistency (e.g., dosync for STM, swap! for atom runtimes)."
  (record-deps! [ctx spin-id]
    "Commit tracked dependencies for spin-id to the runtime graph, updating
     observers as needed. Clears tracking state after commit.

     Inputs: spin-id (opaque). Tracked deps are read from runtime's internal
     tracking store (implementation private).")
  (clear-deps! [ctx spin-id]
    "Remove spin-id from graph, observer sets, continuations, subscriptions.")
  (ordered-observers [ctx signal-id]
    "Return vector of spin-ids to resume for signal-id in a safe order.") )

;; ----------------------------------------------------------------------------
;; Transient dependency tracking (pre-commit)
;; ----------------------------------------------------------------------------

(defprotocol PDepsTracking
  "Record transient dependencies observed during execution. Implementations
  should accumulate these in an implementation-private tracking area which
  `record-deps!` later commits into the graph."
  (track-signal-dep! [ctx spin-id signal-id]
    "Note that spin-id observed signal-id during this turn.")
  (track-spin-dep! [ctx parent-spin-id child-spin-id]
    "Note that parent-spin-id awaits child-spin-id during this turn."))

;; ----------------------------------------------------------------------------
;; Spin lifecycle & scheduling
;; ----------------------------------------------------------------------------

(defprotocol PSpinLifecycle
  "Reactive spin lifecycle, cache and scheduling operations."
  (register-spin! [ctx spin-id spin-meta]
    "Register a Spin instance's metadata in runtime.")
  (mark-dirty! [ctx spin-id]
    "Mark spin as dirty so it recomputes on next opportunity.")
  (cache-result! [ctx spin-id result]
    "Cache spin result (Result record) and mark status as clean.")
  (current-result [ctx spin-id]
    "Return Result record or nil if not cached.")
  (clean? [ctx spin-id]
    "Return true if cached result is clean, false if dirty or uncached.")
  (dirty? [ctx spin-id]
    "Return true if cached result is dirty, false if clean or uncached.")
  (schedule-spin! [ctx spin-id]
    "Schedule a spin for execution on the runtime scheduler."))

;; ----------------------------------------------------------------------------
;; Continuations
;; ----------------------------------------------------------------------------

(defprotocol PContinuation
  "Continuation management and resumption."
  (add-continuation! [ctx spin-id cont]
    "Attach a continuation descriptor to spin-id.")
  (remove-continuation! [ctx spin-id cont-id]
    "Detach continuation by id.")
  (earliest-continuation [ctx spin-id signal-id]
    "Return earliest applicable continuation descriptor for (spin-id, signal-id), or nil.")
  (resume-continuation! [ctx spin-id cont resume-fn]
    "Invoke resume-fn in runtime context to resume continuation cont for spin-id."))

;; ----------------------------------------------------------------------------
;; Engine ingress
;; ----------------------------------------------------------------------------

(defprotocol PEngine
  "Engine/event ingress. Implementations translate domain events into work
  for their scheduling/execution model."
  (enqueue! [ctx event]
    "Enqueue a domain event like {:type :signal-change :id s} or
     {:type :spin-completion :id t}. Should be non-blocking."))

;; ----------------------------------------------------------------------------
;; Scheduling (runtime-level control over spin execution)
;; ----------------------------------------------------------------------------

(defprotocol PScheduler
  "Runtime-level scheduling control.

  The runtime controls WHEN and WHAT to execute (scheduling strategy), while
  executors (PExecutor) control WHERE code runs (thread pool, event loop, etc.).

  This separation allows the runtime to implement different scheduling strategies
  (topological order, priority queues, etc.) while keeping executor abstraction simple."

  (get-executor [rt]
    "Get the executor used by this runtime for running spin functions.

     Returns an object implementing PExecutor (from runtime.scheduler namespace).")

  (schedule-spin-execution! [ctx spin-fn]
    "Schedule a spin function for execution using this runtime's strategy.

     The runtime may:
     - Execute immediately
     - Queue for later batch execution
     - Apply priority/topological ordering
     - Use the executor to determine execution context (thread pool, etc.)

     Returns implementation-specific handle (or nil).")

  (schedule-delayed-execution! [ctx delay-ms spin-fn]
    "Schedule a spin function to execute after delay-ms milliseconds.

     Used by sleep, timeout, and other time-based operations.
     Delegates to the executor's execute-after! method.

     Returns implementation-specific handle (or nil)."))

;; ----------------------------------------------------------------------------
;; General state management with CAS semantics
;; ----------------------------------------------------------------------------

(defprotocol PState
  "General state management with atomic CAS semantics.

  Provides both high-level swap! semantics (automatic retry) and low-level
  CAS operations for advanced patterns. All state paths are vectors like
  [:signals id] or [:state :atoms id :value].

  Implementations must ensure atomicity and automatic retry for swap-state!
  operations, just like clojure.core/swap! does for atoms."

  (swap-state! [ctx path f]
    "Atomically update state at path using function f.

    Equivalent to: (swap! atom update-in path f)

    The function f receives the current value at path and returns the new value.
    If another thread modifies the path concurrently, the implementation must
    automatically retry (just like atom's swap!).

    Returns the new value at path.

    Example:
      (swap-state! ctx [:signals sig-id]
        (fn [old-signal]
          (assoc old-signal :snapshot new-value)))")

  (swap-state-args! [ctx path f args]
    "Atomically update state at path with function args.

    Equivalent to: (apply swap! atom update-in path f args)

    Like swap-state! but allows passing arguments to the function.
    Useful for applying transformations like:
      (swap-state-args! ctx [:state :atoms id :value] conj [item])

    Returns the new value at path.")

  (get-state [ctx path]
    "Non-transactional read of state at path.

    For atomic read-modify-write operations, use swap-state! instead.

    Returns the value at path, or nil if path doesn't exist.

    Example:
      (get-state ctx [:signals sig-id]) => {:snapshot 42 :deltas []}")

  (cas-state! [ctx path old-val new-val]
    "Low-level compare-and-set for advanced CAS patterns.

    Only needed for patterns like semaphore.cljc that require explicit
    retry logic with decisions based on conflict detection.

    Most code should use swap-state! instead, which handles retries automatically.

    Returns true if the CAS succeeded, false if the current value at path
    didn't match old-val.

    Example (semaphore pattern):
      (loop []
        (let [old-state (get-state ctx path)]
          (if (cas-state! ctx path old-state new-state)
            :success
            (recur))))"))