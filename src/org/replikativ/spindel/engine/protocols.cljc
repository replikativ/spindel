(ns org.replikativ.spindel.engine.protocols
  "Granular runtime subprotocols used by higher-level subsystems.

  Implementations (e.g., :atoms, :seq-volatile, :stm) can mix and match
  consistency and performance by providing these protocols. High-level code
  should call through facades in `org.replikativ.spindel.engine.core`.
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
    "Return vector of spin-ids to resume for signal-id in a safe order."))

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
    "Return true if cached result is dirty, false if clean or uncached."))

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

;; ----------------------------------------------------------------------------
;; External references (forkable resources)
;; ----------------------------------------------------------------------------

(defprotocol PForkable
  "Protocol for a SIGNAL VALUE that needs explicit forking when its host context
  forks — a reference to external mutable state (a yggdrasil system) that the
  overlay backend's copy-on-write does NOT isolate by itself, because the value
  is a handle onto a shared store (a git repo, a datahike conn, a konserve CRDT).

  When an ExecutionContext is forked, every signal whose id is in
  [:forkable-signals] is forked by calling `fork-value` on its current value and
  writing the result as the fork-local signal node. Pure signal values (numbers,
  maps, …) are NOT in that set and fall through the overlay unchanged.

  Implementations should:
  - Return a NEW value representing the isolated fork (an Overlay or a branched
    system); NOT mutate the original (value semantics)
  - Create any necessary underlying resources (a git worktree, a datahike branch,
    a CRDT clone)

  yggdrasil extends this for its systems + overlays; the default is identity."

  (fork-value [this fork-id directive]
    "Fork this signal value for a child context.

    Arguments:
      this      - the current signal value (a yggdrasil system or overlay)
      fork-id   - unique id for this fork (keyword), for naming resources
      directive - how to fork, generic so the engine stays yggdrasil-free:
                    {:fork :overlay :mode :following|:frozen}  ; from CURRENT head
                    {:fork :snapshot :snapshot <snapshot-id>}  ; from a FIXED value

    Returns the forked value. Must not mutate the original."))

(extend-protocol PForkable
  #?(:clj Object :cljs default)
  ;; A plain value has no external state to isolate — the overlay backend's CoW
  ;; already gives the fork its own copy, so forking the value is identity.
  (fork-value [this _fork-id _directive] this)

  nil
  (fork-value [_ _ _] nil))