(ns org.replikativ.spindel.engine.protocols
  "Granular runtime subprotocols used by higher-level subsystems.

  Implementations (e.g., :atoms, :seq-volatile, :stm) can mix and match
  consistency and performance by providing these protocols. High-level code
  should call through facades in `org.replikativ.spindel.engine.core`.
  ")

;; ----------------------------------------------------------------------------
;; Dependency graph and observer management
;; ----------------------------------------------------------------------------

(defprotocol PWorldIdentity
  "Stable non-nil identity of an execution world. Lexical context derivatives
   preserve it; forks and restored worlds have distinct identities even when
   they share a physical store. Identity must not retain the world itself."
  (world-identity [ctx]))

;; Existing contexts have a distinct backend per world. Native contexts can
;; implement this protocol with a separate identity for a shared family store.
(extend-protocol PWorldIdentity
  #?(:clj Object :cljs default)
  (world-identity [ctx] (:backend ctx)))

(defprotocol PExecutionScopes
  "World-local execution ownership; physical join observes only this world."
  (root-execution-owner [context])
  (current-execution-owner [context])
  (open-execution-scope! [context kind parent])
  (bindable-execution-owner [context owner])
  (capture-execution-owner [context owner])
  (restore-execution-owner [context captured current])
  (close-execution-scope! [context scope])
  (execution-owner-joined? [context owner]))

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
  (cache-result! [ctx spin-id result] [ctx spin-id result run]
    "Cache spin result (Result record) and mark status as clean. With `run`
    (the run generation `enter-body!` returned), certify it clean only if
    that run was not invalidated; returns false for a superseded run's
    completion, which changes nothing.")
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
    [ctx spin-id cont-id opts]
    "Atomically detach and return a continuation by id, or nil when already
     absent. With `{:cancel? true}`, arm a state-backed external-await token in
     the same transaction so external delivery cannot race cancellation.")
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
  "Protocol for a WORLD-BOUND VALUE that needs explicit forking when its host
  context forks. This includes signal values that reference external mutable
  state (a yggdrasil system) and non-reactive world components such as an
  interpreter heap that the overlay backend's copy-on-write cannot isolate.

  When an ExecutionContext is forked, registered forkable signals and world
  components call `fork-value`; their results are seated in the child context.
  Pure values (numbers, maps, …) are not registered and fall through unchanged.

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
                    {:fork :snapshot :snapshot <snapshot-id>}  ; from a FIXED logical value
                    {:fork :checkpoint :checkpoint <origin>}   ; exact physical repository basis

    Returns the forked VALUE synchronously, never a deferred/CPS operation.
    Historical origin validation/retention belongs to the host bridge.
    Must not mutate the original."))

(extend-protocol PForkable
  #?(:clj Object :cljs default)
  ;; A plain value has no external state to isolate — the overlay backend's CoW
  ;; already gives the fork its own copy, so forking the value is identity.
  (fork-value [this _fork-id _directive] this)

  nil
  (fork-value [_ _ _] nil))

(defprotocol PRuntimeCells
  "Typed lifecycle and value operations for aliasable, world-selected cells.
   Allocation IDs are globally fresh and never reused. Runtime metadata and
   listener registration remain engine-owned; application values are opaque.
   An allocation returns {:id id :anchor anchor}; wrappers retain the anchor,
   never a runtime. Updates notify only after commit and outside mutation gates."
  (allocate-runtime-cell! [ctx value options])
  (runtime-cell-present? [ctx id])
  (runtime-cell-value [ctx id])
  (runtime-cell-meta [ctx id])
  (runtime-cell-watches [ctx id])
  (swap-runtime-cell! [ctx ref id f args])
  (cas-runtime-cell! [ctx ref id old-value new-value])
  (add-runtime-cell-watch! [ctx id key f])
  (remove-runtime-cell-watch! [ctx id key]))

(defprotocol PTraceAddressing
  "Atomic deterministic construction addressing owned by the selected engine.
   A matching ordinary activation advances its run cursor; otherwise the
   requested world's root cursor is used after caller admission."
  (next-trace-address! [ctx prefix source-loc]))

(defprotocol PComputations
  "Public computation ingress. Bodies carry immutable constructor data under
   ::computation in their metadata. Engines own registration, generations and
   result arbitration; generic state paths cannot mutate that authority."
  (register-computation! [ctx target id body])
  (invoke-computation! [ctx target id body resolve reject mode]
    "Invoke with :callback or one-shot :deref observation. Preserve the public
     CPS return convention: value/Thunk for inline success, incomplete when
     suspended, and the existing cached-error rejection convention.")
  (cancel-computation! [ctx target id body reason])
  (computation-result [ctx target id]
    "Immutable {:variant :ok|:error :payload value :clean? boolean}, or nil.")
  (deref-computation! [ctx target id body timeout-ms timeout-val]
    "JVM host blocking adapter; refuse an engine activation or drain.
     ClojureScript blocking deref remains unsupported."))

(defprotocol PComputationAwait
  "Await ingress before any engine-specific cancellation or state access.
   A reactive target supplies id/body; other awaitables supply nil for both."
  (await-computation! [ctx target id body caller-id source-loc resolve reject])
  (await-computation-finalization! [ctx operation caller-id source-loc resolve reject]
    "Protected finalizer wait; retirement must preserve its physical return."))

(defprotocol PSignals
  "Public signal ingress. References retain engine allocation metadata unchanged.
   State reads return an immutable SignalNode-shaped value with :snapshot,
   :old-snapshot, :deltas, :deltaable?, :observers and :generation. Reads must
   not recreate a retired native allocation. Mutations publish after commit;
   publish? false defers reactive publication, but still notifies watches."
  (register-public-signal! [ctx ref])
  (public-signal-state [ctx ref])
  (public-signal-value [ctx ref]
    "Read the raw current value without constructing a diagnostic state view.")
  (swap-public-signal! [ctx ref f args publish? committed observe-change?]
    "Return {:value clean-value :changed? boolean-or-nil}. Compute value equality
     only when observe-change? is true. If non-nil, invoke the
     zero-argument committed callback once after successful commit, outside
     mutation gates and before publication or watch delivery.")
  (cas-public-signal! [ctx ref old-value new-value publish?])
  (clear-public-signal-deltas! [ctx ref])
  (public-signal-watches [ctx ref])
  (add-public-signal-watch! [ctx ref key f])
  (remove-public-signal-watch! [ctx ref key])
  (publish-public-signals! [ctx ids]
    "Publish committed values for distinct IDs in order as one batch."))

(defprotocol PSignalTracking
  "Signal checkpoint ingress, before engine-specific cancellation/state access."
  (track-public-signal! [ctx ref spin-id source-loc resolve reject]))

(defprotocol PDeferred
  "A Deferred's opaque synchronization payload, interpreted by its runtime."
  (deferred-payload [this]))

(defprotocol PSynchronization
  "Typed single-assignment synchronization ingress. Operations select the
   bound world; a reference does not retain or select its creation world.
   Delivered values, including exceptions, are successful application data."
  (create-public-deferred! [ctx id])
  (claim-public-deferred! [ctx ref value]
    "Claim callable delivery once and return the claim winner boolean.")
  (deliver-public-deferred! [ctx ref value]
    "Queue an assignment attempt without claiming; return the supplied value.")
  (read-public-deferred [ctx ref]
    "Immutable {:assigned? boolean :value value}; nil/false are valid values.")
  (invoke-public-deferred! [ctx ref resolve reject]
    "Direct two-argument Deferred CPS invocation."))

(defprotocol PMailbox
  "A Mailbox's opaque synchronization payload, interpreted by its runtime."
  (mailbox-payload [this]))

(defprotocol PMailboxNext
  "Typed callable next step of a Mailbox, yielding [message same-mailbox]."
  (mailbox-next-target [this]))

(defprotocol PMailboxSynchronization
  "World-selected FIFO message delivery. Message selection reserves a value;
   cancelling an unclaimed reservation returns it once. A physical inline claim
   preserves its single entry on the existing frame across cancellation."
  (create-public-mailbox! [ctx id])
  (post-public-mailbox! [ctx ref value]
    "Queue a message and return nil; messages have no error disposition.")
  (take-public-mailbox-now! [ctx ref consumer-id]
    "Immediate {:available? boolean :value value} without a pending consumer.")
  (invoke-public-mailbox! [ctx ref resolve reject]
    "Direct two-argument Mailbox CPS invocation.")
  (invoke-public-mailbox-next! [ctx ref resolve reject]
    "Callable next step, preserving CPS return values and yielding [value ref]."))

(defprotocol PTimers
  "Typed timer waits owned by an admitted ordinary computation. Logical
   cancellation revokes callback admission; physical return is separate evidence."
  (await-public-timer! [ctx delay-ms value resolve reject]
    "Park the current computation until its timer fires with successful value.
     Registration and callback admission use the selected world and generation."))

(defprotocol PWorldLifecycle
  "Logical world release and asynchronous observation of physical completion.
   Releasing a world does not close borrowed executors."
  (request-world-release! [ctx reason]
    "Close ordinary admission immediately and return the world's stable typed
     completion. Repeated requests preserve the first reason and completion.")
  (observe-world-release! [ctx receipt resolve reject]
    "Observe an authenticated release receipt. Return an idempotent detach
     function; detaching never cancels cleanup. Callbacks run outside the gate.
     Success is nil and certifies actual physical return, not a timeout."))

(defprotocol PWorldRelease
  "Typed release completion, outside the released world's source graph."
  (release-runtime [completion])
  (release-receipt [completion]))
