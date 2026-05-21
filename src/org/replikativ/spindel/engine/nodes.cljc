(ns org.replikativ.spindel.engine.nodes
  "Protocols and type implementations for unified reactive nodes.

  This namespace defines fine-grained protocols for the unified :nodes structure
  that replaces separate :signals, :spins, :graph, and :spin-observers maps,
  plus the defrecord implementations (SignalNode, SpinNode) and constructors.

  Following spindel's protocol philosophy:
  - Fine-grained protocols (not monolithic interfaces)
  - Composability (not all nodes need all capabilities)
  - Clear responsibilities (each protocol has focused purpose)
  - Future-proof (new node types can implement subsets)")

;; =============================================================================
;; Core Node Protocol
;; =============================================================================

(defprotocol PNode
  "Core node identity and value access.

  All nodes in the unified reactive graph implement this protocol.
  Provides type discrimination and value access."

  (node-type [node]
    "Returns node type keyword: :signal or :spin.

    This replaces the old pattern of checking map keys like [:type :signal].
    Protocol dispatch provides type safety and better performance.")

  (get-value [node]
    "Get current value from the node.

    For signals: returns snapshot (current value)
    For spins: returns Result record (cached result)"))

;; =============================================================================
;; Observable Protocol
;; =============================================================================

(defprotocol PObservable
  "Nodes can be observed for changes.

  Both signals and spins support observers - spins that depend on them.
  When a node changes, observers are notified via topological ordering."

  (get-observers [node]
    "Returns set of observer node IDs.

    Observer IDs are spin-ids of spins that depend on this node.
    Used by engine for topological notification.")

  (add-observer [node observer-id]
    "Returns new node with observer added.

    Protocol methods are PURE - return new node, don't mutate.
    Runtime handles actual state updates via swap-node!.")

  (remove-observer [node observer-id]
    "Returns new node with observer removed.

    Protocol methods are PURE - return new node, don't mutate.
    Runtime handles actual state updates via swap-node!."))

;; =============================================================================
;; Dependent Protocol
;; =============================================================================

(defprotocol PDependent
  "Nodes can depend on other nodes.

  Spins have dependencies (signals and other spins they read).
  Signals have no dependencies (they are sources).

  Dependencies are tracked during spin execution and used for:
  - Dirty propagation (when signal changes, mark dependent spins dirty)
  - Topological ordering (ensure correct execution order)"

  (has-deps? [node]
    "Returns true if node has dependencies.

    Signals always return false (no dependencies).
    Spins return true if they depend on any signals or spins.")

  (get-deps [node]
    "Returns dependency map {:signals #{...} :spins #{...}}.

    Signal dependencies: IDs of signals read via (track sig)
    Spin dependencies: IDs of spins read via (await spin)

    Used by dirty propagation and topological ordering.")

  (set-deps [node deps]
    "Returns new node with updated dependencies.

    Called by record-deps! after spin execution completes.
    deps format: {:signals #{sig-id ...} :spins #{spin-id ...}}"))

;; =============================================================================
;; Cacheable Protocol
;; =============================================================================

(defprotocol PCacheable
  "Nodes can cache computation results.

  Spins cache their execution results and track dirty/clean state.
  Signals don't cache (their snapshot IS the authoritative value).

  Cache invalidation:
  - When signal changes, mark dependent spins :dirty
  - Dirty spins re-execute on next access
  - After re-execution, mark :clean and update cached result"

  (dirty? [node]
    "Returns true if cached value is stale.

    For spins: true if dependencies changed since last execution
    For signals: always false (snapshot is always current)")

  (clean? [node]
    "Returns true if cached value is valid.

    For spins: true if dependencies unchanged, can use cached result
    For signals: always true (snapshot is always valid)")

  (mark-dirty [node]
    "Returns new node marked as dirty.

    Called when a dependency changes (signal update or upstream spin completion).
    Indicates cached result is stale, must re-execute on next access.")

  (mark-clean [node]
    "Returns new node marked as clean.

    Called after spin execution completes successfully.
    Indicates cached result is valid, can be reused."))

;; =============================================================================
;; SignalNode - Mutable Reactive Sources
;; =============================================================================

(defrecord SignalNode [snapshot          ; Current value
                       old-snapshot      ; Previous value (for dual perspective)
                       deltas            ; Structural changes (for deltaable collections)
                       deltaable?        ; Can track deltas?
                       observers         ; Set of observer node IDs
                       generation]       ; Monotonically increasing counter (for O(1) cache identity)

  PNode
  (node-type [_] :signal)
  (get-value [_] snapshot)

  PObservable
  (get-observers [_] observers)
  (add-observer [this obs-id]
    (assoc this :observers (conj observers obs-id)))
  (remove-observer [this obs-id]
    (assoc this :observers (disj observers obs-id)))

  PDependent
  ;; Signals have no dependencies - they are sources
  (has-deps? [_] false)
  (get-deps [_] {:signals #{} :spins #{}})
  (set-deps [this _] this)  ; No-op for signals

  PCacheable
  ;; Signals don't have dirty state - snapshot is always authoritative
  (dirty? [_] false)
  (clean? [_] true)   ; Always "clean" (current value is authoritative)
  (mark-dirty [this] this)
  (mark-clean [this] this))

;; =============================================================================
;; SpinNode - Cached Reactive Computations
;; =============================================================================

(defrecord SpinNode [result              ; Cached result (Result record)
                     status              ; :clean or :dirty
                     completed?          ; Has spin finished?
                     running?            ; Is spin executing?
                     observers           ; Set of observer node IDs
                     deps                ; {:signals #{...} :spins #{...}}
                     created-by          ; spin-id that created this spin (nil for top-level)
                     created-spins        ; Set of spin-ids created during this spin's execution
                     kind]                ; :computation (deterministic id, replayable, B-gated)
                                          ; | :resource (gensym id, effectful one-shot body)

  PNode
  (node-type [_] :spin)
  (get-value [_] result)

  PObservable
  (get-observers [_] observers)
  (add-observer [this obs-id]
    (assoc this :observers (conj observers obs-id)))
  (remove-observer [this obs-id]
    (assoc this :observers (disj observers obs-id)))

  PDependent
  (has-deps? [_] (boolean (or (seq (:signals deps)) (seq (:spins deps)))))
  (get-deps [_] deps)
  (set-deps [this new-deps]
    (assoc this :deps new-deps))

  PCacheable
  (dirty? [_] (= status :dirty))
  (clean? [_] (= status :clean))
  (mark-dirty [this]
    (assoc this :status :dirty))
  (mark-clean [this]
    (assoc this :status :clean)))

;; =============================================================================
;; Constructor Functions
;; =============================================================================

(defn ->signal-node
  "Create a new SignalNode.

  Parameters:
  - snapshot: Current value
  - old-snapshot: Previous value (for dual perspective)
  - deltas: Structural changes (for deltaable collections)
  - deltaable?: Can track deltas?
  - observers: Set of observer node IDs (defaults to empty set)
  - generation: Monotonically increasing counter (defaults to 0)

  Example:
    (->signal-node 42 nil [] false #{})
    (->signal-node [1 2 3] [1 2] [{:op :conj :value 3}] true #{:spin-1})"
  ([snapshot old-snapshot deltas deltaable?]
   (->signal-node snapshot old-snapshot deltas deltaable? #{} 0))
  ([snapshot old-snapshot deltas deltaable? observers]
   (->signal-node snapshot old-snapshot deltas deltaable? observers 0))
  ([snapshot old-snapshot deltas deltaable? observers generation]
   (->SignalNode snapshot old-snapshot deltas deltaable? observers generation)))

(defn ->spin-node
  "Create a new SpinNode.

  Parameters:
  - result: Cached result (Result record)
  - status: :clean or :dirty
  - completed?: Has spin finished?
  - running?: Is spin executing?
  - observers: Set of observer node IDs
  - deps: {:signals #{...} :spins #{...}} (normalized to proper structure)
  - created-by: spin-id that created this spin (nil for top-level)
  - created-spins: Set of spin-ids created during this spin's execution

  Example:
    (->spin-node nil :clean false false #{} {} nil #{})
    (->spin-node (result/ok 42) :clean true false #{:spin-2}
                 {:signals #{:sig-1} :spins #{}}
                 :parent-spin #{:child-1 :child-2})"
  [result status completed? running? observers deps created-by created-spins]
  (let [;; Normalize deps to ensure proper structure
        normalized-deps (if (and (map? deps)
                                 (or (contains? deps :signals)
                                     (contains? deps :spins)))
                          deps
                          {:signals #{} :spins #{}})]
    (->SpinNode result status completed? running? observers
                normalized-deps
                created-by (or created-spins #{})
                ;; :kind defaults to :computation here; make-spin and
                ;; register-spin! set the real kind on the node. The other
                ;; ->spin-node call sites build transient/default nodes.
                :computation)))
