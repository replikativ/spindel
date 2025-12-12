(ns is.simm.spindel.runtime.node-protocols
  "Protocols for unified reactive nodes.

  This namespace defines fine-grained protocols for the unified :nodes structure
  that replaces separate :signals, :spins, :graph, and :spin-observers maps.

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
  - Content-addressed caching (deps-hash from dependency VALUES)
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
    deps format: {:signals #{sig-id ...} :spins #{spin-id ...}}")

  (get-deps-hash [node]
    "Returns content hash of dependency values (UUID).

    This is the key to content-addressed caching!
    Hash is computed from actual VALUES of dependencies, not just IDs.

    Same deps-hash = same dependency values = can reuse cached result.
    Different deps-hash = different dependency values = must re-execute.")

  (set-deps-hash [node hash]
    "Returns new node with updated deps-hash.

    Called by record-deps! after computing hash from dependency values.
    Hash is a UUID from hasch library (collision-resistant).")

  (get-deps-values [node]
    "Returns captured dependency generations/hashes for identity-based caching.

    Format: {:signal-generations {sig-id generation ...} :spin-hashes {spin-id deps-hash ...}}

    These GENERATIONS are used to compute deps-hash in O(1) time per dependency.
    Stored for debugging and cache identity verification."))

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
