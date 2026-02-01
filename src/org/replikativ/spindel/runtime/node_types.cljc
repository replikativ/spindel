(ns org.replikativ.spindel.runtime.node-types
  "Node type implementations for unified reactive graph.

  Defines SignalNode and SpinNode defrecords that implement the
  node protocols (PNode, PObservable, PDependent, PCacheable).

  These replace the old pattern of storing plain maps in separate
  :signals and :spins structures."
  (:require [org.replikativ.spindel.runtime.node-protocols :as np]))

;; =============================================================================
;; SignalNode - Mutable Reactive Sources
;; =============================================================================

(defrecord SignalNode [snapshot          ; Current value
                       old-snapshot      ; Previous value (for dual perspective)
                       deltas            ; Structural changes (for deltaable collections)
                       deltaable?        ; Can track deltas?
                       observers         ; Set of observer node IDs
                       generation]       ; Monotonically increasing counter (for O(1) cache identity)

  np/PNode
  (node-type [_] :signal)
  (get-value [_] snapshot)

  np/PObservable
  (get-observers [_] observers)
  (add-observer [this obs-id]
    (assoc this :observers (conj observers obs-id)))
  (remove-observer [this obs-id]
    (assoc this :observers (disj observers obs-id)))

  np/PDependent
  ;; Signals have no dependencies - they are sources
  (has-deps? [_] false)
  (get-deps [_] {:signals #{} :spins #{}})
  (set-deps [this _] this)  ; No-op for signals
  (get-deps-hash [_] nil)
  (set-deps-hash [this _] this)
  (get-deps-values [_] {:signal-generations {} :spin-hashes {}})

  np/PCacheable
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
                     deps-hash           ; Identity hash from dependency GENERATIONS (O(1))
                     deps-values         ; {:signal-generations {...} :spin-hashes {...}}
                     created-by          ; spin-id that created this spin (nil for top-level)
                     created-spins]      ; Set of spin-ids created during this spin's execution

  np/PNode
  (node-type [_] :spin)
  (get-value [_] result)

  np/PObservable
  (get-observers [_] observers)
  (add-observer [this obs-id]
    (assoc this :observers (conj observers obs-id)))
  (remove-observer [this obs-id]
    (assoc this :observers (disj observers obs-id)))

  np/PDependent
  (has-deps? [_] (boolean (or (seq (:signals deps)) (seq (:spins deps)))))
  (get-deps [_] deps)
  (set-deps [this new-deps]
    (assoc this :deps new-deps))
  (get-deps-hash [_] deps-hash)
  (set-deps-hash [this hash]
    (assoc this :deps-hash hash))
  (get-deps-values [_] deps-values)

  np/PCacheable
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
  - deps-hash: Identity hash from dependency GENERATIONS (UUID)
  - deps-values: {:signal-generations {...} :spin-hashes {...}} (normalized to proper structure)
  - created-by: spin-id that created this spin (nil for top-level)
  - created-spins: Set of spin-ids created during this spin's execution

  Example:
    (->spin-node nil :clean false false #{} {} nil {} nil #{})
    (->spin-node (result/ok 42) :clean true false #{:spin-2}
                 {:signals #{:sig-1} :spins #{}}
                 #uuid \"...\"
                 {:signal-generations {:sig-1 5} :spin-hashes {:spin-2 #uuid \"...\"}}
                 :parent-spin #{:child-1 :child-2})"
  [result status completed? running? observers deps deps-hash deps-values created-by created-spins]
  (let [;; Normalize deps to ensure proper structure
        normalized-deps (if (and (map? deps)
                                 (or (contains? deps :signals)
                                     (contains? deps :spins)))
                          deps
                          {:signals #{} :spins #{}})
        ;; Normalize deps-values to ensure proper structure
        normalized-deps-values (if (and (map? deps-values)
                                        (or (contains? deps-values :signal-generations)
                                            (contains? deps-values :spin-hashes)))
                                 deps-values
                                 {:signal-generations {} :spin-hashes {}})]
    (->SpinNode result status completed? running? observers
                normalized-deps deps-hash normalized-deps-values
                created-by (or created-spins #{}))))
