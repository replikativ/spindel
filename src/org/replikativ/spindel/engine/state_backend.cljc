(ns org.replikativ.spindel.engine.state-backend
  "State backend abstraction for ExecutionContext.

  Provides pluggable storage strategies:
  - AtomBackend: Default async state (atom-based)
  - RefBackend: STM transactional state (ref-based, JVM only)
  - ImmutableBackend: Readonly snapshots (serializable)
  - OverlayBackend: Fork with delta storage (memory efficient)"
  (:require [incognito.edn :refer [read-string-safe]]))

;; =============================================================================
;; Protocol
;; =============================================================================

(defprotocol PStateBackend
  "Abstraction over state storage strategy."

  (backend-read [backend path]
    "Read value at path. Returns value or nil if not found.")

  (backend-write! [backend path f]
    "Apply function f to value at path, store result, return new value.

    For empty path, f is applied to entire state.
    For non-empty path, f is applied to value at path.")

  (backend-write-2! [backend path-a path-b f2]
    "Atomically transform the values at TWO paths in one commit.

    `f2` receives the current values `[a b]` and returns `[a' b']`;
    both are written in the same atomic state transition. This is the
    transactional-handoff primitive (issue #27 Phase C): popping a
    waiter from a primitive's state and appending its resume event to
    `[:engine/pending]` must be ONE transition, so a wakeup obligation
    is never in zero places (lost) or two places (double delivery).

    `f2` may be retried (CAS semantics) — it must be pure apart from
    idempotent volatile! captures. Returns nil.

    A single-function two-path op (not independent per-path fns)
    because the second write depends on the first's outcome: whether a
    waiter was popped decides whether an event is appended.")

  (backend-deref [backend]
    "Dereference entire state map (for inspection/serialization).")

  (backend-type [backend]
    "Return backend type keyword (:atom, :ref, :immutable, :overlay)."))

;; =============================================================================
;; AtomBackend - Default async state
;; =============================================================================

(defrecord AtomBackend [state-atom]
  PStateBackend

  (backend-read [_ path]
    (get-in @state-atom path))

  (backend-write! [_ path f]
    (if (empty? path)
      ;; Swap entire state
      (swap! state-atom f)
      ;; Swap at path
      (get-in (swap! state-atom update-in path f) path)))

  (backend-write-2! [_ path-a path-b f2]
    (swap! state-atom
           (fn [m]
             (let [[a' b'] (f2 (get-in m path-a) (get-in m path-b))]
               (-> m
                   (assoc-in path-a a')
                   (assoc-in path-b b')))))
    nil)

  (backend-deref [_]
    @state-atom)

  (backend-type [_]
    :atom))

(defn create-atom-backend
  "Create AtomBackend with initial state."
  [initial-state]
  (->AtomBackend (atom initial-state)))

;; =============================================================================
;; OverlayBackend - Fork with delta storage
;; =============================================================================

(def default-fork-local-paths
  "Default set of fork-local paths that don't fall back to parent.

  Fork-local state:
  - :track-subscriptions / :await-conts - Continuations specific to this fork
  - :engine/* - Engine execution state (pending queue, draining flag, timers)

  Shared state (falls back to parent):
  - :nodes - Signal and spin nodes (shared observer graph for reactive invalidation)
  - :spin-tracking - Dependency tracking (transient accumulator)
  - :subscriptions - Event subscriptions
  - :atoms - Runtime atoms

  :listeners is fork-local AND deliberately NOT copied into a fork by
  `fork-context` (unlike :await-conts) — so a fork starts with ZERO listeners.
  This is load-bearing: a listener is side-effecting egress (publish/notify), so a
  fork must not inherit-then-fire the parent's listener on a fork-private mutation
  (that would leak speculative state). A fork that wants to egress adds its own."
  #{:track-subscriptions :await-conts :engine/pending :engine/draining?
    :engine/delayed-spins :engine/timer-handles :listeners})

(defn fork-local-path?
  "Check if path is fork-local (should not fall back to parent).

  Uses the provided local-paths set or defaults to `default-fork-local-paths`."
  ([first-key]
   (fork-local-path? first-key default-fork-local-paths))
  ([first-key local-paths]
   (contains? local-paths first-key)))

(defrecord OverlayBackend [overlay-atom parent-backend local-paths]
  PStateBackend

  (backend-read [_this path]
    ;; Special handling for fork-local state (don't fall back to parent)
    (if (and (seq path) (fork-local-path? (first path) local-paths))
      ;; Fork-local: overlay only, no parent fallback
      (get-in @overlay-atom path)
      ;; Shared state: check overlay, fall back to parent
      (let [overlay-val (get-in @overlay-atom path ::not-found)]
        (if (not= overlay-val ::not-found)
          overlay-val
          (when parent-backend
            (backend-read parent-backend path))))))

  (backend-write! [this path f]
    ;; All writes go to overlay
    ;; CRITICAL: For shared state, use copy-on-write at entity level (e.g., full node)
    (if (empty? path)
      ;; Empty path = full state transaction
      ;; Detect changes at ENTITY level (depth 2) to preserve sparse overlay
      (let [parent-state (when parent-backend (backend-deref parent-backend))
            overlay-state @overlay-atom
            ;; Deep merge: overlay entities override parent entities
            merged (merge-with (fn [parent-val overlay-val]
                                 (if (and (map? parent-val) (map? overlay-val))
                                   (merge parent-val overlay-val)
                                   overlay-val))
                               parent-state
                               overlay-state)
            ;; Apply function to merged view
            new-state (f merged)
            ;; Find changed ENTITIES (depth 2: [:nodes spin-1], [:signals sig-1])
            ;; not just changed top-level keys (depth 1: :nodes, :signals)
            changed-entities (reduce
                              (fn [acc top-key]
                                (let [old-map (get merged top-key)
                                      new-map (get new-state top-key)]
                                  (if (and (map? old-map) (map? new-map))
                                    ;; Both are maps - check entity-level changes
                                    (reduce (fn [acc2 entity-id]
                                              (let [old-entity (get old-map entity-id)
                                                    new-entity (get new-map entity-id)]
                                                (if (not= old-entity new-entity)
                                                  (conj acc2 [[top-key entity-id] new-entity])
                                                  acc2)))
                                            acc
                                            (keys new-map))
                                    ;; Not entity maps - write whole top-level value if changed
                                    (if (not= old-map new-map)
                                      (conj acc [[top-key] new-map])
                                      acc))))
                              []
                              (keys new-state))]
        ;; Write only changed entities to overlay (preserves sparseness!)
        (swap! overlay-atom
               (fn [ov]
                 (reduce (fn [acc [path val]]
                           (assoc-in acc path val))
                         ov
                         changed-entities)))
        new-state)

      ;; Non-empty path
      ;; CRITICAL: All writes must be atomic (f runs inside swap!) to prevent
      ;; concurrent read-modify-write races on the overlay atom.
      ;; The previous read-outside/write-inside pattern lost events when
      ;; concurrent threads (drain + enqueue) modified the same fork-local path.
      (let [is-shared? (not (fork-local-path? (first path) local-paths))
            path-depth (count path)]

        (cond
          (and is-shared? (>= path-depth 2))
          ;; Shared path with depth ≥ 2: Copy-on-write at entity level
          ;; e.g., [:nodes spin-1 :dirty?] → copy entire [:nodes spin-1] node
          (let [entity-path (vec (take 2 path))  ;; Entity = top two levels (e.g., [:nodes spin-1])
                field-path (vec (drop 2 path))]  ;; Field within entity (e.g., [:dirty?])

            ;; Atomic copy-on-write + update in single swap!
            (get-in
             (swap! overlay-atom
                    (fn [ov]
                      (let [entity-in-overlay? (not= ::not-found
                                                     (get-in ov entity-path ::not-found))
                        ;; If entity not in overlay, copy from parent first
                            ov (if entity-in-overlay?
                                 ov
                                 (if-let [parent-entity (when parent-backend
                                                          (backend-read parent-backend entity-path))]
                                   (assoc-in ov entity-path parent-entity)
                                   ov))
                        ;; Now apply f to the current value at path
                            current (get-in ov path)
                            new-val (f current)]
                        (assoc-in ov path new-val))))
             path))

          (and is-shared? parent-backend)
          ;; Shared depth-1 path: seed the overlay with parent's current
          ;; value on first write, then apply f. Without this seeding,
          ;; (swap! overlay-atom update-in path f) would call f with nil
          ;; (overlay is empty at this path), and whatever f returns
          ;; would shadow parent for all future reads via this fork.
          ;; That's the depth-1 analogue of the depth-≥2 CoW above —
          ;; fork's first write would silently discard parent's value
          ;; instead of extending it.
          ;;
          ;; Concretely, this matters for accumulator-style depth-1
          ;; paths like :engine/cancelled-tokens (a set of UUIDs
          ;; describing which external-await gates have been tripped).
          ;; Parent may have tripped {A}; without seeding, fork's first
          ;; trip would land #{B} in fork's overlay and the orphaned
          ;; closure for A would fire in fork's drain.
          ;;
          ;; Once seeded, fork's overlay has its own copy and parent's
          ;; later additions are NOT visible to fork — fork has CoW'd
          ;; the path. This matches the depth-≥2 CoW divergence
          ;; semantic and is the property tests like
          ;; `fork-isolated-cancellation` rely on.
          (get-in
           (swap! overlay-atom
                  (fn [ov]
                    (let [overlay-has? (not= ::not-found
                                             (get-in ov path ::not-found))
                          ov (if overlay-has?
                               ov
                               (if-some [parent-val (backend-read parent-backend path)]
                                 (assoc-in ov path parent-val)
                                 ov))]
                      (assoc-in ov path (f (get-in ov path))))))
           path)

          :else
          ;; Fork-local path (no parent fallback by design) or root
          ;; backend (no parent): direct write.
          (get-in
           (swap! overlay-atom update-in path f)
           path)))))

  (backend-write-2! [_ path-a path-b f2]
    ;; Both paths committed in ONE swap on the overlay atom — atomic
    ;; within this fork. Shared paths are CoW-seeded from the parent
    ;; exactly like backend-write!'s single-path branches (entity level
    ;; for depth ≥ 2, whole value for depth 1); fork-local paths write
    ;; directly. After seeding, the fork has diverged from the parent's
    ;; copy — the standard overlay CoW semantic.
    (letfn [(seed [ov path]
              (if (or (fork-local-path? (first path) local-paths)
                      (nil? parent-backend))
                ov
                (let [seed-path (if (>= (count path) 2)
                                  (vec (take 2 path)) ;; entity-level CoW
                                  path)]
                  (if (not= ::not-found (get-in ov seed-path ::not-found))
                    ov
                    (if-some [parent-val (backend-read parent-backend seed-path)]
                      (assoc-in ov seed-path parent-val)
                      ov)))))]
      (swap! overlay-atom
             (fn [ov]
               (let [ov (-> ov (seed path-a) (seed path-b))
                     [a' b'] (f2 (get-in ov path-a) (get-in ov path-b))]
                 (-> ov
                     (assoc-in path-a a')
                     (assoc-in path-b b'))))))
    nil)

  (backend-deref [_]
    ;; Return overlay only (not merged with parent)
    ;; This is intentional - deref shows what's in this layer
    @overlay-atom)

  (backend-type [_]
    :overlay))

(defn create-overlay-backend
  "Create OverlayBackend with empty overlay over parent backend.

  Args:
    parent-backend - The parent backend to delegate reads to for shared state
    initial-overlay - Initial overlay state map (default: {})
    local-paths - Set of path keys that are fork-local and don't fall back to parent
                  (default: default-fork-local-paths)"
  ([parent-backend]
   (create-overlay-backend parent-backend {} default-fork-local-paths))
  ([parent-backend initial-overlay]
   (create-overlay-backend parent-backend initial-overlay default-fork-local-paths))
  ([parent-backend initial-overlay local-paths]
   (->OverlayBackend (atom initial-overlay) parent-backend local-paths)))

;; =============================================================================
;; Safe Printing (prevent circular reference overflow)
;; =============================================================================

;; Backend state-atom can contain the entire runtime state which may have
;; circular references back to the ExecutionContext. Override print methods
;; to show summaries instead of full state.

#?(:clj
   (do
     (defmethod print-method AtomBackend [b ^java.io.Writer w]
       (.write w (str "#AtomBackend{:keys " (keys @(:state-atom b)) "}")))
     (defmethod print-method OverlayBackend [b ^java.io.Writer w]
       (.write w (str "#OverlayBackend{:overlay-keys " (keys @(:overlay-atom b)) "}"))))
   :cljs
   (do
     (extend-type AtomBackend
       IPrintWithWriter
       (-pr-writer [b writer _opts]
         (-write writer (str "#AtomBackend{:keys " (keys @(.-state-atom b)) "}"))))
     (extend-type OverlayBackend
       IPrintWithWriter
       (-pr-writer [b writer _opts]
         (-write writer (str "#OverlayBackend{:overlay-keys " (keys @(.-overlay-atom b)) "}"))))))

;; =============================================================================
;; Fork Type Helpers
;; =============================================================================

(def fork-type-local-paths
  "Predefined local-paths sets for common fork types.

  :thread - Chat threads with isolated conversation but shared DB
  :exploration - AI explorations with isolated conversation and speculative DB
  :branch - Durable branches with isolated conversation"
  {:thread      (conj default-fork-local-paths :conversation)
   :exploration (into default-fork-local-paths #{:conversation :db :base-db})
   :branch      (conj default-fork-local-paths :conversation)})

(defn local-paths-for-fork-type
  "Get local-paths set for a fork type keyword.

  Supports:
  - :thread - Isolated conversation, shared live DB connection
  - :exploration - Isolated conversation + speculative DB snapshot
  - :branch - Isolated conversation (DB handled by versioning API)

  Returns default-fork-local-paths for unknown types."
  [fork-type-key]
  (get fork-type-local-paths fork-type-key default-fork-local-paths))

;; =============================================================================
;; ImmutableBackend - Readonly snapshots
;; =============================================================================

(defrecord ImmutableBackend [state-map metadata]
  PStateBackend

  (backend-read [_ path]
    (get-in state-map path))

  (backend-write! [_ path _f]
    (throw (ex-info "Cannot write to immutable backend - use thaw-snapshot first"
                    {:backend-type :immutable
                     :path path})))

  (backend-write-2! [_ path-a path-b _f2]
    (throw (ex-info "Cannot write to immutable backend - use thaw-snapshot first"
                    {:backend-type :immutable
                     :path [path-a path-b]})))

  (backend-deref [_]
    state-map)

  (backend-type [_]
    :immutable))

(defn create-immutable-backend
  "Create ImmutableBackend from state map."
  ([state-map]
   (create-immutable-backend state-map {}))
  ([state-map metadata]
   (->ImmutableBackend state-map metadata)))

(defn thaw-backend
  "Convert immutable backend to writable atom backend."
  [backend]
  (if (= (backend-type backend) :immutable)
    (create-atom-backend (backend-deref backend))
    backend))

;; =============================================================================
;; Serialization
;; =============================================================================

(defn serialize-backend
  "Serialize immutable backend to EDN string.

  Drops continuations during serialization since closures cannot be serialized.
  Spins will need to be re-executed after deserialization to re-establish continuations."
  [backend]
  (when (= (backend-type backend) :immutable)
    (let [state (backend-deref backend)
          ;; Remove continuations AND listeners — both contain non-serializable
          ;; closures (re-established by re-running spins / re-adding watches /
          ;; re-exporting signals after restore).
          serializable-state (dissoc state :track-subscriptions :await-conts :listeners)]
      (pr-str {:state serializable-state
               :metadata (:metadata backend)}))))

(defn deserialize-backend
  "Deserialize EDN string to immutable backend.

  Uses incognito to properly deserialize defrecords (Result, SpinNode, SignalNode, etc.).

  Args:
    edn-string - Serialized backend
    read-handlers - Incognito read handlers map

  Returns: ImmutableBackend"
  [edn-string read-handlers]
  (let [{:keys [state metadata]} (read-string-safe read-handlers edn-string)]
    (create-immutable-backend state metadata)))
