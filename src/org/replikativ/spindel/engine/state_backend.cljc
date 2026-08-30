(ns org.replikativ.spindel.engine.state-backend
  "State backend abstraction for ExecutionContext.

  Provides pluggable storage strategies:
  - AtomBackend: Default async state (atom-based)
  - RefBackend: STM transactional state (ref-based, JVM only)
  - ImmutableBackend: Readonly snapshots (serializable)
  - OverlayBackend: Fork with delta storage (memory efficient)"
  (:require [clojure.set :as set]
            [incognito.edn :refer [read-string-safe]]))

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
  - :subscriptions - Reverse index for those continuations; it must share their
    snapshot boundary or a fork can observe a parent registration without the
    matching continuation
  - :engine/* - Engine execution state (pending queue, draining flag, timers)

  Shared state (falls back to parent):
  - :nodes - Signal and spin nodes (shared observer graph for reactive invalidation)
  - :spin-tracking - Dependency tracking (transient accumulator)
  - :atoms - Runtime atoms

  :listeners is fork-local AND deliberately NOT copied into a fork by
  `fork-context` (unlike :await-conts) — so a fork starts with ZERO listeners.
  This is load-bearing: a listener is side-effecting egress (publish/notify), so a
  fork must not inherit-then-fire the parent's listener on a fork-private mutation
  (that would leak speculative state). A fork that wants to egress adds its own."
  #{:track-subscriptions :await-conts :subscriptions :engine/retired-conts
    :engine/pending :engine/draining?
    :engine/delayed-spins :engine/timer-handles :listeners})

(def ^:private deleted ::deleted)
(def ^:private full-replacement-key ::full-replacement)

(defn- full-replacement-map? [value]
  (and (map? value)
       (true? (get (meta value) full-replacement-key))))

(defn- mark-full-replacement [value]
  (if (map? value)
    (vary-meta value assoc full-replacement-key true)
    value))

(defn- unmark-full-replacement [value]
  (if (full-replacement-map? value)
    (vary-meta value dissoc full-replacement-key)
    value))

(defn full-replacement
  "Mark a map-valued initial overlay entry as authoritative.

  Ordinary map entries in an OverlayBackend's initial state are sparse entity
  deltas and inherit untouched entities from the parent. Use this marker when
  the supplied map is the complete value and parent entries must be hidden. The
  marker is internal metadata and is removed from every logical read."
  [value]
  (mark-full-replacement value))

(defn- deleted-ancestor?
  "True when an overlay path or one of its prefixes is an explicit tombstone."
  [overlay path]
  (boolean
   (some #(= deleted (get-in overlay (subvec (vec path) 0 %)))
         (range 1 (inc (count path))))))

(defn- revive-deleted-path
  "Replace tombstoned prefixes so a nested update can safely descend.

  Strict ancestors become maps; a tombstone at the target becomes nil so the
  caller's update function observes the same value as backend-read."
  [overlay path]
  (reduce (fn [state depth]
            (let [prefix (subvec (vec path) 0 depth)]
              (if (= deleted (get-in state prefix))
                (assoc-in state prefix (when (< depth (count path)) {}))
                state)))
          overlay
          (range 1 (inc (count path)))))

(defn- materialize-entity-tombstones
  "Remove entity-level tombstones when a caller reads their containing map.

  Exact reads already treat a tombstoned path as absent through
  `deleted-ancestor?`. A top-level map read must present the same logical view;
  returning the sparse overlay marker as an ordinary value leaks implementation
  state into runtime queues such as `:engine/delayed-spins`."
  [value]
  (if (map? value)
    (reduce-kv (fn [logical k v]
                 (if (= deleted v)
                   (dissoc logical k)
                   logical))
               (unmark-full-replacement value)
               value)
    value))

(defn- merge-entity-overlay
  "Apply a sparse entity map to its logical parent collection.

  OverlayBackend copies shared state at entity granularity. Consequently a
  read of the containing top-level collection must combine inherited entities
  with this layer's replacements and tombstones. Exact entity reads remain
  simple overrides and do not use this function."
  [parent-value overlay-value]
  (reduce-kv (fn [entities entity-id entity-value]
               (if (= deleted entity-value)
                 (dissoc entities entity-id)
                 (assoc entities entity-id entity-value)))
             (if (map? parent-value)
               parent-value
               (empty overlay-value))
             overlay-value))

(defn- merged-overlay-state
  "Materialize the shallow entity-level overlay view, applying tombstones."
  [parent-state overlay local-paths]
  (reduce-kv
   (fn [state top-key overlay-value]
     (cond
       (= deleted overlay-value)
       (dissoc state top-key)

       (full-replacement-map? overlay-value)
       (assoc state top-key
              (materialize-entity-tombstones overlay-value))

       (record? overlay-value)
       (assoc state top-key overlay-value)

       (map? overlay-value)
       (assoc state top-key
              (reduce-kv (fn [entities entity-id entity-value]
                           (if (= deleted entity-value)
                             (dissoc entities entity-id)
                             (assoc entities entity-id entity-value)))
                         (if (map? (get state top-key))
                           (get state top-key)
                           {})
                         overlay-value))

       :else
       (assoc state top-key overlay-value)))
   ;; Fork-local top-level keys are authoritative in this layer. They were
   ;; copied explicitly at fork creation (or initialized empty) and must never
   ;; re-import values the parent registered afterward during a whole-state
   ;; transaction.
   (apply dissoc (or parent-state {}) local-paths)
   overlay))

(defn fork-local-path?
  "Check if path is fork-local (should not fall back to parent).

  Uses the provided local-paths set or defaults to `default-fork-local-paths`."
  ([first-key]
   (fork-local-path? first-key default-fork-local-paths))
  ([first-key local-paths]
   (contains? local-paths first-key)))

(defrecord OverlayBackend [overlay-atom parent-backend local-paths]
  PStateBackend

  (backend-read [this path]
    (if (empty? path)
      (backend-deref this)
      ;; Special handling for fork-local state (don't fall back to parent)
      (if (fork-local-path? (first path) local-paths)
        ;; Fork-local: overlay only, no parent fallback
        (let [overlay @overlay-atom]
          (when-not (deleted-ancestor? overlay path)
            (materialize-entity-tombstones (get-in overlay path))))
        ;; Shared state: check overlay, fall back to parent
        (let [overlay @overlay-atom
              overlay-val (get-in overlay path ::not-found)
              top-overlay (get overlay (first path) ::not-found)]
          (cond
            (deleted-ancestor? overlay path) nil
            (and (> (count path) 1) (full-replacement-map? top-overlay))
            (materialize-entity-tombstones
             (get-in (unmark-full-replacement top-overlay) (rest path)))
            (not= overlay-val ::not-found)
            (if (and (= 1 (count path))
                     (map? overlay-val)
                     (not (record? overlay-val))
                     (not (full-replacement-map? overlay-val)))
              (merge-entity-overlay
               (when parent-backend (backend-read parent-backend path))
               overlay-val)
              (materialize-entity-tombstones overlay-val))
            parent-backend (backend-read parent-backend path)
            :else nil)))))

  (backend-write! [this path f]
    ;; All writes go to overlay
    ;; CRITICAL: For shared state, use copy-on-write at entity level (e.g., full node)
    (if (empty? path)
      ;; Empty path = full state transaction
      ;; Apply `f` INSIDE the overlay CAS. The prior implementation computed
      ;; from @overlay-atom before swap!, so two whole-state transactions could
      ;; both claim the same continuation. Removed inherited entities are
      ;; written as nil tombstones; omission would fall through to the parent
      ;; backend and resurrect the removed subscription/continuation.
      (let [committed (volatile! nil)]
        (swap! overlay-atom
               (fn [ov]
                 (let [parent-state (when parent-backend
                                      ;; Recursively materialized by the
                                      ;; overlay backend implementation.
                                      (backend-deref parent-backend))
                       merged (merged-overlay-state parent-state ov local-paths)
                       new-state (f merged)
                       top-keys (set/union (set (keys merged))
                                           (set (keys new-state)))
                       changes
                       (reduce
                        (fn [acc top-key]
                          (let [old-value (get merged top-key)
                                new-value (get new-state top-key)]
                            (if (and (map? old-value)
                                     (not (record? old-value))
                                     (map? new-value)
                                     (not (record? new-value)))
                              (reduce
                               (fn [acc' entity-id]
                                 (let [old-entity (get old-value entity-id)
                                       present? (contains? new-value entity-id)
                                       new-entity (when present?
                                                    (get new-value entity-id))]
                                   (if (= old-entity new-entity)
                                     acc'
                                     (conj acc'
                                           [[top-key entity-id]
                                            (if present? new-entity deleted)]))))
                               acc
                               (set/union (set (keys old-value))
                                          (set (keys new-value))))
                              (if (= old-value new-value)
                                acc
                                (conj acc [[top-key]
                                           (if (contains? new-state top-key)
                                             (mark-full-replacement new-value)
                                             deleted)])))))
                        []
                        top-keys)]
                   ;; Reset on every retry; only the invocation whose CAS commits
                   ;; determines the auxiliary return value.
                   (vreset! committed new-state)
                   (reduce (fn [next-ov [changed-path value]]
                             (assoc-in next-ov changed-path value))
                           ov
                           changes))))
        @committed)

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
                            full-top? (full-replacement-map?
                                       (get ov (first path)))
                        ;; If entity not in overlay, copy from parent first
                            ov (if entity-in-overlay?
                                 (if (= deleted (get-in ov entity-path))
                                   (assoc-in ov entity-path {})
                                   ov)
                                 (if-let [parent-entity (when (and parent-backend
                                                                   (not full-top?))
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
                    (let [overlay-val (get-in ov path ::not-found)
                          parent-val (backend-read parent-backend path)
                          current (cond
                                    (= overlay-val ::not-found) parent-val
                                    (= overlay-val deleted) nil
                                    (full-replacement-map? overlay-val)
                                    (unmark-full-replacement overlay-val)
                                    (and (map? overlay-val) (not (record? overlay-val)))
                                    (merge-entity-overlay parent-val overlay-val)
                                    :else overlay-val)]
                      (assoc-in ov path (mark-full-replacement (f current))))))
           path)

          :else
          ;; Fork-local path (no parent fallback by design) or root
          ;; backend (no parent): direct write.
          (get-in
           (swap! overlay-atom
                  (fn [ov]
                    (update-in (revive-deleted-path ov path) path f)))
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
                (let [depth (count path)
                      seed-path (if (>= depth 2)
                                  (vec (take 2 path)) ;; entity-level CoW
                                  path)
                      full-top? (full-replacement-map?
                                 (get ov (first path)))]
                  (if (not= ::not-found (get-in ov seed-path ::not-found))
                    (cond
                      (= deleted (get-in ov seed-path))
                      ;; A whole-state transaction removed this entity.
                      ;; Revive an empty fork-local entity before assoc-in
                      ;; descends through the tombstone.
                      (assoc-in ov seed-path {})

                      (and (= depth 1)
                           (map? (get-in ov seed-path))
                           (not (record? (get-in ov seed-path)))
                           (not (full-replacement-map? (get-in ov seed-path))))
                      (assoc-in ov seed-path
                                (mark-full-replacement
                                 (merge-entity-overlay
                                  (backend-read parent-backend seed-path)
                                  (get-in ov seed-path))))

                      :else ov)
                    (if-some [parent-val (when-not full-top?
                                           (backend-read parent-backend seed-path))]
                      (assoc-in ov seed-path
                                (if (= depth 1)
                                  (mark-full-replacement parent-val)
                                  parent-val))
                      ov)))))]
      (swap! overlay-atom
             (fn [ov]
               (let [ov (-> ov (seed path-a) (seed path-b))
                     read-local (fn [path]
                                  (when-not (deleted-ancestor? ov path)
                                    (get-in ov path)))
                     [a' b'] (f2 (read-local path-a) (read-local path-b))]
                 (-> ov
                     (assoc-in path-a
                               (if (and (= 1 (count path-a))
                                        (not (fork-local-path?
                                              (first path-a) local-paths)))
                                 (mark-full-replacement a')
                                 a'))
                     (assoc-in path-b
                               (if (and (= 1 (count path-b))
                                        (not (fork-local-path?
                                              (first path-b) local-paths)))
                                 (mark-full-replacement b')
                                 b')))))))
    nil)

  (backend-deref [_]
    ;; The protocol promises the entire state for inspection and snapshots.
    ;; Materialize recursively so nested overlays include inherited entities
    ;; and every ancestor's tombstones. Diagnostics that need only this sparse
    ;; layer can inspect :overlay-atom directly.
    (merged-overlay-state
     (when parent-backend (backend-deref parent-backend))
     @overlay-atom
     local-paths))

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
