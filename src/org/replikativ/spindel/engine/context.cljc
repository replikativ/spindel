(ns org.replikativ.spindel.engine.context
  "Execution contexts for fork-safe computation.

  An ExecutionContext wraps a runtime and adds fork-specific state:
  - fork-id: Unique identifier for this execution branch
  - backend: PStateBackend implementation (AtomBackend, OverlayBackend, etc.)
  - parent-ctx: Parent ExecutionContext (nil for root)
  - executor: Executor for scheduling spins
  - bindings: Fork-local configuration
  - metadata: User-defined fork metadata

  Key properties:
  - Lightweight forking via overlay backends (O(1) fork creation)
  - Independent state per fork (mutations don't affect siblings)
  - Shared parent state via OverlayBackend (memory efficient)
  - Fork-local effect handlers (can override behavior per branch)"
  (:require [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.impl.delayed :as delayed]
            [org.replikativ.spindel.engine.impl.graph :as graph]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.executor :as sched]
            [org.replikativ.spindel.engine.state-backend :as backend]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [incognito.edn :refer [read-string-safe]])
  #?(:clj (:import [java.util.concurrent LinkedBlockingQueue TimeUnit]
                    [java.lang.ref Cleaner WeakReference])))

;; =============================================================================
;; Incognito Handlers for Serialization
;; =============================================================================

(def incognito-write-handlers
  "Write handlers for custom record types.

  Convert records to plain maps for serialization."
  (atom {'org.replikativ.spindel.engine.nodes.SpinNode
         (fn [node] (into {} node))

         'org.replikativ.spindel.engine.nodes.SignalNode
         (fn [node] (into {} node))

         'org.replikativ.spindel.spin.core.Result
         (fn [r] (into {} r))}))

(def incognito-read-handlers
  "Read handlers for custom record types.

  Convert plain maps back to records after deserialization."
  (atom {'org.replikativ.spindel.engine.nodes.SpinNode
         nodes/map->SpinNode

         'org.replikativ.spindel.engine.nodes.SignalNode
         nodes/map->SignalNode

         'org.replikativ.spindel.spin.core.Result
         ;; requiring-resolve is JVM-only. Serialization round-trip is
         ;; only exercised on JVM in practice (drain threads / executor
         ;; references don't survive an EDN trip), so the CLJS branch
         ;; intentionally returns the input map unchanged. We avoid
         ;; statically referencing spin.core here because spin.core
         ;; requires engine.context (cycle).
         (fn [m] #?(:clj  ((requiring-resolve 'org.replikativ.spindel.spin.core/map->Result) m)
                    :cljs m))}))

;; =============================================================================
;; ExecutionContext Record
;; =============================================================================

(defrecord ExecutionContext
  [fork-id        ; Unique ID for this fork (keyword)
   backend        ; PStateBackend implementation (AtomBackend, OverlayBackend, etc.)
   parent-ctx     ; Parent ExecutionContext (nil for root)
   executor       ; Executor for scheduling (shared across forks for now)
   bindings       ; Fork-local configuration (map for spin access via *execution-context*)
   metadata       ; User-defined fork metadata (e.g., {:particle-id 123})
   running        ; Atom controlling background drain thread lifecycle
   drain-thread   ; Background thread that continuously drains event queue
   drain-signal   ; LinkedBlockingQueue for waking drain thread (nil for forks)
   drain-active]  ; Atom counting drain-events! calls past the running guard.
                  ; stop-context! waits for this to reach 0 before returning,
                  ; so no further drain on this context can mutate state.

  ;; Implement runtime protocols by delegating to simple.cljc functions
  ;; This allows ExecutionContext to be used anywhere runtime is expected

  rtp/PGraph
  (record-deps! [this spin-id]
    (simple/record-deps! this spin-id))
  (clear-deps! [this spin-id]
    (simple/clear-deps! this spin-id))
  (ordered-observers [this signal-id]
    (graph/ordered-observers (backend/backend-deref backend) signal-id))

  rtp/PDepsTracking
  (track-signal-dep! [this spin-id signal-id]
    (simple/track-signal-dep! this spin-id signal-id))
  (track-spin-dep! [this parent-spin-id child-spin-id]
    (simple/track-spin-dep! this parent-spin-id child-spin-id))

  rtp/PSpinLifecycle
  (register-spin! [this spin-id spin-meta]
    (simple/register-spin! this spin-id spin-meta))
  (mark-dirty! [this spin-id]
    (simple/mark-dirty! this spin-id))
  (cache-result! [this spin-id result]
    (simple/cache-result! this spin-id result))
  (current-result [this spin-id]
    (simple/current-result this spin-id))
  (clean? [this spin-id]
    (simple/clean? this spin-id))
  (dirty? [this spin-id]
    (simple/dirty? this spin-id))

  rtp/PContinuation
  (add-continuation! [this spin-id cont]
    (simple/add-continuation! this spin-id cont))
  (remove-continuation! [this spin-id cont-id]
    (simple/remove-continuation! this spin-id cont-id))
  (earliest-continuation [this spin-id signal-id]
    (simple/earliest-continuation this spin-id signal-id))
  (resume-continuation! [this spin-id cont resume-fn]
    (simple/resume-continuation! this spin-id cont resume-fn))

  rtp/PEngine
  (enqueue! [this event]
    ;; Queue event and trigger async drain (like atoms.cljc:89-96)
    (simple/enqueue-event! this event)
    ;; Trigger drain - the CAS in drain-events! will skip if already draining
    (simple/trigger-drain! this executor))

  rtp/PState
  (swap-state! [_ path f]
    (backend/backend-write! backend path f))

  (swap-state-args! [_ path f args]
    (backend/backend-write! backend path
                           (fn [v] (apply f v args))))

  (get-state [_ path]
    (backend/backend-read backend path))

  (cas-state! [_ path old-val new-val]
    ;; CAS implementation depends on backend type
    ;; NOTE: We use a proper CAS loop instead of swap! with volatile
    ;; because swap! may retry the function on contention, and a volatile
    ;; would incorrectly persist a "success" flag across retries.
    (case (backend/backend-type backend)
      :atom
      (let [state-atom (:state-atom backend)]
        (loop []
          (let [current-state @state-atom
                current-val (get-in current-state path)]
            (if (= current-val old-val)
              ;; Value matches - try to CAS
              (if (compare-and-set! state-atom current-state (assoc-in current-state path new-val))
                true   ; CAS succeeded
                (recur)) ; CAS failed due to concurrent modification, retry
              ;; Value doesn't match - CAS fails
              false))))

      :overlay
      ;; OverlayBackend: CAS only supported for fork-local paths
      ;; (shared paths would require CAS on parent, which breaks isolation)
      (let [is-fork-local? (and (seq path)
                                (backend/fork-local-path? (first path)))]
        (if is-fork-local?
          ;; Fork-local: CAS directly on overlay atom
          (let [overlay-atom (:overlay-atom backend)]
            (loop []
              (let [current-state @overlay-atom
                    current-val (get-in current-state path)]
                (if (= current-val old-val)
                  ;; Value matches - try to CAS
                  (if (compare-and-set! overlay-atom current-state (assoc-in current-state path new-val))
                    true   ; CAS succeeded
                    (recur)) ; CAS failed due to concurrent modification, retry
                  ;; Value doesn't match - CAS fails
                  false))))
          ;; Shared path: CAS not supported (would violate fork isolation)
          (throw (ex-info "CAS on shared paths not supported for overlay backend"
                         {:backend-type :overlay
                          :path path
                          :reason "CAS on shared state would require parent modification"}))))

      ;; Immutable: CAS not supported
      (throw (ex-info "CAS not supported for immutable backend"
                     {:backend-type (backend/backend-type backend)})))))

;; =============================================================================
;; Safe Printing (prevent circular reference overflow)
;; =============================================================================

;; ExecutionContext contains backend → state → nodes → ... which can reference
;; back to the context, creating circular print chains. Override the default
;; defrecord print method with a bounded summary.

#?(:clj
   (defmethod print-method ExecutionContext [ctx ^java.io.Writer w]
     (.write w (str "#ExecutionContext{:fork-id " (:fork-id ctx)
                    ", :backend-type " (backend/backend-type (:backend ctx))
                    "}")))
   :cljs
   (extend-type ExecutionContext
     IPrintWithWriter
     (-pr-writer [ctx writer _opts]
       (-write writer (str "#ExecutionContext{:fork-id " (:fork-id ctx)
                           ", :backend-type " (backend/backend-type (:backend ctx))
                           "}")))))

;; =============================================================================
;; Creation
;; =============================================================================

#?(:clj
   (def ^:private ^Cleaner context-cleaner
     (Cleaner/create)))

(defn create-execution-context
  "Create a new root execution context.

  Options:
    :executor - Executor for spin scheduling (default: default-executor)
    :bindings - Initial fork-local configuration (default: {})
    :metadata - User metadata (default: {})
    :initial-state - Initial runtime state map (default: empty runtime state)

  Returns: ExecutionContext record

  Example:
    (def ctx (create-execution-context
               {:executor (sched/thread-pool-executor 4)
                :initial-state {:signals {sig-1 {:snapshot 42}}}}))

    (binding [*execution-context* ctx]
      ;; All execution context operations work here
      )"
  [& {:keys [executor bindings metadata initial-state]}]
  (let [;; Avoid :or with side effects! Evaluate default only when needed
        executor (or executor (sched/default-executor))
        bindings (or bindings {})
        metadata (or metadata {})
        initial-state (or initial-state nil)
        fork-id (keyword (str "root-" (random-uuid)))
        ;; Initialize state with execution context state structure
        initial-rt-state (or initial-state
                             {;; Core execution context structures
                              :nodes {}              ; Unified nodes (SignalNode + SpinNode)
                              :spin-tracking {}      ; Transient dependency tracking
                              :continuations {}      ; Spin continuations
                              :subscriptions {}      ; Event subscriptions
                              :spin-outputs {}       ; Spin output values (for non-blocking await)
                              :atoms {}              ; Fork-safe execution context atoms
                              ;; Engine state
                              :engine/pending []
                              :engine/draining? false
                              :engine/delayed-spins (sorted-map)
                              :engine/virtual-time 0
                              :engine/time-mode :real
                              :engine/timer-handles {}})
        ;; Create AtomBackend for root context
        atom-backend (backend/create-atom-backend initial-rt-state)
        ;; Create background drain thread control
        running (atom true)
        ;; Notification queue for waking drain thread (zero-polling)
        drain-signal #?(:clj (LinkedBlockingQueue.) :cljs nil)
        ;; Counter of drains currently past the function-entry guard.
        ;; stop-context! polls this down to 0 before returning.
        drain-active (atom 0)
        ;; Create the execution context first (needed for drain thread)
        ctx (->ExecutionContext
              fork-id
              atom-backend
              nil    ; No parent for root
              executor
              bindings
              metadata
              running
              nil    ; drain-thread - will be set below
              drain-signal
              drain-active)
        ;; Start background drain thread (zero-polling via LinkedBlockingQueue)
        ;; Blocks on drain-signal.poll(1s) instead of Thread/sleep 10
        ;; Wakes instantly when trigger-drain! calls .offer(:drain)
        ;; Uses daemon thread so leaked contexts don't prevent JVM exit
        ;; or accumulate thread overhead in tests.
        ;;
        ;; IMPORTANT: hold ctx via WeakReference, not as a strong capture. A
        ;; daemon thread is a GC root, so a strong reference would keep ctx
        ;; reachable forever, defeating the Cleaner registered below and
        ;; leaking the context. With a WeakReference, when the user drops
        ;; their last strong ref, the Cleaner fires, which flips :running
        ;; and signals the queue — the drain thread observes the weak ref
        ;; cleared and exits.
        ctx-ref #?(:clj (WeakReference. ctx) :cljs nil)
        drain-thread #?(:clj
                        (doto (Thread.
                                (fn []
                                  (while @running
                                    (try
                                      ;; Block until signaled or 1s timeout (zero CPU while waiting)
                                      (.poll drain-signal 1 TimeUnit/SECONDS)
                                      (when-let [c (.get ^WeakReference ctx-ref)]
                                        (simple/drain-events! c executor))
                                      (catch Throwable e
                                        ;; Log but don't crash drain thread on Error (e.g. StackOverflowError)
                                        (println "ERROR in background drain thread:" e))))))
                          (.setDaemon true)
                          (.start))
                        :cljs nil)]
    ;; Register GC cleaner to stop drain thread if context is abandoned.
    ;; IMPORTANT: The Runnable must NOT capture `ctx` — only the primitives
    ;; needed to stop the drain thread, otherwise the Cleaner prevents GC.
    #?(:clj
       (.register context-cleaner ctx
                  (reify Runnable
                    (run [_]
                      (reset! running false)
                      (.offer ^LinkedBlockingQueue drain-signal :stop)))))
    ;; Update context with drain-thread reference
    (assoc ctx :drain-thread drain-thread)))

(defn stop-context!
  "Stop an execution context's background drain thread.

  Only root contexts own the drain infrastructure; forks share the parent's,
  so calling this on a fork is a safe no-op.

  This should be called when a context is no longer needed to prevent
  thread leaks. After stopping, the context should not be used for
  reactive operations.

  Note: Does NOT close the executor — in-flight async callbacks may still
  need it. Use close-context! for full cleanup including executor shutdown.

  Args:
    context - ExecutionContext to stop

  Returns: nil"
  [context]
  ;; Only root contexts own the drain thread; forks share parent's
  (when (nil? (:parent-ctx context))
    (when-let [running (:running context)]
      (reset! running false))
    ;; Wake drain thread immediately so it notices running=false
    #?(:clj
       (when-let [ds (:drain-signal context)]
         (.offer ^LinkedBlockingQueue ds :stop)))

    ;; Deterministic shutdown contract: wait until no drain-events!
    ;; call is past the function-entry guard for this context. Once
    ;; this returns, the function-entry guard will reject any new
    ;; drain (drain-events! sees :running=false and exits before
    ;; touching state), so no further mutation can happen on this
    ;; context.
    ;;
    ;; In-flight drains observe :running=false at the top of each
    ;; loop iteration and exit with whatever's still in :pending
    ;; left for the next legitimate drain (e.g. restore-snapshot)
    ;; to pick up. This bounds our wait to a single event's
    ;; processing time per active drain, not the whole queue.
    ;;
    ;; The 5s outer timeout is a safety valve for a deadlocked spin
    ;; body. Reaching it indicates a real bug worth investigating;
    ;; we'd rather return and let the caller see weirdness than
    ;; hang forever.
    #?(:clj
       (when-let [drain-active (:drain-active context)]
         (let [deadline (+ (System/currentTimeMillis) 5000)]
           (loop []
             (when (and (pos? @drain-active)
                        (< (System/currentTimeMillis) deadline))
               (java.util.concurrent.locks.LockSupport/parkNanos 100000) ; 100us
               (recur))))))

    ;; Now also join the drain thread itself so its `while @running`
    ;; loop has actually exited. drain-active=0 only proves no drain
    ;; is past the guard *right now*; the drain thread might still be
    ;; in its outer .poll waiting for the next signal. The signal we
    ;; sent above wakes it, it observes :running=false, and exits.
    ;; 200ms is fine here — the thread isn't holding any drain work
    ;; once drain-active hit 0.
    #?(:clj
       (when-let [^Thread drain-thread (:drain-thread context)]
         (try
           (.join drain-thread 200)
           (catch Exception _ nil)))))
  nil)

(defn close-context!
  "Fully shut down an execution context: stop drain thread and close executor.

  Calls stop-context! then closes the executor if it implements Closeable.
  Use this only when you are certain no in-flight async work remains.

  Args:
    context - ExecutionContext to close

  Returns: nil"
  [context]
  (stop-context! context)
  #?(:clj
     (when (and (nil? (:parent-ctx context))
                (instance? java.io.Closeable (:executor context)))
       (try
         (.close ^java.io.Closeable (:executor context))
         (catch Exception _ nil))))
  nil)

;; =============================================================================
;; Forking
;; =============================================================================

(defn fork-context
  "Create a forked execution context from parent.

  Forking creates a new context with:
  - Overlay backend (memory efficient - stores only modifications)
  - Same executor (shared for now)
  - Inherited bindings (can be overridden)
  - New fork-id
  - Reference to parent context
  - Auto-incremented process-id for Elle compatibility (if parent has :process-id)

  Options:
    :state-updates - Map of initial overlay state (optional)
                     These values will be written to the overlay immediately
    :bindings - Fork-local configuration (merged with parent bindings)
                Map of keys to values that spins can read via (:bindings *execution-context*)
    :metadata - Fork metadata (default: parent metadata with updated process-id/depth)
    :process-id - Override auto-assigned process-id (default: parent + 1)

  Returns: New ExecutionContext with overlay backend

  Example:
    ;; Fork with initial state modifications
    (def fork-1 (fork-context parent-ctx
                  :state-updates {:nodes {sig-1 {:snapshot 99}}}
                  :bindings {:http-client mock-client
                             :random-seed 12345}
                  :metadata {:particle-id 1}))

    ;; Spins can access fork-local config:
    (spin
      (let [client (:http-client (:bindings *execution-context*))]
        (http-get client \"http://example.com\")))

    ;; Process-id is automatically assigned for Elle:
    (def sim (create-simulation-context))  ; process-id 0
    (def fork (fork-context sim))          ; process-id 1
    (def fork2 (fork-context fork))        ; process-id 2

  Properties:
  - Fork creation is O(1) with OverlayBackend
  - Overlay stores only modifications (memory efficient)
  - Reads fall through to parent (shared observer graph)
  - Fork-local state (continuations, spin-outputs) doesn't fall back
  - Bindings are merged (child overrides parent)
  - Process-id auto-increments for Elle compatibility"
  [parent-ctx & {:keys [state-updates bindings metadata process-id]
                 :or {state-updates {}
                      bindings {}
                      metadata nil
                      process-id nil}}]
  (let [fork-id (keyword (str "fork-" (random-uuid)))
        ;; Copy parent's continuations so fork inherits reactive subscriptions
        ;; Without this, spins executed in parent won't re-execute in fork when signals change
        ;; because continuations are fork-local (no parent fallback)
        parent-continuations (rtp/get-state parent-ctx [:continuations])

        ;; Fork external refs - pure map transformation
        ;; Each entry in [:external-refs] must implement PForkable
        parent-external-refs (rtp/get-state parent-ctx [:external-refs])
        forked-external-refs (when (seq parent-external-refs)
                               (persistent!
                                 (reduce-kv
                                   (fn [m ref-id ref]
                                     (assoc! m ref-id (rtp/pfork ref fork-id)))
                                   (transient {})
                                   parent-external-refs)))

        ;; Initialize fork-local state (engine state, continuations, external-refs)
        fork-local-state (merge
                           {:continuations (or parent-continuations {})  ; ← Copy parent's continuations!
                            :engine/pending []
                            :engine/draining? false
                            :engine/delayed-spins (sorted-map)
                            :engine/timer-handles {}}
                           (when forked-external-refs
                             {:external-refs forked-external-refs})  ; ← Include forked refs
                           state-updates)

        ;; Create overlay backend over parent's backend
        overlay-backend (backend/create-overlay-backend
                          (:backend parent-ctx)
                          fork-local-state)

        ;; Merge bindings (child overrides parent)
        merged-bindings (merge (:bindings parent-ctx) bindings)

        ;; Handle metadata with process-id/fork-depth tracking for Elle compatibility
        parent-metadata (:metadata parent-ctx)
        parent-pid (get parent-metadata :process-id)
        parent-depth (get parent-metadata :fork-depth 0)

        ;; Auto-assign process-id: parent + 1 (if parent has process-id)
        child-pid (or process-id
                      (when parent-pid (inc parent-pid)))

        ;; Build fork metadata with lineage tracking
        fork-metadata (cond
                        ;; User provided explicit metadata - use it, merge lineage if parent has it
                        metadata
                        (if parent-pid
                          (merge metadata
                                 {:process-id (or (:process-id metadata) child-pid)
                                  :parent-process-id parent-pid
                                  :fork-depth (inc parent-depth)})
                          metadata)

                        ;; No explicit metadata, parent has process-id - track lineage
                        parent-pid
                        (merge parent-metadata
                               {:process-id child-pid
                                :parent-process-id parent-pid
                                :fork-depth (inc parent-depth)})

                        ;; No explicit metadata, no process-id tracking - inherit parent metadata
                        :else
                        parent-metadata)]

    (->ExecutionContext
      fork-id
      overlay-backend
      parent-ctx  ; Keep parent reference
      (:executor parent-ctx)  ; Share executor (for now)
      merged-bindings
      fork-metadata
      (:running parent-ctx)       ; Share parent's drain thread control
      (:drain-thread parent-ctx)  ; Share parent's drain thread
      (:drain-signal parent-ctx)  ; Share parent's drain signal
      (:drain-active parent-ctx)  ; Share parent's drain-active counter
      )))

;; =============================================================================
;; Accessors
;; =============================================================================

(defn root-context?
  "Check if context is a root context (no parent)."
  [ctx]
  (nil? (:parent-ctx ctx)))

(defn fork-depth
  "Calculate fork depth (0 for root, 1 for direct child, etc.)."
  [ctx]
  (if (root-context? ctx)
    0
    (inc (fork-depth (:parent-ctx ctx)))))

(defn get-fork-id
  "Get fork ID of context."
  [ctx]
  (:fork-id ctx))

(defn get-parent-ctx
  "Get parent context (nil for root)."
  [ctx]
  (:parent-ctx ctx))

(defn get-metadata
  "Get fork metadata."
  [ctx]
  (:metadata ctx))

(defn get-executor
  "Get executor from context."
  [ctx]
  (:executor ctx))

(defn get-bindings
  "Get fork-local bindings from context.

  Spins read these via (:bindings *execution-context*). The :bindings map is
  fork-scoped: inherited by children, propagated across continuations, and
  preserved by snapshots.

  Most keys are persistent — set at context/fork creation, unchanged for the
  context's lifetime, survive every continuation resume. Examples: :http-client,
  :rng, app config. This is analogous to how Clojure's dynamic vars (*out*,
  *print-length*, ...) carry per-thread config.

  A key can also be registered as **ephemeral** via
  engine.bindings/register-ephemeral-binding-key!. Ephemeral keys represent
  per-render-pass scope: they're cleared when a track continuation resumes
  (start of a new render pass) but preserved when an await continuation
  resumes (mid-body, same pass). DOM addressing (:dom/parent-addr,
  :dom/current-slot) uses this.

  Returns map of keys to values."
  [ctx]
  (:bindings ctx))

;; =============================================================================
;; Execution Mode
;; =============================================================================

(defn get-execution-mode
  "Get the current execution mode from context bindings.

  Modes:
  - nil (or :normal) - Standard execution with caching
  - :rebuild - Execute spin bodies but use cached values
              (for restoring continuations after deserialization)

  Returns: keyword or nil"
  [ctx]
  (get-in ctx [:bindings :execution-mode]))

(defn set-execution-mode
  "Return new context with execution mode set in bindings.

  This is a pure function - returns new context, doesn't mutate.
  Use for functional updates before binding.

  Args:
    ctx - ExecutionContext
    mode - :normal, :rebuild, or nil

  Returns: New ExecutionContext with updated bindings"
  [ctx mode]
  (assoc-in ctx [:bindings :execution-mode] mode))

(defn rebuild-mode?
  "Check if context is in rebuild mode.

  Rebuild mode executes spin bodies (to create nested spins and
  register continuations) but returns cached values instead of
  recomputed values.

  This is used after deserialization to rebuild the execution state
  including all continuations needed for incremental reactivity."
  [ctx]
  (= :rebuild (get-execution-mode ctx)))

;; =============================================================================
;; Snapshot & Serialization
;; =============================================================================

(defn clean-in-flight-spins
  "Mark in-flight spins as dirty and strip per-render-pass DOM cache state.

  In-flight spins are those with :running? true and :completed? false.
  After cleaning, they'll re-execute on next access.

  Also:
  - Resets engine draining flag.
  - Drops :dom/cache and :dom/attr-cache, since slot/attribute reconciliation
    state belongs to the previous render pass and would mismatch the DOM the
    restored context renders into.

  NOTE: Continuations are preserved for in-memory snapshot/restore.
  They will be dropped during serialization (since closures can't be serialized).

  Args:
    state - Runtime state map (dereferenced)

  Returns: Cleaned state map"
  [state]
  (-> state
      ;; Reset engine draining flag
      (assoc :engine/draining? false)

      ;; Drop render-pass-specific DOM caches; restored context re-renders.
      (dissoc :dom/cache :dom/attr-cache)

      ;; Mark in-flight spins as dirty
      (update :nodes
        (fn [nodes]
          (reduce-kv
            (fn [acc tid node]
              (if (and (:running? node)
                       (not (:completed? node)))
                ;; In-flight spin - clean it up using protocol methods
                (assoc acc tid
                  (-> node
                      (assoc :running? false)
                      (assoc :completed? false)
                      (assoc :result nil)
                      (nodes/mark-dirty)))  ; Use protocol method to set :status :dirty
                ;; Not in-flight - keep as-is
                (assoc acc tid node)))
            {}
            nodes)))))

(defn snapshot-context
  "Create a full snapshot of execution context.

  Returns a new root context (no parent) with ImmutableBackend.
  The snapshot is completely independent and can be serialized.

  Options:
    :clean-in-flight? - If true (default), marks in-flight spins as dirty
    :include-pending? - If true (default), includes pending events

  Example:
    (def snap (snapshot-context ctx))
    (def serialized (serialize-context snap))
    (spit \"snapshot.edn\" serialized)

    ;; Later:
    (def restored (deserialize-context (slurp \"snapshot.edn\") executor))
    (def live (restore-snapshot restored))
    (binding [ec/*execution-context* live]
      (swap! signal inc)  ; Modify state
      @spin)              ; Re-execute

  Args:
    ctx - ExecutionContext to snapshot

  Returns: New ExecutionContext with ImmutableBackend"
  [ctx & {:keys [clean-in-flight? include-pending?]
          :or {clean-in-flight? true
               include-pending? true}}]
  (let [;; Deref entire state
        state (backend/backend-deref (:backend ctx))

        ;; Clean up in-flight spins if requested
        cleaned-state (if clean-in-flight?
                        (clean-in-flight-spins state)
                        state)

        ;; Remove pending events if requested
        final-state (if-not include-pending?
                      (assoc cleaned-state :engine/pending [])
                      cleaned-state)

        ;; Create immutable backend
        snapshot-backend (backend/create-immutable-backend
                          final-state
                          {:snapshot-time #?(:clj (System/currentTimeMillis)
                             :cljs (.now js/Date))
                           :source-fork-id (:fork-id ctx)})

        ;; Create new root context
        fork-id (keyword (str "snapshot-" (random-uuid)))]

    (->ExecutionContext
      fork-id
      snapshot-backend
      nil  ; No parent - independent snapshot
      (:executor ctx)  ; Share executor
      (:bindings ctx)  ; Copy bindings
      (assoc (:metadata ctx) :snapshot? true)
      nil   ; No :running atom — drain-events! treats this as always-allowed
      nil   ; No drain thread - snapshot is immutable
      nil   ; No drain signal - snapshot is immutable
      nil)  ; No drain-active counter — no stop-context! to wait on
    ))

(defn restore-snapshot
  "Restore a snapshot to a live execution context.

  Converts ImmutableBackend → AtomBackend and processes pending events.

  Options:
    :drain-events? - If true (default), drains pending events after restore

  Args:
    snapshot-ctx - ExecutionContext with ImmutableBackend

  Returns: New ExecutionContext with AtomBackend ready for use"
  [snapshot-ctx & {:keys [drain-events?] :or {drain-events? true}}]
  (when-not (= :immutable (backend/backend-type (:backend snapshot-ctx)))
    (throw (ex-info "Can only restore from immutable snapshot"
                    {:backend-type (backend/backend-type (:backend snapshot-ctx))})))

  ;; Thaw backend (immutable → atom)
  (let [atom-backend (backend/thaw-backend (:backend snapshot-ctx))
        restored-ctx (assoc snapshot-ctx :backend atom-backend)]

    ;; Optionally drain pending events
    (when drain-events?
      (simple/drain-events! restored-ctx (:executor restored-ctx)))

    restored-ctx))

(defn serialize-context
  "Serialize execution context to EDN string.

  Only works with snapshot contexts (ImmutableBackend).
  Creates snapshot first if needed.

  Uses incognito to properly serialize defrecords (Result, etc.).

  Args:
    ctx - ExecutionContext to serialize

  Returns: EDN string"
  [ctx]
  (let [snap-ctx (if (= :immutable (backend/backend-type (:backend ctx)))
                   ctx
                   (snapshot-context ctx))]
    (pr-str {:backend (backend/serialize-backend (:backend snap-ctx))
             :fork-id (:fork-id snap-ctx)
             :bindings (:bindings snap-ctx)
             :metadata (:metadata snap-ctx)})))

(defn deserialize-context
  "Deserialize execution context from EDN string.

  Returns immutable snapshot context. Use restore-snapshot to make it live.

  Uses incognito to properly deserialize defrecords (Result, etc.).

  Args:
    edn-string - Serialized context
    executor - Executor to attach to restored context

  Returns: ExecutionContext with ImmutableBackend"
  [edn-string executor]
  (let [{:keys [backend fork-id bindings metadata]} (read-string-safe @incognito-read-handlers edn-string)
        backend-obj (backend/deserialize-backend backend @incognito-read-handlers)
        ;; Only create drain thread for mutable backends (AtomBackend, OverlayBackend)
        ;; ImmutableBackend doesn't support CAS operations needed by drain-events!
        backend-type (backend/backend-type backend-obj)
        mutable? (or (= backend-type :atom) (= backend-type :overlay))]
    (if mutable?
      ;; Mutable backend - create drain thread with notification-based wakeup
      (let [running (atom true)
            drain-signal #?(:clj (LinkedBlockingQueue.) :cljs nil)
            drain-active (atom 0)
            ctx-temp (->ExecutionContext fork-id backend-obj nil executor bindings metadata running nil drain-signal drain-active)
            drain-thread #?(:clj
                            (doto (Thread.
                                    (fn []
                                      (while @running
                                        (try
                                          (.poll drain-signal 1 TimeUnit/SECONDS)
                                          (simple/drain-events! ctx-temp executor)
                                          (catch Exception e
                                            (println "ERROR in background drain thread:" e))))))
                              (.setDaemon true)
                              (.start))
                            :cljs nil)]
        (assoc ctx-temp :drain-thread drain-thread))
      ;; Immutable backend - no drain thread
      (->ExecutionContext fork-id backend-obj nil executor bindings metadata nil nil nil nil))))

;; =============================================================================
;; Rebuild Execution State
;; =============================================================================

(defn prepare-rebuild-context
  "Prepare a context for rebuild execution.

  This is a lower-level function that prepares the context but doesn't
  execute the model. Use with-rebuild-context for the full workflow.

  Steps:
  1. Restore snapshot to live context (immutable → atom backend)
  2. Reset chain-head to initial value
  3. Set :execution-mode to :rebuild in bindings

  Args:
    snapshot-ctx - Deserialized ExecutionContext (immutable backend)

  Options:
    :initial-chain-head - Chain head to restore (default: nil)
    :drain-events? - Whether to drain pending events (default: false)

  Returns: Live ExecutionContext ready for rebuild execution"
  [snapshot-ctx & {:keys [initial-chain-head drain-events?]
                   :or {initial-chain-head nil drain-events? false}}]
  (let [;; Step 1: Restore snapshot to live context
        live-ctx (restore-snapshot snapshot-ctx :drain-events? drain-events?)]

    ;; Step 2: Reset chain-head to initial value
    (addressing/set-chain-head! live-ctx initial-chain-head)

    ;; Step 3: Return context with rebuild mode set
    (set-execution-mode live-ctx :rebuild)))

(defn finalize-rebuild-context
  "Finalize a context after rebuild execution.

  Clears the :rebuild execution mode and optionally drains events.

  Args:
    ctx - ExecutionContext that was used for rebuild

  Options:
    :drain-events? - Whether to drain pending events (default: true)

  Returns: ExecutionContext with normal execution mode"
  [ctx & {:keys [drain-events?] :or {drain-events? true}}]
  (let [final-ctx (set-execution-mode ctx nil)]
    (when drain-events?
      (simple/drain-events! final-ctx (:executor final-ctx)))
    final-ctx))

#?(:clj
   (defmacro with-rebuild-context
     "Execute body in rebuild mode with the given context.

    Rebuild mode executes spin bodies (to create nested spins and register
    continuations) but returns cached values instead of recomputed values.

    This is used after deserialization to rebuild the execution state
    including all continuations needed for incremental reactivity.

    The macro:
    1. Prepares the context for rebuild (restore, reset chain-head, set mode)
    2. Binds *execution-context* to the rebuild context
    3. Executes body (typically @(model-fn))
    4. Finalizes the context (clears mode, drains events)

    Args:
      snapshot-ctx - Deserialized ExecutionContext (immutable backend)
      opts - Options map with:
             :initial-chain-head - Chain head to restore (default: nil)
      body - Forms to execute (typically model execution)

    Returns: Live ExecutionContext with rebuilt continuations

    Example:
      ;; Original execution
      (def ctx (create-execution-context))
      (binding [ec/*execution-context* ctx]
        @(model-fn))

      ;; Serialize
      (def serialized (serialize-context ctx))

      ;; Later: deserialize and rebuild
      (def restored (deserialize-context serialized executor))
      (def live-ctx (with-rebuild-context restored {}
                      @(model-fn)))

      ;; Now live-ctx has all continuations and responds to signals"
     [snapshot-ctx opts & body]
     `(let [rebuild-ctx# (prepare-rebuild-context
                           ~snapshot-ctx
                           :initial-chain-head (:initial-chain-head ~opts))]
        ;; Require runtime.core to get the binding vars
        (require 'org.replikativ.spindel.engine.core)
        (binding [org.replikativ.spindel.engine.core/*execution-context* rebuild-ctx#]
          ~@body)
        (finalize-rebuild-context rebuild-ctx#))))

;; =============================================================================
;; Simulation Context (Deterministic Testing)
;; =============================================================================

(defn create-simulation-context
  "Create an execution context optimized for deterministic simulation testing.

  This is a convenience function that creates a context pre-configured for
  simulation testing scenarios like prufstein, Elle linearizability checking,
  and fault injection testing.

  Configuration:
  - Virtual time mode enabled (time advances explicitly via advance-time!)
  - Synchronous executor option for deterministic execution
  - Process-id 0 for Elle-compatible history (forks get incrementing IDs)
  - Fork depth tracking for debugging

  Options:
    :executor    - Executor for spin scheduling (default: default-executor)
                   Use synchronous-executor for fully deterministic tests
    :bindings    - Fork-local configuration map (default: {})
    :metadata    - User-defined metadata (default: {})
    :process-id  - Elle-compatible process ID (default: 0)

  Returns: ExecutionContext ready for simulation testing

  Example:
    (let [ctx (create-simulation-context
                {:bindings {:rng my-rng :fault-config chaos}
                 :metadata {:trial 42}})]
      ;; Virtual time mode - control time explicitly
      (advance-time! ctx 1000)

      ;; Fork with automatic process-id assignment
      (let [fork (fork-context ctx)]
        ;; fork has process-id 1, fork-depth 1
        (get-process-id fork)  ; => 1
        ))"
  [& {:keys [executor bindings metadata process-id]
      :or {bindings {}
           metadata {}
           process-id 0}}]
  (let [;; Create base context
        ctx (create-execution-context
              :executor executor
              :bindings bindings
              :metadata (merge metadata
                              {:process-id process-id
                               :fork-depth 0}))]

    ;; Set virtual time mode
    (rtp/swap-state! ctx [:engine/time-mode] (constantly :virtual))

    ctx))

;; =============================================================================
;; Fork Lineage & Process ID (Elle Compatibility)
;; =============================================================================

(defn get-process-id
  "Get Elle-compatible process ID for this context.

  Process IDs are:
  - 0 for root contexts (or as specified in create-simulation-context)
  - Automatically incremented for forked contexts

  Returns: integer process-id or 0 if not set"
  [ctx]
  (get-in ctx [:metadata :process-id] 0))

(defn get-parent-process-id
  "Get the process ID of the parent context.

  Returns: integer parent process-id, or nil for root contexts"
  [ctx]
  (get-in ctx [:metadata :parent-process-id]))

(defn get-fork-lineage
  "Get the fork lineage chain from root to this context.

  Returns vector of process-ids from root to current context.

  Example:
    (get-fork-lineage root)  ; => [0]
    (get-fork-lineage fork)  ; => [0 1]
    (get-fork-lineage fork2) ; => [0 1 2]"
  [ctx]
  (loop [curr ctx
         path []]
    (let [pid (get-process-id curr)
          path' (cons pid path)]
      (if-let [parent (:parent-ctx curr)]
        (recur parent path')
        (vec path')))))

;; =============================================================================
;; Virtual Time Control API
;; =============================================================================

(defn get-time-mode
  "Get current time mode (:virtual or :real).

  Returns: :virtual or :real"
  [ctx]
  (rtp/get-state ctx [:engine/time-mode]))

(defn set-time-mode!
  "Set time mode for context.

  Args:
    ctx  - ExecutionContext
    mode - :virtual or :real

  Returns: previous mode"
  [ctx mode]
  (delayed/set-time-mode! ctx mode))

(defn current-time
  "Get current time (virtual or real) in milliseconds.

  In :virtual mode, returns the virtual time set via advance-time!
  In :real mode, returns System/currentTimeMillis or Date.now()"
  [ctx]
  (delayed/current-time ctx))

(defn advance-time!
  "Advance virtual time to target-ms and process all scheduled events.

  Only works in :virtual time mode. Throws if in :real mode.

  This is the primary way to control time in simulation tests:
  - Schedules delayed events via schedule-delayed-execution!
  - advance-time! processes all events up to target-ms

  Args:
    ctx       - ExecutionContext
    target-ms - Target time in milliseconds

  Returns: number of events processed

  Example:
    ;; Advance 100ms and process all timeouts/delays
    (advance-time! ctx 100)

    ;; Or advance to absolute time
    (advance-time! ctx 1000)  ; Jump to t=1000ms"
  [ctx target-ms]
  (delayed/advance-virtual-time! ctx target-ms))

