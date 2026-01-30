(ns is.simm.spindel.runtime.impl.simple
  "Portable async event-based runtime (CLJ/CLJS).

  This engine processes events using a FIFO queue with async draining.
  All state is kept in the runtime atom under :engine/*.

  Responsibilities:
  - Maintain event queue (:engine/pending)
  - Process events: :signal-change, :spin-completion, :deferred-delivery, :mailbox-post, :spin-execution
  - Drain events asynchronously on executor threads
  - Prevent concurrent draining via CAS lock (:engine/draining?)

  Notes:
  - Events are enqueued from various sources (spin completion, signal changes, etc.)
  - Draining happens asynchronously on the thread pool
  - Single drainer at a time via CAS lock (but draining can cascade new events)
  "
  (:refer-clojure :exclude [node])
  (:require [is.simm.spindel.log :as log]
            [is.simm.spindel.runtime.scheduler :as scheduler]
            [is.simm.spindel.runtime.protocols :as rtp]
            [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.runtime.bindings :as bindings]
            [is.simm.spindel.runtime.cache :as cache]
            [is.simm.spindel.runtime.node-protocols :as np]
            [is.simm.spindel.runtime.node-types :as nt]
            [is.simm.spindel.spin.continuation :as cont]
            [is.simm.spindel.spin.result :as result]
            [is.simm.partial-cps.async :as pcps-async]
            [clojure.set :as set]))

;; =============================================================================
;; Forward declarations
;; =============================================================================

(declare track-signal-dep!)

;; =============================================================================
;; Inline delivery/posting (to avoid cyclic dependency with spin/sync)
;; =============================================================================

(defn- deliver-inline!
  "INTERNAL: Deliver value inline to deferred, resuming readers directly."
  [deferred value state-atom]
  (let [;; Atomically check if already assigned and capture pending callbacks
        pending-callbacks (atom nil)
        _assigned? (swap! state-atom
                         (fn [state]
                           (if (:assigned? state)
                             ;; Already assigned - no change
                             state
                             ;; First assignment - capture pending and mark assigned
                             (do
                               (reset! pending-callbacks (:pending state))
                               {:assigned? true
                                :value value
                                :pending []}))))]

    ;; Notify all pending readers INLINE if this was the first assignment
    ;; Event handler already bound *in-trampoline* false
    (when-let [pending @pending-callbacks]
      (doseq [resolve pending]
        (cont/resume resolve value)))

    ;; Return the assigned value
    (:value @state-atom)))

(defn- post-inline!
  "INTERNAL: Post message inline to mailbox, resuming waiters directly."
  [mailbox msg state-atom]
  ;; Loop to find first non-cancelled waiter
  (loop []
    (let [waiter-to-try (atom nil)
          _result (swap! state-atom
                        (fn [state]
                          (if (seq (:waiters state))
                            ;; Has waiters - take first one to try
                            (do
                              (reset! waiter-to-try (first (:waiters state)))
                              (update state :waiters #(vec (rest %))))
                            ;; No waiters - add to queue
                            (update state :queue conj msg))))]
      (if-let [{:keys [spin-id resolve]} @waiter-to-try]
        ;; Got a waiter - check if cancelled (outside swap, context available)
        (if (and spin-id (rtc/spin-is-cancelled? spin-id))
          ;; Cancelled - try next waiter
          (recur)
          ;; Valid waiter - resume it
          ;; Event handler already bound *in-trampoline* false
          (do
            (cont/resume resolve msg)
            nil))
        ;; No waiter, message queued
        nil))))

;; =============================================================================
;; Engine state wiring
;; =============================================================================

(defn init-runtime!
  "Attach engine state to an existing runtime atom. Idempotent.

  Stores values directly (not nested atoms/refs) and accessed via PState protocol.
  Works with both atom-based and STM-based runtimes."
  [rt-atom]
  (swap! rt-atom
         (fn [rt]
           (if (:engine/pending rt)
             rt
             (assoc rt
                    ;; Event queue
                    :engine/pending []                    ; FIFO of events

                    ;; Event queue draining state
                    :engine/draining? false              ; CAS lock for draining

                    ;; Delayed spin scheduling (forkable)
                    :engine/delayed-spins (sorted-map)   ; timestamp -> [{:spin-fn fn :id uuid}]
                    :engine/virtual-time 0               ; virtual time in ms
                    :engine/time-mode :real              ; :real or :virtual
                    :engine/timer-handles {}))))         ; timer-id -> executor-handle
  rt-atom)

;; =============================================================================
;; Event Queue Operations
;; =============================================================================

(defn schedule-spin!
  "Legacy no-op. Spins are now scheduled via :spin-execution events, not a ready queue."
  [_context _spin-id]
  true)

(defn enqueue-event!
  "Atomically enqueue an event to the pending queue.

  Events are processed in FIFO order during draining sessions.
  Does not process event immediately - just adds to queue.

  Args:
    context - context record
    event - Event map with :type key (e.g., {:type :signal-change :id sid})

  Returns: true"
  [context event]
  (rtp/swap-state-args! context [:engine/pending] conj [event])
  (log/trace! {:event :engine/enqueue-event :data {:event event}})
  true)

(defn dequeue-event!
  "Atomically dequeue next event from pending queue.

  Returns nil if queue is empty.

  Args:
    context - context record

  Returns: Event map or nil"
  [context]
  (let [event-atom (atom nil)]
    (rtp/swap-state! context [:engine/pending]
      (fn [queue]
        (if (seq queue)
          (do
            (reset! event-atom (first queue))
            (vec (rest queue)))
          queue)))
    @event-atom))

(defn process-event!
  "Process a single event.

  This is the core event dispatcher. Handles:
  - :signal-change - marks dependent spins dirty
  - :spin-completion - resumes waiting continuations
  - :deferred-delivery - delivers value to deferred
  - :mailbox-post - posts message to mailbox

  May enqueue additional events during processing (cascading).

  Args:
    context - context record
    event - Event map with :type key"
  [context event]
  (log/trace! {:event :engine/process-event :data {:event event}})

  (case (:type event)
    :signal-change
    (let [sid (:id event)
          ;; Get observers in topological order (glitch-free)
          observers (rtp/ordered-observers context sid)]
      (log/trace! {:event :engine/signal-change
                   :data {:signal-id sid :observers observers}})

      ;; Resume track continuations for spins watching this signal
      ;; (Like laufzeit's consume - persistent continuations that resume on signal change)
      (doseq [spin-id observers]
        (when-let [cont (rtp/earliest-continuation context spin-id sid)]
          (log/debug! {:event :engine/resuming-track-continuation
                       :data {:spin-id spin-id :signal-id sid}})

          ;; CRITICAL: Remove all continuations with order > resumed continuation's order
          ;; These are stale continuations from a previous execution that's now being invalidated.
          ;; Without this, when a later signal changes, it would find the stale continuation
          ;; (which captured old values) instead of the fresh one from re-execution.
          (let [cont-order (:order cont)
                all-conts (rtp/get-state context [:continuations spin-id])
                ;; Collect signal-ids from continuations with order < cont-order (skipped continuations)
                ;; These are dependencies that won't be re-tracked by the resumed execution
                skipped-signal-ids (->> (vals all-conts)
                                        (filter #(< (:order %) cont-order))
                                        (keep :signal-id))]
            ;; Remove stale continuations (order > cont-order)
            (rtp/swap-state! context [:continuations spin-id]
              (fn [conts]
                (into {} (filter (fn [[k v]] (<= (:order v) cont-order)) conts))))

            ;; CRITICAL: Re-track signal dependencies from skipped continuations
            ;; When resuming from continuation N, continuations 1 to N-1 don't re-execute,
            ;; so their signals aren't re-tracked. Without this, record-deps! would compute
            ;; removed-signals = old-signals - tracked-signals and remove these signals.
            ;; By re-tracking them here, we preserve the dependency graph.
            (doseq [skipped-sid skipped-signal-ids]
              (track-signal-dep! context spin-id skipped-sid)))

          ;; CRITICAL: Re-track the resumed signal dependency
          ;; Without this, when record-deps! is called after spin completion,
          ;; it would find empty tracking data and remove the spin from observers.
          ;; This ensures the dependency graph stays connected across resumptions.
          (track-signal-dep! context spin-id sid)

          ;; CRITICAL: Mark spin as not completed and dirty before resuming (like laufzeit lines 246, 252)
          ;; This allows the spin to be resumed from the track breakpoint
          (rtp/swap-state! context [:nodes spin-id]
            (fn [node]
              (when node
                (-> node
                    (assoc :completed? false)
                    (np/mark-dirty)))))

          ;; Resume continuation with fresh signal value from :on-resume callback
          ;; CRITICAL: Bind *in-trampoline* to false when resuming from event handler
          ;; CRITICAL: Bind *execution-context* so current-execution-context returns correct context
          ;; CRITICAL: Restore context bindings (DOM context like :dom/parent-addr, :dom/current-slot)
          ;; These were captured when the continuation was created in track.cljc
          (let [ctx-bindings (:ctx-bindings cont)
                ctx-with-bindings (if ctx-bindings
                                    (update context :bindings merge ctx-bindings)
                                    context)]
            (binding [rtc/*execution-context* ctx-with-bindings
                      rtc/*spin-id* spin-id
                      pcps-async/*in-trampoline* false]
              (rtp/resume-continuation!
               context
               spin-id
               cont
               ;; resume-continuation! already calls :on-resume and passes value here
               (fn [signal-value]
                 (cont/resume (:resolve-fn cont) signal-value)))))))
      nil)

    :spin-completion
    (let [tid (:id event)
          ;; Get all parent spin-ids that have continuations subscribed
          parent-spin-ids (keys (rtp/get-state context
                                   [:subscriptions [:spin/complete tid]]))]
      (log/trace! {:event :engine/spin-completion
                   :data {:spin-id tid :parent-spin-ids parent-spin-ids}})

      ;; Resume continuations for spins that are waiting on this spin
      (doseq [parent-id parent-spin-ids]
        ;; Get continuation IDs for this parent
        (let [cont-ids (rtp/get-state context
                         [:subscriptions [:spin/complete tid] parent-id])]
          (doseq [cont-id cont-ids]
            (let [cont (rtp/get-state context
                         [:continuations parent-id cont-id])]
              (when cont
                ;; Resume continuation
                ;; Restore parent *spin-id* and *execution-context* when resuming
                ;; CRITICAL: Bind *in-trampoline* to false when resuming from event handler
                ;; This ensures invoke-continuation establishes a new trampoline loop
                ;; CRITICAL: Bind *execution-context* so current-execution-context returns correct context
                (binding [rtc/*execution-context* context
                          rtc/*spin-id* parent-id
                          pcps-async/*in-trampoline* false]
                  (let [resume-result (rtp/resume-continuation!
                                       context
                                       parent-id
                                       cont
                                       (fn [_child-value-from-on-resume]
                                         ;; Get child's result from :nodes SpinNode (Phase 1B)
                                         (let [spin-node (rtp/get-state context [:nodes tid])
                                               child-result (when spin-node (:result spin-node))]
                                           (result/match child-result
                                             #(cont/resume (:resolve-fn cont) %)
                                             #(cont/resume (:reject-fn cont) %)))))]
                    resume-result)))))))
      nil)

    :deferred-delivery
    (let [deferred (:deferred event)
          value (:value event)
          state-atom (.-state-atom deferred)]  ; Access deftype field
      (log/trace! {:event :engine/deferred-delivery
                   :data {:deferred deferred :value value}})
      ;; Deliver inline - we're already on executor thread, queue broke the call stack
      ;; CRITICAL: Bind *execution-context* and *in-trampoline* when delivering deferred value
      ;; The deferred function will resume continuations which need context access
      ;; CRITICAL: Bind *execution-context* so current-execution-context returns correct context
      (binding [rtc/*execution-context* context
                pcps-async/*in-trampoline* false]
        (deliver-inline! deferred value state-atom))
      nil)

    :mailbox-post
    (let [mailbox (:mailbox event)
          msg (:msg event)
          state-atom (.-state-atom mailbox)]  ; Access deftype field
      (log/trace! {:event :engine/mailbox-post
                   :data {:mailbox mailbox :msg msg}})
      ;; Post inline - we're already on executor thread, queue broke the call stack
      ;; CRITICAL: Bind *execution-context* and *in-trampoline* when posting to mailbox
      ;; The mailbox function will resume continuations which need context access
      (binding [rtc/*execution-context* context
                pcps-async/*in-trampoline* false]
        (post-inline! mailbox msg state-atom))
      nil)

    :spin-execution
    (let [tid (:id event)
          spin (:spin event)
          resolve-fn (:resolve-fn event)
          reject-fn (:reject-fn event)
          execution-context (:execution-context event)]  ; May be nil for normal spins
      (log/trace! {:event :engine/spin-execution
                   :data {:spin-id tid}})
      ;; Execute spin on executor thread with provided callbacks
      ;; CRITICAL: Bind *in-trampoline* to false when re-entering from event handler
      ;; This ensures invoke-continuation establishes a new trampoline loop
      ;; If execution-context is provided (e.g., from SMC), bind it; otherwise use context
      (binding [rtc/*execution-context* (or execution-context context)
                rtc/*spin-id* tid
                pcps-async/*in-trampoline* false]
        ;; Invoke spin (Spin implements IFn)
        (let [result (spin resolve-fn reject-fn)]
          nil)))

    ;; Unknown event type
    (do
      (log/trace! {:event :engine/unknown-event :data {:event event}})
      nil)))

;; Forward declaration for mutual recursion
(declare trigger-drain!)

(defn drain-events!
  "Drain all events from the pending queue.

  Claims the draining lock (:engine/draining? flag) and processes
  all events until the queue is empty. Only one thread can drain at a time.

  Events processed during draining may enqueue additional events (cascading).
  The drain continues until the queue is completely empty.

  This is called after external changes (signal swap, spin completion, etc.)
  and runs asynchronously on the executor.

  Args:
    context - context record
    executor - Executor to run on (unused in single-threaded, but kept for API)

  Returns: Number of events processed"
  [context executor]
  ;; Try to claim draining lock (CAS operation)
  (let [cas-result (rtp/cas-state! context [:engine/draining?] false true)]
    (if-not cas-result
      ;; Another thread is already draining
      (do
        (log/trace! {:event :engine/drain-skipped :data {:reason :already-draining}})
        0)

      ;; We claimed the lock - drain to completion
      (try
        (log/trace! {:event :engine/drain-start})
        (let [event-count (atom 0)]
          ;; Drain loop
          (loop []
            (if-let [event (dequeue-event! context)]
              (do
                ;; Process event (may enqueue more events)
                (process-event! context event)
                (swap! event-count inc)
                ;; Continue draining
                (recur))
              ;; Queue empty - done
              (do
                (log/trace! {:event :engine/drain-complete
                             :data {:events-processed @event-count}})
                @event-count))))
        (finally
          ;; Always release draining lock
          (rtp/swap-state! context [:engine/draining?] (constantly false))

          ;; CRITICAL: Check queue after releasing lock to handle race condition
          ;; If events were enqueued during the gap between our last dequeue and
          ;; releasing the lock, we need to trigger another drain cycle.
          ;; Without this, events can get stuck waiting forever.
          (let [pending (rtp/get-state context [:engine/pending])]
            (when (seq pending)
              (trigger-drain! context executor))))))))

(defn await-drain-complete!
  "Wait for any in-progress drain to complete AND pending queue to be empty.

  Busy-waits until both :engine/draining? is false AND :engine/pending is empty.
  This ensures async drains triggered by signal swaps fully complete before proceeding.

  Args:
    context - context record
    timeout-ms - Max time to wait (default 5000ms)

  Returns: true if drain completed, false if timeout"
  [context & {:keys [timeout-ms] :or {timeout-ms 5000}}]
  #?(:clj
     (let [start (System/currentTimeMillis)
           deadline (+ start timeout-ms)
           iterations (atom 0)]
       (loop []
         (swap! iterations inc)
         (let [draining? (rtp/get-state context [:engine/draining?])
               pending (rtp/get-state context [:engine/pending])]
           (if (or draining? (seq pending))
             (if (< (System/currentTimeMillis) deadline)
               (do
                 (Thread/sleep 1)
                 (recur))
               false) ; Timeout
             true)))) ; Drain complete AND queue empty
     :cljs
     ;; CLJS: busy wait without Thread/sleep (use promises/async in real impl)
     (let [start (.now js/Date)
           deadline (+ start timeout-ms)]
       (loop []
         (let [draining? (rtp/get-state context [:engine/draining?])
               pending (rtp/get-state context [:engine/pending])]
           (if (or draining? (seq pending))
             (if (< (.now js/Date) deadline)
               (recur)
               false) ; Timeout
             true)))))) ; Drain complete AND queue empty

(defn trigger-drain!
  "Trigger async draining of the event queue.

  Schedules drain-events! to run on the executor. Does not wait for
  completion - returns immediately.

  This is called after external changes to ensure events are processed
  eventually. If draining is already in progress, the new events will
  be picked up by the current drain session.

  Args:
    context - context record
    executor - Executor to schedule drain on

  Returns: true if scheduled, false if no executor available"
  [context executor]
  (if executor
    (do
      (scheduler/execute! executor
        #(drain-events! context executor))
      (log/trace! {:event :engine/trigger-drain})
      true)
    (do
      (log/trace! {:event :engine/trigger-drain-no-executor})
      false)))

;; =============================================================================
;; Delayed spin management (forkable event loop)
;; =============================================================================

(defn current-time
  "Get current time (virtual or real) in milliseconds."
  [context]
  (let [time-mode (rtp/get-state context [:engine/time-mode])]
    (if (= time-mode :virtual)
      (rtp/get-state context [:engine/virtual-time])
      #?(:clj (System/currentTimeMillis)
         :cljs (.now js/Date)))))

(defn schedule-delayed-spin!
  "Schedule a spin to run after delay-ms. Returns spin-id for cancellation.

  Spin is stored in forkable event queue. In :real time mode, also schedules
  executor timer to trigger processing at the appropriate time."
  [context delay-ms spin-fn]
  (let [spin-id (keyword (gensym "delayed-spin-"))
        fire-time (+ (current-time context) delay-ms)
        spin-entry {:spin-fn spin-fn :id spin-id}]

    ;; Add to event queue (forkable state) - works for both atoms and STM
    (rtp/swap-state! context [:engine/delayed-spins]
                     (fn [queue]
                       (update queue fire-time (fnil conj []) spin-entry)))

    (log/trace! {:event :engine/schedule-delayed
                 :data {:spin-id spin-id :delay-ms delay-ms :fire-time fire-time}})

    spin-id))

(defn process-delayed-spins!
  "Process all delayed spins whose time has come. Returns number of spins executed.

  TRANSACTIONAL: Atomically extracts all ready spins from queue, then executes them
  outside the transaction to avoid holding the lock during execution."
  [context executor]
  (let [now (current-time context)
        ;; Atomically extract all ready spins and clean up queue + handles
        ;; swap-state! returns the value at path, we need to return spins from fn
        ready-spins (atom nil)
        _ (rtp/swap-state! context []
            (fn [state]
              (let [queue (get state :engine/delayed-spins (sorted-map))
                    ;; Find all entries with fire-time <= now
                    ready (take-while (fn [[fire-time _]] (<= fire-time now)) queue)
                    spins (vec (mapcat val ready))
                    ready-ids (set (map :id spins))
                    ;; Remove ready entries from queue
                    remaining (into (sorted-map)
                                    (drop (count ready) queue))
                    ;; Clean up timer handles for ready spins
                    new-handles (apply dissoc
                                       (get state :engine/timer-handles {})
                                       ready-ids)]
                ;; Store spins for execution outside swap
                (reset! ready-spins spins)
                ;; Return new state
                (-> state
                    (assoc :engine/delayed-spins remaining)
                    (assoc :engine/timer-handles new-handles)))))]

    ;; Execute spins outside the transaction
    (doseq [{:keys [spin-fn id fire-time]} @ready-spins]
      (log/trace! {:event :engine/execute-delayed
                   :data {:spin-id id :fire-time fire-time :now now}})
      (when executor
        (scheduler/execute! executor
          #(binding [rtc/*execution-context* context]
             (spin-fn)))))

    (count @ready-spins)))

(defn cancel-delayed-spin!
  "Cancel a scheduled delayed spin by id. Returns true if cancelled, false if not found."
  [context spin-id]
  (let [cancelled? (atom false)]

    ;; Remove from event queue
    (rtp/swap-state! context [:engine/delayed-spins]
                     (fn [queue]
                       (into (sorted-map)
                             (for [[fire-time spins] queue
                                   :let [filtered (vec (remove #(= (:id %) spin-id) spins))]]
                               (do
                                 (when (not= (count filtered) (count spins))
                                   (reset! cancelled? true))
                                 [fire-time filtered])))))

    ;; Clean up timer handle
    (rtp/swap-state-args! context [:engine/timer-handles] dissoc [spin-id])

    (log/trace! {:event :engine/cancel-delayed
                 :data {:spin-id spin-id :cancelled? @cancelled?}})

    @cancelled?))

(defn advance-virtual-time!
  "Advance virtual time to target-time-ms, processing all spins along the way.
  Only works in :virtual time mode. Returns number of spins executed."
  [context target-time-ms]
  (let [time-mode (rtp/get-state context [:engine/time-mode])]
    (when (not= time-mode :virtual)
      (throw (ex-info "advance-virtual-time! only works in :virtual time mode"
                      {:current-mode time-mode})))

    (rtp/swap-state! context [:engine/virtual-time] (constantly target-time-ms))

    ;; Process all spins up to target time
    (process-delayed-spins! context nil)))

(defn set-time-mode!
  "Set time mode to :real or :virtual. Returns previous mode."
  [context mode]
  (when-not (#{:real :virtual} mode)
    (throw (ex-info "Time mode must be :real or :virtual" {:mode mode})))

  (let [prev-mode (rtp/get-state context [:engine/time-mode])]
    (rtp/swap-state! context [:engine/time-mode] (constantly mode))
    (log/trace! {:event :engine/set-time-mode
                 :data {:prev-mode prev-mode :new-mode mode}})
    prev-mode))

;; =============================================================================
;; Graph Management (shared across all context implementations)
;; =============================================================================

(defn collect-transitive-observers
  "Collect all spins transitively dependent on initial-spin-ids.

  Given a set of initial spin IDs, follows the spin-observers graph to find
  all spins that directly or indirectly observe these spins.

  Args:
    context - context state map (not the record, the dereferenced state)
    initial-spin-ids - Collection of spin IDs to start from

  Returns: Set of all transitive observer spin IDs"
  [context initial-spin-ids]
  (loop [to-visit (vec initial-spin-ids) visited #{}]
    (if-let [tid (first to-visit)]
      (if (visited tid)
        (recur (rest to-visit) visited)
        ;; NEW: Read observers from :nodes using protocol (Phase 1B cleanup)
        (let [node (get-in context [:nodes tid])
              observers (if node (np/get-observers node) #{})]
          (recur (into (rest to-visit) observers) (conj visited tid))))
      visited)))

(defn topological-sort
  "Sort spin IDs in topological order based on spin dependencies.

  Ensures spins are executed in dependency order (dependencies before dependents).
  Uses Kahn's algorithm for topological sorting.

  Args:
    context - context state map (not the record, the dereferenced state)
    spin-ids - Collection of spin IDs to sort

  Returns: Vector of spin IDs in topological order"
  [context spin-ids]
  ;; NEW: Read from :nodes using protocol (Phase 1B cleanup)
  (let [in-degree (reduce (fn [acc tid]
                            (let [node (get-in context [:nodes tid])
                                  deps (if node (np/get-deps node) {:signals #{} :spins #{}})
                                  spin-deps (get deps :spins #{})]
                              (assoc acc tid (count (filter spin-ids spin-deps)))))
                          {}
                          spin-ids)
        initial-queue (vec (filter #(zero? (get in-degree % 0)) spin-ids))]
    (loop [queue initial-queue result [] in-deg in-degree]
      (if-let [tid (first queue)]
        (let [new-result (conj result tid)
              ;; NEW: Read observers from :nodes using protocol (Phase 1B cleanup)
              node (get-in context [:nodes tid])
              dependent-spins (if node (np/get-observers node) #{})
              relevant (filter spin-ids dependent-spins)
              new-in-deg (reduce (fn [deg dep]
                                   (update deg dep dec)) in-deg relevant)
              newly-ready (filter #(zero? (get new-in-deg % 1)) relevant)
              new-queue (into (vec (rest queue)) newly-ready)]
          (recur new-queue new-result new-in-deg))
        result))))

(defn ordered-observers
  "Get observers of a signal in topological order.

  Combines transitive observer collection with topological sorting to ensure
  glitch-free updates.

  Args:
    context - context state map (not the record, the dereferenced state)
    signal-id - Signal ID to get observers for

  Returns: Vector of spin IDs in topological order"
  [context signal-id]
  ;; NEW: Read from :nodes using protocol (Phase 1B read migration)
  (let [node (get-in context [:nodes signal-id])
        observers (if node
                    (np/get-observers node)
                    #{})]
    (if (seq observers)
      (vec (topological-sort context (collect-transitive-observers context observers)))
      [])))

;; =============================================================================
;; Dependency Tracking (shared across all context implementations)
;; =============================================================================

(defn record-deps!
  "Record dependencies tracked during spin execution into the dependency graph.

  Takes the temporary tracking data from [:spin-tracking spin-id] and commits
  it to the permanent [:graph spin-id] structure, updating observer registrations.

  Now also computes identity hash (deps-hash) from dependency GENERATIONS for
  O(1) identity-based caching.

  This is called after a spin completes execution to finalize its dependencies.

  TRANSACTIONAL: All state changes happen atomically in a single swap-state! to
  ensure context consistency for snapshotting.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin whose dependencies to record

  Returns: true"
  [context spin-id]
  (rtp/swap-state! context []
    (fn [rt-state]
      (let [tracked-deps (get-in rt-state [:spin-tracking spin-id])]
        ;; Guard: Skip if already recorded (tracking data cleared)
        ;; This ensures idempotency when record-deps! is called multiple times
        (if-not tracked-deps
          rt-state  ; Return state unchanged
          (let [
            ;; Extract captured generations/hashes for identity hashing (O(1))
            signal-generations (:signal-generations tracked-deps {})
            spin-hashes (:spin-hashes tracked-deps {})
            ;; Derive dependency sets from map keys
            tracked-signals (set (keys signal-generations))
            tracked-spins (set (keys spin-hashes))
            ;; Compute identity hash from GENERATIONS (O(1) per dependency)
            ;; This replaces the slow content hashing that was O(n) for large collections
            deps-hash (when (or (seq signal-generations) (seq spin-hashes))
                        (cache/compute-deps-identity signal-generations spin-hashes nil))
            ;; Get old dependencies from SpinNode in :nodes (Phase 1B)
            spin-node (get-in rt-state [:nodes spin-id])
            old-deps (if spin-node (np/get-deps spin-node) {:signals #{} :spins #{}})
            old-signals (:signals old-deps #{})
            old-spins (:spins old-deps #{})
            removed-signals (set/difference old-signals tracked-signals)
            removed-spins (set/difference old-spins tracked-spins)]

        (-> rt-state
            ;; Update SpinNode in :nodes with dependencies (Phase 1B)
            (update-in [:nodes spin-id]
              (fn [node]
                ;; Create SpinNode if it doesn't exist (preserve created-by/created-spins if exists)
                (let [node (or node (nt/->spin-node nil :clean false false #{} {} nil {} nil #{}))]
                  (-> node
                      (np/set-deps {:signals tracked-signals
                                    :spins tracked-spins})
                      (np/set-deps-hash deps-hash)
                      ;; Store generations/hashes instead of values for debugging
                      (assoc :deps-values {:signal-generations signal-generations
                                          :spin-hashes spin-hashes})))))

            ;; Remove spin from old signal observers in :nodes SignalNode (Phase 1B)
            (as-> state
              (reduce (fn [s sid]
                        (let [node (get-in s [:nodes sid])]
                          (if node
                            (update-in s [:nodes sid] #(np/remove-observer % spin-id))
                            s)))
                      state
                      removed-signals))

            ;; Add spin to new signal observers in :nodes SignalNode (Phase 1B)
            (as-> state
              (reduce (fn [s sid]
                        (let [node (get-in s [:nodes sid])]
                          (if node
                            (update-in s [:nodes sid] #(np/add-observer % spin-id))
                            s)))
                      state
                      tracked-signals))

            ;; Remove spin from old spin observers in :nodes SpinNode (Phase 1B)
            (as-> state
              (reduce (fn [s tid]
                        (let [node (get-in s [:nodes tid])]
                          (if node
                            (update-in s [:nodes tid] #(np/remove-observer % spin-id))
                            s)))
                      state
                      removed-spins))

            ;; Add spin to new spin observers in :nodes SpinNode (Phase 1B)
            (as-> state
              (reduce (fn [s tid]
                        ;; Create node if it doesn't exist, then add observer
                        (update-in s [:nodes tid]
                          (fn [node]
                            (let [node (or node (nt/->spin-node nil :clean false false #{} {} nil {} nil #{}))]
                              (np/add-observer node spin-id)))))
                      state
                      tracked-spins))

            ;; Clear tracking data
            (update :spin-tracking dissoc spin-id)))))))
  true)

(defn clear-deps!
  "Clear all dependencies for a spin and unregister from observers.

  Removes spin from dependency graph and cleans up observer registrations.
  Also cleans up continuations and subscriptions.

  TRANSACTIONAL: All state changes happen atomically in a single swap-state! to
  ensure context consistency for snapshotting.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin whose dependencies to clear

  Returns: true"
  [context spin-id]
  (rtp/swap-state! context []
    (fn [rt-state]
      ;; Get dependencies from SpinNode in :nodes (Phase 1B)
      (let [spin-node (get-in rt-state [:nodes spin-id])
            deps (if spin-node (np/get-deps spin-node) {:signals #{} :spins #{}})
            signal-deps (:signals deps #{})
            spin-deps (:spins deps #{})]

        (-> rt-state
            ;; Clear dependencies in SpinNode (Phase 1B)
            (update-in [:nodes spin-id]
              (fn [node]
                (when node
                  (-> node
                      (np/set-deps {:signals #{} :spins #{}})
                      (np/set-deps-hash nil)
                      (assoc :deps-values {:signal-generations {} :spin-hashes {}})))))

            ;; Unregister from signal observers in :nodes SignalNode (Phase 1B)
            (as-> state
              (reduce (fn [s sid]
                        (let [node (get-in s [:nodes sid])]
                          (if node
                            (update-in s [:nodes sid] #(np/remove-observer % spin-id))
                            s)))
                      state
                      signal-deps))

            ;; Unregister from spin observers in :nodes SpinNode (Phase 1B)
            (as-> state
              (reduce (fn [s tid]
                        (let [node (get-in s [:nodes tid])]
                          (if node
                            (update-in s [:nodes tid] #(np/remove-observer % spin-id))
                            s)))
                      state
                      spin-deps))

            ;; Clear continuations
            (update :continuations dissoc spin-id)

            ;; Clean up subscriptions (remove spin-id from all event keys, remove empty event keys)
            (update :subscriptions
                    (fn [subs]
                      (reduce-kv
                        (fn [acc ek m]
                          (let [m' (dissoc m spin-id)]
                            (if (seq m')
                              (assoc acc ek m')
                              acc)))  ; Don't include empty event keys
                        {}
                        subs)))))))
  true)

(defn track-signal-dep!
  "Track that a spin depends on a signal (during execution).

  Captures signal GENERATION for identity-based caching (O(1) instead of hashing entire value).
  The generation is a monotonically increasing counter that changes whenever the signal is updated.

  This will be committed to the graph when record-deps! is called.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin being tracked
    signal-id - ID of signal being consumed

  Returns: true"
  [context spin-id signal-id]
  ;; Capture signal generation for identity hashing (Phase 1B: read from :nodes)
  (let [signal-node (rtp/get-state context [:nodes signal-id])
        signal-generation (or (:generation signal-node) 0)]
    (rtp/swap-state! context []
      (fn [rt-state]
        ;; Store signal generation for identity hashing (set derived from keys in record-deps!)
        (assoc-in rt-state [:spin-tracking spin-id :signal-generations signal-id]
                  signal-generation))))
  true)

(defn track-spin-dep!
  "Track that a parent spin depends on a child spin (during execution).

  Captures spin's deps-hash for identity-based caching. The deps-hash uniquely identifies
  the spin's computation state based on its dependencies' generations.

  This will be committed to the graph when record-deps! is called.

  Args:
    context - context record (implements PState protocol)
    parent-spin-id - ID of spin doing the await
    child-spin-id - ID of spin being awaited

  Returns: true"
  [context parent-spin-id child-spin-id]
  ;; Capture spin deps-hash for identity hashing (Phase 1B: read from :nodes)
  ;; Note: spin-node may be nil if child spin doesn't exist yet (e.g., in tests)
  (let [spin-node (rtp/get-state context [:nodes child-spin-id])
        spin-deps-hash (when spin-node (np/get-deps-hash spin-node))]
    (rtp/swap-state! context []
      (fn [rt-state]
        ;; Store spin deps-hash for identity hashing (set derived from keys in record-deps!)
        (assoc-in rt-state [:spin-tracking parent-spin-id :spin-hashes child-spin-id]
                  spin-deps-hash))))
  true)

;; =============================================================================
;; Node Access Helpers (Phase 1B - unified :nodes structure)
;; =============================================================================

(defn get-node
  "Get a node by ID from the unified :nodes structure.

  Returns: Node map or nil if not found"
  [context node-id]
  (rtp/get-state context [:nodes node-id]))

(defn swap-node!
  "Atomically update a node in the unified :nodes structure.

  Args:
    context - context record
    node-id - Node identifier
    f - Function to apply to node (takes current node, returns new node)

  Returns: Updated node"
  [context node-id f]
  (rtp/swap-state! context [:nodes node-id] f))

(defn ensure-node!
  "Ensure a node exists with the given type and optional initial data.

  If node doesn't exist, creates it with :type and merges init-data.
  If node exists, does nothing.

  Args:
    context - context record
    node-id - Node identifier
    node-type - :signal or :spin
    init-data - Optional map to merge into new node

  Returns: Node (existing or newly created)"
  [context node-id node-type init-data]
  (rtp/swap-state! context [:nodes node-id]
    (fn [existing-node]
      (or existing-node
          (merge {:type node-type
                  :observers #{}}
                 init-data)))))

(defn get-node-type
  "Get the type of a node (:signal or :spin).

  Returns: :signal, :spin, or nil if node doesn't exist"
  [context node-id]
  (when-let [node (get-node context node-id)]
    (np/node-type node)))

(defn signal-node?
  "Check if a node is a signal.

  Returns: true if node exists and has :type :signal"
  [context node-id]
  (= :signal (get-node-type context node-id)))

(defn spin-node?
  "Check if a node is a spin.

  Returns: true if node exists and has :type :spin"
  [context node-id]
  (= :spin (get-node-type context node-id)))

;; =============================================================================
;; Spin Lifecycle (shared across all context implementations)
;; =============================================================================

(defn register-spin!
  "Register a spin's metadata in the context.

  Also tracks the creator-child relationship:
  - If called during another spin's execution, records that spin as 'created-by'
  - Adds this spin to the creator's 'created-spins' set
  - This enables invalidating child spins when creator reruns

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to register
    spin-meta - Metadata map for the spin

  Returns: true"
  [context spin-id spin-meta]
  ;; Get the current spin-id (creator) from dynamic binding
  (let [creator-id rtc/*spin-id*]

    ;; Write metadata
    (rtp/swap-state! context [:spins-meta spin-id] (constantly spin-meta))

    ;; Create or update SpinNode in :nodes
    (rtp/swap-state! context [:nodes spin-id]
      (fn [existing-node]
        (if existing-node
          ;; Spin already exists - update created-by (closure may have changed)
          (assoc existing-node :created-by creator-id)
          ;; Create new SpinNode with creator tracking
          (nt/->spin-node nil :clean false false #{} {} nil {} creator-id #{}))))

    ;; If there's a creator, add this spin to its created-spins set
    (when creator-id
      (rtp/swap-state! context [:nodes creator-id]
        (fn [creator-node]
          (when creator-node
            (update creator-node :created-spins (fnil conj #{}) spin-id))))))

  true)

(defn mark-dirty!
  "Mark a spin and its observers as dirty (needs re-execution).

  Sets :completed? to false and changes result :status to :dirty.
  Also marks all transitive observers as dirty.

  TRANSACTIONAL: All state changes happen atomically in a single swap-state! to
  ensure context consistency for snapshotting.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to mark dirty

  Returns: true"
  [context spin-id]
  (rtp/swap-state! context []
    (fn [rt-state]
      ;; Get observers from SpinNode (Phase 1B)
      (let [spin-node (get-in rt-state [:nodes spin-id])
            observers (if spin-node (np/get-observers spin-node) #{})]
        (-> rt-state
            ;; Mark spin dirty in :nodes using SpinNode (Phase 1B)
            (update-in [:nodes spin-id]
              (fn [node]
                (when node
                  (-> node
                      (assoc :completed? false)
                      (np/mark-dirty)))))

            ;; Mark all observers dirty in :nodes (Phase 1B)
            (as-> state
              (reduce (fn [s tid]
                        (update-in s [:nodes tid]
                          (fn [node]
                            (when node
                              (-> node
                                  (assoc :completed? false)
                                  (np/mark-dirty))))))
                      state
                      observers))))))
  true)

(defn invalidate-created-spins!
  "Invalidate all spins that were created by this spin during previous execution.

  When a spin re-executes, any spins it previously created have stale closures
  that captured values from the old execution. This function marks those spins
  dirty so they will re-execute with their new closures.

  Also clears the created-spins set since they will be re-registered during
  the new execution.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of the spin that is about to re-execute

  Returns: set of invalidated spin-ids"
  [context spin-id]
  (let [created-spins (rtp/get-state context [:nodes spin-id :created-spins])]
    (when (seq created-spins)
      (log/debug! {:event :spin/invalidate-created
                   :data {:spin-id spin-id :created-spins created-spins}})
      ;; Mark each created spin as dirty
      (doseq [child-id created-spins]
        (mark-dirty! context child-id))
      ;; Clear the created-spins set (they'll be re-registered during execution)
      (rtp/swap-state! context [:nodes spin-id]
        (fn [node]
          (when node
            (assoc node :created-spins #{})))))
    created-spins))

(defn cache-result!
  "Cache a spin's result value and mark observers dirty.

  Marks spin as completed and stores the Result record with :clean status.
  Also marks all observer spins dirty (spins that depend on this one).

  TRANSACTIONAL: All state changes happen atomically in a single swap-state! to
  ensure context consistency for snapshotting.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin whose result to cache
    result - Result record (from is.simm.spindel.spin.result)

  Returns: true"
  [context spin-id result]
  ;; Update :nodes using SpinNode (Phase 1B) AND mark observers dirty
  (rtp/swap-state! context []
    (fn [rt-state]
      ;; First, get observers of this spin before updating it
      (let [spin-node (get-in rt-state [:nodes spin-id])
            observers (if spin-node (np/get-observers spin-node) #{})]
        (-> rt-state
            ;; Mark spin completed with result
            (update-in [:nodes spin-id]
              (fn [node]
                ;; Create SpinNode if it doesn't exist (preserve created-by/created-spins if exists)
                (let [node (or node (nt/->spin-node nil :clean false false #{} {} nil {} nil #{}))]
                  (-> node
                      (assoc :result result)
                      (assoc :completed? true)
                      (assoc :running? false)
                      (np/mark-clean)))))
            ;; Mark all observers dirty (they need to re-execute)
            ;; BUT skip observers that are currently running (have :running? true)
            ;; because those are awaiting this spin via continuation, not observing reactively
            (as-> state
              (reduce (fn [s observer-id]
                        (update-in s [:nodes observer-id]
                          (fn [node]
                            (when (and node (not (:running? node)))
                              (-> node
                                  (assoc :completed? false)
                                  (np/mark-dirty))))))
                      state
                      observers))))))
  true)

(defn current-result
  "Get the current cached result of a spin.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to get result for

  Returns: Result record or nil if not cached"
  [context spin-id]
  ;; NEW: Read from :nodes using protocol (Phase 1B read migration)
  (when-let [node (get-node context spin-id)]
    (np/get-value node)))

(defn clean?
  "Check if a spin's cached result is clean.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to check

  Returns: true if cached result is clean, false if dirty or uncached"
  [context spin-id]
  ;; NEW: Read from :nodes using protocol (Phase 1B read migration)
  (if-let [node (get-node context spin-id)]
    (np/clean? node)
    false))

(defn dirty?
  "Check if a spin's cached result is dirty.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to check

  Returns: true if cached result is dirty, false if clean or uncached"
  [context spin-id]
  ;; NEW: Read from :nodes using protocol (Phase 1B read migration)
  (if-let [node (get-node context spin-id)]
    (np/dirty? node)
    false))

(defn get-deps-hash
  "Get the content hash of a spin's dependencies.

  This hash is computed from the VALUES of dependencies (not IDs) and is
  used for content-addressed caching. Returns nil if spin has no dependencies
  or dependencies haven't been recorded yet.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to get deps-hash for

  Returns: UUID deps-hash or nil"
  [context spin-id]
  ;; NEW: Read from :nodes using protocol (Phase 1B read migration)
  (when-let [node (get-node context spin-id)]
    (np/get-deps-hash node)))

;; =============================================================================
;; Continuation Management (shared across all context implementations)
;; =============================================================================

(defn add-continuation!
  "Add a continuation for a spin.

  TRANSACTIONAL: All state changes happen atomically in a single swap-state! to
  ensure context consistency for snapshotting.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin that owns the continuation
    cont - Continuation map with :event-key, :on-resume, :resolve-fn, :reject-fn

  Returns: Continuation with :id and :order added"
  [context spin-id cont]
  (let [cont-atom (atom nil)]
    (rtp/swap-state! context []
      (fn [rt-state]
        (let [conts (get-in rt-state [:continuations spin-id])
              order (inc (count conts))
              cont-id (or (:id cont) (keyword (str "cont-" (random-uuid))))
              cont' (-> cont (assoc :id cont-id :order order))
              event-key (:event-key cont')]
          ;; Store cont' for return value
          (reset! cont-atom cont')
          ;; Update state atomically
          (-> rt-state
              ;; Store continuation
              (assoc-in [:continuations spin-id cont-id] cont')
              ;; Register subscription
              (update-in [:subscriptions event-key spin-id]
                         (fn [s] (conj (or s #{}) cont-id)))))))
    @cont-atom))

(defn remove-continuation!
  "Remove a continuation from a spin.

  TRANSACTIONAL: All state changes happen atomically in a single swap-state! to
  ensure context consistency for snapshotting.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin that owns the continuation
    cont-id - ID of continuation to remove

  Returns: true"
  [context spin-id cont-id]
  (rtp/swap-state! context []
    (fn [rt-state]
      (let [cont (get-in rt-state [:continuations spin-id cont-id])
            event-key (:event-key cont)]
        (-> rt-state
            ;; Remove continuation
            (update-in [:continuations spin-id] dissoc cont-id)

            ;; Unregister subscription and clean up empty entries
            (update :subscriptions
                    (fn [subs]
                      (let [spin-subs (get-in subs [event-key spin-id])
                            spin-subs' (disj (or spin-subs #{}) cont-id)]
                        (if (seq spin-subs')
                          ;; Still have subscriptions for this spin
                          (assoc-in subs [event-key spin-id] spin-subs')
                          ;; No more subscriptions for this spin
                          (let [event-subs (dissoc (get subs event-key) spin-id)]
                            (if (seq event-subs)
                              ;; Still have other spins subscribed to this event
                              (assoc subs event-key event-subs)
                              ;; No more spins subscribed to this event
                              (dissoc subs event-key)))))))))))
  true)

(defn earliest-continuation
  "Get the earliest continuation for a spin subscribed to a signal or spin completion.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to get continuation for
    signal-id - ID of signal or spin (event-key discriminated by type)

  Returns: Continuation map or nil"
  [context spin-id signal-id]
  (let [rt-state (rtp/get-state context [])
        conts (vals (get-in rt-state [:continuations spin-id]))]
    (first (sort-by :order
                    (filter (fn [c]
                              (when-let [[ek-type ek-id] (:event-key c)]
                                (or (and (= ek-type :signal) (= ek-id signal-id))
                                    (and (= ek-type :spin/complete) (= ek-id signal-id)))))
                            conts)))))

(defn resume-continuation!
  "Resume a continuation with a value.

  Calls :on-resume to get the value, passes it to resume-fn.

  Continuations are NEVER removed - we maintain a fully reactive incremental compute graph
  where all spins remain subscribed to their dependencies and can be resumed multiple times.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin that owns the continuation
    cont - Continuation map
    resume-fn - Function that takes the value and resumes execution

  Returns: Result of resume-fn"
  [context spin-id cont resume-fn]
  (let [;; Call :on-resume to compute the value to pass to resume-fn
        ;; Pass context (not state atom) to allow protocol-based access
        value (if-let [on-resume (:on-resume cont)]
                (on-resume context)
                nil)
        ;; Get captured bindings (default to empty if not present or nil)
        captured-bindings (or (:bindings cont) {})
        ;; Resume with restored bindings
        ;; Force trampolining by binding *in-trampoline* to false
        ;; This ensures that any Thunks returned by resume-fn are executed immediately
        ;; rather than being returned to the caller (which would lose them)
        ret (bindings/restore-bindings captured-bindings
              (fn []
                (binding [pcps-async/*in-trampoline* false]
                  (resume-fn value))))]
    ;; Never remove continuations - maintain fully reactive graph
    ret))

;; =============================================================================
