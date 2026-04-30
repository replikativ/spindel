(ns org.replikativ.spindel.engine.impl.simple
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
  (:require [org.replikativ.spindel.log :as log]
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [is.simm.partial-cps.async :as pcps-async]
            [clojure.set :as set])
  #?(:clj (:import [java.util.concurrent LinkedBlockingQueue ForkJoinPool CountDownLatch]
                    [java.util.concurrent.locks LockSupport])))

;; =============================================================================
;; Drain Context Detection
;; =============================================================================

(def ^:dynamic *in-drain?*
  "True when the current thread is inside drain-events! processing.
   Used by deref-spin to detect re-entrant @(spin ...) which would deadlock."
  false)

;; =============================================================================
;; Forward declarations
;; =============================================================================

(declare track-signal-dep!)
(declare add-pending-callback!)
(declare take-pending-callbacks!)

;; =============================================================================
;; Glitch Prevention - Batch as Context State
;; =============================================================================
;;
;; The batch mechanism prevents FRP glitches by deferring spin completion events
;; during signal-change processing. Instead of dynamic bindings (fragile across
;; thread boundaries), the batch is stored as context state at :engine/current-batch.
;; Any thread with access to the context can find and interact with the batch.
;;
;; See doc/design/runtime-redesign.md for full design rationale.

(defprotocol PBatchQueue
  "Portable queue for batch completion events."
  (batch-put! [q event] "Add event to queue (thread-safe)")
  (batch-take! [q] "Block until event available, return it (JVM: blocks thread, CLJS: throws)")
  (batch-poll! [q] "Non-blocking take, return event or nil"))

#?(:clj
   (deftype BlockingBatchQueue [^LinkedBlockingQueue queue]
     PBatchQueue
     (batch-put! [_ event] (.put queue event))
     (batch-take! [_] (.take queue))
     (batch-poll! [_] (.poll queue)))

   :cljs
   (deftype AtomBatchQueue [events-atom]
     PBatchQueue
     (batch-put! [_ event] (swap! events-atom conj event))
     (batch-take! [_] (throw (ex-info "batch-take! not supported in CLJS (single-threaded)" {})))
     (batch-poll! [_]
       (let [result (atom nil)]
         (swap! events-atom
           (fn [events]
             (if (seq events)
               (do (reset! result (first events))
                   (vec (rest events)))
               events)))
         @result))))

(defn ^:no-doc create-batch-queue
  "Create a platform-appropriate batch queue."
  []
  #?(:clj (->BlockingBatchQueue (LinkedBlockingQueue.))
     :cljs (->AtomBatchQueue (atom []))))

(defn ^:no-doc create-batch
  "Create a Batch data structure for a signal-change processing cycle.

  The batch is stored in context state at :engine/current-batch and coordinates
  glitch-free completion event processing across threads.

  Fields:
    :generation     - monotonic counter for deduplication
    :signal-id      - signal that triggered this batch
    :observers      - set of observer spin-ids expected to complete
    :completed      - atom tracking which observers have completed
    :resumed-conts  - atom tracking [parent child gen] dedup triples
    :processed      - atom tracking spins with fresh cache in this batch
    :processed-events - atom for event deduplication
    :events         - PBatchQueue for completion events
"
  [context signal-id observers]
  (let [gen (rtp/swap-state! context [:engine/batch-generation]
              (fn [gen] (inc (or gen 0))))]
    {:generation gen
     :signal-id signal-id
     :observers (set observers)
     :completed (atom #{})
     :resumed-conts (atom #{})
     :processed (atom #{})
     :processed-events (atom #{})
     :events (create-batch-queue)}))

;; Forward declarations for mutual recursion
(declare trigger-drain!)

(defn ^:no-doc enqueue-completion-event!
  "Enqueue a spin completion event, respecting batch mode.

  If a batch is active in context state (we're in a signal-change batch), routes
  to the batch's event queue. Otherwise enqueues immediately to the engine queue.

  This is the ONLY way spin completions should be enqueued to ensure glitch-freedom.

  Args:
    context - context record
    spin-id - ID of completed spin"
  [context spin-id]
  (if-let [batch (rtp/get-state context [:engine/current-batch])]
    ;; In batch mode - route to batch's event queue (thread-safe via BlockingQueue)
    (do
      (batch-put! (:events batch) {:type :spin-completion :id spin-id})
      ;; Track observer completion
      (when (contains? (:observers batch) spin-id)
        (swap! (:completed batch) conj spin-id))
      ;; Mark as processed early so propagate-await-dirty! knows this spin
      ;; already has a fresh cache (e.g., completed via inline await in Phase 1)
      (swap! (:processed batch) conj spin-id)
      (log/trace! {:event :engine/batch-completion-deferred
                   :data {:spin-id spin-id}}))
    ;; Not in batch - enqueue immediately and trigger drain
    ;; CRITICAL: Must trigger drain for contexts without background drain thread
    ;; (e.g., restored snapshots, forked contexts)
    (do
      (rtp/swap-state-args! context [:engine/pending] conj
                           [{:type :spin-completion :id spin-id}])
      (log/trace! {:event :engine/enqueue-event
                   :data {:event {:type :spin-completion :id spin-id}}})
      (trigger-drain! context (:executor context)))))

;; Forward declaration for generation boundary cleanup
(declare clear-all-await-continuations!)

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
                             ;; IMPORTANT: Preserve :delivery-claimed? for single-assignment semantics
                             (do
                               (reset! pending-callbacks (:pending state))
                               (assoc state
                                      :assigned? true
                                      :value value
                                      :pending [])))))]

    ;; Notify all pending readers INLINE if this was the first assignment
    ;; Event handler already bound *in-trampoline* false
    (when-let [pending @pending-callbacks]
      (doseq [resolve pending]
        (pcps-async/invoke-continuation resolve value)))

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
        (if (and spin-id (ec/spin-is-cancelled? spin-id))
          ;; Cancelled - try next waiter
          (recur)
          ;; Valid waiter - resume it
          ;; Event handler already bound *in-trampoline* false
          (do
            (pcps-async/invoke-continuation resolve msg)
            nil))
        ;; No waiter, message queued
        nil))))

;; =============================================================================
;; Engine state wiring
;; =============================================================================

;; =============================================================================
;; Event Queue Operations
;; =============================================================================

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

(declare try-claim-execution!)
(declare propagate-await-dirty!)
(declare invalidate-created-spins!)

(defn- resume-single-observer!
  "Resume a single observer's track continuation during Phase 1 of signal-change.

  Handles: stale continuation cleanup, signal dep re-tracking, marking dirty/running,
  and resuming the continuation with the fresh signal value.

  Args:
    context - execution context
    spin-id - observer spin to resume
    sid - signal that changed
    cont - the earliest continuation for this observer"
  [context spin-id sid cont]
  (log/debug! {:event :engine/resuming-track-continuation
               :data {:spin-id spin-id :signal-id sid}})

  ;; Remove stale continuations (order > resumed continuation's order)
  (let [cont-order (:order cont)
        all-conts (rtp/get-state context [:continuations spin-id])
        skipped-signal-ids (->> (vals all-conts)
                                (filter #(< (:order %) cont-order))
                                (keep :signal-id))]
    (rtp/swap-state! context [:continuations spin-id]
      (fn [conts]
        (into {} (filter (fn [[k v]] (<= (:order v) cont-order)) conts))))
    (doseq [skipped-sid skipped-signal-ids]
      (track-signal-dep! context spin-id skipped-sid)))

  ;; Re-track the resumed signal dependency
  (track-signal-dep! context spin-id sid)

  ;; Mark spin as not completed, dirty, AND running
  (rtp/swap-state! context [:nodes spin-id]
    (fn [node]
      (when node
        (-> node
            (assoc :completed? false)
            (assoc :running? true)
            (nodes/mark-dirty)))))

  ;; Invalidate child spins created during previous execution
  ;; Their closures captured values from the old run - now stale
  ;; This is the missing call site: spin/core.cljc only calls this during invoke,
  ;; but track resumption also re-executes the spin body from a continuation point
  (invalidate-created-spins! context spin-id)

  ;; Resume continuation with fresh signal value.
  ;; Ephemeral bindings (registered via bindings/register-ephemeral-binding-key!)
  ;; are cleared here because a track resume starts a new render pass; the
  ;; surrounding scope will re-establish them. Persistent bindings (http client,
  ;; execution-mode, app config, ...) are preserved.
  (let [ctx-bindings (:ctx-bindings cont)
        ephemeral-keys (bindings/ephemeral-binding-keys)
        merged-bindings (apply dissoc
                               (if ctx-bindings
                                 (merge (:bindings context) ctx-bindings)
                                 (:bindings context))
                               ephemeral-keys)
        ctx-with-bindings (assoc context :bindings merged-bindings)]
    (binding [ec/*execution-context* ctx-with-bindings
              ec/*spin-id* spin-id
              pcps-async/*in-trampoline* false]
      (rtp/resume-continuation!
       context spin-id cont
       (fn [signal-value]
         (pcps-async/invoke-continuation (:resolve-fn cont) signal-value))))))

(defn- re-execute-dirty-parent!
  "Re-execute a parent/ancestor spin by resuming its earliest track continuation.

  Used by propagate-await-dirty! after a child completes during batch processing
  to re-execute its non-running parent. The parent re-runs from its track point,
  awaits the child (getting fresh cached result), and produces updated output.

  Before re-executing, we invalidate created spins — old children retain stale
  signal registrations that would cause double-executions if not cleaned up.

  Args:
    context - execution context
    spin-id - parent spin to re-execute
    signal-id - signal ID of the parent's earliest track continuation
    cont - the earliest continuation for this parent"
  [context spin-id signal-id cont]
  (log/debug! {:event :engine/re-execute-dirty-parent
               :data {:spin-id spin-id :signal-id signal-id}})

  ;; Remove stale continuations (order > resumed continuation's order)
  (let [cont-order (:order cont)
        all-conts (rtp/get-state context [:continuations spin-id])
        skipped-signal-ids (->> (vals all-conts)
                                (filter #(< (:order %) cont-order))
                                (keep :signal-id))]
    (rtp/swap-state! context [:continuations spin-id]
      (fn [conts]
        (into {} (filter (fn [[k v]] (<= (:order v) cont-order)) conts))))
    (doseq [skipped-sid skipped-signal-ids]
      (track-signal-dep! context spin-id skipped-sid)))

  ;; Re-track the resumed signal dependency
  (track-signal-dep! context spin-id signal-id)

  ;; Mark spin as not completed, dirty, AND running
  (rtp/swap-state! context [:nodes spin-id]
    (fn [node]
      (when node
        (-> node
            (assoc :completed? false)
            (assoc :running? true)
            (nodes/mark-dirty)))))

  ;; Invalidate child spins created during previous execution.
  (invalidate-created-spins! context spin-id)

  ;; Resume continuation with current signal value
  (let [ctx-bindings (:ctx-bindings cont)
        ctx-with-bindings (if ctx-bindings
                            (update context :bindings merge ctx-bindings)
                            context)]
    (binding [ec/*execution-context* ctx-with-bindings
              ec/*spin-id* spin-id
              pcps-async/*in-trampoline* false]
      (rtp/resume-continuation!
       context spin-id cont
       (fn [signal-value]
         (pcps-async/invoke-continuation (:resolve-fn cont) signal-value))))))

(defn- compute-descendant-observers
  "Given observer spin-ids, find those that are descendants of other observers.
  These will be re-created by their parent and should not fire independently."
  [context observer-id-set]
  (loop [to-check observer-id-set
         descendants #{}]
    (if (empty? to-check)
      descendants
      (let [children (into #{}
                      (comp (mapcat #(get (rtp/get-state context [:nodes %]) :created-spins #{}))
                            (filter observer-id-set))
                      to-check)
            new-desc (set/difference children descendants)]
        (recur new-desc (into descendants children))))))

(defn- find-root-await-ancestor
  "Walk await-dependents upward from spin-id to find the topmost ancestor.

  When a child spin is an observer of a changed signal and has an await parent,
  we escalate execution to the root ancestor instead. This prevents double-execution:
  child fires → updates cache → parent re-fires → finds stale cache → 0 deltas.

  Returns the root spin-id if the spin has an await parent chain,
  or nil if the spin has no await parent."
  [context spin-id]
  (let [parents (rtp/get-state context [:await-dependents spin-id])]
    (when (seq parents)
      (loop [current (first parents)
             visited #{spin-id}]
        (if (visited current)
          current ;; cycle detected, return current as root
          (let [grandparents (rtp/get-state context [:await-dependents current])]
            (if (seq grandparents)
              (recur (first grandparents) (conj visited current))
              current)))))))

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
          observers (rtp/ordered-observers context sid)
          ;; Create batch and store in context state
          ;; Any thread with context access can find the batch (no dynamic binding needed)
          batch (create-batch context sid observers)]
      (rtp/swap-state! context [:engine/current-batch] (constantly batch))

      (log/trace! {:event :engine/signal-change
                   :data {:signal-id sid :observers observers :generation (:generation batch)}})


      ;; CRITICAL: Clear await continuations at generation boundary (Design 1)
      ;; Must happen BEFORE track continuations resume to prevent old await
      ;; continuations from being resumed during batch processing
      (clear-all-await-continuations! context)

      ;; Phase 1: Resume track continuations
      ;; With ForkJoinPool: parallel dispatch when >1 observer, sequential otherwise.
      ;; Each observer's state preparation and resume is independent (atomic ops on own node).
      (let [resumed-observers (atom #{})
            ;; Collect observers that have continuations (sequential scan)
            observers-with-conts (vec (keep (fn [spin-id]
                                             (when-let [cont (rtp/earliest-continuation context spin-id sid)]
                                               [spin-id cont]))
                                           observers))
            ;; Filter out descendant observers - they will be re-created by their parent
            ;; and should not fire independently in this drain cycle
            observer-id-set (set (map first observers-with-conts))
            descendant-set (compute-descendant-observers context observer-id-set)
            independent-observers (vec (remove (fn [[sid _]] (descendant-set sid))
                                               observers-with-conts))

            ;; Escalation: children with await parents should not fire independently.
            ;; Instead, escalate to their root ancestor which re-creates the child fresh.
            ;; This prevents double-execution (child fires + parent re-fires → stale cache).
            escalation-targets
            (into {}
              (keep (fn [[spin-id _cont]]
                      (when-let [root-id (find-root-await-ancestor context spin-id)]
                        ;; Check root has track continuations we can resume
                        (when-let [root-conts (seq (vals (rtp/get-state context [:continuations root-id])))]
                          (let [earliest (first (sort-by :order root-conts))]
                            (when (:signal-id earliest)
                              [spin-id {:root-id root-id :cont earliest}]))))))
              independent-observers)

            ;; Direct observers: those NOT being escalated
            direct-observers (if (seq escalation-targets)
                               (vec (remove (fn [[sid _]] (contains? escalation-targets sid))
                                            independent-observers))
                               independent-observers)

            ;; Unique roots to re-execute (deduped — multiple children may share a root)
            roots-to-execute (when (seq escalation-targets)
                               (into {} (map (fn [{:keys [root-id cont]}] [root-id cont]))
                                     (vals escalation-targets)))

            do-resume! (fn [[spin-id cont]]
                         (swap! resumed-observers conj spin-id)
                         (resume-single-observer! context spin-id sid cont))
            do-escalate! (fn [[root-id cont]]
                           (swap! resumed-observers conj root-id)
                           (re-execute-dirty-parent! context root-id (:signal-id cont) cont))]


        (when (seq descendant-set)
          (log/debug! {:event :engine/filtered-descendant-observers
                       :data {:descendants descendant-set
                              :independent (map first independent-observers)}}))

        (when (seq escalation-targets)
          (log/debug! {:event :engine/escalating-to-root-ancestors
                       :data {:escalated (keys escalation-targets)
                              :roots (keys roots-to-execute)}}))

        ;; Add escalated roots to batch observers so their completion is tracked
        (when (seq roots-to-execute)
          (rtp/swap-state! context [:engine/current-batch]
            (fn [batch]
              (when batch
                (update batch :observers into (keys roots-to-execute))))))

        ;; Dispatch direct observers: sequential for 0-1, parallel for >1
        #?(:clj
           (if (<= (count direct-observers) 1)
             ;; Sequential path (no overhead)
             (doseq [obs direct-observers]
               (do-resume! obs))
             ;; Parallel path: dispatch to executor, wait via managedBlock
             (let [executor (:executor context)
                   latch (CountDownLatch. (count direct-observers))]
               (doseq [obs direct-observers]
                 (executor/execute! executor
                   (executor/alive-fn context
                     (fn []
                       (try
                         (do-resume! obs)
                         (finally
                           (.countDown latch)))))))
               ;; Wait for all observers via managedBlock (creates compensating threads)
               (ForkJoinPool/managedBlock
                 (reify java.util.concurrent.ForkJoinPool$ManagedBlocker
                   (block [_]
                     (.await latch)
                     true)
                   (isReleasable [_]
                     (zero? (.getCount latch)))))))
           :cljs
           ;; CLJS: always sequential (single-threaded)
           (doseq [obs direct-observers]
             (do-resume! obs)))

        ;; Escalate to root ancestors (always sequential — modifies shared state)
        (doseq [obs roots-to-execute]
          (do-escalate! obs))

        ;; Update batch observers to only include actually-resumed observers
        ;; Observers without continuations won't produce completion events
        (reset! (:completed batch)
                (set/difference @(:completed batch) (set/difference (:observers batch) @resumed-observers)))
        (let [actual-observers @resumed-observers]

      ;; Phase 2: Process batched completion events (NO POLLING)
      ;; Uses BlockingQueue.take() which blocks with zero CPU until event arrives.
      ;; Events are added by worker threads via enqueue-completion-event! → batch-put!
      (when (seq actual-observers)
        #?(:clj
           (loop []
             ;; Block until an event arrives (zero CPU while waiting)
             (let [comp-event (batch-take! (:events batch))
                   eid (:id comp-event)]
               ;; Process event (dedup + track)
               (when-not (contains? @(:processed-events batch) eid)
                 (swap! (:processed-events batch) conj eid)
                 (swap! (:processed batch) conj eid)
                 (log/debug! {:event :engine/processing-batched-completions
                              :data {:spin-id eid :generation (:generation batch)}})
                 (process-event! context comp-event))
               ;; Drain any additional available events (non-blocking)
               (loop []
                 (when-let [e (batch-poll! (:events batch))]
                   (let [eid2 (:id e)]
                     (when-not (contains? @(:processed-events batch) eid2)
                       (swap! (:processed-events batch) conj eid2)
                       (swap! (:processed batch) conj eid2)
                       (process-event! context e)))
                   (recur)))
               ;; Check if all actually-resumed observers have completed
               (if (every? #(contains? @(:completed batch) %) actual-observers)
                 ;; Final non-blocking drain for cascading events
                 (loop []
                   (when-let [e (batch-poll! (:events batch))]
                     (let [eid3 (:id e)]
                       (when-not (contains? @(:processed-events batch) eid3)
                         (swap! (:processed-events batch) conj eid3)
                         (swap! (:processed batch) conj eid3)
                         (process-event! context e)))
                     (recur)))
                 ;; More observers pending - wait for next event
                 (recur))))
           :cljs
           ;; CLJS: non-blocking drain (TODO: proper callback-based completion)
           (loop []
             (when-let [e (batch-poll! (:events batch))]
               (let [eid (:id e)]
                 (when-not (contains? @(:processed-events batch) eid)
                   (swap! (:processed-events batch) conj eid)
                   (swap! (:processed batch) conj eid)
                   (process-event! context e)))
               (recur)))))))  ;; close (let [actual-observers ...]) and (let [resumed-observers ...])

      ;; Clear batch from context state
      (rtp/swap-state! context [:engine/current-batch] (constantly nil))
      nil)

    :spin-completion
    (let [tid (:id event)
          ;; Get all parent spin-ids that have continuations subscribed
          parent-spin-ids (keys (rtp/get-state context
                                   [:subscriptions [:spin/complete tid]]))
          ;; Read batch from context state (nil when not in batch mode)
          batch (rtp/get-state context [:engine/current-batch])]
      (log/trace! {:event :engine/spin-completion
                   :data {:spin-id tid :parent-spin-ids parent-spin-ids}})

      ;; Resume continuations for spins that are waiting on this spin
      (doseq [parent-id parent-spin-ids]
        ;; Get continuation IDs for this parent
        (let [cont-ids (rtp/get-state context
                         [:subscriptions [:spin/complete tid] parent-id])]
          (doseq [cont-id cont-ids]
            (let [cont (rtp/get-state context
                         [:continuations parent-id cont-id])
                  ;; Generation-based deduplication via batch state (not dynamic bindings)
                  generation (when batch (:generation batch))
                  dedup-key [parent-id tid generation]
                  already-resumed? (when (and generation batch)
                                     (contains? @(:resumed-conts batch) dedup-key))]
              (when (and cont (not already-resumed?))
                ;; Mark [parent child generation] as resumed
                (when (and generation batch)
                  (swap! (:resumed-conts batch) conj dedup-key))
                (log/debug! {:event :engine/resuming-await-continuation
                             :data {:parent-id parent-id :cont-id cont-id :child-id tid
                                    :generation generation}})
                ;; Resume continuation
                (binding [ec/*execution-context* context
                          ec/*spin-id* parent-id
                          pcps-async/*in-trampoline* false]
                  (let [resume-result (rtp/resume-continuation!
                                       context
                                       parent-id
                                       cont
                                       (fn [_child-value-from-on-resume]
                                         ;; Get child's result from :nodes SpinNode
                                         (let [spin-node (rtp/get-state context [:nodes tid])
                                               child-result (when spin-node (:result spin-node))]
                                           (if (= (:variant child-result) :ok)
                                             (pcps-async/invoke-continuation (:resolve-fn cont) (:payload child-result))
                                             (pcps-async/invoke-continuation (:reject-fn cont) (:payload child-result))))))]
                    resume-result)))))))

      ;; Propagate dirty flag through await dependency graph
      (propagate-await-dirty! context tid)
      nil)

    :deferred-delivery
    (let [deferred (:deferred event)
          value (:value event)
          ;; Direct deftype field access. ^js (CLJS-only) suppresses the
          ;; :infer-warning. JVM doesn't need a hint here — the access
          ;; goes through reflection, which is acceptable on a path
          ;; that's already heading into atom mutation.
          state-atom #?(:clj  (.-state-atom deferred)
                        :cljs (.-state-atom ^js deferred))]
      (log/trace! {:event :engine/deferred-delivery
                   :data {:deferred deferred :value value}})
      ;; Deliver inline - we're already on executor thread, queue broke the call stack
      ;; CRITICAL: Bind *execution-context* and *in-trampoline* when delivering deferred value
      ;; The deferred function will resume continuations which need context access
      ;; CRITICAL: Bind *execution-context* so current-execution-context returns correct context
      (binding [ec/*execution-context* context
                pcps-async/*in-trampoline* false]
        (deliver-inline! deferred value state-atom))
      nil)

    :mailbox-post
    (let [mailbox (:mailbox event)
          msg (:msg event)
          ;; Same per-platform hint pattern as :deferred-delivery.
          state-atom #?(:clj  (.-state-atom mailbox)
                        :cljs (.-state-atom ^js mailbox))]
      (log/trace! {:event :engine/mailbox-post
                   :data {:mailbox mailbox :msg msg}})
      ;; Post inline - we're already on executor thread, queue broke the call stack
      ;; CRITICAL: Bind *execution-context* and *in-trampoline* when posting to mailbox
      ;; The mailbox function will resume continuations which need context access
      (binding [ec/*execution-context* context
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
      ;; Try to atomically claim execution
      ;; This checks cache AND running? atomically to prevent duplicate execution
      (if-not (try-claim-execution! context tid)
        ;; Failed to claim - either cached or already running
        ;; Check which case to handle appropriately
        (let [node (rtp/get-state context [:nodes tid])
              cached (when node (nodes/get-value node))
              is-clean? (when node (not (nodes/dirty? node)))]
          (if (and cached is-clean?)
            ;; Already cached - deliver result via callbacks without re-executing
            (do
              (log/trace! {:event :engine/spin-execution-cached
                           :data {:spin-id tid}})
              (if (= (:variant cached) :ok)
                (resolve-fn (:payload cached))
                (reject-fn (:payload cached))))
            ;; Not cached - must be running, add callbacks to pending
            (do
              (log/trace! {:event :engine/spin-execution-skip-running
                           :data {:spin-id tid}})
              (add-pending-callback! context tid {:resolve resolve-fn :reject reject-fn}))))
        ;; Successfully claimed - proceed with execution
        ;; Execute spin on executor thread with provided callbacks
        ;; CRITICAL: Bind *in-trampoline* to false when re-entering from event handler
        ;; This ensures invoke-continuation establishes a new trampoline loop
        ;; If execution-context is provided (e.g., from SMC), bind it; otherwise use context
        (binding [ec/*execution-context* (or execution-context context)
                  ec/*spin-id* tid
                  pcps-async/*in-trampoline* false]
          ;; Invoke spin (Spin implements IFn)
          (let [result (spin resolve-fn reject-fn)]
            nil))))

    ;; Unknown event type
    (do
      (log/trace! {:event :engine/unknown-event :data {:event event}})
      nil)))

;; Forward declaration for mutual recursion
(declare trigger-drain!)

(defn ^:no-doc drain-events!
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
        (binding [*in-drain?* true]
        (let [event-count (atom 0)]
          ;; Drain loop
          (loop []
            (if-let [event (dequeue-event! context)]
              (do
                ;; Process event (may enqueue more events)
                ;; CRITICAL: Catch exceptions per-event so one bad event doesn't abort the
                ;; entire drain session (which would silently lose all remaining queued events).
                ;; For :spin-execution events, call reject-fn to unblock any waiting deref.
                (try
                  (process-event! context event)
                  (catch #?(:clj Throwable :cljs js/Error) e
                    (log/error! {:event :engine/event-processing-error
                                 :data {:event-type (:type event)
                                        :event-id (:id event)
                                        :error #?(:clj (.getMessage ^Throwable e) :cljs (str e))}})
                    (case (:type event)
                      ;; For spin-execution events, deliver the error to the deref promise
                      ;; so the calling thread unblocks with an exception instead of hanging
                      :spin-execution
                      (when-let [reject-fn (:reject-fn event)]
                        (try (reject-fn e)
                             (catch #?(:clj Throwable :cljs :default) _)))

                      ;; For spin-completion events, the parent spin's continuation threw.
                      ;; Cache the error in the parent so its awaiters also see the failure.
                      :spin-completion
                      (let [parent-ids (keys (rtp/get-state context
                                               [:subscriptions [:spin/complete (:id event)]]))]
                        (doseq [pid parent-ids]
                          (try
                            (rtp/swap-state! context [:nodes pid]
                              (fn [node]
                                (when node
                                  (assoc node :result {:variant :error :payload e}))))
                            (catch #?(:clj Throwable :cljs :default) _))))

                      ;; Other event types: already logged, no additional action
                      nil)))
                (swap! event-count inc)
                ;; Continue draining
                (recur))
              ;; Queue empty - done
              (do
                (log/trace! {:event :engine/drain-complete
                             :data {:events-processed @event-count}})
                @event-count)))))
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
  "Wait for event queue to drain AND all spins to complete execution.

  Waits until:
  - :engine/draining? is false (no active drain session)
  - :engine/pending is empty (no queued events)
  - No spins have :running? = true (no in-flight spin bodies)

  JVM: Uses ForkJoinPool.managedBlock + LockSupport.parkNanos (100us)
  instead of Thread/sleep (1ms). 10x lower latency, and managedBlock tells
  ForkJoinPool to create compensating threads if this is a pool thread.

  CLJS: A synchronous wait on the JS thread cannot observe setTimeout
  callbacks fire, so this returns the current state (true when already
  drained, false otherwise) without blocking. Use the async-test patterns
  (run-spin! callbacks, async done) to observe drain completion in CLJS.

  Args:
    context - context record
    timeout-ms - Max time to wait (default 5000ms; unused on CLJS)

  Returns: true if drain completed, false if timeout (or false on CLJS
           when not yet complete)"
  [context & {:keys [timeout-ms] :or {timeout-ms 5000}}]
  #?(:clj
     (let [start (System/currentTimeMillis)
           deadline (+ start timeout-ms)
           done? (fn []
                   (let [draining? (rtp/get-state context [:engine/draining?])
                         pending (rtp/get-state context [:engine/pending])
                         nodes (rtp/get-state context [:nodes])
                         running-spins (filter (fn [[_id node]] (:running? node)) nodes)]
                     (and (not draining?) (empty? pending) (empty? running-spins))))]
       (if (done?)
         true
         ;; Use managedBlock so ForkJoinPool creates compensating threads
         (let [result (volatile! false)]
           (ForkJoinPool/managedBlock
             (reify java.util.concurrent.ForkJoinPool$ManagedBlocker
               (block [_]
                 (LockSupport/parkNanos (* 100 1000)) ; 100 microseconds
                 (let [d (done?)]
                   (when d (vreset! result true))
                   (or d (>= (System/currentTimeMillis) deadline))))
               (isReleasable [_]
                 (cond
                   (done?)
                   (do (vreset! result true) true)
                   (>= (System/currentTimeMillis) deadline)
                   true ; timeout - result stays false
                   :else false))))
           @result)))
     :cljs
     ;; CLJS cannot truly await: a synchronous loop on the JS thread cannot
     ;; observe setTimeout-driven workers complete, so a busy-wait would burn
     ;; CPU until the deadline and never see progress. Instead we report the
     ;; current drain status and let the caller use async/await patterns
     ;; (run-spin! callbacks, async done) to observe completion. timeout-ms
     ;; is accepted for cross-platform call-site compatibility but unused.
     (let [_ timeout-ms
           draining? (rtp/get-state context [:engine/draining?])
           pending (rtp/get-state context [:engine/pending])
           nodes (rtp/get-state context [:nodes])
           running-spins (filter (fn [[_id node]] (:running? node)) nodes)]
       (and (not draining?) (empty? pending) (empty? running-spins)))))

(defn ^:no-doc trigger-drain!
  "Trigger async draining of the event queue.

  Schedules drain-events! to run on the executor AND wakes the background
  drain thread via drain-signal (if present). Does not wait for completion.

  This is called after external changes to ensure events are processed
  eventually. If draining is already in progress, the new events will
  be picked up by the current drain session (via CAS in drain-events!).

  IMPORTANT: This intentionally does NOT check draining? flag before scheduling.
  Multiple trigger-drain! calls may schedule redundant drain-events!, but the CAS
  in drain-events! ensures only one drains at a time. Redundant drains see empty
  queue and exit immediately. This design ensures events eventually get processed
  even with concurrent trigger-drain! calls.

  Args:
    context - context record
    executor - Executor to schedule drain on

  Returns: true if scheduled, false if no executor available"
  [context executor]
  ;; Wake background drain thread via notification queue (zero-polling)
  #?(:clj
     (when-let [ds (:drain-signal context)]
       (.offer ^java.util.concurrent.LinkedBlockingQueue ds :drain)))
  (if executor
    (do
      (executor/execute! executor
        (executor/alive-fn context
          #(drain-events! context executor)))
      (log/trace! {:event :engine/trigger-drain})
      true)
    (do
      (log/trace! {:event :engine/trigger-drain-no-executor})
      false)))


;; =============================================================================
;; Dependency Tracking (shared across all context implementations)
;; =============================================================================

(defn record-deps!
  "Record dependencies tracked during spin execution into the dependency graph.

  Takes the temporary tracking data from [:spin-tracking spin-id] and commits
  it to the permanent dependency sets on the SpinNode, updating observer
  registrations on signals and spins.

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
          (let [tracked-signals (:signals tracked-deps #{})
                tracked-spins   (:spins tracked-deps #{})
                spin-node (get-in rt-state [:nodes spin-id])
                old-deps (if spin-node (nodes/get-deps spin-node) {:signals #{} :spins #{}})
                old-signals (:signals old-deps #{})
                old-spins (:spins old-deps #{})
                removed-signals (set/difference old-signals tracked-signals)
                removed-spins (set/difference old-spins tracked-spins)]

        (-> rt-state
            ;; Update SpinNode in :nodes with dependencies (Phase 1B)
            (update-in [:nodes spin-id]
              (fn [node]
                ;; Create SpinNode if it doesn't exist (preserve created-by/created-spins if exists)
                (let [node (or node (nodes/->spin-node nil :clean false false #{} {} nil #{}))]
                  (nodes/set-deps node {:signals tracked-signals
                                        :spins tracked-spins}))))

            ;; Remove spin from old signal observers in :nodes SignalNode (Phase 1B)
            (as-> state
              (reduce (fn [s sid]
                        (let [node (get-in s [:nodes sid])]
                          (if node
                            (update-in s [:nodes sid] #(nodes/remove-observer % spin-id))
                            s)))
                      state
                      removed-signals))

            ;; Add spin to new signal observers in :nodes SignalNode (Phase 1B)
            (as-> state
              (reduce (fn [s sid]
                        (let [node (get-in s [:nodes sid])]
                          (if node
                            (update-in s [:nodes sid] #(nodes/add-observer % spin-id))
                            s)))
                      state
                      tracked-signals))

            ;; Remove spin from old spin observers in :nodes SpinNode (Phase 1B)
            (as-> state
              (reduce (fn [s tid]
                        (let [node (get-in s [:nodes tid])]
                          (if node
                            (update-in s [:nodes tid] #(nodes/remove-observer % spin-id))
                            s)))
                      state
                      removed-spins))

            ;; Add spin to new spin observers in :nodes SpinNode (Phase 1B)
            (as-> state
              (reduce (fn [s tid]
                        ;; Create node if it doesn't exist, then add observer
                        (update-in s [:nodes tid]
                          (fn [node]
                            (let [node (or node (nodes/->spin-node nil :clean false false #{} {} nil #{}))]
                              (nodes/add-observer node spin-id)))))
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
            deps (if spin-node (nodes/get-deps spin-node) {:signals #{} :spins #{}})
            signal-deps (:signals deps #{})
            spin-deps (:spins deps #{})]

        (-> rt-state
            ;; Clear dependencies in SpinNode (Phase 1B)
            (update-in [:nodes spin-id]
              (fn [node]
                (when node
                  (nodes/set-deps node {:signals #{} :spins #{}}))))

            ;; Unregister from signal observers in :nodes SignalNode (Phase 1B)
            (as-> state
              (reduce (fn [s sid]
                        (let [node (get-in s [:nodes sid])]
                          (if node
                            (update-in s [:nodes sid] #(nodes/remove-observer % spin-id))
                            s)))
                      state
                      signal-deps))

            ;; Unregister from spin observers in :nodes SpinNode (Phase 1B)
            (as-> state
              (reduce (fn [s tid]
                        (let [node (get-in s [:nodes tid])]
                          (if node
                            (update-in s [:nodes tid] #(nodes/remove-observer % spin-id))
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

(defn full-cleanup-spin!
  "Remove ALL runtime state for a spin atomically.

  Unlike clear-deps! which only clears deps/continuations/subscriptions,
  this removes the spin node itself and all 8+ state locations.

  Used by GC cleanup when a spin is safe to fully remove (no observers).

  TRANSACTIONAL: All state changes happen atomically in a single swap-state!.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to fully remove

  Returns: true"
  [context spin-id]
  (rtp/swap-state! context []
    (fn [state]
      (let [node (get-in state [:nodes spin-id])
            deps (when node (nodes/get-deps node))
            signal-deps (:signals deps #{})
            spin-deps (:spins deps #{})]
        (-> state
            ;; 1. Unregister from signal observers
            (as-> s (reduce (fn [s sid]
                              (if (get-in s [:nodes sid])
                                (update-in s [:nodes sid] nodes/remove-observer spin-id)
                                s))
                            s signal-deps))
            ;; 2. Unregister from spin observers
            (as-> s (reduce (fn [s tid]
                              (if (get-in s [:nodes tid])
                                (update-in s [:nodes tid] nodes/remove-observer spin-id)
                                s))
                            s spin-deps))
            ;; 3. Remove the spin node itself
            (update :nodes dissoc spin-id)
            ;; 4. Remove metadata
            (update :spins-meta dissoc spin-id)
            ;; 5. Remove cached output
            (update :spin-outputs dissoc spin-id)
            ;; 6. Remove continuations
            (update :continuations dissoc spin-id)
            ;; 7. Remove pending callbacks
            (update :pending-callbacks dissoc spin-id)
            ;; 8. Remove tracking data
            (update :spin-tracking dissoc spin-id)
            ;; 9. Clean subscriptions (remove spin-id from all event keys)
            (update :subscriptions
              (fn [subs]
                (when subs
                  (persistent!
                    (reduce-kv (fn [acc ek m]
                                 (let [m' (dissoc m spin-id)]
                                   (if (seq m') (assoc! acc ek m') acc)))
                               (transient {}) subs)))))
            ;; 10. Clean await-dependents:
            ;;     - Remove this spin's own entry (it can no longer be a child)
            ;;     - Remove this spin as a parent in every other entry
            (update :await-dependents
              (fn [deps]
                (when deps
                  (persistent!
                    (reduce-kv (fn [m child-id parents]
                                 (if (= child-id spin-id)
                                   m  ; drop this spin's own entry
                                   (let [parents' (disj parents spin-id)]
                                     (if (seq parents')
                                       (assoc! m child-id parents')
                                       m))))
                               (transient {}) deps)))))))))
  true)

(defn try-gc-cleanup-spin!
  "Called from GC callback. Attempts full cleanup if safe, otherwise marks
  the spin as orphaned for deferred cleanup.

  A spin is safe to fully clean when:
  1. Its Spin object was GC'd (caller ensures this)
  2. It has no observers (no other spins depend on it)

  If the spin has observers, it's marked :orphaned? true. When those observers
  are eventually cleaned up and this spin loses its last observer, cascading
  cleanup will remove it.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin whose Spin object was GC'd

  Returns: nil"
  [context spin-id]
  (let [node (rtp/get-state context [:nodes spin-id])]
    (when node ;; may already be cleaned
      (if (empty? (nodes/get-observers node))
        ;; No observers → full cleanup + cascade to dependencies
        (let [deps (nodes/get-deps node)
              dep-spin-ids (:spins deps #{})]
          (full-cleanup-spin! context spin-id)
          ;; Cascade: check if any spin dependency is now cleanable
          (doseq [dep-id dep-spin-ids]
            (let [dep-node (rtp/get-state context [:nodes dep-id])]
              (when (and dep-node
                         (:orphaned? dep-node)
                         (empty? (nodes/get-observers dep-node)))
                (full-cleanup-spin! context dep-id)))))
        ;; Has observers → mark orphaned, defer cleanup
        (rtp/swap-state! context [:nodes spin-id]
          #(when % (assoc % :orphaned? true)))))))

(defn track-signal-dep!
  "Track that a spin depends on a signal (during execution).

  Records signal-id in the spin's pending tracking set. Committed to the
  SpinNode's :deps when record-deps! runs.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin being tracked
    signal-id - ID of signal being consumed

  Returns: true"
  [context spin-id signal-id]
  (rtp/swap-state! context []
    (fn [rt-state]
      (update-in rt-state [:spin-tracking spin-id :signals]
                 (fnil conj #{}) signal-id)))
  true)

(defn track-spin-dep!
  "Track that a parent spin depends on a child spin (during execution).

  Records child-spin-id in the parent's pending tracking set. Committed to
  the parent's :deps when record-deps! runs.

  Args:
    context - context record (implements PState protocol)
    parent-spin-id - ID of spin doing the await
    child-spin-id - ID of spin being awaited

  Returns: true"
  [context parent-spin-id child-spin-id]
  (rtp/swap-state! context []
    (fn [rt-state]
      (update-in rt-state [:spin-tracking parent-spin-id :spins]
                 (fnil conj #{}) child-spin-id)))
  true)

;; =============================================================================
;; Node Access Helpers (Phase 1B - unified :nodes structure)
;; =============================================================================

(defn ^:no-doc get-node
  "Get a node by ID from the unified :nodes structure.

  Returns: Node map or nil if not found"
  [context node-id]
  (rtp/get-state context [:nodes node-id]))


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
  (let [creator-id ec/*spin-id*]

    ;; Write metadata
    (rtp/swap-state! context [:spins-meta spin-id] (constantly spin-meta))

    ;; Create or update SpinNode in :nodes
    (rtp/swap-state! context [:nodes spin-id]
      (fn [existing-node]
        (if existing-node
          ;; Spin already exists - update created-by (closure may have changed)
          (assoc existing-node :created-by creator-id)
          ;; Create new SpinNode with creator tracking
          (nodes/->spin-node nil :clean false false #{} {} creator-id #{}))))

    ;; If there's a creator (other than ourselves), add this spin to its
    ;; created-spins set. Self-add could occur on CLJS if a stale async
    ;; callback from a stopped context restores *spin-id* to a value
    ;; that deterministic addressing then re-issues to a different
    ;; spin in a fresh context. The primary defense is executor/alive-fn,
    ;; which drops scheduled callbacks whose context has been stopped,
    ;; so the binding-leak path can't fire. This guard remains as a
    ;; final invariant: a spin literally cannot be its own creator.
    (when (and creator-id (not= creator-id spin-id))
      (rtp/swap-state! context [:nodes creator-id]
        (fn [creator-node]
          (when creator-node
            (update creator-node :created-spins (fnil conj #{}) spin-id))))))

  true)

(defn mark-dirty!
  "Mark a spin and its observers as dirty (needs re-execution).

  Sets :completed? to false and changes result :status to :dirty.
  Also marks all transitive observers as dirty.
  During batch mode, also marks await dependents dirty (Design 1) recursively.

  TRANSACTIONAL: All state changes happen atomically in a single swap-state! to
  ensure context consistency for snapshotting.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to mark dirty

  Returns: true"
  [context spin-id]
  (rtp/swap-state! context []
    (fn [rt-state]
      ;; Collect all nodes to mark dirty using breadth-first traversal
      ;; This ensures we mark the full transitive closure of dependents
      (let [in-batch? (some? (get rt-state :engine/current-batch))]
        (loop [to-visit #{spin-id}
               visited #{}
               state rt-state]
          (if (empty? to-visit)
            state
            (let [current-id (first to-visit)
                  remaining (disj to-visit current-id)]
              (if (visited current-id)
                (recur remaining visited state)
                (let [spin-node (get-in state [:nodes current-id])
                      observers (if spin-node (nodes/get-observers spin-node) #{})
                      ;; During batch mode, also include await dependents for full propagation
                      await-parents (when in-batch?
                                     (get-in state [:await-dependents current-id]))
                      next-to-mark (into (or observers #{}) (or await-parents #{}))
                      ;; Filter out already visited to avoid infinite loops
                      new-to-visit (into remaining (remove visited next-to-mark))
                      ;; Mark current node dirty
                      new-state (update-in state [:nodes current-id]
                                  (fn [node]
                                    (when node
                                      (-> node
                                          (assoc :completed? false)
                                          (nodes/mark-dirty)))))]
                  (recur new-to-visit (conj visited current-id) new-state)))))))))
  true)

(defn clear-all-await-continuations!
  "Clear ephemeral await continuations from completed spins at generation boundary.

  Only clears continuations marked with :ephemeral-await? true. This preserves
  persistent reactive continuations (like those from the parallel combinator)
  while clearing ephemeral await continuations that should not persist across
  signal-change boundaries.

  Called at generation boundaries to ensure clean separation between generations.

  Args:
    context - context record (implements PState protocol)

  Returns: map of {:spins-affected count :continuations-cleared count}"
  [context]
  (let [all-nodes (rtp/get-state context [:nodes])
        result (atom {:spins-affected 0 :continuations-cleared 0})]

    (doseq [[spin-id node] all-nodes]
      (when node
        ;; CRITICAL: Only clear await continuations from COMPLETED spins
        ;; If a spin is still running (suspended awaiting children), DON'T clear
        ;; its continuations or it will be orphaned and never resume
        (when (and (:completed? node) (not (:running? node)))
          (let [all-conts (rtp/get-state context [:continuations spin-id])
                ;; Filter to only EPHEMERAL await continuations (marked with :ephemeral-await? true)
                ;; This excludes persistent reactive continuations (like parallel's) which should NOT be cleared
                await-conts (filter (fn [[_k v]]
                                     (:ephemeral-await? v))
                                   all-conts)]
            (when (seq await-conts)
              (swap! result update :spins-affected inc)
              (swap! result update :continuations-cleared + (count await-conts))

              ;; Remove await continuations and their subscriptions atomically
              (rtp/swap-state! context []
                (fn [rt-state]
                  (reduce
                    (fn [state [cont-id cont]]
                      (let [[_event-type child-id] (:event-key cont)
                            ;; Remove continuation
                            state' (update-in state [:continuations spin-id] dissoc cont-id)
                            ;; Remove subscription
                            spin-subs (get-in state' [:subscriptions [:spin/complete child-id] spin-id])
                            spin-subs' (disj (or spin-subs #{}) cont-id)]
                        (if (seq spin-subs')
                          ;; Still have subscriptions
                          (assoc-in state' [:subscriptions [:spin/complete child-id] spin-id] spin-subs')
                          ;; No more subscriptions for this spin - remove entry
                          (update-in state' [:subscriptions [:spin/complete child-id]] dissoc spin-id))))
                    rt-state
                    await-conts))))))))

    ;; CRITICAL: Do NOT clear :await-dependents here!
    ;; Await dependencies must persist through batch processing for dirty propagation.
    ;; When a child completes during batch, propagate-await-dirty! needs these dependencies
    ;; to mark parent spins dirty. Dependencies are naturally overwritten as spins re-execute.

    (let [stats @result]
      (when (pos? (:continuations-cleared stats))
        (log/debug! {:event :generation/clear-await-continuations
                     :data stats}))
      stats)))

(defn ^:no-doc record-await-dependency!
  "Record that parent-spin awaits child-spin for dirty propagation.

  When a spin registers an await continuation for another spin, we record
  this dependency relationship. Later, when the child completes dirty,
  we can propagate the dirty flag to all parents that await it.

  This is the core mechanism for ephemeral await semantics - dependencies
  are recorded during execution but cleared at generation boundaries.

  Args:
    context - runtime context
    parent-spin-id - spin that is awaiting
    child-spin-id - spin being awaited"
  [context parent-spin-id child-spin-id]
  (rtp/swap-state! context [:await-dependents child-spin-id]
    (fn [parents]
      (conj (or parents #{}) parent-spin-id)))
  (log/trace! {:event :await/record-dependency
               :data {:parent parent-spin-id :child child-spin-id}}))

(defn ^:no-doc propagate-await-dirty!
  "Propagate dirty flag through await dependency graph.

  When a spin completes during batch processing (signal change),
  all spins awaiting it are marked dirty to ensure they re-execute
  with fresh values.

  This prevents glitches where parent observes stale child cache.
  Called after spin completion. Only propagates during batch mode.

  CRITICAL: Only propagate to COMPLETED parents, not to parents that are
  currently executing/suspended. If a parent is already executing and
  suspended on this await, it will get the fresh value when it resumes -
  no need to mark it dirty.

  Args:
    context - runtime context
    spin-id - spin that just completed"
  [context spin-id]
  ;; Only propagate during batch processing (when in signal-change handling)
  (when-let [batch (rtp/get-state context [:engine/current-batch])]
    (let [awaiting-parents (rtp/get-state context [:await-dependents spin-id])]
      (when (seq awaiting-parents)
        (let [completion-event-key [:spin/complete spin-id]
              processed @(:processed batch)
              parents-to-dirty (filter
                                 (fn [parent-id]
                                   (let [parent-node (rtp/get-state context [:nodes parent-id])
                                         has-completion-continuation
                                         (seq (rtp/get-state context [:subscriptions completion-event-key parent-id]))]
                                     (and parent-node
                                          (not (:running? parent-node))
                                          (not has-completion-continuation)
                                          (not (contains? processed parent-id)))))
                                 awaiting-parents)]
          (when (seq parents-to-dirty)
            (log/debug! {:event :engine/propagate-await-dirty
                         :data {:from-spin spin-id
                                :to-parents parents-to-dirty
                                :count (count parents-to-dirty)
                                :skipped (- (count awaiting-parents) (count parents-to-dirty))}})
            (doseq [parent-id parents-to-dirty]
              (mark-dirty! context parent-id)
              (when-let [conts (seq (vals (rtp/get-state context [:continuations parent-id])))]
                (let [earliest (first (sort-by :order conts))
                      sid (:signal-id earliest)]
                  (when sid
                    (re-execute-dirty-parent! context parent-id sid earliest)))))))))))

(defn ^:no-doc invalidate-created-spins!
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
      ;; Mark each created spin as dirty and fully clean up dependencies
      ;; clear-deps! removes track continuations, subscriptions, and signal observer
      ;; registrations so old children can't fire on future signal changes.
      ;; Skip self-references defensively — register-spin! also prevents
      ;; them, but a stale state map could still contain one.
      (doseq [child-id created-spins
              :when (not= child-id spin-id)]
        (mark-dirty! context child-id)
        (clear-deps! context child-id)
        ;; Recursively invalidate grandchildren
        (invalidate-created-spins! context child-id))
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
    result - Result record (from org.replikativ.spindel.spin.core)

  Returns: true"
  [context spin-id result]
  ;; Update :nodes using SpinNode (Phase 1B) AND mark observers dirty
  (rtp/swap-state! context []
    (fn [rt-state]
      ;; First, get observers of this spin before updating it
      (let [spin-node (get-in rt-state [:nodes spin-id])
            observers (if spin-node (nodes/get-observers spin-node) #{})
            ;; Build the completion event key for this spin
            completion-event-key [:spin/complete spin-id]]
        (-> rt-state
            ;; Mark spin completed with result
            (update-in [:nodes spin-id]
              (fn [node]
                ;; Create SpinNode if it doesn't exist (preserve created-by/created-spins if exists)
                (let [node (or node (nodes/->spin-node nil :clean false false #{} {} nil #{}))]
                  (-> node
                      (assoc :result result)
                      (assoc :completed? true)
                      (assoc :running? false)
                      (nodes/mark-clean)))))
            ;; Mark all observers dirty (they need to re-execute)
            ;; BUT skip observers that:
            ;; 1. Are currently running (have :running? true)
            ;; 2. Have a continuation for this spin's completion event
            ;; Both cases mean the observer will be notified via continuation, not dirty flag
            (as-> state
              (reduce (fn [s observer-id]
                        (let [has-completion-cont? (seq (get-in s [:subscriptions completion-event-key observer-id]))]
                          (update-in s [:nodes observer-id]
                            (fn [node]
                              (when (and node
                                         (not (:running? node))
                                         (not has-completion-cont?))
                                (-> node
                                    (assoc :completed? false)
                                    (nodes/mark-dirty)))))))
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
    (nodes/get-value node)))

(defn clean?
  "Check if a spin's cached result is clean.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to check

  Returns: true if cached result is clean, false if dirty or uncached"
  [context spin-id]
  ;; NEW: Read from :nodes using protocol (Phase 1B read migration)
  (if-let [node (get-node context spin-id)]
    (nodes/clean? node)
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
    (nodes/dirty? node)
    false))

(defn running?
  "Check if a spin is currently executing.

  Returns true if the spin is in-flight (execution started but not yet
  completed via cache-result!). This includes spins that are suspended
  waiting on a deferred.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to check

  Returns: true if spin is executing, false otherwise"
  [context spin-id]
  (if-let [node (get-node context spin-id)]
    (:running? node)
    false))

(defn ^:no-doc mark-running!
  "Mark a spin as currently executing.

  Sets the running? flag to true. Called at the start of direct spin execution
  (Case 3 in invoke path) to indicate the spin is in-flight.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to mark as running

  Returns: true"
  [context spin-id]
  (rtp/swap-state! context [:nodes spin-id]
    (fn [node]
      (if node
        (assoc node :running? true)
        (nodes/->spin-node nil :clean false true #{} {} nil #{}))))
  true)

(defn ^:no-doc try-claim-execution!
  "Atomically try to claim execution of a spin.

  Uses atomic swap to check cached/running? and set running? in one operation.
  If already running OR already cached (clean), returns false without modifying state.
  If not running and not cached, atomically sets running?=true and returns true.

  This is CRITICAL for preventing duplicate execution when multiple
  :spin-execution events are enqueued for the same spin. The cache check
  must be atomic with the claim to prevent the race where thread A checks
  cache, thread B completes and caches, then thread A claims and re-executes.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to claim

  Returns: true if claimed (proceed to execute)
           false if already running/cached (skip execution or use cached value)"
  [context spin-id]
  (let [claimed? (atom false)]
    (rtp/swap-state! context [:nodes spin-id]
      (fn [node]
        (if node
          (let [cached (nodes/get-value node)
                is-clean? (not (nodes/dirty? node))]
            (cond
              ;; Already has clean cached result - don't claim
              (and cached is-clean?)
              (do (reset! claimed? false)
                  (log/trace! {:event :claim/failed-already-cached :data {:spin-id spin-id}})
                  node)

              ;; Already running - don't claim
              (:running? node)
              (do (reset! claimed? false)
                  (log/trace! {:event :claim/failed-already-running :data {:spin-id spin-id}})
                  node)

              ;; Not running and not cached - claim it
              :else
              (do (reset! claimed? true)
                  (log/trace! {:event :claim/success-from-existing :data {:spin-id spin-id}})
                  (assoc node :running? true))))
          ;; No node - create and claim
          (do (reset! claimed? true)
              (log/trace! {:event :claim/success-new-node :data {:spin-id spin-id}})
              (nodes/->spin-node nil :clean false true #{} {} nil #{})))))
    @claimed?))

(defn ^:no-doc mark-not-running!
  "Clear the running? flag for a spin.

  Called when a spin yields (returns ::incomplete) to indicate it's no longer
  actively executing - it's suspended waiting for a continuation.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin to mark as not running

  Returns: true"
  [context spin-id]
  (rtp/swap-state! context [:nodes spin-id]
    (fn [node]
      (when node
        (assoc node :running? false))))
  true)

(defn ^:no-doc add-pending-callback!
  "Add a callback to be invoked when a currently-running spin completes.

  When multiple :spin-execution events are enqueued for the same spin,
  the first one executes and subsequent ones add their callbacks here.
  When the spin completes, all pending callbacks are invoked.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin
    callback - Map with :resolve and :reject functions

  Returns: true"
  [context spin-id callback]
  (rtp/swap-state! context [:pending-callbacks spin-id]
    (fn [callbacks]
      (conj (or callbacks []) callback)))
  true)

(defn ^:no-doc take-pending-callbacks!
  "Atomically take and clear all pending callbacks for a spin.

  Called when a spin completes to get all callbacks that need to be notified.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin

  Returns: Vector of callback maps"
  [context spin-id]
  (let [result (atom nil)]
    (rtp/swap-state! context [:pending-callbacks spin-id]
      (fn [callbacks]
        (reset! result callbacks)
        nil))  ; Clear after taking
    (or @result [])))

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
    ;; CRITICAL: If resumed code suspends (returns ::incomplete), clear running? flag
    ;; This matches the behavior in spin/core.cljc where the spin is considered
    ;; suspended, not actively running. The spin will be woken up when its
    ;; await continuation is resumed.
    ;; Must match spin.core/incomplete (can't require spin.core - circular dep)
    (when (= ret :org.replikativ.spindel.spin/incomplete)
      (mark-not-running! context spin-id))
    ;; Never remove continuations - maintain fully reactive graph
    ret))

;; =============================================================================
