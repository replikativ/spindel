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
  (:require [replikativ.logging :as log]
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.engine.state-backend :as backend]
            [org.replikativ.spindel.engine.addressing :as addressing]
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

;; PBatchQueue and create-batch-queue removed in
;; experiment/unified-subscription-model: there is no separate per-batch
;; event queue; everything flows through :engine/pending. See
;; create-batch and enqueue-completion-event! below.

(defn ^:no-doc create-batch
  "Create a Batch data structure for a signal-change processing cycle.

  Unified-queue design: the batch is no longer an isolated event queue,
  it's a piece of metadata that lives in `:engine/current-batch` while a
  `:signal-change` is being processed. The actual events flow through the
  main `:engine/pending` queue and are drained by the outer `drain-events!`
  loop.

  Surviving fields:
    :generation     - monotonic counter, used for staleness/dedup checks
                      (cont :consumed-generation vs signal :generation, and
                      [parent child gen] await-cont dedup).
    :signal-id      - signal that triggered this batch (informational).
    :resumed-conts  - atom of [parent child gen] dedup triples to prevent
                      a single :spin-completion from resuming the same
                      await cont twice in one batch.
    :processed      - atom of spin-ids whose cache is fresh in this batch;
                      `propagate-await-dirty!` uses it to avoid redundant
                      dirty-mark on parents that already saw the new value.

  Removed:
    :observers / :completed - were Phase 2's blocking-wait condition.
    :processed-events       - was Phase 2's per-event dedup; not needed
                              now that events flow through the main queue
                              which has its own FIFO semantics.
    :events                 - was the per-batch BlockingQueue; now main."
  [context signal-id]
  (let [gen (rtp/swap-state! context [:engine/batch-generation]
                             (fn [gen] (inc (or gen 0))))]
    {:generation gen
     :signal-id signal-id
     :resumed-conts (atom #{})
     :processed (atom #{})}))

;; Forward declarations for mutual recursion
(declare trigger-drain!)

(defn ^:no-doc enqueue-completion-event!
  "Enqueue a spin completion event onto the single drain queue.

  Unified-queue design (experiment/unified-subscription-model): there is no
  separate per-batch event queue. All events — `:signal-change`,
  `:spin-completion`, `:deferred-delivery`, `:mailbox-post`, `:spin-execution`
  — flow through `:engine/pending` in FIFO order, drained by `drain-events!`.

  If a batch is currently active (we're inside `:signal-change` processing),
  we update `(:processed batch)` so that `propagate-await-dirty!` knows this
  spin already has a fresh cache and doesn't redundantly mark its parents
  dirty. We do NOT route the event to a separate batch queue; the outer
  drain loop will pick it up as cascade work.

  Args:
    context - context record
    spin-id - ID of completed spin"
  [context spin-id]
  ;; Always enqueue onto the main pending queue.
  (rtp/swap-state-args! context [:engine/pending] conj
                        [{:type :spin-completion :id spin-id}])
  (log/trace :engine/enqueue-event {:event {:type :spin-completion :id spin-id}})

  ;; If we're inside a signal-change batch, mark the spin as processed so
  ;; propagate-await-dirty! can short-circuit on it. This is the ONLY
  ;; batch-state update enqueue still does; the actual event flows through
  ;; the main queue.
  (when-let [batch (rtp/get-state context [:engine/current-batch])]
    (swap! (:processed batch) conj spin-id)
    (log/trace :engine/batch-completion-marked {:spin-id spin-id}))

  ;; Trigger drain so the event gets picked up. If a drain is already
  ;; running, the cascade is handled by the outer loop; trigger-drain!'s
  ;; CAS in drain-events! ensures we don't double-drain.
  (trigger-drain! context (:executor context)))

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
  "INTERNAL: Post message inline to mailbox, resuming waiters directly.

  The loop skips two flavors of cancelled waiter without consuming the
  message:

  1. Whole-spin cancellation (`ec/spin-is-cancelled?`) — the spin owning
     the waiter was explicitly cancelled by the user.

  2. Per-cont cancellation (the waiter's `:cancel-token` is in the
     current context's `:engine/cancelled-tokens`) — the await cont
     that registered this waiter was truncated by the engine
     (resume-single-observer, clear-deps, etc.). The wrapped resolve
     would no-op via the gate, but consuming the message and invoking
     a no-op would silently lose the message. See
     `effects/await.cljc::cancellable-external-pair` and
     `ec/*external-await-cancel-token*`.

  When a cancelled waiter is found, the loop recurs with the SAME `msg`
  — the swap-state above only popped a waiter and didn't put the msg
  anywhere; the next iteration finds the next waiter (or pushes the msg
  to `:queue` if no more waiters)."
  [mailbox msg state-atom]
  (let [ctx (try (ec/current-execution-context)
                 (catch #?(:clj Throwable :cljs :default) _ nil))
        cancelled-tokens (when ctx (rtp/get-state ctx [:engine/cancelled-tokens]))]
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
        (if-let [{:keys [spin-id cancel-token resolve]} @waiter-to-try]
          (cond
            (and spin-id (ec/spin-is-cancelled? spin-id))
            (recur)

            (and cancel-token cancelled-tokens (contains? cancelled-tokens cancel-token))
            (do
              ;; Self-cleaning: this waiter was cancelled and we're consuming
              ;; (skipping) it now — the cancel-token is no longer needed.
              ;; Drop it from the set so cancelled-tokens doesn't accumulate
              ;; one entry per signal-change × waiter over the context's
              ;; lifetime. See `effects/await.cljc::cancellable-external-pair`
              ;; for the Deferred/ifn? side of the same self-cleaning story.
              (when ctx
                (rtp/swap-state! ctx [:engine/cancelled-tokens]
                                 (fn [s] (if s (disj s cancel-token) s))))
              (recur))

            :else
            (do
              (pcps-async/invoke-continuation resolve msg)
              nil))
          ;; No waiter, message queued
          nil)))))

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
  (log/trace :engine/enqueue-event {:event event})
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
  (log/debug :engine/resuming-track-continuation {:spin-id spin-id :signal-id sid})

  ;; Remove stale continuations (order > resumed continuation's order)
  ;;
  ;; Before dissociating each removed cont, call its `:cancel!` hook if
  ;; any. External-await wrappers (Deferred / Mailbox / plain-fn) install
  ;; a cancellation gate so that when the resource later fires, the
  ;; orphaned resolve closure is a no-op. Without this, both the OLD
  ;; (orphaned) and NEW (registered by the parent re-run) body slices
  ;; would advance to outer-resolve, causing double cache-result, double
  ;; record-deps, and double side effects. See
  ;; `effects/await.cljc::cancellable-external-pair`.
  (let [cont-order (:order cont)
        all-conts (rtp/get-state context [:continuations spin-id])
        skipped-signal-ids (->> (vals all-conts)
                                (filter #(< (:order %) cont-order))
                                (keep :signal-id))
        cancelled-conts (filter #(> (:order %) cont-order) (vals all-conts))]
    ;; Fire cancellation hooks BEFORE state mutation so orphaned closures
    ;; observe cancellation the moment the external resource calls them.
    ;; Pass the current context — under Option A (state-backed cancel
    ;; tokens), each context's cancellation set is fork-isolated, so the
    ;; cancellation only affects this context (parent / sibling forks
    ;; see their own state).
    (doseq [c cancelled-conts]
      (when-let [cancel! (:cancel! c)] (cancel! context)))
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

  ;; Restore the parent's transient deps tracking from the snapshot captured
  ;; at suspend time. Without this, the body slice that resumes after the
  ;; track point starts with empty tracking — the deps it accumulated in the
  ;; pre-suspend slice are gone. record-deps! at body completion would then
  ;; commit only the post-resume deps and tear down observer relations for
  ;; everything tracked in the pre-suspend slice (e.g. nav-spin in a body
  ;; that awaited nav-spin then columns-spin, resuming from the cols await).
  (when-let [snap (:tracking-snap cont)]
    (rtp/swap-state! context [:spin-tracking spin-id] (constantly snap)))

  ;; Resume with the bindings that were active at suspend time. The cont's
  ;; :ctx-bindings is a snapshot of (:bindings ctx) at the suspension point,
  ;; so it already carries whatever scope the body had pushed (DOM
  ;; parent-addr, slot, keys, etc.). Merge with current context bindings to
  ;; pick up any persistent additions (e.g. middleware-set values) that
  ;; arrived between suspend and resume; cont values win where they overlap.
  ;;
  ;; The per-spin chain-head slot is seeded with the cont's
  ;; `:chain-head-snap` (the cursor value captured at suspend) so the
  ;; post-resume slice mints `(spin …)` / `(effect …)` ids deterministically
  ;; continuing from where the pre-suspend slice left off. The cursor
  ;; lives in ctx state under `:addressing :chain-heads` — see
  ;; addressing.cljc — so no dynamic-var capture/restore is needed.
  (let [ctx-bindings (:ctx-bindings cont)
        merged-bindings (if ctx-bindings
                          (merge (:bindings context) ctx-bindings)
                          (:bindings context))
        ctx-with-bindings (assoc context :bindings merged-bindings)
        chain-head-start (or (:chain-head-snap cont)
                             (addressing/body-start-chain-head spin-id))]
    (addressing/seed-chain-head! context spin-id chain-head-start)
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
  (log/debug :engine/re-execute-dirty-parent {:spin-id spin-id :signal-id signal-id})

  ;; Remove stale continuations (order > resumed continuation's order).
  ;; See `resume-single-observer!` for the cancellation-hook rationale —
  ;; same orphaned-callback risk here when re-executing a dirty parent.
  (let [cont-order (:order cont)
        all-conts (rtp/get-state context [:continuations spin-id])
        skipped-signal-ids (->> (vals all-conts)
                                (filter #(< (:order %) cont-order))
                                (keep :signal-id))
        cancelled-conts (filter #(> (:order %) cont-order) (vals all-conts))]
    (doseq [c cancelled-conts]
      (when-let [cancel! (:cancel! c)] (cancel! context)))
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

  ;; Restore tracking snapshot from the suspension point so the body's
  ;; deps tracking continues from there rather than restarting empty.
  ;; See resume-single-observer! for the rationale.
  (when-let [snap (:tracking-snap cont)]
    (rtp/swap-state! context [:spin-tracking spin-id] (constantly snap)))

  ;; Resume continuation with current signal value. cont's :ctx-bindings is
  ;; the suspend-time scope, merged onto current context bindings so any
  ;; intervening persistent additions are kept.
  ;; See resume-single-observer! for the chain-head slot seeding rationale.
  (let [ctx-bindings (:ctx-bindings cont)
        ctx-with-bindings (cond-> context
                            ctx-bindings  (update :bindings merge ctx-bindings))
        chain-head-start (or (:chain-head-snap cont)
                             (addressing/body-start-chain-head spin-id))]
    (addressing/seed-chain-head! context spin-id chain-head-start)
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
  or nil if the spin has no await parent.

  Reads parent set from `:nodes[spin-id]:observers` — under the unified-
  subscription design (stage 3), spin observers includes every parent
  currently awaiting this child, eagerly registered by track-spin-dep!.
  This replaces the separate `:await-dependents` index."
  [context spin-id]
  (letfn [(parents-of [tid]
            (when-let [node (rtp/get-state context [:nodes tid])]
              (nodes/get-observers node)))]
    (let [parents (parents-of spin-id)]
      (when (seq parents)
        (loop [current (first parents)
               visited #{spin-id}]
          (if (visited current)
            current ;; cycle detected, return current as root
            (let [grandparents (parents-of current)]
              (if (seq grandparents)
                (recur (first grandparents) (conj visited current))
                current))))))))

(defn- apply-spin-scope
  "Merge spin `sid`'s captured scope onto `ctx`'s bindings.

  `make-spin` (spin/core.cljc) snapshots the registered spin-scope binding
  keys (see engine.bindings) at construction into `[:nodes sid :spin-scope]`.
  That scope is intrinsic to the spin and must be re-established on EVERY
  body-entry path so the body addresses and behaves consistently no matter
  which engine path runs it.

  Track-continuation resumes happen to restore it via the cont's
  `:ctx-bindings` snapshot, but await-continuation resumes carry no
  `:ctx-bindings` — so without this an awaiting spin (e.g. a keyed
  `ifor-each` item-spin re-running because its awaited child re-completed)
  would lose its construction scope, drifting any scope-derived addressing
  and breaking discharge reconciliation."
  [ctx sid]
  (let [spin-scope (rtp/get-state ctx [:nodes sid :spin-scope])]
    (if (seq spin-scope)
      (update ctx :bindings merge spin-scope)
      ctx)))

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
  (log/trace :engine/process-event {:event event})

  (case (:type event)
    :signal-change
    ;; Unified-queue design (experiment/unified-subscription-model):
    ;;
    ;; A signal change resumes the topologically-ordered observers'
    ;; earliest track continuations. Each resume runs the observer's body
    ;; slice; if the body completes synchronously, its `:spin-completion`
    ;; event is enqueued onto the main `:engine/pending` queue via
    ;; `enqueue-completion-event!`. If the body suspends (await), control
    ;; returns without a completion event. The outer `drain-events!` loop
    ;; picks up cascade events naturally in FIFO order.
    ;;
    ;; There is no Phase 2 blocking wait: a body suspended on a
    ;; `:deferred-delivery` or similar async resolution is handled in a
    ;; later drain pass. Glitch-freedom holds within the SYNC portion of
    ;; the dependency graph (topological dispatch + same-drain cascade);
    ;; async branches are eventually consistent.
    ;;
    ;; The batch metadata (`:engine/current-batch`) survives only for the
    ;; duration of this handler call. It carries the generation counter
    ;; (for cont-staleness dedup) and the `:processed` / `:resumed-conts`
    ;; atoms used by `enqueue-completion-event!` and the `:spin-completion`
    ;; handler. The handler clears it at function exit.
    (let [sid (:id event)
          observers (rtp/ordered-observers context sid)
          batch (create-batch context sid)]
      (rtp/swap-state! context [:engine/current-batch] (constantly batch))

      (log/trace :engine/signal-change {:signal-id sid
                                        :observers observers
                                        :generation (:generation batch)})

      ;; Clear ephemeral await continuations at generation boundary
      ;; (Design 1). Must happen BEFORE track continuations resume so
      ;; old await conts don't fire during this resume cycle.
      (clear-all-await-continuations! context)

      (let [;; Collect observers that have a live continuation for this signal.
            observers-with-conts (vec (keep (fn [spin-id]
                                              (when-let [cont (rtp/earliest-continuation context spin-id sid)]
                                                [spin-id cont]))
                                            observers))
            ;; Filter out descendant observers — they'll be re-created by
            ;; their parent and shouldn't fire independently.
            observer-id-set (set (map first observers-with-conts))
            descendant-set (compute-descendant-observers context observer-id-set)
            independent-observers (vec (remove (fn [[sid _]] (descendant-set sid))
                                               observers-with-conts))

            ;; Escalation: children whose parents await them shouldn't fire
            ;; independently; instead, escalate to the root ancestor which
            ;; re-creates the child fresh. Prevents double-execution.
            escalation-targets
            (into {}
                  (keep (fn [[spin-id _cont]]
                          (when-let [root-id (find-root-await-ancestor context spin-id)]
                            (when-let [root-conts (seq (vals (rtp/get-state context [:continuations root-id])))]
                              (let [earliest (first (sort-by :order root-conts))]
                                (when (:signal-id earliest)
                                  [spin-id {:root-id root-id :cont earliest}]))))))
                  independent-observers)

            direct-observers (if (seq escalation-targets)
                               (vec (remove (fn [[sid _]] (contains? escalation-targets sid))
                                            independent-observers))
                               independent-observers)

            roots-to-execute (when (seq escalation-targets)
                               (into {} (map (fn [{:keys [root-id cont]}] [root-id cont]))
                                     (vals escalation-targets)))

            do-resume! (fn [[spin-id cont]]
                         (resume-single-observer! context spin-id sid cont))
            do-escalate! (fn [[root-id cont]]
                           (re-execute-dirty-parent! context root-id (:signal-id cont) cont))]

        (when (seq descendant-set)
          (log/debug :engine/filtered-descendant-observers
                     {:descendants descendant-set
                      :independent (map first independent-observers)}))

        (when (seq escalation-targets)
          (log/debug :engine/escalating-to-root-ancestors
                     {:escalated (keys escalation-targets)
                      :roots (keys roots-to-execute)}))

        ;; Dispatch direct observers in topological order. JVM: parallel
        ;; for >1 observer (each resume is independent atomic ops on its
        ;; own node); CLJS: always sequential.
        #?(:clj
           (if (<= (count direct-observers) 1)
             (doseq [obs direct-observers]
               (do-resume! obs))
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
               (ForkJoinPool/managedBlock
                (reify java.util.concurrent.ForkJoinPool$ManagedBlocker
                  (block [_]
                    (.await latch)
                    true)
                  (isReleasable [_]
                    (zero? (.getCount latch)))))))
           :cljs
           (doseq [obs direct-observers]
             (do-resume! obs)))

        ;; Escalate to root ancestors (always sequential — modifies shared state).
        (doseq [obs roots-to-execute]
          (do-escalate! obs)))

      ;; Clear batch from context state. Cascade events landed in
      ;; :engine/pending are processed by the outer drain loop.
      (rtp/swap-state! context [:engine/current-batch] (constantly nil))
      nil)

    :spin-completion
    (let [tid (:id event)
          ;; Get all parent spin-ids that have continuations subscribed
          parent-spin-ids (keys (rtp/get-state context
                                               [:subscriptions [:spin/complete tid]]))
          ;; Read batch from context state (nil when not in batch mode)
          batch (rtp/get-state context [:engine/current-batch])]
      (log/trace :engine/spin-completion {:spin-id tid :parent-spin-ids parent-spin-ids})

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
                (log/debug :engine/resuming-await-continuation {:parent-id parent-id :cont-id cont-id :child-id tid
                                                                :generation generation})
                ;; Restore the parent's transient deps tracking captured at the
                ;; await suspend point. See resume-single-observer! for rationale.
                (when-let [snap (:tracking-snap cont)]
                  (rtp/swap-state! context [:spin-tracking parent-id] (constantly snap)))
                ;; Resume with the suspend-time bindings (cont's :ctx-bindings)
                ;; merged onto the current context bindings.
                ;; See resume-single-observer! for the chain-head atom rationale.
                (let [ctx-bindings (:ctx-bindings cont)
                      ctx-for-resume (-> (cond-> context
                                           ctx-bindings (update :bindings merge ctx-bindings))
                                         ;; Re-apply the resuming spin's intrinsic
                                         ;; scope. Await continuations carry no
                                         ;; :ctx-bindings, so this is the only thing
                                         ;; that restores construction scope for a
                                         ;; spin that re-runs because its awaited
                                         ;; child re-completed.
                                         (apply-spin-scope parent-id))
                      chain-head-start (or (:chain-head-snap cont)
                                           (addressing/body-start-chain-head parent-id))]
                  (addressing/seed-chain-head! context parent-id chain-head-start)
                  (binding [ec/*execution-context* ctx-for-resume
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
                      resume-result))))))))

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
      (log/trace :engine/deferred-delivery {:deferred deferred :value value})
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
      (log/trace :engine/mailbox-post {:mailbox mailbox :msg msg})
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
      (log/trace :engine/spin-execution {:spin-id tid})
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
              (log/trace :engine/spin-execution-cached {:spin-id tid})
              (if (= (:variant cached) :ok)
                (resolve-fn (:payload cached))
                (reject-fn (:payload cached))))
            ;; Not cached - must be running, add callbacks to pending
            (do
              (log/trace :engine/spin-execution-skip-running {:spin-id tid})
              (add-pending-callback! context tid {:resolve resolve-fn :reject reject-fn}))))
        ;; Successfully claimed - proceed with execution
        ;; Execute spin on executor thread with provided callbacks
        ;; CRITICAL: Bind *in-trampoline* to false when re-entering from event handler
        ;; This ensures invoke-continuation establishes a new trampoline loop
        ;; If execution-context is provided (e.g., from SMC), bind it; otherwise use context
        ;; Apply this spin's captured scope (see make-spin in spin/core.cljc)
        ;; on top of the chosen context's bindings, so the body's initial
        ;; synchronous code (before any track/await) sees the spin's lexical
        ;; construction scope. Without this, only continuation resumes restore
        ;; scope — elements built before the first effect would use runtime
        ;; bindings.
        (let [base-ctx (or execution-context context)
              spin-scope (rtp/get-state context [:nodes tid :spin-scope])
              effective-ctx (if (seq spin-scope)
                              (update base-ctx :bindings merge spin-scope)
                              base-ctx)]
          (binding [ec/*execution-context* effective-ctx
                    ec/*spin-id* tid
                    pcps-async/*in-trampoline* false]
            ;; Invoke spin (Spin implements IFn)
            (let [result (spin resolve-fn reject-fn)]
              nil)))))

    ;; Unknown event type
    (do
      (log/trace :engine/unknown-event {:event event})
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
  (let [running       (:running context)
        drain-active  (:drain-active context)]
    (cond
      ;; Function-entry guard: drop drains on a stopped context. New drain
      ;; calls scheduled before stop-context! ran (e.g. lingering executor
      ;; tasks from trigger-drain!) observe :running=false here and bail
      ;; before incrementing the active counter — they're invisible to
      ;; stop-context!. Snapshot/restored contexts have :running=nil and
      ;; fall through (restore-snapshot drives drain-events! directly).
      (and running (not @running))
      (do (log/trace :engine/drain-skipped {:reason :context-stopped})
          0)

      :else
      (do
        ;; Mark this drain active. stop-context! polls drain-active down
        ;; to 0 before returning, which gives it a deterministic "no drain
        ;; will run on this context after I return" guarantee — bounded by
        ;; the longest single-event processing time, not by a wall-clock
        ;; .join timeout. Snapshot/restored contexts have no drain-active
        ;; atom; we just skip the bookkeeping for them.
        (when drain-active (swap! drain-active inc))
        (try
          (let [cas-result (rtp/cas-state! context [:engine/draining?] false true)]
            (if-not cas-result
              ;; Another drain holds the lock. We bumped the counter, so
              ;; the finally below decrements it. No work to do here.
              (do (log/trace :engine/drain-skipped {:reason :already-draining})
                  0)

              ;; We claimed the lock — drain to completion.
              (try
                (log/trace :engine/drain-start)
                (binding [*in-drain?* true]
                  (let [event-count (atom 0)]
                    ;; Drain loop with intra-loop running check. If
                    ;; stop-context! flips :running=false while we're
                    ;; mid-drain, exit at the next iteration boundary
                    ;; instead of continuing to dequeue. Without this,
                    ;; stop-context! cannot bound how many of the user's
                    ;; subsequently-appended events the drain processes
                    ;; (the function-entry guard only catches drains that
                    ;; haven't started yet). We exit cleanly between
                    ;; events; whatever's still in :pending stays there
                    ;; for the next legitimate drain (e.g. restore-snapshot)
                    ;; to pick up.
                    (loop []
                      (cond
                        (and running (not @running))
                        (do (log/trace :engine/drain-aborted-stopped {:events-processed @event-count})
                            @event-count)

                        :else
                        (if-let [event (dequeue-event! context)]
                          (do
                            ;; Process event (may enqueue more events).
                            ;; CRITICAL: per-event try/catch so one bad event doesn't
                            ;; abort the entire drain session.
                            (try
                              (process-event! context event)
                              (catch #?(:clj Throwable :cljs js/Error) e
                                (log/error :engine/event-processing-error {:event-type (:type event)
                                                                           :event-id (:id event)
                                                                           :error #?(:clj (.getMessage ^Throwable e) :cljs (str e))})
                                (case (:type event)
                                  :spin-execution
                                  (when-let [reject-fn (:reject-fn event)]
                                    (try (reject-fn e)
                                         (catch #?(:clj Throwable :cljs :default) _)))

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

                                  nil)))
                            (swap! event-count inc)
                            (recur))
                          ;; Queue empty — drain complete.
                          (do
                            (log/trace :engine/drain-complete {:events-processed @event-count})
                            @event-count))))))
                (finally
                  ;; Always release draining lock.
                  (rtp/swap-state! context [:engine/draining?] (constantly false))

                  ;; Re-trigger handling: if events landed in :pending during
                  ;; the gap between our last dequeue and the lock release,
                  ;; schedule another drain so they don't get stranded. But
                  ;; skip the re-trigger if the context has been stopped —
                  ;; otherwise we'd hand work to a context the caller
                  ;; believes is dormant. Snapshot contexts (:running=nil)
                  ;; fall through and re-trigger normally.
                  (let [running-atom (:running context)
                        still-alive? (or (nil? running-atom) @running-atom)
                        pending      (rtp/get-state context [:engine/pending])]
                    (when (and still-alive? (seq pending))
                      (trigger-drain! context executor)))))))
          (finally
            ;; Decrement the active counter so stop-context! can complete.
            (when drain-active (swap! drain-active dec))))))))

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
  ;; The three "is the engine idle?" predicates must be evaluated against a
  ;; single consistent snapshot of the state. Reading them with three
  ;; separate (rtp/get-state) calls is racy: a drain can start between the
  ;; :engine/draining? read and the :engine/pending read, leaving us to
  ;; conclude "idle" while a drain is genuinely in flight. Read the whole
  ;; backend once and inspect the resulting map.
  ;;
  ;; Also include drain-active in the predicate. drain-events! increments
  ;; that counter the moment it passes the function-entry guard — which is
  ;; before it CAS's :engine/draining?. There's a small window where a
  ;; drain has been entered but not yet acquired the lock, and it would be
  ;; invisible to a check that only looked at :engine/draining?. Counting
  ;; the entry catches it.
  (let [drain-active (:drain-active context)
        idle? (fn []
                (let [state    (backend/backend-deref (:backend context))
                      draining (get state :engine/draining?)
                      pending  (get state :engine/pending)
                      nodes    (get state :nodes)
                      running? (some (fn [[_id n]] (:running? n)) nodes)
                      active   (when drain-active @drain-active)]
                  (and (not draining)
                       (empty? pending)
                       (not running?)
                       (or (nil? active) (zero? active)))))]
    #?(:clj
       (let [start (System/currentTimeMillis)
             deadline (+ start timeout-ms)]
         (if (idle?)
           true
           (let [result (volatile! false)]
             (ForkJoinPool/managedBlock
              (reify java.util.concurrent.ForkJoinPool$ManagedBlocker
                (block [_]
                  (LockSupport/parkNanos (* 100 1000)) ; 100 microseconds
                  (let [d (idle?)]
                    (when d (vreset! result true))
                    (or d (>= (System/currentTimeMillis) deadline))))
                (isReleasable [_]
                  (cond
                    (idle?)
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
       (let [_ timeout-ms]
         (idle?)))))

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
      (log/trace :engine/trigger-drain)
      true)
    (do
      (log/trace :engine/trigger-drain-no-executor)
      false)))

;; =============================================================================
;; Dependency Tracking (shared across all context implementations)
;; =============================================================================

(defn record-deps!
  "Commit a body's tracked dependencies to the spin's permanent deps and
  prune any observer registrations from signals/spins that were tracked
  in a previous run but not in this one.

  Under the unified-subscription design, observer registration happens
  EAGERLY at `track-signal-dep!` / `track-spin-dep!` — at the moment the
  body calls `(track sig)` / `(await child)`. So `record-deps!` does
  NOT add observers; that would be redundant. Its responsibility is:

  1. Snapshot the transient tracking into `spin.deps` (used as the diff
     baseline for the next run).
  2. Compute REMOVED deps (signals/spins in old spin.deps but not in
     current spin-tracking) and unregister the spin from their observer
     lists. This catches signals tracked in a previous run that the
     current run skipped (conditional tracking).
  3. Clear the transient `:spin-tracking[spin-id]` entry.

  Called from the body's outer `resolve` callback (spin/core.cljc).

  TRANSACTIONAL: all state changes happen atomically in a single
  swap-state! to keep the snapshot consistent.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin whose dependencies to record

  Returns: true"
  [context spin-id]
  (rtp/swap-state! context []
                   (fn [rt-state]
                     (let [tracked-deps (get-in rt-state [:spin-tracking spin-id])]
        ;; Idempotency guard: if tracking already cleared, no-op.
                       (if-not tracked-deps
                         rt-state
                         (let [tracked-signals (:signals tracked-deps #{})
                               tracked-spins   (:spins tracked-deps #{})
                               spin-node (get-in rt-state [:nodes spin-id])
                               old-deps (if spin-node (nodes/get-deps spin-node) {:signals #{} :spins #{}})
                               old-signals (:signals old-deps #{})
                               old-spins (:spins old-deps #{})
                               removed-signals (set/difference old-signals tracked-signals)
                               removed-spins (set/difference old-spins tracked-spins)]
                           (-> rt-state
                ;; Snapshot tracked deps as the new spin.deps baseline.
                               (update-in [:nodes spin-id]
                                          (fn [node]
                                            (let [node (or node (nodes/->spin-node nil :clean false false #{} {} nil #{}))]
                                              (nodes/set-deps node {:signals tracked-signals
                                                                    :spins tracked-spins}))))

                ;; Remove spin from observer lists of signals it stopped
                ;; tracking this run. (Adds are already in place from
                ;; eager registration at track time.)
                               (as-> state
                                     (reduce (fn [s sid]
                                               (let [node (get-in s [:nodes sid])]
                                                 (if node
                                                   (update-in s [:nodes sid] #(nodes/remove-observer % spin-id))
                                                   s)))
                                             state
                                             removed-signals))

                ;; Spin observers (parents awaiting children) are also
                ;; eagerly registered now (Stage 3, via track-spin-dep!).
                ;; record-deps! only needs to prune observers from spins
                ;; the parent stopped awaiting between runs.
                               (as-> state
                                     (reduce (fn [s tid]
                                               (let [node (get-in s [:nodes tid])]
                                                 (if node
                                                   (update-in s [:nodes tid] #(nodes/remove-observer % spin-id))
                                                   s)))
                                             state
                                             removed-spins))

                ;; Clear transient tracking.
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
  ;; NOTE: we intentionally do NOT fire `:cancel!` on the cleared conts.
  ;; The orphaned-callback double-execution risk only exists at TRUNCATION
  ;; sites (where the spin stays alive and re-runs, generating a NEW cont
  ;; at the same source-loc that races with the OLD external closure).
  ;; clear-deps! is a teardown path — the spin is going away — so no NEW
  ;; cont will compete. A late-firing external resolve will harmlessly
  ;; advance the (already-cleared) body slice toward cache-result, which
  ;; is idempotent. Calling `:cancel!` here would silently no-op
  ;; LEGITIMATE in-flight resolves when the JVM Cleaner GCs a spin whose
  ;; body is still suspended on an external await — observed as test
  ;; flakes in tests where the user drops their Spin ref before the
  ;; deferred delivers (Cleaner-1 thread → full-cleanup-spin! → :cancel!).
  (rtp/swap-state! context []
                   (fn [rt-state]
      ;; To safely clear observers, take the UNION of `spin.deps` (the
      ;; last completed run's deps) and `spin.tracking` (the in-flight
      ;; run's eager registrations). Under the unified-subscription
      ;; design, the in-flight body may have eagerly registered as an
      ;; observer of signals that aren't yet in spin.deps (record-deps!
      ;; hasn't committed). Skipping those would leak observer entries.
                     (let [spin-node (get-in rt-state [:nodes spin-id])
                           deps (if spin-node (nodes/get-deps spin-node) {:signals #{} :spins #{}})
                           tracking (get-in rt-state [:spin-tracking spin-id])
                           signal-deps (set/union (:signals deps #{})
                                                  (:signals tracking #{}))
                           spin-deps (set/union (:spins deps #{})
                                                (:spins tracking #{}))]
                       (-> rt-state
            ;; Clear committed deps on the SpinNode.
                           (update-in [:nodes spin-id]
                                      (fn [node]
                                        (when node
                                          (nodes/set-deps node {:signals #{} :spins #{}}))))

            ;; Unregister from signal observers (committed + eager).
                           (as-> state
                                 (reduce (fn [s sid]
                                           (let [node (get-in s [:nodes sid])]
                                             (if node
                                               (update-in s [:nodes sid] #(nodes/remove-observer % spin-id))
                                               s)))
                                         state
                                         signal-deps))

            ;; Unregister from spin observers (committed + eager —
            ;; same union semantics as signals after Stage 3).
                           (as-> state
                                 (reduce (fn [s tid]
                                           (let [node (get-in s [:nodes tid])]
                                             (if node
                                               (update-in s [:nodes tid] #(nodes/remove-observer % spin-id))
                                               s)))
                                         state
                                         spin-deps))

            ;; Clear continuations + transient tracking.
                           (update :continuations dissoc spin-id)
                           (update :spin-tracking dissoc spin-id)

            ;; Clean up subscriptions (remove spin-id from all event keys,
            ;; drop empty event keys).
                           (update :subscriptions
                                   (fn [subs]
                                     (reduce-kv
                                      (fn [acc ek m]
                                        (let [m' (dissoc m spin-id)]
                                          (if (seq m')
                                            (assoc acc ek m')
                                            acc)))
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
  ;; NOTE: we intentionally do NOT fire `:cancel!` here. Same rationale as
  ;; `clear-deps!` — this is a teardown path, no new cont will compete with
  ;; an orphaned closure. Firing `:cancel!` would silently no-op legitimate
  ;; in-flight resolves when the JVM Cleaner GCs a spin whose body is still
  ;; suspended on an external await.
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
            ;; 5. Remove continuations
                           (update :continuations dissoc spin-id)
            ;; 6. Remove pending callbacks
                           (update :pending-callbacks dissoc spin-id)
            ;; 7. Remove tracking data
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
            ;; Note: await-parent relations live on :nodes :observers
            ;; now; signal observers (above) and the :subscriptions clean
            ;; (above) cover those. No separate :await-dependents map.
                           ))))
  true)

(defn- has-live-signal-cont?
  "True if `spin-id` has any continuation subscribed to a signal —
  which can always fire because signals are mutable state and any
  `swap!` will trigger them. Such a spin is reactive infrastructure
  and must not be GC-cleaned even if its `Spin` Java object is
  unreachable.

  Spin-completion conts (`[:spin/complete _]`) are deliberately NOT
  counted as live here: their source spin's completion is a one-shot
  event (already-completed spins won't re-complete unless they re-run,
  and a parent spin's chance to re-run dies along with the parent's
  own reactive infrastructure). Counting them would block legitimate
  cascade cleanup of awaiter/awaitee pairs once both are unreachable."
  [context spin-id]
  (->> (vals (rtp/get-state context [:continuations spin-id]))
       (some (fn [c]
               (when-let [[ek-type _] (:event-key c)]
                 (= ek-type :signal))))))

(defn try-gc-cleanup-spin!
  "Called from GC callback. Attempts full cleanup if safe, otherwise marks
  the spin as orphaned for deferred cleanup.

  A spin is safe to fully clean when ALL of the following hold:
  1. Its Spin object was GC'd (caller ensures this)
  2. It has no observers (no other spins depend on it)
  3. It has no live signal continuations (no `(track sig)` waiters
     bound to a still-live signal)

  If any condition fails, it's marked `:orphaned? true` and a later
  cleanup pass — triggered when the last observer or signal-cont is
  torn down — will full-clean it.

  Why (3) is essential: a spin with `(track sig)` in its body keeps
  a continuation registered in `:continuations spin-id` that the
  engine resumes on every signal change. The cont's `:resolve-fn`
  closes over the CPS body slice (which references `spin-id`,
  atoms, etc.) but NOT over the `Spin` Java object itself. So the
  Spin object can become GC-eligible (e.g. the user's `let` binding
  goes out of scope after last use) while the reactive machinery is
  still very much alive. Without this check, the Cleaner thread
  would fire, `full-cleanup-spin!` would clear the cont and the
  signal's observer registration, and subsequent signal changes
  would silently no-op — a deeply confusing reactive drop.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin whose Spin object was GC'd

  Returns: nil"
  [context spin-id]
  (let [node (rtp/get-state context [:nodes spin-id])]
    (when node ;; may already be cleaned
      (let [has-observers? (seq (nodes/get-observers node))
            live-signal-cont? (has-live-signal-cont? context spin-id)]
        (cond
          (or has-observers? live-signal-cont?)
          ;; Has observers and/or live signal continuations → mark
          ;; orphaned and defer cleanup. The Cleaner has run, so the
          ;; Spin object itself is unreachable, but the runtime still
          ;; needs this spin's state to fire reactive updates.
          (rtp/swap-state! context [:nodes spin-id]
                           #(when % (assoc % :orphaned? true)))

          :else
          ;; No observers, no live signal continuations → safe to
          ;; fully clean up + cascade to dependencies. Stale spin-
          ;; completion conts (awaits of since-cleaned parents) are
          ;; cleaned away by full-cleanup-spin!.
          (let [deps (nodes/get-deps node)
                dep-spin-ids (:spins deps #{})]
            (full-cleanup-spin! context spin-id)
            ;; Cascade: check if any spin dependency is now cleanable
            (doseq [dep-id dep-spin-ids]
              (let [dep-node (rtp/get-state context [:nodes dep-id])]
                (when (and dep-node
                           (:orphaned? dep-node)
                           (empty? (nodes/get-observers dep-node))
                           (not (has-live-signal-cont? context dep-id)))
                  (full-cleanup-spin! context dep-id))))))))))

(defn track-signal-dep!
  "Track that a spin depends on a signal — eagerly registers the spin
  as an observer of the signal.

  Unified-subscription design: a spin observes a signal from the moment
  it calls `(track ...)`, not from body-completion time. Doing so:

  1. Closes the first-run signal-change gap. If the spin's body suspends
     (e.g., on an await) before its outer resolve fires, signal changes
     during that suspend still reach the spin via the live observer
     registration. Pre-unification, observer registration was deferred
     until `record-deps!`, leaving a window where the cont existed but
     the dispatch handler couldn't find it.

  2. Unifies the two parallel indexes — `:nodes[sid]:observers` (forward
     dispatch) and `:subscriptions[[:signal sid]]` (reverse cont lookup)
     are now kept in sync at every state transition.

  Atomic single swap-state! updates both:
    - `:spin-tracking[spin-id][:signals]` — transient accumulator used
      by `record-deps!` for diff at body completion.
    - `:nodes[signal-id]:observers` — forward index used by
      `signal-change` dispatch.

  Cleanup contracts:
    - `record-deps!` (body resolve) — commits tracking → spin.deps and
      removes spin from observers of signals previously in deps but
      not re-tracked this run.
    - `clear-deps!` (invalidate/full-cleanup) — removes spin from
      observers of (spin.deps ∪ spin.tracking).signals.

  Args:
    context - context record (implements PState protocol)
    spin-id - ID of spin being tracked
    signal-id - ID of signal being consumed

  Returns: true"
  [context spin-id signal-id]
  (rtp/swap-state! context []
                   (fn [rt-state]
                     (-> rt-state
          ;; Transient accumulator for diff at body completion.
                         (update-in [:spin-tracking spin-id :signals]
                                    (fnil conj #{}) signal-id)
          ;; Eager observer registration on the signal node.
                         (update-in [:nodes signal-id]
                                    (fn [signal-node]
                                      (when signal-node
                                        (nodes/add-observer signal-node spin-id)))))))
  true)

(defn track-spin-dep!
  "Track that a parent spin depends on a child spin — eagerly registers
  the parent as an observer of the child's spin-completion event.

  Symmetric with `track-signal-dep!` (Stage 2 of the unified-
  subscription design). At the moment a body calls `(await child)`,
  the parent becomes part of the child's observer set so future
  re-completions of the child propagate to the parent without waiting
  for the parent's body to resolve.

  Atomic single swap-state! updates both:
    - `:spin-tracking[parent-id][:spins]` — transient accumulator used
      by `record-deps!` for diff at body completion.
    - `:nodes[child-id]:observers` — forward index used by
      `cache-result!`'s dirty-marking + `process-event! :spin-completion`
      dispatch.

  Args:
    context - context record (implements PState protocol)
    parent-spin-id - ID of spin doing the await
    child-spin-id - ID of spin being awaited

  Returns: true"
  [context parent-spin-id child-spin-id]
  (rtp/swap-state! context []
                   (fn [rt-state]
                     (-> rt-state
          ;; Transient accumulator for diff at parent body completion.
                         (update-in [:spin-tracking parent-spin-id :spins]
                                    (fnil conj #{}) child-spin-id)
          ;; Eager observer registration on the child spin node. Create
          ;; the child node if it doesn't exist yet — the parent may be
          ;; awaiting a child whose own register-spin! hasn't fired
          ;; (e.g. a chan->spin freshly minted).
                         (update-in [:nodes child-spin-id]
                                    (fn [node]
                                      (let [node (or node (nodes/->spin-node nil :clean false false #{} {} nil #{}))]
                                        (nodes/add-observer node parent-spin-id)))))))
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

(defn- captures-changed?
  "True when a spin's captured environment differs from the previous one.

  The key set is fixed per `(spin …)` form (the macro bakes in the free
  variables), so this reduces to: is any captured value not `identical?`
  to its prior value. `identical?` — not `=` — because it is O(1), never
  throws, and Clojure's structural sharing keeps an unchanged persistent
  value `identical?`; the only cost is an occasional needless re-run when
  a value is rebuilt `=`-equal but not `identical?`."
  [old new]
  (or (not= (set (keys old)) (set (keys new)))
      (boolean (some (fn [[k v]] (not (identical? v (get old k)))) new))))

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
                       (let [new-caps (:captured-locals spin-meta)
                             kind     (:kind spin-meta)]
                         (if existing-node
          ;; Re-registration: the (spin …) form was re-evaluated by a
          ;; re-running enclosing scope → a fresh closure. Mark the node
          ;; dirty — so the fresh cps-fn runs instead of await/deref
          ;; serving the stale cached result — but ONLY when the captured
          ;; environment actually changed (identical?-compared). When no
          ;; capture info was supplied (a non-macro spin: new-caps nil)
          ;; fall back to dirtying unconditionally. :result is kept as the
          ;; previous value (needed for value-change diffing).
                           (let [base (assoc existing-node
                                             :created-by creator-id
                                             :captured-locals new-caps
                                             :kind kind)]
                             (if (or (nil? new-caps)
                                     (captures-changed? (:captured-locals existing-node)
                                                        new-caps))
                               (-> base (assoc :completed? false) (nodes/mark-dirty))
                               base))
          ;; First registration: new node, record the captured environment.
                           (assoc (nodes/->spin-node nil :clean false false #{} {} creator-id #{})
                                  :captured-locals new-caps
                                  :kind kind)))))

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
      ;; Collect all nodes to mark dirty using breadth-first traversal.
      ;; All observer relations live on spin-node :observers now, so a
      ;; single BFS through that field covers both track-dependents and
      ;; await-parents.
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
                      ;; spin-node.observers already includes both committed
                      ;; await-parents AND eagerly-registered ones (Stage 3),
                      ;; so the separate `:await-dependents` walk in batch
                      ;; mode is no longer needed.
                                   next-to-mark (or observers #{})
                      ;; Filter out already visited to avoid infinite loops
                                   new-to-visit (into remaining (remove visited next-to-mark))
                      ;; Mark current node dirty
                                   new-state (update-in state [:nodes current-id]
                                                        (fn [node]
                                                          (when node
                                                            (-> node
                                                                (assoc :completed? false)
                                                                (nodes/mark-dirty)))))]
                               (recur new-to-visit (conj visited current-id) new-state))))))))
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

              ;; NOTE: we intentionally do NOT fire `:cancel!` here. This is
              ;; a generation-boundary cleanup of completed-not-running spins
              ;; — no new cont will be registered for these spins in this
              ;; generation. The orphaned-callback double-execution risk only
              ;; exists at TRUNCATION sites where the spin stays alive and
              ;; re-runs.

              ;; Remove await continuations and their subscriptions atomically.
              ;; The event-key shape depends on cont type:
              ;;   [:spin/complete child-id]  — Spin awaits
              ;;   [:external-await ext-tag]  — Deferred / Mailbox / plain-fn
              ;; We clean the corresponding subscription path. Without the
              ;; explicit dispatch, external-await conts leave a stale
              ;; `:subscriptions [:external-await ext-tag]` entry behind.
              (rtp/swap-state! context []
                               (fn [rt-state]
                                 (reduce
                                  (fn [state [cont-id cont]]
                                    (let [event-key (:event-key cont)
                                          state' (update-in state [:continuations spin-id] dissoc cont-id)
                                          spin-subs (get-in state' [:subscriptions event-key spin-id])
                                          spin-subs' (disj (or spin-subs #{}) cont-id)]
                                      (if (seq spin-subs')
                                        (assoc-in state' [:subscriptions event-key spin-id] spin-subs')
                                        (update-in state' [:subscriptions event-key] dissoc spin-id))))
                                  rt-state
                                  await-conts))))))))

    ;; Spin observers (parent set) live on `:nodes[child-id]:observers`;
    ;; there is no separate `:await-dependents` index any longer.

    (let [stats @result]
      (when (pos? (:continuations-cleared stats))
        (log/debug :generation/clear-await-continuations stats))
      stats)))

(defn ^:no-doc record-await-dependency!
  "Compatibility shim — under the unified-subscription design, the parent
  is already added to `child.observers` eagerly by `track-spin-dep!`
  (called from await-handler before this), so the work this function
  used to do is a no-op.

  Kept as a defined symbol because removing it triggers a flaky Clojure
  compile-time issue under `clojure -M:test`: macroexpansion of certain
  `(spin …)` forms in `examples/todo_app.cljc` ClassCastExceptions in
  `is.simm.partial-cps.ioc/has-breakpoints?`'s expansion-cache. The
  failure pattern (PersistentTreeMap doCompare on Long-vs-Keyword)
  suggests a Clojure/partial-cps compilation-order quirk that we don't
  fully understand. Leaving the stub in place avoids the issue at
  zero runtime cost."
  [_context _parent-spin-id _child-spin-id]
  nil)

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

  Reads parent set from `:nodes[spin-id]:observers` (unified-subscription
  design, stage 3). Previously read from `:await-dependents`.

  Args:
    context - runtime context
    spin-id - spin that just completed"
  [context spin-id]
  ;; Only propagate during batch processing (when in signal-change handling)
  (when-let [batch (rtp/get-state context [:engine/current-batch])]
    (let [child-node (rtp/get-state context [:nodes spin-id])
          awaiting-parents (when child-node (nodes/get-observers child-node))]
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
            (log/debug :engine/propagate-await-dirty {:from-spin spin-id
                                                      :to-parents parents-to-dirty
                                                      :count (count parents-to-dirty)
                                                      :skipped (- (count awaiting-parents) (count parents-to-dirty))})
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
      (log/debug :spin/invalidate-created {:spin-id spin-id :created-spins created-spins})
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
                                                          (if (and node
                                                                   (not (:running? node))
                                                                   (not has-completion-cont?))
                                                            (-> node
                                                                (assoc :completed? false)
                                                                (nodes/mark-dirty))
                                ;; Skipped — return the node unchanged. (Previously
                                ;; used `when`, which returned nil and `update-in`
                                ;; then erased the observer's node entirely — a
                                ;; latent bug only visible once node-resident fields
                                ;; beyond :result/:observers are read across this
                                ;; transition.)
                                                            node)))))
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
                                 (log/trace :claim/failed-already-cached {:spin-id spin-id})
                                 node)

              ;; Already running - don't claim
                             (:running? node)
                             (do (reset! claimed? false)
                                 (log/trace :claim/failed-already-running {:spin-id spin-id})
                                 node)

              ;; Not running and not cached - claim it
                             :else
                             (do (reset! claimed? true)
                                 (log/trace :claim/success-from-existing {:spin-id spin-id})
                                 (assoc node :running? true))))
          ;; No node - create and claim
                         (do (reset! claimed? true)
                             (log/trace :claim/success-new-node {:spin-id spin-id})
                             (nodes/->spin-node nil :clean false true #{} {} nil #{})))))
    @claimed?))

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
  ;; cont-id is stateless — generate it ONCE up front so a swap-fn retry
  ;; doesn't waste a fresh random-uuid per iteration.
  (let [cont-id (or (:id cont) (keyword (str "cont-" (random-uuid))))
        ;; The one piece of in-swap state we have to capture out-of-band:
        ;; the :cancel! hook of any cont being DISPLACED at cont-id (i.e.
        ;; a re-await of the same external resource at the same source-loc).
        ;; The OLD cont's `:cancel!` must fire, otherwise its wrapped
        ;; resolve/reject closures stay ungated in the external resource's
        ;; pending list and re-introduce the orphaned-callback double-
        ;; execution bug Stage 4 closes.
        ;;
        ;; Why the side-effect-in-swap-fn pattern is correct:
        ;;
        ;; - Retry-safe: each retry reads the latest :continuations and
        ;;   captures whichever :cancel! it sees. The LAST retry — the one
        ;;   whose state actually CAS'd — captures the cont truly being
        ;;   displaced. Earlier retries' captures are harmlessly
        ;;   overwritten. We read the atom EXACTLY ONCE after the swap
        ;;   returns, so only the last winner fires.
        ;;
        ;; - Can't move :cancel! inside the swap-fn: :cancel! itself does
        ;;   a swap-state! on a different path (:engine/cancelled-tokens).
        ;;   A nested swap on the same backend tangles with retry semantics
        ;;   — at best wasted work, at worst inconsistent intermediate state.
        ;;
        ;; - Can't pre-fetch :cancel! before the swap: between the read and
        ;;   the swap, another swap could install a NEW cont at the same id;
        ;;   we'd then cancel the wrong (already-replaced) cont and leave
        ;;   the actually-displaced one ungated. Capture must happen INSIDE
        ;;   the swap-fn so it observes the same state the CAS commits.
        displaced-cancel (atom nil)
        new-state (rtp/swap-state! context []
                                   (fn [rt-state]
                                     (let [conts (get-in rt-state [:continuations spin-id])
                                           order (inc (count conts))
                                           _     (when-let [c! (:cancel! (get conts cont-id))]
                                                   (reset! displaced-cancel c!))
                                           cont' (-> cont (assoc :id cont-id :order order))
                                           event-key (:event-key cont')]
                                       (-> rt-state
                                           (assoc-in [:continuations spin-id cont-id] cont')
                                           (update-in [:subscriptions event-key spin-id]
                                                      (fn [s] (conj (or s #{}) cont-id)))))))]
    ;; Fire the displaced cont's cancel hook AFTER the swap commits,
    ;; passing the engine context so the cancellation is recorded
    ;; fork-locally (Option A — state-backed cancel tokens).
    (when-let [c! @displaced-cancel] (c! context))
    (get-in new-state [:continuations spin-id cont-id])))

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
    ;; Body slice suspended (returned ::incomplete). Under the unified-queue
    ;; design we do NOT clear :running? on suspension. The body is still
    ;; in-flight; resolution happens later via cache-result!. See
    ;; `mark-running!` semantics in spin/core.cljc.
    ret))

;; =============================================================================
