(ns org.replikativ.spindel.inference.coordinator
  "Generic inference coordination protocol and KernelCoordinator implementation.

  The InferenceCoordinator protocol enables reactive coordination across
  multiple particle/chain execution contexts. KernelCoordinator is the unified
  coordinator that uses PInferenceKernel to control checkpoint behavior:

  - :barrier-policy :every-observe -> SMC-style resampling at observe sites
  - :barrier-policy :none -> Importance sampling (no barriers)

  Effect handlers (sample, observe) are algorithm-agnostic and work with
  KernelCoordinator via the InferenceCoordinator protocol.

  Lifecycle in brief: `start-inference!` forks one execution context per
  particle and registers the kernel. Each particle's spin runs
  independently; when it hits a `sample`/`observe` effect it posts to
  the coordinator's mailbox. The coordinator's drain loop matches the
  PInferenceKernel's policy — `:every-observe` waits for all particles
  before resampling, `:none` lets them run free. Failed particles call
  `notify-failed!` so the coordinator can resolve `on-complete` with an
  `InferenceFailure` marker instead of hanging.

  See `inference.cljc` for the public entry points (`kernel-infer`,
  `importance-sampling`, `smc-infer`) and `kernel.cljc` for the
  PInferenceKernel protocol the coordinator dispatches on."
  (:require [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as rtc]
            [org.replikativ.spindel.engine.state-backend :as backend]
            [org.replikativ.spindel.engine.executor :as executor
             :refer [execute!]]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [org.replikativ.spindel.world.scope :as world-scope]
            [org.replikativ.spindel.inference.measure :as m]
            [org.replikativ.spindel.inference.kernel :as k]
            [replikativ.logging :as log]
            [is.simm.partial-cps.async :as pcps-async]
            [anglican.runtime :as ar]))

;; =============================================================================
;; InferenceCoordinator Protocol
;; =============================================================================

(defprotocol InferenceCoordinator
  "Generic protocol for coordinating inference across multiple execution contexts.

  Different inference algorithms (SMC, MCMC, importance sampling) implement this
  protocol to coordinate checkpointing, resampling/proposals, and completion.

  Effect handlers (choose, constrain) work polymorphically with any coordinator
  implementation via this protocol."

  (notify-checkpoint! [this particle-id context checkpoint]
    "Called by effect handlers when a particle reaches a checkpoint (e.g., constrain).

    This is a reactive callback - the effect handler notifies the coordinator,
    then suspends execution (returns ::incomplete). The coordinator will resume
    the particle when ready.

    Args:
      particle-id - Unique identifier for this particle/chain
      context - Execution context for this particle
      checkpoint - Checkpoint map with {:resolve :reject :observed-value :spin-id :address}

    Returns: nil (async notification)")

  (notify-complete! [this particle-id context result]
    "Called when a particle's spin completes normally (reaches end without checkpoint).

    Args:
      particle-id - Unique identifier for this particle/chain
      context - Execution context for this particle
      result - Final result value from spin

    Returns: nil (async notification)")

  (notify-failed! [this particle-id context error]
    "Called when a particle's spin fails with an error (its CPS chain
    threw before reaching :complete).

    The coordinator MUST account for the failure so the inference still
    resolves — otherwise `await-completion`'s barrier-count never reaches
    `total-particles` and the inference spin hangs forever, blocking the
    calling thread and pinning every particle context (and its daemon
    drain thread) as reachable.

    Default semantics (KernelCoordinator): fail fast — a broken model
    fails every particle identically, so deliver an `InferenceFailure`
    marker to `on-complete` once. `kernel-infer` re-throws it.

    Args:
      particle-id - Unique identifier for this particle/chain
      context - Execution context for this particle
      error - The Throwable that aborted the particle

    Returns: nil (async notification)")

  (await-completion [this]
    "Block until inference is complete.

    Returns: Final result (algorithm-specific: EmpiricalMeasure, samples, etc.)"))

;; =============================================================================
;; Failure marker
;; =============================================================================

(defrecord InferenceFailure [particle-id error])

(defn inference-failure?
  "True iff `x` is an `InferenceFailure` marker delivered by a coordinator
  when a particle aborted. Callers of `await-completion` re-throw on this."
  [x]
  (instance? InferenceFailure x))

;; =============================================================================
;; Canonical particle worlds
;; =============================================================================

(defn create-world-manager
  "Create process-local ownership for every canonical world fork in one
  inference execution. Handles remain host capabilities; only their portable
  descriptors may cross a durable boundary."
  [fork-opts]
  (doto (world-scope/create {:purpose :particle
                             :fork-opts (or fork-opts {})})
    (swap! assoc :generation-phase nil :generation-activity nil)))

(declare maybe-complete-particle-quiescence!)

(defn world-descriptors
  "Return the portable projections retained by a particle-world manager."
  [manager]
  (world-scope/descriptors manager))

(defn- invoke-result!
  "Invoke a value-or-CPS result without assuming a JVM synchronous substrate."
  [operation resolve reject]
  (try
    (if (fn? operation)
      (operation resolve reject)
      (resolve operation))
    (catch #?(:clj Throwable :cljs :default) error
      (reject error))))

(defn fork-particle-world!
  "Fork `source-context` through the canonical Yggdrasil bridge and deliver its
  non-settleable world reference. Particle forks are frozen at their source
  checkpoint: ordinary execution state reads from the fork-time view and every
  registered external system is independently forked through PForkable."
  [manager source-context resolve reject]
  (world-scope/fork! manager source-context resolve reject))

(defn discard-particle-worlds!
  "Discard all worlds owned by manager, newest generation first."
  [manager]
  (world-scope/discard! manager))

(defn await-particle-world-quiescence
  "Return a CPS operation resolved when no particle context is still running."
  [manager]
  (world-scope/await-quiescence manager))

(defn discard-particle-worlds-when-quiescent!
  "Wait for terminal particle callbacks before consuming world authority."
  [manager]
  (world-scope/discard-when-quiescent! manager))

(defn begin-particle-generation-transition!
  "Keep quiescence closed during construction and source retirement."
  [manager]
  (let [activity (world-scope/begin-activity! manager :particle-generation)]
    (swap! manager assoc
           :generation-activity activity
           :generation-phase :forking)
    nil))

(defn- claim-particle-generation-retirement! [manager]
  ;; A volatile written from inside swap! cannot prove that its invocation won:
  ;; the function may have observed :forking on an abandoned CAS attempt. The
  ;; old value returned by swap-vals! is from the committed transition itself.
  (let [[before _after]
        (swap-vals!
         manager
         (fn [state]
           (if (and (= :forking (:generation-phase state))
                    (not (:cancel-requested? state)))
             (assoc state
                    :generation-phase :retiring
                    :retiring-context-ids
                    (->> (:activities state)
                         (keep (fn [[activity-id activity]]
                                 (when (= :particle-context (:kind activity))
                                   activity-id)))
                         set))
             state)))]
    (and (= :forking (:generation-phase before))
         (not (:cancel-requested? before)))))

(defn complete-particle-generation-transition!
  "Admit replacement contexts unless cancellation won the transition."
  [manager contexts]
  (if-let [activity (:generation-activity @manager)]
    (let [exchange
          (world-scope/exchange-activity!
           manager activity
           (mapv (fn [context]
                   {:id (:fork-id context)
                    :kind :particle-context
                    :value context})
                 contexts))]
      (swap! manager dissoc
             :generation-activity :generation-phase :retiring-context-ids)
      (:admitted? exchange))
    ;; Error unwinding closes a transition defensively after the rejecting
    ;; completion may already have consumed its lease.
    (if (empty? contexts)
      true
      (throw (ex-info "Particle generation transition is not active"
                      {:type ::missing-generation-transition})))))

(defn- maybe-clean-cancelled-worlds! [manager]
  (world-scope/maybe-complete-quiescence! manager))

(defn- maybe-complete-particle-quiescence! [manager]
  (world-scope/maybe-complete-quiescence! manager))

(defn particle-context-terminal!
  "Mark one particle context quiescent and trigger deferred cleanup."
  [manager context]
  (world-scope/end-activity! manager (:fork-id context)))

(defn- cancellation-error []
  (ex-info "Inference particle cancelled"
           {:type spin-core/spin-cancelled}))

(defn- cancellation-error? [error]
  (= spin-core/spin-cancelled (:type (ex-data error))))

(defn- resume-checkpoint-reject!
  "Reject one kernel checkpoint on its owning executor.  If admission is
  rejected, run the terminal slice through a synchronous executor over the
  same context/backend so finally blocks and terminal callbacks still run."
  [context checkpoint error]
  (let [reject-checkpoint!
        (fn [execution-context]
          (binding [rtc/*execution-context* execution-context
                    pcps-async/*in-trampoline* false]
            (spin-core/resume (:reject checkpoint) error)))]
    (try
      (execute! (:executor context) #(reject-checkpoint! context))
      (catch #?(:clj Throwable :cljs :default) scheduling-error
        (log/warn :inference/checkpoint-reject-schedule-failed
                  {:fork-id (:fork-id context)
                   :error scheduling-error})
        (reject-checkpoint!
         (assoc context :executor (executor/synchronous-executor)))))))

(defn- take-retirement!
  "Atomically claim a source context's expected retirement callback."
  [coordinator context]
  (let [fork-id (:fork-id context)
        ;; This is a plain process-local atom, so swap-vals! gives us the entry
        ;; from the CAS-winning prior state without a retry-sensitive capture.
        [before _after]
        (swap-vals! (:retiring-contexts coordinator) dissoc fork-id)]
    (get before fork-id)))

(defn- retirement-entry [coordinator context]
  (get @(:retiring-contexts coordinator) (:fork-id context)))

(defn- retire-particle-generation!
  "Unwind all suspended source particles after their child worlds have been
  constructed.  Retirement is expected control flow, not inference failure.

  The coordinator methods claim each terminal callback through
  `:retiring-contexts`; only after every source has quiesced does this CPS
  operation resolve or reject.  The first non-cancellation cleanup error is
  retained while the remaining sources continue unwinding."
  [coordinator particle-states]
  (fn [resolve reject]
    (let [states (vec particle-states)
          remaining (atom (count states))
          first-error (atom nil)
          finish-one!
          (fn [error]
            (when error (compare-and-set! first-error nil error))
            (when (zero? (swap! remaining dec))
              (if-let [error @first-error]
                (reject error)
                (resolve nil))))]
      (if (empty? states)
        (resolve nil)
        (do
          ;; Publish the complete retirement set before rejecting any source;
          ;; synchronous executors may deliver a terminal callback inline.
          (doseq [[_ {:keys [context]}] states]
            (swap! (:retiring-contexts coordinator)
                   assoc (:fork-id context) {:finish! finish-one!}))
          (swap! (:particles coordinator)
                 (fn [particles]
                   (reduce (fn [next-particles [particle-id state]]
                             (assoc next-particles particle-id
                                    (assoc state :status :retiring)))
                           particles
                           states)))
          (doseq [[_particle-id {:keys [context checkpoint]}] states]
            (try
              ;; Cascade into ordinary await/owned-spin edges first.  The
              ;; kernel checkpoint itself is outside that graph and is rejected
              ;; explicitly below.
              (when-let [task (rtp/get-state context [:inference :task])]
                (binding [rtc/*execution-context* context]
                  (spin-core/cancel-spin! task)))
              (resume-checkpoint-reject! context checkpoint
                                         (cancellation-error))
              (catch #?(:clj Throwable :cljs :default) error
                ;; A synchronous fallback can throw before reaching the model's
                ;; terminal callback. Claim and account for that source here.
                (when-let [{:keys [finish!]} (take-retirement! coordinator context)]
                  (particle-context-terminal!
                   (:world-manager coordinator) context)
                  (finish! (when-not (cancellation-error? error)
                             error)))))))))))

(defn- cancel-kernel-checkpoints!
  "Atomically claim and reject continuations parked at a kernel barrier.

  Kernel checkpoints are deliberately coordinated outside Spin's ordinary
  await graph, so `cancel-spin!` cannot discover them. Claiming the particle
  status first prevents a concurrent cancellation from rejecting the same CPS
  slice twice. Terminal accounting still happens only through the particle's
  top-level reject callback."
  [coordinator retiring-context-ids]
  (when-let [particles (:particles coordinator)]
    (let [retiring-context-ids (or retiring-context-ids #{})
          eligible? (fn [state]
                      (and (= :checkpoint (:status state))
                           (not (contains? retiring-context-ids
                                           (get-in state [:context :fork-id])))))
          ;; As with retirement callback claims, derive ownership from the
          ;; CAS-winning old state. A volatile populated inside swap! can retain
          ;; entries from an abandoned retry and reject one checkpoint twice.
          [before _after]
          (swap-vals! particles
                      (fn [states]
                        (reduce-kv
                         (fn [next-states particle-id state]
                           (assoc next-states particle-id
                                  (if (eligible? state)
                                    (assoc state :status :cancelling)
                                    state)))
                         {}
                         states)))
          claimed (into [] (comp (map val) (filter eligible?)) before)
          error (ex-info "Inference particle cancelled"
                         {:type spin-core/spin-cancelled})]
      (doseq [{:keys [context checkpoint]} claimed]
        (try
          (resume-checkpoint-reject! context checkpoint error)
          (catch #?(:clj Throwable :cljs :default) unwind-error
            ;; The synchronous fallback provides the executor-task boundary
            ;; inline. Cancellation is its expected terminal throw; report only
            ;; a genuine cleanup failure and continue unwinding other sources.
            (when-not (cancellation-error? unwind-error)
              (log/error :inference/checkpoint-cancel-unwind-failed
                         {:fork-id (:fork-id context)
                          :error unwind-error}))))))))

(defn cancel-particle-worlds!
  "Cooperatively cancel every live particle. Cleanup begins automatically once
  their resolve/reject callbacks prove quiescence."
  [manager]
  (let [{:keys [client retiring-context-ids]}
        (world-scope/request-cancel! manager)
        contexts (world-scope/activity-values manager :particle-context)]
    ;; Retirement owns only the captured source checkpoints. Replacement
    ;; contexts admitted concurrently are not in that set and must be cancelled.
    (doseq [context contexts
            :when (not (contains? retiring-context-ids (:fork-id context)))]
      (when-let [task (rtp/get-state context [:inference :task])]
        (try
          (binding [rtc/*execution-context* context]
            (spin-core/cancel-spin! task))
          (catch #?(:clj Throwable :cljs :default) error
            (log/error :inference/particle-cancel-failed
                       {:fork-id (:fork-id context) :error error})))))
    ;; The manager transition atomically publishes the source contexts owned by
    ;; generation retirement before cancellation can win. Their checkpoints
    ;; remain retirement's responsibility even during the short interval before
    ;; retire-particle-generation! changes their particle statuses to :retiring.
    (cancel-kernel-checkpoints! client retiring-context-ids)
    (maybe-clean-cancelled-worlds! manager)
    (discard-particle-worlds-when-quiescent! manager)))

;; =============================================================================
;; Helper: Snapshot-Based Context Forking
;; =============================================================================

(defn particle-id
  "The id of the particle in `slot` of generation `generation` (the sweep).
  Deterministic, so the coordinator's particle map iterates in the same order
  in every run of a seeded inference."
  [generation slot]
  (keyword (str "particle-" generation "-" slot)))

(defn fork-particle-context
  "Create an independent, fully materialized child particle context.

  This avoids overlay-backend coupling while retaining parent lineage and
  independently forking live world components such as SCI interpreters. It is
  an in-process operation, not a portable snapshot.

  Args:
    ctx - ExecutionContext to fork

  Returns: New ExecutionContext with AtomBackend (complete independent copy)"
  [ctx]
  (ctx/materialized-fork-context
   ctx
   :clean-in-flight? false))

;; =============================================================================
;; Helper: Pair Checkpoints for Resampling
;; =============================================================================

;; Forward declaration
(declare trigger-kernel-resample!)
(declare resume-in-slice!)
(declare notify-failed!)

(defn pair-checkpoints
  "Match resampled contexts with their original checkpoints.

  Resampling creates duplicated context references (same object multiple times).
  We use identical? to match each resampled context with its original, then
  get the corresponding checkpoint.

  After matching, we fork each context to create independent copies.

  Args:
    resampled-contexts - Contexts after resampling (may have duplicates)
    original-contexts - Original contexts before resampling
    particles - Particle state map with checkpoints

  Returns: Vector of {:context :checkpoint :particle-id} maps"
  [resampled-contexts original-contexts particles]
  (let [;; Convert particle map to vector for indexed access
        particle-vec (vec particles)
        particle-ids (mapv first particle-vec)
        particle-states (mapv second particle-vec)]  ; Extract values (particle states)

    (mapv (fn [resampled-ctx]
            ;; Find which original context this resampled one came from
            ;; Use identical? to match object references (before forking)
            (let [original-idx (first (keep-indexed
                                       (fn [orig-idx orig-ctx]
                                         (when (identical? resampled-ctx orig-ctx)
                                           orig-idx))
                                       original-contexts))
                  ;; Get checkpoint from original particle state
                  original-particle-id (nth particle-ids original-idx)
                  particle-state (nth particle-states original-idx)
                  checkpoint (:checkpoint particle-state)

                  ;; Fork the context AFTER matching (snapshot-based)
                  forked-ctx (fork-particle-context resampled-ctx)

                  ;; Generate new particle ID
                  new-particle-id (keyword (str "particle-" (gensym)))]

              {:context forked-ctx
               :checkpoint checkpoint
               :particle-id new-particle-id
               :original-idx original-idx}))  ; For debugging
          resampled-contexts)))

(defn pair-world-checkpoints!
  "Asynchronously fork each selected source particle through Yggdrasil, then
  pair the frozen child context with the source checkpoint. Duplicate selected
  ancestors produce distinct writable worlds."
  [manager resampled-contexts original-contexts particles resolve reject]
  (let [particle-vec (vec particles)
        particle-ids (mapv first particle-vec)
        particle-states (mapv second particle-vec)]
    ;; Forks usually complete inline, each continuing the next from its own
    ;; callback; every 200 the walk continues on a fresh executor task so
    ;; the depth does not grow with the population (as `world.scope/discard!`).
    (letfn [(step [remaining acc depth]
              (if-let [source-context (first remaining)]
                (let [original-idx
                      (first
                       (keep-indexed
                        (fn [idx original]
                          (when (identical? source-context original) idx))
                        original-contexts))]
                  (if (nil? original-idx)
                    (reject
                     (ex-info "Resampled particle has no source checkpoint"
                              {:type ::missing-particle-source}))
                    (let [original-particle-id (nth particle-ids original-idx)
                          particle-state (nth particle-states original-idx)
                          checkpoint (:checkpoint particle-state)]
                      (fork-particle-world!
                       manager source-context
                       (fn [handle]
                         (let [acc (conj acc
                                         {:context (:child-ctx handle)
                                          :world handle
                                          :checkpoint checkpoint
                                          :particle-id
                                          (keyword (str "particle-" (gensym)))
                                          :source-particle-id original-particle-id
                                          :original-idx original-idx})]
                           (if (< depth 200)
                             (step (next remaining) acc (inc depth))
                             (let [continue! #(step (next remaining) acc 0)]
                               (try
                                 (execute! (:executor source-context) continue!)
                                 (catch #?(:clj Throwable :cljs :default) _
                                   (continue!)))))))
                       reject))))
                (resolve acc)))]
      (step resampled-contexts [] 0))))

;; =============================================================================
;; Continuation Resume
;; =============================================================================

(defn replay-from-start!
  "Run a completed particle again from its first checkpoint, in place: the
   `:iterate` action. The log-weight is reset and every observe re-adds its
   term; sample sites reach the kernel's `step` with the trace of the previous
   pass.

   This is a FULL replay. Resuming a stored checkpoint in the middle of a
   program, in place, cannot be made correct (the state at that checkpoint is
   gone: upstream observes drop out of the weight, a rejected pass leaves its
   state behind). Moves that change some sites and keep the rest are
   `inference.trace/mh-step`, which replays in a fork of the world as it was."
  [context]
  (let [checkpoints (rtp/get-state context [:inference :checkpoints])
        ;; Program order: checkpoints live in a map, and map key order is not
        ;; program order past eight entries.
        checkpoint (first (sort-by :seq (vals checkpoints)))]
    (when-not checkpoint
      (throw (ex-info "Cannot replay: no checkpoint found" {})))
    (rtp/swap-state! context [:inference :log-weight] (constantly 0.0))
    ;; Re-execution re-creates every checkpoint after the first with fresh
    ;; continuations; stale ones would trip the duplicate-address guard.
    (rtp/swap-state! context [:inference :checkpoints]
                     (constantly {(:address checkpoint) checkpoint}))
    (let [{:keys [resolve source options address]} checkpoint
          {:keys [observe]} options
          entry (get (rtp/get-state context [:inference :trace]) address)
          value (cond
                  (some? observe) observe
                  (map? entry) (:value entry)
                  (some? entry) entry
                  :else (ar/sample* source))]
      ;; NOTE: (some? observe), not observe: an observed value may be false.
      (when (some? observe)
        (rtp/swap-state! context [:inference :log-weight]
                         (fn [w] (+ (or w 0.0) (ar/observe* source observe)))))
      (execute! (:executor context)
                (fn [] (resume-in-slice! context checkpoint resolve value))))))

(defn ^:no-doc resume-in-slice!
  "Invoke a checkpoint's continuation in the environment it suspended in.

   Restores the checkpoint's `:slice-state` (bindings, addressing
   chain-head, dep tracking) exactly as the engine does for track/await
   continuations, binds the execution context and the spin id, and resumes.
   Without the chain-head restore a replayed body mints new addresses for
   every site after the resume point. A checkpoint without a snapshot
   (none are produced any more) resumes in the caller's context unchanged."
  [context checkpoint cont value]
  (let [spin-id (:spin-id checkpoint)
        rctx (if (and spin-id (:slice-state checkpoint))
               (simple/restore-slice-state! context spin-id checkpoint)
               context)]
    (binding [rtc/*execution-context* rctx
              rtc/*spin-id* (or spin-id rtc/*spin-id*)
              pcps-async/*in-trampoline* false]
      (spin-core/resume cont value))))

(defn record-choice!
  "Record the value chosen at a checkpoint: the trace entry (value,
   distribution, its log-density) and, for an observe, its likelihood in the
   particle's log-weight. `log-weight-delta` is an extra weight term a
   kernel reports (e.g. log p − log q of a variational proposal)."
  [context checkpoint value & [log-weight-delta]]
  (let [{:keys [source options address]} checkpoint
        observed? (some? (:observe options))
        log-prob (ar/observe* source value)]
    (rtp/swap-state! context [:inference :trace]
                     (fn [trace]
                       (assoc (or trace {}) address
                              {:value value
                               :distribution source
                               :log-prob log-prob
                               :observed? observed?})))
    ;; NOTE: observed?, not observe: an observed value may be false.
    (when (or observed? log-weight-delta)
      (rtp/swap-state! context [:inference :log-weight]
                       (fn [w] (+ (or w 0.0)
                                  (if observed? log-prob 0.0)
                                  (or log-weight-delta 0.0)))))))

(defn resume-choice!
  "Resume a checkpoint's continuation with `value` on the particle's
   executor, in the slice environment the checkpoint captured (binds
   *execution-context* so resolve-fn reads the updated particle-id)."
  [context checkpoint value]
  (execute! (:executor context)
            (fn [] (resume-in-slice! context checkpoint (:resolve checkpoint) value))))

(defn resume-particle-with-value!
  "Record `value` at the checkpoint (trace entry, observe weight) and resume
  the particle with it."
  [context checkpoint value]
  (log/debug :coordinator/resume-particle {:address (:address checkpoint) :value value})
  (record-choice! context checkpoint value)
  (resume-choice! context checkpoint value))

(defn- arrive-at-barrier!
  "Count one particle in; the last to arrive processes the barrier. A throw
  there would die silently in the future and leave the inference hanging, so
  it fails the inference instead."
  [coordinator]
  (let [count (swap! (:barrier-count coordinator) inc)]
    (log/debug :kernel-coord/barrier-count {:count count :total (:total-particles coordinator)})
    (when (= count (:total-particles coordinator))
      (future
        (try (trigger-kernel-resample! coordinator)
             (catch #?(:clj Throwable :cljs :default) t
               (log/error :kernel-coord/barrier-failed {:error t})
               (notify-failed! coordinator :barrier (:parent-runtime coordinator) t)))))))

;; =============================================================================
;; KernelCoordinator - Generic Kernel-Based Inference
;; =============================================================================
;;
;; This coordinator uses PInferenceKernel to decide values at checkpoints.
;; It supports:
;; - :assign action: Simple forward sampling (like importance sampling)
;; - Barrier synchronization for SMC-style resampling
;;
;; See the namespace docstring above for the architectural overview.

(defrecord KernelCoordinator
           [kernel           ; PInferenceKernel instance
            particles        ; atom: {particle-id -> {:context :checkpoint :status :log-weight :retained?}}
            barrier-count    ; atom: how many have reached current checkpoint
            total-particles  ; int: N
            barrier-policy   ; :every-observe | :manual | :none
            resample-threshold ; float: ESS threshold (default 0.5)
            on-complete      ; Deferred for final result
            current-sweep    ; atom: which checkpoint round we're on
            parent-runtime   ; runtime where coordinator was created (for delivery)
            delivered?       ; atom: flag to ensure we only deliver once
            world-manager    ; canonical particle worlds, or nil for legacy fresh roots
            retiring-contexts ; atom: fork-id -> expected generation-retirement callback
            log-normalizer   ; atom: log Z accumulated at resampling steps
   ;; PGIBBS support
            pgibbs-retained-trace  ; atom: retained trace for PGIBBS (nil if not using)
            retained-particle-id]  ; atom: particle-id of retained particle

  InferenceCoordinator

  (notify-checkpoint! [this particle-id context checkpoint]
    (if (retirement-entry this context)
      ;; A cancellation `finally` may itself reach a probabilistic checkpoint.
      ;; It cannot join the next generation's barrier; keep unwinding the same
      ;; retired slice through its reject continuation.
      (try
        (resume-checkpoint-reject! context checkpoint (cancellation-error))
        (catch #?(:clj Throwable :cljs :default) error
          (when-let [{:keys [finish!]} (take-retirement! this context)]
            (when world-manager
              (particle-context-terminal! world-manager context))
            (finish! (when-not (cancellation-error? error)
                       error)))))
      (let [particle-sweep (rtp/get-state context [:inference :sweep])
            coordinator-sweep @current-sweep]
      ;; Ignore notifications from previous sweeps (race condition protection)
        (when (= particle-sweep coordinator-sweep)
          (let [;; Get current trace from context
                trace (or (rtp/get-state context [:inference :trace]) {})
                {:keys [options address]} checkpoint
                {:keys [observe]} options

              ;; PGIBBS: Check if this is the retained particle at a sample site
              ;; If so, use value from retained trace instead of sampling fresh
                retained-trace @pgibbs-retained-trace
                is-retained? (and retained-trace
                                  (= particle-id @retained-particle-id))
                use-retained-value? (and is-retained?
                                         (not (some? observe))  ; sample site, not observe
                                         (contains? retained-trace address))

              ;; Override kernel result if using retained trace value
                kernel-result (if use-retained-value?
                              ;; Use retained trace value directly
                                (let [retained-value (get-in retained-trace [address :value])]
                                  (log/debug :pgibbs/use-retained-value {:particle-id particle-id
                                                                         :address address
                                                                         :value retained-value})
                                  {:action :assign :value retained-value})
                              ;; Otherwise ask kernel what to do
                                (k/step kernel context checkpoint trace))]

            (log/debug :kernel-coord/checkpoint {:particle-id particle-id
                                                 :sweep coordinator-sweep
                                                 :action (:action kernel-result)
                                                 :is-retained? is-retained?})

            (case (:action kernel-result)
            ;; Simple assignment - resume immediately or barrier
              :assign
              (let [{:keys [value log-weight-delta]} kernel-result]
                ;; Record first: at a barrier the observe's likelihood must be
                ;; in the weight the population is resampled on.
                (record-choice! context checkpoint value log-weight-delta)
                (if (and (= barrier-policy :every-observe) (some? observe))
                  (do
                    (swap! particles assoc particle-id
                           {:context context
                            :checkpoint checkpoint
                            :value value
                            :status :checkpoint
                            :log-weight (rtp/get-state context [:inference :log-weight])
                            :retained? is-retained?})
                    (arrive-at-barrier! this))
                  (resume-choice! context checkpoint value)))))))))

  (notify-complete! [this particle-id context result]
    (if-let [{:keys [finish!]} (take-retirement! this context)]
      (do
        (when world-manager
          (particle-context-terminal! world-manager context))
        (finish! nil))
      (let [particle-sweep (rtp/get-state context [:inference :sweep])
            coordinator-sweep @current-sweep]
      ;; Ignore notifications from previous sweeps
        (when (= particle-sweep coordinator-sweep)
          (log/debug :kernel-coord/complete {:particle-id particle-id})

        ;; Store result in context
          (rtp/swap-state! context [:inference :result] (constantly result))

        ;; Get trace and ask kernel
          (let [trace (or (rtp/get-state context [:inference :trace]) {})
                kernel-result (k/on-complete kernel context trace result)]

            (case (:action kernel-result)
            ;; Done - record completion
              :done
              (let [;; Use kernel's accepted result (may differ from current if proposal rejected)
                    accepted-result (or (:result kernel-result) result)
                    accepted-trace (or (:trace kernel-result) trace)]

              ;; Update context with accepted state (for m/get-value to return correct value)
                (rtp/swap-state! context [:inference :result] (constantly accepted-result))
                (rtp/swap-state! context [:inference :trace] (constantly accepted-trace))

                (swap! particles assoc particle-id
                       {:context context
                        :status :complete
                        :result accepted-result
                        :log-weight (:log-weight kernel-result)})

                (when world-manager
                  (particle-context-terminal! world-manager context))

                (arrive-at-barrier! this))

            ;; Iterate - run the whole program again, in place
              :iterate
              (do
                (when (seq (:updates kernel-result))
                  (throw (ex-info "In-place partial replay is not supported; use inference.trace/mh-step"
                                  {:type ::partial-replay-unsupported
                                   :updates (keys (:updates kernel-result))})))
                (log/debug :kernel-coord/iterate {:particle-id particle-id})
              ;; Clear result since we're re-running
                (rtp/swap-state! context [:inference :result] (constantly nil))
                (replay-from-start! context))))))))

  (notify-failed! [this particle-id context error]
    (if-let [{:keys [finish!]} (take-retirement! this context)]
      (do
        (when world-manager
          (particle-context-terminal! world-manager context))
        ;; Cancellation is the expected control signal. A finally/cleanup
        ;; failure remains a real inference failure, but only after every
        ;; superseded source has been given a chance to unwind.
        (finish! (when-not (cancellation-error? error) error)))
      (do
        (log/error :kernel-coord/particle-failed {:particle-id particle-id
                                                  :error error})
    ;; Record the failure on the particle (so it counts as "done" for any
    ;; bookkeeping that walks particle state). No sweep check: a particle
    ;; abort fails the whole inference regardless of sweep — a broken
    ;; model fails every particle identically.
        (swap! particles assoc particle-id
               {:context context :status :failed :error error})
        (when world-manager
          (particle-context-terminal! world-manager context))
    ;; Fail fast: deliver an InferenceFailure marker to on-complete once.
    ;; kernel-infer awaits this Deferred and re-throws on the marker.
    ;; Without this, the still-running particles (if any) never let
    ;; barrier-count reach total-particles, so on-complete is never
    ;; delivered and (await (await-completion …)) waits forever.
        (when (compare-and-set! delivered? false true)
          (binding [rtc/*execution-context* parent-runtime]
            (sync/deliver! on-complete (->InferenceFailure particle-id error)))
          (when world-manager
            (cancel-particle-worlds! world-manager))))))

  (await-completion [_this]
    on-complete))

;; =============================================================================
;; Kernel Coordinator Resample Logic
;; =============================================================================

(defn- ancestor-indices
  "Ancestor index per slot. Plain SMC: systematic resampling. Conditional
  SMC (PGibbs): the retained slot keeps its own lineage and the other N−1
  are drawn multinomially, so the retained trajectory can never be
  resampled away."
  [weights n retained-slot]
  (if retained-slot
    (vec (for [slot (range n)]
           (if (= slot retained-slot) slot (m/sample-categorical weights))))
    (m/systematic-resample weights n)))

(defn- resume-resampled-contexts!
  "Install the next generation: the forked waiting particles (resumed past
  the barrier's observe, which is already recorded) and the completed
  particles carried over as they are. Completed particles count as arrived
  at the next barrier; if every slot is complete the population is done."
  [coordinator contexts-with-checkpoints slot-numbers resample? retained-position carried]
  (reset! (:particles coordinator) {})
  (reset! (:barrier-count coordinator) 0)
  (let [retained-pid @(:retained-particle-id coordinator)
        sweep @(:current-sweep coordinator)
        running (vec (map-indexed
                      (fn [i {:keys [context world] :as entry}]
                        (let [pid (if (= i retained-position)
                                    retained-pid
                                    (particle-id sweep (nth slot-numbers i)))]
                          (when resample?
                            (rtp/swap-state! context [:inference :log-weight] (constantly 0.0)))
                          (rtp/swap-state! context [:inference :particle-id] (constantly pid))
                          (rtp/swap-state! context [:inference :sweep] (constantly sweep))
                          (when world
                            (rtp/swap-state! context [:inference :world] (constantly world)))
                          (assoc entry :particle-id pid)))
                      contexts-with-checkpoints))]
    (doseq [{:keys [particle-id state]} carried]
      (swap! (:particles coordinator) assoc particle-id state))
    (doseq [{:keys [context world particle-id]} running]
      (swap! (:particles coordinator) assoc particle-id
             {:context context :world world :status :running
              :retained? (= particle-id retained-pid)}))
    (if (and (seq carried) (= (count carried) (:total-particles coordinator)))
      (trigger-kernel-resample! coordinator)
      (do
        (swap! (:barrier-count coordinator) + (count carried))
        (doseq [{:keys [context checkpoint value]} running]
          (resume-choice! context checkpoint value))))))

(def ^:private projected-inference-keys
  #{:log-weight :choice-stack :trace :particle-id :sweep :result
    :deterministic :interventions :mcmc})

(declare project-settled-particle-context)

(defn project-posterior-context
  "Create a parentless immutable posterior context from a world that ended."
  [context]
  (project-settled-particle-context context {}))

(defn- project-settled-particle-context
  "Create a parentless immutable posterior context. Returning the settled
  execution context itself would retain its complete resampling ancestry."
  [context descriptors-by-id]
  (let [inference-state (rtp/get-state context [:inference])
        creation-descriptor (some-> inference-state :world :descriptor)
        settled-descriptor (get descriptors-by-id
                                (:fork/id creation-descriptor)
                                creation-descriptor)
        projected (cond-> (select-keys inference-state
                                       projected-inference-keys)
                    (:world inference-state)
                    (assoc :world-descriptor settled-descriptor))]
    (assoc context
           :backend (backend/create-immutable-backend
                     {:inference projected}
                     {:source-fork-id (:fork-id context)
                      :projection :inference-posterior})
           :parent-ctx nil
           :bindings {}
           :metadata {:inference/projection true}
           :running nil
           :drain-active nil)))

(defn trigger-kernel-resample!
  "Process a barrier: every particle is waiting at an observe or complete.

  The whole population is resampled when its ESS falls below the threshold
  (always, in conditional SMC), and the log mean weight is folded into the
  evidence. Waiting ancestors are forked and resumed; completed ones — a
  particle that reached fewer observes than the others — are carried along
  with their final weight. When every particle is complete the measure is
  delivered.

  PGIBBS mode: the retained particle's lineage survives every resampling and
  it follows its fixed trace at sample sites."
  [coordinator]
  (swap! (:current-sweep coordinator) inc)

  (let [particles-state @(:particles coordinator)
        entries (vec particles-state)
        n (count entries)
        state-of #(val (nth entries %))
        is-pgibbs? (some? @(:pgibbs-retained-trace coordinator))]

    (if (every? #(= :complete (:status (val %))) entries)
      ;; All particles completed - deliver final result
      (when (compare-and-set! (:delivered? coordinator) false true)
        (let [final-particles (vals particles-state)
              contexts (mapv :context final-particles)
              log-weights (mapv #(or (:log-weight %) 0.0) final-particles)
              with-evidence #(assoc % :log-normalizer @(:log-normalizer coordinator))
              deliver!
              (fn [value]
                (binding [rtc/*execution-context* (:parent-runtime coordinator)]
                  (sync/deliver! (:on-complete coordinator) value)))]
          (log/debug :kernel-coord/all-complete {:num-sweeps @(:current-sweep coordinator)
                                                 :num-particles (count contexts)})
          (if-let [manager (:world-manager coordinator)]
            (invoke-result!
             (discard-particle-worlds! manager)
             (fn [_]
               (let [descriptors-by-id (into {} (map (juxt :fork/id identity))
                                             (world-descriptors manager))]
                 (deliver!
                  (with-evidence
                    (m/empirical
                     (mapv vector
                           (mapv #(project-settled-particle-context % descriptors-by-id) contexts)
                           log-weights))))))
             (fn [error]
               (deliver! (->InferenceFailure :particle-world-cleanup error))))
            (deliver! (with-evidence (m/empirical (mapv vector contexts log-weights)))))))

      (let [log-weights (mapv #(or (:log-weight (state-of %)) 0.0) (range n))
            weights (m/normalize-log-weights log-weights)
            retained-slot (when is-pgibbs?
                            (first (keep-indexed
                                    (fn [i [pid _]] (when (= pid @(:retained-particle-id coordinator)) i))
                                    entries)))
            resample? (or (some? retained-slot)
                          (< (m/compute-ess weights) (* (:resample-threshold coordinator) n)))
            waiting-idxs (filterv #(= :checkpoint (:status (state-of %))) (range n))
            ancestors (if resample?
                        (ancestor-indices weights n retained-slot)
                        (vec (range n)))
            slots (map-indexed vector ancestors)
            checkpoint-slots (filterv #(= :checkpoint (:status (state-of (second %)))) slots)
            retained-position (first (keep-indexed (fn [i [slot _]] (when (= slot retained-slot) i))
                                                   checkpoint-slots))
            carried (vec (for [[slot a] slots
                               :let [st (state-of a)]
                               :when (= :complete (:status st))]
                           {:particle-id (if (= slot retained-slot)
                                           @(:retained-particle-id coordinator)
                                           (particle-id @(:current-sweep coordinator) slot))
                            :state (cond-> st resample? (assoc :log-weight 0.0))}))
            ;; the waiting sources: forked into the next generation, then retired
            waiting-state (into {} (map #(nth entries %)) waiting-idxs)
            original-contexts-ordered (mapv (comp :context val) waiting-state)
            resampled-contexts (mapv #(:context (state-of (second %))) checkpoint-slots)
            with-values (fn [contexts-with-checkpoints]
                          (mapv (fn [{:keys [original-idx] :as e}]
                                  (assoc e :value (:value (val (nth (vec waiting-state) original-idx)))))
                                contexts-with-checkpoints))
            continue!
            (fn [contexts-with-checkpoints]
              (let [cwc (with-values contexts-with-checkpoints)]
                (if-let [manager (:world-manager coordinator)]
                  (if (claim-particle-generation-retirement! manager)
                    (invoke-result!
                     (retire-particle-generation! coordinator waiting-state)
                     (fn [_]
                       (if (complete-particle-generation-transition! manager (mapv :context cwc))
                         (resume-resampled-contexts! coordinator cwc (mapv first checkpoint-slots) resample? retained-position carried)
                         ;; Cancellation landed while source finalizers were
                         ;; running. The children were never started.
                         (notify-failed! coordinator :particle-generation
                                         (:parent-runtime coordinator)
                                         (cancellation-error))))
                     (fn [retirement-error]
                       (complete-particle-generation-transition! manager [])
                       (notify-failed! coordinator :particle-retirement
                                       (:parent-runtime coordinator)
                                       retirement-error)))
                    ;; Cancellation won while child worlds were being forked
                    ;; and already owns the old source checkpoints.
                    (do
                      (complete-particle-generation-transition! manager [])
                      (notify-failed! coordinator :particle-generation
                                      (:parent-runtime coordinator)
                                      (cancellation-error))))
                  (resume-resampled-contexts! coordinator cwc (mapv first checkpoint-slots) resample? retained-position carried))))]

        (log/debug :kernel-coord/barrier {:sweep @(:current-sweep coordinator)
                                          :resample? resample?
                                          :waiting (count waiting-idxs)
                                          :is-pgibbs? is-pgibbs?})
        (when resample?
          (swap! (:log-normalizer coordinator) + (m/log-mean-exp log-weights)))

        (if-let [manager (:world-manager coordinator)]
          (do
            ;; Hold quiescence before the first asynchronous child fork.
            (begin-particle-generation-transition! manager)
            (pair-world-checkpoints!
             manager resampled-contexts original-contexts-ordered waiting-state
             continue!
             (fn [fork-error]
               (complete-particle-generation-transition! manager [])
               (notify-failed! coordinator :particle-world
                               (:parent-runtime coordinator) fork-error))))
          (continue! (pair-checkpoints resampled-contexts original-contexts-ordered waiting-state)))))))

;; =============================================================================
;; KernelCoordinator Constructor
;; =============================================================================

(defn create-kernel-coordinator
  "Create KernelCoordinator for kernel-based inference.

  Args:
    runtime - Parent runtime for delivery
    kernel - PInferenceKernel instance
    num-particles - Number of particles
    opts - Optional map with:
      :barrier-policy - :every-observe | :manual | :none (default :every-observe)
      :resample-threshold - ESS threshold (default 0.5)
      :pgibbs-retained-trace - Retained trace for PGIBBS (nil for standard SMC)

  Returns: KernelCoordinator instance"
  [runtime kernel num-particles & [opts]]
  (->KernelCoordinator
   kernel
   (atom {})                                        ; particles
   (atom 0)                                         ; barrier-count
   num-particles                                    ; total-particles
   (or (:barrier-policy opts) :every-observe)       ; barrier-policy
   (or (:resample-threshold opts) 0.5)              ; resample-threshold
   (sync/create-deferred runtime)                   ; on-complete
   (atom 0)                                         ; current-sweep
   runtime                                          ; parent-runtime
   (atom false)                                     ; delivered?
   (:world-manager opts)                            ; world-manager
   (atom {})                                        ; retiring-contexts
   (atom 0.0)                                       ; log-normalizer
    ;; PGIBBS fields
   (atom (:pgibbs-retained-trace opts))             ; pgibbs-retained-trace
   (atom nil)))                                     ; retained-particle-id (set by first particle)
