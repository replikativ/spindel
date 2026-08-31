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
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.yggdrasil :as ygg]
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
  (atom {:id (random-uuid)
         :status :open
         :fork-opts (or fork-opts {})
         :handles []
         :active-contexts {}
         :cancel-requested? false
         :cleanup-started? false
         :quiescence (atom {:status :pending :readers []})
         :cleanup (atom {:status :pending :readers []})}))

(defn world-descriptors
  "Return the portable projections retained by a particle-world manager."
  [manager]
  (let [{:keys [descriptors handles]} @manager]
    (or descriptors (mapv ygg/fork-descriptor handles))))

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
  ForkHandle. Particle forks are frozen at their source checkpoint: ordinary
  execution state reads from the fork-time view and every registered external
  system is independently forked through PForkable."
  [manager source-context resolve reject]
  (let [{:keys [id fork-opts]} @manager
        opts (-> fork-opts
                 (assoc :mode :frozen
                        :purpose :particle
                        :owner id
                        :sync? false))]
    (binding [rtc/*execution-context* source-context
              pcps-async/*in-trampoline* false]
      (invoke-result!
       (ygg/fork! opts)
       (fn [handle]
         (swap! manager update :handles conj handle)
         (resolve handle))
       reject))))

(defn discard-particle-worlds!
  "Discard all worlds owned by `manager`, newest generation first. Returns a
  CPS operation and is idempotent after successful cleanup."
  [manager]
  (fn [resolve reject]
    (let [cleanup (:cleanup @manager)
          immediate (volatile! nil)]
      ;; A read-only settlement preflight reopens its ForkHandle. Retrying gets
      ;; a fresh subscriber generation; mutating/incomplete failures remain
      ;; terminal in the manager and keep their memoized rejection.
      (loop []
        (let [state @cleanup]
          (when (and (= :failed (:status state))
                     (= :open (:status @manager))
                     (not (compare-and-set!
                           cleanup state {:status :pending :readers []})))
            (recur))))
      ;; Subscribe before trying to become the cleanup owner. Completion and
      ;; subscription linearize on this atom, so concurrent callers neither
      ;; hang nor execute settlement twice.
      (swap! cleanup
             (fn [state]
               (if (= :pending (:status state))
                 (update state :readers conj {:resolve resolve :reject reject})
                 (do (vreset! immediate state) state))))
      (when-let [{:keys [status value error]} @immediate]
        (if (= :done status) (resolve value) (reject error)))
      (letfn [(complete! [status payload]
                (let [readers (volatile! [])]
                  (swap! cleanup
                         (fn [state]
                           (if (= :pending (:status state))
                             (do
                               (vreset! readers (:readers state))
                               (cond-> {:status status :readers []}
                                 (= status :done) (assoc :value payload)
                                 (= status :failed) (assoc :error payload)))
                             state)))
                  (doseq [{:keys [resolve reject]} @readers]
                    ((if (= status :done) resolve reject) payload))))
              (fail! [handle error]
                (swap! manager assoc
                       :status (if (ygg/open-fork? handle) :open :failed)
                       :error error)
                (complete! :failed error))
              (step [handles]
                (if-let [handle (first handles)]
                  (if (ygg/open-fork? handle)
                    (binding [rtc/*execution-context* (:parent-ctx handle)
                              pcps-async/*in-trampoline* false]
                      (invoke-result!
                       (ygg/discard-fork! handle {:sync? false})
                       (fn [_] (step (next handles)))
                       (fn [error] (fail! handle error))))
                    (step (next handles)))
                  (do
                    ;; Replace process-local affine capabilities with portable
                    ;; audit projections. This releases every superseded
                    ;; generation once the final measure no longer needs it.
                    (swap! manager
                           (fn [state]
                             (-> state
                                 (assoc :status :discarded
                                        :descriptors
                                        (mapv ygg/fork-descriptor
                                              (:handles state))
                                        :handles [])
                                 (dissoc :coordinator))))
                    (complete! :done nil))))
              (claim! []
                (let [state @manager]
                  (case (:status state)
                    :open
                    (if (compare-and-set! manager state
                                          (assoc state :status :discarding))
                      (step (reverse (:handles state)))
                      (recur))

                    :discarded (complete! :done nil)
                    :failed (complete! :failed (:error state))
                    ;; Another caller owns :discarding; this caller is already
                    ;; subscribed to the shared cleanup outcome.
                    :discarding nil
                    nil)))]
        (when-not @immediate (claim!))))))

(defn await-particle-world-quiescence
  "Return a CPS operation resolved when no particle context is still running."
  [manager]
  (fn [resolve _reject]
    (let [quiescence (:quiescence @manager)
          immediate? (volatile! false)]
      (swap! quiescence
             (fn [state]
               (if (= :done (:status state))
                 (do (vreset! immediate? true) state)
                 (update state :readers conj resolve))))
      (when @immediate? (resolve nil)))))

(defn discard-particle-worlds-when-quiescent!
  "Return a CPS operation that waits for terminal particle callbacks before
  consuming world settlement authority."
  [manager]
  (fn [resolve reject]
    ((await-particle-world-quiescence manager)
     (fn [_]
       (invoke-result! (discard-particle-worlds! manager) resolve reject))
     reject)))

(defn register-particle-contexts!
  "Replace the live particle generation tracked by a world manager."
  [manager contexts]
  (swap! manager assoc
         :active-contexts (into {} (map (juxt :fork-id identity)) contexts))
  nil)

(defn- maybe-clean-cancelled-worlds! [manager]
  (loop []
    (let [state @manager]
      (when (and (:cancel-requested? state)
                 (empty? (:active-contexts state))
                 (not (:cleanup-started? state)))
        (if (compare-and-set! manager state (assoc state :cleanup-started? true))
          (invoke-result!
           (discard-particle-worlds! manager)
           (constantly nil)
           (fn [error]
             (log/error :inference/particle-world-cleanup-failed
                        {:error error})))
          (recur))))))

(defn particle-context-terminal!
  "Mark one particle context quiescent and trigger deferred failure cleanup."
  [manager context]
  (let [remaining (volatile! nil)]
    (swap! manager
           (fn [state]
             (let [active (dissoc (:active-contexts state) (:fork-id context))]
               (vreset! remaining active)
               (assoc state :active-contexts active))))
    (when (empty? @remaining)
      (let [readers (volatile! [])
            quiescence (:quiescence @manager)]
        (swap! quiescence
               (fn [state]
                 (if (= :done (:status state))
                   state
                   (do (vreset! readers (:readers state))
                       {:status :done :readers []}))))
        (doseq [reader @readers] (reader nil))
        (maybe-clean-cancelled-worlds! manager)))
    nil))

(defn- cancel-kernel-checkpoints!
  "Atomically claim and reject continuations parked at a kernel barrier.

  Kernel checkpoints are deliberately coordinated outside Spin's ordinary
  await graph, so `cancel-spin!` cannot discover them. Claiming the particle
  status first prevents a concurrent cancellation from rejecting the same CPS
  slice twice. Terminal accounting still happens only through the particle's
  top-level reject callback."
  [coordinator]
  (when-let [particles (:particles coordinator)]
    (let [claimed (volatile! [])
          error (ex-info "Inference particle cancelled"
                         {:type spin-core/spin-cancelled})]
      (swap! particles
             (fn [states]
               (reduce-kv
                (fn [next-states particle-id state]
                  (if (= :checkpoint (:status state))
                    (do
                      (vswap! claimed conj state)
                      (assoc next-states particle-id
                             (assoc state :status :cancelling)))
                    (assoc next-states particle-id state)))
                {}
                states)))
      (doseq [{:keys [context checkpoint]} @claimed]
        (let [reject-checkpoint!
              (fn [execution-context]
                (binding [rtc/*execution-context* execution-context
                          pcps-async/*in-trampoline* false]
                  (spin-core/resume (:reject checkpoint) error)))]
          (try
            (execute! (:executor context) #(reject-checkpoint! context))
            (catch #?(:clj Throwable :cljs :default) scheduling-error
              ;; A rejected executor cannot own this CPS slice. Unwind it on
              ;; the cancelling caller so :finally and the terminal callback
              ;; still run and the affine worlds cannot remain wedged.
              (log/warn :inference/checkpoint-cancel-schedule-failed
                        {:fork-id (:fork-id context)
                         :error scheduling-error})
              (try
                ;; Continuation unwinding may itself enqueue engine events. A
                ;; rejected particle executor cannot service those either, so
                ;; run the same context/backend through a synchronous executor
                ;; for this terminal slice only.
                (reject-checkpoint!
                 (assoc context :executor
                        (executor/synchronous-executor)))
                (catch #?(:clj Throwable :cljs :default) unwind-error
                  ;; Executor guard-task normally contains a terminal throw.
                  ;; The synchronous fallback must provide the same boundary
                  ;; so one particle cannot prevent the remaining claims from
                  ;; unwinding.
                  (when-not (spin-core/spin-cancelled? unwind-error)
                    (log/error :inference/checkpoint-cancel-unwind-failed
                               {:fork-id (:fork-id context)
                                :error unwind-error})))))))))))

(defn cancel-particle-worlds!
  "Cooperatively cancel every live particle. Cleanup begins automatically once
  their resolve/reject callbacks prove quiescence."
  [manager]
  (let [{:keys [active-contexts coordinator]}
        (swap! manager assoc :cancel-requested? true)
        contexts (vals active-contexts)]
    (doseq [context contexts]
      (when-let [task (rtp/get-state context [:inference :task])]
        (try
          (binding [rtc/*execution-context* context]
            (spin-core/cancel-spin! task))
          (catch #?(:clj Throwable :cljs :default) error
            (log/error :inference/particle-cancel-failed
                       {:fork-id (:fork-id context) :error error})))))
    (cancel-kernel-checkpoints! coordinator)
    (maybe-clean-cancelled-worlds! manager)
    (await-particle-world-quiescence manager)))

;; =============================================================================
;; Helper: Snapshot-Based Context Forking
;; =============================================================================

(defn fork-particle-context
  "Create independent copy of particle context using snapshot-based forking.

  Uses snapshot-context + restore-snapshot instead of fork-context to avoid
  overlay backend isolation issues (see OVERLAY_BACKEND_BUG.md).

  This creates a complete independent copy with AtomBackend, ensuring no
  shared state between particles.

  Args:
    ctx - ExecutionContext to fork

  Returns: New ExecutionContext with AtomBackend (complete independent copy)"
  [ctx]
  (let [snap (ctx/snapshot-context ctx
                                   :clean-in-flight? false   ; Keep spin states as-is
                                   :include-pending? false)] ; Don't include pending events
    (ctx/restore-snapshot snap
                          :drain-events? false)))  ; Don't drain - caller initializes state first

;; =============================================================================
;; Helper: Pair Checkpoints for Resampling
;; =============================================================================

;; Forward declaration
(declare trigger-kernel-resample!)

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
    (letfn [(step [remaining acc]
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
                         (step
                          (next remaining)
                          (conj acc
                                {:context (:child-ctx handle)
                                 :world handle
                                 :checkpoint checkpoint
                                 :particle-id
                                 (keyword (str "particle-" (gensym)))
                                 :source-particle-id original-particle-id
                                 :original-idx original-idx})))
                       reject))))
                (resolve acc)))]
      (step resampled-contexts []))))

;; =============================================================================
;; Continuation Resume
;; =============================================================================

(defn resume-from-checkpoint!
  "Resume particle execution from a checkpoint, optionally with trace modifications.

   This unified function handles both :modify (mid-execution replay) and
   :iterate (post-completion replay) actions. Both are fundamentally the same:
   apply updates to trace, then resume from earliest modified checkpoint.

   Args:
     context - Particle's execution context
     updates - Map of {address -> new-value} to apply to trace (raw values)

   Returns: nil (side effect: resumes continuation via scheduler)"
  [context updates]
  (let [checkpoints (rtp/get-state context [:inference :checkpoints])
        trace (or (rtp/get-state context [:inference :trace]) {})

        ;; Get checkpoint addresses in order (first = program start)
        ;; Note: checkpoints are stored as {address -> checkpoint}
        checkpoint-addrs (keys checkpoints)

        ;; Apply updates to trace - updates are raw values, trace has rich entries
        ;; Update the :value field of existing rich entries
        updated-trace (reduce-kv
                       (fn [t addr new-value]
                         (let [existing (get t addr)
                               checkpoint (get checkpoints addr)]
                           (if existing
                              ;; Update existing entry's value
                             (assoc t addr (assoc existing :value new-value))
                              ;; Create new rich entry using checkpoint's source
                             (assoc t addr {:value new-value
                                            :distribution (:source checkpoint)
                                            :observed? (some? (get-in checkpoint [:options :observe]))}))))
                       trace
                       updates)

        ;; Find earliest modified checkpoint (or first for full replay)
        resume-addr (or (first (filter (set (keys updates)) checkpoint-addrs))
                        (first checkpoint-addrs))

        checkpoint (get checkpoints resume-addr)
        ;; Extract raw value from rich trace entry
        resume-entry (get updated-trace resume-addr)
        resume-value (if (map? resume-entry) (:value resume-entry) resume-entry)]

    (when-not checkpoint
      (throw (ex-info "Cannot resume: no checkpoint found"
                      {:resume-addr resume-addr
                       :available-checkpoints checkpoint-addrs
                       :updates (keys updates)})))

    (log/debug :coordinator/resume-from-checkpoint {:resume-addr resume-addr
                                                    :num-updates (count updates)
                                                    :has-value? (some? resume-value)})

    ;; Reset log-weight (will be recomputed during replay)
    (rtp/swap-state! context [:inference :log-weight] (constantly 0.0))

    ;; Update trace with modifications
    (rtp/swap-state! context [:inference :trace] (constantly updated-trace))

    ;; CRITICAL: Clear all checkpoints EXCEPT the one we're resuming from
    ;; Re-execution will recreate them with fresh continuations
    ;; This prevents "duplicate address" errors during MCMC iteration
    (rtp/swap-state! context [:inference :checkpoints]
                     (fn [chkpts]
                       (select-keys chkpts [resume-addr])))

    ;; CRITICAL: Restore choice-stack to checkpoint state + checkpoint address
    ;; The checkpoint stores the stack BEFORE push, continuation expects AFTER push
    ;; This ensures MCMC re-execution generates same addresses as original run
    (let [checkpoint-stack (or (:choice-stack checkpoint) [])
          restored-stack (conj checkpoint-stack (:address checkpoint))]
      (rtp/swap-state! context [:inference :choice-stack] (constantly restored-stack)))

    ;; Resume from checkpoint with the (possibly modified) value
    (let [{:keys [resolve source options address]} checkpoint
          {:keys [observe]} options
          executor (:executor context)
          ;; Use updated value from trace, or sample fresh if not in trace
          value (or resume-value
                    (if observe observe (ar/sample* source)))]

      ;; For observations, update log-weight
      ;; NOTE: Use (some? observe) not just observe, because observe can be boolean false!
      (when (some? observe)
        (let [log-prob (ar/observe* source observe)]
          (rtp/swap-state! context [:inference :log-weight]
                           (fn [w] (+ (or w 0.0) log-prob)))))

      ;; Resume continuation
      (execute! executor
                (fn []
                  (binding [rtc/*execution-context* context
                            pcps-async/*in-trampoline* false]
                    (spin-core/resume resolve value)))))))

(defn resume-particle-with-value!
  "Resume particle execution from checkpoint with a specific value.

  This is the unified resume function used by all coordinators.
  Updates trace and weight, then resumes the continuation.

  Args:
    context - Particle's execution context
    checkpoint - Checkpoint map with {:resolve :source :options :address}
    value - The value to resume with (sampled or observed)

  Returns: nil (side effect: resumes continuation via scheduler)"
  [context checkpoint value]
  (let [{:keys [resolve source options address]} checkpoint
        {:keys [observe]} options
        executor (:executor context)
        log-prob (ar/observe* source value)]

    (log/debug :coordinator/resume-particle {:address address
                                             :value value
                                             :has-observe? (some? observe)})

    ;; Update trace with rich entry (for MCMC kernel access)
    (rtp/swap-state! context [:inference :trace]
                     (fn [trace]
                       (assoc (or trace {}) address
                              {:value value
                               :distribution source
                               :log-prob log-prob
                               :observed? (some? observe)})))

    ;; For observations, update log-weight
    ;; NOTE: Use (some? observe) not just observe, because observe can be boolean false!
    (when (some? observe)
      (rtp/swap-state! context [:inference :log-weight]
                       (fn [w] (+ (or w 0.0) log-prob))))

    ;; Execute continuation resume on particle's executor
    ;; CRITICAL: Bind *execution-context* so resolve-fn reads updated particle-id
    (execute! executor
              (fn []
                (binding [rtc/*execution-context* context
                          pcps-async/*in-trampoline* false]
                  (spin-core/resume resolve value))))))

;; =============================================================================
;; KernelCoordinator - Generic Kernel-Based Inference
;; =============================================================================
;;
;; This coordinator uses PInferenceKernel to decide values at checkpoints.
;; It supports:
;; - :assign action: Simple forward sampling (like importance sampling)
;; - Barrier synchronization for SMC-style resampling
;; - Future: :modify and :iterate actions for MCMC
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
   ;; PGIBBS/PGAS support
            pgibbs-retained-trace  ; atom: retained trace for PGIBBS/PGAS (nil if not using)
            retained-particle-id   ; atom: particle-id of retained particle
            pgas-ancestor-sampling?] ; boolean: enable ancestor sampling at barriers

  InferenceCoordinator

  (notify-checkpoint! [this particle-id context checkpoint]
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
            (let [{:keys [value]} kernel-result]

              ;; If barrier policy requires waiting at observations
              (if (and (= barrier-policy :every-observe) (some? observe))
                ;; Store state and wait at barrier
                (do
                  (swap! particles assoc particle-id
                         {:context context
                          :checkpoint checkpoint
                          :value value
                          :status :checkpoint
                          :log-weight (rtp/get-state context [:inference :log-weight])
                          :retained? is-retained?})

                  (let [count (swap! barrier-count inc)]
                    (log/debug :kernel-coord/barrier-count {:count count :total total-particles})
                    (when (= count total-particles)
                      ;; All particles at barrier - trigger resample logic
                      (future (trigger-kernel-resample! this)))))

                ;; No barrier - resume immediately
                (resume-particle-with-value! context checkpoint value)))

            ;; Modify existing trace values - replay from earliest modified checkpoint
            :modify
            (let [{:keys [updates]} kernel-result]
              (log/debug :kernel-coord/modify {:particle-id particle-id
                                               :num-updates (count updates)})
              (resume-from-checkpoint! context updates))

            ;; Assign current value, then modify others and replay
            :assign-and-modify
            (let [{:keys [value updates]} kernel-result
                  {:keys [address]} checkpoint]
              (log/debug :kernel-coord/assign-and-modify {:particle-id particle-id
                                                          :address address
                                                          :value value
                                                          :num-updates (count updates)})
              ;; First record current assignment in trace
              (rtp/swap-state! context [:inference :trace]
                               (fn [t] (assoc (or t {}) address value)))
              ;; Then replay from earliest modified
              (resume-from-checkpoint! context updates)))))))

  (notify-complete! [this particle-id context result]
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

              ;; Increment barrier count for completion
              (let [count (swap! barrier-count inc)]
                (log/debug :kernel-coord/completion-count {:count count :total total-particles})
                (when (= count total-particles)
                  (future (trigger-kernel-resample! this)))))

            ;; Iterate - replay from beginning with optional updates
            :iterate
            (let [{:keys [updates]} kernel-result]
              (log/debug :kernel-coord/iterate {:particle-id particle-id
                                                :num-updates (count updates)})
              ;; Clear result since we're re-running
              (rtp/swap-state! context [:inference :result] (constantly nil))
              ;; Resume from checkpoint (empty updates = full replay from first checkpoint)
              (resume-from-checkpoint! context (or updates {}))))))))

  (notify-failed! [_this particle-id context error]
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
        (cancel-particle-worlds! world-manager))))

  (await-completion [_this]
    on-complete))

;; =============================================================================
;; ScoringCoordinator - Lightweight coordinator for PGAS ancestor scoring
;; =============================================================================
;;
;; This coordinator runs particles to completion in forward-sampling mode,
;; using pre-populated trace values. Used by PGAS to compute ancestor weights.

(defrecord ScoringCoordinator
           [retained-trace   ; Map of {address -> trace-entry} for future values
            result-promise   ; Promise to deliver final log-weight
            latch]           ; CountDownLatch to signal completion

  InferenceCoordinator

  (notify-checkpoint! [_this _particle-id context checkpoint]
    ;; Forward sampling: use trace value if available, otherwise sample
    (let [{:keys [address source options]} checkpoint
          {:keys [observe]} options
          trace (or (rtp/get-state context [:inference :trace]) {})

          ;; Check retained trace for pre-populated value
          retained-entry (get retained-trace address)
          retained-value (when retained-entry
                           (if (map? retained-entry)
                             (:value retained-entry)
                             retained-entry))

          ;; Determine value: observe > retained > sample
          value (cond
                  (some? observe) observe
                  (some? retained-value) retained-value
                  :else (ar/sample* source))]

      (log/trace :scoring-coord/checkpoint {:address address :value value :from-retained? (some? retained-value)})

      ;; Resume immediately with value
      (resume-particle-with-value! context checkpoint value)))

  (notify-complete! [_this _particle-id context _result]
    ;; Deliver final log-weight and signal completion
    (let [final-weight (or (rtp/get-state context [:inference :log-weight]) 0.0)]
      (log/debug :scoring-coord/complete {:final-weight final-weight})
      (deliver result-promise final-weight)
      (.countDown latch)))

  (notify-failed! [_this _particle-id _context error]
    ;; Scoring: a failed particle has zero likelihood (log-weight -Inf).
    ;; Deliver the -Inf weight and count down so the outer latch unblocks
    ;; instead of waiting forever for a particle that will never report.
    (log/error :scoring-coord/particle-failed {:error error})
    (deliver result-promise #?(:clj Double/NEGATIVE_INFINITY
                               :cljs js/Number.NEGATIVE_INFINITY))
    (.countDown latch))

  (await-completion [_this]
    ;; Not used for scoring - we use the latch externally
    nil))

(defn create-scoring-coordinator
  "Create a lightweight coordinator for PGAS ancestor scoring.

  Args:
    retained-trace - Map of future trace values
    result-promise - Promise to deliver final log-weight
    latch - CountDownLatch to signal completion

  Returns: ScoringCoordinator instance"
  [retained-trace result-promise latch]
  (->ScoringCoordinator retained-trace result-promise latch))

;; =============================================================================
;; PGAS Ancestor Sampling via Continuation Re-execution
;; =============================================================================

(defn run-ancestor-scoring-particles!
  "Fork each particle and run forward using retained trace to compute ancestor weights.

  For PGAS, we need to evaluate: p(retained_future | particle_i_state).
  This is done by:
  1. Fork each particle at the current barrier
  2. Install a ScoringCoordinator that uses retained trace values
  3. Resume each fork from its checkpoint
  4. ScoringCoordinator delivers final log-weights when particles complete

  Args:
    particles-state - Map of particle states at barrier
    retained-trace - Full retained trace
    executor - Executor for running scoring particles

  Returns: Vector of ancestor log-weights (one per particle)"
  [particles-state retained-trace executor]
  (let [particle-vec (vec (vals particles-state))
        n (count particle-vec)
        ;; Shared latch for all scoring particles
        scoring-complete (java.util.concurrent.CountDownLatch. n)
        ;; Individual promises for each particle's result
        result-promises (vec (repeatedly n promise))]

    (log/debug :pgas/start-ancestor-scoring {:n-particles n})

    ;; Fork and run each particle with its own ScoringCoordinator
    (doseq [[idx p] (map-indexed vector particle-vec)]
      (let [ctx (:context p)
            checkpoint (:checkpoint p)
            value (:value p)

            ;; Fork the context
            forked-ctx (fork-particle-context ctx)

            ;; Create ScoringCoordinator for this particle
            scoring-coord (create-scoring-coordinator
                           retained-trace
                           (nth result-promises idx)
                           scoring-complete)]

        ;; Reset log-weight to 0 for scoring (we'll recompute from current point)
        (rtp/swap-state! forked-ctx [:inference :log-weight] (constantly 0.0))

        ;; Install ScoringCoordinator - this handles checkpoints and completion
        (rtp/swap-state! forked-ctx [:inference :inference-coordinator] (constantly scoring-coord))

        ;; Clear checkpoints to avoid duplicate address detection
        (rtp/swap-state! forked-ctx [:inference :checkpoints] (constantly {}))

        ;; Resume from checkpoint - ScoringCoordinator will handle the rest
        (execute! executor
                  (fn []
                    (binding [rtc/*execution-context* forked-ctx
                              pcps-async/*in-trampoline* false]
                      (try
                        (spin-core/resume (:resolve checkpoint) value)
                        (catch #?(:clj Throwable :cljs :default) t
                          (log/error :pgas/scoring-error {:idx idx :error (str t)})
                  ;; On error, deliver -Infinity and countdown
                          (deliver (nth result-promises idx) #?(:clj Double/NEGATIVE_INFINITY :cljs js/Number.NEGATIVE_INFINITY))
                          (.countDown scoring-complete))))))))

    ;; Wait for all scoring particles to complete (with timeout)
    (let [timeout-ms 30000
          completed? (.await scoring-complete timeout-ms java.util.concurrent.TimeUnit/MILLISECONDS)]
      (if completed?
        ;; Collect weights
        (let [weights (mapv (fn [p] (or (deref p 100 #?(:clj Double/NEGATIVE_INFINITY :cljs js/Number.NEGATIVE_INFINITY))
                                        #?(:clj Double/NEGATIVE_INFINITY :cljs js/Number.NEGATIVE_INFINITY)))
                            result-promises)]
          (log/debug :pgas/ancestor-scoring-complete {:weights weights})
          weights)
        ;; Timeout - use current weights
        (do
          (log/warn :pgas/ancestor-scoring-timeout)
          (mapv (comp #(or % 0.0) :log-weight) particle-vec))))))

(defn perform-ancestor-sampling
  "Perform PGAS ancestor sampling using re-execution from checkpoints.

  At each barrier:
  1. Fork each particle and run forward with retained trace values
  2. Compute ancestor weights from scoring particles' final log-weights
  3. Sample ancestor index proportionally

  Args:
    particles-state - Map of particle states at barrier
    retained-trace - Full retained trace
    executor - Executor for scoring particles

  Returns: Index of selected ancestor in particles-state order"
  [particles-state retained-trace executor]
  (let [particle-vec (vec (vals particles-state))
        n (count particle-vec)

        ;; Run scoring particles to get ancestor weights
        ancestor-log-weights (run-ancestor-scoring-particles! particles-state retained-trace executor)

        ;; Add current particle weights (weight up to barrier + weight from scoring)
        combined-weights (mapv (fn [p score-w]
                                 (+ (or (:log-weight p) 0.0) (or score-w 0.0)))
                               particle-vec
                               ancestor-log-weights)

        ;; Normalize and sample
        max-lw (if (empty? combined-weights) 0.0 (apply max combined-weights))
        weights (mapv #(Math/exp (- % max-lw)) combined-weights)
        total-w (reduce + weights)
        norm-weights (if (> total-w 0)
                       (mapv #(/ % total-w) weights)
                       (vec (repeat n (/ 1.0 n))))  ; Uniform if all weights are 0

        ;; Sample ancestor index
        u (rand)
        ancestor-idx (loop [i 0 cumsum 0.0]
                       (if (>= i n)
                         (dec n)
                         (let [cumsum' (+ cumsum (nth norm-weights i))]
                           (if (< u cumsum')
                             i
                             (recur (inc i) cumsum')))))]

    (log/debug :pgas/ancestor-sampled {:ancestor-idx ancestor-idx
                                       :combined-weights combined-weights
                                       :norm-weights norm-weights})

    ancestor-idx))

;; =============================================================================
;; Kernel Coordinator Resample Logic
;; =============================================================================

(defn- resume-resampled-contexts!
  [coordinator particles-state particles-ordered should-resample?
   is-pgibbs? is-pgas? ancestor-idx contexts-with-checkpoints]
  (when-let [manager (:world-manager coordinator)]
    (register-particle-contexts! manager (mapv :context contexts-with-checkpoints)))
  ;; Reset weights if we resampled.
  (when should-resample?
    (doseq [{:keys [context]} contexts-with-checkpoints]
      (rtp/swap-state! context [:inference :log-weight] (constantly 0.0))))

  (reset! (:particles coordinator) {})
  (reset! (:barrier-count coordinator) 0)

  (let [retained-pid @(:retained-particle-id coordinator)
        effective-retained-idx
        (if (and is-pgas? ancestor-idx)
          ancestor-idx
          (when is-pgibbs?
            (first
             (keep-indexed
              (fn [i p] (when (= (first p) retained-pid) i))
              particles-state))))
        new-retained-pid
        (when effective-retained-idx
          (some->> contexts-with-checkpoints
                   (filter #(= (:original-idx %) effective-retained-idx))
                   first
                   :particle-id))]

    (log/debug :kernel-coord/retained-tracking
               {:is-pgas? is-pgas?
                :ancestor-idx ancestor-idx
                :effective-retained-idx effective-retained-idx
                :new-retained-pid new-retained-pid})

    (when (and is-pgibbs? new-retained-pid)
      (reset! (:retained-particle-id coordinator) new-retained-pid))

    (doseq [{:keys [context checkpoint particle-id original-idx world]}
            contexts-with-checkpoints]
      (let [orig-state (nth particles-ordered original-idx)
            value (:value orig-state)
            is-new-retained? (and is-pgibbs?
                                  (= particle-id new-retained-pid))]
        (rtp/swap-state! context [:inference :particle-id]
                         (constantly particle-id))
        (rtp/swap-state! context [:inference :sweep]
                         (constantly @(:current-sweep coordinator)))
        (when world
          (rtp/swap-state! context [:inference :world]
                           (constantly world)))
        (swap! (:particles coordinator) assoc particle-id
               {:context context
                :world world
                :status :running
                :retained? is-new-retained?})
        (resume-particle-with-value! context checkpoint value)))))

(def ^:private projected-inference-keys
  #{:log-weight :choice-stack :trace :particle-id :sweep :result
    :deterministic :interventions :mcmc :rw-mcmc :block-gibbs})

(defn- project-settled-particle-context
  "Create a parentless immutable posterior context. Returning the settled
  execution context itself would retain its complete resampling ancestry."
  [context]
  (let [inference-state (rtp/get-state context [:inference])
        projected (cond-> (select-keys inference-state
                                       projected-inference-keys)
                    (:world inference-state)
                    (assoc :world-descriptor
                           (ygg/fork-descriptor (:world inference-state))))]
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
  "Trigger barrier processing for KernelCoordinator.

  Called when all particles reach a barrier (checkpoint or completion).
  Performs ESS-based resampling if needed, then resumes particles.

  PGIBBS mode: If pgibbs-retained-trace is set, the retained particle
  follows its fixed trace at sample sites.

  PGAS mode: If pgas-ancestor-sampling? is true, performs ancestor sampling
  at each barrier to select which particle's history the retained particle adopts."
  [coordinator]
  (swap! (:current-sweep coordinator) inc)

  (let [particles-state @(:particles coordinator)
        statuses (map (comp :status val) particles-state)
        all-checkpoint? (every? #(= :checkpoint %) statuses)
        all-complete? (every? #(= :complete %) statuses)
        is-pgibbs? (some? @(:pgibbs-retained-trace coordinator))
        is-pgas? (and is-pgibbs? (:pgas-ancestor-sampling? coordinator))]

    (log/debug :kernel-coord/trigger-resample {:sweep @(:current-sweep coordinator)
                                               :all-checkpoint? all-checkpoint?
                                               :all-complete? all-complete?
                                               :is-pgibbs? is-pgibbs?
                                               :is-pgas? is-pgas?})

    (cond
      ;; All particles hit checkpoint - resample and continue
      all-checkpoint?
      (let [;; PGAS: Perform ancestor sampling to select retained particle's ancestor
            ;; This determines which particle's history the retained particle adopts
            ancestor-idx (when is-pgas?
                           (let [retained-trace @(:pgibbs-retained-trace coordinator)
                                 executor (:executor (:parent-runtime coordinator))]
                             (perform-ancestor-sampling particles-state retained-trace executor)))

            _ (when ancestor-idx
                (log/debug :pgas/selected-ancestor {:ancestor-idx ancestor-idx}))

            ;; Standard SMC processing
            contexts (mapv (comp :context val) particles-state)
            log-weights (mapv (comp :log-weight val) particles-state)

            measure (m/empirical (mapv vector contexts log-weights))

            ;; Calculate ESS
            ess (m/effective-sample-size measure)
            n (:total-particles coordinator)

            _ (log/debug :kernel-coord/checkpoint-reached {:ess ess
                                                           :threshold (* (:resample-threshold coordinator) n)
                                                           :is-pgibbs? is-pgibbs?})

            ;; Resample if ESS < threshold
            should-resample? (< ess (* (:resample-threshold coordinator) n))

            resampled-contexts
            (if should-resample?
              (let [weights (m/normalize-log-weights log-weights)
                    indices (m/systematic-resample weights n)]
                (mapv #(nth contexts %) indices))
              contexts)

            ;; Pair with original checkpoints and fork
            particles-ordered (vec (vals particles-state))
            original-contexts-ordered (mapv :context particles-ordered)
            continue!
            (fn [contexts-with-checkpoints]
              (resume-resampled-contexts!
               coordinator particles-state particles-ordered should-resample?
               is-pgibbs? is-pgas? ancestor-idx contexts-with-checkpoints))]

        (if-let [manager (:world-manager coordinator)]
          (pair-world-checkpoints!
           manager resampled-contexts original-contexts-ordered particles-state
           continue!
           (fn [fork-error]
             ;; Source particles are suspended, not terminal: structured
             ;; cancellation must unwind their parked continuations and user
             ;; finally blocks before automatic quiescent cleanup consumes the
             ;; source and partially constructed child worlds.
             (notify-failed! coordinator :particle-world
                             (:parent-runtime coordinator) fork-error)))
          (continue!
           (pair-checkpoints resampled-contexts
                             original-contexts-ordered
                             particles-state))))

      ;; All particles completed - deliver final result
      all-complete?
      (when (compare-and-set! (:delivered? coordinator) false true)
        (let [final-particles (vals particles-state)
              contexts (mapv :context final-particles)
              log-weights (mapv :log-weight final-particles)
              legacy-measure (when-not (:world-manager coordinator)
                               (m/empirical
                                (mapv vector contexts log-weights)))]

          (log/debug :kernel-coord/all-complete {:num-sweeps @(:current-sweep coordinator)
                                                 :num-particles (count contexts)})
          (let [deliver!
                (fn [value]
                  (binding [rtc/*execution-context*
                            (:parent-runtime coordinator)]
                    (sync/deliver! (:on-complete coordinator) value)))]
            (if-let [manager (:world-manager coordinator)]
              (invoke-result!
               (discard-particle-worlds! manager)
               (fn [_]
                 (deliver!
                  (m/empirical
                   (mapv vector
                         (mapv project-settled-particle-context contexts)
                         log-weights))))
               (fn [error]
                 (deliver! (->InferenceFailure :particle-world-cleanup
                                               error))))
              (deliver! legacy-measure)))))

      ;; Mixed state
      :else
      (throw (ex-info "KernelCoordinator: Mixed particle states"
                      {:checkpoint-count (count (filter #(= :checkpoint %) statuses))
                       :complete-count (count (filter #(= :complete %) statuses))})))))

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
      :pgibbs-retained-trace - Retained trace for PGIBBS/PGAS (nil for standard SMC)
      :pgas-ancestor-sampling? - Enable ancestor sampling at barriers (default false)

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
    ;; PGIBBS/PGAS fields
   (atom (:pgibbs-retained-trace opts))             ; pgibbs-retained-trace
   (atom nil)                                       ; retained-particle-id (set by first particle)
   (:pgas-ancestor-sampling? opts false)))          ; pgas-ancestor-sampling?
