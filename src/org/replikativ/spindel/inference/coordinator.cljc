(ns org.replikativ.spindel.inference.coordinator
  "Generic inference coordination protocol and KernelCoordinator implementation.

  The InferenceCoordinator protocol enables reactive coordination across
  multiple particle/chain execution contexts. KernelCoordinator is the unified
  coordinator that uses PInferenceKernel to control checkpoint behavior:

  - :barrier-policy :every-observe -> SMC-style resampling at observe sites
  - :barrier-policy :none -> Importance sampling (no barriers)

  Effect handlers (sample, observe) are algorithm-agnostic and work with
  KernelCoordinator via the InferenceCoordinator protocol.

  See KERNEL_INFERENCE_DESIGN.md for the full architecture."
  (:require [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as rtc]
            [org.replikativ.spindel.engine.executor :refer [execute!]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
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
;; See KERNEL_INFERENCE_DESIGN.md for full architecture.

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
    ;; Fail fast: deliver an InferenceFailure marker to on-complete once.
    ;; kernel-infer awaits this Deferred and re-throws on the marker.
    ;; Without this, the still-running particles (if any) never let
    ;; barrier-count reach total-particles, so on-complete is never
    ;; delivered and (await (await-completion …)) waits forever.
    (when (compare-and-set! delivered? false true)
      (binding [rtc/*execution-context* parent-runtime]
        (sync/deliver! on-complete (->InferenceFailure particle-id error)))))

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

            contexts-with-checkpoints (pair-checkpoints resampled-contexts
                                                        original-contexts-ordered
                                                        particles-state)]

        ;; Reset weights if we resampled
        (when should-resample?
          (doseq [{:keys [context]} contexts-with-checkpoints]
            (rtp/swap-state! context [:inference :log-weight] (constantly 0.0))))

        ;; Update coordinator state
        (reset! (:particles coordinator) {})
        (reset! (:barrier-count coordinator) 0)

        ;; Resume all particles with their assigned values
        ;; particles-ordered is in the SAME order as original-contexts-ordered
        (let [;; For PGIBBS: find which particle inherited the retained trace
              ;; by checking which resampled context came from the original retained particle
              retained-pid @(:retained-particle-id coordinator)

              ;; PGAS: In PGAS mode, ancestor-idx determines which particle's history
              ;; the retained particle adopts. Use that index directly.
              ;; PGIBBS: Use the original retained particle index.
              effective-retained-idx (if (and is-pgas? ancestor-idx)
                                      ancestor-idx
                                      (when is-pgibbs?
                                        (first (keep-indexed
                                                (fn [i p] (when (= (first p) retained-pid) i))
                                                particles-state))))

              ;; Find which new particle inherits from the retained/ancestor source
              new-retained-pid (when effective-retained-idx
                                (let [matches (filter #(= (:original-idx %) effective-retained-idx)
                                                     contexts-with-checkpoints)]
                                  (when (seq matches)
                                    (:particle-id (first matches)))))]

          (log/debug :kernel-coord/retained-tracking {:is-pgas? is-pgas?
                              :ancestor-idx ancestor-idx
                              :effective-retained-idx effective-retained-idx
                              :new-retained-pid new-retained-pid})

          ;; Update retained particle ID for next barrier
          (when (and is-pgibbs? new-retained-pid)
            (reset! (:retained-particle-id coordinator) new-retained-pid))

          (doseq [{:keys [context checkpoint particle-id original-idx]} contexts-with-checkpoints]
            ;; Get the value that was assigned by the kernel (from original particle state)
            ;; original-idx indexes into particles-ordered (same order as original-contexts-ordered)
            (let [orig-state (nth particles-ordered original-idx)
                  value (:value orig-state)
                  is-new-retained? (and is-pgibbs? (= particle-id new-retained-pid))]

              ;; Update particle-id and sweep in forked context
              (rtp/swap-state! context [:inference :particle-id] (constantly particle-id))
              (rtp/swap-state! context [:inference :sweep] (constantly @(:current-sweep coordinator)))

              ;; Register forked particle
              (swap! (:particles coordinator) assoc particle-id
                     {:context context :status :running :retained? is-new-retained?})

              ;; Resume with the value from kernel step
              (resume-particle-with-value! context checkpoint value)))))

      ;; All particles completed - deliver final result
      all-complete?
      (when (compare-and-set! (:delivered? coordinator) false true)
        (let [final-particles (vals particles-state)
              contexts (mapv :context final-particles)
              log-weights (mapv :log-weight final-particles)
              final-measure (m/empirical (mapv vector contexts log-weights))]

          (log/debug :kernel-coord/all-complete {:num-sweeps @(:current-sweep coordinator)
                              :num-particles (count contexts)})

          (binding [rtc/*execution-context* (:parent-runtime coordinator)]
            (sync/deliver! (:on-complete coordinator) final-measure))))

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
    ;; PGIBBS/PGAS fields
    (atom (:pgibbs-retained-trace opts))             ; pgibbs-retained-trace
    (atom nil)                                       ; retained-particle-id (set by first particle)
    (:pgas-ancestor-sampling? opts false)))          ; pgas-ancestor-sampling?
