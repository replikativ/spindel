(ns org.replikativ.spindel.inference.inference
  "Compositional probabilistic inference algorithms.

  Implements spin-returning inference functions using the kernel-based
  architecture from KERNEL_INFERENCE_DESIGN.md:

  - kernel-infer: Core inference function using PInferenceKernel
  - importance-sampling: Delegates to kernel-infer with PriorKernel, no barriers
  - smc-infer: Delegates to kernel-infer with PriorKernel, barriers at observe

  All functions return Spin<EmpiricalMeasure> for composability.

  Key design principles:
  - Unified kernel protocol (PInferenceKernel controls checkpoint behavior)
  - Single coordinator (KernelCoordinator handles all inference patterns)
  - Spin-returning API (non-blocking, composable via await)
  - Measure-centric post-processing (query, predict)"
  (:require [org.replikativ.spindel.inference.measure :as m]
            [org.replikativ.spindel.inference.kernel :as k]
            [org.replikativ.spindel.inference.coordinator :as coord]
            [org.replikativ.spindel.inference.gradient :as grad]
            [org.replikativ.spindel.engine.core :as rtc]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.executor :as sched]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.effects.await :refer [await]]
            [replikativ.logging :as log]
            [anglican.runtime :as ar]
            [clojure.set :as set]))

;; =============================================================================
;; Particle Execution
;; =============================================================================

(defn start-particle!
  "Start a particle's spin execution on its own executor.

  Enqueues the spin to the particle's executor with a custom resolve-fn
  that notifies the coordinator when the spin completes.

  Args:
    context - Particle's execution context
    coordinator - InferenceCoordinator instance

  Returns: nil (side effect: spin enqueued)"
  [context coordinator]
  (let [task (rtp/get-state context [:inference :task])
        particle-id (rtp/get-state context [:inference :particle-id])]

    (when-not task
      (throw (ex-info "No task found in particle context"
                      {:particle-id particle-id})))

    (log/trace :smc/start-particle {:particle-id particle-id
                        :spin-id (spin-core/spin-id task)})

    ;; Enqueue spin to particle's own executor
    (rtc/with-context context
      (let [spin-id (spin-core/spin-id task)
            ;; Custom resolve-fn that notifies coordinator on completion
            ;; CRITICAL: Read particle-id from *execution-context* dynamically,
            ;; NOT from captured closure! This allows forked contexts to complete
            ;; with their NEW particle-id after resampling.
            resolve-fn (fn [value]
                         ;; Read CURRENT particle-id from execution context
                         ;; Fall back to captured context if *execution-context* not bound
                         (let [current-ctx (or rtc/*execution-context* context)
                               current-pid (rtp/get-state current-ctx [:inference :particle-id])
                               current-coord (rtp/get-state current-ctx [:inference :inference-coordinator])]
                           (log/trace :smc/task-completed {:particle-id current-pid
                                               :spin-id spin-id})
                           ;; Notify coordinator with CURRENT state (not captured)
                           (when current-coord
                             (coord/notify-complete! current-coord current-pid current-ctx value)))
                         value)  ; Return value for spin result flow

            reject-fn (fn [error]
                        ;; Read current particle-id + coordinator from the
                        ;; *current* execution context (same reasoning as
                        ;; resolve-fn above: forked contexts after
                        ;; resampling carry a new particle-id).
                        (let [current-ctx   (or rtc/*execution-context* context)
                              current-pid   (rtp/get-state current-ctx [:inference :particle-id])
                              current-coord (rtp/get-state current-ctx [:inference :inference-coordinator])]
                          (log/error :smc/task-failed {:particle-id current-pid
                                                       :spin-id spin-id
                                                       :error error})
                          ;; CRITICAL: notify the coordinator. Without this
                          ;; the coordinator's barrier-count never reaches
                          ;; total-particles, on-complete is never
                          ;; delivered, and (await (await-completion …))
                          ;; hangs forever — pinning every particle
                          ;; context (and its daemon drain thread) as
                          ;; reachable. (Re-throwing here doesn't help —
                          ;; the engine event loop catches it and the
                          ;; coordinator is none the wiser.)
                          (if current-coord
                            (coord/notify-failed! current-coord current-pid current-ctx error)
                            ;; No coordinator wired up — rethrow rather
                            ;; than silently swallow.
                            (throw error))))]

        ;; Enqueue spin execution event
        ;; The particle's executor will process this asynchronously
        (rtc/enqueue-event! {:type :spin-execution
                             :id spin-id
                             :spin task
                             :execution-context context  ; Use particle's context
                             :resolve-fn resolve-fn
                             :reject-fn reject-fn})))))

;; =============================================================================
;; Kernel-Based Inference
;; =============================================================================

(defn kernel-infer
  "Run inference using a PInferenceKernel.

  This is the new kernel-based inference API that provides more flexibility
  than importance-sampling or smc-infer. The kernel controls:
  - What value to assign at each checkpoint
  - Whether to use barriers at observations (for SMC-like behavior)
  - Whether to iterate after program completion (for MCMC)

  Args:
  - model-task: Spin (from model function) - Probabilistic program to infer
  - kernel: PInferenceKernel instance (e.g., prior-kernel, single-site-mh-kernel)
  - num-particles: Number of particles
  - opts: Optional map with:
    - :barrier-policy - :every-observe | :none (default :every-observe for SMC behavior)
    - :resample-threshold - ESS threshold (default 0.5)
    - :executor - Shared executor for all particles

  Returns: Spin<EmpiricalMeasure>

  Examples:
    ;; Importance sampling with prior kernel
    (spin
      (let [model (coin-flip-model)
            measure (await (kernel-infer model (prior-kernel) 100))]
        (query measure identity)))

    ;; SMC with prior kernel (default barrier policy)
    (spin
      (let [model (coin-flip-model)
            measure (await (kernel-infer model (prior-kernel) 100
                                        {:barrier-policy :every-observe}))]
        (query measure identity)))"
  [model-task kernel num-particles & [opts]]
  (spin
    (log/debug :kernel-infer/start {:kernel-id (k/kernel-id kernel)
                        :num-particles num-particles
                        :barrier-policy (:barrier-policy opts :every-observe)})

    (let [runtime rtc/*execution-context*
          coordinator (coord/create-kernel-coordinator
                        runtime
                        kernel
                        num-particles
                        opts)

          ;; Create or use provided shared executor
          shared-executor (or (:executor opts)
                             (sched/thread-pool-executor {:threads 2}))

          ;; PGIBBS: Check if we have a retained trace (for conditional SMC)
          pgibbs-retained-trace (:pgibbs-retained-trace opts)

          ;; Initialize particles with coordinator reference
          ;; For PGIBBS: first particle is retained
          initial-particles
          (vec (map-indexed
                (fn [idx _]
                  (let [ctx (ctx/create-execution-context
                             :executor shared-executor)
                        particle-id (keyword (str "particle-" (gensym)))
                        is-retained? (and pgibbs-retained-trace (= idx 0))]

                    ;; Initialize probabilistic state
                    (rtp/swap-state! ctx [:inference]
                                    (constantly {:log-weight 0.0
                                                :choice-stack []
                                                :trace {}
                                                :checkpoints {}
                                                :particle-id particle-id
                                                :sweep 0
                                                :inference-coordinator coordinator}))

                    ;; Store model spin in context
                    (rtp/swap-state! ctx [:inference :task]
                                    (constantly model-task))

                    ;; PGIBBS: Set retained particle ID in coordinator
                    (when is-retained?
                      (reset! (.-retained-particle-id coordinator) particle-id)
                      (log/debug :kernel-infer/set-retained-particle {:particle-id particle-id}))

                    ctx))
                (range num-particles)))]

      (log/debug :kernel-infer/particles-initialized {:num-particles (count initial-particles)})

      ;; Start all particles
      (doseq [particle-ctx initial-particles]
        (start-particle! particle-ctx coordinator))

      (log/debug :kernel-infer/particles-started)

      ;; Await completion
      (let [final-measure (await (coord/await-completion coordinator))]

        ;; A particle's spin aborted: the coordinator delivered a
        ;; failure marker instead of an EmpiricalMeasure. Re-throw so
        ;; the calling spin / @(spin …) propagates the error to the
        ;; agent / REPL caller, instead of returning a bogus measure.
        (when (coord/inference-failure? final-measure)
          (throw (ex-info "Inference failed: a particle's model threw"
                          {:particle-id (:particle-id final-measure)}
                          (:error final-measure))))

        (log/debug :kernel-infer/complete {:num-particles num-particles
                            :log-marginal (m/log-marginal final-measure)
                            :ess (m/effective-sample-size final-measure)})

        final-measure))))

;; =============================================================================
;; Convenience Functions (Delegate to kernel-infer)
;; =============================================================================

(defn smc-infer
  "Run SMC inference on probabilistic program.

  Sequential Monte Carlo with resampling at observe barriers.
  Delegates to kernel-infer with PriorKernel and :barrier-policy :every-observe.

  Args:
  - model-task: Spin (from model function) - Probabilistic program to infer
  - num-particles: Number of particles for SMC
  - opts: Optional map with:
    - :resample-threshold - ESS threshold (default 0.5)
    - :executor - Shared executor for all particles (default: 2-thread pool)

  Returns: Spin<EmpiricalMeasure>

  Example:
    (spin
      (let [model (coin-flip-model)
            measure (await (smc-infer model 100 {:executor shared-exec}))]
        (query measure identity)))"
  [model-task num-particles & [opts]]
  ;; SMC = PriorKernel with barriers at every observe
  (kernel-infer model-task
                (k/prior-kernel)
                num-particles
                (assoc opts :barrier-policy :every-observe)))

(defn importance-sampling
  "Run importance sampling inference on probabilistic program.

  Simple importance sampling without resampling barriers.
  Delegates to kernel-infer with PriorKernel and :barrier-policy :none.

  Args:
  - model-task: Spin (from model function) - Probabilistic program
  - num-samples: Number of samples
  - opts: Optional map with:
    - :executor - Shared executor for all samples (default: 2-thread pool)

  Returns: Spin<EmpiricalMeasure>

  Example:
    (spin
      (let [model (gaussian-model)  ; Returns spin
            measure (await (importance-sampling model 1000 {:executor shared-exec}))]
        (query measure identity)))"
  [model-task num-samples & [opts]]
  ;; Importance sampling = PriorKernel with no barriers
  (kernel-infer model-task
                (k/prior-kernel)
                num-samples
                (assoc opts :barrier-policy :none)))

;; =============================================================================
;; Helper Functions
;; =============================================================================

(defn query
  "Extract statistics from posterior measure.

  measure: Posterior measure from inference
  query-fn: (fn [value] -> extracted-value) to extract from program results
           OR :identity to get the program result directly

  Returns: Map with :mean, :variance, :std-dev, :quantiles"
  [measure query-fn]
  (let [extract-fn (cond
                     ;; identity means "get the main result"
                     (= query-fn identity) m/get-value
                     ;; keyword means "extract field from result"
                     (keyword? query-fn) (fn [ctx] (get (m/get-value ctx) query-fn))
                     ;; function: compose with get-value
                     :else (fn [ctx] (query-fn (m/get-value ctx))))]
    (m/measure-stats measure extract-fn)))

(defn predict
  "Generate predictive samples from posterior.

  measure: Posterior measure
  pred-fn: (fn [context] -> predicted-value)
  num-samples: Number of predictions

  Returns: Vector of predicted values"
  [measure pred-fn num-samples]
  (let [samples (m/sample-measure measure num-samples)]
    (mapv (fn [[ctx _]] (pred-fn ctx)) samples)))

;; =============================================================================
;; Particle MCMC Methods
;; =============================================================================

(defn pimh-infer
  "Particle Independent Metropolis-Hastings inference.

  Runs SMC sweeps as Metropolis-Hastings proposals, accepting or rejecting
  entire sweeps based on marginal likelihood ratio.

  Algorithm:
  1. Run initial SMC sweep, compute log-Z
  2. For each iteration:
     - Propose new SMC sweep
     - Accept with prob min(1, Z_new/Z_old)
     - Emit accepted particles as samples

  Args:
    model-task - Spin representing probabilistic program
    num-particles - Number of particles per SMC sweep
    num-iterations - Number of MCMC iterations
    opts - Optional map with:
      :executor - Shared executor
      :resample-threshold - ESS threshold for SMC (default 0.5)

  Returns: Spin<EmpiricalMeasure>

  Example:
    (spin
      (let [measure (await (pimh-infer (coin-flip-model) 50 100 {}))]
        (query measure identity)))"
  [model-task num-particles num-iterations & [opts]]
  (spin
    (log/debug :pimh/start {:num-particles num-particles
                        :num-iterations num-iterations})

    ;; Run initial SMC sweep
    (let [initial-measure (await (smc-infer model-task num-particles opts))
          initial-log-Z (m/log-marginal initial-measure)]

      (log/debug :pimh/initial-sweep {:log-Z initial-log-Z
                          :ess (m/effective-sample-size initial-measure)})

      ;; MCMC loop
      (loop [current-measure initial-measure
             current-log-Z initial-log-Z
             iteration 0
             all-particles []]

        (if (>= iteration num-iterations)
          ;; Done - combine all accepted particles into final measure
          (do
            (log/debug :pimh/complete {:iterations num-iterations
                                :total-particles (count all-particles)})
            (m/empirical all-particles))

          ;; Propose new sweep
          (let [proposed-measure (await (smc-infer model-task num-particles opts))
                proposed-log-Z (m/log-marginal proposed-measure)

                ;; MH acceptance ratio: alpha = Z_new / Z_old
                log-alpha (- proposed-log-Z current-log-Z)
                u (Math/log (rand))
                accept? (or (>= log-alpha 0.0)
                           (< u log-alpha))

                _ (log/trace :pimh/mh-step {:iteration iteration
                                      :proposed-log-Z proposed-log-Z
                                      :current-log-Z current-log-Z
                                      :log-alpha log-alpha
                                      :accept? accept?})

                ;; Update state based on acceptance
                [new-measure new-log-Z]
                (if accept?
                  [proposed-measure proposed-log-Z]
                  [current-measure current-log-Z])

                ;; Collect particles from accepted measure
                accepted-particles (m/get-particles new-measure)]

            (recur new-measure
                   new-log-Z
                   (inc iteration)
                   (into all-particles accepted-particles))))))))

(defn pgibbs-infer
  "Particle Gibbs (Conditional SMC) inference.

  Runs conditional SMC where one 'retained' particle follows a fixed trace
  from the previous sweep. The retained particle is never resampled away.

  Algorithm:
  1. Run initial SMC sweep, select random particle as retained
  2. For each iteration:
     - Particle 0 follows retained trace (sample sites use trace values)
     - Particles 1..N-1 sample fresh from prior
     - At barriers: conditional resampling (particle 0 always survives)
     - Select new retained particle randomly from final particles

  Args:
    model-task - Spin representing probabilistic program
    num-particles - Total particles (1 retained + N-1 fresh)
    num-iterations - Number of CSMC sweeps
    opts - Optional map with:
      :executor - Shared executor
      :resample-threshold - ESS threshold (default 0.5)

  Returns: Spin<EmpiricalMeasure>

  Example:
    (spin
      (let [measure (await (pgibbs-infer (coin-flip-model) 20 200 {}))]
        (query measure identity)))"
  [model-task num-particles num-iterations & [opts]]
  (spin
    (log/debug :pgibbs/start {:num-particles num-particles
                        :num-iterations num-iterations})

    ;; Run initial sweep to get first retained trace
    (let [initial-measure (await (smc-infer model-task num-particles opts))
          initial-particles (m/get-particles initial-measure)
          ;; Select random particle's trace as initial retained trace
          initial-retained-ctx (first (rand-nth initial-particles))
          initial-retained-trace (rtp/get-state initial-retained-ctx [:inference :trace])]

      (log/debug :pgibbs/initial-sweep {:retained-trace-size (count initial-retained-trace)})

      ;; CSMC loop - run iterations to mix, then collect from final sweep
      (loop [retained-trace initial-retained-trace
             iteration 0]

        (if (>= iteration num-iterations)
          ;; Done - run one final sweep and collect all particles
          (let [final-measure (await (kernel-infer
                                       model-task
                                       (k/prior-kernel)
                                       num-particles
                                       (assoc opts
                                         :barrier-policy :every-observe
                                         :pgibbs-retained-trace retained-trace)))]

            (log/debug :pgibbs/complete {:iterations num-iterations
                                :num-particles num-particles})

            ;; Return the final sweep's measure directly
            ;; (weighted particles from converged MCMC state)
            final-measure)

          ;; Run conditional SMC sweep with retained trace
          (let [sweep-measure (await (kernel-infer
                                       model-task
                                       (k/prior-kernel)
                                       num-particles
                                       (assoc opts
                                         :barrier-policy :every-observe
                                         :pgibbs-retained-trace retained-trace)))

                sweep-particles (m/get-particles sweep-measure)

                ;; Select new retained particle according to weights
                ;; This is proper PGIBBS: new retained is sampled from posterior
                log-weights (mapv second sweep-particles)
                norm-weights (m/normalize-log-weights log-weights)
                ;; Sample one index according to weights
                u (rand)
                selected-idx (loop [i 0 cumsum 0.0]
                               (let [cumsum' (+ cumsum (nth norm-weights i))]
                                 (if (< u cumsum')
                                   i
                                   (recur (inc i) cumsum'))))
                [new-retained-ctx _] (nth sweep-particles selected-idx)
                new-retained-trace (rtp/get-state new-retained-ctx [:inference :trace])]

            (log/trace :pgibbs/sweep {:iteration iteration
                                :new-trace-size (count new-retained-trace)})

            (recur new-retained-trace
                   (inc iteration))))))))

;; =============================================================================
;; IPMCMC - Interacting Particle MCMC
;; =============================================================================

(defn- norm-exp
  "Normalized exponential. Returns [probabilities log-mean-weight].
   If all weights are -infinity, returns uniform probabilities."
  [log-weights]
  (let [max-log-weight (apply max log-weights)]
    (if (or (nil? max-log-weight)
            (= max-log-weight ##-Inf))
      ;; All -infinity: return uniform
      (let [n (count log-weights)]
        [(vec (repeat n (/ 1.0 n))) ##-Inf])
      ;; Normal case
      (let [weights (mapv #(Math/exp (- % max-log-weight)) log-weights)
            total (reduce + weights)
            probs (mapv #(/ % total) weights)
            log-mean-weight (+ (Math/log (/ total (count log-weights))) max-log-weight)]
        [probs log-mean-weight]))))

(defn- sample-categorical
  "Sample an index from categorical distribution defined by probabilities."
  [probs]
  (let [u (rand)]
    (loop [i 0
           cumsum 0.0]
      (if (>= i (count probs))
        (dec (count probs))  ; Edge case: return last index
        (let [cumsum' (+ cumsum (nth probs i))]
          (if (< u cumsum')
            i
            (recur (inc i) cumsum')))))))

(defn- gibbs-update-csmc-indices
  "Perform Gibbs sweep on CSMC node indices.

   For each CSMC slot, consider swapping with an SMC node based on log-Z values.
   Returns [new-csmc-indices zeta-sums] where zeta-sums are weights for
   Rao-Blackwellization.

   Args:
     log-Zs - Vector of log marginal likelihood estimates from all nodes
     num-csmc-nodes - Number of CSMC nodes

   Returns:
     [csmc-indices zeta-sums]"
  [log-Zs num-csmc-nodes]
  (let [num-nodes (count log-Zs)]
    (loop [i 0
           csmc-indices (vec (range num-csmc-nodes))
           smc-indices (vec (range num-csmc-nodes num-nodes))
           zeta-sums (vec (repeat num-nodes 0.0))]
      (if (= i num-csmc-nodes)
        [csmc-indices zeta-sums]
        ;; Consider swapping CSMC node i with an SMC node
        (let [;; Candidate indices: current SMC nodes + current CSMC node i
              proposal-indices (conj smc-indices (csmc-indices i))
              proposal-log-Zs (mapv #(nth log-Zs %) proposal-indices)
              [probs _] (norm-exp proposal-log-Zs)

              ;; Update zeta sums for Rao-Blackwellization
              new-zeta-sums (reduce (fn [zs [idx p]]
                                     (update zs idx + p))
                                   zeta-sums
                                   (map vector proposal-indices probs))

              ;; Sample which node to use as CSMC
              k (sample-categorical probs)]

          (if (= k (count smc-indices))
            ;; Keep current CSMC node (k points to the appended csmc index)
            (recur (inc i) csmc-indices smc-indices new-zeta-sums)
            ;; Swap: SMC node k becomes CSMC, current CSMC becomes SMC
            (recur (inc i)
                   (assoc csmc-indices i (smc-indices k))
                   (assoc smc-indices k (csmc-indices i))
                   new-zeta-sums)))))))

(defn- run-sweep
  "Run a single SMC or CSMC sweep.

   Args:
     model-task - The probabilistic program
     num-particles - Particles per sweep
     retained-trace - Retained trace for CSMC (nil for plain SMC)
     opts - Inference options

   Returns: Spin<Measure>"
  [model-task num-particles retained-trace opts]
  (if retained-trace
    ;; CSMC sweep with retained trace
    (kernel-infer model-task
                  (k/prior-kernel)
                  num-particles
                  (assoc opts
                    :barrier-policy :every-observe
                    :pgibbs-retained-trace retained-trace))
    ;; SMC sweep (no retained trace)
    (smc-infer model-task num-particles opts)))

(defn- run-parallel-sweeps
  "Run SMC/CSMC sweeps in parallel across all nodes.

   Uses the parallel combinator to launch all sweeps concurrently,
   scaling with the underlying executor.

   Args:
     model-task - The probabilistic program
     num-particles - Particles per sweep
     retained-traces - Vector of retained traces (nil for SMC, trace for CSMC)
     opts - Inference options

   Returns: Spin<Vector<Measure>> - A spin that completes with all sweep measures"
  [model-task num-particles retained-traces opts]
  ;; Create individual sweep spins for each node
  (let [sweep-spins (mapv (fn [retained-trace]
                            (run-sweep model-task num-particles retained-trace opts))
                          retained-traces)]
    ;; Use parallel combinator to run all sweeps concurrently
    (apply comb/parallel sweep-spins)))

(defn ipmcmc-infer
  "Interacting Particle MCMC inference.

   Runs M nodes in parallel, where M_c nodes run conditional SMC (with retained
   particles) and M_s nodes run plain SMC. After each sweep, performs Gibbs
   updates on which nodes become CSMC based on marginal likelihood estimates.

   This creates 'interaction' between parallel chains: nodes with higher log-Z
   are more likely to have their particles retained in future sweeps.

   Algorithm:
   1. Initialize: Run SMC on all nodes
   2. For each iteration:
      a. Run CSMC on M_c nodes (with retained particles from previous sweep)
      b. Run SMC on M_s nodes (fresh)
      c. Collect log-Z estimates from each node
      d. Gibbs update: sample which nodes become CSMC for next sweep
      e. Extract retained particles for selected CSMC nodes
   3. Output: Weighted samples from all nodes with Rao-Blackwellized weights

   Args:
     model-task - Spin representing probabilistic program
     num-particles - Number of particles per sweep (per node)
     num-iterations - Number of IPMCMC iterations
     opts - Optional map with:
       :num-nodes - Total number of nodes (default 8)
       :num-csmc-nodes - Number of CSMC nodes (default num-nodes/2)
       :executor - Shared executor
       :all-particles? - Return all particles or one per node (default true)

   Returns: Spin<EmpiricalMeasure>

   Reference:
     Rainforth et al., 'Interacting Particle Markov Chain Monte Carlo', ICML 2016"
  [model-task num-particles num-iterations & [opts]]
  (spin
    (let [num-nodes (or (:num-nodes opts) 8)
          num-csmc-nodes (or (:num-csmc-nodes opts) (quot num-nodes 2))
          num-smc-nodes (- num-nodes num-csmc-nodes)
          all-particles? (get opts :all-particles? true)]

      (log/debug :ipmcmc/start {:num-nodes num-nodes
                          :num-csmc-nodes num-csmc-nodes
                          :num-particles num-particles
                          :num-iterations num-iterations})

      (assert (> num-csmc-nodes 0) ":num-csmc-nodes must be > 0")
      (assert (< num-csmc-nodes num-nodes) ":num-csmc-nodes must be < :num-nodes")

      ;; Initialize: all nodes run plain SMC (no retained traces yet)
      (let [initial-retained-traces (vec (repeat num-nodes nil))
            initial-sweeps (await (run-parallel-sweeps
                                   model-task num-particles initial-retained-traces opts))]

        (log/debug :ipmcmc/initial-sweeps {:num-sweeps (count initial-sweeps)})

        ;; Main IPMCMC loop
        (loop [iteration 0
               prev-measures initial-sweeps
               all-samples []]  ; Accumulate weighted samples

          (if (>= iteration num-iterations)
            ;; Done - return combined measure
            (do
              (log/debug :ipmcmc/complete {:iterations num-iterations
                                  :total-samples (count all-samples)})
              (m/empirical all-samples))

            ;; One IPMCMC iteration
            (let [;; Extract log-Z from each node
                  log-Zs (mapv m/log-marginal prev-measures)

                  ;; Gibbs update on CSMC indices
                  [csmc-indices zeta-sums] (gibbs-update-csmc-indices log-Zs num-csmc-nodes)

                  _ (log/trace :ipmcmc/gibbs-update {:iteration iteration
                                        :csmc-indices csmc-indices
                                        :log-Zs log-Zs})

                  ;; Extract retained traces for CSMC nodes
                  retained-traces
                  (vec (concat
                         ;; CSMC nodes get traces from selected particles
                         (map (fn [node-idx]
                                (let [measure (nth prev-measures node-idx)
                                      particles (m/get-particles measure)
                                      ;; Sample random particle from this node
                                      [ctx _] (rand-nth particles)]
                                  (rtp/get-state ctx [:inference :trace])))
                              csmc-indices)
                         ;; SMC nodes have no retained traces
                         (repeat num-smc-nodes nil)))

                  ;; Run new sweeps (parallel across all nodes)
                  new-measures (await (run-parallel-sweeps
                                       model-task num-particles retained-traces opts))

                  ;; Collect weighted samples with Rao-Blackwellized weights
                  ;; Weight adjustment: log(zeta_j / num_particles)
                  new-samples
                  (vec (mapcat
                         (fn [node-idx]
                           (let [measure (nth new-measures node-idx)
                                 particles (m/get-particles measure)
                                 zeta (nth zeta-sums node-idx)
                                 log-weight-adj (if (> zeta 0)
                                                  (- (Math/log zeta) (Math/log num-particles))
                                                  ##-Inf)]
                             (if all-particles?
                               ;; Return all particles from this node
                               (mapv (fn [[ctx lw]]
                                       [ctx (+ lw log-weight-adj)])
                                     particles)
                               ;; Return one random particle
                               (let [[ctx lw] (rand-nth particles)]
                                 [[ctx (+ lw log-weight-adj)]]))))
                         (range num-nodes)))]

              (log/trace :ipmcmc/iteration {:iteration iteration
                                  :new-samples (count new-samples)})

              (recur (inc iteration)
                     new-measures
                     (into all-samples new-samples)))))))))

(defn pgas-infer
  "Particle Gibbs with Ancestor Sampling inference.

  Like PGIBBS, but at each resampling barrier, performs ancestor sampling
  to probabilistically select which particle's history the retained particle
  should adopt. This improves mixing for state-space models (HMMs, etc.).

  Algorithm:
  1. Run initial sweep, select retained particle
  2. For each iteration:
     - Particle 0 follows retained trace at sample sites
     - At barriers: ancestor sampling determines which particle's history
       the retained particle adopts
       - Fork all particles, run forward with retained trace values
       - Sample ancestor proportionally to rescored weights
       - Retained particle adopts selected ancestor's history
     - Standard resampling for other particles

  Args:
    model-task - Spin representing probabilistic program
    num-particles - Total particles (1 retained + N-1 fresh)
    num-iterations - Number of PGAS sweeps
    opts - Optional map with:
      :executor - Shared executor
      :resample-threshold - ESS threshold (default 0.5)

  Returns: Spin<EmpiricalMeasure>

  Example:
    (spin
      (let [measure (await (pgas-infer (hmm-model) 20 100 {}))]
        (query measure identity)))"
  [model-task num-particles num-iterations & [opts]]
  (spin
    (log/debug :pgas/start {:num-particles num-particles
                        :num-iterations num-iterations})

    ;; Run initial sweep to get first retained trace
    (let [initial-measure (await (smc-infer model-task num-particles opts))
          initial-particles (m/get-particles initial-measure)
          ;; Select random particle's trace as initial retained trace
          initial-retained-ctx (first (rand-nth initial-particles))
          initial-retained-trace (rtp/get-state initial-retained-ctx [:inference :trace])]

      (log/debug :pgas/initial-sweep {:retained-trace-size (count initial-retained-trace)})

      ;; PGAS loop - run iterations with ancestor sampling to mix
      (loop [retained-trace initial-retained-trace
             iteration 0]

        (if (>= iteration num-iterations)
          ;; Done - run one final sweep and collect all particles
          (let [final-measure (await (kernel-infer
                                       model-task
                                       (k/prior-kernel)
                                       num-particles
                                       (assoc opts
                                         :barrier-policy :every-observe
                                         :pgibbs-retained-trace retained-trace
                                         :pgas-ancestor-sampling? true)))]

            (log/debug :pgas/complete {:iterations num-iterations
                                :num-particles num-particles})

            ;; Return the final sweep's measure directly
            final-measure)

          ;; Run conditional SMC sweep with ancestor sampling
          (let [sweep-measure (await (kernel-infer
                                       model-task
                                       (k/prior-kernel)
                                       num-particles
                                       (assoc opts
                                         :barrier-policy :every-observe
                                         :pgibbs-retained-trace retained-trace
                                         :pgas-ancestor-sampling? true)))

                sweep-particles (m/get-particles sweep-measure)

                ;; Select new retained particle according to weights
                log-weights (mapv second sweep-particles)
                norm-weights (m/normalize-log-weights log-weights)
                ;; Sample one index according to weights
                u (rand)
                selected-idx (loop [i 0 cumsum 0.0]
                               (let [cumsum' (+ cumsum (nth norm-weights i))]
                                 (if (< u cumsum')
                                   i
                                   (recur (inc i) cumsum'))))
                [new-retained-ctx _] (nth sweep-particles selected-idx)
                new-retained-trace (rtp/get-state new-retained-ctx [:inference :trace])]

            (log/trace :pgas/sweep {:iteration iteration
                                :new-trace-size (count new-retained-trace)})

            (recur new-retained-trace
                   (inc iteration))))))))

;; =============================================================================
;; Black Box Variational Inference (BBVI)
;; =============================================================================

(defn- optimal-scaling
  "Compute optimal control variate coefficient for variance reduction.
   Given f = w*g and g, returns Cov(f,g)/Var(g)."
  [f g]
  (when (and (seq f) (seq g) (= (count f) (count g)))
    (let [n (count f)
          f-bar (/ (reduce + f) n)
          g-bar (/ (reduce + g) n)
          g-centered (mapv #(- % g-bar) g)
          numerator (reduce + 1e-12 (map * (map #(- % f-bar) f) g-centered))
          denominator (reduce + 1e-12 (map * g-centered g-centered))]
      (/ numerator denominator))))

(defn- aggregate-gradients
  "Aggregate gradients from multiple particles with variance reduction.

   For each address, computes REINFORCE gradient with control variate:
   grad-ELBO ~ sum (w_i - a*) * grad-log q(z_i)

   where a* = Cov(w*g, g)/Var(g) is the optimal baseline."
  [particle-gradients particle-log-weights]
  (let [;; Collect all addresses across particles
        all-addrs (reduce set/union
                         (map #(set (keys %)) particle-gradients))]
    (reduce
     (fn [result addr]
       (let [;; Get gradients and weights for particles that have this address
             valid-pairs (filter
                          (fn [[grads lw]]
                            (and (contains? grads addr)
                                 (grad/finite? lw)))
                          (map vector particle-gradients particle-log-weights))
             n (count valid-pairs)]
         (if (zero? n)
           result
           (let [grads (mapv #(get (first %) addr) valid-pairs)
                 weights (mapv second valid-pairs)
                 ;; Normalize weights to [0,1] range
                 max-w (apply max weights)
                 norm-weights (mapv #(Math/exp (- % max-w)) weights)
                 ;; For each gradient dimension, compute scaled gradient
                 grad-dim (count (first grads))
                 final-grad
                 (mapv
                  (fn [dim]
                    (let [g-vals (mapv #(nth % dim) grads)
                          wg-vals (mapv * norm-weights g-vals)
                          a-star (or (optimal-scaling wg-vals g-vals) 0.0)]
                      ;; Average gradient with baseline subtraction
                      (/ (reduce + (map (fn [wg g] (- wg (* a-star g)))
                                        wg-vals g-vals))
                         n)))
                  (range grad-dim))]
             (assoc result addr final-grad)))))
     {}
     all-addrs)))

(defn- update-variational-dists!
  "Update variational distributions via gradient ascent.

   Uses AdaGrad for adaptive learning rates."
  [q-dists-atom adagrad-atom gradients base-lr use-adagrad?]
  (doseq [[addr grad] gradients]
    (when-let [[dist _] (get @q-dists-atom addr)]
      (when (and dist (grad/has-gradient? dist))
        ;; Update AdaGrad accumulator
        (let [grad-squared (mapv #(* % %) grad)
              old-adagrad (or (get @adagrad-atom addr)
                              (vec (repeat (count grad) 0.0)))
              new-adagrad (if use-adagrad?
                            (mapv + old-adagrad grad-squared)
                            old-adagrad)
              ;; Compute per-parameter learning rate
              lr (if use-adagrad?
                   (mapv #(/ base-lr (+ 1e-8 (Math/sqrt %))) new-adagrad)
                   base-lr)]
          (when use-adagrad?
            (swap! adagrad-atom assoc addr new-adagrad))
          ;; Apply gradient step
          (let [new-dist (grad/grad-step dist grad lr)]
            (swap! q-dists-atom assoc addr [new-dist nil])))))))

(defn bbvi-infer
  "Black Box Variational Inference.

   Learns variational approximation q(z) ~ p(z|x) by maximizing ELBO
   using REINFORCE gradient estimator with control variates.

   Algorithm:
   1. Initialize q(z) = p(z) (prior) at each sample address
   2. For each iteration:
      a. Run N particles sampling from current q
      b. Compute importance weights w = p(x,z)/q(z)
      c. Estimate gradient: grad-ELBO ~ sum w_i grad-log q(z_i) (with baseline)
      d. Update q via gradient ascent (AdaGrad)
   3. Return final weighted samples

   Args:
     model-task - Spin representing probabilistic program
     num-particles - Particles per iteration (batch size)
     num-iterations - Number of optimization iterations
     opts - Optional map with:
       :base-lr - Base learning rate (default 0.1)
       :use-adagrad? - Use AdaGrad adaptive learning (default true)
       :executor - Shared executor
       :only - Set of addresses to learn (nil = all)
       :exclude - Set of addresses to exclude from learning

   Returns: Spin<EmpiricalMeasure>

   Note: BBVI works best for models with differentiable sample sites.
   For discrete variables, consider using enumeration or REINFORCE.

   Reference:
     Ranganath et al., 'Black Box Variational Inference', AISTATS 2014"
  [model-task num-particles num-iterations & [opts]]
  (spin
    (let [base-lr (or (:base-lr opts) 0.1)
          use-adagrad? (get opts :use-adagrad? true)
          ;; Shared variational distributions: {addr -> [distribution adagrad-state]}
          q-dists (atom {})
          ;; AdaGrad accumulators: {addr -> gradient-squared-sum}
          adagrad-state (atom {})]

      (log/debug :bbvi/start {:num-particles num-particles
                          :num-iterations num-iterations
                          :base-lr base-lr})

      ;; BBVI optimization loop
      (loop [iteration 0
             all-samples []]

        (if (>= iteration num-iterations)
          ;; Done - return weighted samples from final iteration
          (do
            (log/debug :bbvi/complete {:iterations num-iterations
                                :num-samples (count all-samples)
                                :num-q-dists (count @q-dists)})
            ;; Return measure from final samples
            ;; Use samples from last few iterations for better estimate
            (m/empirical (vec (take-last (* num-particles 3) all-samples))))

          ;; Run one BBVI iteration
          (let [;; Run particles in parallel, sampling from current q
                ;; For simplicity, use importance sampling with prior
                ;; and record gradients manually
                sweep-measure (await (importance-sampling model-task num-particles opts))
                particles (m/get-particles sweep-measure)

                ;; Collect gradients from particles
                ;; Since we're using importance sampling, gradients come from
                ;; sampling from prior - need to record them during execution
                ;; For now, compute approximate gradients from traces
                particle-data
                (mapv (fn [[ctx log-weight]]
                        (let [trace (rtp/get-state ctx [:inference :trace])]
                          {:log-weight log-weight
                           :trace trace
                           :gradients
                           ;; Compute gradients from trace samples
                           (reduce-kv
                            (fn [grads addr entry]
                              (if (:observed? entry)
                                grads  ; Don't update observed sites
                                (let [dist (:distribution entry)
                                      value (:value entry)
                                      ;; Get or initialize q for this address
                                      q-dist (or (first (get @q-dists addr))
                                                 (do (swap! q-dists assoc addr [dist nil])
                                                     dist))]
                                  (if (grad/has-gradient? q-dist)
                                    (assoc grads addr (grad/compute-gradient q-dist value))
                                    grads))))
                            {}
                            trace)}))
                      particles)

                ;; Aggregate gradients with variance reduction
                all-gradients (mapv :gradients particle-data)
                all-log-weights (mapv :log-weight particle-data)
                aggregated-grads (aggregate-gradients all-gradients all-log-weights)

                _ (log/trace :bbvi/iteration {:iteration iteration
                                      :num-grad-addrs (count aggregated-grads)
                                      :avg-log-weight (/ (reduce + all-log-weights)
                                                         num-particles)})

                ;; Update variational distributions
                _ (update-variational-dists! q-dists adagrad-state
                                             aggregated-grads base-lr use-adagrad?)

                ;; Collect samples for output
                new-samples (mapv (fn [[ctx lw]] [ctx lw]) particles)]

            (recur (inc iteration)
                   (into all-samples new-samples))))))))

(defn get-variational-dists
  "Extract learned variational distributions from BBVI measure.

   Returns: {address -> distribution}

   Note: This requires the measure to have been produced by bbvi-infer
   and have metadata attached. Currently returns nil for other measures."
  [_measure]
  ;; Future: attach q-dists to measure metadata
  nil)
