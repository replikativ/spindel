(ns org.replikativ.spindel.inference.inference
  "Compositional probabilistic inference algorithms.

  Implements spin-returning inference functions on top of the kernel
  abstraction in `kernel.cljc` and the `KernelCoordinator` in
  `coordinator.cljc`:

  - kernel-infer: Core inference function using PInferenceKernel
  - importance-sampling: Delegates to kernel-infer with PriorKernel, no barriers
  - smc-infer: Delegates to kernel-infer with PriorKernel, barriers at observe

  The particle methods (smc-infer, pimh-infer, pgibbs-infer, pgas-infer, and
  the sweeps of ipmcmc-infer) run on savepoint SMC (`inference.smc`) for
  pure inference (`:world-policy :fresh`, the default): their measures hold
  `Sample`s (result + trace) rather than particle contexts. With
  `:world-policy :fork` they stay on the coordinator below.

  All functions return Spin<EmpiricalMeasure> for composability.

  Architecture in one paragraph: each particle runs the probabilistic
  program in its own forked execution context. `sample` / `observe`
  effects post to the shared KernelCoordinator. The coordinator's
  PInferenceKernel decides what to do at each checkpoint — assign a
  fresh sample (importance), wait for all particles and resample
  (SMC), etc. Per-particle results are folded into an
  `EmpiricalMeasure` (weighted samples) delivered through `on-complete`.

  Key design principles:
  - Unified kernel protocol (PInferenceKernel controls checkpoint behavior)
  - Single coordinator (KernelCoordinator handles all inference patterns)
  - Spin-returning API (non-blocking, composable via await)
  - Measure-centric post-processing (query, predict)"
  (:require [org.replikativ.spindel.inference.measure :as m]
            [org.replikativ.spindel.inference.random :as random]
            [org.replikativ.spindel.inference.hmc :as hmc]
            [org.replikativ.spindel.inference.kernel :as k]
            [org.replikativ.spindel.inference.smc :as smc]
            [org.replikativ.spindel.inference.coordinator :as coord]
            [org.replikativ.spindel.inference.gradient :as grad]
            [org.replikativ.spindel.inference.trace :as itrace]
            [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.engine.core :as rtc]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.executor :as sched]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]
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

        ;; Enqueue spin execution event. PEngine currently appends the event
        ;; before asking its executor to drain, so executor rejection can throw
        ;; after the event became visible. Cache cancellation immediately: a
        ;; later drain can then only observe the cancelled result, never run the
        ;; particle body in a world the startup recovery has already settled.
        (try
          (rtc/enqueue-event! {:type :spin-execution
                               :id spin-id
                               :spin task
                               :execution-context context
                               :callback-egress-policy :causal-follow
                               :resolve-fn resolve-fn
                               :reject-fn reject-fn})
          (catch #?(:clj Throwable :cljs :default) error
            (spin-core/cancel-spin! task)
            (when-let [manager (:world-manager coordinator)]
              (coord/particle-context-terminal! manager context))
            (throw error)))))))

;; =============================================================================
;; Kernel-Based Inference
;; =============================================================================

(defn- particle-world-recovery [world-manager]
  {:status (:status @world-manager)
   :manager world-manager
   :await-quiescent
   (coord/await-particle-world-quiescence world-manager)
   :cancel! #(coord/cancel-particle-worlds! world-manager)
   :discard!
   #(coord/discard-particle-worlds-when-quiescent! world-manager)
   :descriptors (coord/world-descriptors world-manager)})

(defmacro ^:private inference-spin [& body]
  `(spin-core/with-causal-descendant-egress (spin ~@body)))

;; =============================================================================
;; Markov chains: replay plus accept
;; =============================================================================

(defn- block-gibbs-options
  "Translate a BlockGibbsKernel into `itrace/mh-step` options. The classifier
  and the selector see the trace in the coordinator's shape; only latent
  sites are classified, and a step whose block is empty or has no kernel moves
  nothing. The selection probability is taken to be the same in both traces,
  which holds when a move does not change which sites belong to the block."
  [{:keys [block-selector block-kernels address-classifier]}]
  (let [proposals (atom nil)]
    {:select
     (fn [current iteration]
       (let [legacy (itrace/legacy-trace current)
             latent (set (itrace/latent-addresses current))
             blocks (reduce-kv (fn [acc address entry]
                                 (if-let [block-id (and (latent address)
                                                        (address-classifier address entry))]
                                   (update acc block-id (fnil conj #{}) address)
                                   acc))
                               {} legacy)
             block-id (k/select-block block-selector legacy iteration)
             targets (get blocks block-id #{})
             kernel (get block-kernels block-id)]
         (reset! proposals (when (and kernel (seq targets)
                                      (not (instance? org.replikativ.spindel.inference.kernel.PriorBlockKernel kernel)))
                             (k/propose-block kernel legacy targets)))
         ;; Blocks are selected by id, independently of the trace.
         {:targets targets :log-selection (constantly 0.0)}))
     :propose
     (fn [sp-value old-entry]
       (if-let [proposed @proposals]
         ;; A block kernel's move is taken to be symmetric (the random walk
         ;; is; a custom kernel must be).
         {:value (get proposed (:savepoint/address sp-value)) :symmetric? true}
         (itrace/prior-proposal sp-value old-entry)))}))

(defn- mh-options
  "`itrace/mh-step` options of a Markov-chain kernel, or nil for kernels the
  coordinator runs."
  [kernel]
  (case (k/kernel-id kernel)
    :single-site-mh {:iterations (:num-iterations kernel)}
    :random-walk-mh {:iterations (:num-iterations kernel)
                     :propose (itrace/random-walk-proposal (:step-size kernel))}
    :block-gibbs (assoc (block-gibbs-options kernel)
                        :iterations (:num-iterations kernel))
    :hmc {:iterations (:num-iterations kernel)
          :step (hmc/within-gibbs (select-keys kernel [:step-size :steps]))}
    nil))

(defn- run-markov-chain
  "One chain in its own world: run the model, move it `iterations` times,
  give every world back. Returns the chain's particles: its projected final
  state, or (kernel `:samples :all`) every state after `:burn` as a Sample."
  [model-task kernel executor seed]
  (inference-spin
   (let [;; per chain: a block Gibbs description closes over its own state
         {:keys [iterations] :as step-opts} (mh-options kernel)
         root (ctx/create-execution-context :executor executor)
         session (sp/open! root {:purpose :mcmc :seed seed :fork-opts {:systems :none}
                                 :retain-released? false})]
     (try
       (let [initial (await (trace/run session model-task (itrace/policy {:init? true})
                                       {:anchor? itrace/anchor?}))
             _ (when (contains? initial :trace/error)
                 (throw (ex-info "Inference failed during model execution"
                                 {:type ::inference-failed}
                                 (:trace/error initial))))
             ;; From an impossible state every ratio is NaN and nothing is
             ;; ever accepted; say so instead of returning that state.
             _ (when (= ##-Inf (itrace/log-joint initial))
                 (throw (ex-info "The initial state of the chain has zero density"
                                 {:type ::impossible-initial-state})))
             samples (volatile! [])
             step-opts (cond-> step-opts
                         (= :all (:samples kernel))
                         (assoc :on-step
                                (let [i (volatile! 0)]
                                  (fn [{t :trace}]
                                    (when (> (vswap! i inc) (:burn kernel 0))
                                      (vswap! samples conj
                                              [(m/sample-particle (:trace/result t)
                                                                  (itrace/legacy-trace t))
                                               0.0]))))))
             {final :trace accepted :accepted}
             (await (itrace/mh-chain initial iterations step-opts))
             world (:trace/world final)]
         (rtp/swap-state! world [:inference]
                          (fn [state]
                            (assoc state
                                   :result (:trace/result final)
                                   :trace (itrace/legacy-trace final)
                                   :mcmc {:completed-iterations iterations
                                          :acceptance-count accepted})))
         (if (= :all (:samples kernel))
           @samples
           [[(coord/project-posterior-context world) 0.0]]))
       (finally
         ;; Closing the session cancels and joins every world of the chain.
         ;; The root is not stopped here: `stop-context!` waits for the
         ;; context's drains, and this body may be running inside one.
         (await-finalization (sp/close! session)))))))

(defn- markov-chain-infer
  [model-task kernel num-chains opts]
  ;; Chains run in fresh worlds of their own. Running them in forks of the
  ;; caller's world, as `:world-policy :fork` does for particles, is not
  ;; implemented; refuse it, do not ignore it.
  (when (or (= :fork (:world-policy opts)) (some? (:world-opts opts)))
    (throw (ex-info "Markov-chain kernels run in fresh worlds"
                    {:type ::invalid-world-policy
                     :world-policy (:world-policy opts)
                     :supported #{:fresh}})))
  (inference-spin
   (let [own-executor (when-not (:executor opts)
                        (sched/thread-pool-executor {:threads 2}))
         executor (or (:executor opts) own-executor)]
     (try
       (let [;; drawn here, in order: the chains then run concurrently
             seeds (vec (repeatedly num-chains random/fresh-seed))
             chains (await (apply comb/parallel
                                  (mapv #(run-markov-chain model-task kernel executor %) seeds)))]
         (m/empirical (into [] cat chains)))
       (finally
         (when own-executor
           #?(:clj (.close ^java.lang.AutoCloseable own-executor)
              :cljs nil)))))))

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
    - :world-policy - :fresh (default) for pure inference, or :fork to
      execute each particle in a frozen canonical Yggdrasil world that is
      discarded after the final particle values are captured
    - :world-opts - Optional :systems/:rights/:snapshots policy forwarded to
      canonical particle forks; lifecycle fields are owned by inference

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
  (if (mh-options kernel)
    ;; Markov-chain kernels are replay plus accept over traces; each of the
    ;; `num-particles` is an independent chain.
    (markov-chain-infer model-task kernel num-particles opts)
    (inference-spin
     (log/debug :kernel-infer/start {:kernel-id (k/kernel-id kernel)
                                     :num-particles num-particles
                                     :barrier-policy (:barrier-policy opts :every-observe)})

     (let [runtime rtc/*execution-context*
           world-policy (get opts :world-policy :fresh)
           _ (when-not (#{:fresh :fork} world-policy)
               (throw (ex-info "Unknown inference world policy"
                               {:type ::invalid-world-policy
                                :world-policy world-policy
                                :supported #{:fresh :fork}})))
          ;; Create or use provided shared executor
           shared-executor (or (:executor opts)
                             ;; Canonical child worlds share the ambient runtime
                             ;; unless the caller explicitly delegates another
                             ;; scheduler. This keeps executor ownership with the
                             ;; enclosing world instead of leaking an inference-
                             ;; local pool after affine world settlement.
                               (when (= :fork world-policy)
                                 (:executor runtime))
                               (sched/thread-pool-executor {:threads 2}))
           world-manager (when (= :fork world-policy)
                           (coord/create-world-manager
                            (assoc (:world-opts opts) :executor shared-executor)))
           coordinator (coord/create-kernel-coordinator
                        runtime
                        kernel
                        num-particles
                        (assoc opts :world-manager world-manager))
           _ (when world-manager
               (swap! world-manager assoc :client coordinator))

          ;; PGIBBS: Check if we have a retained trace (for conditional SMC)
           pgibbs-retained-trace (:pgibbs-retained-trace opts)

           _initial-generation
           (when world-manager
             (coord/begin-particle-generation-transition! world-manager))

          ;; Initialize particles with coordinator reference
         ;; For PGIBBS: first particle is retained
           initial-particles
           (try
             (let [particles
                   (loop [idx 0
                          particles []]
                     (if (= idx num-particles)
                       particles
                       (let [world (when world-manager
                                     (await
                                      (fn [resolve reject]
                                        (coord/fork-particle-world!
                                         world-manager runtime resolve reject))))
                             particle-ctx (if world
                                            (:child-ctx world)
                                            (ctx/create-execution-context
                                             :executor shared-executor))
                             ;; generation-slot ids, not gensyms: the particle map's
                             ;; order decides which draw goes to which particle, so
                             ;; a seeded run is reproducible only if it is the same
                             ;; in every run
                             particle-id (coord/particle-id 0 idx)
                             is-retained? (and pgibbs-retained-trace (= idx 0))]

                         (rtp/swap-state!
                          particle-ctx [:inference]
                          (constantly
                           {:log-weight 0.0
                            :choice-stack []
                            :checkpoint-seq 0
                            :trace {}
                            :checkpoints {}
                            :particle-id particle-id
                            :sweep 0
                            :world world
                            :inference-coordinator coordinator}))
                         (rtp/swap-state! particle-ctx [:inference :task]
                                          (constantly model-task))

                         (when is-retained?
                           (reset! (.-retained-particle-id coordinator) particle-id)
                           (log/debug :kernel-infer/set-retained-particle
                                      {:particle-id particle-id}))

                         (recur (inc idx) (conj particles particle-ctx)))))]
               (when (and world-manager
                          (not (coord/complete-particle-generation-transition!
                                world-manager particles)))
                 (throw (ex-info "Inference cancelled during particle initialization"
                                 {:type spin-core/spin-cancelled})))
               particles)
             (catch #?(:clj Throwable :cljs :default) error
               (when world-manager
               ;; Close the generation transaction, then wait past the owning
               ;; Spin's cancellation for every in-flight fork callback and
               ;; affine discard to finish.
                 (coord/complete-particle-generation-transition!
                  world-manager [])
                 (await-finalization
                  (coord/cancel-particle-worlds! world-manager)))
               (throw error)))]

       (log/debug :kernel-infer/particles-initialized {:num-particles (count initial-particles)})

     ;; Once particles are registered, this Spin owns their complete lifecycle.
     ;; Normal completion sets `completed?` only after world settlement and
     ;; posterior projection. Every other exit — especially cancellation of the
     ;; public inference Spin by an enclosing Run — cancels and joins the manager
     ;; before propagating the original result/error.
       (let [completed? (atom false)]
         (try
         ;; Start all particles. Initialization is all-or-nothing from the
         ;; caller's perspective, but an executor can reject midway through the
         ;; enqueue loop. In that case distinguish successfully started contexts
         ;; from contexts that never ran, then enter the normal supervised
         ;; cancellation/quiescence lifecycle.
           (let [started (atom #{})]
             (try
               (doseq [particle-ctx initial-particles]
                 (start-particle! particle-ctx coordinator)
                 (swap! started conj (:fork-id particle-ctx)))
               (catch #?(:clj Throwable :cljs :default) error
                 (when world-manager
                   (doseq [particle-ctx initial-particles
                           :when (not (contains? @started (:fork-id particle-ctx)))]
                     (coord/particle-context-terminal! world-manager particle-ctx))
                   (coord/cancel-particle-worlds! world-manager))
                 (throw
                  (ex-info
                   "Inference failed while starting particles"
                   (cond-> {:type ::particle-start-failed
                            :started (count @started)
                            :requested num-particles}
                     world-manager
                     (assoc :world/recovery
                            (particle-world-recovery world-manager)))
                   error)))))

           (log/debug :kernel-infer/particles-started)

         ;; Await completion
           (let [final-measure (await (coord/await-completion coordinator))]

           ;; A particle's spin aborted: the coordinator delivered a
           ;; failure marker instead of an EmpiricalMeasure. Re-throw so
           ;; the calling spin / @(spin …) propagates the error to the
           ;; agent / REPL caller, instead of returning a bogus measure.
             (when (coord/inference-failure? final-measure)
               (let [world-recovery
                     (when world-manager (particle-world-recovery world-manager))]
                 (throw (ex-info "Inference failed during particle execution"
                                 (cond-> {:type ::inference-failed
                                          :particle-id (:particle-id final-measure)}
                                   world-recovery
                                   (assoc :world/recovery world-recovery))
                                 (:error final-measure)))))

             (log/debug :kernel-infer/complete
                        {:num-particles num-particles
                         :log-marginal (m/log-marginal final-measure)
                         :ess (m/effective-sample-size final-measure)})

             (reset! completed? true)
             final-measure)
           (finally
             (when (and world-manager (not @completed?))
               (await-finalization
                (coord/cancel-particle-worlds! world-manager))))))))))

;; =============================================================================
;; Convenience Functions (Delegate to kernel-infer)
;; =============================================================================

(defn- on-savepoints?
  "Whether a particle method runs on savepoint SMC (`inference.smc`): pure
  inference in fresh worlds does; `:world-policy :fork` stays on the
  coordinator, whose canonical worlds carry recovery and settlement."
  [opts]
  (= :fresh (get opts :world-policy :fresh)))

(defn- on-savepoints
  "A spin resolving the savepoint CPS `operation`, a failure reported as
  `::inference-failed` with the model's error as its cause."
  [operation]
  (inference-spin
   (try
     (await operation)
     (catch #?(:clj Throwable :cljs :default) e
       (throw (ex-info "Inference failed during particle execution"
                       {:type ::inference-failed} e))))))

(defn smc-infer
  "Run SMC inference on probabilistic program.

  Sequential Monte Carlo with resampling at observe barriers. Pure inference
  (`:world-policy :fresh`, the default) runs `inference.smc/smc`, whose
  particles are `Sample`s; `:world-policy :fork` delegates to kernel-infer
  with PriorKernel and :barrier-policy :every-observe.

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
  (if (on-savepoints? opts)
    (on-savepoints (smc/smc model-task num-particles opts))
    ;; SMC = PriorKernel with barriers at every observe
    (kernel-infer model-task
                  (k/prior-kernel)
                  num-particles
                  (assoc opts :barrier-policy :every-observe))))

(defn importance-sampling
  "Run importance sampling inference on probabilistic program.

  Simple importance sampling without resampling. Pure inference
  (`:world-policy :fresh`, the default) runs `inference.smc/smc` with
  resampling off; `:world-policy :fork` delegates to kernel-infer with
  PriorKernel and :barrier-policy :none.

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
  (if (on-savepoints? opts)
    ;; savepoint SMC that never resamples: ESS never falls below 0
    (on-savepoints (smc/smc model-task num-samples (assoc opts :resample-threshold 0.0)))
    ;; Importance sampling = PriorKernel with no barriers
    (kernel-infer model-task
                  (k/prior-kernel)
                  num-samples
                  (assoc opts :barrier-policy :none))))

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

(defn- normalized-samples
  "A sweep's particles as lightweight samples whose weights sum to one, so
   sweeps can be pooled into one MCMC estimate."
  [measure]
  (let [ps (m/get-particles measure)
        lse (m/log-sum-exp (mapv second ps))]
    (mapv (fn [[c lw]] [(m/sample-particle (m/get-value c) (m/get-trace c)) (- lw lse)]) ps)))

(defn pimh-infer
  "Particle Independent Metropolis-Hastings (Andrieu et al. 2010).

  Each iteration proposes a fresh SMC sweep and accepts it with probability
  min(1, Ẑ_new / Ẑ_current); the current sweep's particles, normalized, are
  emitted every iteration.

  Args:
    model-task, num-particles (per sweep), num-iterations
    opts: :executor, :resample-threshold

  Returns: Spin<EmpiricalMeasure>"
  [model-task num-particles num-iterations & [opts]]
  (if (on-savepoints? opts)
    (on-savepoints (smc/pimh model-task num-particles num-iterations opts))
    (spin
     (let [initial (await (smc-infer model-task num-particles opts))]
       (loop [current (normalized-samples initial)
              current-log-Z (m/log-marginal initial)
              iteration 0
              all-samples []]
         (if (>= iteration num-iterations)
           (m/empirical all-samples)
           (let [proposed (await (smc-infer model-task num-particles opts))
                 proposed-log-Z (m/log-marginal proposed)
                 log-alpha (- proposed-log-Z current-log-Z)
                 accept? (or (>= log-alpha 0.0) (< (Math/log (m/uniform01)) log-alpha))
                 [current' log-Z'] (if accept?
                                     [(normalized-samples proposed) proposed-log-Z]
                                     [current current-log-Z])]
             (log/trace :pimh/mh-step {:iteration iteration :log-alpha log-alpha :accept? accept?})
             (recur current' log-Z' (inc iteration) (into all-samples current')))))))))

(defn- csmc-chain
  "Iterated conditional SMC: each sweep keeps one retained trajectory (from
   the previous sweep) alive through resampling, the next retained
   trajectory is drawn from the sweep's weights, and every sweep's
   particles are emitted normalized."
  [model-task num-particles num-iterations opts]
  (spin
   (let [initial (await (smc-infer model-task num-particles opts))
         pick (fn [measure]
                (let [ps (m/get-particles measure)]
                  (m/get-trace (first (nth ps (m/sample-categorical
                                               (m/normalize-log-weights (mapv second ps))))))))]
     (loop [retained-trace (pick initial)
            iteration 0
            all-samples []]
       (if (>= iteration num-iterations)
         (m/empirical all-samples)
         (let [sweep (await (kernel-infer model-task (k/prior-kernel) num-particles
                                          (assoc opts
                                                 :barrier-policy :every-observe
                                                 :pgibbs-retained-trace retained-trace)))]
           (recur (pick sweep) (inc iteration) (into all-samples (normalized-samples sweep)))))))))

(defn pgibbs-infer
  "Particle Gibbs (conditional SMC, Andrieu et al. 2010).

  Args:
    model-task, num-particles (per sweep, including the retained one),
    num-iterations (sweeps)
    opts: :executor

  Returns: Spin<EmpiricalMeasure> of every sweep's particles, each sweep
  normalized to total weight one."
  [model-task num-particles num-iterations & [opts]]
  (if (on-savepoints? opts)
    (on-savepoints (smc/pgibbs model-task num-particles num-iterations opts))
    (csmc-chain model-task num-particles num-iterations opts)))

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
              k (m/sample-categorical probs)]

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
  (cond
    ;; SMC sweep (no retained trace)
    (nil? retained-trace)
    (smc-infer model-task num-particles opts)

    (on-savepoints? opts)
    (on-savepoints (smc/smc model-task num-particles
                            (assoc opts :retained (smc/retained-choices retained-trace))))

    ;; CSMC sweep with retained trace
    :else
    (kernel-infer model-task
                  (k/prior-kernel)
                  num-particles
                  (assoc opts
                         :barrier-policy :every-observe
                         :pgibbs-retained-trace retained-trace))))

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
     (assert (> num-csmc-nodes 0) ":num-csmc-nodes must be > 0")
     (assert (< num-csmc-nodes num-nodes) ":num-csmc-nodes must be < :num-nodes")
     (loop [iteration 0
            ;; iteration 0 runs plain SMC on every node
            measures (await (run-parallel-sweeps model-task num-particles
                                                 (vec (repeat num-nodes nil)) opts))
            all-samples []]
       (if (>= iteration num-iterations)
         (m/empirical all-samples)
         (let [log-Zs (mapv m/log-marginal measures)
               [csmc-indices zeta-sums] (gibbs-update-csmc-indices log-Zs num-csmc-nodes)
               ;; emit THESE sweeps, each node weighted by its Rao-Blackwellized
               ;; probability of being a conditional node (ζ_j), particles
               ;; normalized within the node
               samples (vec (mapcat
                             (fn [node-idx]
                               (let [zeta (nth zeta-sums node-idx)
                                     node (normalized-samples (nth measures node-idx))]
                                 (when (pos? zeta)
                                   (if all-particles?
                                     (map (fn [[smp lw]] [smp (+ lw (Math/log zeta))]) node)
                                     [[(first (nth node (m/sample-categorical
                                                         (m/normalize-log-weights (mapv second node)))))
                                       (Math/log zeta)]]))))
                             (range num-nodes)))
               retained-traces (vec (concat
                                     (map (fn [node-idx]
                                            (let [ps (m/get-particles (nth measures node-idx))]
                                              (m/get-trace (first (nth ps (m/sample-categorical
                                                                           (m/normalize-log-weights (mapv second ps))))))))
                                          csmc-indices)
                                     (repeat num-smc-nodes nil)))]
           (log/trace :ipmcmc/gibbs-update {:iteration iteration :csmc-indices csmc-indices})
           (recur (inc iteration)
                  (await (run-parallel-sweeps model-task num-particles retained-traces opts))
                  (into all-samples samples))))))))

(defn pgas-infer
  "Particle Gibbs with Ancestor Sampling (Lindsten et al. 2014).

  Like `pgibbs-infer`, but at every barrier the retained particle redraws
  which particle's past it continues from, with weights
  w_i · p(retained future | particle i's past) computed by re-running each
  particle's future on the retained values. Improves mixing on state-space
  models; costs a forward re-run per particle per barrier.

  Returns: Spin<EmpiricalMeasure> of every sweep's particles, each sweep
  normalized to total weight one."
  [model-task num-particles num-iterations & [opts]]
  (case (get opts :world-policy :fresh)
    :fresh (on-savepoints (smc/pgas model-task num-particles num-iterations opts))
    :fork (throw (ex-info "PGAS ancestor scoring does not yet support canonical worlds"
                          {:type ::world-pgas-unsupported
                           :world-policy :fork}))
    (throw (ex-info "Unknown inference world policy"
                    {:type ::invalid-world-policy
                     :world-policy (:world-policy opts)
                     :supported #{:fresh :fork}}))))

;; =============================================================================
;; Black Box Variational Inference (BBVI)
;; =============================================================================

(defrecord VariationalKernel [q-dists]
  ;; q-dists: atom {address -> distribution}, shared by all particles.
  ;; A latent site samples from q (initialized to the site's prior the first
  ;; time the address is seen), contributes log p − log q to the weight,
  ;; and records ∇ log q at its value for the gradient step.
  k/PInferenceKernel
  (kernel-id [_] :variational)
  (step [_ ctx checkpoint _trace]
    (let [{:keys [source options address]} checkpoint
          {:keys [observe]} options]
      (if (some? observe)
        {:action :assign :value observe}
        (let [q (get (swap! q-dists #(if (contains? % address) % (assoc % address source)))
                     address)]
          (if (grad/has-gradient? q)
            (let [v (ar/sample* q)]
              (rtp/swap-state! ctx [:inference :q-grads]
                               #(assoc (or % {}) address (grad/compute-gradient q v)))
              {:action :assign :value v
               :log-weight-delta (- (ar/observe* source v) (ar/observe* q v))})
            {:action :assign :value (ar/sample* source)})))))
  (on-complete [_ ctx trace result]
    {:action :done :trace trace :result result
     :log-weight (or (rtp/get-state ctx [:inference :log-weight]) 0.0)}))

(defn- variational-draw
  "The proposal of a savepoint BBVI iteration: a latent site whose q (the
  site's prior, the first time its address is seen) has a gradient draws from
  q; `inference.trace/policy` then weights it by p/q."
  [q-dists]
  (fn [sp _old-entry]
    (let [address (:savepoint/address sp)
          prior (:dist (:savepoint/payload sp))
          q (get (swap! q-dists #(if (contains? % address) % (assoc % address prior))) address)]
      (when (grad/has-gradient? q)
        (let [v (ar/sample* q)]
          {:value v :log-proposal (ar/observe* q v)})))))

(defn- q-gradients
  "{address ∇log q(value)} of the latent sites of a Sample's trace that
  `qs` has a differentiable q for."
  [qs trace]
  (into {} (keep (fn [[address {:keys [value observed?]}]]
                   (let [q (get qs address)]
                     (when (and (not observed?) q (grad/has-gradient? q))
                       [address (grad/compute-gradient q value)]))))
        trace))

(defn- optimal-scaling
  "Control variate coefficient Cov(f,g)/Var(g)."
  [f g]
  (let [n (count f)
        f-bar (/ (reduce + f) n)
        g-bar (/ (reduce + g) n)
        g-centered (mapv #(- % g-bar) g)]
    (/ (reduce + 1e-12 (map * (map #(- % f-bar) f) g-centered))
       (reduce + 1e-12 (map * g-centered g-centered)))))

(defn- aggregate-gradients
  "Per address, the score-function ELBO gradient
     (1/n) Σ (log w_i − a*) ∇log q(z_i),   log w = log p(x, y) − log q(x)
   with the variance-minimizing control variate a* = Cov(f, g)/Var(g),
   f = log w · g (Ranganath et al. 2014)."
  [particle-gradients particle-log-weights]
  (let [all-addrs (reduce set/union (map #(set (keys %)) particle-gradients))]
    (reduce
     (fn [result addr]
       (let [valid (filter (fn [[grads lw]] (and (contains? grads addr) (grad/finite? lw)))
                           (map vector particle-gradients particle-log-weights))
             n (count valid)]
         (if (< n 2)
           result
           (let [grads (mapv #(get (first %) addr) valid)
                 lws (mapv second valid)]
             (assoc result addr
                    (mapv (fn [dim]
                            (let [g (mapv #(nth % dim) grads)
                                  f (mapv * lws g)
                                  a (optimal-scaling f g)]
                              (/ (reduce + (map (fn [x y] (- x (* a y))) f g)) n)))
                          (range (count (first grads)))))))))
     {}
     all-addrs)))

(defn- update-variational-dists!
  "One ascent step on every q with a gradient. `adagrad`: true accumulates
   squared gradients (AdaGrad), a number γ decays them (RMSprop), false
   takes plain steps of size `lr`."
  [q-dists accumulators gradients lr adagrad]
  (doseq [[addr g] gradients]
    (let [dist (get @q-dists addr)]
      (when (grad/has-gradient? dist)
        (let [g2 (mapv #(* % %) g)
              prev (get @accumulators addr)
              acc (cond (nil? prev) g2
                        (number? adagrad) (mapv #(+ (* adagrad %1) (* (- 1.0 adagrad) %2)) prev g2)
                        :else (mapv + prev g2))
              rate (if adagrad (mapv #(/ lr (+ 1e-8 (Math/sqrt %))) acc) lr)]
          (swap! accumulators assoc addr acc)
          (swap! q-dists assoc addr (grad/grad-step dist g rate)))))))

(defn bbvi-infer
  "Black Box Variational Inference (Ranganath et al., AISTATS 2014).

   Learns a mean-field q(z) = Π_addr q_addr, initialized to the priors, by
   stochastic ascent on the ELBO with the score-function estimator and
   control variates. Each iteration runs `num-particles` programs that
   sample latents from q and weight by p(x, y)/q(x).

   Args:
     model-task, num-particles, num-iterations
     opts: :base-lr (1.0) — step size at iteration t is
           base-lr / (t+1)^robbins-monro
           :robbins-monro (0.0)
           :adagrad (true) — true: AdaGrad, γ ∈ (0,1): RMSprop with decay γ,
           false: plain steps
           :executor

   Returns: Spin<EmpiricalMeasure> — the last iteration's importance-weighted
   samples from q; the learned q is under `:variational-dists`
   (see `get-variational-dists`)."
  [model-task num-particles num-iterations & [opts]]
  (spin
   (let [base-lr (or (:base-lr opts) 1.0)
         robbins-monro (or (:robbins-monro opts) 0.0)
         adagrad (get opts :adagrad true)
         q-dists (atom {})
         accumulators (atom {})
         kernel (->VariationalKernel q-dists)]
     (loop [iteration 0]
       (let [qs @q-dists
             measure (if (on-savepoints? opts)
                       (await (on-savepoints
                               (smc/smc model-task num-particles
                                        (assoc opts
                                               :resample-threshold 0.0
                                               :policy (itrace/policy {:draw (variational-draw q-dists)})))))
                       (await (kernel-infer model-task kernel num-particles
                                            (assoc opts :barrier-policy :none))))]
         (if (>= (inc iteration) num-iterations)
           (assoc measure :variational-dists @q-dists)
           (let [particles (m/get-particles measure)
                 grads (mapv (fn [[c _]]
                               (if (instance? org.replikativ.spindel.inference.measure.Sample c)
                                 (q-gradients (merge @q-dists qs) (m/get-trace c))
                                 (or (rtp/get-state c [:inference :q-grads]) {})))
                             particles)]
             (update-variational-dists! q-dists accumulators
                                        (aggregate-gradients grads (mapv second particles))
                                        (/ base-lr (Math/pow (inc iteration) robbins-monro))
                                        adagrad)
             (recur (inc iteration)))))))))

(defn get-variational-dists
  "The learned {address -> distribution} of a `bbvi-infer` result."
  [measure]
  (:variational-dists measure))
