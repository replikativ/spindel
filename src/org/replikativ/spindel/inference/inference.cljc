(ns org.replikativ.spindel.inference.inference
  "Compositional probabilistic inference algorithms.

  Every method runs a probabilistic program as a savepoint handler: SMC
  (`inference.smc`) for the particle methods — smc-infer,
  importance-sampling, pimh-infer, pgibbs-infer, pgas-infer, ipmcmc-infer,
  bbvi-infer and kernel-infer with a PInferenceKernel — and replay plus
  accept over traces (`inference.trace`) for the Markov-chain kernels.

  Pure inference (`:world-policy :fresh`, the default) runs in fresh worlds;
  `:world-policy :fork` in canonical forks of the caller's world (see
  `in-canonical-worlds`). Particle measures hold `Sample`s (result, trace,
  and a canonical particle's world descriptor).

  All functions return Spin<EmpiricalMeasure> for composability;
  post-processing is measure-centric (query, predict)."
  (:require [org.replikativ.spindel.inference.measure :as m]
            [org.replikativ.spindel.inference.random :as random]
            [org.replikativ.spindel.inference.hmc :as hmc]
            [org.replikativ.spindel.inference.kernel :as k]
            [org.replikativ.spindel.inference.smc :as smc]
            [org.replikativ.spindel.inference.gradient :as grad]
            [org.replikativ.spindel.inference.trace :as itrace]
            [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.world.scope :as world-scope]
            [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.engine.core :as rtc]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.state-backend :as backend]
            [org.replikativ.spindel.engine.executor :as sched]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]
            [replikativ.logging :as log]
            [anglican.runtime :as ar]
            [clojure.set :as set]))

(defmacro ^:private inference-spin [& body]
  `(spin-core/with-causal-descendant-egress (spin ~@body)))

;; =============================================================================
;; Markov chains: replay plus accept
;; =============================================================================

(defn- block-gibbs-options
  "Translate a BlockGibbsKernel into `itrace/mh-step` options. The classifier
  and the selector see the trace in its legacy shape; only latent
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
  "`itrace/mh-step` options of a Markov-chain kernel, or nil for kernels
  that decide sites of savepoint SMC."
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

(defn- project-posterior-context
  "A parentless immutable context holding what the posterior needs of
  `world`'s inference state: the world itself would retain its ancestry."
  [world]
  (assoc world
         :backend (backend/create-immutable-backend
                   {:inference (select-keys (rtp/get-state world [:inference])
                                            [:log-weight :trace :result :mcmc])}
                   {:source-fork-id (:fork-id world)
                    :projection :inference-posterior})
         :parent-ctx nil
         :bindings {}
         :metadata {:inference/projection true}
         :running nil
         :drain-active nil))

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
           [[(project-posterior-context world) 0.0]]))
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

(declare particles)

(defn- kernel-policy
  "An `inference.trace` policy that asks `kernel` (a PInferenceKernel) for
  every latent site's value; the value's `:log-weight-delta` (default 0) is
  what it adds to the particle's weight."
  [kernel]
  (itrace/policy
   {:draw (fn [sp _old-entry]
            (let [world (:savepoint/world sp)
                  {:keys [dist options]} (:savepoint/payload sp)
                  {:keys [value log-weight-delta]}
                  (k/step kernel world
                          {:source dist :options options :address (:savepoint/address sp)}
                          (itrace/legacy-trace (rtp/get-state world [:savepoint/trace])))]
              {:value value
               :log-proposal (- (ar/observe* dist value) (or log-weight-delta 0.0))}))}))

(defn kernel-infer
  "Run inference with a kernel.

  Markov-chain kernels (`single-site-mh-kernel`, `random-walk-mh-kernel`,
  `block-gibbs-kernel`, `hmc-kernel`) run `num-particles` independent chains.
  Any other PInferenceKernel runs savepoint SMC whose latent sites take the
  value the kernel's `step` gives (the prior kernel: a draw from the prior).

  Args:
  - model-task: Spin (from model function) - Probabilistic program to infer
  - kernel: a kernel (e.g., prior-kernel, single-site-mh-kernel)
  - num-particles: Number of particles (chains)
  - opts: Optional map with:
    - :barrier-policy - :every-observe (default, SMC) | :none (importance
      sampling)
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
            measure (await (kernel-infer model (prior-kernel) 100
                                         {:barrier-policy :none}))]
        (query measure identity)))"
  [model-task kernel num-particles & [opts]]
  (let [smc-opts (cond-> (dissoc opts :barrier-policy)
                   (= :none (:barrier-policy opts)) (assoc :resample-threshold 0.0))]
    (cond
      (mh-options kernel)
      ;; Markov-chain kernels are replay plus accept over traces; each of the
      ;; `num-particles` is an independent chain.
      (markov-chain-infer model-task kernel num-particles opts)

      (= :prior (k/kernel-id kernel))
      (particles model-task num-particles smc-opts)

      :else
      (particles model-task num-particles (assoc smc-opts :policy (kernel-policy kernel))))))

;; =============================================================================
;; Convenience Functions (Delegate to kernel-infer)
;; =============================================================================

(defn- world-policy
  "The `:world-policy` of `opts`, :fresh by default; refuses any other."
  [opts]
  (let [policy (get opts :world-policy :fresh)]
    (when-not (#{:fresh :fork} policy)
      (throw (ex-info "Unknown inference world policy"
                      {:type ::invalid-world-policy
                       :world-policy policy
                       :supported #{:fresh :fork}})))
    policy))

(defn- on-savepoints?
  "Whether a particle method whose canonical worlds are not on savepoints
  yet runs on savepoint SMC: pure inference in fresh worlds does."
  [opts]
  (= :fresh (world-policy opts)))

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

;; -----------------------------------------------------------------------------
;; Canonical particle worlds (`:world-policy :fork`)
;; -----------------------------------------------------------------------------
;;
;; The model runs in a frozen fork of the caller's world, owned by a scope of
;; its own; savepoint SMC opens its session there, so every particle world is
;; a fork of that root and sees the caller's systems as they were, and
;; nothing a particle writes reaches the caller. Each particle runs the whole
;; model (`smc/start-site`). When inference ends, however
;; it ends, the session is closed and the root discarded before the result
;; or error is delivered; particles keep their worlds' descriptors.

(defn- canonical-scopes
  "The scopes of a canonical inference: the root's, then the session's once
  it is open."
  [scope root]
  (cond-> [scope] (some-> root sp/session) (conj (:scope (sp/session root)))))

(defn- canonical-descriptors [scope root]
  (into [] (mapcat world-scope/descriptors) (canonical-scopes scope root)))

(defn- close-canonical!
  "CPS: close the session in `root` (cancelling and joining its worlds),
  then discard the root once its scope is quiescent — a root fork still in
  flight included. Idempotent."
  [scope root]
  (fn [resolve reject]
    (let [discard-root #((world-scope/discard-when-quiescent! scope) resolve reject)]
      (if-let [session (some-> root sp/session)]
        ((sp/close! session) (fn [_] (discard-root)) reject)
        (discard-root)))))

(defn- canonical-recovery
  "What a host needs when a canonical inference failed: the worlds'
  descriptors and the operations that finish their cleanup, should the
  automatic one have failed. Process-local."
  [scope root]
  (let [scopes (canonical-scopes scope root)
        session-scope (peek scopes)]
    {:status (:status @session-scope)
     :manager session-scope
     :await-quiescent (world-scope/await-quiescence session-scope)
     :cancel! #(doseq [s scopes] (world-scope/request-cancel! s))
     :discard! #(close-canonical! scope root)
     :descriptors (canonical-descriptors scope root)}))

(defn- with-world-descriptors
  "`measure` whose particles carry their worlds' settled descriptors."
  [measure descriptors]
  (let [by-id (into {} (map (juxt :fork/id identity)) descriptors)]
    (update measure :particles
            (fn [particles]
              (mapv (fn [[s w]]
                      [(if-let [id (:world-id s)]
                         (-> s (dissoc :world-id) (assoc :world-descriptor (get by-id id)))
                         s)
                       w])
                    particles)))))

(defn- in-canonical-worlds
  "Savepoint SMC (`smc/smc`) of `model-task` with `n` particles in canonical
  worlds of the caller's (see above). `:world-opts` are the forks' options
  (`:systems`, `:rights`, `:snapshots`); `:executor` the worlds' executor."
  [model-task n opts]
  (inference-spin
   (let [caller rtc/*execution-context*
         world-opts (or (:world-opts opts) {})
         scope (world-scope/create {:purpose :inference
                                    :fork-opts (cond-> world-opts
                                                 (:executor opts) (assoc :executor (:executor opts)))})
         root (volatile! nil)
         measure (volatile! nil)]
     (try
       (vreset! root (:child-ctx (await (fn [resolve reject]
                                          (world-scope/fork! scope caller resolve reject)))))
       (rtp/swap-state! @root [:inference :canonical?] (constantly true))
       (vreset! measure
                (await (smc/smc (binding [rtc/*execution-context* @root]
                                  ;; every particle runs the whole model: a
                                  ;; canonical model's effects may be random
                                  ;; without a sample site
                                  (spin (sp/savepoint smc/start-site nil)
                                        (await model-task)))
                                n
                                (-> opts
                                    (dissoc :world-policy :world-opts :executor)
                                    (assoc :root @root :purpose :particle
                                           :fork-opts world-opts :retain-released? true)))))
       (catch #?(:clj Throwable :cljs :default) e
         (throw (if (= spin-core/spin-cancelled (:type (ex-data e)))
                  e
                  (ex-info "Inference failed during particle execution"
                           {:type ::inference-failed
                            :world/recovery (canonical-recovery scope @root)}
                           e))))
       (finally
         (await-finalization (close-canonical! scope @root))))
     (with-world-descriptors @measure (canonical-descriptors scope @root)))))

(defn- particles
  "Savepoint SMC of `model-task` with `n` particles in the worlds `opts`'
  `:world-policy` names."
  [model-task n opts]
  (case (world-policy opts)
    :fresh (on-savepoints (smc/smc model-task n opts))
    :fork (in-canonical-worlds model-task n opts)))

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
  (particles model-task num-particles opts))

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
  ;; savepoint SMC that never resamples: ESS never falls below 0
  (particles model-task num-samples (assoc opts :resample-threshold 0.0)))

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
  "A sweep's particles (`Sample`s) with weights that sum to one, so sweeps
   can be pooled into one MCMC estimate."
  [measure]
  (let [ps (m/get-particles measure)
        lse (m/log-sum-exp (mapv second ps))]
    (mapv (fn [[s lw]] [s (- lw lse)]) ps)))

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
         (let [sweep (await (particles model-task num-particles
                                       (assoc opts :retained (smc/retained-choices retained-trace))))]
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

    ;; CSMC sweep with retained trace
    :else
    (particles model-task num-particles
               (assoc opts :retained (smc/retained-choices retained-trace)))))

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
  (if (on-savepoints? opts)
    (on-savepoints (smc/pgas model-task num-particles num-iterations opts))
    (csmc-chain model-task num-particles num-iterations (assoc opts :ancestor-sampling? true))))

;; =============================================================================
;; Black Box Variational Inference (BBVI)
;; =============================================================================

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
         accumulators (atom {})]
     (loop [iteration 0]
       (let [qs @q-dists
             measure (await (particles model-task num-particles
                                       (assoc opts
                                              :resample-threshold 0.0
                                              :policy (itrace/policy {:draw (variational-draw q-dists)}))))]
         (if (>= (inc iteration) num-iterations)
           (assoc measure :variational-dists @q-dists)
           (let [ps (m/get-particles measure)
                 grads (mapv (fn [[c _]] (q-gradients (merge @q-dists qs) (m/get-trace c)))
                             ps)]
             (update-variational-dists! q-dists accumulators
                                        (aggregate-gradients grads (mapv second ps))
                                        (/ base-lr (Math/pow (inc iteration) robbins-monro))
                                        adagrad)
             (recur (inc iteration)))))))))

(defn get-variational-dists
  "The learned {address -> distribution} of a `bbvi-infer` result."
  [measure]
  (:variational-dists measure))
