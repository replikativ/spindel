(ns org.replikativ.spindel.inference.kernel
  "Kernel abstraction for compositional inference.

  Kernels are measure-preserving transformations that form the building
  blocks of inference algorithms. Sequential composition of kernels
  implements complex inference strategies like SMC.

  This namespace also defines PInferenceKernel - kernels that operate
  at checkpoints during execution (not post-processing on measures).

  Two protocol layers:
  - `PKernel`        — operates on measures (post hoc). Used for
                       resampling, MCMC moves, etc.
  - `PInferenceKernel` — operates on particles *at checkpoints* during
                       execution. The KernelCoordinator
                       (`coordinator.cljc`) calls
                       `decide-checkpoint` whenever a particle hits
                       `sample` or `observe`; the kernel returns
                       `[:assign value]`, `[:modify ...]`, or
                       `[:iterate ...]` to drive the particle forward.
                       This is what makes importance sampling vs SMC
                       a choice of kernel, not a choice of engine."
  (:require [org.replikativ.spindel.inference.measure :as m]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [replikativ.logging :as log]
            [anglican.runtime :as ar]))

;; =============================================================================
;; PKernel Protocol
;; =============================================================================

(defprotocol PKernel
  "Protocol for measure-preserving kernels.

  Kernels transform measures while (ideally) preserving the target distribution.
  Different kernels implement different inference operations:
  - ImportanceKernel: Forward execution with weight updates
  - ResampleKernel: Low-variance resampling
  - MCMCKernel: Metropolis-Hastings proposals
  - (Future) RejuvenateKernel: MCMC moves between resampling"

  (apply-kernel [this measure]
    "Apply this kernel to a measure, returning a new measure.

    This is the core operation for inference composition.
    Kernels should be stateless - all state lives in measures."))

;; =============================================================================
;; Kernel Composition
;; =============================================================================

(defn compose-kernels
  "Sequentially compose kernels: (k3 . k2 . k1)(measure).

  Returns a new kernel that applies kernels left-to-right."
  [& kernels]
  (reify PKernel
    (apply-kernel [_ measure]
      (reduce (fn [m kernel]
                (apply-kernel kernel m))
              measure
              kernels))))

(defn conditional-kernel
  "Apply kernel only if predicate on measure returns true.

  pred: (fn [measure] -> boolean)
  If pred returns false, returns measure unchanged."
  [pred kernel]
  (reify PKernel
    (apply-kernel [_ measure]
      (if (pred measure)
        (apply-kernel kernel measure)
        measure))))

;; =============================================================================
;; ImportanceKernel - Forward Execution with Weighting
;; =============================================================================

(defrecord ImportanceKernel [exec-fn]
  PKernel

  (apply-kernel [_ measure]
    (case (m/measure-type measure)
      :dirac
      (let [context (:context measure)
            new-context (exec-fn context)]
        (m/dirac new-context))

      :empirical
      (let [new-particles
            (mapv (fn [[ctx log-weight]]
                    (let [new-ctx (exec-fn ctx)
                          new-log-weight (get-in new-ctx [:inference :log-weight] 0.0)]
                      [new-ctx new-log-weight]))
                  (:particles measure))]
        (m/empirical new-particles)))))

(defn importance-kernel
  "Create importance sampling kernel with execution function."
  [exec-fn]
  (->ImportanceKernel exec-fn))

;; =============================================================================
;; ResampleKernel - Particle Resampling
;; =============================================================================

(defrecord ResampleKernel [threshold]
  PKernel

  (apply-kernel [_ measure]
    (case (m/measure-type measure)
      :dirac
      measure

      :empirical
      (m/resample-if-needed measure threshold))))

(defn resample-kernel
  "Create resampling kernel with ESS threshold."
  [threshold]
  {:pre [(and (> threshold 0) (<= threshold 1))]}
  (->ResampleKernel threshold))

;; =============================================================================
;; MCMCKernel - Metropolis-Hastings Proposals
;; =============================================================================

(defn mh-chain
  "Run Metropolis-Hastings chain for steps iterations."
  [proposal-fn context steps]
  (loop [current-ctx context
         step 0]
    (if (>= step steps)
      current-ctx
      (let [proposed-ctx (proposal-fn current-ctx)
            current-log-weight (get-in current-ctx [:inference :log-weight] 0.0)
            proposed-log-weight (get-in proposed-ctx [:inference :log-weight] 0.0)
            log-accept-ratio (- proposed-log-weight current-log-weight)
            accept? (or (>= log-accept-ratio 0)
                        (< (Math/log (m/uniform01)) log-accept-ratio))]
        (log/trace :mcmc/mh-step {:step step
                                  :accept? accept?
                                  :log-accept-ratio log-accept-ratio})
        (recur (if accept? proposed-ctx current-ctx)
               (inc step))))))

(defrecord MCMCKernel [proposal-fn steps]
  PKernel

  (apply-kernel [_ measure]
    (case (m/measure-type measure)
      :dirac
      (let [context (:context measure)
            new-context (mh-chain proposal-fn context steps)]
        (m/dirac new-context))

      :empirical
      (let [new-particles
            (mapv (fn [[ctx log-weight]]
                    (let [new-ctx (mh-chain proposal-fn ctx steps)
                          new-log-weight (get-in new-ctx [:inference :log-weight] 0.0)]
                      [new-ctx new-log-weight]))
                  (:particles measure))]
        (m/empirical new-particles)))))

(defn mcmc-kernel
  "Create MCMC kernel with proposal function."
  [proposal-fn steps]
  {:pre [(> steps 0)]}
  (->MCMCKernel proposal-fn steps))

;; =============================================================================
;; Conditional Resample Kernel (Common Pattern)
;; =============================================================================

(defn conditional-resample
  "Resample kernel that only triggers when ESS is low."
  [threshold]
  (conditional-kernel
   (fn [measure]
     (and (= :empirical (m/measure-type measure))
          (let [n (count (:particles measure))
                ess (m/effective-sample-size measure)]
            (< ess (* threshold n)))))
   (resample-kernel threshold)))

;; =============================================================================
;; Utility Kernels
;; =============================================================================

(defn map-contexts
  "Create kernel that maps function over contexts."
  [f]
  (reify PKernel
    (apply-kernel [_ measure]
      (case (m/measure-type measure)
        :dirac
        (m/dirac (f (:context measure)))

        :empirical
        (let [new-particles
              (mapv (fn [[ctx log-weight]]
                      [(f ctx) log-weight])
                    (:particles measure))]
          (m/empirical new-particles))))))

(defn reset-weights
  "Create kernel that resets all log-weights to 0."
  []
  (map-contexts
   (fn [ctx]
     (assoc-in ctx [:inference :log-weight] 0.0))))

(defn filter-particles
  "Create kernel that filters particles by predicate."
  [pred]
  (reify PKernel
    (apply-kernel [_ measure]
      (case (m/measure-type measure)
        :dirac
        (if (pred (:context measure))
          measure
          (throw (ex-info "Dirac measure filtered out" {})))

        :empirical
        (let [filtered (filterv (fn [[ctx _]] (pred ctx))
                                (:particles measure))]
          (when (empty? filtered)
            (throw (ex-info "All particles filtered out" {})))
          (m/empirical filtered))))))

;; =============================================================================
;; InferenceKernel Protocol - Checkpoint-Level Inference Control
;; =============================================================================

(defprotocol PInferenceKernel
  "Protocol for kernels that operate at checkpoints during program execution.

  Unlike PKernel (which transforms measures post-hoc), a PInferenceKernel
  decides what value to assign at each random variable/observation point of a
  particle the KernelCoordinator drives.

  Markov-chain kernels (`single-site-mh-kernel`, `random-walk-mh-kernel`,
  `block-gibbs-kernel`) implement `kernel-id` only: they are descriptions that
  `inference/kernel-infer` runs as replay plus accept over traces
  (`inference.trace`), not through the coordinator."

  (kernel-id [this]
    "Unique identifier for this kernel type (e.g., :prior, :single-site-mh).")

  (step [this ctx checkpoint trace]
    "Process a checkpoint with the current trace.

    Returns {:action :assign, :value v}.")

  (on-complete [this ctx trace result]
    "Called when program execution completes.

    Returns {:action :done, :trace trace, :result result, :log-weight w}, or
    {:action :iterate} to run the whole program again in place."))

;; =============================================================================
;; PriorKernel - Simple Forward Sampling (Importance Sampling)
;; =============================================================================

(defrecord PriorKernel []
  PInferenceKernel

  (kernel-id [_] :prior)

  (step [_ ctx checkpoint trace]
    (let [{:keys [source options]} checkpoint
          {:keys [observe init]} options
          value (cond
                  (some? observe) observe
                  (some? init) init
                  :else (ar/sample* source))]
      {:action :assign, :value value}))

  (on-complete [_ ctx trace result]
    {:action :done
     :trace trace
     :result result
     :log-weight (or (rtp/get-state ctx [:inference :log-weight]) 0.0)}))

(defn prior-kernel
  "Create a PriorKernel for simple importance sampling."
  []
  (->PriorKernel))

;; =============================================================================
;; SingleSiteMHKernel - Lightweight Metropolis-Hastings
;; =============================================================================

(defrecord SingleSiteMHKernel [num-iterations]
  PInferenceKernel
  (kernel-id [_] :single-site-mh))

(defn single-site-mh-kernel
  "Create SingleSiteMHKernel for lightweight Metropolis-Hastings."
  [num-iterations]
  {:pre [(pos-int? num-iterations)]}
  (->SingleSiteMHKernel num-iterations))

;; =============================================================================
;; RandomWalkMHKernel
;; =============================================================================

(defn- random-walk-propose
  [current-value step-size]
  (+ current-value (* step-size (ar/sample* (ar/normal 0 1)))))

(defrecord RandomWalkMHKernel [num-iterations step-size]
  PInferenceKernel
  (kernel-id [_] :random-walk-mh))

(defn random-walk-mh-kernel
  "Create RandomWalkMHKernel for continuous variables.

  Metropolis-Hastings with a symmetric Gaussian proposal on one unobserved
  site per iteration; the program is replayed from that site with every other
  site held at its trace value and rescored, and the proposal is accepted on
  the ratio of joint densities (see `inference.trace/mh-log-ratio`)."
  [num-iterations & [{:keys [step-size] :or {step-size 0.1}}]]
  {:pre [(pos-int? num-iterations) (pos? step-size)]}
  (->RandomWalkMHKernel num-iterations step-size))

;; =============================================================================
;; BlockGibbsKernel
;; =============================================================================

(defprotocol PBlockSelector
  "Protocol for selecting which block to update at each iteration."
  (select-block [this trace iteration]
    "Returns block-id (keyword) for which block to update this iteration."))

(defprotocol PBlockKernel
  "Protocol for block-level proposal kernels."
  (propose-block [this trace block-addresses]
    "Returns {addr -> proposed-value} for addresses in this block."))

(defrecord RoundRobinSelector [block-ids]
  PBlockSelector
  (select-block [_ _trace iteration]
    (nth block-ids (mod iteration (count block-ids)))))

(defn round-robin-selector
  [block-ids]
  {:pre [(seq block-ids) (every? keyword? block-ids)]}
  (->RoundRobinSelector (vec block-ids)))

(defrecord RandomSelector [block-ids]
  PBlockSelector
  (select-block [_ _trace _iteration]
    (m/pick-uniformly block-ids)))

(defn random-selector
  [block-ids]
  {:pre [(seq block-ids) (every? keyword? block-ids)]}
  (->RandomSelector (vec block-ids)))

(defrecord PriorBlockKernel []
  PBlockKernel
  (propose-block [_ trace block-addresses]
    (into {}
          (map (fn [addr]
                 (let [entry (get trace addr)
                       dist (:distribution entry)]
                   [addr (ar/sample* dist)]))
               block-addresses))))

(defn prior-block-kernel [] (->PriorBlockKernel))

(defrecord RandomWalkBlockKernel [step-size]
  PBlockKernel
  (propose-block [_ trace block-addresses]
    (into {}
          (map (fn [addr]
                 (let [entry (get trace addr)
                       current (:value entry)
                       proposed (random-walk-propose current step-size)]
                   [addr proposed]))
               block-addresses))))

(defn random-walk-block-kernel
  [& [{:keys [step-size] :or {step-size 0.1}}]]
  {:pre [(pos? step-size)]}
  (->RandomWalkBlockKernel step-size))

(defrecord BlockGibbsKernel
           [num-iterations block-selector block-kernels address-classifier]
  PInferenceKernel
  (kernel-id [_] :block-gibbs))

(defn block-gibbs-kernel
  "Create a BlockGibbsKernel for block Gibbs sampling."
  [num-iterations block-selector block-kernels address-classifier]
  {:pre [(pos-int? num-iterations)
         (satisfies? PBlockSelector block-selector)
         (map? block-kernels)
         (fn? address-classifier)]}
  (->BlockGibbsKernel num-iterations block-selector block-kernels address-classifier))
