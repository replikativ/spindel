(ns org.replikativ.spindel.inference.measure
  "Measure abstraction for probabilistic programming.

  Measures represent probability distributions over execution traces.
  This is the foundation for compositional inference algorithms."
  (:require [replikativ.logging :as log]
            [org.replikativ.spindel.engine.protocols :as rtp]))

;; =============================================================================
;; PMeasure Protocol
;; =============================================================================

(defprotocol PMeasure
  "Protocol for probability measures over execution traces.

  A measure represents a distribution over execution contexts (traces).
  Different measure types enable different inference strategies:
  - EmpiricalMeasure: Weighted particle set (for SMC)
  - DiracMeasure: Single execution context (for forward sampling)
  - (Future) Parametric measures for variational inference"

  (measure-type [this]
    "Returns the type of measure: :empirical, :dirac, etc.")

  (sample-measure [this n]
    "Sample n execution contexts from this measure.

    Returns vector of [context log-weight] pairs.
    For DiracMeasure: returns n copies with uniform weight.
    For EmpiricalMeasure: samples from particles according to weights.")

  (log-marginal [this]
    "Estimate of log p(observations).

    For EmpiricalMeasure: log-sum-exp of particle weights.
    For DiracMeasure: the single context's log-weight.")

  (effective-sample-size [this]
    "Effective sample size (ESS) for particle degeneracy detection.

    ESS = (sum w_i)^2 / sum(w_i^2) where w_i are normalized weights.
    Low ESS indicates degeneracy -> trigger resampling.

    For DiracMeasure: returns 1.0 (perfect, no degeneracy).")

  (measure-stats [this query-fn]
    "Compute statistics over the measure using query-fn.

    query-fn: (fn [context] -> value)

    Returns map with :mean, :variance, :quantiles, etc.
    Useful for extracting posterior statistics."))

;; =============================================================================
;; Utility Functions
;; =============================================================================

(defn log-sum-exp
  "Numerically stable log-sum-exp.

  log(sum(exp(x_i))) = log-max + log(sum(exp(x_i - log-max)))"
  [log-weights]
  (when (empty? log-weights)
    (throw (ex-info "log-sum-exp requires non-empty sequence" {})))
  (let [log-max (apply max log-weights)
        sum-exp (reduce + (map #(Math/exp (- % log-max)) log-weights))]
    (+ log-max (Math/log sum-exp))))

(defn normalize-log-weights
  "Convert log-weights to normalized linear weights.

  Returns vector of weights summing to 1.0"
  [log-weights]
  (let [log-max (apply max log-weights)
        weights (mapv #(Math/exp (- % log-max)) log-weights)
        total (reduce + weights)]
    (mapv #(/ % total) weights)))

(defn compute-ess
  "Compute effective sample size from normalized weights.

  ESS = 1 / sum(w_i^2) for normalized weights"
  [weights]
  (let [sum-squares (reduce + (map #(* % %) weights))]
    (/ 1.0 sum-squares)))

(defn systematic-resample
  "Systematic resampling algorithm from Anglican.

  Low-variance resampling for particle filters.
  weights: normalized weights (sum to 1)
  n: number of particles to sample

  Returns vector of indices into original particle vector."
  [weights n]
  {:pre [(every? #(and (>= % 0) (<= % 1)) weights)
         (< (Math/abs (- (reduce + weights) 1.0)) 1e-6)]}
  (let [u (/ (rand) n)  ; Random offset
        cumsum (reductions + 0 weights)]
    (loop [i 0
           j 0
           indices []]
      (if (>= i n)
        indices
        (let [threshold (+ u (/ i n))]
          (if (< threshold (nth cumsum (inc j)))
            (recur (inc i) j (conj indices j))
            (recur i (inc j) indices)))))))

;; =============================================================================
;; DiracMeasure - Single Execution Context
;; =============================================================================

(defrecord DiracMeasure [context]
  PMeasure

  (measure-type [_]
    :dirac)

  (sample-measure [_ n]
    (let [log-weight (get-in context [:inference :log-weight] 0.0)]
      (vec (repeat n [context log-weight]))))

  (log-marginal [_]
    (get-in context [:inference :log-weight] 0.0))

  (effective-sample-size [_]
    1.0)

  (measure-stats [_ query-fn]
    (let [value (query-fn context)]
      {:mean value
       :variance 0.0
       :samples [value]
       :type :dirac})))

(defn dirac
  "Create a Dirac measure from a single execution context.

  Used for forward sampling and as initial measure."
  [context]
  (->DiracMeasure context))

;; =============================================================================
;; EmpiricalMeasure - Weighted Particle Set
;; =============================================================================

(defrecord EmpiricalMeasure [particles]
  ;; particles: vector of [context log-weight] pairs

  PMeasure

  (measure-type [_]
    :empirical)

  (sample-measure [_ n]
    (let [log-weights (mapv second particles)
          weights (normalize-log-weights log-weights)
          ;; Systematic resampling (low-variance)
          indices (systematic-resample weights n)]
      (mapv #(nth particles %) indices)))

  (log-marginal [_]
    (log-sum-exp (mapv second particles)))

  (effective-sample-size [_]
    (let [log-weights (mapv second particles)
          weights (normalize-log-weights log-weights)]
      (compute-ess weights)))

  (measure-stats [_ query-fn]
    (let [log-weights (mapv second particles)
          weights (normalize-log-weights log-weights)
          values (mapv (fn [[ctx _]] (query-fn ctx)) particles)
          mean (reduce + (map * weights values))
          variance (reduce + (map (fn [w v] (* w (Math/pow (- v mean) 2)))
                                  weights values))
          sorted (vec (sort values))
          n (count values)]
      {:mean mean
       :variance variance
       :std-dev (Math/sqrt variance)
       :samples values
       :weights weights
       :quantiles {:p50 (nth sorted (quot n 2))
                   :p025 (nth sorted (quot n 40))
                   :p975 (nth sorted (* 39 (quot n 40)))}
       :type :empirical})))

(defn empirical
  "Create an empirical measure from weighted particles.

  particles: vector of [context log-weight] pairs"
  [particles]
  {:pre [(vector? particles)
         (every? (fn [[ctx lw]] (and (map? ctx) (number? lw))) particles)]}
  (->EmpiricalMeasure particles))

;; =============================================================================
;; Helper Functions for Particle Manipulation
;; =============================================================================

(defn get-contexts
  "Extract execution contexts from measure."
  [measure]
  (case (measure-type measure)
    :dirac [(:context measure)]
    :empirical (mapv first (:particles measure))))

(defn get-log-weights
  "Extract log-weights from measure."
  [measure]
  (case (measure-type measure)
    :dirac [(get-in (:context measure) [:inference :log-weight] 0.0)]
    :empirical (mapv second (:particles measure))))

(defn get-particles
  "Extract raw particles (context, log-weight pairs) from measure.

  For DiracMeasure: returns single-element vector
  For EmpiricalMeasure: returns the particles vector"
  [measure]
  (case (measure-type measure)
    :dirac [(let [ctx (:context measure)]
              [ctx (get-in ctx [:inference :log-weight] 0.0)])]
    :empirical (:particles measure)))

(defn update-particles
  "Update particles in empirical measure.

  f: (fn [[context log-weight]] -> [new-context new-log-weight])"
  [measure f]
  {:pre [(= :empirical (measure-type measure))]}
  (let [new-particles (mapv f (:particles measure))]
    (empirical new-particles)))

(defn resample-if-needed
  "Resample particles if ESS drops below threshold.

  threshold: fraction of particle count (e.g., 0.5)
  Returns new measure (resampled if needed)."
  [measure threshold]
  (if (not= :empirical (measure-type measure))
    measure
    (let [n (count (:particles measure))
          ess (effective-sample-size measure)
          resample? (< ess (* threshold n))]
      (if resample?
        (do
          (log/debug :measure/resample {:ess ess :threshold (* threshold n) :n n})
          (let [resampled (sample-measure measure n)
                ;; Reset weights to uniform after resampling
                new-particles (mapv (fn [[ctx _]] [ctx 0.0]) resampled)]
            (empirical new-particles)))
        measure))))

;; =============================================================================
;; Context Value Extraction
;; =============================================================================

(defn get-value
  "Extract the program result from an execution context.

  The result is stored in [:inference :result] after execution completes.

  Args:
    context - ExecutionContext from inference

  Returns: The value returned by the probabilistic program"
  [context]
  (rtp/get-state context [:inference :result]))

;; =============================================================================
;; Print Methods (avoid StackOverflow from circular refs)
;; =============================================================================

#?(:clj
   (defmethod print-method EmpiricalMeasure [m ^java.io.Writer w]
     (.write w "#EmpiricalMeasure{")
     (.write w (str ":n " (count (:particles m))))
     (.write w (str ", :ess " (format "%.2f" (double (effective-sample-size m)))))
     (.write w (str ", :log-marginal " (format "%.4f" (double (log-marginal m)))))
     (.write w "}")))

#?(:clj
   (defmethod print-method DiracMeasure [m ^java.io.Writer w]
     (.write w "#DiracMeasure{")
     (.write w (str ":log-weight " (format "%.4f" (double (log-marginal m)))))
     (.write w "}")))
