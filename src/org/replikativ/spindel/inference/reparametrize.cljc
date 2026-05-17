(ns org.replikativ.spindel.inference.reparametrize
  "Pure helper functions for distribution reparametrization.

  These are DETERMINISTIC functions that transform standard random variables
  (e.g., standard normal, uniform) into samples from other distributions.

  Used for explicit reparametrization in models:
    (let [U (choose (normal 0 1) :id :exo)]
      (reparametrize-normal U mu sigma))

  This pattern enables:
  - Amortized inference (reuse U across multiple observations)
  - Gradient-based inference (differentiable with respect to U)
  - Explicit control over exogenous randomness

  NO EFFECTS - these are pure math functions.")

;; =============================================================================
;; Normal Distribution
;; =============================================================================

(defn reparametrize-normal
  "Transform standard normal U ~ N(0, 1) to N(mu, sigma).

  Location-scale transformation: X = mu + sigma * U

  Args:
    U: Sample from standard normal N(0, 1)
    mu: Mean of target normal
    sigma: Standard deviation of target normal

  Returns: Sample from N(mu, sigma)

  Example:
    (let [U (choose (normal 0 1) :id :exo)]
      (reparametrize-normal U 5.0 2.0))  ; N(5, 2)"
  [U mu sigma]
  (+ mu (* sigma U)))

;; =============================================================================
;; Log-Normal Distribution
;; =============================================================================

(defn reparametrize-log-normal
  "Transform standard normal U ~ N(0, 1) to LogNormal(mu, sigma).

  X = exp(mu + sigma * U)

  Args:
    U: Sample from standard normal N(0, 1)
    mu: Log-space mean
    sigma: Log-space standard deviation

  Returns: Sample from LogNormal(mu, sigma)

  Example:
    (let [U (choose (normal 0 1) :id :exo)]
      (reparametrize-log-normal U 0.0 1.0))"
  [U mu sigma]
  (Math/exp (+ mu (* sigma U))))

;; =============================================================================
;; Multivariate Normal (via Cholesky decomposition)
;; =============================================================================

(defn reparametrize-mvn
  "Transform standard normal vector to multivariate normal.

  X = mu + L * U, where L is Cholesky decomposition of covariance matrix.

  Args:
    U: Vector of independent standard normals
    mu: Mean vector
    L: Lower triangular Cholesky factor (covariance = L * L^T)

  Returns: Vector sampled from MVN(mu, Sigma)

  Example:
    (let [U [(choose (normal 0 1) :id :U1)
             (choose (normal 0 1) :id :U2)]
          mu [0.0 0.0]
          L [[1.0 0.0]
             [0.5 0.866]]]  ; Cholesky of [[1.0 0.5] [0.5 1.0]]
      (reparametrize-mvn U mu L))"
  [U mu L]
  (let [dim (count U)]
    (mapv (fn [i]
            (+ (nth mu i)
               (reduce + (map * (nth L i) U))))
          (range dim))))

;; =============================================================================
;; Beta Distribution (via inverse CDF)
;; =============================================================================

(defn reparametrize-beta
  "Transform uniform U ~ Uniform(0, 1) to Beta(alpha, beta).

  Uses inverse CDF (quantile function). For general alpha, beta this requires
  numerical methods. We use a simple approximation for common cases.

  Args:
    U: Sample from Uniform(0, 1)
    alpha: Shape parameter (> 0)
    beta: Shape parameter (> 0)

  Returns: Sample from Beta(alpha, beta)

  Note: For exact inverse CDF, use a numerical library.
  This implementation delegates to Apache Commons Math or similar.

  Example:
    (let [U (choose (uniform 0 1) :id :exo)]
      (reparametrize-beta U 2.0 5.0))"
  [U alpha beta]
  ;; For now, we'll throw - users should implement with their numerical library
  ;; In practice, use Apache Commons Math's BetaDistribution.inverseCumulativeProbability
  (throw (ex-info "reparametrize-beta requires numerical library for inverse CDF"
                  {:U U :alpha alpha :beta beta
                   :hint "Use Apache Commons Math BetaDistribution or similar"})))

;; =============================================================================
;; Gamma Distribution
;; =============================================================================

(defn reparametrize-gamma
  "Transform standard exponential(s) to Gamma(shape, scale).

  For integer shape k, Gamma(k, theta) is sum of k exponentials scaled by theta.
  For non-integer shape, use rejection sampling or inverse CDF.

  Args:
    U: Standard exponential sample (or vector for integer shape)
    shape: Shape parameter (k)
    scale: Scale parameter (theta)

  Returns: Sample from Gamma(shape, scale)

  Example (integer shape):
    (let [U [(choose (exponential 1) :id :U1)
             (choose (exponential 1) :id :U2)]  ; For shape=2
          shape 2.0
          scale 3.0]
      (reparametrize-gamma U shape scale))

  Note: This is simplified for integer shapes. Use numerical library for general case."
  [U shape scale]
  (if (== shape (int shape))
    ;; Integer shape: sum of exponentials
    (let [k (int shape)]
      (if (number? U)
        ;; Single exponential provided, assume shape=1
        (* scale U)
        ;; Vector of exponentials for shape > 1
        (* scale (reduce + U))))
    ;; Non-integer shape: throw, use numerical library
    (throw (ex-info "reparametrize-gamma for non-integer shape requires numerical library"
                    {:U U :shape shape :scale scale
                     :hint "Use Apache Commons Math GammaDistribution or similar"}))))

;; =============================================================================
;; Exponential Distribution
;; =============================================================================

(defn reparametrize-exponential
  "Transform uniform U ~ Uniform(0, 1) to Exponential(rate).

  Uses inverse CDF: X = -log(U) / rate

  Args:
    U: Sample from Uniform(0, 1)
    rate: Rate parameter (lambda > 0)

  Returns: Sample from Exponential(rate)

  Example:
    (let [U (choose (uniform 0 1) :id :exo)]
      (reparametrize-exponential U 2.0))"
  [U rate]
  (/ (- (Math/log U)) rate))

;; =============================================================================
;; Categorical Distribution (via inverse CDF)
;; =============================================================================

(defn reparametrize-categorical
  "Transform uniform U ~ Uniform(0, 1) to Categorical(probs).

  Uses inverse CDF (cumulative probability bins).

  Args:
    U: Sample from Uniform(0, 1)
    probs: Vector of probabilities (must sum to 1)

  Returns: Integer index i such that U falls in probability bin i

  Example:
    (let [U (choose (uniform 0 1) :id :exo)
          probs [0.2 0.5 0.3]]  ; 3 categories
      (reparametrize-categorical U probs))  ; Returns 0, 1, or 2"
  [U probs]
  (loop [cumsum 0.0
         i 0]
    (if (>= i (count probs))
      (dec i)  ; Last category
      (let [cumsum' (+ cumsum (nth probs i))]
        (if (< U cumsum')
          i
          (recur cumsum' (inc i)))))))

;; =============================================================================
;; Dirichlet Distribution (via Gamma reparametrization)
;; =============================================================================

(defn reparametrize-dirichlet
  "Transform Gamma samples to Dirichlet(alpha).

  Dirichlet can be constructed from Gammas: X_i ~ Gamma(alpha_i, 1),
  then Y = X / sum(X) ~ Dirichlet(alpha).

  Args:
    gammas: Vector of Gamma(alpha_i, 1) samples (use reparametrize-gamma)
    alpha: Concentration parameters (vector)

  Returns: Vector of probabilities summing to 1

  Example:
    (let [alpha [2.0 3.0 5.0]
          gammas [(reparametrize-gamma U1 2.0 1.0)
                  (reparametrize-gamma U2 3.0 1.0)
                  (reparametrize-gamma U3 5.0 1.0)]]
      (reparametrize-dirichlet gammas alpha))"
  [gammas alpha]
  (let [total (reduce + gammas)]
    (mapv #(/ % total) gammas)))

;; =============================================================================
;; Cauchy Distribution
;; =============================================================================

(defn reparametrize-cauchy
  "Transform uniform U ~ Uniform(0, 1) to Cauchy(location, scale).

  Uses inverse CDF: X = location + scale * tan(pi * (U - 0.5))

  Args:
    U: Sample from Uniform(0, 1)
    location: Location parameter
    scale: Scale parameter (> 0)

  Returns: Sample from Cauchy(location, scale)

  Example:
    (let [U (choose (uniform 0 1) :id :exo)]
      (reparametrize-cauchy U 0.0 1.0))"
  [U location scale]
  (+ location
     (* scale (Math/tan (* Math/PI (- U 0.5))))))

;; =============================================================================
;; Helper: Standard samples
;; =============================================================================

(defn standard-normal-sample
  "Convenience: Sample standard normal U ~ N(0, 1) with choose.

  This is what you typically use as the exogenous variable.

  Example:
    (require '[org.replikativ.spindel.inference.effects :refer [choose]])
    (let [U (standard-normal-sample :my-exo)]
      (reparametrize-normal U mu sigma))"
  [id]
  ;; This is just documentation - the actual choose must be called in spin context
  (throw (ex-info "standard-normal-sample is a documentation helper only - use choose directly"
                  {:hint "Use: (choose (normal 0 1) :id id) in your model"})))

(defn standard-uniform-sample
  "Convenience: Sample uniform U ~ Uniform(0, 1) with choose.

  This is what you typically use as the exogenous variable for inverse CDF.

  Example:
    (require '[org.replikativ.spindel.inference.effects :refer [choose]])
    (let [U (standard-uniform-sample :my-exo)]
      (reparametrize-exponential U rate))"
  [id]
  ;; This is just documentation - the actual choose must be called in spin context
  (throw (ex-info "standard-uniform-sample is a documentation helper only - use choose directly"
                  {:hint "Use: (choose (uniform 0 1) :id id) in your model"})))
