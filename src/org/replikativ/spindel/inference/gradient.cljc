(ns org.replikativ.spindel.inference.gradient
  "Gradient protocol for variational inference.

  Provides grad-log and grad-step for distributions, enabling:
  - Black Box Variational Inference (BBVI)
  - Amortized inference with learned proposals

  Gradients are w.r.t. unconstrained parameters for numerical stability:
  - Normal: (mean, log-std)
  - Gamma/Beta: (log-shape, log-rate) / (log-alpha, log-beta)
  - Flip: logit(p)"
  (:require [anglican.runtime :as ar]))

;; =============================================================================
;; Math Helpers
;; =============================================================================

(defn digamma
  "Digamma function psi(x) = d/dx ln(Gamma(x)).
   Asymptotic expansion for x >= 1."
  [x]
  (assert (>= x 0.0) "digamma requires x >= 0")
  (if (<= x 0.0)
    ##-Inf
    (let [partial-sum (if (< x 1) (/ -1.0 x) 0.0)
          x (if (< x 1) (+ x 1.0) x)]
      (+ partial-sum
         (Math/log x)
         (/ -1.0 (* 2 x))
         (/ -1.0 (* 12 (Math/pow x 2)))
         (/ 1.0 (* 120 (Math/pow x 4)))
         (/ -1.0 (* 252 (Math/pow x 6)))))))

(defn sigmoid [x]
  (/ 1.0 (+ 1.0 (Math/exp (- x)))))

(defn logit [p]
  (Math/log (/ p (- 1.0 p))))

(defn finite? [x]
  (and (number? x)
       (not (#?(:clj Double/isNaN :cljs js/isNaN) x))
       (not (#?(:clj Double/isInfinite :cljs (fn [v] (or (= v ##Inf) (= v ##-Inf)))) x))))

(defn positive-finite? [x]
  (and (finite? x) (> x 0.0)))

;; =============================================================================
;; Gradient Protocol
;; =============================================================================

(defprotocol PDistGradient
  "Protocol for computing gradients of log probability."
  (grad-log [dist]
    "Returns (fn [x] gradient-vector) for gradient of log p(x) w.r.t. parameters.")
  (grad-step [dist gradient learning-rate]
    "Returns updated distribution after gradient step.
     gradient: vector of gradients w.r.t. unconstrained parameters
     learning-rate: scalar or vector of per-parameter rates"))

;; =============================================================================
;; Normal Distribution
;; =============================================================================

;; Parameterized by (mean, log-std) for unconstrained optimization
(extend-type anglican.runtime.normal-distribution
  PDistGradient
  (grad-log [dist]
    (let [mu (:mean dist)
          sigma (:sd dist)]
      (fn [x]
        ;; d/d(mu) log N(x|mu,sigma) = (x - mu) / sigma^2
        ;; d/d(log-sigma) log N(x|mu,sigma) = -1 + (x-mu)^2 / sigma^2
        [(/ (- x mu) (* sigma sigma))
         (+ -1.0 (/ (* (- x mu) (- x mu)) (* sigma sigma)))])))

  (grad-step [dist grad lr]
    (let [lr (if (number? lr) [lr lr] lr)
          mu (:mean dist)
          log-sigma (Math/log (:sd dist))
          new-mu (+ mu (* (first lr) (first grad)))
          new-log-sigma (+ log-sigma (* (second lr) (second grad)))
          new-sigma (Math/exp new-log-sigma)]
      (if (positive-finite? new-sigma)
        (ar/normal new-mu new-sigma)
        dist))))  ; Return unchanged if update invalid

;; =============================================================================
;; Gamma Distribution
;; =============================================================================

;; Parameterized by (log-shape, log-rate) for positivity constraints
(extend-type anglican.runtime.gamma-distribution
  PDistGradient
  (grad-log [dist]
    (let [alpha (:shape dist)
          beta (:rate dist)]
      (fn [x]
        ;; Transform to log-space gradients
        ;; d/d(log-alpha) = alpha * (log(beta) + log(x) - digamma(alpha))
        ;; d/d(log-beta) = beta * (alpha/beta - x)
        [(* alpha (+ (Math/log beta) (Math/log x) (- (digamma alpha))))
         (* beta (- (/ alpha beta) x))])))

  (grad-step [dist grad lr]
    (let [lr (if (number? lr) [lr lr] lr)
          log-alpha (Math/log (:shape dist))
          log-beta (Math/log (:rate dist))
          new-log-alpha (+ log-alpha (* (first lr) (first grad)))
          new-log-beta (+ log-beta (* (second lr) (second grad)))
          new-alpha (Math/exp new-log-alpha)
          new-beta (Math/exp new-log-beta)]
      (if (and (positive-finite? new-alpha) (positive-finite? new-beta))
        (ar/gamma new-alpha new-beta)
        dist))))

;; =============================================================================
;; Beta Distribution
;; =============================================================================

;; Parameterized by (log-alpha, log-beta)
(extend-type anglican.runtime.beta-distribution
  PDistGradient
  (grad-log [dist]
    (let [a (:alpha dist)
          b (:beta dist)
          digamma-sum (digamma (+ a b))]
      (fn [x]
        ;; Natural gradient in log-space
        [(* a (+ digamma-sum (- (Math/log (max x 1e-12)) (digamma a))))
         (* b (+ digamma-sum (- (Math/log (max (- 1.0 x) 1e-12)) (digamma b))))])))

  (grad-step [dist grad lr]
    (let [lr (if (number? lr) [lr lr] lr)
          log-a (Math/log (:alpha dist))
          log-b (Math/log (:beta dist))
          new-log-a (+ log-a (* (first lr) (first grad)))
          new-log-b (+ log-b (* (second lr) (second grad)))
          new-a (Math/exp new-log-a)
          new-b (Math/exp new-log-b)]
      (if (and (positive-finite? new-a) (positive-finite? new-b))
        (ar/beta new-a new-b)
        dist))))

;; =============================================================================
;; Flip (Bernoulli) Distribution
;; =============================================================================

;; Parameterized by logit(p) for unconstrained optimization
(extend-type anglican.runtime.flip-distribution
  PDistGradient
  (grad-log [dist]
    (let [p (:p dist)
          q (- 1.0 p)]
      (fn [x]
        ;; d/d(logit(p)) log Bernoulli(x|p)
        ;; = p*q * (x/p - (1-x)/q) = p*q * (if x 1/p -1/q)
        [(* p q (if x (/ 1.0 p) (/ -1.0 q)))])))

  (grad-step [dist grad lr]
    (let [lr (if (number? lr) (first (if (sequential? lr) lr [lr])) lr)
          z (logit (:p dist))
          new-z (+ z (* lr (first grad)))
          new-p (sigmoid new-z)]
      (if (and (> new-p 0.0) (< new-p 1.0))
        (ar/flip new-p)
        dist))))

;; =============================================================================
;; Exponential Distribution
;; =============================================================================

;; Parameterized by log-rate
(extend-type anglican.runtime.exponential-distribution
  PDistGradient
  (grad-log [dist]
    (let [beta (:rate dist)]
      (fn [x]
        ;; d/d(log-beta) = beta * (1/beta - x)
        [(* beta (- (/ 1.0 beta) x))])))

  (grad-step [dist grad lr]
    (let [lr (if (number? lr) (first (if (sequential? lr) lr [lr])) lr)
          log-beta (Math/log (:rate dist))
          new-log-beta (+ log-beta (* lr (first grad)))
          new-beta (Math/exp new-log-beta)]
      (if (positive-finite? new-beta)
        (ar/exponential new-beta)
        dist))))

;; =============================================================================
;; Dirichlet Distribution
;; =============================================================================

;; Parameterized by log-alpha vector
(extend-type anglican.runtime.dirichlet-distribution
  PDistGradient
  (grad-log [dist]
    (let [alpha (:alpha dist)
          sum-alpha (reduce + alpha)
          digamma-sum (digamma sum-alpha)]
      (fn [x]
        ;; d/d(log-alpha_i) = alpha_i * (digamma(sum) + log(x_i) - digamma(alpha_i))
        (mapv (fn [ai xi]
                (* ai (+ digamma-sum
                        (- (Math/log (max xi 1e-12))
                           (digamma ai)))))
              alpha x))))

  (grad-step [dist grad lr]
    (let [lr (if (number? lr) (vec (repeat (count (:alpha dist)) lr)) (vec lr))
          log-alpha (mapv #(Math/log %) (:alpha dist))
          new-log-alpha (mapv (fn [la g l] (+ la (* l g))) log-alpha grad lr)
          new-alpha (mapv #(Math/exp %) new-log-alpha)]
      (if (every? positive-finite? new-alpha)
        (ar/dirichlet new-alpha)
        dist))))

;; =============================================================================
;; Discrete (Categorical) Distribution
;; =============================================================================

;; Parameterized by log-weights (softmax)
(extend-type anglican.runtime.discrete-distribution
  PDistGradient
  (grad-log [dist]
    (let [w (vec (:weights dist))
          total (reduce + w)
          p (mapv #(/ % total) w)
          K (count w)]
      (fn [x]
        ;; d/d(log-w_i) = 1(i=x) - p_i
        (mapv (fn [i pi] (- (if (= i x) 1.0 0.0) pi))
              (range K) p))))

  (grad-step [dist grad lr]
    (let [lr (if (number? lr) (vec (repeat (count (:weights dist)) lr)) (vec lr))
          log-w (mapv #(Math/log (max % 1e-12)) (:weights dist))
          new-log-w (mapv (fn [lw g l] (+ lw (* l g))) log-w grad lr)
          new-w (mapv #(Math/exp %) new-log-w)]
      (if (every? positive-finite? new-w)
        (ar/discrete new-w)
        dist))))

;; =============================================================================
;; Uniform Distribution (non-differentiable - return zero gradients)
;; =============================================================================

(extend-type anglican.runtime.uniform-continuous-distribution
  PDistGradient
  (grad-log [_dist]
    ;; Uniform has constant density - gradient is zero
    (fn [_x] [0.0 0.0]))
  (grad-step [dist _grad _lr]
    ;; Cannot update uniform - return unchanged
    dist))

;; =============================================================================
;; Helpers
;; =============================================================================

(defn has-gradient?
  "Check if distribution type has gradient implemented."
  [dist]
  (satisfies? PDistGradient dist))

(defn compute-gradient
  "Compute gradient of log p(x) for distribution.
   Returns nil if gradient not implemented."
  [dist x]
  (when (has-gradient? dist)
    ((grad-log dist) x)))
