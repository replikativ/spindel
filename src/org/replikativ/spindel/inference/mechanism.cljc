(ns org.replikativ.spindel.inference.mechanism
  "Sample sites as structural equations x = f(u), u exogenous noise.

  A distribution is read as a mechanism: `noise` draws u, `push` computes the
  value from it, `abduct` goes back from a value to its noise. For an
  invertible mechanism (location-scale, inverse CDF of a continuous law)
  abduction is exact. For a discrete one, many u give the same value, and
  `abduct` draws u from its posterior given the value — here under the
  inverse-CDF convention x = F⁻¹(u), u ~ U(0,1), under which that posterior is
  uniform on the value's CDF interval. Which convention a discrete site uses
  changes counterfactual answers and cannot be told from data, so it is fixed
  here and documented rather than guessed.

  Parameters come from the distribution at the site, so replaying a site with
  its old u under new parents is the counterfactual value."
  (:require [org.replikativ.spindel.inference.measure :as m]
            [anglican.runtime :as ar]))

(defprotocol PMechanism
  (noise [d] "A fresh draw of the site's exogenous noise.")
  (push [d u] "The value the mechanism gives noise `u`.")
  (abduct [d x] "Noise that gives value `x`: exact when the mechanism is
    invertible, a draw from the posterior over u otherwise."))

(defn- uniform-between [a b] (+ a (* (- b a) (m/uniform01))))

(extend-type anglican.runtime.normal-distribution
  PMechanism
  (noise [_] (ar/sample* (ar/normal 0.0 1.0)))
  (push [d u] (+ (:mean d) (* (:sd d) u)))
  (abduct [d x] (/ (- x (:mean d)) (:sd d))))

(extend-type anglican.runtime.uniform-continuous-distribution
  PMechanism
  (noise [_] (m/uniform01))
  (push [d u] (+ (:min d) (* (- (:max d) (:min d)) u)))
  (abduct [d x] (/ (- x (:min d)) (- (:max d) (:min d)))))

(extend-type anglican.runtime.exponential-distribution
  PMechanism
  (noise [_] (m/uniform01))
  (push [d u] (/ (- (Math/log (- 1.0 u))) (:rate d)))
  (abduct [d x] (- 1.0 (Math/exp (- (* (:rate d) x))))))

;; flip(p) = [u < p]: true takes u ∈ [0, p), false u ∈ [p, 1)
(extend-type anglican.runtime.flip-distribution
  PMechanism
  (noise [_] (m/uniform01))
  (push [d u] (< u (:p d)))
  (abduct [d x] (if x (uniform-between 0.0 (:p d)) (uniform-between (:p d) 1.0))))

(extend-type anglican.runtime.bernoulli-distribution
  PMechanism
  (noise [_] (m/uniform01))
  (push [d u] (if (< u (:p d)) 1 0))
  (abduct [d x] (if (= 1 x) (uniform-between 0.0 (:p d)) (uniform-between (:p d) 1.0))))

;; discrete(w) = the first index whose cumulative weight exceeds u·Σw
(extend-type anglican.runtime.discrete-distribution
  PMechanism
  (noise [_] (m/uniform01))
  (push [d u]
    (let [target (* u (:total-weight d))]
      (loop [i 0 acc 0.0 [w & more] (:weights d)]
        (let [acc' (+ acc w)]
          (if (or (< target acc') (empty? more)) i (recur (inc i) acc' more))))))
  (abduct [d x]
    (let [total (:total-weight d)
          lo (reduce + 0.0 (take x (:weights d)))]
      (uniform-between (/ lo total) (/ (+ lo (nth (:weights d) x)) total)))))

(defn mechanism?
  "Whether distribution `d` can be read as a mechanism."
  [d]
  (satisfies? PMechanism d))
