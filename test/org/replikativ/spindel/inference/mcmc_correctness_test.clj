(ns org.replikativ.spindel.inference.mcmc-correctness-test
  "MCMC against analytic posteriors, on models whose sites are NOT laid out as
  'all samples, then all observes'. Each model isolates one thing a kernel
  that resumes a stored continuation must get right:

  - an observe UPSTREAM of the moved site stays in the acceptance ratio;
  - a KEPT sample downstream of the moved site is rescored under its new
    distribution;
  - a move that changes control flow leaves no entry of the branch not taken,
    and is accepted with the trans-dimensional ratio."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.inference.inference :as infer]
            [org.replikativ.spindel.inference.kernel :as k]
            [org.replikativ.spindel.inference.measure :as measure]
            [org.replikativ.spindel.inference.effects :refer [sample observe]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :as aw]
            [org.replikativ.spindel.engine.core :as rtc]
            [org.replikativ.spindel.engine.context :as ctx]
            [anglican.runtime :as ar]))

(defn- finals
  "The final state of `n-chains` independently seeded chains of `model-fn`."
  [model-fn kernel-fn n-chains]
  (mapv (fn [seed]
          (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG (long seed))
          (let [root (ctx/create-execution-context)]
            (try
              (binding [rtc/*execution-context* root]
                (let [meas @(spin (aw/await (infer/kernel-infer (model-fn) (kernel-fn) 1 {})))]
                  (measure/get-value (first (first (measure/get-particles meas))))))
              (finally (ctx/stop-context! root)))))
        (range 1 (inc n-chains))))

(defn- stats [xs]
  (let [n (count xs)
        mean (/ (reduce + xs) n)]
    {:mean mean
     :var (/ (reduce + (map #(let [d (- % mean)] (* d d)) xs)) n)}))

(def ^:private kernels
  [["single-site-mh" #(k/single-site-mh-kernel 200)]
   ["random-walk-mh" #(k/random-walk-mh-kernel 200 {:step-size 0.8})]])

;; Two independent conjugate pairs, interleaved:
;;   x ~ N(0,1), 2 | x ~ N(x,1)   =>  x | y ~ N(1, 1/2)
;;   w ~ N(0,1), -2 | w ~ N(w,1)  =>  w | y ~ N(-1, 1/2)
(defn- interleaved-model []
  (spin
   (let [x (sample (ar/normal 0.0 1.0))]
     (observe (ar/normal x 1.0) 2.0)
     (let [w (sample (ar/normal 0.0 1.0))]
       (observe (ar/normal w 1.0) -2.0)
       [x w]))))

(deftest an-observe-upstream-of-the-moved-site-stays-in-the-ratio
  (doseq [[label kernel-fn] kernels]
    (testing label
      (let [chains (finals interleaved-model kernel-fn 120)
            x (stats (map first chains))
            w (stats (map second chains))]
        (is (< (Math/abs (- (:mean x) 1.0)) 0.2) (str "x mean " (:mean x)))
        (is (< (Math/abs (- (:mean w) -1.0)) 0.2) (str "w mean " (:mean w)))
        (is (< 0.3 (:var x) 0.75) (str "x var " (:var x)))
        (is (< 0.3 (:var w) 0.75) (str "w var " (:var w)))))))

;; A chain: x ~ N(0,1), z | x ~ N(x,1), 3 | z ~ N(z,1).
;;   y | x ~ N(x,2)  =>  x | y ~ N(1, 2/3);   z | y ~ N(2, 2/3)
(defn- chain-model []
  (spin
   (let [x (sample (ar/normal 0.0 1.0))
         z (sample (ar/normal x 1.0))]
     (observe (ar/normal z 1.0) 3.0)
     [x z])))

(deftest a-kept-downstream-sample-is-rescored
  (doseq [[label kernel-fn] kernels]
    (testing label
      (let [chains (finals chain-model kernel-fn 120)
            x (stats (map first chains))
            z (stats (map second chains))]
        (is (< (Math/abs (- (:mean x) 1.0)) 0.25) (str "x mean " (:mean x)))
        (is (< (Math/abs (- (:mean z) 2.0)) 0.25) (str "z mean " (:mean z)))
        (is (< 0.4 (:var x) 1.0) (str "x var " (:var x)))
        (is (< 0.4 (:var z) 1.0) (str "z var " (:var z)))))))

;; A mixture whose second component has an extra latent:
;;   b ~ flip(1/2);  b: 1 ~ N(1,1)        evidence N(1; 1, 1) = 0.3989
;;                  !b: u ~ N(0,1), 1 ~ N(u,1)   evidence N(1; 0, 2) = 0.2197
;;   P(b | y) = 0.3989 / (0.3989 + 0.2197) = 0.645
(defn- branching-model []
  (spin
   (let [b (sample (ar/flip 0.5))]
     (if b
       (observe (ar/normal 1.0 1.0) 1.0)
       (let [u (sample (ar/normal 0.0 1.0))]
         (observe (ar/normal u 1.0) 1.0)))
     b)))

(deftest a-move-across-branches-uses-the-trans-dimensional-ratio
  (let [chains (finals branching-model #(k/single-site-mh-kernel 200) 400)
        p (/ (count (filter true? chains)) (double (count chains)))]
    (is (< (Math/abs (- p 0.645)) 0.07) (str "P(b | y) " p))))
