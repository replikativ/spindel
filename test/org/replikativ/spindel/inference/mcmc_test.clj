(ns org.replikativ.spindel.inference.mcmc-test
  "What a Metropolis-Hastings kernel must do, checked against the
   properties that were broken until the replay restored its slice state:
   the trace stays the size of the model, every site is reachable, moves are
   random-walk steps, a proposal outside the prior's support is rejected, and
   on a conjugate model the chain lands on the analytic posterior.

   Every run here is one particle from a seed, so it is bit-reproducible."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.inference.inference :as infer]
            [org.replikativ.spindel.inference.kernel :as k]
            [org.replikativ.spindel.inference.measure :as measure]
            [org.replikativ.spindel.inference.effects :refer [sample observe]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :as aw]
            [org.replikativ.spindel.engine.core :as rtc]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [anglican.runtime :as ar]))

(defn- run-chain
  "One seeded single-particle random-walk MH run. Returns the final particle
   context plus the run's value and log-weight."
  [model-fn iterations step-size seed]
  (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG (long seed))
  (let [root (ctx/create-execution-context)]
    (try (binding [rtc/*execution-context* root]
           (let [meas @(spin (aw/await (infer/kernel-infer (model-fn)
                                                            (k/random-walk-mh-kernel iterations {:step-size step-size})
                                                            1 {})))
                 [c lw] (first (measure/get-particles meas))]
             (let [mh (rtp/get-state c [:inference :rw-mcmc])]
               {:ctx c :value (measure/get-value c) :log-weight lw
                :mh (assoc mh :acceptance-rate
                           (/ (double (:acceptance-count mh 0))
                              (max 1 (:completed-iterations mh 0))))})))
         (finally (ctx/stop-context! root)))))

(def visited (atom []))

(defn- three-site-model []
  (spin
    (let [a (sample (ar/uniform-continuous -5.0 5.0))
          b (sample (ar/uniform-continuous -5.0 5.0))
          c (sample (ar/uniform-continuous -5.0 5.0))]
      (swap! visited conj [a b c])
      (observe (ar/normal a 0.5) 1.0)
      (observe (ar/normal b 0.5) 2.0)
      (observe (ar/normal c 0.5) 3.0)
      [a b c])))

(deftest replay-keeps-the-trace-the-size-of-the-model
  (reset! visited [])
  (let [{:keys [ctx mh]} (run-chain three-site-model 30 0.4 7)
        trace (rtp/get-state ctx [:inference :trace])
        vs @visited
        step-size 0.4]
    (is (= 6 (count trace)) "three samples and three observes, however many replays")
    (is (= 3 (count (remove :observed? (vals trace)))))
    (is (= 31 (count vs)) "one initial run and one replay per iteration")
    (testing "every site is reachable"
      (doseq [site [first second last]]
        (is (> (count (distinct (map site vs))) 3) (str site))))
    (testing "moves are random-walk steps, not fresh prior draws"
      ;; Between consecutive program runs at most ONE site changes, by a
      ;; Gaussian step. A run that re-sampled from the prior would jump the
      ;; whole range.
      (let [jumps (for [[x y] (partition 2 1 vs) site [0 1 2]]
                    (Math/abs (- (double (nth y site)) (double (nth x site)))))]
        (is (zero? (count (filter #(> % (* 5 step-size)) jumps))))))
    (testing "acceptance is a real rate, not a count of no-ops"
      (is (< 0.05 (:acceptance-rate mh) 0.95) (str (:acceptance-rate mh))))))

(defn- conjugate-model []
  ;; prior N(0,1), one observation y = 2 with σ = 1 → posterior N(1, 1/2)
  (spin
    (let [mu (sample (ar/normal 0.0 1.0))]
      (observe (ar/normal mu 1.0) 2.0)
      mu)))

(deftest a-chain-lands-on-the-analytic-posterior
  ;; 60 independent seeded chains of 80 steps each; their end points are
  ;; 60 draws from whatever the kernel targets. The analytic posterior has
  ;; mean 1 and variance 1/2.
  (let [finals (mapv #(:value (run-chain conjugate-model 80 0.8 %)) (range 1 61))
        n (count finals)
        mean (/ (reduce + finals) n)
        var (/ (reduce + (map #(let [d (- % mean)] (* d d)) finals)) n)]
    (is (< (Math/abs (- mean 1.0)) 0.2) (str "mean " mean))
    (is (< 0.25 var 0.85) (str "variance " var))))

(defn- bounded-model []
  ;; prior U(0,1); the likelihood pulls toward 0.95, so an unguarded random
  ;; walk would drift past 1.0
  (spin
    (let [p (sample (ar/uniform-continuous 0.0 1.0))]
      (observe (ar/normal p 0.1) 0.95)
      p)))

(deftest a-proposal-outside-the-prior-is-rejected
  (doseq [seed (range 1 13)]
    (let [{:keys [value mh]} (run-chain bounded-model 60 0.3 seed)]
      (is (<= 0.0 value 1.0) (str "seed " seed " left the support: " value))
      (is (< (:acceptance-rate mh) 0.95) (str "seed " seed " accepted almost everything")))))

(deftest single-site-mh-also-lands-on-the-analytic-posterior
  ;; The prior-proposal kernel: same replay machinery, likelihood-only
  ;; acceptance (the prior cancels against the proposal). 60 seeded chains
  ;; of 80 steps on the conjugate model.
  (let [run1 (fn [seed]
               (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG (long seed))
               (let [root (ctx/create-execution-context)]
                 (try (binding [rtc/*execution-context* root]
                        (let [meas @(spin (aw/await (infer/kernel-infer (conjugate-model)
                                                                         (k/single-site-mh-kernel 80)
                                                                         1 {})))]
                          (measure/get-value (first (first (measure/get-particles meas))))))
                      (finally (ctx/stop-context! root)))))
        finals (mapv run1 (range 1 61))
        n (count finals)
        mean (/ (reduce + finals) n)
        var (/ (reduce + (map #(let [d (- % mean)] (* d d)) finals)) n)]
    (is (< (Math/abs (- mean 1.0)) 0.2) (str "mean " mean))
    (is (< 0.25 var 0.85) (str "variance " var))))
