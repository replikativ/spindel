(ns org.replikativ.spindel.inference.streaming-smc-test
  "Online SMC against the Kalman filter: a random walk x_t = x_{t-1} + N(0,1)
  observed as y_t ~ N(x_t, 1), its observations pushed one at a time. After
  each push the particle filter's x_t must match the Kalman filtering
  distribution, and its evidence the Kalman marginal likelihood."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.inference.smc :as smc]
            [org.replikativ.spindel.inference.measure :as m]
            [org.replikativ.spindel.inference.effects :refer [sample]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [anglican.runtime :as ar]))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [outcome (deref result 60000 ::timeout)]
      (when (= ::timeout outcome)
        (throw (ex-info "CPS operation timed out" {})))
      (if (= :ok (first outcome)) (second outcome) (throw (second outcome))))))

(def ^:private ys [0.8 1.9 1.2 3.0 2.5])

(defn- random-walk [root]
  (binding [ec/*execution-context* root]
    (spin
     (loop [t 0 x (sample (ar/normal 0.0 1.0) :id [:x 0])]
       (sample (ar/normal x 1.0) :id [:y t] :stream true)
       (if (= t (dec (count ys)))
         x
         (recur (inc t) (sample (ar/normal x 1.0) :id [:x (inc t)])))))))

(defn- kalman
  "[mean var log-likelihood] of the filtering distribution after each y."
  [ys]
  (loop [[y & more] ys, prior-mean 0.0, prior-var 1.0, ll 0.0, acc []]
    (if-not y
      acc
      (let [s (+ prior-var 1.0)
            k (/ prior-var s)
            mean (+ prior-mean (* k (- y prior-mean)))
            var (* (- 1.0 k) prior-var)
            ll (+ ll (ar/observe* (ar/normal prior-mean (Math/sqrt s)) y))]
        (recur more mean (+ var 1.0) ll (conj acc [mean var ll]))))))

(defn- moments [measure t]
  (let [ps (m/get-particles measure)
        ws (m/normalize-log-weights (mapv second ps))
        xs (mapv (fn [[s _]] (:value (get (m/get-trace s) [:x t]))) ps)
        mean (reduce + (map * ws xs))]
    [mean (reduce + (map (fn [w x] (* w (let [d (- x mean)] (* d d)))) ws xs))]))

(deftest online-smc-tracks-the-kalman-filter
  (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG 5)
  (let [root (context/create-execution-context)
        truth (kalman ys)
        first-step (await-cps (smc/stream (random-walk root) 3000
                                          {:executor (executor/thread-pool-executor {:threads 1})}))]
    (is (not (:done? first-step)) "waiting for the first observation")
    (loop [step first-step t 0]
      (if (= t (count ys))
        (do (is (:done? step) "every particle returned after the last observation")
            (is (< (Math/abs (- (m/log-marginal (:measure step)) (nth (peek truth) 2))) 0.15)
                (str "evidence " (m/log-marginal (:measure step)) " vs " (nth (peek truth) 2))))
        (let [step' (await-cps ((:push step) (nth ys t)))
              [mean var] (moments (:measure step') t)
              [kmean kvar] (nth truth t)]
          (testing (str "after y_" t)
            (is (< (Math/abs (- mean kmean)) 0.08) (str "mean " mean " vs " kmean))
            (is (< (Math/abs (- var kvar)) 0.06) (str "var " var " vs " kvar)))
          (recur step' (inc t)))))))

(deftest batch-smc-refuses-stream-sites
  (let [root (context/create-execution-context)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"stream sites"
                          (await-cps (smc/smc (random-walk root) 10))))))
