(ns org.replikativ.spindel.inference.counterfactual-test
  "Counterfactuals against closed forms: mechanisms round-trip their noise,
  a linear-Gaussian twin is exact, a confounded one is exact whatever the
  posterior over the confounder, and the probability of necessity of a binary
  model matches its analytic value."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.inference.counterfactual :as cf]
            [org.replikativ.spindel.inference.mechanism :as mech]
            [org.replikativ.spindel.inference.measure :as m]
            [org.replikativ.spindel.inference.effects :refer [sample]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [anglican.runtime :as ar]))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [outcome (deref result 60000 ::timeout)]
      (when (= ::timeout outcome)
        (throw (ex-info "CPS operation timed out" {})))
      (if (= :ok (first outcome)) (second outcome) (throw (second outcome))))))

(def ^:private root (context/create-execution-context))

(defmacro ^:private model [& body]
  `(fn [] (binding [ec/*execution-context* root] (spin ~@body))))

(defn- close? [a b] (< (Math/abs (- a b)) 1e-9))

(deftest mechanisms-round-trip-their-noise
  (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG 1)
  (doseq [d [(ar/normal 2.0 3.0) (ar/uniform-continuous -1.0 4.0) (ar/exponential 1.5)]]
    (let [u (mech/noise d)]
      (is (close? u (mech/abduct d (mech/push d u))) (str (type d)))))
  (testing "discrete laws: abducted noise gives the value back"
    (doseq [d [(ar/flip 0.3) (ar/bernoulli 0.6) (ar/discrete [1.0 2.0 3.0])]]
      (dotimes [_ 50]
        (let [x (ar/sample* d)]
          (is (= x (mech/push d (mech/abduct d x))) (str (type d) " " x)))))))

(deftest a-linear-gaussian-twin-is-exact
  ;; X = Ux, Y = 2X + Uy. Seen X = 1, Y = 3 (so Uy = 1); had X been 2, Y = 5.
  (let [[pair] (await-cps (cf/counterfactual
                           (model (let [x (sample (ar/normal 0.0 1.0) :id :x)
                                        y (sample (ar/normal (* 2.0 x) 1.0) :id :y)]
                                    {:x x :y y}))
                           {:evidence {:x 1.0 :y 3.0} :interventions {:x {:do 2.0}}}))]
    (is (= {:x 1.0 :y 3.0} (:factual pair)))
    (is (close? 5.0 (:y (:counterfactual pair))))
    (is (= [] (:unaligned pair)))))

(deftest a-confounded-twin-is-exact-under-any-posterior
  ;; Z ~ N(0,1), X ~ N(Z,1), Y ~ N(X+Z,1). Given X = 1, Y = 2.5 the posterior
  ;; over Z is uncertain, but Y - X = Z + Uy is known: Y' = 2 + 1.5 = 3.5.
  (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG 2)
  (let [pairs (await-cps (cf/counterfactual
                          (model (let [z (sample (ar/normal 0.0 1.0) :id :z)
                                       x (sample (ar/normal z 1.0) :id :x)
                                       y (sample (ar/normal (+ x z) 1.0) :id :y)]
                                   {:z z :x x :y y}))
                          {:evidence {:x 1.0 :y 2.5} :interventions {:x {:do 2.0}} :particles 50}))]
    (is (< 1 (count (distinct (map (comp :z :factual) pairs)))) "Z is sampled, not fixed")
    (is (every? #(close? 3.5 (:y (:counterfactual %))) pairs))
    (is (every? #(= (:z (:factual %)) (:z (:counterfactual %))) pairs) "Z keeps its noise")))

(deftest the-probability-of-necessity-of-a-binary-cause
  ;; X ~ flip(.5); Y ~ flip(X ? 1 : .3). Seen X = Y = true: had X been false,
  ;; Y = [U < .3] with U | Y=true, X=true ~ U(0,1): P(Y' = false) = .7.
  (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG 3)
  (let [pairs (await-cps (cf/counterfactual
                          (model (let [x (sample (ar/flip 0.5) :id :x)
                                       y (sample (ar/flip (if x 1.0 0.3)) :id :y)]
                                   {:x x :y y}))
                          {:evidence {:x true :y true} :interventions {:x {:do false}} :particles 1500}))
        ws (m/normalize-log-weights (mapv :weight pairs))
        pn (reduce + (map (fn [p w] (if (:y (:counterfactual p)) 0.0 w)) pairs ws))]
    (is (< (Math/abs (- pn 0.7)) 0.04) (str "PN " pn))))

(deftest a-site-only-the-counterfactual-reaches-is-reported
  (let [[pair] (await-cps (cf/counterfactual
                           (model (let [b (sample (ar/flip 0.5) :id :b)]
                                    (if b (sample (ar/normal 0.0 1.0) :id :u) :none)))
                           {:evidence {:b false} :interventions {:b {:do true}}}))]
    (is (= :none (:factual pair)))
    (is (number? (:counterfactual pair)))
    (is (= [:u] (:unaligned pair)))))
