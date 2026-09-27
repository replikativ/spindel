(ns org.replikativ.spindel.inference.intervention-test
  "Selectors, and interventions by selector, against closed-form answers.

  The model is confounded: Z ~ N(0,1), X ~ N(Z,1), Y ~ N(X+Z,1). Seeing X = 1
  says something about Z (E[Y | X=1] = 1.5); setting X = 1 does not
  (E[Y | do(X=1)] = 1)."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.select :as sel]
            [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.inference.trace :as itrace]
            [org.replikativ.spindel.inference.measure :as m]
            [org.replikativ.spindel.inference.effects :refer [sample]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [anglican.runtime :as ar]))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [outcome (deref result 20000 ::timeout)]
      (when (= ::timeout outcome)
        (throw (ex-info "CPS operation timed out" {})))
      (if (= :ok (first outcome)) (second outcome) (throw (second outcome))))))

(defn- run
  "One run of `(make)` under `policy-opts`; returns [result log-weight trace]."
  [make policy-opts]
  (let [root (context/create-execution-context)
        session (sp/open! root {:fork-opts {:systems :none} :retain-released? false})
        t (await-cps (trace/run session (binding [ec/*execution-context* root] (make))
                                (itrace/policy policy-opts)))]
    (await-cps (sp/close! session))
    [(:trace/result t) (itrace/log-weight t) t]))

(defn- scm []
  (spin
   (let [z (sample (ar/normal 0.0 1.0) :id :z)
         x (sample (ar/normal z 1.0) :id :x)
         y (sample (ar/normal (+ x z) 1.0) :id :y)]
     {:z z :x x :y y})))

(defn- weighted-mean
  "Self-normalized importance estimate of E[f] over `n` runs."
  [n make policy-opts f]
  (let [runs (vec (repeatedly n #(run make policy-opts)))
        ws (m/normalize-log-weights (mapv second runs))]
    (reduce + (map (fn [[r] w] (* w (f r))) runs ws))))

(deftest selectors-match-names-paths-and-sites
  (let [d (fn [address path] {:address address :path path :site :inference/choose})]
    (is (sel/selects? (sel/id :mu) (d :mu [:mu])))
    (is (sel/selects? (sel/path [:step :* :x]) (d [:step 3 :x] [:step 3 :x])))
    (is (not (sel/selects? (sel/path [:step :* :x]) (d [:step 3 :y] [:step 3 :y]))))
    (is (sel/selects? (sel/prefix [:step]) (d [:step 3 :y] [:step 3 :y])))
    (is (sel/selects? (sel/site :inference/choose) (d :a [:a])))
    (is (sel/selects? (sel/union (sel/id :a) (sel/id :b)) (d :b [:b])))
    (is (not (sel/selects? (sel/intersection (sel/id :a) (sel/site :other)) (d :a [:a]))))
    (is (sel/selects? (sel/complement* (sel/id :a)) (d :b [:b])))))

(deftest seeing-is-not-doing
  (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG 3)
  (testing "conditioning on X = 1: E[Y | X=1] = 1.5"
    (is (< (Math/abs (- 1.5 (weighted-mean 3000 scm {:constraints {:x 1.0}} :y))) 0.1)))
  (testing "do(X = 1) by name: E[Y | do(X=1)] = 1, and X scores nothing"
    (let [[r w] (run scm {:interventions {:x {:do 1.0}}})]
      (is (= 1.0 (:x r)))
      (is (= 0.0 w)))
    (is (< (Math/abs (- 1.0 (weighted-mean 3000 scm {:interventions {(sel/id :x) {:do 1.0}}} :y))) 0.1))))

(deftest soft-shift-and-policy-interventions
  (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG 5)
  (testing "a new mechanism: X ~ N(3, 0.1) gives E[Y] = 3"
    (is (< (Math/abs (- 3.0 (weighted-mean 2000 scm {:interventions {:x {:dist (ar/normal 3.0 0.1)}}} :y))) 0.1)))
  (testing "a shift: X := X + 2 gives E[Y] = 2"
    (is (< (Math/abs (- 2.0 (weighted-mean 2000 scm {:interventions {:x {:shift 2.0}}} :y))) 0.12)))
  (testing "a policy of earlier choices: X := 2Z gives Y ~ N(3Z, 1), Var[Y] = 10"
    (let [ys (mapv (comp :y first) (repeatedly 3000 #(run scm {:interventions {:x {:policy (fn [c] (* 2.0 (:z c)))}}})))
          mean (/ (reduce + ys) (count ys))
          var (/ (reduce + (map #(let [d (- % mean)] (* d d)) ys)) (count ys))]
      (is (< (Math/abs mean) 0.15) (str "mean " mean))
      (is (< (Math/abs (- var 10.0)) 0.8) (str "var " var)))))

(deftest interventions-select-by-path
  (let [units (fn []
                (spin
                 (loop [i 0 acc []]
                   (if (= i 3)
                     acc
                     (recur (inc i) (conj acc (sample (ar/normal 0.0 1.0) :id [:unit i :x])))))))
        [r] (run units {:interventions {(sel/path [:unit :* :x]) {:do 7.0}}})]
    (is (= [7.0 7.0 7.0] r))))
