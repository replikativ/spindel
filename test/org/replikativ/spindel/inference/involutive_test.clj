(ns org.replikativ.spindel.inference.involutive-test
  "Involutive MCMC against conjugate posteriors: a random walk written as an
  involution, and a scale move whose Jacobian matters — without it the chain
  settles on the wrong posterior."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.inference.involutive :as inv]
            [org.replikativ.spindel.inference.gfi :as gfi]
            [org.replikativ.spindel.inference.effects :refer [sample observe]]
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

(def ^:private root (context/create-execution-context))

(defn- chain
  "Run `n` moves from a simulated trace of `model`; the values of site `a`
  after `burn` moves."
  [model move n burn a]
  (loop [t (await-cps (gfi/simulate model)) i 0 xs []]
    (if (= i n)
      (do (await-cps (gfi/close! t)) xs)
      (let [{t' :trace} (await-cps (inv/step t move))]
        (recur t' (inc i) (if (>= i burn) (conj xs (get-in t' [:trace/entries a :value])) xs))))))

(defn- mean-var [xs]
  (let [n (count xs) mu (/ (reduce + xs) n)]
    [mu (/ (reduce + (map #(let [d (- % mu)] (* d d)) xs)) n)]))

(deftest a-random-walk-is-an-involution
  ;; x ~ N(0,1), 2 ~ N(x,1)  =>  x | y ~ N(1, 1/2).  (x, u) -> (x+u, -u).
  (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG 4)
  (let [model (binding [ec/*execution-context* root]
                (spin (let [x (sample (ar/normal 0.0 1.0) :id :x)]
                        (observe (ar/normal x 1.0) 2.0 :id :y)
                        x)))
        q (ar/normal 0.0 0.8)
        move {:propose (fn [_] (let [u (ar/sample* q)] {:aux u :log-q (ar/observe* q u)}))
              :log-q (fn [_ u] (ar/observe* q u))
              :involution (fn [{x :x} u] {:choices {:x (+ x u)} :aux (- u) :log-jacobian 0.0})}
        [mu var] (mean-var (chain model move 4000 500 :x))]
    (is (< (Math/abs (- mu 1.0)) 0.1) (str "mean " mu))
    (is (< (Math/abs (- var 0.5)) 0.1) (str "var " var))))

(defn- gamma-poisson []
  ;; λ ~ Gamma(2, 1), 5 ~ Poisson(λ)  =>  λ | y ~ Gamma(7, 2): mean 3.5
  (binding [ec/*execution-context* root]
    (spin (let [l (sample (ar/gamma 2.0 1.0) :id :l)]
            (observe (ar/poisson l) 5 :id :y)
            l))))

(defn- scale-move
  "(λ, s) -> (λ·s, 1/s), log s ~ U(-1, 1): q(s) = 1/(2s) on [e⁻¹, e].
  |det ∂(λs, 1/s)/∂(λ, s)| = 1/s."
  [with-jacobian?]
  (let [log-q (fn [_ s] (- (Math/log (* 2.0 s))))]
    {:propose (fn [_] (let [s (Math/exp (ar/sample* (ar/uniform-continuous -1.0 1.0)))]
                        {:aux s :log-q (log-q nil s)}))
     :log-q log-q
     :involution (fn [{l :l} s] {:choices {:l (* l s)} :aux (/ 1.0 s)
                                 :log-jacobian (if with-jacobian? (- (Math/log s)) 0.0)})}))

(deftest a-scale-move-needs-its-jacobian
  (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG 6)
  (let [[mu] (mean-var (chain (gamma-poisson) (scale-move true) 4000 500 :l))]
    (is (< (Math/abs (- mu 3.5)) 0.25) (str "with the Jacobian: mean " mu)))
  (testing "leaving it out targets another law"
    (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG 6)
    (let [[mu] (mean-var (chain (gamma-poisson) (scale-move false) 4000 500 :l))]
      (is (> (Math/abs (- mu 3.5)) 0.3) (str "without: mean " mu)))))

(deftest the-numerical-jacobian-of-the-scale-move
  (doseq [[l s] [[2.0 1.5] [0.3 0.5] [7.0 2.7]]]
    (is (< (Math/abs (- (- (Math/log s))
                        (inv/fd-log-jacobian (fn [[l s]] [(* l s) (/ 1.0 s)]) [l s])))
           1e-5))))
