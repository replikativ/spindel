(ns org.replikativ.spindel.inference.mcmc-correctness-test
  "MCMC against analytic posteriors, on models whose sites are NOT laid out as
  'all samples, then all observes'. Each model isolates one thing a kernel
  that returns to a site of a program must get right:

  - an observe UPSTREAM of the moved site stays in the acceptance ratio;
  - a KEPT sample downstream of the moved site is rescored under its new
    distribution;
  - a move that changes control flow leaves no entry of the branch not taken,
    and is accepted with the trans-dimensional ratio;
  - a kept value that fell out of its support is drawn again only when the
    reverse move would draw again too.

  One long chain per case, every state after burn-in a sample. The states are
  correlated, so the tolerances are wide for their count; each was checked to
  reject the specific wrong ratio it is there for."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.inference.trace :as itrace]
            [org.replikativ.spindel.inference.inference :as infer]
            [org.replikativ.spindel.inference.kernel :as k]
            [org.replikativ.spindel.inference.measure :as measure]
            [org.replikativ.spindel.inference.effects :refer [sample observe]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :as aw]
            [org.replikativ.spindel.engine.core :as rtc]
            [org.replikativ.spindel.engine.context :as ctx]
            [anglican.runtime :as ar]))

(defn- await-cps [operation timeout-ms]
  (let [result (promise)]
    (operation #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [outcome (deref result timeout-ms ::timeout)]
      (when (= ::timeout outcome)
        (throw (ex-info "CPS operation timed out" {})))
      (if (= :ok (first outcome)) (second outcome) (throw (second outcome))))))

(defn- states
  "The results of `steps` states of one seeded chain of `model-fn`, after
  `burn-in`."
  [model-fn step-opts steps burn-in seed]
  (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG (long seed))
  (let [root (ctx/create-execution-context)
        session (sp/open! root {:fork-opts {:systems :none} :retain-released? false})
        seen (atom [])]
    (try
      (let [initial (await-cps (trace/run session
                                          (binding [rtc/*execution-context* root] (model-fn))
                                          (itrace/policy)
                                          {:anchor? itrace/anchor?})
                               20000)]
        (await-cps (itrace/mh-chain initial (+ burn-in steps)
                                    (assoc step-opts :on-step
                                           (fn [{current :trace}]
                                             (swap! seen conj (:trace/result current)))))
                   600000)
        (subvec @seen burn-in))
      (finally
        (await-cps (sp/close! session) 20000)
        (ctx/close-context! root)))))

(defn- stats [xs]
  (let [n (count xs)
        mean (/ (reduce + xs) n)]
    {:mean mean
     :var (/ (reduce + (map #(let [d (- % mean)] (* d d)) xs)) n)}))

(def ^:private kernels
  [["single-site, prior proposal" {}]
   ["single-site, random walk" {:propose (itrace/random-walk-proposal 0.8)}]])

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
  (doseq [[label step-opts] kernels]
    (testing label
      (let [chain (states interleaved-model step-opts 2500 200 1)
            x (stats (map first chain))
            w (stats (map second chain))]
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
  (doseq [[label step-opts] kernels]
    (testing label
      (let [chain (states chain-model step-opts 3000 300 2)
            x (stats (map first chain))
            z (stats (map second chain))]
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
  (let [chain (states branching-model {} 4000 200 3)
        p (/ (count (filter true? chain)) (double (count chain)))]
    (is (< (Math/abs (- p 0.645)) 0.06) (str "P(b | y) " p))))

;; Two supports that overlap: s ~ flip(1/2); x ~ U(0,3) if s else U(2,5);
;; 1 | x ~ N(x,1).
;;   evidence(s)  = (Phi(2) - Phi(-1)) / 3 = 0.81859 / 3
;;   evidence(!s) = (Phi(4) - Phi(1))  / 3 = 0.15863 / 3
;;   P(s | y) = 0.8377
;; Flipping s keeps x when x is in the overlap and draws it again when it is
;; not; a redraw INTO the overlap cannot be undone (the way back would keep
;; it), so it must be refused.
(defn- overlapping-model []
  (spin
   (let [s (sample (ar/flip 0.5))
         x (sample (if s (ar/uniform-continuous 0.0 3.0) (ar/uniform-continuous 2.0 5.0)))]
     (observe (ar/normal x 1.0) 1.0)
     s)))

(deftest a-redraw-the-reverse-move-would-keep-is-refused
  (let [chain (states overlapping-model {} 5000 200 4)
        p (/ (count (filter true? chain)) (double (count chain)))]
    (is (< (Math/abs (- p 0.8377)) 0.05) (str "P(s | y) " p))))

;; The same through the public entry point, with independent chains.
(deftest kernel-infer-runs-the-markov-chain-kernels-as-independent-chains
  (doseq [[label kernel] [["single-site" (k/single-site-mh-kernel 120)]
                          ["random-walk" (k/random-walk-mh-kernel 120 {:step-size 0.8})]]]
    (testing label
      (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG 5)
      (let [root (ctx/create-execution-context)]
        (try
          (binding [rtc/*execution-context* root]
            (let [meas @(spin (aw/await (infer/kernel-infer (interleaved-model) kernel 60 {})))
                  finals (map (comp measure/get-value first) (measure/get-particles meas))
                  x (stats (map first finals))]
              (is (= 60 (count finals)))
              (is (< (Math/abs (- (:mean x) 1.0)) 0.3) (str "x mean " (:mean x)))))
          (finally (ctx/close-context! root)))))))
