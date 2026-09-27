(ns org.replikativ.spindel.inference.gfi-test
  "Gen's weight identities for `inference.gfi`, checked by hand on small
  models, and MH-by-selection against an analytic posterior."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.inference.gfi :as gfi]
            [org.replikativ.spindel.inference.trace :as itrace]
            [org.replikativ.spindel.inference.measure :as m]
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

(defmacro ^:private with-root [[root] & body]
  `(let [~root (context/create-execution-context)]
     (try
       ~@body
       (finally
         (context/close-context! ~root)))))

(defn- lp [dist v] (ar/observe* dist v))

(defn- close? [a b] (< (Math/abs (- a b)) 1e-9))

(defn- hierarchical
  "x ~ N(0,1), z | x ~ N(x,1), y = 2 | z ~ N(z,1): x | y ~ N(2/3, 2/3)."
  [root]
  (binding [ec/*execution-context* root]
    (spin
     (let [x (sample (ar/normal 0.0 1.0) :id :x)
           z (sample (ar/normal x 1.0) :id :z)]
       (observe (ar/normal z 1.0) 2.0 :id :y)
       x))))

(defn- switch
  "Which latent exists depends on b."
  [root]
  (binding [ec/*execution-context* root]
    (spin
     (let [b (sample (ar/flip 0.5) :id :b)
           v (if b
               (sample (ar/normal 0.0 1.0) :id :v0)
               (sample (ar/normal 5.0 1.0) :id :v1))]
       (observe (ar/normal v 1.0) 5.0 :id :y)
       b))))

(deftest assess-is-the-log-joint
  (with-root [root]
    (let [{:keys [weight result]} (await-cps (gfi/assess (hierarchical root) {:x 0.5 :z 1.5}))]
      (is (= 0.5 result))
      (is (close? weight (+ (lp (ar/normal 0.0 1.0) 0.5)
                            (lp (ar/normal 0.5 1.0) 1.5)
                            (lp (ar/normal 1.5 1.0) 2.0)))))
    (testing "a free sample site is an error"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"every sample site"
                            (await-cps (gfi/assess (hierarchical root) {:x 0.5})))))))

(deftest generate-weighs-by-the-constrained-and-observed-sites
  (with-root [root]
    (let [{t :trace w :weight} (await-cps (gfi/generate (hierarchical root) {:z 1.5}))
          x (:trace/result t)]
      (is (close? w (+ (lp (ar/normal x 1.0) 1.5) (lp (ar/normal 1.5 1.0) 2.0))))
      (is (= [:x] (itrace/latent-addresses t)))
      (await-cps (gfi/close! t)))))

(deftest update-keeps-rescores-and-discards
  (with-root [root]
    (testing "a constrained upstream site: z is kept and rescored, nothing fresh"
      (let [{t :trace} (await-cps (gfi/generate (hierarchical root) {:x 0.5 :z 1.5}))
            {t' :trace w :weight d :discard} (await-cps (gfi/update t {:x -0.5}))]
        (is (= -0.5 (:trace/result t')))
        (is (close? w (- (+ (lp (ar/normal 0.0 1.0) -0.5) (lp (ar/normal -0.5 1.0) 1.5))
                         (+ (lp (ar/normal 0.0 1.0) 0.5) (lp (ar/normal 0.5 1.0) 1.5)))))
        (is (= {:x 0.5} d) "the overwritten value of a constrained choice")
        (await-cps (gfi/close! t))))
    (testing "a branch change: the old branch's site is discarded, the new one drawn"
      (let [{t :trace} (await-cps (gfi/generate (switch root) {:b true :v0 0.3}))
            {t' :trace w :weight d :discard} (await-cps (gfi/update t {:b false}))
            v1 (get (itrace/choices t') :v1)]
        (is (false? (:trace/result t')))
        (is (number? v1))
        (is (not (contains? (itrace/choices t') :v0)))
        (is (= {:b true :v0 0.3} d) "the overwritten b and the site no longer reached")
        ;; log p(t') − log p(t) − log q(v1): v1's prior cancels against its draw
        (is (close? w (- (+ (lp (ar/flip 0.5) false) (lp (ar/normal v1 1.0) 5.0))
                         (+ (lp (ar/flip 0.5) true) (lp (ar/normal 0.0 1.0) 0.3)
                            (lp (ar/normal 0.3 1.0) 5.0)))))
        (await-cps (gfi/close! t))))))

(deftest regenerate-is-mh-by-selection
  (with-root [root]
    (testing "regenerating nothing is the identity"
      (let [t (await-cps (gfi/simulate (hierarchical root)))]
        (is (identical? t (:trace (await-cps (gfi/regenerate t #{})))))
        (await-cps (gfi/close! t))))
    (testing "alternating x and z moves sample x | y ~ N(2/3, 2/3)"
      (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG 7)
      (let [xs (loop [t (await-cps (gfi/simulate (hierarchical root)))
                      i 0
                      xs []]
                 (if (= i 4000)
                   (do (await-cps (gfi/close! t)) xs)
                   (let [{t' :trace} (await-cps (gfi/mh t (if (even? i) #{:x} #{:z})))]
                     (recur t' (inc i) (if (> i 1000) (conj xs (:trace/result t')) xs)))))
            n (count xs)
            mean (/ (reduce + xs) n)
            var (/ (reduce + (map #(let [d (- % mean)] (* d d)) xs)) n)]
        (is (< (Math/abs (- mean (/ 2.0 3))) 0.12) (str "mean " mean))
        (is (< (Math/abs (- var (/ 2.0 3))) 0.15) (str "variance " var))))))

(deftest importance-sampling-by-generate-estimates-the-evidence
  ;; y = 2 with y ~ N(0, 3): log Z = log N(2; 0, √3)
  (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG 11)
  (with-root [root]
    (let [ws (vec (repeatedly 1500 (fn []
                                     (let [{t :trace w :weight} (await-cps (gfi/generate (hierarchical root) {}))]
                                       (await-cps (gfi/close! t))
                                       w))))
          log-z (m/log-mean-exp ws)]
      (is (< (Math/abs (- log-z (lp (ar/normal 0.0 (Math/sqrt 3.0)) 2.0))) 0.05)
          (str "log Z " log-z)))))
