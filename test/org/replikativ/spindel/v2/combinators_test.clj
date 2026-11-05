(ns org.replikativ.spindel.v2.combinators-test
  "M6 phase A: combinators on v2 (parallel, race, timeout, sleep, spawn!, blocking)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)

(defn- vworld []
  (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- outcome [h]
  (try [:ok (v2/value h 2000 ::timeout)] (catch Exception e [:err (ex-data e)])))

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 500) false :else (do (Thread/sleep 5) (recur (inc n))))))

(deftest parallel-values-and-fail-fast
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (is (= [:ok [1 2 3]] (outcome (comb/parallel (spin 1) (spin 2) (spin 3)))))
       (is (= [:err {:boom true}]
              (outcome (comb/parallel (spin (throw (ex-info "x" {:boom true}))) (comb/never))))
           "Z#61: the first error ends it, even with a member that never settles")))))

(deftest parallel-is-reactive
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 1)
             a (spin (* 10 (iv/get-new (track x))))
             p (comb/parallel a (spin :k))
             seen (atom [])]
         (v2/observe! p (fn [v _] (swap! seen conj v)))
         (reset! x 2)
         (is (= [[10 :k] [20 :k]] @seen) "it re-runs when a child changes"))))))

(deftest race-and-timeout
  (checked
   (let [w (vworld) loser-ran-to-end (atom false)]
     (binding [v2/*world* w]
       (is (= [:ok :fast] (outcome (comb/race (comb/sleep 5 :fast) (comb/sleep 2000 :slow)))))
       (is (= [:ok :fallback] (outcome (comb/timeout (comb/never) 10 :fallback))))
       (is (= [:ok :in-time] (outcome (comb/timeout (comb/sleep 5 :in-time) 2000 :fallback))))
       (testing "a loser demanded only by the race loses its demand and is cancelled"
         (let [slow (spin (v2/sleep 300) (reset! loser-ran-to-end true) :slow)]
           (is (= [:ok :fast] (outcome (comb/race (comb/sleep 5 :fast) slow))))
           (Thread/sleep 400)
           (is (false? @loser-ran-to-end))))))))

(deftest spawn-callbacks
  (checked
   (let [w (vworld) ok (promise) bad (promise)]
     (binding [v2/*world* w]
       (comb/spawn! (task :done) {:on-success #(deliver ok %)})
       (comb/spawn! (task (throw (ex-info "no" {:x 1}))) {:on-error #(deliver bad (ex-data %))})
       (is (= :done (deref ok 1000 nil)))
       (is (= {:x 1} (deref bad 1000 nil)))
       (comb/spawn! (task :fine) {:on-success (fn [_] (throw (ex-info "callback bug" {})))})
       (is (= [:ok :still-fine] (outcome (task :still-fine))) "a failing callback does not hurt the world")))))

(def ^:dynamic *conveyed* nil)

(deftest blocking-runs-off-the-world
  (checked
   (let [w (vworld)
         pool (java.util.concurrent.Executors/newFixedThreadPool 1)]
     (try
       (binding [v2/*world* w *conveyed* :yes]
         (let [main (Thread/currentThread)
               b (comb/blocking (fn [] [*conveyed* (not= main (Thread/currentThread))]) {:pool pool})]
           (is (= [:ok [:yes true]] (outcome (task (await b))))
               "bindings are conveyed, and f runs on the pool")))
       (finally (.shutdown pool))))))
