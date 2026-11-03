(ns org.replikativ.spindel.await-retention-census-test
  "Census of engine state retained by `await` on spins that are final (complete,
  not signal-dependent). This is the shape of dvergr's per-attempt
  `:await-conts` growth: a long-lived body awaits a fresh child per
  iteration."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

(defn- census [c]
  (binding [ec/*execution-context* c]
    (let [count-nested (fn [k] (reduce + 0 (map count (vals (ec/get-state [k])))))]
      {:await-conts (count-nested :await-conts)
       :subscriptions (count (ec/get-state [:subscriptions]))
       :spin-tracking (count (ec/get-state [:spin-tracking]))
       :nodes (count (ec/get-state [:nodes]))})))

(defn- sync-child [i] (spin (* 2 i)))

(defn- async-child [d i] (spin (+ i (await d))))

(defn- loop-sync [n]
  (spin (loop [i 0 acc 0]
          (if (< i n)
            (recur (inc i) (+ acc (await (sync-child i))))
            acc))))

(defn- loop-async [ds]
  (spin (loop [i 0 acc 0]
          (if (< i (count ds))
            (recur (inc i) (+ acc (await (async-child (nth ds i) i))))
            acc))))

(defn- loop-then-park [n gate]
  (spin (loop [i 0]
          (when (< i n)
            (await (sync-child i))
            (recur (inc i))))
        (await gate)))

(defn- run-census [make-ctx label n]
  (let [c (make-ctx)]
    (binding [ec/*execution-context* c]
      (let [sync-res @(loop-sync n)
            ds (vec (repeatedly n sync/deferred))
            async-spin (loop-async ds)
            p (future @async-spin)
            _ (doseq [d ds] (sync/deliver! d 1))
            async-res (deref p 10000 ::timeout)
            gate (sync/deferred)
            parked (loop-then-park n gate)
            _ (future @parked)
            _ (Thread/sleep 200)
            parked-census (census c)]
        (sync/deliver! gate :done)
        (Thread/sleep 100)
        (let [after (census c)]
          (System/gc)
          (Thread/sleep 300)
          {:label label :n n :sync-res sync-res :async-res async-res
           :while-parked parked-census :after after :after-gc (census c)})))))

(defn- consuming-ctx []
  (ctx/create-execution-context :bindings {:spindel/await-retention :consume-final}))

(defn- check-results [r n]
  (is (= (reduce + (map #(* 2 %) (range n))) (:sync-res r)))
  (is (= (+ n (reduce + (range n))) (:async-res r))))

(deftest await-retention-census
  (testing "default retention grows with history (documented; fixed by the opt-in below)"
    (doseq [n [10 100]]
      (let [r (run-census #(ctx/create-execution-context) :default n)]
        (println "CENSUS" (pr-str r))
        (check-results r n)
        (is (<= (* 3 n) (get-in r [:after :await-conts]))))))
  (testing ":consume-final keeps await state independent of N"
    (doseq [n [10 100]]
      (let [r (run-census consuming-ctx :consume-final n)]
        (println "CENSUS" (pr-str r))
        (check-results r n)
        (is (<= (get-in r [:while-parked :await-conts]) 2))
        (is (<= (get-in r [:after :await-conts]) 1))
        (is (<= (get-in r [:after :subscriptions]) 1))))))

(defn- signal-child [s] (spin (let [{:keys [new]} (track s)] (* 10 new))))

(deftest consume-final-keeps-reactive-awaits
  (testing "an await of a signal-dependent child stays reactive under :consume-final"
    (let [c (consuming-ctx)]
      (binding [ec/*execution-context* c]
        (let [s (sig/signal 1)
              child (signal-child s)
              parent (spin (+ 1 (await child)))]
          (is (= 11 @parent))
          (swap! s (constantly 2))
          (await-drain c)
          (is (= 21 @parent)))))))
