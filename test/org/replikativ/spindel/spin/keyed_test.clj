(ns org.replikativ.spindel.spin.keyed-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.keyed :refer [keyed children rerun!]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

(deftest a-child-change-patches-its-key-only
  (let [ctx (ctx/create-execution-context)
        runs (atom {})]
    (try
      (binding [ec/*execution-context* ctx]
        (let [sigs (mapv (fn [i] (sig/signal i)) (range 5))
              outer-runs (atom 0)
              ks (range 5)
              k-spin (atom nil)
              outer (spin
                     (let [p (keyed :items ks
                                    (fn [k]
                                      ;; counted after the track: a change resumes
                                      ;; the body from its track point
                                      (spin (let [v (:new (track (sigs k)))]
                                              (swap! runs update k (fnil inc 0))
                                              (* 10 v)))))
                           _ (reset! k-spin p)
                           v (await p)]
                       (swap! outer-runs inc)
                       v))]
          (is (= [0 10 20 30 40] @outer))
          (reset! (sigs 2) 7)
          (await-drain ctx)
          (is (= [0 10 70 30 40] @outer))
          (is (= {0 1 1 1 2 2 3 1 4 1} @runs) "only key 2 re-ran")
          (reset! (sigs 2) 2)
          (await-drain ctx)
          (is (= [0 10 20 30 40] @outer) "back to its first value")
          (testing "children are kept, by key"
            (let [kids (children (spin-core/spin-id @k-spin))]
              (is (= (set ks) (set (keys kids))))
              (is (every? #(satisfies? spin-core/PSpin %) (vals kids)))))))
      (finally (ctx/stop-context! ctx)))))

(deftest child-ids-are-functions-of-the-key
  (let [ids (fn []
              (let [ctx (ctx/create-execution-context)]
                (try
                  (binding [ec/*execution-context* ctx]
                    (let [p (atom nil)
                          outer (spin (let [k (keyed :items [:a :b :c] (fn [k] (spin k)))]
                                        (reset! p k)
                                        (await k)))]
                      @outer
                      (into {} (map (fn [[k s]] [k (spin-core/spin-id s)]))
                            (children (spin-core/spin-id @p)))))
                  (finally (ctx/stop-context! ctx)))))]
    (is (= (ids) (ids)))
    (is (= 3 (count (set (vals (ids))))))))

(deftest empty-keys-resolve-to-an-empty-vector
  (let [ctx (ctx/create-execution-context)]
    (try
      (binding [ec/*execution-context* ctx]
        (is (= [] @(spin (await (keyed :none [] (fn [k] (spin k))))))))
      (finally (ctx/stop-context! ctx)))))

(deftest rerunning-one-key-in-a-fork
  ;; the operation an incremental trace update needs: in a fork, run one
  ;; key's spin again; the keyed result and what awaits it follow, no other
  ;; key runs, and the source world is untouched
  (let [ctx (ctx/create-execution-context)
        runs (atom {})
        knob (atom {})]
    (try
      (binding [ec/*execution-context* ctx]
        (let [p (atom nil)
              outer (spin (let [k (keyed :items (range 4)
                                         (fn [i] (spin (swap! runs update i (fnil inc 0))
                                                       (+ (* 10 i) (get @knob i 0)))))]
                            (reset! p k)
                            (reduce + (await k))))]
          (is (= 60 @outer))
          (let [fork (ctx/fork-context ctx :mode :frozen)
                kid (get (children (spin-core/spin-id @p)) 2)]
            (swap! knob assoc 2 5)
            (binding [ec/*execution-context* fork]
              (let [res (promise)]
                ((rerun! kid) #(deliver res %) #(deliver res %))
                (is (= 25 (deref res 5000 ::timeout)))
                (await-drain fork)
                (is (= 65 @outer) "the fork's outer result followed")))
            (is (= {0 1 1 1 2 2 3 1} @runs) "only key 2 ran again")
            (is (= 60 @outer) "the source world is untouched"))))
      (finally (ctx/stop-context! ctx)))))
