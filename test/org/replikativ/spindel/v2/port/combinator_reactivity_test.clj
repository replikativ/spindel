(ns org.replikativ.spindel.v2.port.combinator-reactivity-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.port.support2 :as h]))

(use-fixtures :each h/fixture)

(deftest test-parallel-reactive-to-child-signals
  (let [a (v2/signal 1) b (v2/signal 2)
        ca (atom 0) cb (atom 0) co (atom 0)
        outer (spin (let [p (comb/parallel
                             (spin (let [v (:new (track a))] (swap! ca inc) v))
                             (spin (let [v (:new (track b))] (swap! cb inc) v)))
                          r (await p)] (swap! co inc) r))
        seen (atom []) stop (v2/observe! outer #(swap! seen conj [%1 %2]))]
    (try
      (is (= [1 2] (h/result outer))) (is (= [1 1] [@ca @cb])) (is (<= 1 @co))
      (reset! a 10)
      (is (= [10 2] (h/result outer))) (is (= [2 1] [@ca @cb])) (is (<= 2 @co))
      (reset! b 20)
      (is (= [10 20] (h/result outer))) (is (= [2 2] [@ca @cb]))
      (is (= [[[1 2] false] [[10 2] false] [[10 20] false]] @seen))
      (finally (stop)))))

(deftest test-race-is-reactive-on-v2
  ;; Re-ported to v2 semantics: race is a computation, so a change of its
  ;; winner re-runs it and its awaiters (the old race kept its first winner;
  ;; a decision of M6 phase A, flagged to the user).
  (let [fast (v2/signal :fast-1) slow (v2/signal :slow-1) runs (atom 0)
        outer (spin (swap! runs inc)
                    (await (comb/race (spin (:new (track fast))) (spin (:new (track slow))))))
        stop (v2/observe! outer (fn [_ _]))]
    (try
      (is (#{:fast-1 :slow-1} (h/result outer))) (is (= 1 @runs))
      (reset! fast :fast-2)
      (is (h/wait-until #(= :fast-2 (h/result outer))) "the race re-ran with the new value")
      (is (= 1 @runs) "outer re-enters at its await site (T11): the counting prefix is not repeated")
      (finally (stop)))))

(deftest test-accumulate-is-reactive
  (let [s (v2/signal 0) a (comb/accumulate s iv/merge-intervals) runs (atom 0)
        outer (spin (let [i (await a)] (swap! runs inc) (:new i)))
        stop (v2/observe! outer (fn [_ _]))]
    (try
      (is (= 0 (h/result outer))) (is (= 1 @runs))
      (reset! s 1)
      (is (= 1 (h/result outer))) (is (= 2 @runs))
      (finally (stop)))))

(deftest test-outer-track-creates-new-parallel
  (let [s (v2/signal 2) runs (atom 0)
        outer (spin (let [m (:new (track s))]
                      (swap! runs inc)
                      (await (comb/parallel (spin (* 10 m)) (spin (* 20 m))))))
        stop (v2/observe! outer (fn [_ _]))]
    (try
      (is (= [20 40] (h/result outer))) (is (= 1 @runs))
      (reset! s 3)
      (is (= [30 60] (h/result outer))) (is (= 2 @runs))
      (finally (stop)))))

(deftest test-await-chain-propagates-reactivity
  (let [s (v2/signal 0) order (atom [])
        a (spin (let [v (:new (track s))] (swap! order conj :a) v))
        b (spin (let [v (await a)] (swap! order conj :b) (* 2 v)))
        c (spin (let [v (await b)] (swap! order conj :c) (* 3 v)))
        stop (v2/observe! c (fn [_ _]))]
    (try
      (is (= [0 0 0] (mapv h/result [a b c])))
      (reset! order []) (swap! s inc)
      (is (= [1 2 6] (mapv h/result [a b c])))
      (is (= [:a :b :c] @order))
      (finally (stop)))))

;; v2 source writes currently provide no deltas to accumulate.
(deftest ^:gap test-accumulate-merges-intervals
  (let [s (v2/signal []) a (comb/accumulate s iv/merge-intervals)
        outer (spin (let [i (await a)] {:new (:new i) :old (:old i) :deltas (:deltas i)}))
        stop (v2/observe! outer (fn [_ _]))]
    (try
      (is (= [] (:new (h/result outer))))
      (swap! s conj :a)
      (is (= [:a] (:new (h/result outer)))) (is (some? (:deltas (h/result outer))))
      (swap! s conj :b)
      (is (= [:a :b] (:new (h/result outer))))
      (finally (stop)))))

(deftest test-parallel-pure-children-one-shot
  (let [runs (atom 0) outer (spin (swap! runs inc) (await (comb/parallel (spin (+ 1 2)) (spin (* 3 4)))))]
    (dotimes [_ 3] (is (= [3 12] (h/result outer))))
    (is (= 1 @runs))))

(deftest parallel-follows-a-child-back-to-its-first-value
  (let [s (v2/signal 1) outer (spin (await (comb/parallel (spin (:new (track s))) (spin :other))))
        stop (v2/observe! outer (fn [_ _]))]
    (try
      (is (= [1 :other] (h/result outer)))
      (reset! s 2) (is (= [2 :other] (h/result outer)))
      (reset! s 1) (is (= [1 :other] (h/result outer)))
      (finally (stop)))))

(deftest parallel-recovers-from-a-child-error-with-current-values
  (let [a (v2/signal 1) b (v2/signal :x)
        p (comb/parallel (spin (:new (track a)))
                         (spin (let [v (:new (track b))] (if (= v :boom) (throw (ex-info "boom" {})) v))))
        outer (spin (try (await p) (catch Exception _ :failed)))
        stop (v2/observe! outer (fn [_ _]))]
    (try
      (is (= [1 :x] (h/result outer)))
      (reset! a 2) (is (= [2 :x] (h/result outer)))
      (reset! b :boom) (is (= :failed (h/result outer)))
      (reset! b :x) (is (= [2 :x] (h/result outer)))
      (reset! b :y) (is (= [2 :y] (h/result outer)))
      (finally (stop)))))
