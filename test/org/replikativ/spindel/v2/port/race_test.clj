(ns org.replikativ.spindel.v2.port.race-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.port.support2 :as h]))

(use-fixtures :each h/fixture)

(deftest test-race-two-immediate-spins
  (is (#{:first :second} (h/result (comb/race (spin :first) (spin :second))))))

(deftest test-race-three-immediate-spins
  (is (#{:a :b :c} (h/result (comb/race (spin :a) (spin :b) (spin :c))))))

(deftest test-race-deferred-immediate
  (is (= :immediate (h/result (comb/race (v2/deferred) (spin :immediate))))))

(deftest test-await-race-in-spin
  (is (#{20 40} (h/result (spin (* 2 (await (comb/race (spin 10) (spin 20)))))))))

(deftest test-race-result-can-be-processed
  (let [r (h/result (comb/race (spin [:type-a :value-a]) (spin [:type-b :value-b])))]
    (is (vector? r)) (is (#{:type-a :type-b} (first r))) (is (#{:value-a :value-b} (second r)))))

(deftest test-race-two-deferreds-first-wins
  (let [a (v2/deferred) b (v2/deferred) r (comb/race a b)]
    (a :first-wins) (is (= :first-wins (h/result r))) (b :second)
    (is (= :first-wins (h/result r)))))

(deftest test-race-two-deferreds-second-wins
  (let [a (v2/deferred) b (v2/deferred) r (comb/race a b)]
    (b :second-wins) (is (= :second-wins (h/result r)))))

(deftest test-race-with-never-completing-deferred
  (let [a (v2/deferred) b (v2/deferred) r (comb/race a b)]
    (b :winner) (is (= :winner (h/result r)))))

(deftest test-race-yield-vs-termination
  (let [a (v2/deferred) b (v2/deferred) r (comb/race a b)]
    (a [:yield {:value 42}]) (is (= [:yield {:value 42}] (h/result r)))))

(deftest test-race-termination-wins
  (let [a (v2/deferred) b (v2/deferred) r (comb/race a b)]
    (b [:ok nil]) (is (= [:ok nil] (h/result r)))))

(deftest test-race-can-distinguish-results
  (let [a (v2/deferred) b (v2/deferred) r (comb/race a b)]
    (a [:type-a :value-a])
    (let [v (h/result r)]
      (is (vector? v)) (is (= :type-a (first v))) (is (= :value-a (second v))))))
