(ns org.replikativ.spindel.v2.port.deferred-deadlock-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await]]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture]]))

(use-fixtures :each checked-fixture)

(deftest test-deferred-self-delivery
  (let [started (promise) proceed (promise)
        t (task (let [d (v2/deferred)] (deliver started d) (await d)))
        d (deref started 5000 ::timeout)
        delivery (future (deliver proceed true) (v2/deliver! d 42))]
    (is (true? (deref proceed 5000 false)))
    (is (= 42 (v2/value t 5000 ::timeout)))
    (is (= 42 (deref delivery 5000 ::timeout)))))

(deftest test-deferred-same-spin-cps-delivery
  (let [started (promise) proceed (promise)
        t (task (let [d (v2/deferred)] (deliver started d) (await d)))
        d (deref started 5000 ::timeout)
        delivery (future (deliver proceed true) (v2/deliver! d 99))]
    (is (true? (deref proceed 5000 false)))
    (is (= 99 (v2/value t 5000 ::timeout)))
    (is (= 99 (deref delivery 5000 ::timeout)))))

(deftest test-deferred-inline-delivery-attempt
  (let [started (promise) proceed (promise)
        t (task (let [d (v2/deferred)] (deliver started d) (await d)))
        d (deref started 5000 ::timeout)
        delivery (future (deliver proceed true) (v2/deliver! d :delivered-value))]
    (is (true? (deref proceed 5000 false)))
    (is (= :delivered-value (v2/value t 5000 ::timeout)))
    (is (= :delivered-value (deref delivery 5000 ::timeout)))))

(deftest test-deferred-synchronous-cps-delivery
  (is (= :inner-result
         (v2/value (task (let [d (v2/deferred)
                               inner (fn [resolve _reject] (resolve :inner-result))
                               resolve (fn [v] (d v))]
                           (inner resolve identity)
                           (await d)))))))
