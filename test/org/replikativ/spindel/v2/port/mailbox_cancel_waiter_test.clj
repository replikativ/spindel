(ns org.replikativ.spindel.v2.port.mailbox-cancel-waiter-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task take!]]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture outcome]]))

(use-fixtures :each checked-fixture)

(deftest test-cancelled-anext-waiter-absorbs-and-loses-message
  (let [m (v2/mailbox) received (atom ::none)
        cancelled (task (let [v (take! m)] (reset! received v)))]
    (v2/cancel-task! cancelled)
    (doseq [v [:m1]] (m v))
    (is (= ::none @received))
    (is (v2/cancelled? (second (outcome cancelled))))
    (is (= [:m1]
           (v2/value (task (loop [n (count [:m1]) acc []]
                             (if (pos? n) (recur (dec n) (conj acc (take! m))) acc))))))))

(deftest test-cancelled-direct-waiter-preserves-message
  (let [m (v2/mailbox) received (atom ::none)
        cancelled (task (let [v (take! m)] (reset! received v)))]
    (v2/cancel-task! cancelled)
    (doseq [v [:m1]] (m v))
    (is (= ::none @received))
    (is (v2/cancelled? (second (outcome cancelled))))
    (is (= [:m1]
           (v2/value (task (loop [n (count [:m1]) acc []]
                             (if (pos? n) (recur (dec n) (conj acc (take! m))) acc))))))))

(deftest test-wedge-shape-matches-production
  (let [m (v2/mailbox) received (atom ::none)
        cancelled (task (let [v (take! m)] (reset! received v)))]
    (v2/cancel-task! cancelled)
    (doseq [v [:lost :q1 :q2 :q3]] (m v))
    (is (= ::none @received))
    (is (v2/cancelled? (second (outcome cancelled))))
    (is (= [:lost :q1 :q2 :q3]
           (v2/value (task (loop [n (count [:lost :q1 :q2 :q3]) acc []]
                             (if (pos? n) (recur (dec n) (conj acc (take! m))) acc))))))))
