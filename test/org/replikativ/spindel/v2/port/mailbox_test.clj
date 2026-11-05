(ns org.replikativ.spindel.v2.port.mailbox-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task take!]]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture]]))

(use-fixtures :each checked-fixture)

(deftest test-mailbox-post-returns-nil
  (let [m (v2/mailbox)] (is (nil? (m :msg)))))

(deftest test-mailbox-fifo-order
  (let [m (v2/mailbox)]
    (doseq [v [:first :second :third]] (m v))
    (is (= [:first :second :third] (v2/value (task [(take! m) (take! m) (take! m)]))))))

(deftest test-mailbox-blocking-take
  (let [m (v2/mailbox) seen (atom [])
        t (task (let [v (take! m)] (swap! seen conj :consumed) v))]
    (is (empty? @seen))
    (m :delivered)
    (is (= :delivered (v2/value t)))
    (is (= [:consumed] @seen))))

(deftest test-mailbox-multiple-consumers
  (let [m (v2/mailbox) a (task (take! m)) b (task (take! m))]
    (m :msg1) (m :msg2)
    (let [results [(v2/value a) (v2/value b)]]
      (is (= 2 (count results)))
      (is (= #{:msg1 :msg2} (set results))))))

(deftest test-mailbox-producer-consumer-pattern
  (let [m (v2/mailbox)
        consumer (task (loop [n 3 acc []]
                         (if (pos? n) (recur (dec n) (conj acc (take! m))) acc)))]
    (doseq [v [:a :b :c]] (m v))
    (is (= [:a :b :c] (v2/value consumer)))))

(deftest test-mailbox-external-post
  (let [m (v2/mailbox) t (task (take! m))
        posted (future (v2/post! m :external-msg))]
    (is (= :external-msg (v2/value t 5000 ::timeout)))
    (is (nil? (deref posted 5000 ::timeout)))))

(deftest test-mailbox-queue-buildup
  (let [m (v2/mailbox)]
    (dotimes [i 10] (m i))
    (is (= (range 10) (v2/value (task (loop [i 0 acc []]
                                        (if (< i 10) (recur (inc i) (conj acc (take! m))) acc))))))))

(deftest test-mailbox-multiple-producers
  (let [m (v2/mailbox)
        producers (mapv (fn [i] (future (dotimes [j 10] (m [i j])))) (range 10))]
    (doseq [p producers] (is (nil? (deref p 5000 ::timeout))))
    (let [results (v2/value (task (loop [i 0 acc []]
                                    (if (< i 100) (recur (inc i) (conj acc (take! m))) acc))))]
      (is (= 100 (count results)))
      (is (= 100 (count (distinct results)))))))

(deftest test-mailbox-rendezvous-pattern
  (let [m (v2/mailbox) ready (promise) received (promise)
        consumer (future (let [t (task (take! m))]
                           (deliver ready :ready)
                           (deliver received (v2/value t 5000 ::timeout))))]
    (is (= :ready (deref ready 5000 ::timeout)))
    (m :rendezvous-msg)
    (is (= :rendezvous-msg (deref received 5000 ::timeout)))
    (is (not= ::timeout (deref consumer 5000 ::timeout)))))
