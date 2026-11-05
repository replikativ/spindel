(ns org.replikativ.spindel.v2.port.sync-delivery-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await take!]]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture outcome api]]))

(use-fixtures :each checked-fixture)

(deftest a-loop-over-a-queued-mailbox-does-not-grow-the-stack
  (let [m (v2/mailbox)]
    (dotimes [i 20000] (m i))
    (is (= (range 20000)
           (v2/value (task (loop [i 0 acc []]
                             (if (< i 20000) (recur (inc i) (conj acc (take! m))) acc)))
                     30000 ::timeout)))))

(deftest a-loop-over-an-assigned-deferred-does-not-grow-the-stack
  (let [d (v2/deferred)]
    (d 1)
    (is (= 20000 (v2/value (task (loop [i 0 acc 0]
                                   (if (< i 20000) (recur (inc i) (+ acc (await d))) acc)))
                           30000 ::timeout)))))

(deftest ^:gap a-loop-over-anext-of-a-queued-mailbox-does-not-grow-the-stack
  (when-let [anext (api 'anext)]
    (let [m (v2/mailbox)]
      (dotimes [i 20000] (m i))
      (is (= (range 20000)
             (v2/value (task (loop [i 0 acc [] s m]
                               (if (< i 20000)
                                 (let [[v more] (await (anext s))]
                                   (recur (inc i) (conj acc v) more)) acc)))
                       30000 ::timeout))))))

(deftest cancelling-after-synchronous-takes-runs-finally-once
  (let [m (v2/mailbox) never (v2/deferred) seen (atom [])]
    (doseq [v [:a :b :stop]] (m v))
    (let [t (task (try (loop []
                         (let [v (take! m)]
                           (swap! seen conj v)
                           (if (= v :stop) (await never) (recur))))
                       (finally (swap! seen conj :finally))))]
      (v2/value-async t (fn [_ err?] (when err? (swap! seen conj :on-error))))
      (is (= [:a :b :stop] @seen))
      (v2/cancel-task! t)
      (is (= [:a :b :stop :finally :on-error] @seen)))))

(deftest cancelling-does-not-reenter-an-await-the-body-has-left
  (let [m (v2/mailbox) never (v2/deferred) seen (atom [])]
    (doseq [v [:a :stop]] (m v))
    (let [t (task (loop [k 0]
                    (when (< k 3)
                      (let [v (try (take! m) (catch Exception _ :caught))]
                        (swap! seen conj v)
                        (when (= v :stop) (await never))
                        (recur (inc k))))))]
      (is (= [:a :stop] @seen))
      (v2/cancel-task! t)
      (is (v2/cancelled? (second (outcome t))))
      (is (= [:a :stop] @seen)))))

(deftest a-cancelled-consumer-takes-nothing
  (let [m (v2/mailbox) never (v2/deferred)
        t (task (await never) (take! m))]
    (m :kept)
    (v2/cancel-task! t)
    (never :resume)
    (is (v2/cancelled? (second (outcome t))))
    (is (= :kept (v2/value (task (take! m)))))))

(deftest a-fast-take-never-jumps-a-parked-waiter
  (let [m (v2/mailbox) first-taker (task (take! m))]
    (m :one) (m :two)
    (is (= :one (v2/value first-taker)))
    (is (= :two (v2/value (task (take! m)))))))

(deftest ^:gap a-parallel-controller-drains-a-large-backlog
  (when-let [parallel-controller (api 'parallel-controller)]
    (when-let [submit! (api 'submit!)]
      (when-let [close! (api 'close!)]
        (when-let [completion (api 'completion)]
          (let [finished (atom 0)
                controller (parallel-controller {:concurrency 6 :capacity 500 :ingress-capacity 500}
                                                (fn [i] (task (when (zero? (mod i 9)) (v2/sleep 20))
                                                              (swap! finished inc))))]
            (dotimes [i 500] (is (submit! controller i)))
            (close! controller)
            (let [result (v2/value (completion controller) 60000 ::timeout)]
              (is (map? result))
              (is (= 0 (:work/active result)))
              (is (= 500 @finished)))))))))

(deftest a-fork-takes-from-its-own-copy-of-the-queue
  (let [m (v2/mailbox)]
    (dotimes [i 50] (m i))
    (let [child (v2/fork! v2/*world*) cm (v2/in-world child m)]
      (try
        (binding [v2/*world* child]
          (is (= (range 50) (v2/value (task (loop [i 0 acc []]
                                              (if (< i 50) (recur (inc i) (conj acc (take! cm))) acc)))))))
        (is (= (range 50) (v2/value (task (loop [i 0 acc []]
                                            (if (< i 50) (recur (inc i) (conj acc (take! m))) acc))))))
        (finally (v2/release-world! child))))))
