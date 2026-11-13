(ns org.replikativ.spindel.v2.port.deferred-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await]]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture outcome]]))

(use-fixtures :each checked-fixture)

(deftest test-deferred-single-assignment
  (let [d (v2/deferred)]
    (is (true? (d :first-value)))
    (is (false? (d :second-value)))
    (is (= :first-value (v2/value (task (await d)))))))

(deftest test-deferred-double-delivery-no-crash
  (let [d (v2/deferred) deliveries (atom 0)]
    (is (true? (d :value1))) (swap! deliveries inc)
    (is (false? (d :value2))) (swap! deliveries inc)
    (is (false? (d :value3))) (swap! deliveries inc)
    (is (= 3 @deliveries))))

(deftest test-deferred-await-after-delivery
  (let [d (v2/deferred)]
    (d :delivered-value)
    (is (= :delivered-value (v2/value (spin (await d)))))))

(deftest test-deferred-falsey-values-after-delivery
  (doseq [v [nil false]]
    (let [d (v2/deferred)]
      (is (true? (d v)))
      (is (= [:ok v] (outcome (spin (await d))))))))

(deftest test-deferred-multiple-readers
  (let [d (v2/deferred) readers [(task (await d)) (task (await d)) (task (await d))]]
    (d :shared-value)
    (doseq [r readers] (is (= :shared-value (v2/value r))))))

(deftest test-deferred-delivery-during-await
  (let [d (v2/deferred) reader (task (await d))
        delivery (future (v2/deliver! d :async-delivered))]
    (is (= :async-delivered (v2/value reader 5000 ::timeout)))
    (is (= :async-delivered (deref delivery 5000 ::timeout)))))

(deftest test-deferred-concurrent-delivery-has-one-winner
  (let [executor (java.util.concurrent.Executors/newFixedThreadPool 16)]
    (try
      (dotimes [attempt 32]
        (let [d (v2/deferred)
              ready (java.util.concurrent.CountDownLatch. 16)
              start (java.util.concurrent.CountDownLatch. 1)
              jobs (mapv (fn [v]
                           (.submit executor ^java.util.concurrent.Callable
                                    (reify java.util.concurrent.Callable
                                      (call [_] (.countDown ready) (.await start) (d v)))))
                         (range 16))]
          (is (.await ready 2 java.util.concurrent.TimeUnit/SECONDS) (str "barrier " attempt))
          (.countDown start)
          (let [results (mapv #(.get ^java.util.concurrent.Future % 2 java.util.concurrent.TimeUnit/SECONDS) jobs)]
            (is (= 1 (count (filter true? results))) (str "winner " attempt))
            (is (= (.indexOf results true) (v2/value d))))))
      (finally (.shutdownNow executor)
               (.awaitTermination executor 2 java.util.concurrent.TimeUnit/SECONDS)))))
