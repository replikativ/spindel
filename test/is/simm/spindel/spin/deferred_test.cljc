(ns is.simm.spindel.spin.deferred-test
  "Tests for deferred synchronization primitive"
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing use-fixtures]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.runtime.context :as ctx]
            [is.simm.spindel.runtime.impl.atoms]
            [is.simm.spindel.spin.sync :as sync]
            [is.simm.spindel.spin.cps :refer [spin]]
            [is.simm.spindel.effects.await :refer [await]]
            [is.simm.spindel.test-helpers :refer [async with-ctx run-spin!]])
  #?(:cljs (:require-macros [is.simm.spindel.spin.cps :refer [spin]])))

;; CLJ-only fixture
#?(:clj
   (use-fixtures :each
     (fn [f]
       (let [ctx (ctx/create-execution-context)]
         (binding [rtc/*execution-context* ctx]
           (f))))))

;; =============================================================================
;; Cross-platform tests (async pattern)
;; =============================================================================

(deftest test-deferred-single-assignment
  (testing "Deferred accepts first assignment, returns same value"
    (async done
      (with-ctx [_ctx]
        (let [d (sync/deferred)
              first-result (d :first-value)
              second-result (d :second-value)]

          (is (= :first-value first-result) "First assignment should return the value")
          (is (= :first-value second-result) "Second assignment should return first value (idempotent)")
          (done))))))

(deftest test-deferred-double-delivery-no-crash
  (testing "Double delivery to deferred doesn't crash"
    (async done
      (with-ctx [_ctx]
        (let [d (sync/deferred)
              delivery-count (atom 0)]

          ;; First delivery
          (is (= :value1 (d :value1)) "First delivery should work")
          (swap! delivery-count inc)

          ;; Second delivery - should not crash
          (is (= :value1 (d :value2)) "Second delivery should return first value")
          (swap! delivery-count inc)

          ;; Third delivery - should not crash
          (is (= :value1 (d :value3)) "Third delivery should return first value")
          (swap! delivery-count inc)

          (is (= 3 @delivery-count) "All three deliveries should complete")
          (done))))))

(deftest test-deferred-await-after-delivery
  (testing "Awaiting deferred after delivery returns immediately"
    (async done
      (with-ctx [_ctx]
        (let [d (sync/deferred)
              _ (d :delivered-value)  ; Deliver first
              reader-spin (spin (await d))]

          (run-spin! reader-spin
                     (fn [result]
                       (is (= :delivered-value result) "Should get delivered value immediately")
                       (done))
                     (fn [err]
                       (is false (str "Spin failed: " err))
                       (done))))))))

;; =============================================================================
;; CLJ-only tests: require Thread/sleep, future, promise
;; =============================================================================

#?(:clj
   (deftest test-deferred-multiple-readers
     (testing "Multiple readers all get the same value"
       (binding [rtc/*execution-context* (ctx/create-execution-context)]
         (let [d (sync/deferred)
               results (atom [])]

           ;; Start three readers
           (let [reader1 (spin (await d))
                 reader2 (spin (await d))
                 reader3 (spin (await d))]

             ;; Deliver value
             (Thread/sleep 10) ;; Give readers time to register
             (d :shared-value)

             ;; All readers should get the value
             (is (= :shared-value @reader1) "Reader 1 should get value")
             (is (= :shared-value @reader2) "Reader 2 should get value")
             (is (= :shared-value @reader3) "Reader 3 should get value")))))))

#?(:clj
   (deftest test-deferred-delivery-during-await
     (testing "Delivery while await is blocked"
       (binding [rtc/*execution-context* (ctx/create-execution-context)]
         (let [d (sync/deferred)
               result-promise (promise)]

           ;; Start async reader
           (future
             (binding [rtc/*execution-context* (rtc/current-execution-context)]
               (let [result @(spin (await d))]
                 (deliver result-promise result))))

           ;; Give reader time to block
           (Thread/sleep 10)

           ;; Deliver value
           (d :async-delivered)

           ;; Reader should wake up and get value
           (is (= :async-delivered (deref result-promise 1000 :timeout))
               "Reader should receive delivered value"))))))
