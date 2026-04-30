(ns org.replikativ.spindel.spin.deferred-test
  "Tests for deferred synchronization primitive"
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing use-fixtures]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; CLJ-only fixture
#?(:clj
   (use-fixtures :each
     (fn [f]
       (let [ctx (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* ctx]
             (f))
           (finally
             (ctx/stop-context! ctx)))))))

;; =============================================================================
;; Cross-platform tests (async pattern)
;; =============================================================================

(deftest test-deferred-single-assignment
  (testing "Deferred returns true on first delivery, false on subsequent"
    (async done
      (with-ctx [_ctx]
        (let [d (sync/deferred)
              first-result (d :first-value)
              second-result (d :second-value)]

          (is (= true first-result) "First delivery should succeed (return true)")
          (is (= false second-result) "Second delivery should be rejected (return false)")
          (done))))))

(deftest test-deferred-double-delivery-no-crash
  (testing "Double delivery returns false, doesn't crash"
    (async done
      (with-ctx [_ctx]
        (let [d (sync/deferred)
              delivery-count (atom 0)]

          ;; First delivery - should succeed
          (is (= true (d :value1)) "First delivery should succeed")
          (swap! delivery-count inc)

          ;; Second delivery - should be rejected (return false)
          (is (= false (d :value2)) "Second delivery should be rejected")
          (swap! delivery-count inc)

          ;; Third delivery - should be rejected (return false)
          (is (= false (d :value3)) "Third delivery should be rejected")
          (swap! delivery-count inc)

          (is (= 3 @delivery-count) "All three deliveries should complete without crashing")
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
       (binding [ec/*execution-context* (ctx/create-execution-context)]
         (let [d (sync/deferred)]
           ;; (spin ...) just builds the Spin record — the body doesn't run
           ;; until @reader. Whether `d` is delivered before or after the
           ;; spin is built doesn't matter for single-assignment deferreds:
           ;; the reader observes the assigned state on first deref.
           (let [reader1 (spin (await d))
                 reader2 (spin (await d))
                 reader3 (spin (await d))]
             (d :shared-value)
             (is (= :shared-value @reader1) "Reader 1 should get value")
             (is (= :shared-value @reader2) "Reader 2 should get value")
             (is (= :shared-value @reader3) "Reader 3 should get value")))))))

#?(:clj
   (deftest test-deferred-delivery-during-await
     (testing "Delivery while await is blocked"
       (binding [ec/*execution-context* (ctx/create-execution-context)]
         (let [d (sync/deferred)
               started (promise)
               result-promise (promise)
               ctx (ec/current-execution-context)]

           ;; Start async reader. Use a dedicated promise to signal that the
           ;; reader has actually entered the deref (so the test below can
           ;; deliver `d` *after* the reader is blocked, not before).
           (future
             (binding [ec/*execution-context* ctx]
               (let [reader (spin (await d))]
                 (deliver started :ready)
                 (deliver result-promise @reader))))

           ;; Wait until the reader has been built and is about to block on
           ;; the deref. There's still a small window between (deliver started ...)
           ;; and the actual @reader call, but it doesn't matter: the deferred
           ;; works correctly regardless of whether d is delivered before or
           ;; during the await.
           (is (= :ready (deref started 1000 :timeout)))

           (d :async-delivered)
           (is (= :async-delivered (deref result-promise 1000 :timeout))
               "Reader should receive delivered value"))))))
