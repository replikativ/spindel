(ns org.replikativ.spindel.runtime.bindings-test
  "Tests for dynamic binding capture and restore across async boundaries."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.runtime.bindings :as bindings]
            [org.replikativ.spindel.runtime.core :as rtc]))

(deftest capture-bindings-test
  (testing "captures bound vars (except *execution-context*)"
    (binding [rtc/*execution-context* :test-rt
              rtc/*spin-id* :test-spin]
      (let [captured (bindings/capture-bindings)]
        (is (nil? (get captured #'rtc/*execution-context*))
            "*execution-context* should NOT be captured (circular reference risk)")
        (is (= :test-spin (get captured #'rtc/*spin-id*))
            "Should capture *spin-id* value"))))

  (testing "omits unbound vars"
    (let [captured (bindings/capture-bindings)]
      ;; If *yield-handler* not bound, should be absent from map
      (when-not (bound? #'rtc/*yield-handler*)
        (is (not (contains? captured #'rtc/*yield-handler*))
            "Should omit unbound *yield-handler*"))))

  (testing "captures registered vars when bound (not *execution-context*)"
    (binding [rtc/*execution-context* :rt-val
              rtc/*spin-id* :spin-val
              rtc/*worker-id* :worker-val
              rtc/*yield-handler* (fn [v _] v)]
      (let [captured (bindings/capture-bindings)]
        (is (= 3 (count captured))
            "Should capture 3 registered vars (*execution-context* not captured)")
        (is (nil? (get captured #'rtc/*execution-context*))
            "*execution-context* should NOT be captured (circular reference risk)")
        (is (= :spin-val (get captured #'rtc/*spin-id*)))
        (is (= :worker-val (get captured #'rtc/*worker-id*)))
        (is (fn? (get captured #'rtc/*yield-handler*))
            "Should capture yield-handler function")))))

(deftest restore-bindings-test
  (testing "restores bindings for function execution"
    (let [captured {#'rtc/*execution-context* :restored-rt
                    #'rtc/*spin-id* :restored-spin}
          result (bindings/restore-bindings captured
                   (fn []
                     ;; Inside restored context
                     (is (= :restored-rt rtc/*execution-context*)
                         "Should have restored *execution-context*")
                     (is (= :restored-spin rtc/*spin-id*)
                         "Should have restored *spin-id*")
                     :success))]
      (is (= :success result)
          "Should return function result")))

  (testing "cleans up bindings after execution"
    (binding [rtc/*execution-context* :outer-rt
              rtc/*spin-id* :outer-spin]
      ;; Execute with different bindings
      (bindings/restore-bindings {#'rtc/*execution-context* :inner-rt
                                   #'rtc/*spin-id* :inner-spin}
        (fn []
          (is (= :inner-rt rtc/*execution-context*))
          (is (= :inner-spin rtc/*spin-id*))))

      ;; After restore-bindings returns, original bindings should be restored
      (is (= :outer-rt rtc/*execution-context*)
          "Should restore original *execution-context* after execution")
      (is (= :outer-spin rtc/*spin-id*)
          "Should restore original *spin-id* after execution")))

  (testing "handles empty bindings map"
    (let [result (bindings/restore-bindings {}
                   (fn []
                     :no-bindings))]
      (is (= :no-bindings result)
          "Should handle empty bindings map")))

  (testing "handles nil bindings as empty"
    (let [result (bindings/restore-bindings nil
                   (fn []
                     :nil-bindings))]
      (is (= :nil-bindings result)
          "Should handle nil bindings"))))

(deftest capture-restore-round-trip-test
  (testing "captured bindings can be restored correctly"
    (binding [rtc/*execution-context* :original-rt
              rtc/*spin-id* :original-spin
              rtc/*worker-id* :original-worker
              rtc/*yield-handler* (fn [v _] (* 2 v))]

      ;; Capture in one context
      (let [captured (bindings/capture-bindings)]

        ;; Simulate being in a different context
        (binding [rtc/*execution-context* :different-rt
                  rtc/*spin-id* :different-spin]

          ;; Restore captured bindings
          (bindings/restore-bindings captured
            (fn []
              ;; Should see original values, not "different" values
              ;; NOTE: *execution-context* is NOT captured, so it stays as :different-rt
              (is (= :different-rt rtc/*execution-context*)
                  "*execution-context* should NOT be restored (not captured)")
              (is (= :original-spin rtc/*spin-id*)
                  "Restored *spin-id* should match captured value")
              (is (= :original-worker rtc/*worker-id*)
                  "Restored *worker-id* should match captured value")
              (is (fn? rtc/*yield-handler*)
                  "Restored *yield-handler* should be a function")
              ;; Test that the function still works
              (when rtc/*yield-handler*
                (is (= 10 (rtc/*yield-handler* 5 nil))
                    "Restored function should work correctly")))))))))

(deftest bindings-isolation-test
  (testing "bindings in nested contexts don't interfere"
    (binding [rtc/*spin-id* :outer-spin]
      (let [outer-captured (bindings/capture-bindings)]

        (binding [rtc/*spin-id* :middle-spin]
          (let [middle-captured (bindings/capture-bindings)]

            (binding [rtc/*spin-id* :inner-spin]
              (let [inner-captured (bindings/capture-bindings)]

                ;; Each capture should have captured its own binding
                (is (= :outer-spin (get outer-captured #'rtc/*spin-id*)))
                (is (= :middle-spin (get middle-captured #'rtc/*spin-id*)))
                (is (= :inner-spin (get inner-captured #'rtc/*spin-id*)))

                ;; Restore each in turn
                (bindings/restore-bindings outer-captured
                  (fn []
                    (is (= :outer-spin rtc/*spin-id*))))

                (bindings/restore-bindings middle-captured
                  (fn []
                    (is (= :middle-spin rtc/*spin-id*))))

                (bindings/restore-bindings inner-captured
                  (fn []
                    (is (= :inner-spin rtc/*spin-id*))))))))))))

(deftest bindings-exception-safety-test
  (testing "bindings are cleaned up even when function throws"
    (binding [rtc/*spin-id* :original-spin]
      (try
        (bindings/restore-bindings {#'rtc/*spin-id* :temporary-spin}
          (fn []
            (is (= :temporary-spin rtc/*spin-id*))
            (throw (ex-info "intentional error" {}))))
        (catch Exception _e
          ;; Expected
          ))

      ;; Original binding should be restored despite exception
      (is (= :original-spin rtc/*spin-id*)
          "Should restore original binding even after exception"))))
