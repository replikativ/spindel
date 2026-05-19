(ns org.replikativ.spindel.engine.bindings-test
  "Tests for dynamic binding capture and restore across async boundaries."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.core :as ec]))

(deftest capture-bindings-test
  (testing "captures bound vars (except *execution-context*)"
    (binding [ec/*execution-context* :test-rt
              ec/*spin-id* :test-spin]
      (let [captured (bindings/capture-bindings)]
        (is (nil? (get captured #'ec/*execution-context*))
            "*execution-context* should NOT be captured (circular reference risk)")
        (is (= :test-spin (get captured #'ec/*spin-id*))
            "Should capture *spin-id* value"))))

  (testing "omits unbound vars"
    (let [captured (bindings/capture-bindings)]
      ;; If *yield-handler* not bound, should be absent from map
      (when-not (bound? #'ec/*yield-handler*)
        (is (not (contains? captured #'ec/*yield-handler*))
            "Should omit unbound *yield-handler*"))))

  (testing "captures registered vars when bound (not *execution-context*)"
    (binding [ec/*execution-context* :rt-val
              ec/*spin-id* :spin-val
              ec/*external-await-cancel-token* :cancel-token-val
              ec/*yield-handler* (fn [v _] v)]
      (let [captured (bindings/capture-bindings)]
        (is (= 3 (count captured))
            "Should capture 3 registered vars (*execution-context* not captured)")
        (is (nil? (get captured #'ec/*execution-context*))
            "*execution-context* should NOT be captured (circular reference risk)")
        (is (= :spin-val (get captured #'ec/*spin-id*)))
        (is (= :cancel-token-val (get captured #'ec/*external-await-cancel-token*)))
        (is (fn? (get captured #'ec/*yield-handler*))
            "Should capture yield-handler function")))))

(deftest restore-bindings-test
  (testing "restores bindings for function execution"
    (let [captured {#'ec/*execution-context* :restored-rt
                    #'ec/*spin-id* :restored-spin}
          result (bindings/restore-bindings captured
                                            (fn []
                     ;; Inside restored context
                                              (is (= :restored-rt ec/*execution-context*)
                                                  "Should have restored *execution-context*")
                                              (is (= :restored-spin ec/*spin-id*)
                                                  "Should have restored *spin-id*")
                                              :success))]
      (is (= :success result)
          "Should return function result")))

  (testing "cleans up bindings after execution"
    (binding [ec/*execution-context* :outer-rt
              ec/*spin-id* :outer-spin]
      ;; Execute with different bindings
      (bindings/restore-bindings {#'ec/*execution-context* :inner-rt
                                  #'ec/*spin-id* :inner-spin}
                                 (fn []
                                   (is (= :inner-rt ec/*execution-context*))
                                   (is (= :inner-spin ec/*spin-id*))))

      ;; After restore-bindings returns, original bindings should be restored
      (is (= :outer-rt ec/*execution-context*)
          "Should restore original *execution-context* after execution")
      (is (= :outer-spin ec/*spin-id*)
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
    (binding [ec/*execution-context* :original-rt
              ec/*spin-id* :original-spin
              ec/*external-await-cancel-token* :original-cancel-token
              ec/*yield-handler* (fn [v _] (* 2 v))]

      ;; Capture in one context
      (let [captured (bindings/capture-bindings)]

        ;; Simulate being in a different context
        (binding [ec/*execution-context* :different-rt
                  ec/*spin-id* :different-spin]

          ;; Restore captured bindings
          (bindings/restore-bindings captured
                                     (fn []
              ;; Should see original values, not "different" values
              ;; NOTE: *execution-context* is NOT captured, so it stays as :different-rt
                                       (is (= :different-rt ec/*execution-context*)
                                           "*execution-context* should NOT be restored (not captured)")
                                       (is (= :original-spin ec/*spin-id*)
                                           "Restored *spin-id* should match captured value")
                                       (is (= :original-cancel-token ec/*external-await-cancel-token*)
                                           "Restored *external-await-cancel-token* should match captured value")
                                       (is (fn? ec/*yield-handler*)
                                           "Restored *yield-handler* should be a function")
              ;; Test that the function still works
                                       (when ec/*yield-handler*
                                         (is (= 10 (ec/*yield-handler* 5 nil))
                                             "Restored function should work correctly")))))))))

(deftest bindings-isolation-test
  (testing "bindings in nested contexts don't interfere"
    (binding [ec/*spin-id* :outer-spin]
      (let [outer-captured (bindings/capture-bindings)]

        (binding [ec/*spin-id* :middle-spin]
          (let [middle-captured (bindings/capture-bindings)]

            (binding [ec/*spin-id* :inner-spin]
              (let [inner-captured (bindings/capture-bindings)]

                ;; Each capture should have captured its own binding
                (is (= :outer-spin (get outer-captured #'ec/*spin-id*)))
                (is (= :middle-spin (get middle-captured #'ec/*spin-id*)))
                (is (= :inner-spin (get inner-captured #'ec/*spin-id*)))

                ;; Restore each in turn
                (bindings/restore-bindings outer-captured
                                           (fn []
                                             (is (= :outer-spin ec/*spin-id*))))

                (bindings/restore-bindings middle-captured
                                           (fn []
                                             (is (= :middle-spin ec/*spin-id*))))

                (bindings/restore-bindings inner-captured
                                           (fn []
                                             (is (= :inner-spin ec/*spin-id*))))))))))))

(deftest bindings-exception-safety-test
  (testing "bindings are cleaned up even when function throws"
    (binding [ec/*spin-id* :original-spin]
      (try
        (bindings/restore-bindings {#'ec/*spin-id* :temporary-spin}
                                   (fn []
                                     (is (= :temporary-spin ec/*spin-id*))
                                     (throw (ex-info "intentional error" {}))))
        (catch Exception _e
          ;; Expected
          ))

      ;; Original binding should be restored despite exception
      (is (= :original-spin ec/*spin-id*)
          "Should restore original binding even after exception"))))
