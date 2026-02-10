(ns org.replikativ.spindel.spin-error-test
  "Tests for spin error handling, propagation, and recovery."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
            #?(:clj [org.replikativ.spindel.test-async :refer [await-drain]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; Basic Error Handling (cross-platform async pattern)
;; =============================================================================

(deftest test-spin-throws-exception
  (testing "Spin that throws exception propagates it to caller"
    (async done
      (with-ctx [_ctx]
        (let [error-spin (spin (throw (ex-info "Test error" {:code 42})))]
          (run-spin! error-spin
                     (fn [_]
                       (is false "Spin should have thrown")
                       (done))
                     (fn [error]
                       (is (= "Test error" (ex-message error)))
                       (is (= {:code 42} (ex-data error)))
                       (done))))))))

;; =============================================================================
;; Error Caching (CLJ-only - uses @deref which re-throws cached errors cleanly)
;; =============================================================================

#?(:clj
   (deftest test-error-is-cached
     (testing "Spin error is cached and rethrown on subsequent calls"
       (with-ctx [ctx]
         (let [exec-count (atom 0)
               error-spin (spin
                            (swap! exec-count inc)
                            (throw (ex-info "Cached error" {:attempt @exec-count})))]

           ;; First deref - executes and throws
           (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Cached error"
                 @error-spin))
           (is (= 1 @exec-count))

           ;; Second deref - should throw cached error without re-executing
           (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Cached error"
                 @error-spin))
           (is (= 1 @exec-count) "Should not re-execute, error is cached"))))))

;; =============================================================================
;; Error Propagation Through Spin Chains (cross-platform async pattern)
;; =============================================================================

(deftest test-error-propagates-through-await
  (testing "Error in upstream spin propagates to downstream spin"
    (async done
      (with-ctx [_ctx]
        (let [failing-spin (spin (throw (ex-info "Upstream error" {})))
              dependent-spin (spin
                               (let [result (await failing-spin)]
                                 (* 2 result)))]

          ;; Dependent spin should receive the error
          (run-spin! dependent-spin
                     (fn [_]
                       (is false "Should have thrown")
                       (done))
                     (fn [error]
                       (is (= "Upstream error" (ex-message error)))
                       (done))))))))

(deftest test-error-propagates-through-chain
  (testing "Error propagates through entire spin chain"
    (async done
      (with-ctx [_ctx]
        (let [spin1 (spin 10)
              spin2 (spin (throw (ex-info "Spin2 error" {})))
              spin3 (spin (+ (await spin1) (await spin2)))]

          ;; Spin3 should receive the error from spin2
          (run-spin! spin3
                     (fn [_]
                       (is false "Should have thrown")
                       (done))
                     (fn [error]
                       (is (= "Spin2 error" (ex-message error)))
                       (done))))))))

(deftest test-partial-chain-success
  (testing "Spins before error in chain succeed"
    (async done
      (with-ctx [_ctx]
        (let [spin1 (spin (+ 1 2))
              spin2 (spin (* 2 (await spin1)))
              spin3 (spin (throw (ex-info "Spin3 error" {})))
              spin4 (spin (+ (await spin2) (await spin3)))]

          ;; spin1 and spin2 should succeed
          (run-spin! spin1
                     (fn [r1]
                       (is (= 3 r1))
                       (run-spin! spin2
                                  (fn [r2]
                                    (is (= 6 r2))
                                    ;; spin3 should fail
                                    (run-spin! spin3
                                               (fn [_]
                                                 (is false "spin3 should fail")
                                                 (done))
                                               (fn [e3]
                                                 (is (= "Spin3 error" (ex-message e3)))
                                                 ;; spin4 should also fail
                                                 (run-spin! spin4
                                                            (fn [_]
                                                              (is false "spin4 should fail")
                                                              (done))
                                                            (fn [e4]
                                                              (is (= "Spin3 error" (ex-message e4)))
                                                              (done))))))
                                  (fn [_] (done))))
                     (fn [_] (done))))))))

;; =============================================================================
;; Error Messages and Data (cross-platform async pattern)
;; =============================================================================

(deftest test-error-preserves-message
  (testing "Error message is preserved through caching"
    (async done
      (with-ctx [_ctx]
        (let [error-spin (spin (throw (ex-info "Specific error message" {:x 1})))]
          (run-spin! error-spin
                     (fn [_]
                       (is false "Should have thrown")
                       (done))
                     (fn [error]
                       (is (= "Specific error message" (ex-message error)))
                       (done))))))))

(deftest test-error-preserves-ex-data
  (testing "Error ex-data is preserved"
    (async done
      (with-ctx [_ctx]
        (let [error-data {:error-code 500 :context "test"}
              error-spin (spin (throw (ex-info "Error" error-data)))]
          (run-spin! error-spin
                     (fn [_]
                       (is false "Should have thrown")
                       (done))
                     (fn [error]
                       (is (= error-data (ex-data error)))
                       (done))))))))

;; =============================================================================
;; Error State Tracking (cross-platform async pattern)
;; =============================================================================

(deftest test-error-marks-spin-completed
  (testing "Spin with error is marked as completed (with error status)"
    (async done
      (with-ctx [_ctx]
        (let [error-spin (spin (throw (ex-info "Error" {})))
              spin-id (spin-core/spin-id error-spin)]

          ;; Execute spin
          (run-spin! error-spin
                     (fn [_]
                       (is false "Should have thrown")
                       (done))
                     (fn [_error]
                       ;; Check cached value indicates error
                       (let [res (ec/spin-current-result spin-id)]
                         (is (some? res))
                         (is (ec/spin-result-clean? spin-id))
                         (is (spin-core/error? res))
                         (done)))))))))

;; =============================================================================
;; JVM-only tests (use specific exception types and @deref blocking)
;; =============================================================================

#?(:clj
   (deftest test-spin-division-by-zero
     (testing "Spin with arithmetic error throws exception"
       (with-ctx [ctx]
         (let [div-spin (spin (/ 1 0))]
           (is (thrown? ArithmeticException @div-spin)))))))

#?(:clj
   (deftest test-spin-null-pointer
     (testing "Spin with null pointer access throws NPE"
       (with-ctx [ctx]
         (let [npe-spin (spin (.toString nil))]
           (is (thrown? NullPointerException @npe-spin)))))))

#?(:clj
   (deftest test-error-cache-stores-correct-error
     (testing "Cached error is the same instance"
       (with-ctx [ctx]
         (let [original-error (ex-info "Original" {:data 123})
               error-spin (spin (throw original-error))]

           ;; First deref
           (let [error1 (try @error-spin (catch Exception e e))]
             (is (= "Original" (.getMessage error1)))
             (is (= {:data 123} (ex-data error1)))

             ;; Second deref - should be same error
             (let [error2 (try @error-spin (catch Exception e e))]
               (is (= "Original" (.getMessage error2)))
               (is (= {:data 123} (ex-data error2))))))))))

#?(:clj
   (deftest test-error-with-cause
     (testing "Error with cause chain is preserved"
       (with-ctx [ctx]
         (let [root-cause (Exception. "Root cause")
               wrapped-error (ex-info "Wrapped" {:wrapped true} root-cause)
               error-spin (spin (throw wrapped-error))]

           (try
             @error-spin
             (is false "Should have thrown")
             (catch clojure.lang.ExceptionInfo e
               (is (= "Wrapped" (.getMessage e)))
               (is (= {:wrapped true} (ex-data e)))
               (is (= root-cause (.getCause e)))
               (is (= "Root cause" (.getMessage (.getCause e)))))))))))

;; =============================================================================
;; Error Recovery and Retry (CLJ-only - requires await-drain)
;; =============================================================================

#?(:clj
   (deftest test-spin-error-then-signal-change
     (testing "Spin that initially errors can succeed after signal change"
       (with-ctx [ctx]
         (let [divisor (sig/signal 0)
               div-spin (spin
                          (let [{:keys [new]} (track divisor)]
                            (/ 100 new)))]

           ;; First execution - should throw
           (is (thrown? ArithmeticException @div-spin))

           ;; Update signal to valid value
           (reset! divisor 10)
           (await-drain ctx)

           ;; Should now succeed
           (is (= 10 @div-spin)))))))

#?(:clj
   (deftest test-retry-with-success
     (testing "Spin retries and eventually succeeds"
       (with-ctx [ctx]
         (let [attempt-signal (sig/signal 1)
               retry-spin (spin
                            (let [{:keys [new]} (track attempt-signal)]
                              (if (< new 3)
                                (throw (ex-info "Not ready" {:attempt new}))
                                (* 2 new))))]

           ;; First attempt fails
           (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Not ready"
                 @retry-spin))

           ;; Second attempt fails
           (reset! attempt-signal 2)
           (await-drain ctx)
           (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Not ready"
                 @retry-spin))

           ;; Third attempt succeeds
           (reset! attempt-signal 3)
           (await-drain ctx)
           (is (= 6 @retry-spin)))))))

;; =============================================================================
;; Mixed Success and Error Scenarios (CLJ-only - requires await-drain)
;; =============================================================================

#?(:clj
   (deftest test-successful-spin-then-error
     (testing "Spin succeeds, then signal changes cause error"
       (with-ctx [ctx]
         (let [value (sig/signal 10)
               risky-spin (spin
                            (let [{:keys [new]} (track value)]
                              (when (< new 0)
                                (throw (ex-info "Negative value" {:val new})))
                              (* 2 new)))]

           ;; First execution succeeds
           (is (= 20 @risky-spin))

           ;; Update to negative value
           (reset! value -5)
           (await-drain ctx)

           ;; Should now throw
           (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Negative value"
                 @risky-spin)))))))

#?(:clj
   (deftest test-error-then-success
     (testing "Spin errors, then signal changes lead to success"
       (with-ctx [ctx]
         (let [value (sig/signal -5)
               guarded-spin (spin
                              (let [{:keys [new]} (track value)]
                                (when (< new 0)
                                  (throw (ex-info "Must be positive" {:val new})))
                                (* 2 new)))]

           ;; First execution fails
           (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Must be positive"
                 @guarded-spin))

           ;; Update to positive value
           (reset! value 10)
           (await-drain ctx)

           ;; Should now succeed
           (is (= 20 @guarded-spin)))))))

;; =============================================================================
;; Exception Types (CLJ-only - JVM-specific exception types)
;; =============================================================================

#?(:clj
   (deftest test-runtime-exception
     (testing "RuntimeException is properly handled"
       (with-ctx [ctx]
         (let [runtime-error-spin (spin (throw (RuntimeException. "Runtime error")))]
           (is (thrown? RuntimeException @runtime-error-spin)))))))

#?(:clj
   (deftest test-illegal-argument-exception
     (testing "IllegalArgumentException is properly handled"
       (with-ctx [ctx]
         (let [illegal-arg-spin (spin
                                  (throw (IllegalArgumentException. "Invalid argument")))]
           (is (thrown? IllegalArgumentException @illegal-arg-spin)))))))

#?(:clj
   (deftest test-assertion-error
     (testing "AssertionError is properly handled"
       (with-ctx [ctx]
         (let [assertion-spin (spin (assert false "Assertion failed"))]
           (is (thrown? AssertionError @assertion-spin)))))))
