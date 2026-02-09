(ns org.replikativ.spindel.runtime-impls-test
  "Test suite for ExecutionContext runtime.

  Tests that the ExecutionContext correctly implements core functionality:
  - Spin execution and caching
  - Signal consumption and reactivity
  - Spin-to-spin await (continuation mechanism)
  - Error propagation
  - Dependency graph tracking

  Uses async/done test pattern from test-helpers for cross-platform CLJ/CLJS."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
            [org.replikativ.spindel.test-async :refer [await-drain]]
            [org.replikativ.spindel.engine.impl.simple :as simple]))

;; =============================================================================
;; ExecutionContext is the unified runtime implementation
;; =============================================================================

;; =============================================================================
;; Core Functionality Tests
;; =============================================================================

(deftest test-basic-spin-execution
  (testing "Basic spin execution works across all runtime implementations"
    (async done
      (with-ctx [_ctx]
        (let [simple-spin (spin (+ 1 2))]
          (run-spin! simple-spin
                     (fn [result]
                       (is (= 3 result))
                       (done))
                     (fn [error]
                       (is false (str "error: " error))
                       (done))))))))

(deftest test-spin-caching
  (testing "Spin caching works"
    (async done
      (with-ctx [_ctx]
        (let [exec-count (atom 0)
              cached-spin (spin
                            (swap! exec-count inc)
                            42)]
          ;; First execution
          (run-spin! cached-spin
                     (fn [result]
                       (is (= 42 result) "first run")
                       (is (= 1 @exec-count) "exec count after first")
                       ;; Second execution - should use cache
                       (run-spin! cached-spin
                                  (fn [result2]
                                    (is (= 42 result2) "second run")
                                    (is (= 1 @exec-count) "should not re-execute")
                                    (done))
                                  (fn [error]
                                    (is false (str "second run error: " error))
                                    (done))))
                     (fn [error]
                       (is false (str "first run error: " error))
                       (done))))))))

;; =============================================================================
;; Continuation Mechanism Tests (await)
;; =============================================================================

(deftest test-spin-await-spin
  (testing "Spin can await another spin (continuation mechanism)"
    (async done
      (with-ctx [_ctx]
        (let [base-spin (spin (+ 1 2))
              dependent-spin (spin
                               (let [base-result (await base-spin)]
                                 (* 2 base-result)))]
          ;; Run base spin first
          (run-spin! base-spin
                     (fn [base-result]
                       (is (= 3 base-result) "base")
                       ;; Then run dependent
                       (run-spin! dependent-spin
                                  (fn [dep-result]
                                    (is (= 6 dep-result) "dependent")
                                    (done))
                                  (fn [error]
                                    (is false (str "dependent error: " error))
                                    (done))))
                     (fn [error]
                       (is false (str "base error: " error))
                       (done))))))))

(deftest test-spin-await-unstarted
  (testing "Spin can await another spin that hasn't started yet"
    (async done
      (with-ctx [_ctx]
        (let [base-spin (spin (+ 20 22))
              ;; Create dependent WITHOUT running base first
              dependent-spin (spin (* 2 (await base-spin)))]
          ;; This tests the continuation mechanism:
          ;; - Parent suspends when child not ready
          ;; - Child executes
          ;; - :spin-completion event triggers
          ;; - Parent resumes via continuation
          (run-spin! dependent-spin
                     (fn [result]
                       (is (= 84 result))
                       (done))
                     (fn [error]
                       (is false (str "error: " error))
                       (done))))))))

(deftest test-spin-chain
  (testing "Spins can form dependency chains"
    (async done
      (with-ctx [_ctx]
        (let [spin1 (spin (+ 1 2))
              spin2 (spin (* 2 (await spin1)))
              spin3 (spin (- (await spin2) 1))]
          ;; Run the final spin - should trigger entire chain
          (run-spin! spin3
                     (fn [result]
                       (is (= 5 result) "spin3")
                       (done))
                     (fn [error]
                       (is false (str "error: " error))
                       (done))))))))

;; =============================================================================
;; Error Propagation Tests
;; =============================================================================

(deftest test-error-propagation
  (testing "Errors propagate through spin chains"
    (async done
      (with-ctx [_ctx]
        (let [error-spin (spin (throw (ex-info "Test error" {:data 42})))
              dependent (spin (+ 1 (await error-spin)))]
          ;; Error spin should fail
          (run-spin! error-spin
                     (fn [result]
                       (is false (str "expected error, got: " result))
                       (done))
                     (fn [error]
                       (is (= "Test error" (ex-message error)) "error message")
                       ;; Dependent should also fail
                       (run-spin! dependent
                                  (fn [result]
                                    (is false (str "dependent expected error, got: " result))
                                    (done))
                                  (fn [dep-error]
                                    (is (= "Test error" (ex-message dep-error)) "dependent error")
                                    (done))))))))))

(deftest test-partial-chain-error
  (testing "Errors stop propagation but earlier spins succeed"
    (async done
      (with-ctx [_ctx]
        (let [spin1 (spin (+ 1 2))
              spin2 (spin (* 2 (await spin1)))
              spin3 (spin (throw (ex-info "Spin3 error" {})))
              spin4 (spin (+ (await spin2) (await spin3)))]
          ;; spin1 should succeed
          (run-spin! spin1
                     (fn [r1]
                       (is (= 3 r1) "spin1")
                       ;; spin2 should succeed
                       (run-spin! spin2
                                  (fn [r2]
                                    (is (= 6 r2) "spin2")
                                    ;; spin3 should fail
                                    (run-spin! spin3
                                               (fn [_r3]
                                                 (is false "spin3 expected error")
                                                 (done))
                                               (fn [e3]
                                                 (is (= "Spin3 error" (ex-message e3)) "spin3 error")
                                                 ;; spin4 should fail with spin3's error
                                                 (run-spin! spin4
                                                            (fn [_r4]
                                                              (is false "spin4 expected error")
                                                              (done))
                                                            (fn [e4]
                                                              (is (= "Spin3 error" (ex-message e4)) "spin4 error")
                                                              (done))))))
                                  (fn [error]
                                    (is false (str "spin2 error: " error))
                                    (done))))
                     (fn [error]
                       (is false (str "spin1 error: " error))
                       (done))))))))

;; =============================================================================
;; Signal Tracking Tests (JVM only - signals use swap! which needs sync drain)
;; =============================================================================

#?(:clj
   (deftest test-signal-tracking
     (testing "Spins can track signals with ExecutionContext"
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [counter (sig/signal 0)
                 doubled (spin
                           (let [{:keys [new]} (track counter)]
                             (* 2 new)))]
             ;; Initial execution
             (is (= 0 @doubled))
             ;; Update signal
             (swap! counter inc)
             ;; Wait for events to be processed
             (await-drain ctx)
             ;; Spin should re-execute
             (is (= 2 @doubled))))))))

#?(:clj
   (deftest test-dependency-tracking
     (testing "Dependency graph is correctly maintained"
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [counter (sig/signal 10)
                 doubled (spin
                           (let [{:keys [new]} (track counter)]
                             (* 2 new)))
                 tripled (spin (* 3 (await doubled)))]
             ;; Execute both spins
             (is (= 20 @doubled))
             (is (= 60 @tripled))
             ;; Update signal - both should re-execute
             (swap! counter + 5)
             ;; Wait for events to be processed
             (await-drain ctx)
             (is (= 30 @doubled))
             (is (= 90 @tripled))))))))