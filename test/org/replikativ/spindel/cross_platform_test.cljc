(ns org.replikativ.spindel.cross-platform-test
  "Example cross-platform test demonstrating proper async test patterns.

  This test file serves as a template for writing tests that work in both
  CLJ and CLJS. Key patterns demonstrated:

  1. Using `async` macro for async test blocks
  2. Using `with-ctx` for test context setup
  3. Using `run-spin!` instead of blocking deref
  4. Platform-specific exception handling"
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]))

;; =============================================================================
;; Basic Spin Tests - Cross Platform
;; =============================================================================

(deftest test-simple-spin-value
  (testing "Simple spin returns computed value"
    (async done
      (with-ctx [ctx]
        (let [t (spin (+ 1 2))]
          (run-spin! t
                     (fn [result]
                       (is (= 3 result))
                       (done))
                     (fn [error]
                       (is false (str "Spin failed: " error))
                       (done))))))))

(deftest test-spin-with-let-bindings
  (testing "Spin with local bindings"
    (async done
      (with-ctx [ctx]
        (let [t (spin
                  (let [x 10
                        y 20]
                    (+ x y)))]
          (run-spin! t
                     (fn [result]
                       (is (= 30 result))
                       (done))
                     (fn [error]
                       (is false (str "Spin failed: " error))
                       (done))))))))

(deftest test-nested-spin-computation
  (testing "Spin with nested expressions"
    (async done
      (with-ctx [ctx]
        (let [t (spin
                  (* 2
                     (+ 3
                        (- 10 5))))]
          (run-spin! t
                     (fn [result]
                       (is (= 16 result)) ; 2 * (3 + (10-5)) = 2 * 8 = 16
                       (done))
                     (fn [error]
                       (is false (str "Spin failed: " error))
                       (done))))))))

;; =============================================================================
;; Spin Await Tests - Cross Platform
;; =============================================================================

(deftest test-spin-await-another
  (testing "Spin can await another spin"
    (async done
      (with-ctx [ctx]
        (let [base-spin (spin (+ 1 2))
              dependent-spin (spin
                               (let [base-result (await base-spin)]
                                 (* 2 base-result)))]
          (run-spin! dependent-spin
                     (fn [result]
                       (is (= 6 result)) ; 2 * 3 = 6
                       (done))
                     (fn [error]
                       (is false (str "Spin failed: " error))
                       (done))))))))

(deftest test-spin-chain
  (testing "Spins can form dependency chains"
    (async done
      (with-ctx [ctx]
        (let [spin1 (spin (+ 1 2))
              spin2 (spin (* 2 (await spin1)))
              spin3 (spin (- (await spin2) 1))]
          (run-spin! spin3
                     (fn [result]
                       (is (= 5 result)) ; (3 * 2) - 1 = 5
                       (done))
                     (fn [error]
                       (is false (str "Spin failed: " error))
                       (done))))))))

;; =============================================================================
;; Error Handling Tests - Cross Platform
;; =============================================================================

(deftest test-spin-error-propagates
  (testing "Spin error reaches error callback"
    (async done
      (with-ctx [ctx]
        (let [error-spin (spin (throw (ex-info "Test error" {:data 42})))]
          (run-spin! error-spin
                     (fn [result]
                       (is false (str "Expected error, got: " result))
                       (done))
                     (fn [error]
                       (is (= "Test error" (ex-message error)))
                       (done))))))))

(deftest test-spin-error-propagates-through-await
  (testing "Error propagates through awaiting spin"
    (async done
      (with-ctx [ctx]
        (let [error-spin (spin (throw (ex-info "Source error" {})))
              dependent (spin (+ 1 (await error-spin)))]
          (run-spin! dependent
                     (fn [result]
                       (is false (str "Expected error, got: " result))
                       (done))
                     (fn [error]
                       (is (= "Source error" (ex-message error)))
                       (done))))))))

;; =============================================================================
;; Multiple Spins Tests - Cross Platform
;; =============================================================================

(deftest test-multiple-independent-spins
  (testing "Multiple independent spins can complete"
    (async done
      (with-ctx [ctx]
        (let [completed (atom #{})
              check-done (fn []
                          (when (= #{:spin1 :spin2 :spin3} @completed)
                            (done)))
              spin1 (spin (+ 1 1))
              spin2 (spin (* 2 2))
              spin3 (spin (- 10 5))]
          ;; Run all three spins
          (run-spin! spin1
                     (fn [result]
                       (is (= 2 result))
                       (swap! completed conj :spin1)
                       (check-done))
                     (fn [_] (done)))
          (run-spin! spin2
                     (fn [result]
                       (is (= 4 result))
                       (swap! completed conj :spin2)
                       (check-done))
                     (fn [_] (done)))
          (run-spin! spin3
                     (fn [result]
                       (is (= 5 result))
                       (swap! completed conj :spin3)
                       (check-done))
                     (fn [_] (done))))))))
