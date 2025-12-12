(ns is.simm.spindel.smoke-test
  "Smoke test to validate basic testing infrastructure.

   This test ensures that:
   1. We can create a runtime
   2. We can create a signal
   3. We can create a spin that consumes the signal
   4. The spin executes and caches properly
   5. Signal updates trigger re-execution"
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.runtime.context :as ctx]
            [is.simm.spindel.runtime.impl.atoms]  ; Load to register :atoms runtime
            [is.simm.spindel.spin.cps :refer [spin]]
            [is.simm.spindel.state.signal :as sig]
            [is.simm.spindel.effects.await :refer [await]]
            [is.simm.spindel.effects.track :refer [track]]
            [is.simm.spindel.test-helpers :refer [async with-ctx run-spin!]]
            #?(:clj [is.simm.spindel.test-async :refer [await-drain]]))
  #?(:cljs (:require-macros [is.simm.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; CLJ-only tests (use @deref and await-drain)
;; =============================================================================

#?(:clj
   (deftest smoke-test-basic-workflow-clj
     (testing "End-to-end: runtime → signal → spin → execution"
       (let [ctx (ctx/create-execution-context)]
         (is (some? ctx) "Context should be created")
         (binding [rtc/*execution-context* ctx]
           (let [counter (sig/signal 0)]
             (is (some? counter) "Signal should be created")
             (is (= 0 @counter) "Signal initial value should be 0")
             (let [doubled (spin
                             (let [{:keys [new]} (track counter)]
                               (* 2 new)))]
               (is (some? doubled) "Spin should be created")
               (is (= 0 @doubled) "Spin should return 0 (2 * 0)")
               (swap! counter inc)
               (await-drain ctx)
               (is (= 1 @counter) "Signal should be updated to 1")
               (is (= 2 @doubled) "Spin should re-execute and return 2 (2 * 1)"))))))))

#?(:clj
   (deftest smoke-test-multiple-signals-clj
     (testing "Spin can depend on multiple signals"
       (let [ctx (ctx/create-execution-context)]
         (binding [rtc/*execution-context* ctx]
           (let [x (sig/signal 10)
                 y (sig/signal 20)
                 sum-spin (spin
                            (let [{x-val :new} (track x)
                                  {y-val :new} (track y)]
                              (+ x-val y-val)))]
             (is (= 30 @sum-spin) "Spin should sum both signals")
             (swap! x + 5)
             (await-drain ctx)
             (is (= 35 @sum-spin) "Spin should re-execute with new x value")
             (swap! y + 10)
             (await-drain ctx)
             (is (= 45 @sum-spin) "Spin should re-execute with new y value")))))))

;; =============================================================================
;; Cross-platform tests (use async/done pattern)
;; =============================================================================

(deftest smoke-test-spin-caching
  (testing "Spins cache results and don't re-execute unnecessarily"
    (async done
      (with-ctx [_ctx]
        (let [exec-count (atom 0)
              simple-spin (spin
                            (swap! exec-count inc)
                            42)]
          (run-spin! simple-spin
                     (fn [result]
                       (is (= 42 result))
                       (is (= 1 @exec-count) "Spin should execute once")
                       ;; Second execution - should use cache
                       (run-spin! simple-spin
                                  (fn [result2]
                                    (is (= 42 result2))
                                    (is (= 1 @exec-count) "Spin should not re-execute")
                                    (done))
                                  (fn [_] (done))))
                     (fn [_] (done))))))))

(deftest smoke-test-spin-composition
  (testing "Spins can await other spins"
    (async done
      (with-ctx [_ctx]
        (let [base-spin (spin (+ 1 2))
              dependent-spin (spin
                               (let [base-val (await base-spin)]
                                 (* 2 base-val)))]
          (run-spin! base-spin
                     (fn [base-result]
                       (is (= 3 base-result) "Base spin should return 3")
                       (run-spin! dependent-spin
                                  (fn [dep-result]
                                    (is (= 6 dep-result) "Dependent spin should return 6")
                                    (done))
                                  (fn [_] (done))))
                     (fn [_] (done))))))))

(deftest smoke-test-simple-spin
  (testing "Simple spin executes correctly"
    (async done
      (with-ctx [_ctx]
        (let [simple-spin (spin (+ 1 2 3))]
          (run-spin! simple-spin
                     (fn [result]
                       (is (= 6 result))
                       (done))
                     (fn [err]
                       (is false (str "Spin failed: " err))
                       (done))))))))

(deftest smoke-test-signal-tracking
  (testing "Spin can track signal value"
    (async done
      (with-ctx [ctx]
        (let [counter (sig/signal 10)
              doubled (spin
                        (let [{:keys [new]} (track counter)]
                          (* 2 new)))]
          (run-spin! doubled
                     (fn [result]
                       (is (= 20 result) "Spin should double signal value")
                       (done))
                     (fn [err]
                       (is false (str "Spin failed: " err))
                       (done))))))))
