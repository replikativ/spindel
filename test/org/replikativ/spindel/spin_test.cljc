(ns org.replikativ.spindel.spin-test
  "Comprehensive tests for Spin lifecycle, caching, and dependency tracking."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.context :as ctx]
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
;; Cross-platform Basic Spin Execution (async pattern)
;; =============================================================================

(deftest test-basic-spin-execution
  (testing "Basic spin executes and returns result"
    (async done
      (with-ctx [_ctx]
        (let [simple-spin (spin (+ 1 2))]
          (run-spin! simple-spin
                     (fn [result]
                       (is (= 3 result))
                       (done))
                     (fn [_] (done))))))))

(deftest test-spin-with-binding
  (testing "Spin executes with values from outer scope"
    (async done
      (with-ctx [_ctx]
        (let [x 10
              y 20
              sum-spin (spin (+ x y))]
          (run-spin! sum-spin
                     (fn [result]
                       (is (= 30 result))
                       (done))
                     (fn [_] (done))))))))

(deftest test-spin-with-let-binding
  (testing "Spin can use let bindings"
    (async done
      (with-ctx [_ctx]
        (let [complex-spin (spin
                             (let [x 5
                                   y (* x 2)
                                   z (+ x y)]
                               z))]
          (run-spin! complex-spin
                     (fn [result]
                       (is (= 15 result))
                       (done))
                     (fn [_] (done))))))))

;; =============================================================================
;; Spin Caching (cross-platform)
;; =============================================================================

(deftest test-spin-caching-basic
  (testing "Spins cache results and don't re-execute unnecessarily"
    (async done
      (with-ctx [_ctx]
        (let [exec-count (atom 0)
              cached-spin (spin
                            (swap! exec-count inc)
                            42)]
          (run-spin! cached-spin
                     (fn [result1]
                       (is (= 42 result1))
                       (is (= 1 @exec-count) "Spin should execute once")
                       ;; Second call
                       (run-spin! cached-spin
                                  (fn [result2]
                                    (is (= 42 result2))
                                    (is (= 1 @exec-count) "Spin should not re-execute")
                                    (done))
                                  (fn [_] (done))))
                     (fn [_] (done))))))))

;; =============================================================================
;; CLJ-only: expensive computation caching with timing
;; =============================================================================

#?(:clj
   (deftest test-spin-caching-with-computation
     (testing "Expensive computations are cached"
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [exec-count (atom 0)
                 expensive-spin (spin
                                  (swap! exec-count inc)
                                  (Thread/sleep 10)
                                  (reduce + (range 1000)))]

             (let [start (System/currentTimeMillis)
                   result1 @expensive-spin
                   time1 (- (System/currentTimeMillis) start)]
               (is (= 499500 result1))
               (is (= 1 @exec-count))
               (is (>= time1 10) "Should take at least 10ms"))

             (let [start (System/currentTimeMillis)
                   result2 @expensive-spin
                   time2 (- (System/currentTimeMillis) start)]
               (is (= 499500 result2))
               (is (= 1 @exec-count) "Should not re-execute")
               (is (< time2 5) "Should be instant from cache"))))))))

;; =============================================================================
;; Signal Consumption and Dependency Tracking (cross-platform)
;; =============================================================================

(deftest test-spin-tracks-signal
  (testing "Spin can track a signal"
    (async done
      (with-ctx [_ctx]
        (let [counter (sig/signal 42)
              consumer-spin (spin
                              (let [{:keys [new]} (track counter)]
                                (* 2 new)))]
          (run-spin! consumer-spin
                     (fn [result]
                       (is (= 84 result))
                       (done))
                     (fn [_] (done))))))))

(deftest test-spin-tracks-multiple-signals
  (testing "Spin can track multiple signals"
    (async done
      (with-ctx [_ctx]
        (let [x-signal (sig/signal 10)
              y-signal (sig/signal 20)
              sum-spin (spin
                         (let [{x :new} (track x-signal)
                               {y :new} (track y-signal)]
                           (+ x y)))]
          (run-spin! sum-spin
                     (fn [result]
                       (is (= 30 result))
                       (done))
                     (fn [_] (done))))))))

;; =============================================================================
;; CLJ-only: Dependency graph recording (uses @deref)
;; =============================================================================

#?(:clj
   (deftest test-dependency-graph-recording
     (testing "Dependencies are recorded in the graph after spin execution"
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [x-signal (sig/signal 10)
                 y-signal (sig/signal 20)
                 sum-spin (spin
                            (let [{x :new} (track x-signal)
                                  {y :new} (track y-signal)]
                              (+ x y)))]

             (is (= 30 @sum-spin))

             (let [spin-id (spin-core/spin-id sum-spin)
                   spin-node (ec/get-state [:nodes spin-id])
                   deps (:deps spin-node)]
               (is (some? spin-node) "Spin node should exist")
               (is (contains? (:signals deps) (:id x-signal)) "x-signal should be tracked")
               (is (contains? (:signals deps) (:id y-signal)) "y-signal should be tracked")

               (let [x-observers (ec/get-state [:nodes (:id x-signal) :observers])
                     y-observers (ec/get-state [:nodes (:id y-signal) :observers])]
                 (is (contains? x-observers spin-id) "Spin should observe x-signal")
                 (is (contains? y-observers spin-id) "Spin should observe y-signal")))))))))

;; =============================================================================
;; CLJ-only: Reactive Updates (uses await-drain and @deref)
;; =============================================================================

#?(:clj
   (deftest test-signal-change-marks-spin-dirty
     (testing "When signal changes, spin is marked dirty and re-executes on next deref"
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [counter (sig/signal 0)
                 exec-count (atom 0)
                 doubled (spin
                           (let [{:keys [new]} (track counter)]
                             (swap! exec-count inc)
                             (* 2 new)))]

             (is (= 0 @doubled))
             (is (= 1 @exec-count))

             (swap! counter inc)
             (await-drain ctx)

             (is (= 2 @doubled))
             (is (= 2 @exec-count) "Spin should have re-executed")))))))

#?(:clj
   (deftest test-multiple-signal-updates
     (testing "Spin re-executes for each signal update"
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [counter (sig/signal 0)
                 exec-count (atom 0)
                 doubled (spin
                           (let [{:keys [new]} (track counter)]
                             (swap! exec-count inc)
                             (* 2 new)))]

             (is (= 0 @doubled))
             (is (= 1 @exec-count))

             (swap! counter inc)
             (await-drain ctx)
             (is (= 2 @doubled))
             (is (= 2 @exec-count))

             (swap! counter inc)
             (await-drain ctx)
             (is (= 4 @doubled))
             (is (= 3 @exec-count))

             (swap! counter + 3)
             (await-drain ctx)
             (is (= 10 @doubled))
             (is (= 4 @exec-count))))))))

#?(:clj
   (deftest test-multiple-signals-one-changes
     (testing "Spin only re-executes when one of its signals changes"
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [x (sig/signal 10)
                 y (sig/signal 20)
                 exec-count (atom 0)
                 sum-spin (spin
                            (let [{x-val :new} (track x)
                                  {y-val :new} (track y)]
                              (swap! exec-count inc)
                              (+ x-val y-val)))]

             (is (= 30 @sum-spin))
             (is (= 1 @exec-count))

             (swap! x + 5)
             (await-drain ctx)
             (is (= 35 @sum-spin))
             (is (= 2 @exec-count))

             (swap! y + 10)
             (await-drain ctx)
             (is (= 45 @sum-spin))
             (is (= 3 @exec-count))))))))

;; =============================================================================
;; Spin Composition (cross-platform)
;; =============================================================================

(deftest test-spin-awaits-spin
  (testing "Spin can await another spin"
    (async done
      (with-ctx [_ctx]
        (let [base-spin (spin (+ 1 2))
              dependent-spin (spin
                               (let [base-result (await base-spin)]
                                 (* 2 base-result)))]
          (run-spin! dependent-spin
                     (fn [result]
                       (is (= 6 result))
                       (done))
                     (fn [_] (done))))))))

(deftest test-spin-chain
  (testing "Spins can form dependency chains"
    (async done
      (with-ctx [_ctx]
        (let [spin1 (spin (+ 1 2))
              spin2 (spin (* 2 (await spin1)))
              spin3 (spin (- (await spin2) 1))]
          (run-spin! spin3
                     (fn [result]
                       (is (= 5 result))
                       (done))
                     (fn [_] (done))))))))

;; =============================================================================
;; Edge Cases (cross-platform)
;; =============================================================================

(deftest test-spin-with-nil-result
  (testing "Spin can return nil"
    (async done
      (with-ctx [_ctx]
        (let [nil-spin (spin nil)]
          (run-spin! nil-spin
                     (fn [result]
                       (is (nil? result))
                       (done))
                     (fn [_] (done))))))))

(deftest test-spin-with-false-result
  (testing "Spin can return false"
    (async done
      (with-ctx [_ctx]
        (let [false-spin (spin false)]
          (run-spin! false-spin
                     (fn [result]
                       (is (false? result))
                       (done))
                     (fn [_] (done))))))))

(deftest test-spin-with-vector-result
  (testing "Spin can return collections"
    (async done
      (with-ctx [_ctx]
        (let [vec-spin (spin [1 2 3])]
          (run-spin! vec-spin
                     (fn [result]
                       (is (= [1 2 3] result))
                       (done))
                     (fn [_] (done))))))))

(deftest test-spin-with-map-result
  (testing "Spin can return maps"
    (async done
      (with-ctx [_ctx]
        (let [map-spin (spin {:a 1 :b 2})]
          (run-spin! map-spin
                     (fn [result]
                       (is (= {:a 1 :b 2} result))
                       (done))
                     (fn [_] (done))))))))
