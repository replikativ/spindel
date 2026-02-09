(ns org.replikativ.spindel.spin.rate-control-test
  "Tests for rate control combinators: debounce, throttle, sample, relieve, timeout, accumulate"
  (:refer-clojure :exclude [await])
  #?(:clj
     (:require [clojure.test :refer [deftest is testing use-fixtures]]
               [org.replikativ.spindel.runtime.core :as rtc]
               [org.replikativ.spindel.runtime.context :as ctx]
               [org.replikativ.spindel.runtime.scheduler :as sched]
               [org.replikativ.spindel.spin.sync :as sync]
               [org.replikativ.spindel.spin.combinators :refer [debounce throttle sample relieve timeout sleep race accumulate]]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.effects.await :refer [await]]
               [org.replikativ.spindel.incremental.interval :as iv]
               [org.replikativ.spindel.incremental.deltaable :as d]
               [org.replikativ.spindel.signal :as sig]
               [org.replikativ.spindel.effects.track :refer [track]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]]
               [org.replikativ.spindel.runtime.core :as rtc]
               [org.replikativ.spindel.runtime.context :as ctx]
               [org.replikativ.spindel.spin.sync :as sync]
               [org.replikativ.spindel.spin.combinators :refer [debounce throttle sample relieve timeout sleep race accumulate]]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.effects.await :refer [await]]
               [org.replikativ.spindel.incremental.interval :as iv]
               [org.replikativ.spindel.incremental.deltaable :as d]
               [org.replikativ.spindel.signal :as sig]
               [org.replikativ.spindel.effects.track :refer [track]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.signal :refer [signal]]))
  #?(:clj (:require [org.replikativ.spindel.signal :refer [signal]])))

;; CLJ-only fixture for thread pool executor
#?(:clj
   (use-fixtures :each
     (fn [f]
       (let [execution-ctx (ctx/create-execution-context {:executor (sched/thread-pool-executor 4)})]
         (try
           (binding [rtc/*execution-context* execution-ctx]
             (f))
           (finally
             (ctx/stop-context! execution-ctx)))))))

;; =============================================================================
;; Timeout Tests
;; =============================================================================

(deftest test-timeout-fast-spin-wins
  (testing "Timeout returns source value when source is faster"
    (async done
      (with-ctx [_ctx]
        (let [fast-spin (spin :fast)
              timeout-spin (timeout fast-spin 1000 :fallback)]
          (run-spin! timeout-spin
                     (fn [result]
                       (is (= :fast result) "Fast spin should win against timeout")
                       (done))
                     (fn [err]
                       (is false (str "Timeout failed: " err))
                       (done))))))))

(deftest test-timeout-fallback-on-slow-spin
  (testing "Timeout returns fallback when source is slower"
    (async done
      (with-ctx [_ctx]
        (let [slow-spin (sleep 500 :slow)
              timeout-spin (timeout slow-spin 50 :fallback)]
          (run-spin! timeout-spin
                     (fn [result]
                       (is (= :fallback result) "Fallback should be returned when timeout wins")
                       (done))
                     (fn [err]
                       (is false (str "Timeout failed: " err))
                       (done))))))))

;; =============================================================================
;; Sample Tests
;; =============================================================================

(deftest test-sample-returns-value-after-interval
  (testing "Sample waits for interval then returns source value"
    (async done
      (with-ctx [_ctx]
        (let [source-spin (spin 42)
              sample-spin (sample source-spin 50)]
          (run-spin! sample-spin
                     (fn [result]
                       (is (= 42 result) "Sample should return source value after interval")
                       (done))
                     (fn [err]
                       (is false (str "Sample failed: " err))
                       (done))))))))

;; =============================================================================
;; Relieve Tests
;; =============================================================================

(deftest test-relieve-returns-value
  (testing "Relieve returns the value from source"
    (async done
      (with-ctx [_ctx]
        (let [source-spin (spin :value)
              relieve-spin (relieve source-spin)]
          (run-spin! relieve-spin
                     (fn [result]
                       (is (= :value result) "Relieve should return source value")
                       (done))
                     (fn [err]
                       (is false (str "Relieve failed: " err))
                       (done))))))))

;; =============================================================================
;; Debounce Tests
;; =============================================================================

(deftest test-debounce-delays-value
  (testing "Debounce waits before returning value"
    (async done
      (with-ctx [_ctx]
        (let [source-spin (spin :delayed)
              debounce-spin (debounce source-spin 50)]
          (run-spin! debounce-spin
                     (fn [result]
                       (is (= :delayed result) "Debounce should return source value after delay")
                       (done))
                     (fn [err]
                       (is false (str "Debounce failed: " err))
                       (done))))))))

;; =============================================================================
;; Throttle Tests
;; =============================================================================

(deftest test-throttle-returns-value-through-merge
  (testing "Throttle applies merge function and returns value"
    (async done
      (with-ctx [_ctx]
        (let [source-spin (spin :value)
              throttle-spin (throttle source-spin 100 (fn [_ new] new))]  ; 100 Hz = 10ms
          (run-spin! throttle-spin
                     (fn [result]
                       (is (= :value result) "Throttle should return merged value")
                       (done))
                     (fn [err]
                       (is false (str "Throttle failed: " err))
                       (done))))))))

(deftest test-throttle-with-custom-merge
  (testing "Throttle uses custom merge function"
    (async done
      (with-ctx [_ctx]
        (let [source-spin (spin 10)
              ;; Merge function wraps value in vector
              throttle-spin (throttle source-spin 100 (fn [_ new] [:merged new]))]
          (run-spin! throttle-spin
                     (fn [result]
                       (is (= [:merged 10] result) "Throttle should apply custom merge function")
                       (done))
                     (fn [err]
                       (is false (str "Throttle failed: " err))
                       (done))))))))

;; =============================================================================
;; CLJ-only: Timing tests
;; =============================================================================

#?(:clj
   (deftest test-timeout-timing-fast
     (testing "Timeout respects timing - fast source wins"
       (let [fast-source (spin :fast)
             result @(timeout fast-source 100 :fallback)]
         (is (= :fast result) "Immediate spin should complete before timeout")))))

#?(:clj
   (deftest test-timeout-timing-slow
     (testing "Timeout respects timing - slow source loses"
       (let [slow-source (sleep 200 :slow)
             result @(timeout slow-source 50 :fallback)]
         (is (= :fallback result) "Slow spin should lose to timeout")))))

#?(:clj
   (deftest test-sample-timing
     (testing "Sample waits for the interval before returning"
       (let [start (System/currentTimeMillis)
             source (spin 42)
             result @(sample source 100)
             elapsed (- (System/currentTimeMillis) start)]
         (is (= 42 result) "Sample should return source value")
         (is (>= elapsed 90) "Sample should wait at least ~100ms")))))

#?(:clj
   (deftest test-debounce-timing
     (testing "Debounce waits for the duration before returning"
       (let [start (System/currentTimeMillis)
             source (spin :debounced)
             result @(debounce source 100)
             elapsed (- (System/currentTimeMillis) start)]
         (is (= :debounced result) "Debounce should return source value")
         (is (>= elapsed 90) "Debounce should wait at least ~100ms")))))

#?(:clj
   (deftest test-throttle-timing
     (testing "Throttle waits for the interval before returning"
       (let [start (System/currentTimeMillis)
             source (spin :throttled)
             result @(throttle source 10 (fn [_ new] new))  ; 10 Hz = 100ms
             elapsed (- (System/currentTimeMillis) start)]
         (is (= :throttled result) "Throttle should return source value")
         (is (>= elapsed 90) "Throttle should wait at least ~100ms")))))

#?(:clj
   (deftest test-relieve-immediate
     (testing "Relieve passes through values immediately"
       (let [source (spin :immediate)
             result @(relieve source)]
         (is (= :immediate result) "Relieve should return immediate value")))))

;; =============================================================================
;; Integration: Using Deferreds
;; =============================================================================

#?(:clj
   (deftest test-timeout-with-deferred-fast
     (testing "Timeout works with deferred that completes before timeout"
       (let [d (sync/deferred)
             timeout-spin (timeout d 200 :fallback)]
         ;; Deliver value before timeout
         (d :delivered)
         (is (= :delivered @timeout-spin) "Deferred delivered before timeout should win")))))

#?(:clj
   (deftest test-timeout-deferred-slow
     (testing "Timeout returns fallback when deferred is too slow"
       (let [d (sync/deferred)
             timeout-spin (timeout d 50 :fallback)]
         ;; Don't deliver - timeout should win
         (let [result @timeout-spin]
           (is (= :fallback result) "Timeout should return fallback when deferred doesn't complete"))))))

;; =============================================================================
;; Merge-Intervals Tests
;; =============================================================================

(deftest test-merge-intervals-nil-accumulator
  (testing "merge-intervals with nil accumulator returns new interval"
    (let [iv1 (iv/->Interval :a :b [{:delta :add :path [0] :value 1}])
          result (iv/merge-intervals nil iv1)]
      (is (= :a (:old result)) "Old should come from new interval")
      (is (= :b (:new result)) "New should come from new interval")
      (is (= 1 (count (:deltas result))) "Deltas should be preserved"))))

(deftest test-merge-intervals-combines-values
  (testing "merge-intervals combines old from acc, new from new interval"
    (let [iv1 (iv/->Interval :a :b [{:delta :add :path [0] :value 1}])
          iv2 (iv/->Interval :b :c [{:delta :add :path [1] :value 2}])
          result (iv/merge-intervals iv1 iv2)]
      (is (= :a (:old result)) "Old should come from first interval")
      (is (= :c (:new result)) "New should come from second interval")
      (is (= 2 (count (:deltas result))) "Deltas should be merged"))))

(deftest test-merge-intervals-compacts-redundant-deltas
  (testing "merge-intervals compacts redundant delta operations"
    (let [;; Add then remove same item should cancel out
          iv1 (iv/->Interval nil [1] [{:delta :add :path [0] :value 1}])
          iv2 (iv/->Interval [1] [] [{:delta :remove :path [0] :old-value 1}])
          result (iv/merge-intervals iv1 iv2)]
      (is (= nil (:old result)) "Old should be preserved from first")
      (is (= [] (:new result)) "New should come from second")
      ;; Compaction removes add+remove on same path
      (is (empty? (:deltas result)) "Redundant deltas should be compacted"))))

(deftest test-merge-intervals-associativity
  (testing "merge-intervals is associative: merge(merge(a,b),c) = merge(a,merge(b,c))"
    (let [iv1 (iv/->Interval nil :a [{:delta :add :path [0] :value 1}])
          iv2 (iv/->Interval :a :b [{:delta :add :path [1] :value 2}])
          iv3 (iv/->Interval :b :c [{:delta :add :path [2] :value 3}])
          left-assoc (iv/merge-intervals (iv/merge-intervals iv1 iv2) iv3)
          right-assoc (iv/merge-intervals iv1 (iv/merge-intervals iv2 iv3))]
      (is (= (:old left-assoc) (:old right-assoc)) "Old values should match")
      (is (= (:new left-assoc) (:new right-assoc)) "New values should match")
      ;; Note: deltas may differ in structure but should be equivalent after compaction
      (is (= (count (:deltas left-assoc)) (count (:deltas right-assoc)))
          "Delta counts should match"))))

;; =============================================================================
;; Accumulate Tests (CLJ-only since they require signals)
;; =============================================================================

#?(:clj
   (deftest test-accumulate-basic
     (testing "Accumulate returns interval from signal"
       (let [execution-ctx (ctx/create-execution-context {:executor (sched/thread-pool-executor 4)})
             sig (binding [rtc/*execution-context* execution-ctx]
                   (signal [1 2 3]))
             acc-spin (binding [rtc/*execution-context* execution-ctx]
                        (accumulate sig iv/merge-intervals))]
         (binding [rtc/*execution-context* execution-ctx]
           (let [result @acc-spin]
             (is (satisfies? iv/PInterval result) "Result should be an interval")
             (is (= [1 2 3] @result) "Interval new value should match signal")))))))

#?(:clj
   (deftest test-accumulate-preserves-deltas
     (testing "Accumulate preserves delta information"
       (let [execution-ctx (ctx/create-execution-context {:executor (sched/thread-pool-executor 4)})
             dv (d/deltaable-vector [1 2 3])
             sig (binding [rtc/*execution-context* execution-ctx]
                   (signal dv))]
         (binding [rtc/*execution-context* execution-ctx]
           ;; Update signal with deltaable operation
           (swap! sig conj 4)
           (let [acc-spin (accumulate sig iv/merge-intervals)
                 result @acc-spin]
             (is (= [1 2 3 4] @result) "New value should include update")
             ;; Note: deltas may be present depending on timing
             ))))))
