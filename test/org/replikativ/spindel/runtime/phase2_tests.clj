(ns org.replikativ.spindel.runtime.phase2-tests
  "Phase 2: High Priority Tests - Performance and caching validation

  These tests validate performance-critical optimizations:
  1. Large fan-out (100+ observers) - stress test for real-world usage
  2. Signal batching - prevents unnecessary intermediate renders
  3. Generation-based caching - validates O(1) identity checks"
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.protocols :as rtp]
            [org.replikativ.spindel.runtime.nodes :as nodes]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

;; =============================================================================
;; Test 1: Large Fan-Out (100+ observers)
;; =============================================================================

(deftest test-large-fanout-100-observers
  (testing "Single signal with 100 direct observers updates efficiently"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* ctx]
          (let [root-sig (sig/signal 1)

                ;; Create 100 spins that track the same signal
                observers (mapv (fn [i]
                                 (spin (* i (:new (track root-sig)))))
                               (range 1 101))

                ;; Create 10 intermediate aggregators (each aggregates 10 observers)
                ;; We need explicit awaits for CPS transformation
                agg-0 (spin (+ (await (nth observers 0)) (await (nth observers 1))
                               (await (nth observers 2)) (await (nth observers 3))
                               (await (nth observers 4)) (await (nth observers 5))
                               (await (nth observers 6)) (await (nth observers 7))
                               (await (nth observers 8)) (await (nth observers 9))))
                agg-1 (spin (+ (await (nth observers 10)) (await (nth observers 11))
                               (await (nth observers 12)) (await (nth observers 13))
                               (await (nth observers 14)) (await (nth observers 15))
                               (await (nth observers 16)) (await (nth observers 17))
                               (await (nth observers 18)) (await (nth observers 19))))
                agg-2 (spin (+ (await (nth observers 20)) (await (nth observers 21))
                               (await (nth observers 22)) (await (nth observers 23))
                               (await (nth observers 24)) (await (nth observers 25))
                               (await (nth observers 26)) (await (nth observers 27))
                               (await (nth observers 28)) (await (nth observers 29))))
                agg-3 (spin (+ (await (nth observers 30)) (await (nth observers 31))
                               (await (nth observers 32)) (await (nth observers 33))
                               (await (nth observers 34)) (await (nth observers 35))
                               (await (nth observers 36)) (await (nth observers 37))
                               (await (nth observers 38)) (await (nth observers 39))))
                agg-4 (spin (+ (await (nth observers 40)) (await (nth observers 41))
                               (await (nth observers 42)) (await (nth observers 43))
                               (await (nth observers 44)) (await (nth observers 45))
                               (await (nth observers 46)) (await (nth observers 47))
                               (await (nth observers 48)) (await (nth observers 49))))
                agg-5 (spin (+ (await (nth observers 50)) (await (nth observers 51))
                               (await (nth observers 52)) (await (nth observers 53))
                               (await (nth observers 54)) (await (nth observers 55))
                               (await (nth observers 56)) (await (nth observers 57))
                               (await (nth observers 58)) (await (nth observers 59))))
                agg-6 (spin (+ (await (nth observers 60)) (await (nth observers 61))
                               (await (nth observers 62)) (await (nth observers 63))
                               (await (nth observers 64)) (await (nth observers 65))
                               (await (nth observers 66)) (await (nth observers 67))
                               (await (nth observers 68)) (await (nth observers 69))))
                agg-7 (spin (+ (await (nth observers 70)) (await (nth observers 71))
                               (await (nth observers 72)) (await (nth observers 73))
                               (await (nth observers 74)) (await (nth observers 75))
                               (await (nth observers 76)) (await (nth observers 77))
                               (await (nth observers 78)) (await (nth observers 79))))
                agg-8 (spin (+ (await (nth observers 80)) (await (nth observers 81))
                               (await (nth observers 82)) (await (nth observers 83))
                               (await (nth observers 84)) (await (nth observers 85))
                               (await (nth observers 86)) (await (nth observers 87))
                               (await (nth observers 88)) (await (nth observers 89))))
                agg-9 (spin (+ (await (nth observers 90)) (await (nth observers 91))
                               (await (nth observers 92)) (await (nth observers 93))
                               (await (nth observers 94)) (await (nth observers 95))
                               (await (nth observers 96)) (await (nth observers 97))
                               (await (nth observers 98)) (await (nth observers 99))))

                ;; Create top-level observer to aggregate all 10 groups
                top-observer (spin
                               (+ (await agg-0) (await agg-1)
                                  (await agg-2) (await agg-3)
                                  (await agg-4) (await agg-5)
                                  (await agg-6) (await agg-7)
                                  (await agg-8) (await agg-9)))]

            ;; Make everything reactive by creating an observer and dereferencing it
            (let [observer (spin (await top-observer))]
              ;; Initial: Sum of (1*1 + 2*1 + ... + 100*1) = 5050
              (is (= 5050 @observer))

              ;; Measure update time
              (let [start (System/currentTimeMillis)]
                (reset! root-sig 2)
                (await-drain ctx)
                (let [elapsed (- (System/currentTimeMillis) start)]

                  ;; After: Sum of (1*2 + 2*2 + ... + 100*2) = 10100
                  (is (= 10100 @observer) "All 100 observers should update")

                  ;; Should complete reasonably fast
                  (is (< elapsed 3000)
                      (str "100-observer update should complete in <3s (was " elapsed "ms)")))))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-large-fanout-50-observers
  (testing "50 observers with 2-level aggregation"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* ctx]
          (let [root-sig (sig/signal 1)

                ;; Level 1: 50 direct observers
                level1 (mapv (fn [i] (spin (+ i (:new (track root-sig))))) (range 50))

                ;; Level 2: aggregate via explicit awaits (no map)
                level2 (spin
                         (+ (await (nth level1 0)) (await (nth level1 1)) (await (nth level1 2))
                            (await (nth level1 3)) (await (nth level1 4)) (await (nth level1 5))
                            (await (nth level1 6)) (await (nth level1 7)) (await (nth level1 8))
                            (await (nth level1 9))))]

            ;; Make reactive
            (let [observer (spin (await level2))]

              ;; Initial: 0+1+2+...+9 = 45, plus 1 ten times = 55
              (is (= 55 @observer))

              ;; Update
              (reset! root-sig 2)
              (await-drain ctx)

              ;; After: 0+1+2+...+9 = 45, plus 2 ten times = 65
              (is (= 65 @observer) "First 10 observers should update"))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Test 2: Signal Batching
;; =============================================================================

(deftest test-signal-batch-prevents-intermediate-renders
  (testing "Batch macro batches multiple signal updates"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* ctx]
          (let [sig-a (sig/signal 0)
                sig-b (sig/signal 0)
                sig-c (sig/signal 0)

                exec-count (atom 0)

                ;; Spin that observes all 3 signals
                observer (spin
                           (let [a (:new (track sig-a))
                                 b (:new (track sig-b))
                                 c (:new (track sig-c))]
                             (swap! exec-count inc)
                             (+ a b c)))]

            ;; Initial execution
            @observer
            (is (= 1 @exec-count) "Initial execution")

            ;; WITH batch: single update
            (sig/batch
              (reset! sig-a 10)
              (reset! sig-b 20)
              (reset! sig-c 30))

            (await-drain ctx)

            ;; Should execute only once more (batch groups the updates)
            (is (<= @exec-count 2)
                (str "Should execute at most twice (1 initial + 1 batch), got " @exec-count))
            (is (= 60 @observer) "Should see all updates at once")))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-signal-batch-with-nested-batches
  (testing "Nested batches work correctly"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* ctx]
          (let [sig-a (sig/signal 0)
                sig-b (sig/signal 0)

                exec-count (atom 0)

                observer (spin
                           (swap! exec-count inc)
                           (+ (:new (track sig-a))
                              (:new (track sig-b))))]

            @observer
            (reset! exec-count 0)

            ;; Nested batch
            (sig/batch
              (reset! sig-a 1)
              (sig/batch
                (reset! sig-b 2)))

            (await-drain ctx)

            (is (<= @exec-count 1)
                "Nested batches should still result in at most single execution")
            (is (= 3 @observer))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Test 3: Generation-Based Caching
;; =============================================================================

(deftest test-signal-generation-increments
  (testing "Signal generation increments on each update"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* ctx]
          (let [sig (sig/signal 0)]

            ;; Get initial generation
            (let [node1 (rtp/get-state ctx [:nodes (:id sig)])
                  gen1 (:generation node1 0)]

              ;; Update signal
              (reset! sig 1)

              (let [node2 (rtp/get-state ctx [:nodes (:id sig)])
                    gen2 (:generation node2 0)]

                (is (> gen2 gen1) "Generation should increment on update")

                ;; Update again
                (reset! sig 2)

                (let [node3 (rtp/get-state ctx [:nodes (:id sig)])
                      gen3 (:generation node3 0)]

                  (is (> gen3 gen2) "Generation should increment on second update"))))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-spin-caches-result-without-signal-change
  (testing "Spin returns cached result when no dependencies changed"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* ctx]
          (let [sig (sig/signal 1)
                exec-count (atom 0)

                test-spin (spin
                            (swap! exec-count inc)
                            (* 2 (:new (track sig))))]

            ;; Initial execution
            (is (= 2 @test-spin))
            (is (= 1 @exec-count))

            ;; Deref again - should use cached result
            (is (= 2 @test-spin))
            (is (= 1 @exec-count) "Should NOT re-execute (cached)")

            ;; Create observer to make it reactive
            (let [observer (spin (await test-spin))]
              @observer

              ;; Now update signal
              (reset! sig 5)
              (await-drain ctx)

              (is (= 10 @test-spin))
              (is (= 2 @exec-count) "Should re-execute after signal change"))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-deps-hash-exists-after-execution
  (testing "Spins have deps-hash after execution for caching"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* ctx]
          (let [sig-a (sig/signal :a)
                sig-b (sig/signal :b)

                test-spin (spin
                            (let [a (:new (track sig-a))
                                  b (:new (track sig-b))]
                              [a b]))

                spin-id (spin-core/spin-id test-spin)

                ;; Observer makes it reactive
                observer (spin (await test-spin))]

            ;; Initial execution
            @observer

            ;; Check deps-hash exists
            (let [node (rtp/get-state ctx [:nodes spin-id])
                  deps-hash (nodes/get-deps-hash node)]

              (is (some? deps-hash) "deps-hash should exist after execution")

              ;; Update signal
              (reset! sig-a :a2)
              (await-drain ctx)

              ;; Get new deps-hash
              (let [node2 (rtp/get-state ctx [:nodes spin-id])
                    deps-hash2 (nodes/get-deps-hash node2)]

                (is (some? deps-hash2) "deps-hash should exist after re-execution")
                (is (not= deps-hash deps-hash2)
                    "deps-hash should change when dependencies change")))))
        (finally
          (ctx/stop-context! ctx))))))
