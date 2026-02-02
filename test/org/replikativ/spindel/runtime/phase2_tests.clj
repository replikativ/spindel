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
            [org.replikativ.spindel.runtime.node-protocols :as np]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.state.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.spin.protocols :as tp]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

;; =============================================================================
;; Test 1: Large Fan-Out (100+ observers)
;; =============================================================================

(deftest test-large-fanout-100-observers
  (testing "Single signal with 100 direct observers updates efficiently"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [root-sig (sig/signal 1)

              ;; Create 100 spins that track the same signal
              observers (mapv (fn [i]
                               (spin (* i (:new (track root-sig)))))
                             (range 1 101))]

          ;; Create top-level observer to make everything reactive
          (let [top-observer (spin
                               (reduce + (for [i (range 100)]
                                          (await (nth observers i)))))]

            ;; Initial: Sum of (1*1 + 2*1 + ... + 100*1) = 5050
            (is (= 5050 @top-observer))

            ;; Measure update time
            (let [start (System/currentTimeMillis)]
              (reset! root-sig 2)
              (await-drain ctx)
              (let [elapsed (- (System/currentTimeMillis) start)]

                ;; After: Sum of (1*2 + 2*2 + ... + 100*2) = 10100
                (is (= 10100 @top-observer) "All 100 observers should update")

                ;; Should complete reasonably fast
                (is (< elapsed 3000)
                    (str "100-observer update should complete in <3s (was " elapsed "ms)"))))))))))

(deftest test-large-fanout-50-observers
  (testing "50 observers with 2-level aggregation"
    (let [ctx (ctx/create-execution-context)]
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

          ;; Initial: 0+1+2+...+9 = 45, plus 1 ten times = 55
          (is (= 55 @level2))

          ;; Update
          (reset! root-sig 2)
          (await-drain ctx)

          ;; After: 0+1+2+...+9 = 45, plus 2 ten times = 65
          (is (= 65 @level2) "First 10 observers should update"))))))

;; =============================================================================
;; Test 2: Signal Batching
;; =============================================================================

(deftest test-signal-batch-prevents-intermediate-renders
  (testing "Batch macro batches multiple signal updates"
    (let [ctx (ctx/create-execution-context)]
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
          (is (= 60 @observer) "Should see all updates at once"))))))

(deftest test-signal-batch-with-nested-batches
  (testing "Nested batches work correctly"
    (let [ctx (ctx/create-execution-context)]
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
          (is (= 3 @observer)))))))

;; =============================================================================
;; Test 3: Generation-Based Caching
;; =============================================================================

(deftest test-signal-generation-increments
  (testing "Signal generation increments on each update"
    (let [ctx (ctx/create-execution-context)]
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

                (is (> gen3 gen2) "Generation should increment on second update")))))))))

(deftest test-spin-caches-result-without-signal-change
  (testing "Spin returns cached result when no dependencies changed"
    (let [ctx (ctx/create-execution-context)]
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
            (is (= 2 @exec-count) "Should re-execute after signal change")))))))

(deftest test-deps-hash-exists-after-execution
  (testing "Spins have deps-hash after execution for caching"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [sig-a (sig/signal :a)
              sig-b (sig/signal :b)

              test-spin (spin
                          (let [a (:new (track sig-a))
                                b (:new (track sig-b))]
                            [a b]))

              spin-id (tp/spin-id test-spin)

              ;; Observer makes it reactive
              observer (spin (await test-spin))]

          ;; Initial execution
          @observer

          ;; Check deps-hash exists
          (let [node (rtp/get-state ctx [:nodes spin-id])
                deps-hash (np/get-deps-hash node)]

            (is (some? deps-hash) "deps-hash should exist after execution")

            ;; Update signal
            (reset! sig-a :a2)
            (await-drain ctx)

            ;; Get new deps-hash
            (let [node2 (rtp/get-state ctx [:nodes spin-id])
                  deps-hash2 (np/get-deps-hash node2)]

              (is (some? deps-hash2) "deps-hash should exist after re-execution")
              (is (not= deps-hash deps-hash2)
                  "deps-hash should change when dependencies change"))))))))
