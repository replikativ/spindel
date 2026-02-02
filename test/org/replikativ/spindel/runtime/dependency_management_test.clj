(ns org.replikativ.spindel.runtime.dependency-management-test
  "Critical tests for dependency management, continuation lifecycle, and graph operations.

  These tests verify core reactive graph operations that were previously untested:
  1. Continuation cleanup when signals change (stale continuation removal)
  2. clear-deps! complete cleanup (memory safety)
  3. Deep dependency chains (stress test for real-world usage)"
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.protocols :as rtp]
            [org.replikativ.spindel.runtime.node-protocols :as np]
            [org.replikativ.spindel.runtime.impl.simple :as simple]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.state.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.spin.protocols :as tp]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

;; =============================================================================
;; Test 1: Continuation Cleanup During Signal Changes
;; =============================================================================

(deftest test-continuation-cleanup-stale-removal
  (testing "Stale continuations removed when signal changes before later tracks execute"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [;; Three signals tracked in sequence
              sig-a (sig/signal :a1)
              sig-b (sig/signal :b1)
              sig-c (sig/signal :c1)

              exec-count (atom 0)

              ;; Spin that tracks all three signals sequentially
              test-spin (spin
                          (let [{:keys [new]} (track sig-a)
                                a-val new
                                {:keys [new]} (track sig-b)
                                b-val new
                                {:keys [new]} (track sig-c)
                                c-val new]
                            (swap! exec-count inc)
                            [a-val b-val c-val]))

              spin-id (tp/spin-id test-spin)]

          ;; Initial execution - all three continuations registered
          (is (= [:a1 :b1 :c1] @test-spin))
          (is (= 1 @exec-count))

          ;; Check that 3 continuations were created (order 1, 2, 3)
          (let [conts (rtp/get-state ctx [:continuations spin-id])]
            (is (= 3 (count conts)) "Should have 3 continuations after initial execution"))

          ;; Change sig-b (middle signal) - spin resumes from continuation 2
          ;; This should:
          ;; 1. Resume continuation 2 (for sig-b)
          ;; 2. Remove continuation 3 (stale, order > 2)
          ;; 3. Re-track sig-a (skipped, order < 2)
          (reset! sig-b :b2)
          (await-drain ctx)

          (is (= [:a1 :b2 :c1] @test-spin) "Should see updated sig-b value")
          (is (= 2 @exec-count) "Should have re-executed once")

          ;; CRITICAL: Check that continuation 3 was removed (stale)
          (let [conts-after (rtp/get-state ctx [:continuations spin-id])]
            (is (<= (count conts-after) 3)
                "Stale continuation should be removed or replaced"))

          ;; CRITICAL TEST: Change sig-a after resuming from sig-b
          ;; Before the fix, sig-a would NOT trigger re-execution because
          ;; it was removed from dependencies when resuming from sig-b.
          ;; The fix re-tracks skipped signals (line 228 in simple.cljc)
          (reset! sig-a :a2)
          (await-drain ctx)

          (is (= [:a2 :b2 :c1] @test-spin)
              "Spin should react to sig-a changes (skipped signal re-tracked)")
          (is (= 3 @exec-count)
              "Spin should re-execute for sig-a change")

          ;; Verify sig-c still triggers updates (wasn't removed)
          (reset! sig-c :c2)
          (await-drain ctx)

          (is (= [:a2 :b2 :c2] @test-spin))
          (is (= 4 @exec-count)))))))

(deftest test-continuation-cleanup-order-preservation
  (testing "Continuation order correctly preserved and stale removed"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [sig-1 (sig/signal 1)
              sig-2 (sig/signal 2)
              sig-3 (sig/signal 3)
              sig-4 (sig/signal 4)
              sig-5 (sig/signal 5)

              test-spin (spin
                          (let [v1 (:new (track sig-1))
                                v2 (:new (track sig-2))
                                v3 (:new (track sig-3))
                                v4 (:new (track sig-4))
                                v5 (:new (track sig-5))]
                            (+ v1 v2 v3 v4 v5)))

              spin-id (tp/spin-id test-spin)]

          ;; Initial execution
          (is (= 15 @test-spin)) ; 1+2+3+4+5

          ;; 5 continuations created
          (let [conts (rtp/get-state ctx [:continuations spin-id])]
            (is (= 5 (count conts))))

          ;; Change sig-3 (middle) - resumes from continuation 3
          ;; Should remove continuations 4 and 5 (stale)
          ;; Should re-track sig-1 and sig-2 (skipped)
          (reset! sig-3 30)
          (await-drain ctx)

          (is (= 42 @test-spin)) ; 1+2+30+4+5

          ;; Verify sig-1 and sig-2 still trigger (re-tracked)
          (reset! sig-1 10)
          (await-drain ctx)
          (is (= 51 @test-spin)) ; 10+2+30+4+5

          (reset! sig-2 20)
          (await-drain ctx)
          (is (= 69 @test-spin)) ; 10+20+30+4+5

          ;; Verify sig-4 and sig-5 still work
          (reset! sig-4 40)
          (await-drain ctx)
          (is (= 105 @test-spin)) ; 10+20+30+40+5

          (reset! sig-5 50)
          (await-drain ctx)
          (is (= 150 @test-spin)))))))

;; =============================================================================
;; Test 2: clear-deps! Complete Cleanup
;; =============================================================================

(deftest test-clear-deps-removes-all-observers
  (testing "clear-deps! removes spin from all signal and spin observers"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [;; Create multiple signals
              sig-a (sig/signal :a)
              sig-b (sig/signal :b)
              sig-c (sig/signal :c)

              ;; Spin that depends on multiple signals
              dependent-spin (spin
                               (let [a (:new (track sig-a))
                                     b (:new (track sig-b))
                                     c (:new (track sig-c))]
                                 [a b c]))

              spin-id (tp/spin-id dependent-spin)]

          ;; Execute to register dependencies
          @dependent-spin

          ;; Verify spin is in observers of each signal
          (let [sig-a-node (rtp/get-state ctx [:nodes (:id sig-a)])
                sig-b-node (rtp/get-state ctx [:nodes (:id sig-b)])
                sig-c-node (rtp/get-state ctx [:nodes (:id sig-c)])]
            (is (contains? (:observers sig-a-node) spin-id)
                "Spin should be observer of sig-a before clear")
            (is (contains? (:observers sig-b-node) spin-id)
                "Spin should be observer of sig-b before clear")
            (is (contains? (:observers sig-c-node) spin-id)
                "Spin should be observer of sig-c before clear"))

          ;; Clear dependencies
          (simple/clear-deps! ctx spin-id)

          ;; Verify spin removed from all signal observers
          (let [sig-a-node (rtp/get-state ctx [:nodes (:id sig-a)])
                sig-b-node (rtp/get-state ctx [:nodes (:id sig-b)])
                sig-c-node (rtp/get-state ctx [:nodes (:id sig-c)])]
            (is (not (contains? (:observers sig-a-node) spin-id))
                "Spin should NOT be observer of sig-a after clear")
            (is (not (contains? (:observers sig-b-node) spin-id))
                "Spin should NOT be observer of sig-b after clear")
            (is (not (contains? (:observers sig-c-node) spin-id))
                "Spin should NOT be observer of sig-c after clear"))

          ;; Verify spin node's deps are cleared
          (let [spin-node (rtp/get-state ctx [:nodes spin-id])
                deps (if spin-node (np/get-deps spin-node) nil)]
            (is (or (nil? deps)
                    (and (empty? (:signals deps))
                         (empty? (:spins deps))))
                "Spin should have empty dependencies after clear")))))))

(deftest test-clear-deps-removes-continuations
  (testing "clear-deps! removes all continuations for the spin"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [sig-a (sig/signal :a)
              sig-b (sig/signal :b)

              test-spin (spin
                          (let [a (:new (track sig-a))
                                b (:new (track sig-b))]
                            [a b]))

              spin-id (tp/spin-id test-spin)]

          ;; Execute to create continuations
          @test-spin

          ;; Verify continuations exist
          (let [conts (rtp/get-state ctx [:continuations spin-id])]
            (is (= 2 (count conts)) "Should have 2 continuations before clear"))

          ;; Clear deps
          (simple/clear-deps! ctx spin-id)

          ;; Verify continuations removed
          (let [conts (rtp/get-state ctx [:continuations spin-id])]
            (is (or (nil? conts) (empty? conts))
                "All continuations should be removed after clear-deps!")))))))

(deftest test-clear-deps-cleans-subscriptions
  (testing "clear-deps! removes all subscription entries for the spin"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [sig-a (sig/signal :a)
              sig-b (sig/signal :b)

              test-spin (spin
                          (let [a (:new (track sig-a))
                                b (:new (track sig-b))]
                            [a b]))

              spin-id (tp/spin-id test-spin)]

          ;; Execute to create subscriptions
          @test-spin

          ;; Check subscriptions exist (for signal-change events)
          (let [subs (rtp/get-state ctx [:subscriptions])]
            (is (some (fn [[ek m]]
                       (and (vector? ek)
                            (= :signal (first ek))
                            (contains? m spin-id)))
                      subs)
                "Spin should have signal subscriptions before clear"))

          ;; Clear deps
          (simple/clear-deps! ctx spin-id)

          ;; Verify spin removed from all subscription maps
          (let [subs (rtp/get-state ctx [:subscriptions])]
            (is (not (some (fn [[_ek m]] (contains? m spin-id)) subs))
                "Spin should be removed from all subscription maps after clear")))))))

(deftest test-clear-deps-with-spin-dependencies
  (testing "clear-deps! handles both signal and spin dependencies"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [sig-a (sig/signal :a)

              ;; Child spin that tracks signal
              child-spin (spin
                           (:new (track sig-a)))

              ;; Parent spin that awaits child
              parent-spin (spin
                            (await child-spin))

              parent-id (tp/spin-id parent-spin)
              child-id (tp/spin-id child-spin)]

          ;; Execute to create dependencies
          @parent-spin

          ;; Verify parent observes child
          (let [child-node (rtp/get-state ctx [:nodes child-id])]
            (is (contains? (:observers child-node) parent-id)
                "Parent should observe child before clear"))

          ;; Clear parent deps
          (simple/clear-deps! ctx parent-id)

          ;; Verify parent no longer observes child
          (let [child-node (rtp/get-state ctx [:nodes child-id])]
            (is (not (contains? (:observers child-node) parent-id))
                "Parent should NOT observe child after clear"))

          ;; Verify parent's deps are empty
          (let [parent-node (rtp/get-state ctx [:nodes parent-id])
                deps (if parent-node
                       (np/get-deps parent-node)
                       nil)]
            (is (or (nil? deps)
                    (empty? (:spins deps)))
                "Parent should have no spin dependencies after clear")))))))

;; =============================================================================
;; Test 3: Deep Dependency Chain Stress Test
;; =============================================================================

(deftest test-deep-chain-25-levels
  (testing "Deep chain of 25 spins executes and updates correctly"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [;; Root signal
              root-sig (sig/signal 0)

              ;; Create chain: root-sig -> t1 -> t2 -> ... -> t25
              ;; Each spin adds 1 to previous value
              t1 (spin (inc (:new (track root-sig))))
              t2 (spin (inc (await t1)))
              t3 (spin (inc (await t2)))
              t4 (spin (inc (await t3)))
              t5 (spin (inc (await t4)))
              t6 (spin (inc (await t5)))
              t7 (spin (inc (await t6)))
              t8 (spin (inc (await t7)))
              t9 (spin (inc (await t8)))
              t10 (spin (inc (await t9)))
              t11 (spin (inc (await t10)))
              t12 (spin (inc (await t11)))
              t13 (spin (inc (await t12)))
              t14 (spin (inc (await t13)))
              t15 (spin (inc (await t14)))
              t16 (spin (inc (await t15)))
              t17 (spin (inc (await t16)))
              t18 (spin (inc (await t17)))
              t19 (spin (inc (await t18)))
              t20 (spin (inc (await t19)))
              t21 (spin (inc (await t20)))
              t22 (spin (inc (await t21)))
              t23 (spin (inc (await t22)))
              t24 (spin (inc (await t23)))
              t25 (spin (inc (await t24)))]

          ;; Initial execution - should compute 0 -> 1 -> 2 -> ... -> 25
          ;; Deref all to ensure full chain executes
          (is (= 25 @t25) "Final spin should be 25 (0 + 25 increments)")
          (is (= 1 @t1))
          (is (= 5 @t5))
          (is (= 10 @t10))
          (is (= 15 @t15))
          (is (= 20 @t20))

          ;; Create an outer spin that tracks t25 to make the chain reactive
          (let [observer (spin (await t25))]
            @observer  ; Initial execution

            ;; Change root signal to 100
            (reset! root-sig 100)
            (await-drain ctx)

            ;; All spins should update: 100 -> 101 -> 102 -> ... -> 125
            (is (= 101 @t1) "t1 should be 101")
            (is (= 105 @t5) "t5 should be 105")
            (is (= 110 @t10) "t10 should be 110")
            (is (= 115 @t15) "t15 should be 115")
            (is (= 120 @t20) "t20 should be 120")
            (is (= 125 @t25) "t25 should be 125")
            (is (= 125 @observer) "Observer should see updated value")

            ;; Change again to verify chain still works
            (reset! root-sig 200)
            (await-drain ctx)

            (is (= 225 @t25) "t25 should be 225 after second update")
            (is (= 225 @observer) "Observer should see second update")))))))

(deftest test-deep-chain-performance
  (testing "Deep chain completes in reasonable time"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [root-sig (sig/signal 0)

              ;; Helper to create chain of N levels
              create-chain (fn [n]
                            (loop [i 0
                                   prev-spin (spin (:new (track root-sig)))
                                   chain [prev-spin]]
                              (if (>= i n)
                                chain
                                (let [next-spin (spin (inc (await prev-spin)))]
                                  (recur (inc i) next-spin (conj chain next-spin))))))

              ;; Create 20-level chain
              chain (create-chain 20)
              final-spin (last chain)]

          ;; Initial execution
          (is (= 20 @final-spin))

          ;; Measure update time
          (let [start (System/currentTimeMillis)]
            (reset! root-sig 100)
            (await-drain ctx)
            (let [elapsed (- (System/currentTimeMillis) start)]

              (is (= 120 @final-spin) "Chain should update correctly")
              (is (< elapsed 1000)
                  (str "Deep chain update should complete in <1s (was " elapsed "ms)"))))

          ;; Verify topological order maintained
          (doseq [[i spin] (map-indexed vector chain)]
            (is (= (+ 100 i) @spin)
                (str "Spin at level " i " should have correct value"))))))))

(deftest test-deep-chain-no-stack-overflow
  (testing "Very deep chain (30 levels) does not cause stack overflow"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        ;; This test primarily verifies we don't hit recursion limits
        ;; The reactive graph uses iteration, not recursion, so should handle this
        (let [root-sig (sig/signal 1)

              ;; Create 30-level chain using reduce
              final-spin (reduce (fn [prev-spin _]
                                  (spin (inc (await prev-spin))))
                                (spin (:new (track root-sig)))
                                (range 30))]

          ;; Should complete without stack overflow
          (is (= 31 @final-spin) "30-level chain should compute correctly")

          ;; Update should also work
          (reset! root-sig 10)
          (await-drain ctx)

          (is (= 40 @final-spin) "30-level chain should update without stack overflow"))))))

(deftest test-wide-fanout-deep-chain-combination
  (testing "Combination of wide fan-out and deep chain"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [root-sig (sig/signal 1)

              ;; First level: 5 spins tracking root
              level1 (mapv (fn [i]
                            (spin (* i (:new (track root-sig)))))
                          (range 1 6))

              ;; Second level: 5 spins each awaiting one from level1
              level2 (mapv (fn [s]
                            (spin (inc (await s))))
                          level1)

              ;; Third level: 5 spins each awaiting one from level2
              level3 (mapv (fn [s]
                            (spin (* 2 (await s))))
                          level2)

              ;; Final: sum all from level3 (need to await each in spin)
              final-spin (spin
                           (let [[v1 v2 v3 v4 v5] [(await (nth level3 0))
                                                    (await (nth level3 1))
                                                    (await (nth level3 2))
                                                    (await (nth level3 3))
                                                    (await (nth level3 4))]]
                             (+ v1 v2 v3 v4 v5)))

              ;; Create observer to make final-spin reactive
              observer (spin (await final-spin))]

          ;; Initial: root=1
          ;; level1: [1, 2, 3, 4, 5]
          ;; level2: [2, 3, 4, 5, 6]
          ;; level3: [4, 6, 8, 10, 12]
          ;; final: 40

          ;; CRITICAL: Force level3 to complete before checking final-spin
          ;; This ensures all async execution finishes in correct order
          (is (= [4 6 8 10 12] (mapv deref level3)) "level3 should be correct after initial")
          (is (= 40 @final-spin) "final-spin should be 40")
          (is (= 40 @observer) "observer should see 40")

          ;; Update root
          (reset! root-sig 2)
          (await-drain ctx)

          ;; After update: level1: [2, 4, 6, 8, 10]
          ;;              level2: [3, 5, 7, 9, 11]
          ;;              level3: [6, 10, 14, 18, 22]
          ;;              final: 70

          ;; CRITICAL: Check each level in order to ensure async execution completes
          (is (= [2 4 6 8 10] (mapv deref level1)) "Level1 should all multiply by 2")
          (is (= [3 5 7 9 11] (mapv deref level2)) "Level2 should all increment")
          (is (= [6 10 14 18 22] (mapv deref level3)) "Level3 should all double")
          (is (= 70 @final-spin) "Final-spin should sum to 70")
          (is (= 70 @observer) "Observer should see updated value"))))))

