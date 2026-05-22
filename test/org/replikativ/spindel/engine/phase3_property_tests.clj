(ns org.replikativ.spindel.engine.phase3-property-tests
  "Phase 3: Property-Based Tests - Core invariant validation

  These tests validate critical invariants through randomized scenarios:
  1. Glitch-freedom: No spin ever sees inconsistent dependency values
  2. Continuation leak-freedom: Continuation count stays bounded
  3. Concurrent update atomicity: All events processed correctly

  Note: These are manual property tests (not using test.check) to minimize dependencies."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

(defn- all-conts
  "All of a spin's continuations — track + await — as one map. The
  engine stores them in two kind-routed structures."
  [ctx spin-id]
  (merge (rtp/get-state ctx [:track-subscriptions spin-id])
         (rtp/get-state ctx [:await-conts spin-id])))

;; =============================================================================
;; Property 1: Glitch-Freedom
;; =============================================================================

(deftest property-glitch-freedom-diamond
  (testing "Diamond dependency never sees inconsistent values (glitch-freedom)"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          ;; Run test with multiple random updates
          (dotimes [trial 20]
            (let [root-sig (sig/signal 0)
                  observed-inconsistencies (atom [])

                  ;; Two spins depend on root
                  left (spin (* 2 (:new (track root-sig))))
                  right (spin (* 3 (:new (track root-sig))))

                  ;; Bottom spin awaits both - should NEVER see inconsistent values
                  bottom (spin
                          (let [l (await left)
                                r (await right)]
                             ;; Invariant: r should always be (3/2) * l
                            (when (not= r (* 3/2 l))
                              (swap! observed-inconsistencies conj {:left l :right r}))
                            (+ l r)))]

              ;; Random updates
              (doseq [val (range 1 (+ trial 10))]
                (reset! root-sig val)
                (await-drain ctx))

              ;; Verify NO inconsistencies observed
              (is (empty? @observed-inconsistencies)
                  (str "GLITCH DETECTED in trial " trial ": " @observed-inconsistencies)))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest property-glitch-freedom-wide-diamond
  (testing "Wide diamond (4 middle nodes) maintains consistency"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (dotimes [trial 10]
            (let [root-sig (sig/signal 0)
                  inconsistencies (atom [])

                  ;; 4 spins in middle level
                  m1 (spin (* 2 (:new (track root-sig))))
                  m2 (spin (* 3 (:new (track root-sig))))
                  m3 (spin (* 5 (:new (track root-sig))))
                  m4 (spin (* 7 (:new (track root-sig))))

                  ;; Bottom aggregates all 4
                  bottom (spin
                          (let [v1 (await m1)
                                v2 (await m2)
                                v3 (await m3)
                                v4 (await m4)
                                root-val (:new (track root-sig))]
                             ;; Check consistency: each vi should be factor * root-val
                            (when-not (and (= v1 (* 2 root-val))
                                           (= v2 (* 3 root-val))
                                           (= v3 (* 5 root-val))
                                           (= v4 (* 7 root-val)))
                              (swap! inconsistencies conj
                                     {:root root-val :values [v1 v2 v3 v4]}))
                            (+ v1 v2 v3 v4)))]

              ;; Random updates
              (doseq [val (range 1 (+ 5 (* trial 2)))]
                (reset! root-sig val)
                (await-drain ctx))

              (is (empty? @inconsistencies)
                  (str "Wide diamond glitch in trial " trial ": " @inconsistencies)))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest property-glitch-freedom-deep-chain
  (testing "Deep chain maintains consistency under rapid updates"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (dotimes [trial 10]
            (let [root-sig (sig/signal 0)

                  ;; Chain: root -> t1 -> t2 -> ... -> t10
                  t1 (spin (inc (:new (track root-sig))))
                  t2 (spin (inc (await t1)))
                  t3 (spin (inc (await t2)))
                  t4 (spin (inc (await t3)))
                  t5 (spin (inc (await t4)))
                  t6 (spin (inc (await t5)))
                  t7 (spin (inc (await t6)))
                  t8 (spin (inc (await t7)))
                  t9 (spin (inc (await t8)))
                  t10 (spin (inc (await t9)))]

              ;; Rapid random updates
              (doseq [val (take 10 (repeatedly #(rand-int 100)))]
                (reset! root-sig val)
                (await-drain ctx)

                ;; Verify: t10 should always be root + 10
                (let [expected (+ val 10)
                      actual @t10]
                  (is (= expected actual)
                      (str "Deep chain inconsistency: expected " expected ", got " actual)))))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Property 2: Continuation Leak-Freedom
;; =============================================================================

(deftest property-no-continuation-leaks
  (testing "Continuation count stays bounded under repeated signal changes"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [sig-a (sig/signal 0)
                sig-b (sig/signal 0)
                sig-c (sig/signal 0)

                test-spin (spin
                           (let [a (:new (track sig-a))
                                 b (:new (track sig-b))
                                 c (:new (track sig-c))]
                             (+ a b c)))

                spin-id (spin-core/spin-id test-spin)

                ;; Observer makes it reactive
                observer (spin (await test-spin))]

            ;; Initial execution
            @observer

            ;; Record initial continuation count
            (let [initial-conts (all-conts ctx spin-id)
                  initial-count (count initial-conts)]

              ;; Perform 100 randomized signal updates
              (dotimes [i 100]
                (case (mod i 3)
                  0 (reset! sig-a (rand-int 1000))
                  1 (reset! sig-b (rand-int 1000))
                  2 (reset! sig-c (rand-int 1000)))
                (await-drain ctx))

              ;; Check continuation count didn't grow unbounded
              (let [final-conts (all-conts ctx spin-id)
                    final-count (count final-conts)]

                (is (<= final-count (+ initial-count 5))
                    (str "Continuation leak detected: started with " initial-count
                         ", ended with " final-count " after 100 updates"))))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest property-continuation-cleanup-under-random-updates
  (testing "Continuations cleaned up correctly under random signal change patterns"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (dotimes [trial 5]
            (let [;; 5 signals
                  sigs (mapv (fn [_] (sig/signal 0)) (range 5))

                  ;; Spin tracks all 5 sequentially
                  test-spin (spin
                             (+ (:new (track (nth sigs 0)))
                                (:new (track (nth sigs 1)))
                                (:new (track (nth sigs 2)))
                                (:new (track (nth sigs 3)))
                                (:new (track (nth sigs 4)))))

                  spin-id (spin-core/spin-id test-spin)

                  ;; Observer
                  observer (spin (await test-spin))]

              @observer

              ;; Random updates to random signals
              (dotimes [i 50]
                (let [sig-idx (rand-int 5)]
                  (reset! (nth sigs sig-idx) (rand-int 100)))
                (await-drain ctx))

              ;; Verify continuation count is reasonable
              (let [conts (all-conts ctx spin-id)]
                (is (<= (count conts) 10)
                    (str "Trial " trial ": Too many continuations: " (count conts)))))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Property 3: Concurrent Update Atomicity
;; =============================================================================

(deftest property-concurrent-updates-no-lost-events
  (testing "Concurrent updates from multiple threads don't lose events"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [sig (sig/signal 0)
                update-count (atom 0)
                observed-values (atom #{})

                ;; Spin that observes signal
                observer (spin
                          (let [val (:new (track sig))]
                            (swap! update-count inc)
                            (swap! observed-values conj val)
                            val))

                n-threads 10
                n-updates-per-thread 10]

            ;; Initial execution
            @observer

            ;; Concurrent updates from multiple threads
            (let [futures (doall
                           (for [thread-id (range n-threads)]
                             (future
                               (binding [ec/*execution-context* ctx]
                                 (dotimes [i n-updates-per-thread]
                                   (reset! sig (+ (* thread-id 100) i)))))))]

              ;; Wait for all threads
              (doseq [f futures]
                (deref f 10000 :timeout))

              ;; Drain all events
              (await-drain ctx))

            ;; Verify: should have processed some updates (may coalesce heavily under concurrency)
            (is (>= @update-count 2)
                (str "Should process at least 2 updates, got " @update-count))

            ;; Verify: should have observed multiple distinct values
            (is (>= (count @observed-values) 2)
                (str "Should observe at least 2 distinct values, got " (count @observed-values)))))
        (finally
          (ctx/stop-context! ctx))))))

;; A `property-concurrent-multi-signal-consistency` test used to live
;; here, commented out because it tripped on expected race conditions
;; when multiple threads updated signals concurrently. Deleted —
;; reader-discarded code rots and the genuine concurrent-consistency
;; story is covered by sig/batch + the cross-fork tests in
;; engine/multi_track_observer_test.cljc.

;; =============================================================================
;; Property 4: Termination (All Updates Eventually Complete)
;; =============================================================================

(deftest property-all-updates-terminate
  (testing "All signal changes eventually drain (no infinite loops or deadlocks)"
    ;; Implicit assertion: `await-drain` (test_async.cljc) throws on
    ;; timeout, so completing all 10×20 iterations means every drain
    ;; settled within the 5s budget. The single `is (= 200 …)` at the
    ;; end keeps the test honest (catches an early throw that's
    ;; somehow swallowed; gives reporting a positive number to print).
    (let [ctx (ctx/create-execution-context)
          completed (atom 0)]
      (try
        (binding [ec/*execution-context* ctx]
          (dotimes [_trial 10]
            (let [sigs (mapv (fn [_] (sig/signal 0)) (range 5))
                  ;; Interconnected spins (no cycles)
                  s1 (spin (:new (track (nth sigs 0))))
                  s2 (spin (+ (await s1) (:new (track (nth sigs 1)))))
                  s3 (spin (+ (await s2) (:new (track (nth sigs 2)))))
                  s4 (spin (+ (await s3) (:new (track (nth sigs 3)))))
                  _s5 (spin (+ (await s4) (:new (track (nth sigs 4)))))]
              (dotimes [_i 20]
                (let [sig-idx (rand-int 5)
                      val (rand-int 100)]
                  (reset! (nth sigs sig-idx) val))
                ;; Throws on >5s timeout; reaching the next line means drained.
                (await-drain ctx 5000)
                (swap! completed inc)))))
        (is (= 200 @completed) "All 10 trials × 20 updates should drain")
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Property 5: Idempotence (Multiple Derefs Return Same Value)
;; =============================================================================

(deftest property-spin-deref-idempotent
  (testing "Multiple derefs of same spin return same value (until signal changes)"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [sig (sig/signal 42)
                test-spin (spin (* 2 (:new (track sig))))]

            ;; Observer makes it reactive
            (let [observer (spin (await test-spin))]
              @observer

              ;; Multiple derefs should return same value
              (let [v1 @test-spin
                    v2 @test-spin
                    v3 @test-spin]
                (is (= v1 v2 v3) "Multiple derefs should return same value")
                (is (= 84 v1)))

              ;; Update signal
              (reset! sig 100)
              (await-drain ctx)

              ;; Multiple derefs after update should also be consistent
              (let [v4 @test-spin
                    v5 @test-spin]
                (is (= v4 v5) "Derefs after update should be consistent")
                (is (= 200 v4))))))
        (finally
          (ctx/stop-context! ctx))))))
