(ns org.replikativ.spindel.spin.combinator-reactivity-test
  "Tests for combinator behavior when tracked signals change.

  Key questions being tested:
  1. Does parallel re-run when child spins' tracked signals change?
  2. Does accumulate re-run when its tracked signal changes?
  3. How do rate combinators behave with reactive sources?"
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.combinators :refer [parallel race accumulate]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

;; =============================================================================
;; Test: parallel IS reactive when child signals change
;; =============================================================================

(deftest test-parallel-reactive-to-child-signals
  (testing "parallel updates and notifies awaiters when child signals change"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [sig-a (sig/signal 1)
                sig-b (sig/signal 2)
                outer-exec-count (atom 0)
                child-a-exec-count (atom 0)
                child-b-exec-count (atom 0)
                parallel-spin-holder (atom nil)  ;; To capture parallel spin ID

                outer-spin
                (spin
                 (let [p (parallel
                          (spin
                           (let [{:keys [new]} (track sig-a)]
                             (swap! child-a-exec-count inc)
                             new))
                          (spin
                           (let [{:keys [new]} (track sig-b)]
                             (swap! child-b-exec-count inc)
                             new)))
                       _ (reset! parallel-spin-holder p)
                       results (await p)]
                    ;; swap AFTER await to count resume
                   (swap! outer-exec-count inc)
                   results))]

            ;; Initial execution
            (let [result-1 @outer-spin
                  parallel-id (when @parallel-spin-holder
                                (spin-core/spin-id @parallel-spin-holder))
                  outer-id (spin-core/spin-id outer-spin)]
              (is (= [1 2] result-1) "Initial parallel result")
              ;; outer-exec-count is 2 because:
              ;; 1. First execution when outer-spin runs
              ;; 2. Second execution when parallel completes (continuation resumes)
              ;; Actually in immediate executor, it's just once per full completion
              (is (>= @outer-exec-count 1) "Outer executed at least once")
              (is (= 1 @child-a-exec-count) "Child A executed once")
              (is (= 1 @child-b-exec-count) "Child B executed once"))

            ;; Change sig-a - parallel should update reactively
            (reset! sig-a 10)
            (await-drain ctx)

            ;; After signal change + drain, check that parallel updated
            (let [result-2 @outer-spin
                  parallel-id (when @parallel-spin-holder
                                (spin-core/spin-id @parallel-spin-holder))]
              ;; parallel should have updated to [10 2]
              (is (= [10 2] result-2) "Parallel result updated after signal change")
              ;; Child A should have re-executed
              (is (= 2 @child-a-exec-count) "Child A re-executed")
              ;; Child B should NOT have re-executed (its signal didn't change)
              (is (= 1 @child-b-exec-count) "Child B not re-executed")
              ;; Outer should have been notified and re-executed
              (is (>= @outer-exec-count 2) "Outer re-executed after parallel update"))

            ;; Change sig-b - should update again
            (reset! sig-b 20)
            (await-drain ctx)

            (let [result-3 @outer-spin]
              (is (= [10 20] result-3) "Parallel result updated after second signal change")
              (is (= 2 @child-a-exec-count) "Child A still at 2")
              (is (= 2 @child-b-exec-count) "Child B re-executed"))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Test: race does NOT re-run when winner's signal changes
;; =============================================================================

(deftest test-race-not-reactive-after-winner
  (testing "race completes once with winner and ignores subsequent signal changes"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [sig-fast (sig/signal :fast-1)
                sig-slow (sig/signal :slow-1)
                outer-exec-count (atom 0)

                outer-spin
                (spin
                 (swap! outer-exec-count inc)
                 (await (race
                         (spin (:new (track sig-fast)))
                         (spin (:new (track sig-slow))))))]

            ;; Initial execution - first spin wins (both immediate)
            (let [result-1 @outer-spin]
              (is (#{:fast-1 :slow-1} result-1) "Race returns one result")
              (is (= 1 @outer-exec-count) "Outer executed once"))

            ;; Change signal - race already completed
            (reset! sig-fast :fast-2)
            (await-drain ctx)

            (let [result-2 @outer-spin]
              (is (#{:fast-1 :slow-1} result-2) "Race result unchanged (one-shot)")
              (is (= 1 @outer-exec-count) "Outer still executed only once"))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Test: accumulate IS reactive to signal changes
;; =============================================================================

(deftest test-accumulate-is-reactive
  (testing "accumulate re-runs when its tracked signal changes, propagating to awaiter"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [counter-sig (sig/signal 0)

                ;; accumulate creates a spin that tracks the signal
                acc-spin (accumulate counter-sig iv/merge-intervals)

                ;; Outer spin that awaits accumulate
                ;; Note: exec-count AFTER await to count re-executions
                outer-exec-count (atom 0)
                outer-spin
                (spin
                 (let [iv (await acc-spin)]
                   (swap! outer-exec-count inc)
                   (:new iv)))]

            ;; Initial execution
            (let [result-1 @outer-spin]
              (is (= 0 result-1) "Initial accumulate value")
              (is (= 1 @outer-exec-count) "Outer executed once"))

            ;; Change signal - accumulate should re-run
            (reset! counter-sig 1)
            (await-drain ctx)

            ;; Check if outer got updated
            (let [result-2 @outer-spin]
              ;; await continuation is resumed when acc-spin completes again
              (is (= 1 result-2) "Accumulate value updated")
              (is (= 2 @outer-exec-count) "Outer continuation resumed"))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Test: Outer spin with direct track re-runs, child spins inherit
;; =============================================================================

(deftest test-outer-track-creates-new-parallel
  (testing "When outer spin tracks signal, it re-runs and creates new parallel"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [multiplier-sig (sig/signal 2)
                outer-exec-count (atom 0)

                outer-spin
                (spin
                 (let [mult (:new (track multiplier-sig))]
                    ;; swap AFTER track so it runs on re-execution
                   (swap! outer-exec-count inc)
                    ;; Each run creates NEW parallel and child spins
                   (let [results (await (parallel
                                         (spin (* 10 mult))
                                         (spin (* 20 mult))))]
                     results)))]

            ;; Initial execution
            (let [result-1 @outer-spin]
              (is (= [20 40] result-1) "Initial parallel result (mult=2)")
              (is (= 1 @outer-exec-count) "Outer executed once"))

            ;; Change multiplier - outer re-runs from track breakpoint
            (reset! multiplier-sig 3)
            (await-drain ctx)

            (let [result-2 @outer-spin]
              ;; Outer re-ran, created NEW parallel with NEW child spins
              (is (= [30 60] result-2) "Parallel result updated (mult=3)")
              (is (= 2 @outer-exec-count) "Outer re-executed"))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Test: Multiple levels of await propagate reactivity
;; =============================================================================

(deftest test-await-chain-propagates-reactivity
  (testing "Signal change propagates through chain of awaiting spins"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [counter (sig/signal 0)
                execution-order (atom [])

                ;; Level 1: Tracks signal - exactly like signal_test
                spin1 (spin
                       (let [{:keys [new]} (track counter)]
                         (swap! execution-order conj :spin1)
                         new))

                ;; Level 2: Awaits level 1
                spin2 (spin
                       (let [t1-result (await spin1)]
                         (swap! execution-order conj :spin2)
                         (* 2 t1-result)))

                ;; Level 3: Awaits level 2
                spin3 (spin
                       (let [t2-result (await spin2)]
                         (swap! execution-order conj :spin3)
                         (* 3 t2-result)))]

            ;; Initial execution
            @spin1
            @spin2
            @spin3
            (reset! execution-order [])

            ;; Update signal - should execute in dependency order
            (swap! counter inc)
            (await-drain ctx)

            ;; Get results after drain
            (let [r1 @spin1
                  r2 @spin2
                  r3 @spin3]

              ;; spin1 should execute before spin2, spin2 before spin3
              (let [order @execution-order
                    spin1-idx (.indexOf order :spin1)
                    spin2-idx (.indexOf order :spin2)
                    spin3-idx (.indexOf order :spin3)]
                (is (>= spin1-idx 0) "spin1 should have executed")
                (is (>= spin2-idx 0) "spin2 should have executed")
                (is (>= spin3-idx 0) "spin3 should have executed")
                (when (and (>= spin1-idx 0) (>= spin2-idx 0))
                  (is (< spin1-idx spin2-idx) "spin1 should execute before spin2"))
                (when (and (>= spin2-idx 0) (>= spin3-idx 0))
                  (is (< spin2-idx spin3-idx) "spin2 should execute before spin3"))))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Test: accumulate accumulates across multiple signal changes
;; =============================================================================

(deftest test-accumulate-merges-intervals
  (testing "accumulate merges intervals from multiple signal changes"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [items-sig (sig/signal [])

                ;; accumulate should merge intervals across changes
                acc-spin (accumulate items-sig iv/merge-intervals)

                outer-spin
                (spin
                 (let [iv (await acc-spin)]
                   {:new (:new iv)
                    :old (:old iv)
                    :deltas (:deltas iv)}))]

            ;; Initial execution
            (let [result-1 @outer-spin]
              (is (= [] (:new result-1)) "Initial empty vector"))

            ;; First update
            (swap! items-sig conj :a)
            (await-drain ctx)

            (let [result-2 @outer-spin]
              (is (= [:a] (:new result-2)) "After first conj")
              (is (some? (:deltas result-2)) "Has deltas"))

            ;; Second update
            (swap! items-sig conj :b)
            (await-drain ctx)

            (let [result-3 @outer-spin]
              (is (= [:a :b] (:new result-3)) "After second conj"))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Test: parallel with non-tracking children is one-shot
;; =============================================================================

(deftest test-parallel-pure-children-one-shot
  (testing "parallel with pure (non-tracking) children completes once"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [exec-count (atom 0)

                outer-spin
                (spin
                 (swap! exec-count inc)
                 (await (parallel
                         (spin (+ 1 2))
                         (spin (* 3 4)))))]

            ;; Execute multiple times - result should be cached
            (is (= [3 12] @outer-spin))
            (is (= [3 12] @outer-spin))
            (is (= [3 12] @outer-spin))

            ;; Only executed once (cached)
            (is (= 1 @exec-count))))
        (finally
          (ctx/stop-context! ctx))))))
