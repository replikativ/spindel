(ns org.replikativ.spindel.nested-spin-invalidation-test
  "Tests for nested spin closure invalidation.

   When a parent spin re-executes, any spins it created during previous runs
   have stale closures that captured values from the old run. These child spins
   must be invalidated so they re-execute with fresh closures.

   This tests the creator-child tracking and invalidation mechanism."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.protocols :as tp]
            [org.replikativ.spindel.state.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

;; =============================================================================
;; Test: Nested spin gets fresh closure when parent reruns
;; =============================================================================

(deftest test-nested-spin-closure-update
  (testing "Nested spin uses updated closure values when parent reruns"
    (let [ctx (ctx/create-execution-context)]

      (binding [rtc/*execution-context* ctx]
        ;; Signal that the outer spin tracks
        (let [multiplier-signal (sig/signal 2)]
          ;; Outer spin creates an inner spin that captures the tracked value
          (let [outer-spin
                (spin
                 (let [{:keys [new]} (track multiplier-signal)
                       multiplier new]
                   ;; Inner spin captures 'multiplier' from outer's scope
                   (let [inner (spin (* 10 multiplier))]
                     (await inner))))]

            ;; First execution: multiplier = 2, result = 20
            (let [result-1 @outer-spin]
              (is (= 20 result-1) "First run: 10 * 2 = 20"))

            ;; Update signal
            (swap! multiplier-signal inc)  ; Now 3
            (await-drain ctx)

            ;; Second execution: multiplier = 3, result = 30
            ;; The inner spin should use the NEW multiplier value
            (let [result-2 @outer-spin]
              (is (= 30 result-2) "After signal change: 10 * 3 = 30"))))))))

;; =============================================================================
;; Test: Creator-child relationship is tracked
;; =============================================================================

(deftest test-creator-child-tracking
  (testing "Spins created during execution are tracked as children"
    (let [ctx (ctx/create-execution-context)]

      (binding [rtc/*execution-context* ctx]
        (let [child-id (atom nil)
              parent-spin
              (spin
                (let [child (spin :child-result)]
                  (reset! child-id (tp/spin-id child))
                  (await child)))]

          ;; Execute parent, which creates child
          @parent-spin

          ;; Check that child's created-by points to parent
          (let [parent-id (tp/spin-id parent-spin)
                child-node (rtc/get-state [:nodes @child-id])]
            (is (= parent-id (:created-by child-node))
                "Child's created-by should point to parent")

            ;; Check that parent's created-spins contains child
            (let [parent-node (rtc/get-state [:nodes parent-id])]
              (is (contains? (:created-spins parent-node) @child-id)
                  "Parent's created-spins should contain child"))))))))

;; =============================================================================
;; Test: Child spins are invalidated on parent re-execution
;; =============================================================================

(deftest test-child-invalidation-on-parent-rerun
  (testing "Child spins are marked dirty when parent re-executes"
    (let [ctx (ctx/create-execution-context)]

      (binding [rtc/*execution-context* ctx]
        (let [trigger-signal (sig/signal :initial)]
          (let [child-id (atom nil)
                execution-count (atom 0)
                parent-spin
                (spin
                 (let [{:keys [new]} (track trigger-signal)]
                   ;; Create child spin
                   (let [child (spin
                                (swap! execution-count inc)
                                new)]
                     (reset! child-id (tp/spin-id child))
                     (await child))))]

            ;; First execution
            (let [result-1 @parent-spin]
              (is (= :initial result-1))
              (is (= 1 @execution-count) "Child executed once"))

            ;; Update signal to trigger parent re-execution
            (reset! trigger-signal :updated)
            (await-drain ctx)

            ;; Second execution - child should also re-execute
            (let [result-2 @parent-spin]
              (is (= :updated result-2) "Parent returns new value")
              (is (= 2 @execution-count) "Child re-executed (not cached)"))))))))

