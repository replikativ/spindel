(ns org.replikativ.spindel.signal-test
  "Comprehensive tests for Signal functionality: creation, updates, delta tracking, and observers."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.state.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
            #?(:clj [org.replikativ.spindel.test-async :refer [await-drain]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; Basic Signal Creation and Manipulation (cross-platform)
;; =============================================================================

(deftest test-signal-creation
  (testing "Signal can be created with initial value"
    (async done
      (with-ctx [_ctx]
        (let [counter (sig/signal 0)]
          (is (some? counter))
          (is (= 0 @counter))
          (done))))))

(deftest test-signal-swap
  (testing "Signal value can be updated with swap!"
    (async done
      (with-ctx [_ctx]
        (let [counter (sig/signal 0)]
          (swap! counter inc)
          (is (= 1 @counter))

          (swap! counter + 5)
          (is (= 6 @counter))
          (done))))))

(deftest test-signal-reset
  (testing "Signal value can be replaced with reset!"
    (async done
      (with-ctx [_ctx]
        (let [counter (sig/signal 0)]
          (reset! counter 42)
          (is (= 42 @counter))
          (done))))))

(deftest test-signal-swap-changed
  (testing "swap-signal-changed? detects value changes"
    (async done
      (with-ctx [_ctx]
        (let [counter (sig/signal 0)]
          ;; Change should return true
          (is (true? (sig/swap-signal-changed? counter inc)))
          (is (= 1 @counter))

          ;; No change should return false
          (is (false? (sig/swap-signal-changed? counter identity)))
          (is (= 1 @counter))
          (done))))))

(deftest test-signal-types
  (testing "Signals work with different value types"
    (async done
      (with-ctx [_ctx]
        ;; Scalar
        (let [num (sig/signal 42)]
          (is (= 42 @num)))

        ;; Vector
        (let [vec-sig (sig/signal [1 2 3])]
          (is (= [1 2 3] @vec-sig)))

        ;; Map
        (let [map-sig (sig/signal {:a 1 :b 2})]
          (is (= {:a 1 :b 2} @map-sig)))

        ;; Nil
        (let [nil-sig (sig/signal nil)]
          (is (nil? @nil-sig)))
        (done)))))

;; =============================================================================
;; Signal State Management (cross-platform)
;; =============================================================================

(deftest test-signal-state-structure
  (testing "Signal state has correct structure"
    (async done
      (with-ctx [_ctx]
        (let [counter (sig/signal 42)
              signal-state (sig/get-signal-state counter)]

          (is (contains? signal-state :snapshot))
          (is (contains? signal-state :old-snapshot))
          (is (contains? signal-state :deltas))
          (is (contains? signal-state :deltaable?))
          (is (contains? signal-state :observers))

          (is (= 42 (d/unwrap-deltaable (:snapshot signal-state))))
          (is (nil? (:old-snapshot signal-state)) "Initially no old snapshot")
          (is (= #{} (:observers signal-state)) "Initially no observers")
          (done))))))

(deftest test-signal-state-after-update
  (testing "Signal state updates correctly after swap!/reset!"
    (async done
      (with-ctx [_ctx]
        (let [counter (sig/signal 0)]

          ;; Initial state
          (let [state-before (sig/get-signal-state counter)]
            (is (= 0 (d/unwrap-deltaable (:snapshot state-before)))))

          ;; After update
          (swap! counter inc)
          (let [state-after (sig/get-signal-state counter)]
            (is (= 1 (d/unwrap-deltaable (:snapshot state-after))))
            (is (= 0 (d/unwrap-deltaable (:old-snapshot state-after)))))

          ;; After another update
          (swap! counter + 5)
          (let [state-after (sig/get-signal-state counter)]
            (is (= 6 (d/unwrap-deltaable (:snapshot state-after))))
            (is (= 1 (d/unwrap-deltaable (:old-snapshot state-after)))))
          (done))))))

(deftest test-signal-get-detailed
  (testing "get-signal-detailed returns Interval"
    (async done
      (with-ctx [_ctx]
        (let [counter (sig/signal 10)]

          ;; Get detailed view
          (let [view (sig/get-signal-detailed counter)]
            (is (some? view))
            (is (= 10 (d/unwrap-deltaable (:new view))))
            (is (nil? (:old view))))

          ;; After update
          (swap! counter inc)
          (let [view (sig/get-signal-detailed counter)]
            (is (= 11 (d/unwrap-deltaable (:new view))))
            (is (= 10 (d/unwrap-deltaable (:old view)))))
          (done))))))

;; =============================================================================
;; Spin tracking signals (cross-platform, single execution only)
;; =============================================================================

(deftest test-signal-spin-tracking
  (testing "Spin can track a signal value"
    (async done
      (with-ctx [_ctx]
        (let [counter (sig/signal 42)
              spin-result (spin
                            (let [{:keys [new]} (track counter)]
                              (* 2 new)))]
          (run-spin! spin-result
                     (fn [result]
                       (is (= 84 result))
                       (done))
                     (fn [_] (done))))))))

(deftest test-signal-interval-destructuring
  (testing "Interval supports destructuring"
    (async done
      (with-ctx [_ctx]
        (let [counter (sig/signal 10)]

          ;; Map destructuring
          (let [map-spin (spin
                           (let [{:keys [new old delta]} (track counter)]
                             {:new new :old old :delta delta}))]
            (run-spin! map-spin
                       (fn [result]
                         (is (= 10 (:new result)))
                         (done))
                       (fn [_] (done)))))))))

(deftest test-signal-observer-registration
  (testing "Observers are registered in signal state"
    (async done
      (with-ctx [_ctx]
        (let [counter (sig/signal 0)
              spin1 (spin
                      (let [{:keys [new]} (track counter)]
                        (* 2 new)))
              spin2 (spin
                      (let [{:keys [new]} (track counter)]
                        (* 3 new)))]

          ;; Execute spins to register dependencies
          (run-spin! spin1
                     (fn [_]
                       (run-spin! spin2
                                  (fn [_]
                                    ;; Check observers are registered
                                    (let [signal-state (sig/get-signal-state counter)
                                          observers (:observers signal-state)]
                                      (is (= 2 (count observers)) "Should have 2 observers")
                                      (done)))
                                  (fn [_] (done))))
                     (fn [_] (done))))))))

;; =============================================================================
;; Delta Tracking (CLJ-only - requires await-drain for reactive updates)
;; =============================================================================

#?(:clj
   (deftest test-signal-interval-scalar
     (testing "Interval for scalar values"
       (let [ctx (ctx/create-execution-context)]
         (binding [rtc/*execution-context* ctx]
           (let [counter (sig/signal 0)
                 spin-result (spin
                               (let [view (track counter)]
                                 {:new (:new view)
                                  :old (:old view)
                                  :delta (:delta view)}))]

             ;; Initial execution
             (let [result @spin-result]
               (is (= 0 (:new result)))
               (is (nil? (:old result)))
               (is (nil? (:delta result)) "Scalars don't have deltas"))

             ;; After update
             (swap! counter inc)
             (await-drain ctx)
             (let [result @spin-result]
               (is (= 1 (:new result)))
               (is (= 0 (:old result)))
               (is (nil? (:delta result)) "Scalars don't have deltas"))))))))

#?(:clj
   (deftest test-signal-interval-vector
     (testing "Interval for vector values with deltas"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [todos (sig/signal [])
                 spin-result (spin
                               (let [view (track todos)]
                                 {:new (:new view)
                                  :old (:old view)
                                  :delta (:delta view)}))]

             ;; Initial execution
             (let [result @spin-result]
               (is (= [] (d/unwrap-deltaable (:new result))))
               (is (nil? (:old result))))

             ;; After conj
             (swap! todos conj {:text "Spin 1"})
             (await-drain rt)
             (let [result @spin-result
                   new-val (d/unwrap-deltaable (:new result))
                   old-val (d/unwrap-deltaable (:old result))]
               (is (= [{:text "Spin 1"}] new-val))
               (is (= [] old-val))
               (is (some? (:delta result))))))))))

#?(:clj
   (deftest test-signal-interval-deltaable-operations
     (testing "Deltaable collections track operations via Interval"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [items (sig/signal [])
                 deltas-spin (spin
                               (let [{:keys [delta]} (track items)]
                                 delta))]

             ;; Initial state
             @deltas-spin

             ;; Conj operation
             (swap! items conj :a)
             (await-drain rt)
             (let [deltas @deltas-spin]
               (is (some? deltas) "Should have deltas after conj"))

             ;; Multiple operations
             (swap! items conj :b)
             (await-drain rt)
             (let [deltas @deltas-spin]
               (is (some? deltas) "Should have deltas after multiple operations"))))))))

;; =============================================================================
;; Multiple Observers (CLJ-only - requires await-drain for reactive updates)
;; =============================================================================

#?(:clj
   (deftest test-signal-multiple-observers
     (testing "Multiple spins can observe the same signal"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [counter (sig/signal 0)
                 doubled (spin
                           (let [{:keys [new]} (track counter)]
                             (* 2 new)))
                 tripled (spin
                           (let [{:keys [new]} (track counter)]
                             (* 3 new)))
                 quadrupled (spin
                              (let [{:keys [new]} (track counter)]
                                (* 4 new)))]

             ;; Initial execution
             (is (= 0 @doubled))
             (is (= 0 @tripled))
             (is (= 0 @quadrupled))

             ;; Update signal - all observers should re-execute
             (swap! counter inc)
             (await-drain rt)
             (is (= 2 @doubled))
             (is (= 3 @tripled))
             (is (= 4 @quadrupled))

             ;; Another update
             (swap! counter + 5)
             (await-drain rt)
             (is (= 12 @doubled))
             (is (= 18 @tripled))
             (is (= 24 @quadrupled))))))))

#?(:clj
   (deftest test-signal-observers-independence
     (testing "Observers execute independently"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [counter (sig/signal 0)
                 exec-count-1 (atom 0)
                 exec-count-2 (atom 0)
                 spin1 (spin
                         (let [{:keys [new]} (track counter)]
                           (swap! exec-count-1 inc)
                           (* 2 new)))
                 spin2 (spin
                         (let [{:keys [new]} (track counter)]
                           (swap! exec-count-2 inc)
                           (* 3 new)))]

             ;; Both execute initially
             @spin1
             @spin2
             (is (= 1 @exec-count-1))
             (is (= 1 @exec-count-2))

             ;; Update signal
             (swap! counter inc)
             (await-drain rt)

             ;; Both re-execute
             @spin1
             @spin2
             (is (= 2 @exec-count-1))
             (is (= 2 @exec-count-2))))))))

#?(:clj
   (deftest test-signal-observer-topological-order
     (testing "Observers execute in topological order"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [counter (sig/signal 0)
                 execution-order (atom [])
                 spin1 (spin
                         (let [{:keys [new]} (track counter)]
                           (swap! execution-order conj :spin1)
                           new))
                 spin2 (spin
                         (let [t1-result (await spin1)]
                           (swap! execution-order conj :spin2)
                           (* 2 t1-result)))
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
             (await-drain rt)
             @spin1
             @spin2
             @spin3

             ;; spin1 should execute before spin2, spin2 before spin3
             (let [order @execution-order
                   spin1-idx (.indexOf order :spin1)
                   spin2-idx (.indexOf order :spin2)
                   spin3-idx (.indexOf order :spin3)]
               (is (< spin1-idx spin2-idx) "spin1 should execute before spin2")
               (is (< spin2-idx spin3-idx) "spin2 should execute before spin3"))))))))

;; =============================================================================
;; Edge Cases (CLJ-only - requires await-drain for reactive updates)
;; =============================================================================

#?(:clj
   (deftest test-signal-concurrent-updates
     (testing "Signal handles multiple updates between spin executions"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [counter (sig/signal 0)
                 spin-result (spin
                               (let [{:keys [new]} (track counter)]
                                 new))]

             ;; Initial execution
             (is (= 0 @spin-result))

             ;; Multiple updates before next deref
             (swap! counter inc)
             (swap! counter inc)
             (swap! counter inc)
             (await-drain rt)

             ;; Should see latest value
             (is (= 3 @spin-result))))))))

#?(:clj
   (deftest test-signal-same-value-update
     (testing "Signal update with same value"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [counter (sig/signal 0)
                 exec-count (atom 0)
                 spin-result (spin
                               (let [{:keys [new]} (track counter)]
                                 (swap! exec-count inc)
                                 new))]

             ;; Initial execution
             @spin-result
             (is (= 1 @exec-count))

             ;; Update with same value
             (reset! counter 0)
             (await-drain rt)

             ;; Spin should still re-execute (signal changed, even if value is same)
             @spin-result
             (is (= 2 @exec-count))))))))

#?(:clj
   (deftest test-signal-nil-values
     (testing "Signals can hold nil values"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [nullable (sig/signal nil)
                 spin-result (spin
                               (let [{:keys [new]} (track nullable)]
                                 (if (nil? new) :was-nil :was-not-nil)))]

             (is (= :was-nil @spin-result))

             (reset! nullable 42)
             (await-drain rt)
             (is (= :was-not-nil @spin-result))

             (reset! nullable nil)
             (await-drain rt)
             (is (= :was-nil @spin-result))))))))

#?(:clj
   (deftest test-signal-false-values
     (testing "Signals can hold false values"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [bool-sig (sig/signal false)
                 spin-result (spin
                               (let [{:keys [new]} (track bool-sig)]
                                 (if new :was-true :was-false)))]

             (is (= :was-false @spin-result))

             (reset! bool-sig true)
             (await-drain rt)
             (is (= :was-true @spin-result))

             (reset! bool-sig false)
             (await-drain rt)
             (is (= :was-false @spin-result)))))))

;; =============================================================================
;; Multi-Signal Dependency Preservation (CLJ-only)
;; =============================================================================

#?(:clj
   (deftest test-multi-signal-dependency-preservation
     (testing "When resuming from later signal, earlier signal dependencies are preserved"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [;; Signal A is tracked first, Signal B is tracked second
                 signal-a (sig/signal :a1)
                 signal-b (sig/signal :b1)
                 exec-count (atom 0)
                 spin-result (spin
                               (let [{:keys [new] :as a-view} (track signal-a)
                                     a-val new
                                     {:keys [new] :as b-view} (track signal-b)
                                     b-val new]
                                 (swap! exec-count inc)
                                 [a-val b-val]))]

             ;; Initial execution - both signals tracked
             (is (= [:a1 :b1] @spin-result))
             (is (= 1 @exec-count))

             ;; Change signal B - spin resumes from B's continuation
             ;; This should NOT cause signal A to be removed from dependencies
             (reset! signal-b :b2)
             (await-drain rt)
             (is (= [:a1 :b2] @spin-result))
             (is (= 2 @exec-count) "Spin should re-execute once for signal-b change")

             ;; CRITICAL TEST: Change signal A after resuming from B
             ;; Before the fix, this would NOT trigger re-execution because
             ;; signal-a was removed from observers in record-deps!
             (reset! signal-a :a2)
             (await-drain rt)
             (is (= [:a2 :b2] @spin-result) "Spin should react to signal-a changes")
             (is (= 3 @exec-count) "Spin should re-execute for signal-a change")))))))

#?(:clj
   (deftest test-multi-signal-later-then-earlier-sequence
     (testing "Changing signals in reverse order (later then earlier) maintains reactivity"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [signal-a (sig/signal 0)
                 signal-b (sig/signal 0)
                 signal-c (sig/signal 0)
                 exec-count (atom 0)
                 spin-result (spin
                               (let [{:keys [new]} (track signal-a)
                                     a new
                                     {:keys [new]} (track signal-b)
                                     b new
                                     {:keys [new]} (track signal-c)
                                     c new]
                                 (swap! exec-count inc)
                                 (+ a b c)))]

             ;; Initial execution
             (is (= 0 @spin-result))
             (is (= 1 @exec-count))

             ;; Change C (latest), then B, then A
             (reset! signal-c 100)
             (await-drain rt)
             (is (= 100 @spin-result))
             (is (= 2 @exec-count))

             ;; Now change B - should still work
             (reset! signal-b 10)
             (await-drain rt)
             (is (= 110 @spin-result))
             (is (= 3 @exec-count))

             ;; Now change A - should still work
             (reset! signal-a 1)
             (await-drain rt)
             (is (= 111 @spin-result))
             (is (= 4 @exec-count))

             ;; Change C again to verify all dependencies still active
             (reset! signal-c 200)
             (await-drain rt)
             (is (= 211 @spin-result))
             (is (= 5 @exec-count))))))))

#?(:clj
   (deftest test-conditional-signal-tracking
     (testing "Conditional branches only track signals in taken branch"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [condition (sig/signal true)
                 signal-true-branch (sig/signal :true-val)
                 signal-false-branch (sig/signal :false-val)
                 exec-count (atom 0)
                 spin-result (spin
                               (let [{:keys [new]} (track condition)
                                     cond-val new]
                                 (swap! exec-count inc)
                                 (if cond-val
                                   (let [{:keys [new]} (track signal-true-branch)]
                                     [:true-branch new])
                                   (let [{:keys [new]} (track signal-false-branch)]
                                     [:false-branch new]))))]

             ;; Initial execution - takes true branch
             (is (= [:true-branch :true-val] @spin-result))
             (is (= 1 @exec-count))

             ;; Change signal in true branch - should trigger
             (reset! signal-true-branch :true-val-2)
             (await-drain rt)
             (is (= [:true-branch :true-val-2] @spin-result))
             (is (= 2 @exec-count))

             ;; Change signal in false branch - should NOT trigger (not tracked)
             (reset! signal-false-branch :false-val-2)
             (await-drain rt)
             (is (= [:true-branch :true-val-2] @spin-result))
             (is (= 2 @exec-count) "Should NOT re-execute for untracked signal")

             ;; Switch condition to false branch
             (reset! condition false)
             (await-drain rt)
             (is (= [:false-branch :false-val-2] @spin-result))
             (is (= 3 @exec-count))

             ;; Now true branch signal should not trigger, false branch should
             (reset! signal-true-branch :true-val-3)
             (await-drain rt)
             (is (= [:false-branch :false-val-2] @spin-result))
             (is (= 3 @exec-count) "Should NOT re-execute for untracked true branch signal")

             (reset! signal-false-branch :false-val-3)
             (await-drain rt)
             (is (= [:false-branch :false-val-3] @spin-result))
             (is (= 4 @exec-count) "Should re-execute for tracked false branch signal"))))))))
