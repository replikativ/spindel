(ns org.replikativ.spindel.v2.port.signal-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture api hot-spin]]))

(use-fixtures :each checked-fixture)

(deftest test-signal-interval-scalar
  (testing "Interval for scalar values"
    (let [ctx v2/*world*]
      (let [counter (v2/signal 0)
            spin-result (hot-spin
                         (let [view (track counter)]
                           {:new (:new view)
                            :old (:old view)
                            :deltas (:deltas view)}))]

           ;; Initial execution
        (let [result @spin-result]
          (is (= 0 (:new result)))
          (is (nil? (:old result)))
          (is (nil? (:deltas result)) "Scalars don't have deltas"))

           ;; After update
        (swap! counter inc)

        (let [result @spin-result]
          (is (= 1 (:new result)))
          (is (= 0 (:old result)))
          (is (nil? (:deltas result)) "Scalars don't have deltas"))))))

(deftest test-signal-interval-vector
  (testing "Interval for vector values with deltas"
    (let [rt v2/*world*]
      (let [todos (v2/signal [])
            spin-result (hot-spin
                         (let [view (track todos)]
                           {:new (:new view)
                            :old (:old view)
                            :deltas (:deltas view)}))]

           ;; Initial execution
        (let [result @spin-result]
          (is (= [] (identity (:new result))))
          (is (nil? (:old result))))

           ;; After conj
        (swap! todos conj {:text "Spin 1"})

        (let [result @spin-result
              new-val (identity (:new result))
              old-val (identity (:old result))]
          (is (= [{:text "Spin 1"}] new-val))
          (is (= [] old-val))
          (is (some? (:deltas result))))))))

(deftest test-signal-interval-deltaable-operations
  (testing "Deltaable collections track operations via Interval"
    (let [rt v2/*world*]
      (let [items (v2/signal [])
            deltas-spin (hot-spin
                         (let [{:keys [deltas]} (track items)]
                           deltas))]

           ;; Initial state
        @deltas-spin

           ;; Conj operation
        (swap! items conj :a)

        (let [deltas @deltas-spin]
          (is (some? deltas) "Should have deltas after conj"))

           ;; Multiple operations
        (swap! items conj :b)

        (let [deltas @deltas-spin]
          (is (some? deltas) "Should have deltas after multiple operations"))))))

(deftest test-signal-multiple-observers
  (testing "Multiple spins can observe the same signal"
    (let [rt v2/*world*]
      (let [counter (v2/signal 0)
            doubled (hot-spin
                     (let [{:keys [new]} (track counter)]
                       (* 2 new)))
            tripled (hot-spin
                     (let [{:keys [new]} (track counter)]
                       (* 3 new)))
            quadrupled (hot-spin
                        (let [{:keys [new]} (track counter)]
                          (* 4 new)))]

           ;; Initial execution
        (is (= 0 @doubled))
        (is (= 0 @tripled))
        (is (= 0 @quadrupled))

           ;; Update signal - all observers should re-execute
        (swap! counter inc)

        (is (= 2 @doubled))
        (is (= 3 @tripled))
        (is (= 4 @quadrupled))

           ;; Another update
        (swap! counter + 5)

        (is (= 12 @doubled))
        (is (= 18 @tripled))
        (is (= 24 @quadrupled))))))

(deftest test-signal-observers-independence
  (testing "Observers execute independently"
    (let [rt v2/*world*]
      (let [counter (v2/signal 0)
            exec-count-1 (atom 0)
            exec-count-2 (atom 0)
            spin1 (hot-spin
                   (let [{:keys [new]} (track counter)]
                     (swap! exec-count-1 inc)
                     (* 2 new)))
            spin2 (hot-spin
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

;; Both re-execute
        @spin1
        @spin2
        (is (= 2 @exec-count-1))
        (is (= 2 @exec-count-2))))))

(deftest test-signal-observer-topological-order
  (testing "Observers execute in topological order"
    (let [rt v2/*world*]
      (let [counter (v2/signal 0)
            execution-order (atom [])
            spin1 (hot-spin
                   (let [{:keys [new]} (track counter)]
                     (swap! execution-order conj :spin1)
                     new))
            spin2 (hot-spin
                   (let [t1-result (await spin1)]
                     (swap! execution-order conj :spin2)
                     (* 2 t1-result)))
            spin3 (hot-spin
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

        @spin1
        @spin2
        @spin3

           ;; spin1 should execute before spin2, spin2 before spin3
        (let [order @execution-order
              spin1-idx (.indexOf order :spin1)
              spin2-idx (.indexOf order :spin2)
              spin3-idx (.indexOf order :spin3)]
          (is (< spin1-idx spin2-idx) "spin1 should execute before spin2")
          (is (< spin2-idx spin3-idx) "spin2 should execute before spin3"))))))

(deftest test-signal-concurrent-updates
  (testing "Signal handles multiple updates between spin executions"
    (let [rt v2/*world*]
      (let [counter (v2/signal 0)
            spin-result (hot-spin
                         (let [{:keys [new]} (track counter)]
                           new))]

           ;; Initial execution
        (is (= 0 @spin-result))

           ;; Multiple updates before next deref
        (swap! counter inc)
        (swap! counter inc)
        (swap! counter inc)

;; Should see latest value
        (is (= 3 @spin-result))))))

(deftest test-signal-same-value-update
  (testing "Signal update with same value"
    (let [rt v2/*world*]
      (let [counter (v2/signal 0)
            exec-count (atom 0)
            spin-result (hot-spin
                         (let [{:keys [new]} (track counter)]
                           (swap! exec-count inc)
                           new))]

           ;; Initial execution
        @spin-result
        (is (= 1 @exec-count))

           ;; Update with same value
        (reset! counter 0)

;; Spin should still re-execute (signal changed, even if value is same)
        @spin-result
        (is (= 2 @exec-count))))))

(deftest test-signal-nil-values
  (testing "Signals can hold nil values"
    (let [rt v2/*world*]
      (let [nullable (v2/signal nil)
            spin-result (hot-spin
                         (let [{:keys [new]} (track nullable)]
                           (if (nil? new) :was-nil :was-not-nil)))]

        (is (= :was-nil @spin-result))

        (reset! nullable 42)

        (is (= :was-not-nil @spin-result))

        (reset! nullable nil)

        (is (= :was-nil @spin-result))))))

(deftest test-signal-false-values
  (testing "Signals can hold false values"
    (let [rt v2/*world*]
      (let [bool-sig (v2/signal false)
            spin-result (hot-spin
                         (let [{:keys [new]} (track bool-sig)]
                           (if new :was-true :was-false)))]

        (is (= :was-false @spin-result))

        (reset! bool-sig true)

        (is (= :was-true @spin-result))

        (reset! bool-sig false)

        (is (= :was-false @spin-result))))))

(deftest test-multi-signal-dependency-preservation
  (testing "When resuming from later signal, earlier signal dependencies are preserved"
    (let [rt v2/*world*]
      (let [;; Signal A is tracked first, Signal B is tracked second
            signal-a (v2/signal :a1)
            signal-b (v2/signal :b1)
            exec-count (atom 0)
            spin-result (hot-spin
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

        (is (= [:a1 :b2] @spin-result))
        (is (= 2 @exec-count) "Spin should re-execute once for signal-b change")

           ;; CRITICAL TEST: Change signal A after resuming from B
           ;; Before the fix, this would NOT trigger re-execution because
           ;; signal-a was removed from observers in record-deps!
        (reset! signal-a :a2)

        (is (= [:a2 :b2] @spin-result) "Spin should react to signal-a changes")
        (is (= 3 @exec-count) "Spin should re-execute for signal-a change")))))

(deftest test-multi-signal-later-then-earlier-sequence
  (testing "Changing signals in reverse order (later then earlier) maintains reactivity"
    (let [rt v2/*world*]
      (let [signal-a (v2/signal 0)
            signal-b (v2/signal 0)
            signal-c (v2/signal 0)
            exec-count (atom 0)
            spin-result (hot-spin
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

        (is (= 100 @spin-result))
        (is (= 2 @exec-count))

           ;; Now change B - should still work
        (reset! signal-b 10)

        (is (= 110 @spin-result))
        (is (= 3 @exec-count))

           ;; Now change A - should still work
        (reset! signal-a 1)

        (is (= 111 @spin-result))
        (is (= 4 @exec-count))

           ;; Change C again to verify all dependencies still active
        (reset! signal-c 200)

        (is (= 211 @spin-result))
        (is (= 5 @exec-count))))))

(deftest test-conditional-signal-tracking
  ;; v2 (T11): a change re-enters the computation at the earliest changed
  ;; track site, so the prefix before that site (the exec-count swap) is not
  ;; repeated by a branch change; only a change of `condition`, the first
  ;; site, re-runs it. The old engine re-ran the whole body each time.
  (testing "Conditional branches only track signals in taken branch"
    (let [rt v2/*world*]
      (let [condition (v2/signal true)
            signal-true-branch (v2/signal :true-val)
            signal-false-branch (v2/signal :false-val)
            exec-count (atom 0)
            spin-result (hot-spin
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

        (is (= [:true-branch :true-val-2] @spin-result))
        (is (= 1 @exec-count) "re-entry at the branch site skips the prefix")

           ;; Change signal in false branch - should NOT trigger (not tracked)
        (reset! signal-false-branch :false-val-2)

        (is (= [:true-branch :true-val-2] @spin-result))
        (is (= 1 @exec-count) "Should NOT re-execute for untracked signal")

           ;; Switch condition to false branch
        (reset! condition false)

        (is (= [:false-branch :false-val-2] @spin-result))
        (is (= 2 @exec-count) "a change at the first site re-runs the prefix")

           ;; Now true branch signal should not trigger, false branch should
        (reset! signal-true-branch :true-val-3)

        (is (= [:false-branch :false-val-2] @spin-result))
        (is (= 2 @exec-count) "Should NOT re-execute for untracked true branch signal")

        (reset! signal-false-branch :false-val-3)

        (is (= [:false-branch :false-val-3] @spin-result))
        (is (= 2 @exec-count) "the false branch site re-enters past the prefix")))))

(deftest test-signal-creation
  (let [s (v2/signal 0)] (is (some? s)) (is (= 0 @s))))

(deftest test-signal-swap
  (let [s (v2/signal 0)] (swap! s inc) (is (= 1 @s)) (swap! s + 5) (is (= 6 @s))))

(deftest test-signal-reset
  (let [s (v2/signal 0)] (reset! s 42) (is (= 42 @s))))

(deftest test-signal-types
  (doseq [v [42 [1 2 3] {:a 1 :b 2} nil]] (is (= v @(v2/signal v)))))

(deftest test-signal-spin-tracking
  (let [s (v2/signal 42)] (is (= 84 (v2/value (spin (* 2 (iv/get-new (track s)))))))))

(deftest test-signal-interval-destructuring
  (let [s (v2/signal 10) c (spin (let [{:keys [new old deltas]} (track s)]
                                   {:new new :old old :deltas deltas}))]
    (is (= 10 (:new (v2/value c))))))

(deftest test-signal-get-detailed
  (let [s (v2/signal 10) c (hot-spin (track s))]
    (let [view (v2/value c)]
      (is (some? view)) (is (= 10 (:new view))) (is (nil? (:old view))))
    (swap! s inc)
    (let [view (v2/value c)] (is (= 11 (:new view))) (is (= 10 (:old view))))))

(deftest test-signal-swap-changed
  (when-let [swap-changed? (api 'swap-changed?)]
    (let [s (v2/signal 0)]
      (is (true? (swap-changed? s inc))) (is (= 1 @s))
      (is (false? (swap-changed? s identity))) (is (= 1 @s)))))

(deftest test-swap-await-async-f
  (when-let [swap-await! (api 'swap-await!)]
    (let [s (v2/signal 10)
          async-x2 (fn [c] (spin (v2/sleep 1) (* c 2)))]
      (is (= 20 (v2/value (task (await (swap-await! s async-x2))))))
      (is (= 20 @s)))))
