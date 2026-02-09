(ns org.replikativ.spindel.incremental.combinator-test
  "Tests for interval-based incremental combinators with address-based caching.

   These tests verify the interval abstraction where:
   - Each combinator call gets a unique address
   - Previous results stored at [:incremental address]
   - prev.new becomes our.old for incremental computation
   - Results returned as intervals for downstream combinators

   CLJ-only: requires Thread/sleep and signal macro."
  #?(:clj
     (:refer-clojure :exclude [filter map reduce])
     :cljs
     (:refer-clojure :exclude [filter map reduce]))
  #?(:clj
     (:require [clojure.test :refer [deftest is testing]]
               [org.replikativ.spindel.engine.context :as ctx]
               [org.replikativ.spindel.engine.core :as ec]
               [org.replikativ.spindel.engine.scheduler :as sched]
               [org.replikativ.spindel.signal :as sig]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.effects.track :refer [track]]
               [org.replikativ.spindel.incremental.interval :as iv]
               [org.replikativ.spindel.incremental.combinators :as ic]
               [org.replikativ.spindel.incremental.deltaable :as d]
               [org.replikativ.spindel.test-async :refer [await-drain]])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]])))

;; =============================================================================
;; Basic Interval Protocol Tests
;; =============================================================================

#?(:clj
   (deftest test-interval-creation
     (testing "Create interval with old, new, deltas"
       (let [iv (iv/interval [1 2] [1 2 3] [{:delta :add :value 3}])]
         (is (= [1 2] (iv/get-old iv)))
         (is (= [1 2 3] (iv/get-new iv)))
         (is (= [{:delta :add :value 3}] (iv/get-deltas iv)))
         (is (iv/has-deltas? iv))))

     (testing "Create interval with just new value"
       (let [iv (iv/interval [1 2 3])]
         (is (nil? (iv/get-old iv)))
         (is (= [1 2 3] (iv/get-new iv)))
         (is (nil? (iv/get-deltas iv)))
         (is (not (iv/has-deltas? iv)))))

     (testing "Interval supports deref for convenience"
       (let [iv (iv/interval nil 42 nil)]
         (is (= 42 @iv))))

     (testing "Interval supports map destructuring"
       (let [iv (iv/interval [1] [1 2] [{:delta :add :value 2}])
             {:keys [old new deltas]} iv]
         (is (= [1] old))
         (is (= [1 2] new))
         (is (= [{:delta :add :value 2}] deltas))))))

#?(:clj
   (deftest test-interval-coercion
     (testing "Plain values coerce to static intervals"
       (let [iv (iv/as-interval [1 2 3])]
         (is (nil? (iv/get-old iv)))
         (is (= [1 2 3] (iv/get-new iv)))
         (is (nil? (iv/get-deltas iv)))
         (is (iv/static? iv))))

     (testing "Deltaable collections coerce preserving deltas"
       (let [dv (-> (d/deltaable-vector [1 2])
                    (conj 3))
             iv (iv/as-interval dv)]
         (is (nil? (iv/get-old iv)))  ; No old without previous result
         (is (= [1 2 3] (iv/get-new iv)))
         (is (seq (iv/get-deltas iv)))))

     (testing "Intervals pass through as-is"
       (let [iv1 (iv/interval [1] [1 2] [{:delta :add :value 2}])
             iv2 (iv/as-interval iv1)]
         (is (identical? iv1 iv2))))

     (testing "Protocol extended to plain objects"
       (let [v [1 2 3]]
         (is (= v (iv/get-new v)))
         (is (nil? (iv/get-old v)))
         (is (nil? (iv/get-deltas v)))))))

#?(:clj
   (deftest test-interval-commit
     (testing "Commit moves new to old, clears deltas"
       (let [iv1 (iv/interval [1] [1 2] [{:delta :add :value 2}])
             iv2 (iv/commit iv1)]
         (is (= [1 2] (iv/get-old iv2)))
         (is (= [1 2] (iv/get-new iv2)))
         (is (nil? (iv/get-deltas iv2)))))))

;; =============================================================================
;; Filter Combinator Tests
;; =============================================================================

#?(:clj
   (deftest test-filter-initial-execution
     (testing "Filter computes full result on first execution"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           (let [source (iv/interval nil [1 2 3 4 5] nil)
                 result (ic/filter even? source)]
             (is (= [2 4] (iv/get-new result)))
             (is (nil? (iv/get-old result)))))))))

#?(:clj
   (deftest test-filter-incremental-add
     (testing "Filter processes :add delta incrementally"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           ;; First execution - establishes cache
           (let [source1 (iv/interval nil [1 2 3 4] nil)
                 result1 (ic/filter* {:file "test" :line 1 :column 0} even? source1)]
             (is (= [2 4] (iv/get-new result1)))

             ;; Second execution with :add delta - should be incremental
             (let [source2 (iv/interval [1 2 3 4]
                                        [1 2 3 4 6]
                                        [{:delta :add :value 6}])
                   result2 (ic/filter* {:file "test" :line 1 :column 0} even? source2)]
               ;; Old should be previous new
               (is (= [2 4] (iv/get-old result2)))
               ;; New should include the added even number
               (is (= [2 4 6] (iv/get-new result2)))
               ;; Should have delta for the add
               (is (= 1 (count (iv/get-deltas result2)))))))))))

#?(:clj
   (deftest test-filter-enter-exit
     (testing "Filter handles enter/exit on :update delta"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           ;; Initial: [1 2 3] filtered for even gives [2]
           (let [source1 (iv/interval nil [1 2 3] nil)
                 result1 (ic/filter* {:file "test" :line 10 :column 0} even? source1)]
             (is (= [2] (iv/get-new result1)))

             ;; Update 1 -> 4 (odd -> even = ENTER)
             (let [source2 (iv/interval [1 2 3]
                                        [4 2 3]
                                        [{:delta :update :value 4 :old-value 1}])
                   result2 (ic/filter* {:file "test" :line 10 :column 0} even? source2)]
               (is (= [2] (iv/get-old result2)))
               ;; 4 should now be in the result
               (is (some #{4} (iv/get-new result2)))
               (is (some #{2} (iv/get-new result2))))))))))

;; =============================================================================
;; Map Combinator Tests
;; =============================================================================

#?(:clj
   (deftest test-map-initial-execution
     (testing "Map transforms all values on first execution"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           (let [source (iv/interval nil [1 2 3] nil)
                 result (ic/map #(* 2 %) source)]
             (is (= [2 4 6] (iv/get-new result)))
             (is (nil? (iv/get-old result)))))))))

#?(:clj
   (deftest test-map-incremental-add
     (testing "Map transforms only :add delta"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           ;; First execution
           (let [source1 (iv/interval nil [1 2 3] nil)
                 result1 (ic/map* {:file "test" :line 20 :column 0} #(* 2 %) source1)]
             (is (= [2 4 6] (iv/get-new result1)))

             ;; Add value 4
             (let [source2 (iv/interval [1 2 3]
                                        [1 2 3 4]
                                        [{:delta :add :value 4}])
                   result2 (ic/map* {:file "test" :line 20 :column 0} #(* 2 %) source2)]
               (is (= [2 4 6] (iv/get-old result2)))
               (is (= [2 4 6 8] (iv/get-new result2)))
               (is (= [{:delta :add :value 8}] (iv/get-deltas result2))))))))))

;; =============================================================================
;; Reduce Combinator Tests
;; =============================================================================

#?(:clj
   (deftest test-reduce-initial-execution
     (testing "Reduce computes full result on first execution"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           (let [source (iv/interval nil [1 2 3 4] nil)
                 result (ic/reduce + 0 source)]
             ;; Returns interval wrapping scalar
             (is (= 10 (iv/get-new result)))
             (is (nil? (iv/get-old result)))))))))

#?(:clj
   (deftest test-reduce-incremental-add
     (testing "Reduce applies enter-fn for :add delta"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           ;; First execution: sum = 6
           (let [source1 (iv/interval nil [1 2 3] nil)
                 result1 (ic/reduce* {:file "test" :line 30 :column 0} + 0 + - source1)]
             (is (= 6 (iv/get-new result1)))

             ;; Add 4: sum should be 10
             (let [source2 (iv/interval [1 2 3]
                                        [1 2 3 4]
                                        [{:delta :add :value 4}])
                   result2 (ic/reduce* {:file "test" :line 30 :column 0} + 0 + - source2)]
               (is (= 6 (iv/get-old result2)))
               (is (= 10 (iv/get-new result2))))))))))

#?(:clj
   (deftest test-reduce-incremental-remove
     (testing "Reduce applies exit-fn for :remove delta"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           ;; First execution: sum = 10
           (let [source1 (iv/interval nil [1 2 3 4] nil)
                 result1 (ic/reduce* {:file "test" :line 40 :column 0} + 0 + - source1)]
             (is (= 10 (iv/get-new result1)))

             ;; Remove 3: sum should be 7
             (let [source2 (iv/interval [1 2 3 4]
                                        [1 2 4]
                                        [{:delta :remove :value 3}])
                   result2 (ic/reduce* {:file "test" :line 40 :column 0} + 0 + - source2)]
               (is (= 10 (iv/get-old result2)))
               (is (= 7 (iv/get-new result2))))))))))

;; =============================================================================
;; Pipeline Tests - Chained Combinators
;; =============================================================================

#?(:clj
   (deftest test-pipeline-filter-map-reduce
     (testing "Chained combinators pass intervals correctly"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           ;; Pipeline: filter even -> double -> sum
           ;; [1 2 3 4] -> [2 4] -> [4 8] -> 12
           (let [source (iv/interval nil [1 2 3 4] nil)
                 step1 (ic/filter* {:file "test" :line 50 :column 0} even? source)
                 step2 (ic/map* {:file "test" :line 51 :column 0} #(* 2 %) step1)
                 result (ic/reduce* {:file "test" :line 52 :column 0} + 0 + - step2)]
             (is (= [2 4] (iv/get-new step1)))
             (is (= [4 8] (iv/get-new step2)))
             (is (= 12 (iv/get-new result)))))))))

#?(:clj
   (deftest test-pipeline-incremental
     (testing "Pipeline processes incremental updates correctly"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           ;; Initial: [1 2 3 4] -> filter even [2 4] -> double [4 8] -> sum 12
           (let [source1 (iv/interval nil [1 2 3 4] nil)
                 step1-r1 (ic/filter* {:file "test" :line 60 :column 0} even? source1)
                 step2-r1 (ic/map* {:file "test" :line 61 :column 0} #(* 2 %) step1-r1)
                 result1 (ic/reduce* {:file "test" :line 62 :column 0} + 0 + - step2-r1)]
             (is (= 12 (iv/get-new result1)))

             ;; Add 6: [1 2 3 4 6] -> [2 4 6] -> [4 8 12] -> 24
             (let [source2 (iv/interval [1 2 3 4]
                                        [1 2 3 4 6]
                                        [{:delta :add :value 6}])
                   step1-r2 (ic/filter* {:file "test" :line 60 :column 0} even? source2)
                   step2-r2 (ic/map* {:file "test" :line 61 :column 0} #(* 2 %) step1-r2)
                   result2 (ic/reduce* {:file "test" :line 62 :column 0} + 0 + - step2-r2)]
               ;; Filter should pass through 6 (even)
               (is (some #{6} (iv/get-new step1-r2)))
               ;; Map should transform to 12
               (is (some #{12} (iv/get-new step2-r2)))
               ;; Sum should be 24
               (is (= 24 (iv/get-new result2))))))))))

;; =============================================================================
;; For-Each Combinator Tests
;; =============================================================================

#?(:clj
   (deftest test-for-each-initial
     (testing "For-each transforms all items on first execution"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           (let [todos [{:id 1 :text "A"} {:id 2 :text "B"}]
                 source (iv/interval nil todos nil)
                 result (ic/for-each :id #(assoc % :rendered true) source)]
             (is (= 2 (count (iv/get-new result))))
             (is (every? :rendered (iv/get-new result)))))))))

#?(:clj
   (deftest test-for-each-incremental-add
     (testing "For-each only transforms new items on :add"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))
             transform-count (atom 0)
             transform-fn (fn [item]
                           (swap! transform-count inc)
                           (assoc item :rendered true))]
         (binding [ec/*execution-context* exec-ctx]
           ;; Initial: 2 items
           (let [source1 (iv/interval nil [{:id 1 :text "A"} {:id 2 :text "B"}] nil)
                 result1 (ic/for-each* {:file "test" :line 70 :column 0} :id transform-fn source1)]
             (is (= 2 @transform-count))

             ;; Add third item
             (reset! transform-count 0)
             (let [source2 (iv/interval [{:id 1 :text "A"} {:id 2 :text "B"}]
                                        [{:id 1 :text "A"} {:id 2 :text "B"} {:id 3 :text "C"}]
                                        [{:delta :add :value {:id 3 :text "C"}}])
                   result2 (ic/for-each* {:file "test" :line 70 :column 0} :id transform-fn source2)]
               ;; Should only transform the new item
               (is (= 1 @transform-count))
               (is (= 3 (count (iv/get-new result2)))))))))))

;; =============================================================================
;; Address-Based Caching Tests
;; =============================================================================

#?(:clj
   (deftest test-address-caching
     (testing "Same source-loc uses same cache"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           ;; Two calls with same source-loc should share cache
           (let [source-loc {:file "cache-test" :line 100 :column 0}
                 source1 (iv/interval nil [1 2 3] nil)
                 result1 (ic/filter* source-loc even? source1)]
             (is (= [2] (iv/get-new result1)))

             ;; Second call with delta - should use cached old
             (let [source2 (iv/interval [1 2 3]
                                        [1 2 3 4]
                                        [{:delta :add :value 4}])
                   result2 (ic/filter* source-loc even? source2)]
               (is (= [2] (iv/get-old result2)))
               (is (= [2 4] (iv/get-new result2))))))))))

#?(:clj
   (deftest test-different-addresses
     (testing "Different source-locs use different caches"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           ;; First filter at line 200
           (let [source (iv/interval nil [1 2 3 4] nil)
                 result1 (ic/filter* {:file "test" :line 200 :column 0} even? source)
                 result2 (ic/filter* {:file "test" :line 201 :column 0} odd? source)]
             ;; Both should work independently
             (is (= [2 4] (iv/get-new result1)))
             (is (= [1 3] (iv/get-new result2)))))))))

;; =============================================================================
;; Integration with Signals
;; =============================================================================

#?(:clj
   (deftest test-integration-with-signals
     (testing "Combinators work with signal tracking in spin"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           (let [results (atom [])
                 data-signal (sig/signal (d/deltaable-vector [1 2 3 4]))

                 ;; Spin that uses combinators on tracked signal
                 result-spin
                 (spin
                   (let [view (track data-signal)
                         ;; Get the new value and wrap as interval
                         source-iv (iv/as-interval (:new view))
                         ;; Filter and sum
                         filtered (ic/filter even? source-iv)
                         summed (ic/reduce + 0 filtered)]
                     (swap! results conj (iv/get-new summed))
                     (iv/get-new summed)))]

             ;; Trigger initial execution
             @result-spin
             (is (= [6] @results) "Initial sum of evens: 2 + 4 = 6")

             ;; Add even number
             (swap! data-signal conj 6)
             (await-drain exec-ctx)
             @result-spin
             (is (= [6 12] @results) "After adding 6: 2 + 4 + 6 = 12")))))))

;; =============================================================================
;; Cascading Signal Changes Tests
;; =============================================================================

#?(:clj
   (deftest test-cascading-multiple-updates
     (testing "Multiple rapid signal updates processed correctly"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           (let [results (atom [])
                 todos-signal (sig/signal (d/deltaable-vector []))

                 pipeline-spin
                 (spin
                   (let [view (track todos-signal)
                         source-iv (iv/as-interval (:new view))
                         ;; Filter active, extract hours, sum
                         active (ic/filter* {:file "cascade" :line 1 :column 0}
                                            #(= :active (:status %)) source-iv)
                         hours (ic/map* {:file "cascade" :line 2 :column 0}
                                        :hours active)
                         total (ic/reduce* {:file "cascade" :line 3 :column 0}
                                           + 0 + - hours)]
                     (swap! results conj (iv/get-new total))
                     (iv/get-new total)))]

             ;; Trigger initial execution
             @pipeline-spin
             (is (= [0] @results) "Initial: empty list = 0 hours")

             ;; Add active todo
             (swap! todos-signal conj {:id 1 :status :active :hours 5})
             (await-drain exec-ctx)
             @pipeline-spin
             (is (= [0 5] @results) "After adding active todo: 5 hours")

             ;; Add done todo (should not affect sum)
             (swap! todos-signal conj {:id 2 :status :done :hours 3})
             (await-drain exec-ctx)
             @pipeline-spin
             (is (= [0 5 5] @results) "After adding done todo: still 5 hours")

             ;; Add another active todo
             (swap! todos-signal conj {:id 3 :status :active :hours 8})
             (await-drain exec-ctx)
             @pipeline-spin
             (is (= [0 5 5 13] @results) "After adding active todo: 5 + 8 = 13")))))))

#?(:clj
   (deftest test-signal-update-triggers-incremental
     (testing "Signal update delta propagates through pipeline"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           (let [filter-calls (atom 0)
                 map-calls (atom 0)
                 data-signal (sig/signal (d/deltaable-vector [1 2 3 4 5]))

                 ;; Spin that counts combinator invocations
                 pipeline-spin
                 (spin
                   (let [view (track data-signal)
                         source-iv (iv/as-interval (:new view))

                         ;; Wrap filter to count calls
                         filtered (do (swap! filter-calls inc)
                                     (ic/filter* {:file "count" :line 1 :column 0}
                                                 even? source-iv))

                         ;; Wrap map to count calls
                         doubled (do (swap! map-calls inc)
                                    (ic/map* {:file "count" :line 2 :column 0}
                                             #(* 2 %) filtered))]
                     (iv/get-new doubled)))]

             ;; Initial execution
             @pipeline-spin
             (is (= 1 @filter-calls) "Filter called once on initial")
             (is (= 1 @map-calls) "Map called once on initial")

             ;; Add value - should trigger re-execution
             (swap! data-signal conj 6)
             (await-drain exec-ctx)
             @pipeline-spin
             (is (= 2 @filter-calls) "Filter called on update")
             (is (= 2 @map-calls) "Map called on update")))))))

#?(:clj
   (deftest test-todo-list-realistic-scenario
     (testing "Realistic todo list with multiple operations"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           (let [results (atom [])
                 todos (sig/signal (d/deltaable-vector
                                    [{:id 1 :text "Task 1" :done false :hours 2}
                                     {:id 2 :text "Task 2" :done true :hours 1}
                                     {:id 3 :text "Task 3" :done false :hours 3}]))

                 ;; Calculate remaining hours (undone tasks only)
                 remaining-hours-spin
                 (spin
                   (let [view (track todos)
                         source-iv (iv/as-interval (:new view))
                         ;; Filter undone, extract hours, sum
                         undone (ic/filter* {:file "todo" :line 1 :column 0}
                                            #(not (:done %)) source-iv)
                         hours (ic/map* {:file "todo" :line 2 :column 0}
                                        :hours undone)
                         total (ic/reduce* {:file "todo" :line 3 :column 0}
                                           + 0 + - hours)]
                     (swap! results conj (iv/get-new total))
                     (iv/get-new total)))]

             ;; Initial: 2 + 3 = 5 hours remaining
             @remaining-hours-spin
             (is (= [5] @results) "Initial: 2 + 3 = 5 remaining hours")

             ;; Complete task 1 (2 hours done)
             (swap! todos (fn [v] (assoc v 0 {:id 1 :text "Task 1" :done true :hours 2})))
             (await-drain exec-ctx)
             @remaining-hours-spin
             (is (= [5 3] @results) "After completing Task 1: 3 remaining hours")

             ;; Add new task
             (swap! todos conj {:id 4 :text "Task 4" :done false :hours 4})
             (await-drain exec-ctx)
             @remaining-hours-spin
             (is (= [5 3 7] @results) "After adding Task 4: 3 + 4 = 7 remaining hours")))))))

;; =============================================================================
;; Macro Tests - Auto Source Location Capture
;; =============================================================================

#?(:clj
   (deftest test-ifilter-macro
     (testing "ifilter macro captures source location"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           ;; First call
           (let [source1 (iv/interval nil [1 2 3 4 5] nil)
                 result1 (ic/ifilter even? source1)]
             (is (= [2 4] (iv/get-new result1)))

             ;; Second call at same location - should use cached old
             (let [source2 (iv/interval [1 2 3 4 5]
                                        [1 2 3 4 5 6]
                                        [{:delta :add :value 6}])
                   result2 (ic/ifilter even? source2)]
               ;; Note: This is a different source location than result1 due to being
               ;; in a different let binding, so it gets its own cache
               (is (= [2 4 6] (iv/get-new result2))))))))))

#?(:clj
   (deftest test-pipeline-with-macros
     (testing "Pipeline using macros works correctly"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [ec/*execution-context* exec-ctx]
           ;; Pipeline: filter even -> double -> sum
           (let [source (iv/interval nil [1 2 3 4] nil)
                 filtered (ic/ifilter even? source)
                 doubled (ic/imap #(* 2 %) filtered)
                 summed (ic/ireduce + 0 doubled)]
             (is (= [2 4] (iv/get-new filtered)))
             (is (= [4 8] (iv/get-new doubled)))
             (is (= 12 (iv/get-new summed)))))))))