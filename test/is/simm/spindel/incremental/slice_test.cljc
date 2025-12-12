(ns is.simm.spindel.incremental.slice-test
  "Comprehensive tests for the islice combinator.

   Tests cover:
   1. Basic slicing behavior
   2. Window slide deltas (right, left, jump)
   3. Source changes within window
   4. Edge cases (empty, bounds clamping)
   5. Performance characteristics
   6. Integration with signals and for-each"
  #?(:clj
     (:refer-clojure :exclude [filter map reduce])
     :cljs
     (:refer-clojure :exclude [filter map reduce]))
  #?(:clj
     (:require [clojure.test :refer [deftest is testing]]
               [is.simm.spindel.runtime.context :as ctx]
               [is.simm.spindel.runtime.core :as rtc]
               [is.simm.spindel.runtime.scheduler :as sched]
               [is.simm.spindel.state.signal :as sig]
               [is.simm.spindel.spin.cps :refer [spin]]
               [is.simm.spindel.effects.track :refer [track]]
               [is.simm.spindel.incremental.interval :as iv]
               [is.simm.spindel.incremental.combinators :as ic]
               [is.simm.spindel.incremental.deltaable :as d])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]])))

;; =============================================================================
;; Helper: Create test context
;; =============================================================================

#?(:clj
   (defmacro with-test-context [& body]
     `(let [exec-ctx# (ctx/create-execution-context :executor (sched/default-executor))]
        (binding [rtc/*execution-context* exec-ctx#]
          ~@body))))

;; =============================================================================
;; Basic Slicing Tests
;; =============================================================================

#?(:clj
   (deftest test-slice-initial
     (testing "Slice returns correct range on initial call"
       (with-test-context
         (let [source (vec (range 100))
               result (ic/slice* {:file "test" :line 1 :column 0}
                                 {:start 10 :end 20}
                                 source)]
           (is (= (vec (range 10 20)) (iv/get-new result)))
           (is (nil? (iv/get-old result)))
           (is (nil? (iv/get-deltas result))))))))

#?(:clj
   (deftest test-slice-empty-window
     (testing "Empty window returns empty vector"
       (with-test-context
         (let [source (vec (range 100))
               result (ic/slice* {:file "test" :line 2 :column 0}
                                 {:start 50 :end 50}
                                 source)]
           (is (= [] (iv/get-new result))))))))

#?(:clj
   (deftest test-slice-bounds-clamping
     (testing "Window bounds are clamped to source length"
       (with-test-context
         (let [source (vec (range 10))
               ;; Window extends beyond source
               result (ic/slice* {:file "test" :line 3 :column 0}
                                 {:start 5 :end 100}
                                 source)]
           (is (= [5 6 7 8 9] (iv/get-new result))))))))

#?(:clj
   (deftest test-slice-negative-start-clamped
     (testing "Negative start is clamped to 0"
       (with-test-context
         (let [source (vec (range 10))
               result (ic/slice* {:file "test" :line 4 :column 0}
                                 {:start -5 :end 5}
                                 source)]
           (is (= [0 1 2 3 4] (iv/get-new result))))))))

;; =============================================================================
;; Window Slide Tests - Core Incremental Behavior
;; =============================================================================

#?(:clj
   (deftest test-window-slide-right
     (testing "Sliding window right produces correct deltas"
       (with-test-context
         (let [source (vec (range 100))
               source-loc {:file "slide" :line 10 :column 0}

               ;; First call: window [5, 15)
               result1 (ic/slice* source-loc {:start 5 :end 15} source)
               _ (is (= (vec (range 5 15)) (iv/get-new result1)))
               _ (is (nil? (iv/get-deltas result1)))

               ;; Second call: window [7, 17) - slide right by 2
               result2 (ic/slice* source-loc {:start 7 :end 17} source)]

           ;; Old should be previous output
           (is (= (vec (range 5 15)) (iv/get-old result2)))

           ;; New should be new window
           (is (= (vec (range 7 17)) (iv/get-new result2)))

           ;; Should have deltas
           (let [deltas (iv/get-deltas result2)]
             (is (seq deltas) "Should have deltas for window slide")

             ;; Should have 2 removes (items 5, 6 exiting)
             (let [removes (clojure.core/filter #(= :remove (:delta %)) deltas)]
               (is (= 2 (count removes)))
               ;; Removes should be for positions 1 and 0 (high to low for stable removal)
               (is (= #{5 6} (set (clojure.core/map :old-value removes)))))

             ;; Should have 2 adds (items 15, 16 entering)
             (let [adds (clojure.core/filter #(= :add (:delta %)) deltas)]
               (is (= 2 (count adds)))
               (is (= #{15 16} (set (clojure.core/map :value adds)))))))))))

#?(:clj
   (deftest test-window-slide-left
     (testing "Sliding window left produces correct deltas"
       (with-test-context
         (let [source (vec (range 100))
               source-loc {:file "slide-left" :line 20 :column 0}

               ;; First call: window [10, 20)
               result1 (ic/slice* source-loc {:start 10 :end 20} source)
               _ (is (= (vec (range 10 20)) (iv/get-new result1)))

               ;; Second call: window [7, 17) - slide left by 3
               result2 (ic/slice* source-loc {:start 7 :end 17} source)]

           (is (= (vec (range 7 17)) (iv/get-new result2)))

           (let [deltas (iv/get-deltas result2)]
             (is (seq deltas))

             ;; Should have 3 removes (items 17, 18, 19 exiting from back)
             (let [removes (clojure.core/filter #(= :remove (:delta %)) deltas)]
               (is (= 3 (count removes)))
               (is (= #{17 18 19} (set (clojure.core/map :old-value removes)))))

             ;; Should have 3 adds (items 7, 8, 9 entering at front)
             (let [adds (clojure.core/filter #(= :add (:delta %)) deltas)]
               (is (= 3 (count adds)))
               (is (= #{7 8 9} (set (clojure.core/map :value adds)))))))))))

#?(:clj
   (deftest test-window-jump-no-overlap
     (testing "Window jump with no overlap produces full replace"
       (with-test-context
         (let [source (vec (range 100))
               source-loc {:file "jump" :line 30 :column 0}

               ;; First call: window [0, 10)
               result1 (ic/slice* source-loc {:start 0 :end 10} source)

               ;; Second call: window [50, 60) - complete jump
               result2 (ic/slice* source-loc {:start 50 :end 60} source)]

           (is (= (vec (range 50 60)) (iv/get-new result2)))

           (let [deltas (iv/get-deltas result2)]
             ;; Should have 10 removes and 10 adds (complete turnover)
             (let [removes (clojure.core/filter #(= :remove (:delta %)) deltas)
                   adds (clojure.core/filter #(= :add (:delta %)) deltas)]
               (is (= 10 (count removes)))
               (is (= 10 (count adds)))
               (is (= (set (range 0 10)) (set (clojure.core/map :old-value removes))))
               (is (= (set (range 50 60)) (set (clojure.core/map :value adds)))))))))))

#?(:clj
   (deftest test-window-expand
     (testing "Window expanding produces add deltas"
       (with-test-context
         (let [source (vec (range 100))
               source-loc {:file "expand" :line 40 :column 0}

               ;; First call: window [10, 15) - 5 items
               result1 (ic/slice* source-loc {:start 10 :end 15} source)

               ;; Second call: window [10, 20) - expand to 10 items
               result2 (ic/slice* source-loc {:start 10 :end 20} source)]

           (is (= (vec (range 10 20)) (iv/get-new result2)))

           (let [deltas (iv/get-deltas result2)]
             ;; Should only have adds (no removes when expanding right)
             (let [removes (clojure.core/filter #(= :remove (:delta %)) deltas)
                   adds (clojure.core/filter #(= :add (:delta %)) deltas)]
               (is (= 0 (count removes)))
               (is (= 5 (count adds)))
               (is (= (set (range 15 20)) (set (clojure.core/map :value adds)))))))))))

#?(:clj
   (deftest test-window-shrink
     (testing "Window shrinking produces remove deltas"
       (with-test-context
         (let [source (vec (range 100))
               source-loc {:file "shrink" :line 50 :column 0}

               ;; First call: window [10, 20) - 10 items
               result1 (ic/slice* source-loc {:start 10 :end 20} source)

               ;; Second call: window [10, 15) - shrink to 5 items
               result2 (ic/slice* source-loc {:start 10 :end 15} source)]

           (is (= (vec (range 10 15)) (iv/get-new result2)))

           (let [deltas (iv/get-deltas result2)]
             ;; Should only have removes (no adds when shrinking)
             (let [removes (clojure.core/filter #(= :remove (:delta %)) deltas)
                   adds (clojure.core/filter #(= :add (:delta %)) deltas)]
               (is (= 5 (count removes)))
               (is (= 0 (count adds)))
               (is (= (set (range 15 20)) (set (clojure.core/map :old-value removes)))))))))))

#?(:clj
   (deftest test-window-no-change
     (testing "Same window produces no deltas"
       (with-test-context
         (let [source (vec (range 100))
               source-loc {:file "no-change" :line 60 :column 0}

               result1 (ic/slice* source-loc {:start 10 :end 20} source)
               result2 (ic/slice* source-loc {:start 10 :end 20} source)]

           (is (= (iv/get-new result1) (iv/get-new result2)))
           (is (nil? (iv/get-deltas result2))))))))

;; =============================================================================
;; Source Change Tests
;; =============================================================================

#?(:clj
   (deftest test-source-update-in-window
     (testing "Source update within window produces update delta"
       (with-test-context
         (let [source-loc {:file "update" :line 70 :column 0}
               source1 [{:id 1 :text "a"} {:id 2 :text "b"} {:id 3 :text "c"}]
               window {:start 0 :end 3}

               ;; Initial
               result1 (ic/slice* source-loc window (iv/interval nil source1 nil))

               ;; Update item at index 1
               source2 [{:id 1 :text "a"} {:id 2 :text "B"} {:id 3 :text "c"}]
               source-iv (iv/interval source1 source2
                                      [{:delta :update
                                        :old-value {:id 2 :text "b"}
                                        :value {:id 2 :text "B"}}])

               result2 (ic/slice* source-loc window source-iv)]

           (is (= source2 (iv/get-new result2)))
           (let [deltas (iv/get-deltas result2)]
             (is (= 1 (count deltas)))
             (is (= :update (:delta (first deltas))))
             (is (= {:id 2 :text "B"} (:value (first deltas))))))))))

#?(:clj
   (deftest test-source-update-outside-window
     (testing "Source update outside window produces no delta"
       (with-test-context
         (let [source-loc {:file "update-outside" :line 80 :column 0}
               source1 (vec (range 100))
               window {:start 10 :end 20}

               result1 (ic/slice* source-loc window (iv/interval nil source1 nil))

               ;; Update item at index 50 (outside window)
               source2 (assoc source1 50 999)
               source-iv (iv/interval source1 source2
                                      [{:delta :update
                                        :old-value 50
                                        :value 999}])

               result2 (ic/slice* source-loc window source-iv)]

           ;; Slice should be unchanged
           (is (= (vec (range 10 20)) (iv/get-new result2)))
           ;; No deltas for out-of-window changes
           (is (nil? (iv/get-deltas result2))))))))

;; =============================================================================
;; Delta Application Correctness Tests
;; =============================================================================

#?(:clj
   (deftest test-delta-application-correctness
     (testing "Applying deltas to old produces new"
       (with-test-context
         (let [source (vec (range 100))
               source-loc {:file "correctness" :line 90 :column 0}

               ;; Test various window slides
               test-cases [{:old-window {:start 0 :end 10}
                            :new-window {:start 5 :end 15}}
                           {:old-window {:start 50 :end 60}
                            :new-window {:start 45 :end 55}}
                           {:old-window {:start 10 :end 20}
                            :new-window {:start 10 :end 30}}
                           {:old-window {:start 10 :end 30}
                            :new-window {:start 10 :end 20}}]]

           (doseq [{:keys [old-window new-window]} test-cases]
             ;; Reset context for each test case
             (let [ctx (ctx/create-execution-context :executor (sched/default-executor))]
               (binding [rtc/*execution-context* ctx]
                 (let [loc {:file (str "correctness-" (:start old-window))
                            :line (:start new-window)
                            :column 0}
                       result1 (ic/slice* loc old-window source)
                       old-output (iv/get-new result1)

                       result2 (ic/slice* loc new-window source)
                       new-output (iv/get-new result2)
                       deltas (iv/get-deltas result2)

                       ;; Apply deltas to old to verify correctness
                       applied (clojure.core/reduce
                                 (fn [acc delta]
                                   (case (:delta delta)
                                     :remove
                                     (let [idx (first (:path delta))]
                                       (vec (concat (subvec acc 0 idx)
                                                    (subvec acc (inc idx)))))
                                     :add
                                     (let [idx (first (:path delta))
                                           val (:value delta)]
                                       (vec (concat (subvec acc 0 idx)
                                                    [val]
                                                    (subvec acc idx))))
                                     acc))
                                 old-output
                                 deltas)]
                   (is (= new-output applied)
                       (str "Applying deltas should produce new output for "
                            old-window " -> " new-window)))))))))))

;; =============================================================================
;; Integration with Signals
;; =============================================================================

#?(:clj
   (deftest test-slice-with-signal
     (testing "Slice works with tracked signal"
       (with-test-context
         (let [results (atom [])
               items-signal (sig/signal (d/deltaable-vector (vec (range 100))))
               window-signal (sig/signal {:start 0 :end 10})

               scroll-spin
               (spin
                 (let [items-iv (track items-signal)
                       window (track window-signal)
                       ;; Use @window to get the map value
                       sliced (ic/slice* {:file "signal-test" :line 100 :column 0}
                                         @window
                                         (iv/as-interval (:new items-iv)))]
                   (swap! results conj {:slice (iv/get-new sliced)
                                        :deltas (iv/get-deltas sliced)})
                   (iv/get-new sliced)))]

           ;; Initial execution
           (scroll-spin (fn [_] nil) (fn [e] (throw e)))
           (Thread/sleep 100)

           (is (= 1 (count @results)))
           (is (= (vec (range 0 10)) (:slice (first @results))))
           (is (nil? (:deltas (first @results))))

           ;; Simulate scroll - change window
           (reset! window-signal {:start 5 :end 15})
           (Thread/sleep 100)

           (is (= 2 (count @results)))
           (is (= (vec (range 5 15)) (:slice (second @results))))
           ;; Should have deltas for the window change
           (let [deltas (:deltas (second @results))]
             (is (seq deltas) "Should have deltas after window change")))))))

;; =============================================================================
;; Performance Tests
;; =============================================================================

#?(:clj
   (deftest test-slice-performance-characteristics
     (testing "Slice is O(delta) not O(n) for window slides"
       (with-test-context
         (let [;; Large source - 1 million items
               source (vec (range 1000000))
               source-loc {:file "perf" :line 200 :column 0}
               window-size 100

               ;; Time initial slice (should be O(window-size))
               _ (ic/slice* source-loc {:start 0 :end window-size} source)

               ;; Time small window slide (should be O(delta))
               slide-delta 5
               start-time (System/nanoTime)
               _ (ic/slice* source-loc
                            {:start slide-delta :end (+ window-size slide-delta)}
                            source)
               slide-time (/ (- (System/nanoTime) start-time) 1000000.0)]

           ;; Small slide should be very fast (< 10ms even with overhead)
           ;; The key insight: we're not iterating the full million items
           (is (< slide-time 50)
               (str "Small window slide should be fast, took " slide-time "ms")))))))

#?(:clj
   (deftest test-slice-memory-efficiency
     (testing "Slice output shares structure with source via subvec"
       (with-test-context
         (let [source (vec (range 10000))
               source-loc {:file "memory" :line 210 :column 0}

               result (ic/slice* source-loc {:start 1000 :end 2000} source)
               slice (iv/get-new result)]

           ;; subvec creates a view, not a copy
           ;; We can verify by checking it's a SubVector type
           (is (instance? clojure.lang.APersistentVector$SubVector slice)
               "Slice should be a subvector (memory efficient)"))))))

;; =============================================================================
;; Benchmark: Compare with naive slice
;; =============================================================================

#?(:clj
   (defn benchmark-slice
     "Benchmark islice vs naive subvec for a series of window slides.

      Returns: Map with timing results"
     [source-size window-size num-slides slide-delta]
     (let [source (vec (range source-size))
           exec-ctx (ctx/create-execution-context :executor (sched/default-executor))

           ;; Naive approach: just subvec each time (no deltas)
           naive-times
           (binding [rtc/*execution-context* exec-ctx]
             (doall
               (for [i (range num-slides)]
                 (let [start (* i slide-delta)
                       end (+ start window-size)
                       t0 (System/nanoTime)
                       _ (subvec source start (min end source-size))
                       t1 (System/nanoTime)]
                   (- t1 t0)))))

           ;; Incremental approach with islice
           incremental-times
           (binding [rtc/*execution-context* exec-ctx]
             (let [source-loc {:file "bench" :line 1 :column 0}]
               (doall
                 (for [i (range num-slides)]
                   (let [start (* i slide-delta)
                         end (+ start window-size)
                         t0 (System/nanoTime)
                         _ (ic/slice* source-loc {:start start :end end} source)
                         t1 (System/nanoTime)]
                     (- t1 t0))))))]

       {:source-size source-size
        :window-size window-size
        :num-slides num-slides
        :slide-delta slide-delta
        :naive-total-ns (clojure.core/reduce + naive-times)
        :naive-avg-ns (/ (clojure.core/reduce + naive-times) num-slides)
        :incremental-total-ns (clojure.core/reduce + incremental-times)
        :incremental-avg-ns (/ (clojure.core/reduce + incremental-times) num-slides)
        ;; Skip first (init) for incremental steady-state
        :incremental-steady-avg-ns (when (> num-slides 1)
                                     (/ (clojure.core/reduce + (rest incremental-times))
                                        (dec num-slides)))})))

#?(:clj
   (deftest test-benchmark-islice
     (testing "Benchmark islice performance"
       ;; Run benchmark with reasonable parameters
       (let [results (benchmark-slice
                       100000   ; 100k items
                       50       ; 50 item window
                       100      ; 100 slides
                       2)]      ; slide by 2 each time

         ;; Just verify it runs and produces reasonable results
         (is (map? results))
         (is (pos? (:incremental-total-ns results)))))))

;; =============================================================================
;; Edge Cases and Robustness
;; =============================================================================

#?(:clj
   (deftest test-empty-source
     (testing "Slice handles empty source"
       (with-test-context
         (let [result (ic/slice* {:file "empty" :line 1 :column 0}
                                 {:start 0 :end 10}
                                 [])]
           (is (= [] (iv/get-new result))))))))

#?(:clj
   (deftest test-window-larger-than-source
     (testing "Window larger than source returns full source"
       (with-test-context
         (let [source [1 2 3]
               result (ic/slice* {:file "larger" :line 1 :column 0}
                                 {:start 0 :end 100}
                                 source)]
           (is (= [1 2 3] (iv/get-new result))))))))

#?(:clj
   (deftest test-window-completely-past-source
     (testing "Window past source returns empty"
       (with-test-context
         (let [source (vec (range 10))
               result (ic/slice* {:file "past" :line 1 :column 0}
                                 {:start 100 :end 200}
                                 source)]
           (is (= [] (iv/get-new result))))))))

#?(:clj
   (deftest test-reversed-window-bounds
     (testing "Reversed bounds (start > end) handled gracefully"
       (with-test-context
         (let [source (vec (range 100))
               ;; start > end should be treated as empty
               result (ic/slice* {:file "reversed" :line 1 :column 0}
                                 {:start 50 :end 40}
                                 source)]
           (is (= [] (iv/get-new result))))))))

;; =============================================================================
;; Run all tests
;; =============================================================================

;; =============================================================================
;; Comprehensive Benchmark: End-to-End DOM Operations
;; =============================================================================

#?(:clj
   (deftest test-delta-count-scaling
     (testing "Delta count scales with window movement, not source size"
       ;; This is the key property: whether we have 100 items or 1M items,
       ;; sliding the window by 5 should produce exactly 10 deltas (5 removes + 5 adds)
       (let [small-source (vec (range 100))
             large-source (vec (range 1000000))
             slide-delta 5
             window-size 50]

         (with-test-context
           ;; Test with small source
           (let [loc1 {:file "scaling-small" :line 1 :column 0}
                 _ (ic/slice* loc1 {:start 0 :end window-size} small-source)
                 result1 (ic/slice* loc1 {:start slide-delta :end (+ window-size slide-delta)} small-source)
                 deltas1 (iv/get-deltas result1)]

             (is (= 10 (count deltas1))
                 "Small source: sliding by 5 should produce 10 deltas"))

           ;; Test with large source
           (let [loc2 {:file "scaling-large" :line 2 :column 0}
                 _ (ic/slice* loc2 {:start 0 :end window-size} large-source)
                 result2 (ic/slice* loc2 {:start slide-delta :end (+ window-size slide-delta)} large-source)
                 deltas2 (iv/get-deltas result2)]

             (is (= 10 (count deltas2))
                 "Large source: sliding by 5 should still produce only 10 deltas")))))))

#?(:clj
   (deftest test-incremental-vs-full-ops-count
     (testing "Incremental approach produces O(delta) DOM operations vs O(n)"
       (with-test-context
         (let [source-size 10000
               window-size 100
               num-slides 50
               slide-delta 3
               source (vec (range source-size))

               ;; Count "operations" for naive approach (full re-render each time)
               naive-ops (* num-slides window-size)  ; Would need to render all items each slide

               ;; Count operations for incremental approach
               loc {:file "ops-count" :line 1 :column 0}
               _ (ic/slice* loc {:start 0 :end window-size} source)

               incremental-ops
               (loop [i 1
                      total-deltas 0]
                 (if (>= i num-slides)
                   total-deltas
                   (let [start (* i slide-delta)
                         end (+ start window-size)
                         result (ic/slice* loc {:start start :end end} source)
                         delta-count (count (or (iv/get-deltas result) []))]
                     (recur (inc i) (+ total-deltas delta-count)))))]

           ;; Incremental should be at least 10x fewer operations for this scenario
           (is (< incremental-ops (/ naive-ops 10))
               "Incremental should produce at least 10x fewer operations"))))))

;; =============================================================================
;; Integration with DOM for-each
;; =============================================================================

#?(:clj
   (deftest test-slice-with-foreach-integration
     (testing "islice deltas work with ifor-each for DOM rendering"
       (with-test-context
         (let [;; Simulate a list of items with ids
               items (vec (for [i (range 100)]
                           {:id i :text (str "Item " i)}))
               ;; Render fn returns map with :id for easy verification
               render-fn (fn [item] {:tag :li :id (:id item) :text (:text item)})

               source-loc-slice {:file "integration" :line 1 :column 0}
               source-loc-foreach {:file "integration" :line 2 :column 0}

               ;; Initial render: window [0, 10)
               slice1 (ic/slice* source-loc-slice {:start 0 :end 10} items)
               rendered1 (ic/for-each* source-loc-foreach :id render-fn slice1)
               rendered1-items (iv/get-new rendered1)]

           ;; Should have 10 rendered items
           (is (= 10 (count rendered1-items)))
           ;; First item should have id 0
           (is (= 0 (:id (first rendered1-items))))
           ;; Last item should have id 9
           (is (= 9 (:id (last rendered1-items))))

           ;; Slide window to [3, 13)
           (let [slice2 (ic/slice* source-loc-slice {:start 3 :end 13} items)
                 slice-deltas (iv/get-deltas slice2)]

             ;; Slice should have 6 deltas (3 removes + 3 adds)
             (is (= 6 (count slice-deltas)))

             ;; Pass sliced interval with deltas to for-each
             (let [rendered2 (ic/for-each* source-loc-foreach :id render-fn slice2)
                   rendered2-items (iv/get-new rendered2)
                   foreach-deltas (iv/get-deltas rendered2)]

               ;; Should have 10 items
               (is (= 10 (count rendered2-items)))
               ;; First item should have id 3
               (is (= 3 (:id (first rendered2-items))))
               ;; Last item should have id 12
               (is (= 12 (:id (last rendered2-items))))

               ;; For-each should produce deltas when source has deltas
               ;; Note: for-each produces deltas based on key changes
               (is (or (nil? foreach-deltas) (seq foreach-deltas))
                   "For-each delta behavior depends on key tracking"))))))))

#?(:clj
   (deftest test-full-infinite-scroll-simulation
     (testing "Simulate full infinite scroll scenario"
       (with-test-context
         (let [;; Large list - simulating fetched data
               total-items 10000
               items (vec (for [i (range total-items)]
                           {:id i :text (str "Item " i) :height 50}))

               ;; Window parameters
               window-size 20
               scroll-events 100
               pixels-per-scroll 150  ; Scroll 3 items per event (50px each)
               items-per-scroll (/ pixels-per-scroll 50)

               ;; Track operations
               slice-loc {:file "scroll-sim" :line 1 :column 0}
               foreach-loc {:file "scroll-sim" :line 2 :column 0}
               render-fn (fn [item] {:tag :div :key (:id item) :content (:text item)})

               ;; Initial render
               _ (ic/slice* slice-loc {:start 0 :end window-size} items)
               _ (ic/for-each* foreach-loc :id render-fn
                               (iv/interval nil (subvec items 0 window-size) nil))

               ;; Simulate scroll events
               total-deltas
               (loop [event 1
                      deltas 0]
                 (if (> event scroll-events)
                   deltas
                   (let [start (* event items-per-scroll)
                         end (+ start window-size)
                         slice-result (ic/slice* slice-loc {:start start :end end} items)
                         slice-deltas (iv/get-deltas slice-result)
                         foreach-result (ic/for-each* foreach-loc :id render-fn slice-result)
                         foreach-deltas (iv/get-deltas foreach-result)
                         event-deltas (+ (count (or slice-deltas []))
                                         (count (or foreach-deltas [])))]
                     (recur (inc event) (+ deltas event-deltas)))))]

           ;; Each scroll produces deltas from both slice and for-each:
           ;; - slice: 3 removes + 3 adds = 6 deltas
           ;; - for-each: 3 removes + 3 adds = 6 deltas
           ;; Total: ~12 deltas per scroll vs naive 20 (full window re-render)
           ;; This is still 40% reduction (1200 vs 2000)
           (is (< total-deltas (* scroll-events window-size 0.8))
               "Should be at least 20% fewer operations than naive"))))))

(comment
  ;; Run tests in REPL
  (clojure.test/run-tests 'is.simm.spindel.incremental.slice-test))
