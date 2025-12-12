(ns is.simm.spindel.incremental.deltaable-test
  "Comprehensive tests for deltaable collections and delta tracking.
   Ported from laufzeit."
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [is.simm.spindel.incremental.deltaable :as d]
            [is.simm.spindel.incremental.interval :as iv]
            [is.simm.spindel.runtime.context :as ctx]
            [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.state.signal :as sig]))

;; =============================================================================
;; Interval Tests (formerly SignalValue/SignalDeltaView)
;; =============================================================================

(deftest test-interval-creation
  (testing "Interval creation and access"
    (let [iv (sig/signal-interval 41 42)]
      (is (= 42 (iv/get-new iv)))
      (is (= 41 (iv/get-old iv)))
      (is (= 42 @iv) "Deref returns current value")))

  (testing "Interval with nil old value"
    (let [iv (sig/signal-interval 42)]
      (is (= 42 (iv/get-new iv)))
      (is (nil? (iv/get-old iv)))))

  (testing "Interval destructuring via nth"
    (let [iv (sig/signal-interval 41 42)]
      (is (= 42 (nth iv 0)) "Index 0 returns new value")
      (is (= 41 (nth iv 1)) "Index 1 returns old-value")
      (is (nil? (nth iv 2)) "Index 2 returns deltas (nil for non-deltaable)")))

  (testing "Interval destructuring with let"
    (let [iv (sig/signal-interval 41 42)
          [new old deltas] iv]
      (is (= 42 new))
      (is (= 41 old))
      (is (nil? deltas))))

  (testing "Interval out of bounds"
    (let [iv (sig/signal-interval 41 42)]
      (is (thrown? #?(:clj IndexOutOfBoundsException :cljs js/Error) (nth iv 3)))
      (is (= :not-found (nth iv 3 :not-found))))))

;; =============================================================================
;; DeltaableValue Tests
;; =============================================================================

(deftest test-deltaable-value
  (testing "DeltaableValue creation"
    (let [dv (d/deltaable-value 42)]
      (is (= 42 @dv))
      (is (nil? (d/get-deltas dv)) "Simple values have no structural deltas")))

  (testing "DeltaableValue equality"
    (let [dv1 (d/deltaable-value 42)
          dv2 (d/deltaable-value 42)
          dv3 (d/deltaable-value 43)]
      (is (= dv1 dv2))
      (is (not= dv1 dv3))))

  (testing "DeltaableValue with different types"
    (is (nil? (d/get-deltas (d/deltaable-value "hello"))))
    (is (nil? (d/get-deltas (d/deltaable-value :keyword))))
    (is (nil? (d/get-deltas (d/deltaable-value [1 2 3]))))))

;; =============================================================================
;; Protocol Extension Tests
;; =============================================================================

(deftest test-protocol-extension
  (testing "IDeltaable extended to all values"
    (is (nil? (d/get-deltas 42)) "Numbers return nil")
    (is (nil? (d/get-deltas "hello")) "Strings return nil")
    (is (nil? (d/get-deltas :keyword)) "Keywords return nil")
    (is (nil? (d/get-deltas nil)) "nil returns nil")
    (is (nil? (d/get-deltas [1 2 3])) "Plain vectors return nil")))

;; =============================================================================
;; Helper Function Tests
;; =============================================================================

(deftest test-helper-functions
  (testing "has-deltas?"
    (is (not (d/has-deltas? 42)))
    (is (not (d/has-deltas? (d/deltaable-value 42))))
    (is (not (d/has-deltas? nil))))

  (testing "deltaable? - returns true only for deltaable collections"
    ;; Plain values are not deltaable collections
    (is (not (d/deltaable? 42)))
    (is (not (d/deltaable? (d/deltaable-value 42))))
    (is (not (d/deltaable? nil)))
    (is (not (d/deltaable? [1 2 3])))
    (is (not (d/deltaable? {:a 1})))
    (is (not (d/deltaable? #{1 2})))

    ;; Deltaable collections return true
    (is (d/deltaable? (d/deltaable-vector [1 2 3])))
    (is (d/deltaable? (d/deltaable-map {:a 1})))
    (is (d/deltaable? (d/deltaable-set #{1 2}))))

  (testing "unwrap"
    (is (= 42 (d/unwrap (d/deltaable-value 42))))
    (is (= 42 @(sig/signal-interval 41 42)) "Interval uses IDeref for unwrapping")
    (is (= 42 (d/unwrap 42)) "Non-wrapped values return as-is")
    (is (= [1 2 3] (d/unwrap [1 2 3])))))

;; =============================================================================
;; Signal Integration Tests
;; =============================================================================

(deftest test-interval-with-deltaable-value
  (testing "Interval containing DeltaableValue"
    (let [dv-new (d/deltaable-value 42)
          dv-old (d/deltaable-value 41)
          iv (sig/signal-interval dv-old dv-new)
          [new old deltas] iv]
      (is (= dv-new new))
      (is (= dv-old old))
      (is (nil? deltas) "DeltaableValue has no structural deltas"))))

;; CLJ-only: Signal macro not available in CLJS
#?(:clj
   (deftest test-signal-integration
     (testing "Signal integration with dual perspective"
       (let [ctx (ctx/create-execution-context)]

         (binding [rtc/*execution-context* ctx]
           (let [counter (sig/signal 0)]
           ;; Initial state
           (let [[new old deltas] (sig/get-signal-detailed counter)]
             (is (= 0 new) "Initial value is 0")
             (is (nil? old) "No old value initially")
             (is (nil? deltas) "No deltas for simple values"))

           ;; After swap
           (swap! counter inc)

           (let [[new old deltas] (sig/get-signal-detailed counter)]
             (is (= 1 new) "New value is 1")
             (is (= 0 old) "Old value is 0")
             (is (nil? deltas) "No deltas for simple values"))

           ;; Deref returns current value
           (is (= 1 @(sig/get-signal-detailed counter))
               "Dereferencing SignalValue returns current value")))))))

;; =============================================================================
;; DeltaableVector Tests
;; =============================================================================

(deftest test-deltaable-vector-creation
  (testing "DeltaableVector creation"
    (let [dv (d/deltaable-vector [1 2 3])]
      (is (= 3 (count dv)))
      (is (= 1 (nth dv 0)))
      (is (= 2 (nth dv 1)))
      (is (= 3 (nth dv 2)))
      (is (empty? (d/get-deltas dv)) "No deltas initially")))

  (testing "DeltaableVector with empty collection"
    (let [dv (d/deltaable-vector [])]
      (is (zero? (count dv)))
      (is (empty? (d/get-deltas dv))))))

(deftest test-deltaable-vector-conj
  (testing "conj operation records :add delta"
    (let [dv (d/deltaable-vector [1 2])
          dv2 (conj dv 3)]

      ;; Check value
      (is (= [1 2 3] @dv2))
      (is (= 3 (count dv2)))

      ;; Check deltas
      (let [deltas (d/get-deltas dv2)]
        (is (= 1 (count deltas)))
        (is (= :add (:delta (first deltas))))
        (is (= [2] (:path (first deltas))))  ; Added at index 2
        (is (= 3 (:value (first deltas))))))))

(deftest test-deltaable-vector-assoc
  (testing "assoc operation records :update delta"
    (let [dv (d/deltaable-vector [1 2 3])
          dv2 (assoc dv 1 99)]

      ;; Check value
      (is (= [1 99 3] @dv2))

      ;; Check deltas
      (let [deltas (d/get-deltas dv2)]
        (is (= 1 (count deltas)))
        (is (= :update (:delta (first deltas))))
        (is (= [1] (:path (first deltas))))
        (is (= 99 (:value (first deltas))))
        (is (= 2 (:old-value (first deltas))))))))

(deftest test-deltaable-vector-multiple-ops
  (testing "Multiple operations accumulate deltas"
    (let [dv (d/deltaable-vector [1 2])
          dv2 (-> dv
                  (conj 3)
                  (assoc 0 10)
                  (conj 4))]

      ;; Check value
      (is (= [10 2 3 4] @dv2))

      ;; Check deltas
      (let [deltas (d/get-deltas dv2)]
        (is (= 3 (count deltas)))

        ;; First: conj 3 at index 2
        (is (= :add (:delta (nth deltas 0))))
        (is (= [2] (:path (nth deltas 0))))
        (is (= 3 (:value (nth deltas 0))))

        ;; Second: assoc 10 at index 0
        (is (= :update (:delta (nth deltas 1))))
        (is (= [0] (:path (nth deltas 1))))
        (is (= 10 (:value (nth deltas 1))))
        (is (= 1 (:old-value (nth deltas 1))))

        ;; Third: conj 4 at index 3
        (is (= :add (:delta (nth deltas 2))))
        (is (= [3] (:path (nth deltas 2))))
        (is (= 4 (:value (nth deltas 2))))))))

(deftest test-deltaable-vector-reset-deltas
  (testing "clear-deltas returns new instance with cleared deltas"
    (let [dv (d/deltaable-vector [1 2])
          dv2 (conj dv 3)]

      ;; Has deltas
      (is (= 1 (count (d/get-deltas dv2))))

      ;; Clear deltas returns new instance
      (let [dv3 (d/clear-deltas dv2)]
        ;; Deltas cleared in new instance
        (is (empty? (d/get-deltas dv3)))

        ;; Value unchanged
        (is (= [1 2 3] @dv3))))))

(deftest test-deltaable-vector-nested
  (testing "Shallow wrapping: nested vectors are NOT automatically wrapped"
    (let [dv (d/deltaable-vector [[1 2] [3 4]])
          ;; Get nested vector
          inner (nth dv 0)]

      ;; With shallow wrapping, inner vector is NOT deltaable
      (is (not (d/deltaable? inner)))
      (is (vector? inner))
      (is (= [1 2] inner))

      ;; Modifying the outer vector tracks top-level changes only
      (let [dv2 (assoc dv 0 [1 2 99])
            deltas (d/get-deltas dv2)]
        (is (= 1 (count deltas)))
        (is (= :update (:delta (first deltas))))
        (is (= [0] (:path (first deltas))))  ; Top-level path only
        (is (= [1 2 99] (:value (first deltas))))
        (is (= [1 2] (:old-value (first deltas))))))))

(deftest test-deltaable-vector-equality
  (testing "DeltaableVector converts to plain vector with unwrap-deltaable"
    (let [dv (d/deltaable-vector [1 2 3])]
      (is (= [1 2 3] (d/unwrap-deltaable dv)))
      ;; CLJ: DeltaableVectors only equal other DeltaableVectors, not plain vectors
      ;; CLJS: IEquiv makes them equal to plain vectors for collection compatibility
      #?(:clj (is (not= dv [1 2 3])))))

  (testing "DeltaableVector equality with other DeltaableVectors"
    (let [dv1 (d/deltaable-vector [1 2 3])
          dv2 (d/deltaable-vector [1 2 3])
          dv3 (d/deltaable-vector [1 2 4])]
      (is (= dv1 dv2))
      (is (not= dv1 dv3)))))

(deftest test-deltaable-vector-deref
  (testing "Deref returns underlying vector (unwrapped simple values)"
    (let [dv (d/deltaable-vector [1 2 3])]
      (is (= [1 2 3] @dv))
      (is (vector? @dv))))

  (testing "Deref returns underlying vector (nested vectors are plain)"
    (let [dv (d/deltaable-vector [[1 2] [3 4]])]
      ;; Deref returns internal vector
      (let [v @dv]
        (is (vector? v))
        (is (= 2 (count v)))
        ;; With shallow wrapping, nested vectors are plain (NOT deltaable)
        (is (not (d/deltaable? (nth v 0))))
        (is (not (d/deltaable? (nth v 1))))
        (is (= [1 2] (nth v 0)))
        (is (= [3 4] (nth v 1)))))))

;; =============================================================================
;; DeltaableVector pop/remove-at/filter-vec Tests
;; =============================================================================

(deftest test-deltaable-vector-pop
  (testing "pop removes last element with :remove delta"
    (let [dv (d/deltaable-vector [1 2 3])
          dv2 (pop dv)]
      (is (= [1 2] @dv2))
      (is (= 1 (count (d/get-deltas dv2))))
      (let [delta (first (d/get-deltas dv2))]
        (is (= :remove (:delta delta)))
        (is (= [2] (:path delta)))
        (is (= 3 (:old-value delta))))))

  (testing "pop on empty vector throws"
    (let [dv (d/deltaable-vector [])]
      (is (thrown? #?(:clj IllegalStateException :cljs js/Error) (pop dv)))))

  (testing "peek returns last element"
    (let [dv (d/deltaable-vector [1 2 3])]
      (is (= 3 (peek dv))))))

(deftest test-deltaable-vector-remove-at
  (testing "remove-at removes element at index with :remove delta"
    (let [dv (d/deltaable-vector [1 2 3 4])
          dv2 (d/remove-at dv 1)]
      (is (= [1 3 4] @dv2))
      (is (= 1 (count (d/get-deltas dv2))))
      (let [delta (first (d/get-deltas dv2))]
        (is (= :remove (:delta delta)))
        (is (= [1] (:path delta)))
        (is (= 2 (:old-value delta))))))

  (testing "remove-at first element"
    (let [dv (d/deltaable-vector [:a :b :c])
          dv2 (d/remove-at dv 0)]
      (is (= [:b :c] @dv2))
      (is (= :a (:old-value (first (d/get-deltas dv2)))))))

  (testing "remove-at last element"
    (let [dv (d/deltaable-vector [:a :b :c])
          dv2 (d/remove-at dv 2)]
      (is (= [:a :b] @dv2))
      (is (= :c (:old-value (first (d/get-deltas dv2)))))))

  (testing "remove-at with invalid index throws"
    (let [dv (d/deltaable-vector [1 2 3])]
      (is (thrown? #?(:clj IllegalArgumentException :cljs js/Error) (d/remove-at dv -1)))
      (is (thrown? #?(:clj IllegalArgumentException :cljs js/Error) (d/remove-at dv 5))))))

(deftest test-deltaable-vector-insert-at
  (testing "insert-at inserts element at index with :add delta"
    (let [dv (d/deltaable-vector [1 2 3 4])
          dv2 (d/insert-at dv 2 :new)]
      (is (= [1 2 :new 3 4] @dv2))
      (is (= 1 (count (d/get-deltas dv2))))
      (let [delta (first (d/get-deltas dv2))]
        (is (= :add (:delta delta)))
        (is (= [2] (:path delta)))
        (is (= :new (:value delta))))))

  (testing "insert-at at beginning"
    (let [dv (d/deltaable-vector [:a :b :c])
          dv2 (d/insert-at dv 0 :first)]
      (is (= [:first :a :b :c] @dv2))
      (is (= [0] (:path (first (d/get-deltas dv2)))))))

  (testing "insert-at at end (append)"
    (let [dv (d/deltaable-vector [:a :b :c])
          dv2 (d/insert-at dv 3 :last)]
      (is (= [:a :b :c :last] @dv2))
      (is (= [3] (:path (first (d/get-deltas dv2)))))))

  (testing "insert-at into empty vector"
    (let [dv (d/deltaable-vector [])
          dv2 (d/insert-at dv 0 :only)]
      (is (= [:only] @dv2))
      (is (= [0] (:path (first (d/get-deltas dv2)))))))

  (testing "insert-at preserves existing deltas"
    (let [dv (-> (d/deltaable-vector [1 2])
                 (conj 3))
          dv2 (d/insert-at dv 1 :inserted)]
      (is (= [1 :inserted 2 3] @dv2))
      ;; Should have original :add delta + new :add delta
      (is (= 2 (count (d/get-deltas dv2))))
      (is (every? #(= :add (:delta %)) (d/get-deltas dv2)))))

  (testing "insert-at with invalid index throws"
    (let [dv (d/deltaable-vector [1 2 3])]
      (is (thrown? #?(:clj IllegalArgumentException :cljs js/Error) (d/insert-at dv -1 :x)))
      (is (thrown? #?(:clj IllegalArgumentException :cljs js/Error) (d/insert-at dv 5 :x))))))

(deftest test-deltaable-vector-filter-vec
  (testing "filter-vec keeps matching elements with :remove deltas for filtered out"
    (let [dv (d/deltaable-vector [1 2 3 4 5])
          dv2 (d/filter-vec even? dv)]
      (is (= [2 4] @dv2))
      ;; Should have 3 :remove deltas for odd numbers
      (is (= 3 (count (d/get-deltas dv2))))
      (is (every? #(= :remove (:delta %)) (d/get-deltas dv2)))))

  (testing "filter-vec preserves existing deltas"
    (let [dv (-> (d/deltaable-vector [1 2 3])
                 (conj 4))
          dv2 (d/filter-vec even? dv)]
      (is (= [2 4] @dv2))
      ;; Should have original :add delta + :remove deltas
      (let [deltas (d/get-deltas dv2)]
        (is (some #(= :add (:delta %)) deltas))
        (is (some #(= :remove (:delta %)) deltas)))))

  (testing "filter-vec with no matches returns empty vector"
    (let [dv (d/deltaable-vector [1 3 5])
          dv2 (d/filter-vec even? dv)]
      (is (= [] @dv2))
      (is (= 3 (count (d/get-deltas dv2))))))

  (testing "filter-vec with all matches returns same elements"
    (let [dv (d/deltaable-vector [2 4 6])
          dv2 (d/filter-vec even? dv)]
      (is (= [2 4 6] @dv2))
      (is (= 0 (count (d/get-deltas dv2)))))))

(deftest test-deltaable-vector-move-to
  (testing "move-to moves element forward with :move delta"
    (let [dv (d/deltaable-vector [:a :b :c :d])
          dv2 (d/move-to dv 0 2)]  ; Move first element to position 2
      (is (= [:b :c :a :d] @dv2) "Element moved from index 0 to index 2")
      (is (= 1 (count (d/get-deltas dv2))))
      (let [delta (first (d/get-deltas dv2))]
        (is (= :move (:delta delta)))
        (is (= [0] (:from-path delta)))
        (is (= [2] (:to-path delta)))
        (is (= :a (:value delta))))))

  (testing "move-to moves element backward"
    (let [dv (d/deltaable-vector [:a :b :c :d])
          dv2 (d/move-to dv 3 1)]  ; Move last element to position 1
      (is (= [:a :d :b :c] @dv2) "Element moved from index 3 to index 1")
      (let [delta (first (d/get-deltas dv2))]
        (is (= :move (:delta delta)))
        (is (= [3] (:from-path delta)))
        (is (= [1] (:to-path delta)))
        (is (= :d (:value delta))))))

  (testing "move-to same position is identity"
    (let [dv (d/deltaable-vector [:a :b :c])
          dv2 (d/move-to dv 1 1)]
      (is (= [:a :b :c] @dv2) "No change when moving to same position")))

  (testing "move-to last position"
    (let [dv (d/deltaable-vector [:a :b :c :d])
          dv2 (d/move-to dv 0 3)]  ; Move first to last
      (is (= [:b :c :d :a] @dv2))))

  (testing "move-to first position"
    (let [dv (d/deltaable-vector [:a :b :c :d])
          dv2 (d/move-to dv 3 0)]  ; Move last to first
      (is (= [:d :a :b :c] @dv2))))

  (testing "move-to with invalid indices throws"
    (let [dv (d/deltaable-vector [:a :b :c])]
      (is (thrown? #?(:clj IllegalArgumentException :cljs js/Error) (d/move-to dv -1 1)))
      (is (thrown? #?(:clj IllegalArgumentException :cljs js/Error) (d/move-to dv 5 1)))
      (is (thrown? #?(:clj IllegalArgumentException :cljs js/Error) (d/move-to dv 1 -1)))
      (is (thrown? #?(:clj IllegalArgumentException :cljs js/Error) (d/move-to dv 1 5))))))

(deftest test-apply-delta-move
  (testing "apply-delta handles :move delta"
    (let [v [:a :b :c :d]
          delta {:delta :move :from-path [0] :to-path [2] :value :a}
          result (d/apply-delta v delta)]
      (is (= [:b :c :a :d] result))))

  (testing "apply-delta move backward"
    (let [v [:a :b :c :d]
          delta {:delta :move :from-path [3] :to-path [1] :value :d}
          result (d/apply-delta v delta)]
      (is (= [:a :d :b :c] result))))

  (testing "apply-delta move ignores non-vectors"
    (let [m {:a 1 :b 2}
          delta {:delta :move :from-path [0] :to-path [1] :value :a}
          result (d/apply-delta m delta)]
      (is (= {:a 1 :b 2} result) "Maps unchanged by move"))))

;; =============================================================================
;; Delta Transducer Tests
;; =============================================================================

(deftest test-delta-map
  (testing "d/map transforms :add deltas"
    (let [delta {:delta :add :path [0] :value 1}
          xf (d/map inc)
          result (transduce xf conj [] [delta])]
      (is (= 1 (count result)))
      (is (= :add (:delta (first result))))
      (is (= 2 (:value (first result))))))

  (testing "d/map transforms :update deltas (both values)"
    (let [delta {:delta :update :path [0] :value 2 :old-value 1}
          xf (d/map inc)
          result (transduce xf conj [] [delta])]
      (is (= 1 (count result)))
      (is (= :update (:delta (first result))))
      (is (= 3 (:value (first result))))
      (is (= 2 (:old-value (first result))))))

  (testing "d/map passes through :remove deltas unchanged"
    (let [delta {:delta :remove :path [0]}
          xf (d/map inc)
          result (transduce xf conj [] [delta])]
      (is (= 1 (count result)))
      (is (= delta (first result))))))

(deftest test-delta-filter
  (testing "d/filter keeps :add deltas that pass predicate"
    (let [delta-pass {:delta :add :path [0] :value 2}
          delta-fail {:delta :add :path [1] :value 1}
          xf (d/filter even?)
          result (transduce xf conj [] [delta-pass delta-fail])]
      (is (= 1 (count result)))
      (is (= delta-pass (first result)))))

  (testing "d/filter with :update - both pass"
    (let [delta {:delta :update :path [0] :value 4 :old-value 2}
          xf (d/filter even?)
          result (transduce xf conj [] [delta])]
      (is (= 1 (count result)))
      (is (= :update (:delta (first result))))
      (is (= 4 (:value (first result))))
      (is (= 2 (:old-value (first result))))))

  (testing "d/filter with :update - entered filter (old fail, new pass)"
    (let [delta {:delta :update :path [0] :value 4 :old-value 3}
          xf (d/filter even?)
          result (transduce xf conj [] [delta])]
      (is (= 1 (count result)))
      (is (= :add (:delta (first result))))
      (is (= 4 (:value (first result))))
      (is (nil? (:old-value (first result))))))

  (testing "d/filter with :update - exited filter (old pass, new fail)"
    (let [delta {:delta :update :path [0] :value 3 :old-value 4}
          xf (d/filter even?)
          result (transduce xf conj [] [delta])]
      (is (= 1 (count result)))
      (is (= :remove (:delta (first result))))
      (is (nil? (:old-value (first result))))))

  (testing "d/filter with :update - neither pass"
    (let [delta {:delta :update :path [0] :value 3 :old-value 1}
          xf (d/filter even?)
          result (transduce xf conj [] [delta])]
      (is (empty? result)))))

(deftest test-delta-remove
  (testing "d/remove filters out matching deltas"
    (let [delta-odd {:delta :add :path [0] :value 1}
          delta-even {:delta :add :path [1] :value 2}
          xf (d/remove odd?)
          result (transduce xf conj [] [delta-odd delta-even])]
      (is (= 1 (count result)))
      (is (= 2 (:value (first result)))))))

(deftest test-delta-keep
  (testing "d/keep transforms and filters :add deltas"
    (let [delta-even {:delta :add :path [0] :value 2}
          delta-odd {:delta :add :path [1] :value 3}
          xf (d/keep #(when (even? %) (* 2 %)))
          result (transduce xf conj [] [delta-even delta-odd])]
      (is (= 1 (count result)))
      (is (= 4 (:value (first result))))))

  (testing "d/keep with :update - both some (stay in)"
    (let [delta {:delta :update :path [0] :value 4 :old-value 2}
          xf (d/keep #(when (even? %) (* 2 %)))
          result (transduce xf conj [] [delta])]
      (is (= 1 (count result)))
      (is (= :update (:delta (first result))))
      (is (= 8 (:value (first result))))
      (is (= 4 (:old-value (first result))))))

  (testing "d/keep with :update - entered (old nil, new some)"
    (let [delta {:delta :update :path [0] :value 4 :old-value 3}
          xf (d/keep #(when (even? %) (* 2 %)))
          result (transduce xf conj [] [delta])]
      (is (= 1 (count result)))
      (is (= :add (:delta (first result))))
      (is (= 8 (:value (first result))))))

  (testing "d/keep with :update - exited (old some, new nil)"
    (let [delta {:delta :update :path [0] :value 3 :old-value 4}
          xf (d/keep #(when (even? %) (* 2 %)))
          result (transduce xf conj [] [delta])]
      (is (= 1 (count result)))
      (is (= :remove (:delta (first result)))))))

(deftest test-delta-transducer-composition
  (testing "Compose d/map and d/filter"
    (let [deltas [{:delta :add :path [0] :value 1}
                  {:delta :add :path [1] :value 2}
                  {:delta :add :path [2] :value 3}]
          xf (comp (d/map inc) (d/filter even?))
          result (transduce xf conj [] deltas)]
      ;; inc: 1->2, 2->3, 3->4
      ;; filter even?: keep 2 and 4
      (is (= 2 (count result)))
      (is (= 2 (:value (nth result 0))))
      (is (= 4 (:value (nth result 1))))))

  (testing "Compose d/filter, d/map, d/remove"
    (let [deltas [{:delta :add :path [0] :value 1}
                  {:delta :add :path [1] :value 2}
                  {:delta :add :path [2] :value 3}
                  {:delta :add :path [3] :value 4}]
          xf (comp (d/filter even?) (d/map #(* % 2)) (d/remove #(> % 5)))
          result (transduce xf conj [] deltas)]
      ;; filter even?: 2, 4
      ;; map * 2: 4, 8
      ;; remove > 5: keep 4 (remove 8)
      (is (= 1 (count result)))
      (is (= 4 (:value (first result)))))))

;; =============================================================================
;; Delta Application Tests
;; =============================================================================

(deftest test-apply-delta-add
  (testing "Apply :add delta to plain vector"
    (let [delta {:delta :add :path [2] :value 3}
          result (d/apply-delta [1 2] delta)]
      (is (= [1 2 3] result))))

  (testing "Apply :add delta to DeltaableVector"
    (let [dv (d/deltaable-vector [1 2])
          delta {:delta :add :path [2] :value 3}
          result (d/apply-delta dv delta)]
      (is (= [1 2 3] @result)))))

(deftest test-apply-delta-update
  (testing "Apply :update delta to plain vector"
    (let [delta {:delta :update :path [1] :value 99 :old-value 2}
          result (d/apply-delta [1 2 3] delta)]
      (is (= [1 99 3] result))))

  (testing "Apply :update delta to DeltaableVector"
    (let [dv (d/deltaable-vector [1 2 3])
          delta {:delta :update :path [1] :value 99 :old-value 2}
          result (d/apply-delta dv delta)]
      (is (= [1 99 3] @result)))))

(deftest test-apply-delta-remove
  (testing "Apply :remove delta to plain vector"
    (let [delta {:delta :remove :path [1]}
          result (d/apply-delta [1 2 3] delta)]
      (is (= [1 3] result))))

  (testing "Apply :remove delta to map"
    (let [delta {:delta :remove :path [:b]}
          result (d/apply-delta {:a 1 :b 2 :c 3} delta)]
      (is (= {:a 1 :c 3} result)))))

(deftest test-apply-delta-multiple
  (testing "Apply multiple deltas in sequence"
    (let [deltas [{:delta :add :path [0] :value 1}
                  {:delta :add :path [1] :value 2}
                  {:delta :update :path [0] :value 10 :old-value 1}]
          result (reduce d/apply-delta [] deltas)]
      (is (= [10 2] result)))))

(deftest test-transduce-helper
  (testing "Transduce with transformation"
    (let [deltas [{:delta :add :path [0] :value 1}
                  {:delta :add :path [1] :value 2}
                  {:delta :add :path [2] :value 3}]
          result (d/transduce (d/map inc) [] deltas)]
      (is (= [2 3 4] result))))

  (testing "Transduce with filtering"
    (let [deltas [{:delta :add :path [0] :value 1}
                  {:delta :add :path [1] :value 2}
                  {:delta :add :path [2] :value 3}
                  {:delta :add :path [3] :value 4}]
          result (d/transduce (d/filter even?) [] deltas)]
      (is (= [2 4] result))))

  (testing "Transduce with composition"
    (let [deltas [{:delta :add :path [0] :value 1}
                  {:delta :add :path [1] :value 2}
                  {:delta :add :path [2] :value 3}]
          xf (comp (d/map inc) (d/filter even?))
          result (d/transduce xf [] deltas)]
      (is (= [2 4] result)))))

(deftest test-merge-deltas
  (testing "Merge multiple delta sequences"
    (let [deltas1 [{:delta :add :path [0] :value 1}]
          deltas2 [{:delta :add :path [1] :value 2}]
          deltas3 [{:delta :add :path [2] :value 3}]
          merged (d/merge-deltas deltas1 deltas2 deltas3)]
      (is (= 3 (count merged)))
      (is (= 1 (:value (nth merged 0))))
      (is (= 2 (:value (nth merged 1))))
      (is (= 3 (:value (nth merged 2)))))))

(deftest test-compact-deltas
  (testing "Compact add + remove = cancel"
    (let [deltas [{:delta :add :path [0] :value 1}
                  {:delta :remove :path [0]}]
          compacted (d/compact-deltas deltas)]
      (is (empty? compacted))))

  (testing "Compact multiple updates = keep last"
    (let [deltas [{:delta :update :path [0] :value 1 :old-value 0}
                  {:delta :update :path [0] :value 2 :old-value 1}
                  {:delta :update :path [0] :value 3 :old-value 2}]
          compacted (d/compact-deltas deltas)]
      (is (= 1 (count compacted)))
      (is (= 3 (:value (first compacted))))
      (is (= 0 (:old-value (first compacted))))))

  (testing "Compact add + update = add with new value"
    (let [deltas [{:delta :add :path [0] :value 1}
                  {:delta :update :path [0] :value 2 :old-value 1}]
          compacted (d/compact-deltas deltas)]
      (is (= 1 (count compacted)))
      (is (= :add (:delta (first compacted))))
      (is (= 2 (:value (first compacted))))))

  (testing "Compact remove + add = update"
    (let [deltas [{:delta :remove :path [0]}
                  {:delta :add :path [0] :value 2}]
          compacted (d/compact-deltas deltas)]
      (is (= 1 (count compacted)))
      (is (= :update (:delta (first compacted))))
      (is (= 2 (:value (first compacted))))))

  (testing "Compact preserves operations on different paths"
    (let [deltas [{:delta :add :path [0] :value 1}
                  {:delta :add :path [1] :value 2}
                  {:delta :update :path [0] :value 10 :old-value 1}]
          compacted (d/compact-deltas deltas)]
      (is (= 2 (count compacted))))))

;; =============================================================================
;; DeltaableMap Tests
;; =============================================================================

(deftest test-deltaable-map-creation
  (testing "Create empty DeltaableMap"
    (let [dm (d/deltaable-map {})]
      (is (= 0 (count dm)))
      (is (= {} @dm))
      (is (empty? (d/get-deltas dm)))))

  (testing "Create DeltaableMap with initial values"
    (let [dm (d/deltaable-map {:a 1 :b 2})]
      (is (= 2 (count dm)))
      (is (= 1 (:a dm)))
      (is (= 2 (:b dm)))
      (is (= {:a 1 :b 2} @dm))
      (is (empty? (d/get-deltas dm)))))

  (testing "DeltaableMap preserves metadata"
    (let [dm (with-meta (d/deltaable-map {:a 1}) {:foo :bar})]
      (is (= {:foo :bar} (meta dm))))))

(deftest test-deltaable-map-assoc
  (testing "Assoc new key generates :add delta"
    (let [dm (d/deltaable-map {:a 1})
          dm2 (assoc dm :b 2)]
      (is (= 2 (count dm2)))
      (is (= {:a 1 :b 2} @dm2))
      (let [deltas (d/get-deltas dm2)]
        (is (= 1 (count deltas)))
        (is (= :add (:delta (first deltas))))
        (is (= [:b] (:path (first deltas))))
        (is (= 2 (:value (first deltas)))))))

  (testing "Assoc existing key generates :update delta"
    (let [dm (d/deltaable-map {:a 1})
          dm2 (assoc dm :a 10)]
      (is (= 1 (count dm2)))
      (is (= {:a 10} @dm2))
      (let [deltas (d/get-deltas dm2)]
        (is (= 1 (count deltas)))
        (is (= :update (:delta (first deltas))))
        (is (= [:a] (:path (first deltas))))
        (is (= 10 (:value (first deltas))))
        (is (= 1 (:old-value (first deltas)))))))

  (testing "Multiple assocs accumulate deltas"
    (let [dm (-> (d/deltaable-map {:a 1})
                 (assoc :b 2)
                 (assoc :c 3))]
      (is (= {:a 1 :b 2 :c 3} @dm))
      (let [deltas (d/get-deltas dm)]
        (is (= 2 (count deltas)))
        (is (every? #(= :add (:delta %)) deltas))))))

(deftest test-deltaable-map-dissoc
  (testing "Dissoc generates :remove delta"
    (let [dm (d/deltaable-map {:a 1 :b 2})
          dm2 (dissoc dm :b)]
      (is (= 1 (count dm2)))
      (is (= {:a 1} @dm2))
      (let [deltas (d/get-deltas dm2)]
        (is (= 1 (count deltas)))
        (is (= :remove (:delta (first deltas))))
        (is (= [:b] (:path (first deltas))))
        (is (= 2 (:old-value (first deltas)))))))

  (testing "Dissoc non-existent key has no effect"
    (let [dm (d/deltaable-map {:a 1})
          dm2 (dissoc dm :b)]
      (is (= dm dm2))
      (is (empty? (d/get-deltas dm2))))))

(deftest test-deltaable-map-nested
  (testing "Shallow wrapping: only top-level keys are tracked"
    (let [dm (d/deltaable-map {:data [1 2 3]})
          dm2 (assoc-in dm [:data 0] 10)]
      (is (= {:data [10 2 3]} @dm2))
      (let [deltas (d/get-deltas dm2)]
        (is (= 1 (count deltas)))
        (is (= :update (:delta (first deltas))))
        ;; Only top-level path [:data], not [:data 0]
        (is (= [:data] (:path (first deltas))))
        ;; Value is the entire updated vector
        (is (= [10 2 3] (:value (first deltas)))))))

  (testing "Nested maps track only top-level keys"
    (let [dm (d/deltaable-map {:config {:a 1 :b 2}})
          dm2 (assoc-in dm [:config :a] 10)]
      ;; Use unwrap-deltaable for comparison with plain collections
      (is (= {:config {:a 10 :b 2}} (d/unwrap-deltaable dm2)))
      (let [deltas (d/get-deltas dm2)]
        (is (= 1 (count deltas)))
        (is (= :update (:delta (first deltas))))
        ;; Only top-level path [:config], not [:config :a]
        (is (= [:config] (:path (first deltas))))
        ;; Value is the entire updated map
        (is (= {:a 10 :b 2} (:value (first deltas)))))))

  (testing "Complex nested structure tracks top-level only"
    (let [dm (d/deltaable-map {:users [{:name "Alice" :age 30}
                                        {:name "Bob" :age 25}]})
          dm2 (assoc-in dm [:users 1 :age] 26)]
      ;; Use unwrap-deltaable for comparison with plain collections
      (is (= {:users [{:name "Alice" :age 30}
                      {:name "Bob" :age 26}]}
             (d/unwrap-deltaable dm2)))
      (let [deltas (d/get-deltas dm2)]
        (is (= 1 (count deltas)))
        (is (= :update (:delta (first deltas))))
        ;; Only top-level path [:users], not [:users 1 :age]
        (is (= [:users] (:path (first deltas))))
        ;; Value is the entire updated vector
        (is (= [{:name "Alice" :age 30}
                {:name "Bob" :age 26}]
               (:value (first deltas))))))))

(deftest test-deltaable-map-equality
  (testing "DeltaableMap converts to plain map with ->plain"
    (let [dm (d/deltaable-map {:a 1 :b 2})]
      (is (= {:a 1 :b 2} (d/unwrap-deltaable dm)))
      ;; CLJ: DeltaableMaps only equal other DeltaableMaps, not plain maps
      ;; CLJS: IEquiv makes them equal to plain maps for collection compatibility
      #?(:clj (is (not= dm {:a 1 :b 2})))))

  (testing "DeltaableMap equals other DeltaableMap"
    (let [dm1 (d/deltaable-map {:a 1 :b 2})
          dm2 (d/deltaable-map {:a 1 :b 2})]
      (is (= dm1 dm2)))))

(deftest test-deltaable-map-lookup
  (testing "Lookup with keyword"
    (let [dm (d/deltaable-map {:a 1 :b 2})]
      (is (= 1 (:a dm)))
      (is (= 2 (:b dm)))
      (is (nil? (:c dm)))))

  (testing "Lookup with get"
    (let [dm (d/deltaable-map {:a 1 :b 2})]
      (is (= 1 (get dm :a)))
      (is (= :not-found (get dm :c :not-found)))))

  (testing "Map as function"
    (let [dm (d/deltaable-map {:a 1 :b 2})]
      (is (= 1 (dm :a)))
      (is (= :default (dm :c :default))))))

;; =============================================================================
;; DeltaableSet Tests
;; =============================================================================

(deftest test-deltaable-set-creation
  (testing "Create empty DeltaableSet"
    (let [ds (d/deltaable-set #{})]
      (is (= 0 (count ds)))
      (is (= #{} @ds))
      (is (empty? (d/get-deltas ds)))))

  (testing "Create DeltaableSet with initial values"
    (let [ds (d/deltaable-set #{1 2 3})]
      (is (= 3 (count ds)))
      (is (contains? ds 1))
      (is (contains? ds 2))
      (is (contains? ds 3))
      (is (= #{1 2 3} @ds))
      (is (empty? (d/get-deltas ds)))))

  (testing "DeltaableSet preserves metadata"
    (let [ds (with-meta (d/deltaable-set #{1}) {:foo :bar})]
      (is (= {:foo :bar} (meta ds))))))

(deftest test-deltaable-set-conj
  (testing "Conj new element generates :add delta"
    (let [ds (d/deltaable-set #{1 2})
          ds2 (conj ds 3)]
      (is (= 3 (count ds2)))
      (is (= #{1 2 3} @ds2))
      (let [deltas (d/get-deltas ds2)]
        (is (= 1 (count deltas)))
        (is (= :add (:delta (first deltas))))
        (is (= [3] (:path (first deltas))))
        (is (= 3 (:value (first deltas)))))))

  (testing "Conj existing element has no effect"
    (let [ds (d/deltaable-set #{1 2})
          ds2 (conj ds 1)]
      (is (= ds ds2))
      (is (empty? (d/get-deltas ds2)))))

  (testing "Multiple conjs accumulate deltas"
    (let [ds (-> (d/deltaable-set #{1})
                 (conj 2)
                 (conj 3))]
      (is (= #{1 2 3} @ds))
      (let [deltas (d/get-deltas ds)]
        (is (= 2 (count deltas)))
        (is (every? #(= :add (:delta %)) deltas))))))

(deftest test-deltaable-set-disj
  (testing "Disj generates :remove delta"
    (let [ds (d/deltaable-set #{1 2 3})
          ds2 (disj ds 2)]
      (is (= 2 (count ds2)))
      (is (= #{1 3} @ds2))
      (let [deltas (d/get-deltas ds2)]
        (is (= 1 (count deltas)))
        (is (= :remove (:delta (first deltas))))
        (is (= [2] (:path (first deltas))))
        (is (= 2 (:old-value (first deltas)))))))

  (testing "Disj non-existent element has no effect"
    (let [ds (d/deltaable-set #{1 2})
          ds2 (disj ds 3)]
      (is (= ds ds2))
      (is (empty? (d/get-deltas ds2))))))

(deftest test-deltaable-set-nested
  (testing "Nested vectors in set are wrapped"
    (let [ds (d/deltaable-set #{[1 2] [3 4]})]
      ;; Verify sets contain vectors
      (is (= 2 (count ds)))
      ;; Note: Can't modify nested collections in sets easily
      ;; because sets use value equality for contains?
      (is (= #{[1 2] [3 4]} (d/unwrap-deltaable ds)))))

  (testing "Sets can contain maps"
    (let [ds (d/deltaable-set #{{:id 1} {:id 2}})]
      (is (= 2 (count ds)))
      (is (= #{{:id 1} {:id 2}} (d/unwrap-deltaable ds))))))

(deftest test-deltaable-set-equality
  (testing "DeltaableSet converts to plain set with ->plain"
    (let [ds (d/deltaable-set #{1 2 3})]
      (is (= #{1 2 3} (d/unwrap-deltaable ds)))
      ;; CLJ: DeltaableSets only equal other DeltaableSets, not plain sets
      ;; CLJS: IEquiv makes them equal to plain sets for collection compatibility
      #?(:clj (is (not= ds #{1 2 3})))))

  (testing "DeltaableSet equals other DeltaableSet"
    (let [ds1 (d/deltaable-set #{1 2 3})
          ds2 (d/deltaable-set #{1 2 3})]
      (is (= ds1 ds2)))))

(deftest test-deltaable-set-lookup
  (testing "Lookup with contains?"
    (let [ds (d/deltaable-set #{1 2 3})]
      (is (contains? ds 1))
      (is (contains? ds 2))
      (is (not (contains? ds 4)))))

  (testing "Lookup with get"
    (let [ds (d/deltaable-set #{1 2 3})]
      (is (= 1 (get ds 1)))
      (is (nil? (get ds 4)))))

  (testing "Set as function"
    (let [ds (d/deltaable-set #{1 2 3})]
      (is (= 1 (ds 1)))
      (is (nil? (ds 4))))))

;; =============================================================================
;; Mixed Nested Collections Tests
;; =============================================================================

(deftest test-mixed-nested-collections
  (testing "Vector containing map and set: shallow wrapping tracks top-level only"
    (let [dv (d/deltaable-vector [{:id 1} #{:a :b}])
          dv2 (assoc-in dv [0 :id] 10)]
      (is (= [{:id 10} #{:a :b}] (d/unwrap-deltaable dv2)))
      (let [deltas (d/get-deltas dv2)]
        (is (= 1 (count deltas)))
        ;; Only top-level index [0] is tracked, not nested :id key
        (is (= [0] (:path (first deltas)))))))

  (testing "Map containing vector and set: shallow wrapping tracks top-level only"
    (let [dm (d/deltaable-map {:list [1 2] :tags #{:a :b}})
          dm2 (assoc-in dm [:list 0] 10)]
      (is (= {:list [10 2] :tags #{:a :b}} (d/unwrap-deltaable dm2)))
      (let [deltas (d/get-deltas dm2)]
        (is (= 1 (count deltas)))
        ;; Only top-level key [:list] is tracked, not nested index
        (is (= [:list] (:path (first deltas)))))))

  (testing "Complex nested structure: shallow wrapping tracks top-level keys only"
    (let [data {:users [{:id 1 :tags #{:admin :user}}
                        {:id 2 :tags #{:user}}]
                :config {:settings {:theme "dark"}}}
          dd (d/deltaable-map data)
          dd2 (-> dd
                  (update-in [:users 0 :tags] conj :moderator)
                  (assoc-in [:config :settings :theme] "light"))]
      (is (= {:users [{:id 1 :tags #{:admin :user :moderator}}
                      {:id 2 :tags #{:user}}]
              :config {:settings {:theme "light"}}}
             (d/unwrap-deltaable dd2)))
      (let [deltas (d/get-deltas dd2)]
        (is (= 2 (count deltas)))
        ;; Two top-level key deltas: [:users] and [:config]
        (is (some #(= [:users] (:path %)) deltas))
        (is (some #(= [:config] (:path %)) deltas))))))
