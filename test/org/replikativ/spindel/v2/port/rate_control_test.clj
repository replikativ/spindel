(ns org.replikativ.spindel.v2.port.rate-control-test
  "Port of spin/rate_control_test.cljc to v2 (M6 phase A)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin]]
            [org.replikativ.spindel.v2.combinators :refer [debounce throttle sample relieve timeout sleep accumulate]]
            [org.replikativ.spindel.incremental.interval :as iv]))

(use-fixtures :each (fn [f] (binding [v2/*world* (v2/world)] (f))))

(defn- elapsed-ms [f]
  (let [start (System/currentTimeMillis) v (f)]
    [v (- (System/currentTimeMillis) start)]))

(deftest test-timeout-fast-spin-wins
  (is (= 42 @(timeout (spin 42) 1000 :fallback))))

(deftest test-timeout-fallback-on-slow-spin
  (is (= :fallback @(timeout (sleep 1000 :slow) 50 :fallback))))

(deftest test-sample-returns-value-after-interval
  (let [[v ms] (elapsed-ms #(deref (sample (spin 42) 100)))]
    (is (= 42 v))
    (is (>= ms 90))))

(deftest test-relieve-returns-value
  (is (= :value @(relieve (spin :value))))
  (is (= :immediate @(relieve (spin :immediate)))))

(deftest test-debounce-delays-value
  (let [[v ms] (elapsed-ms #(deref (debounce (spin :debounced) 100)))]
    (is (= :debounced v))
    (is (>= ms 90))))

(deftest test-throttle-returns-value-through-merge
  (is (= :value @(throttle (spin :value) 100 (fn [_ new] new))))
  (is (= [:merged 10] @(throttle (spin 10) 100 (fn [_ new] [:merged new]))))
  (let [[v ms] (elapsed-ms #(deref (throttle (spin :throttled) 10 (fn [_ new] new))))]
    (is (= :throttled v))
    (is (>= ms 90) "10 Hz waits ~100ms")))

(deftest test-timeout-with-deferreds
  (let [d (v2/deferred)
        t (timeout d 1000 :fallback)]
    (d :delivered)
    (is (= :delivered @t)))
  (is (= :fallback @(timeout (v2/deferred) 50 :fallback))))

(deftest test-merge-intervals
  ;; engine-independent algebra, unchanged
  (testing "nil accumulator"
    (let [r (iv/merge-intervals nil (iv/->Interval :a :b [{:delta :add :path [0] :value 1}]))]
      (is (= [:a :b 1] [(:old r) (:new r) (count (:deltas r))]))))
  (testing "combines old from acc, new from new"
    (let [r (iv/merge-intervals (iv/->Interval :a :b [{:delta :add :path [0] :value 1}])
                                (iv/->Interval :b :c [{:delta :add :path [1] :value 2}]))]
      (is (= [:a :c 2] [(:old r) (:new r) (count (:deltas r))]))))
  (testing "compacts redundant deltas"
    (let [r (iv/merge-intervals (iv/->Interval nil [1] [{:delta :add :path [0] :value 1}])
                                (iv/->Interval [1] [] [{:delta :remove :path [0] :old-value 1}]))]
      (is (= [nil [] true] [(:old r) (:new r) (empty? (:deltas r))]))))
  (testing "associative"
    (let [a (iv/->Interval nil :a [{:delta :add :path [0] :value 1}])
          b (iv/->Interval :a :b [{:delta :add :path [1] :value 2}])
          c (iv/->Interval :b :c [{:delta :add :path [2] :value 3}])
          l (iv/merge-intervals (iv/merge-intervals a b) c)
          r (iv/merge-intervals a (iv/merge-intervals b c))]
      (is (= [(:old l) (:new l) (count (:deltas l))] [(:old r) (:new r) (count (:deltas r))])))))

(deftest test-accumulate
  (let [sig (v2/signal [1 2 3])
        acc (accumulate sig iv/merge-intervals)]
    (let [r @acc]
      (is (satisfies? iv/PInterval r))
      (is (= [1 2 3] (iv/get-new r)))))
  (let [sig (v2/signal [1 2 3])]
    (swap! sig conj 4)
    (is (= [1 2 3 4] (iv/get-new @(accumulate sig iv/merge-intervals))))))
