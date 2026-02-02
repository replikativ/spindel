(ns org.replikativ.spindel.pubsub.pub-test
  "Tests for pub/sub pub (topic-routing) implementation."
  (:require #?(:clj [clojure.test :refer [deftest is testing use-fixtures]]
               :cljs [cljs.test :refer [deftest is testing] :include-macros true])
            [org.replikativ.spindel.pubsub.pub :as pub]
            [org.replikativ.spindel.pubsub.buffer :as buf]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.impl.atoms]  ; Register :atoms impl
            [is.simm.partial-cps.sequence :refer [PAsyncSeq anext]]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]])
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.test-helpers :as th])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [cljs.test :refer [use-fixtures]]
                            [org.replikativ.spindel.test-helpers :refer [async with-ctx]])))

;; =============================================================================
;; Test Fixtures
;; =============================================================================

(def ^:dynamic *test-runtime* nil)

(defn with-execution-context [f]
  (let [ctx (ctx/create-execution-context)]
    (binding [*test-runtime* ctx
              rtc/*execution-context* ctx]
      (f))))

(use-fixtures :each with-execution-context)

;; =============================================================================
;; Helper: Simple vector-based async sequence
;; =============================================================================

(deftype VectorSeq [items-atom idx]
  PAsyncSeq
  (anext [_]
    (spin
      (let [items @items-atom]
        (when (< idx (count items))
          [(nth items idx) (VectorSeq. items-atom (inc idx))])))))

(defn vec->aseq
  "Create an async sequence from a vector."
  [v]
  (VectorSeq. (atom v) 0))

;; =============================================================================
;; Cross-Platform Tests (no blocking deref)
;; =============================================================================

(deftest test-pub-initially-not-closed
  (testing "pub starts not closed"
    (let [source (vec->aseq [{:type :a :value 1}])
          p (pub/pub source :type)]
      (is (not (pub/pub-closed? p))))))

;; =============================================================================
;; CLJ-only tests: require blocking deref (@)
;; =============================================================================

#?(:clj
   (deftest test-pub-single-topic
     (testing "pub routes items to correct topic"
       (let [items [{:type :a :value 1}
                    {:type :a :value 2}
                    {:type :b :value 3}
                    {:type :a :value 4}]
             source (vec->aseq items)
             p (pub/pub source :type)
             sub-a (pub/sub p :a (buf/fixed-buffer 10))]

         ;; Let pump run via async delay
         @(spin (await (comb/sleep 200)))

         ;; Should get only :a items
         (let [result @(spin
                         (loop [seq sub-a
                                acc []]
                           (if-let [[item rest-seq] (await (anext seq))]
                             (recur rest-seq (conj acc item))
                             acc)))]
           (is (= 3 (count result)))
           (is (every? #(= :a (:type %)) result)))))))

#?(:clj
   (deftest test-pub-multiple-topics
     (testing "pub routes to multiple topics independently"
       (let [items [{:type :a :value 1}
                    {:type :b :value 2}
                    {:type :a :value 3}
                    {:type :b :value 4}]
             source (vec->aseq items)
             p (pub/pub source :type)
             sub-a (pub/sub p :a (buf/fixed-buffer 10))
             sub-b (pub/sub p :b (buf/fixed-buffer 10))]

         ;; Let pump run via async delay
         @(spin (await (comb/sleep 200)))

         (let [result-a @(spin
                           (loop [seq sub-a
                                  acc []]
                             (if-let [[item rest-seq] (await (anext seq))]
                               (recur rest-seq (conj acc (:value item)))
                               acc)))
               result-b @(spin
                           (loop [seq sub-b
                                  acc []]
                             (if-let [[item rest-seq] (await (anext seq))]
                               (recur rest-seq (conj acc (:value item)))
                               acc)))]
           (is (= [1 3] result-a))
           (is (= [2 4] result-b)))))))

#?(:clj
   (deftest test-pub-unsubscribed-topics-dropped
     (testing "items for unsubscribed topics are dropped"
       (let [items [{:type :a :value 1}
                    {:type :ignored :value 999}
                    {:type :a :value 2}]
             source (vec->aseq items)
             p (pub/pub source :type)
             sub-a (pub/sub p :a (buf/fixed-buffer 10))]

         ;; Let pump run via async delay
         @(spin (await (comb/sleep 200)))

         (let [result @(spin
                         (loop [seq sub-a
                                acc []]
                           (if-let [[item rest-seq] (await (anext seq))]
                             (recur rest-seq (conj acc (:value item)))
                             acc)))]
           ;; Should only have :a items, :ignored items are dropped
           (is (= [1 2] result)))))))

#?(:clj
   (deftest test-pub-closed-detection
     (testing "pub detects when source is exhausted"
       (let [source (vec->aseq [{:type :a :value 1}])
             p (pub/pub source :type)
             _ (pub/sub p :a (buf/fixed-buffer 10))]

         ;; Initially not closed
         (is (not (pub/pub-closed? p)))

         ;; Let pump run to completion via async delay
         @(spin (await (comb/sleep 200)))

         ;; Now should be closed
         (is (pub/pub-closed? p))))))

#?(:clj
   (deftest test-pub-unsub
     (testing "unsub removes subscription and allows buffer drain"
       (let [items (vec (for [i (range 10)]
                          {:type :a :value i}))
             source (vec->aseq items)
             p (pub/pub source :type)
             sub-a (pub/sub p :a (buf/fixed-buffer 20))]

         ;; Let pump fill buffer via async delay
         @(spin (await (comb/sleep 100)))

         ;; Unsub while buffer has items
         (pub/unsub p :a sub-a)

         ;; Should still be able to drain buffer
         (let [result @(spin
                         (loop [seq sub-a
                                acc []]
                           (if-let [[item rest-seq] (await (anext seq))]
                             (recur rest-seq (conj acc (:value item)))
                             acc)))]
           (is (seq result) "Should drain at least some items")
           (is (= (first result) 0) "First item should be 0"))))))
;; =============================================================================
;; Multiple Subscribers Per Topic Tests
;; =============================================================================

#?(:clj
   (deftest test-pub-multiple-subscribers-per-topic
     (testing "multiple subscribers to same topic each receive all items"
       (let [items (vec (for [i (range 5)]
                          {:type :a :value i}))
             source (vec->aseq items)
             p (pub/pub source :type)
             sub1 (pub/sub p :a (buf/fixed-buffer 10))
             sub2 (pub/sub p :a (buf/fixed-buffer 10))]

         ;; Let pump run
         @(spin (await (comb/sleep 200)))

         ;; Consume from both subscribers sequentially
         (let [result1 @(spin
                          (loop [seq sub1 acc []]
                            (if-let [[item rest-seq] (await (anext seq))]
                              (recur rest-seq (conj acc (:value item)))
                              acc)))
               result2 @(spin
                          (loop [seq sub2 acc []]
                            (if-let [[item rest-seq] (await (anext seq))]
                              (recur rest-seq (conj acc (:value item)))
                              acc)))]

           ;; Both should get all items (order may vary due to concurrent delivery)
           (is (= 5 (count result1)) "First subscriber should get 5 items")
           (is (= 5 (count result2)) "Second subscriber should get 5 items")
           (is (= (set (range 5)) (set result1)) "First subscriber should get all values")
           (is (= (set (range 5)) (set result2)) "Second subscriber should get all values"))))))
