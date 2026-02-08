(ns org.replikativ.spindel.pubsub.mult-test
  "Tests for pub/sub mult (fan-out) implementation."
  (:require #?(:clj [clojure.test :refer [deftest is testing use-fixtures]]
               :cljs [cljs.test :refer [deftest is testing] :include-macros true])
            [org.replikativ.spindel.pubsub.mult :as mult]
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

(deftest test-mult-lazy-pump-start
  (testing "pump doesn't start until first tap"
    (let [source (vec->aseq [1 2 3])
          m (mult/mult source)]

      ;; No pump yet
      (is (nil? (mult/mult-pump m)))
      (is (not @(:pump-started-atom m)))

      ;; Create tap - pump should start
      (let [_ (mult/tap m (buf/fixed-buffer 10))]
        (is (some? (mult/mult-pump m)))
        (is @(:pump-started-atom m))))))

(deftest test-mult-untap
  (testing "untap removes tap from mult"
    (let [source (vec->aseq [1 2 3])
          m (mult/mult source)
          t (mult/tap m (buf/fixed-buffer 10))]

      ;; Untap
      (mult/untap m t)

      ;; Tap should be closed
      (is (mult/tap-closed? t)))))

;; =============================================================================
;; CLJ-only tests: require blocking deref (@)
;; =============================================================================

#?(:clj
   (deftest test-mult-single-tap-basic
     (testing "single tap receives all items from source"
       (let [source (vec->aseq [1 2 3])
             m (mult/mult source)
             t (mult/tap m (buf/fixed-buffer 10))]

         ;; Consume all items
         (let [result @(spin
                         (loop [seq t
                                acc []]
                           (if-let [[item rest-seq] (await (anext seq))]
                             (recur rest-seq (conj acc item))
                             acc)))]
           (is (= [1 2 3] result)))))))

#?(:clj
   (deftest test-mult-multiple-taps-basic
     (testing "multiple taps each receive all items"
       (let [source (vec->aseq [1 2 3])
             m (mult/mult source)
             t1 (mult/tap m (buf/fixed-buffer 10))
             t2 (mult/tap m (buf/fixed-buffer 10))]

         ;; Both taps should receive all items
         (let [result1 @(spin
                          (loop [seq t1
                                 acc []]
                            (if-let [[item rest-seq] (await (anext seq))]
                              (recur rest-seq (conj acc item))
                              acc)))
               result2 @(spin
                          (loop [seq t2
                                 acc []]
                            (if-let [[item rest-seq] (await (anext seq))]
                              (recur rest-seq (conj acc item))
                              acc)))]
           (is (= [1 2 3] result1))
           (is (= [1 2 3] result2)))))))

#?(:clj
   (deftest test-mult-closed-detection
     (testing "mult detects when source is exhausted"
       (let [source (vec->aseq [1 2])
             m (mult/mult source)
             t (mult/tap m (buf/fixed-buffer 10))]

         ;; Consume all items and give pump time to detect exhaustion
         @(spin
            (loop [seq t]
              (when-let [[_ rest-seq] (await (anext seq))]
                (recur rest-seq)))
            ;; Give pump time to detect exhaustion via async delay
            (await (comb/sleep 50)))

         ;; Now should be closed
         (is (mult/mult-closed? m))))))

#?(:clj
   (deftest test-mult-tap-with-fixed-buffer
     (testing "tap with fixed buffer"
       (let [source (vec->aseq (range 5))
             m (mult/mult source)
             t (mult/tap m (buf/fixed-buffer 3))]

         (let [result @(spin
                         (loop [seq t
                                acc []]
                           (if-let [[item rest-seq] (await (anext seq))]
                             (recur rest-seq (conj acc item))
                             acc)))]
           (is (= [0 1 2 3 4] result)))))))

#?(:clj
   (deftest test-mult-tap-with-dropping-buffer
     (testing "tap with dropping buffer drops newest when full"
       (let [source (vec->aseq (range 5))
             m (mult/mult source)
             t (mult/tap m (buf/dropping-buffer 3))]

         (let [result @(spin
                         (loop [seq t
                                acc []]
                           (if-let [[item rest-seq] (await (anext seq))]
                             (recur rest-seq (conj acc item))
                             acc)))]
           ;; Dropping buffer may drop items if pump runs faster than consumption
           ;; With buffer size 3, we expect to get the first items that fit
           ;; The exact count depends on timing, but we should get at least buffer-size items
           (is (>= (count result) 3) "Should get at least buffer-size items")
           (is (<= (count result) 5) "Should not get more than source items")
           (is (= (first result) 0) "First item should be 0"))))))

#?(:clj
   (deftest test-mult-tap-with-sliding-buffer
     (testing "tap with sliding buffer keeps newest items"
       (let [source (vec->aseq (range 5))
             m (mult/mult source)
             t (mult/tap m (buf/sliding-buffer 3))]

         (let [result @(spin
                         (loop [seq t
                                acc []]
                           (if-let [[item rest-seq] (await (anext seq))]
                             (recur rest-seq (conj acc item))
                             acc)))]
           ;; Sliding buffer may drop oldest items if pump runs faster than consumption
           ;; With buffer size 3, we expect to get the most recent items
           ;; The exact count depends on timing
           (is (>= (count result) 3) "Should get at least buffer-size items")
           (is (<= (count result) 5) "Should not get more than source items"))))))

#?(:clj
   (deftest test-mult-untap-drains-buffer
     (testing "untap allows draining remaining buffer items"
       (let [source (vec->aseq (range 10))
             m (mult/mult source)
             t (mult/tap m (buf/fixed-buffer 20))]

         ;; Let pump fill buffer via async delay
         @(spin (await (comb/sleep 100)))

         ;; Untap while buffer has items
         (mult/untap m t)

         ;; Should still be able to drain buffer
         (let [result @(spin
                         (loop [seq t
                                acc []]
                           (if-let [[item rest-seq] (await (anext seq))]
                             (recur rest-seq (conj acc item))
                             acc)))]
           ;; Should get all items that were buffered
           (is (seq result) "Should drain at least some items")
           (is (= (first result) 0) "First item should be 0"))))))
;; =============================================================================
;; Pump Execution Tests (verifies event-based pump fix)
;; =============================================================================

#?(:clj
   (deftest test-mult-pump-execution-context
     (testing "pump executes with correct execution context"
       (let [source (vec->aseq [1 2 3])
             m (mult/mult source)
             t (mult/tap m (buf/fixed-buffer 10))]

         ;; Consume items - this forces pump to execute
         (let [result @(spin
                         (loop [seq t
                                acc []]
                           (if-let [[item rest-seq] (await (anext seq))]
                             (recur rest-seq (conj acc item))
                             acc)))]

           ;; Pump should have delivered all items successfully
           ;; (verifying event-based execution works correctly)
           (is (= [1 2 3] result) "Pump should deliver all items via event-based execution"))))))
