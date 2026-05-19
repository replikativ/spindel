(ns org.replikativ.spindel.pubsub.mult-test
  "Tests for pub/sub mult (fan-out) implementation."
  (:require #?(:clj [clojure.test :refer [deftest is testing use-fixtures]]
               :cljs [cljs.test :refer [deftest is testing] :include-macros true])
            [org.replikativ.spindel.pubsub.mult :as mult]
            [org.replikativ.spindel.pubsub.buffer :as buf]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [is.simm.partial-cps.sequence :refer [PAsyncSeq anext]]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]])
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.spin.sync :as sync]
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
  (let [c (ctx/create-execution-context)]
    (try
      (binding [*test-runtime* c
                ec/*execution-context* c]
        (f))
      (finally
        (ctx/stop-context! c)))))

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

;; Gated source: emits items from `inner` only after `gate` is delivered.
;; Matches the core.async mult convention of "register all taps BEFORE
;; producing items into the source". `vec->aseq` produces eagerly the
;; instant the pump asks for an item, which races multi-tap setup; the
;; gate lets the test arrange tap registration first, then `deliver!`
;; the gate to release the pump.
(deftype GatedSeq [gate inner]
  PAsyncSeq
  (anext [_]
    (spin
     (await gate)
     (when-let [result (await (anext inner))]
       (let [[item rest-seq] result]
         [item (GatedSeq. gate rest-seq)])))))

(defn gated-vec->aseq
  "Like `vec->aseq` but no items are emitted until `gate` (a Deferred)
   is delivered. Use this in multi-tap tests so taps register before
   the pump can advance."
  [gate v]
  (GatedSeq. gate (vec->aseq v)))

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
     (testing "multiple taps each receive all items when registered before source produces"
       ;; This test reproduces a real race that exists in any mult-style
       ;; primitive (core.async included): if the source produces items
       ;; before all taps are registered, late-registered taps miss the
       ;; early items. core.async documents this as "items received when
       ;; there are no taps get dropped"; our mult is slightly more
       ;; forgiving (lazy pump on first tap) but still races between the
       ;; first tap and any subsequent ones if the source has items
       ;; ready immediately.
       ;;
       ;; The standard fix is to gate the source so it can't produce
       ;; until all taps are registered. Here we use a Deferred as that
       ;; gate.
       (let [gate    (sync/deferred)
             source  (gated-vec->aseq gate [1 2 3])
             m       (mult/mult source)
             t1      (mult/tap m (buf/fixed-buffer 10))
             t2      (mult/tap m (buf/fixed-buffer 10))
             ;; Both taps registered — release the pump.
             _       (sync/deliver! gate :go)
             result1 @(spin
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
         (is (= [1 2 3] result2))))))

;; Slowing aseq: forces the pump to take measurable time per pull so a
;; multi-threaded test can deterministically time interventions relative
;; to the pump's progress. Each anext suspends for `delay-ms` before
;; emitting the next item from `inner`.
(deftype SleepingSeq [delay-ms inner]
  PAsyncSeq
  (anext [_]
    (spin
     (await (comb/sleep delay-ms))
     (when-let [result (await (anext inner))]
       (let [[item rest-seq] result]
         [item (SleepingSeq. delay-ms rest-seq)])))))

(defn sleeping-vec->aseq
  "Like `vec->aseq` but each pull takes `delay-ms` of wall-clock time."
  [delay-ms v]
  (SleepingSeq. delay-ms (vec->aseq v)))

#?(:clj
   (deftest test-mult-untap-during-backpressure-no-jam
     (testing "untap of a backpressuring tap wakes the pump (regression)"
       ;; Pre-fix bug: when the pump was blocked on a full tap's
       ;; `space-available-atom`, `close-tap!` only signaled the
       ;; consumer-side `item-available` waiter — the producer-side
       ;; waiter never woke and the pump jammed for all OTHER taps.
       ;;
       ;; Fix: `close-tap!` also signals `space-available!`, and the
       ;; pump rechecks `:closed?` after the await before adding to
       ;; the buffer.
       (let [;; 30ms per pull. Item 0 arrives at ~t=30; pump enters
             ;; await-on-t1-space-available at ~t=60.
             source (sleeping-vec->aseq 30 (vec (range 10)))
             m      (mult/mult source)
             t1     (mult/tap m (buf/fixed-buffer 1))    ; small → backpressure
             t2     (mult/tap m (buf/fixed-buffer 100))
             ;; Drain t2 in a parallel spin so its consumption doesn't
             ;; race-fill back the producer-side wait we want to observe.
             drain  (spin
                     (loop [seq t2 acc []]
                       (if-let [[item rest-seq] (await (anext seq))]
                         (recur rest-seq (conj acc item))
                         acc)))]
         ;; Give the pump time to deliver item 0 and enter the await
         ;; for item 1 on t1's full buffer.
         (Thread/sleep 100)
         ;; The fix's job: this untap must wake the pump.
         (mult/untap m t1)
         ;; Without the fix this drain hangs forever; with the fix the
         ;; pump skips t1 (closed) and continues delivering to t2.
         (let [result @(comb/timeout drain 3000 ::timeout)]
           (is (not= ::timeout result)
               "Pump must not jam when a backpressuring tap is untapped")
           (is (= 10 (count result))
               (str "t2 should receive all 10 items, got " (count result))))))))

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
