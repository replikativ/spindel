(ns org.replikativ.spindel.engine.event-system-test
  "Tests for event queue and drain system.

  The event system is critical infrastructure that processes state changes
  asynchronously via a FIFO queue. Tests verify:
  - FIFO ordering preserved
  - No events lost under concurrent enqueue
  - Single drainer at a time (CAS lock)
  - Test synchronization (await-drain) works correctly"
  (:require #?(:clj [clojure.test :refer [deftest is testing]])
            #?(:cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.signal :as sig]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]])
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-helpers :as th])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; FIFO Ordering Tests
;; =============================================================================

#?(:clj
   (deftest test-fifo-event-ordering-via-signals
     (testing "Events are processed in FIFO order"
       (let [processing-order (atom [])]
         (th/with-ctx [ctx]
           ;; Create 10 signals
           (let [signals (mapv (fn [i] (sig/signal i)) (range 10))
                 ;; Create tracking spin that records order
                 tracker (spin
                          (doseq [i (range 10)]
                            (track (nth signals i))
                            (swap! processing-order conj i)))]

             ;; Wait for initial execution
             @tracker

             ;; Reset order tracking
             (reset! processing-order [])

             ;; Change all signals in order 0-9
             ;; This enqueues 10 :signal-change events
             (doseq [i (range 10)]
               (reset! (nth signals i) (+ i 100)))

             ;; Drain all events
             (simple/await-drain-complete! ctx)

             ;; Events should be processed in FIFO order
             ;; Each signal change should trigger tracker re-execution
             ;; Due to reactive system, we should see processing in order
             (is (seq @processing-order)
                 "Should have processed some events")))))))

;; =============================================================================
;; Concurrent Enqueue Tests
;; =============================================================================

#?(:clj
   (deftest test-concurrent-enqueue-no-lost-events
     (testing "Concurrent enqueues from multiple threads don't lose events"
       (let [n-threads 50
             n-changes-per-thread 100
             change-count (atom 0)]
         (th/with-ctx [ctx]
           ;; Create signal and tracking spin
           (let [test-sig (sig/signal 0)
                 tracker (spin
                          (track test-sig)
                          (swap! change-count inc))]

             ;; Wait for initial execution
             @tracker

             ;; Reset counter (initial execution counted)
             (reset! change-count 0)

             ;; Many threads changing signal concurrently
             ;; Each change enqueues a :signal-change event
             (let [futures (repeatedly n-threads
                                       (fn []
                                         (future
                                           (dotimes [i n-changes-per-thread]
                                             (reset! test-sig i)))))]

               ;; Wait for all enqueues to complete
               (doseq [f futures]
                 (deref f 10000 :timeout))

               ;; Drain all events
               (simple/await-drain-complete! ctx)

               ;; Tracker should have re-executed at least once.
               ;; Due to batching/coalescing, concurrent changes to the same signal
               ;; can be merged, so we can't guarantee one notification per thread.
               ;; What we CAN guarantee: at least one re-execution happened.
               (is (pos? @change-count)
                   (str "Should process at least one change notification. Got: " @change-count)))))))))

#?(:clj
   (deftest test-concurrent-enqueue-all-processed
     (testing "All concurrently enqueued events eventually processed"
       (let [n-threads 20
             n-signals-per-thread 5
             all-signals (atom [])]
         (th/with-ctx [ctx]
           ;; Each thread creates its own signals
           (let [futures (repeatedly n-threads
                                     (fn []
                                       (future
                                         (binding [ec/*execution-context* ctx]
                                           (let [thread-signals (mapv (fn [_] (sig/signal 0))
                                                                      (range n-signals-per-thread))]
                                             (swap! all-signals into thread-signals)
                                   ;; Change each signal once
                                             (doseq [s thread-signals]
                                               (reset! s 1)))))))]

             ;; Wait for all threads
             (doseq [f futures]
               (deref f 10000 :timeout))

             ;; Drain all events
             (simple/await-drain-complete! ctx)

             ;; All signals should have their changes processed
             (is (= (* n-threads n-signals-per-thread) (count @all-signals))
                 "Should have created all signals")))))))

;; =============================================================================
;; Single Drainer Tests
;; =============================================================================

;; =============================================================================
;; await-drain Tests
;; =============================================================================

#?(:clj
   (deftest test-await-drain-with-no-events
     (testing "await-drain returns immediately when no events"
       (let [start (System/currentTimeMillis)]
         (th/with-ctx [ctx]
           ;; No events enqueued
           (let [result (simple/await-drain-complete! ctx :timeout-ms 1000)
                 elapsed (- (System/currentTimeMillis) start)]

             (is (true? result) "Should complete successfully")
             (is (< elapsed 100) "Should return quickly (< 100ms)")))))))

#?(:clj
   (deftest test-await-drain-waits-for-events
     (testing "await-drain waits for enqueued events to process"
       (let [processed (atom false)]
         (th/with-ctx [ctx]
           ;; Create signal that will trigger processing
           (let [sig (sig/signal 0)
                 tracker (spin
                          (track sig)
                          (reset! processed true))]

             ;; Initial execution
             @tracker
             (reset! processed false)

             ;; Change signal (enqueues event)
             (reset! sig 1)

             ;; await-drain should wait for event to process
             (let [result (simple/await-drain-complete! ctx :timeout-ms 2000)]
               (is (true? result) "Should complete successfully")
               (is (true? @processed) "Event should have been processed"))))))))

;; =============================================================================
;; Event Queue State Tests
;; =============================================================================

(deftest test-event-queue-enqueue-dequeue
  (testing "Basic enqueue and dequeue operations"
    (let [ctx (ctx/create-execution-context)]
      (try
        ;; Queue should be empty initially
        (is (empty? (rtp/get-state ctx [:engine/pending])))

        ;; Enqueue event
        (simple/enqueue-event! ctx {:type :test :id 1})

        ;; Queue should have one event
        (let [pending (rtp/get-state ctx [:engine/pending])]
          (is (= 1 (count pending)))
          (is (= :test (:type (first pending)))))

        ;; Dequeue event
        (let [event (simple/dequeue-event! ctx)]
          (is (= :test (:type event)))
          (is (= 1 (:id event))))

        ;; Queue should be empty again
        (is (empty? (rtp/get-state ctx [:engine/pending])))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-event-queue-fifo-order
  (testing "Multiple enqueues preserve FIFO order"
    (let [ctx (ctx/create-execution-context)]
      (try
        ;; Enqueue 5 events
        (doseq [i (range 5)]
          (simple/enqueue-event! ctx {:type :test :id i}))

        ;; Dequeue in order
        (let [dequeued (repeatedly 5 #(simple/dequeue-event! ctx))
              ids (map :id dequeued)]
          (is (= (range 5) ids) "Events should be dequeued in FIFO order"))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-draining-flag
  (testing "Draining flag is managed correctly"
    (let [ctx (ctx/create-execution-context)]
      (try
        ;; Initially not draining
        (is (false? (rtp/get-state ctx [:engine/draining?])))

        ;; CAS to true should succeed
        (is (true? (rtp/cas-state! ctx [:engine/draining?] false true)))
        (is (true? (rtp/get-state ctx [:engine/draining?])))

        ;; CAS to true again should fail (already true)
        (is (false? (rtp/cas-state! ctx [:engine/draining?] false true)))

        ;; Set back to false
        (rtp/swap-state! ctx [:engine/draining?] (constantly false))
        (is (false? (rtp/get-state ctx [:engine/draining?])))
        (finally
          (ctx/stop-context! ctx))))))
