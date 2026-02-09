(ns org.replikativ.spindel.spin.mailbox-test
  "Tests for mailbox synchronization primitive"
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing use-fixtures]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.impl.atoms]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; CLJ-only fixture
#?(:clj
   (use-fixtures :each
     (fn [f]
       (let [ctx (ctx/create-execution-context)]
         (try
           (binding [rtc/*execution-context* ctx]
             (f))
           (finally
             (ctx/stop-context! ctx)))))))

;; =============================================================================
;; Cross-platform tests (async pattern)
;; =============================================================================

(deftest test-mailbox-post-returns-nil
  (testing "Posting to mailbox returns nil (like core.async put!)"
    (async done
      (with-ctx [_ctx]
        (let [mbx (sync/mailbox)
              result (mbx :msg)]
          (is (nil? result) "Post should return nil")
          (done))))))

(deftest test-mailbox-fifo-order
  (testing "Messages are consumed in FIFO order"
    (async done
      (with-ctx [_ctx]
        (let [mbx (sync/mailbox)]
          ;; Post three messages
          (mbx :first)
          (mbx :second)
          (mbx :third)

          ;; Consume them
          (let [consumer (spin
                           [(await mbx)
                            (await mbx)
                            (await mbx)])]
            (run-spin! consumer
                       (fn [result]
                         (is (= [:first :second :third] result) "Should consume in FIFO order")
                         (done))
                       (fn [err]
                         (is false (str "Spin failed: " err))
                         (done)))))))))

(deftest test-mailbox-blocking-take
  (testing "Taking from empty mailbox blocks until message available"
    (async done
      (with-ctx [_ctx]
        (let [mbx (sync/mailbox)
              results (atom [])]

          ;; Start consumer (will block)
          (let [consumer (spin
                           (let [msg (await mbx)]
                             (swap! results conj :consumed)
                             msg))]

            ;; Consumer is waiting, post message
            (mbx :delivered)

            ;; Consumer should wake up
            (run-spin! consumer
                       (fn [result]
                         (is (= :delivered result) "Consumer should get message")
                         (is (= [:consumed] @results) "Consumer should have run")
                         (done))
                       (fn [err]
                         (is false (str "Spin failed: " err))
                         (done)))))))))

(deftest test-mailbox-multiple-consumers
  (testing "Each message goes to exactly one consumer (not broadcast)"
    (async done
      (with-ctx [_ctx]
        (let [mbx (sync/mailbox)
              results (atom [])]

          ;; Post two messages
          (mbx :msg1)
          (mbx :msg2)

          ;; Two consumers compete
          (let [consumer1 (spin (await mbx))
                consumer2 (spin (await mbx))]

            (run-spin! consumer1
                       (fn [result1]
                         (swap! results conj result1)
                         (run-spin! consumer2
                                    (fn [result2]
                                      (swap! results conj result2)
                                      ;; Each consumer should get one message
                                      (is (= 2 (count @results)) "Both consumers should get a message")
                                      (is (contains? (set @results) :msg1) "msg1 should be consumed")
                                      (is (contains? (set @results) :msg2) "msg2 should be consumed")
                                      (done))
                                    (fn [err]
                                      (is false (str "Consumer2 failed: " err))
                                      (done))))
                       (fn [err]
                         (is false (str "Consumer1 failed: " err))
                         (done)))))))))

(deftest test-mailbox-producer-consumer-pattern
  (testing "Producer-consumer pattern works correctly"
    (async done
      (with-ctx [_ctx]
        (let [mbx (sync/mailbox)
              consumed (atom [])]

          ;; Consumer loop
          (let [consumer (spin
                           (loop [count 3]
                             (when (pos? count)
                               (let [msg (await mbx)]
                                 (swap! consumed conj msg)
                                 (recur (dec count)))))
                           @consumed)]

            ;; Producer posts messages
            (mbx :a)
            (mbx :b)
            (mbx :c)

            ;; Consumer should get all three
            (run-spin! consumer
                       (fn [result]
                         (is (= [:a :b :c] result) "Should consume all messages in order")
                         (done))
                       (fn [err]
                         (is false (str "Consumer failed: " err))
                         (done)))))))))

;; =============================================================================
;; CLJ-only tests: require Thread/sleep, future
;; =============================================================================

#?(:clj
   (deftest test-mailbox-external-post
     (testing "External post! from future works correctly"
       (binding [rtc/*execution-context* (ctx/create-execution-context)]
         (let [mbx (sync/mailbox)
               result-promise (promise)]

           ;; Start consumer
           (future
             (binding [rtc/*execution-context* (rtc/current-execution-context)]
               (let [msg @(spin (await mbx))]
                 (deliver result-promise msg))))

           ;; Give consumer time to block
           (Thread/sleep 10)

           ;; Post from external context
           (sync/post! mbx :external-msg)

           ;; Consumer should wake up
           (is (= :external-msg (deref result-promise 1000 :timeout))
               "Consumer should receive externally posted message"))))))

#?(:clj
   (deftest test-mailbox-queue-buildup
     (testing "Messages queue up when no consumers"
       (binding [rtc/*execution-context* (ctx/create-execution-context)]
         (let [mbx (sync/mailbox)]

           ;; Post many messages with no consumers
           (dotimes [i 10]
             (mbx i))

           ;; Now consume them all
           (let [results (atom [])]
             (dotimes [_ 10]
               (swap! results conj @(spin (await mbx))))

             (is (= (range 10) @results) "Should consume all queued messages in order")))))))

#?(:clj
   (deftest test-mailbox-multiple-producers
     (testing "Multiple producers posting concurrently"
       (binding [rtc/*execution-context* (ctx/create-execution-context)]
         (let [mbx (sync/mailbox)
               n-messages 100
               results (atom [])]

           ;; Multiple producers
           (let [producers (doall
                             (for [i (range 10)]
                               (future
                                 (binding [rtc/*execution-context* (rtc/current-execution-context)]
                                   (dotimes [j 10]
                                     (mbx [i j]))))))]

             ;; Wait for all producers
             (doseq [f producers] @f)

             ;; Consume all messages
             (dotimes [_ n-messages]
               (swap! results conj @(spin (await mbx))))

             (is (= n-messages (count @results)) "Should consume all posted messages")
             (is (= n-messages (count (distinct @results))) "All messages should be unique")))))))

#?(:clj
   (deftest test-mailbox-rendezvous-pattern
     (testing "Rendezvous: producer waits for consumer"
       (binding [rtc/*execution-context* (ctx/create-execution-context)]
         (let [mbx (sync/mailbox)
               consumer-ready (promise)
               message-received (promise)]

           ;; Consumer waits
           (future
             (binding [rtc/*execution-context* (rtc/current-execution-context)]
               (deliver consumer-ready :ready)
               (let [msg @(spin (await mbx))]
                 (deliver message-received msg))))

           ;; Wait for consumer to be waiting
           (is (= :ready (deref consumer-ready 1000 :timeout)))
           (Thread/sleep 10)

           ;; Producer posts
           (mbx :rendezvous-msg)

           ;; Consumer should get it
           (is (= :rendezvous-msg (deref message-received 1000 :timeout))
               "Consumer should receive message in rendezvous"))))))
