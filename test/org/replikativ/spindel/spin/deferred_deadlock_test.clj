(ns org.replikativ.spindel.spin.deferred-deadlock-test
  "Minimal test to reproduce deferred deadlock issue"
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.scheduler :as sched]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [is.simm.partial-cps.async]))

(use-fixtures :each
  (fn [f]
    (let [execution-ctx (ctx/create-execution-context {:executor (sched/thread-pool-executor 4)})]
      (binding [rtc/*execution-context* execution-ctx]
        (f)))))

(deftest test-deferred-self-delivery
  (testing "Deferred delivered from within same spin that awaits it - DEADLOCK?"
    (let [test-spin (spin
                     (let [d (sync/deferred)
                           ;; Set up delivery that happens "later" in CPS execution
                           _ (future
                               (Thread/sleep 100)
                               (sync/deliver! d 42))
                           result (await d)]
                       result))
          result @test-spin]
      (is (= 42 result) "Should receive delivered value"))))

(deftest test-deferred-same-spin-cps-delivery
  (testing "Deferred delivered from CPS continuation within same spin - TRUE DEADLOCK"
    (let [test-spin (spin
                     (let [d (sync/deferred)
                           ;; Simulate what happens when external code delivers:
                           ;; Start async operation that will deliver from external thread
                           _ (future
                               (Thread/sleep 100)
                               ;; Use deliver! for external delivery (CORRECT way)
                               (sync/deliver! d 99))
                           ;; Await the deferred (like anext does)
                           result (await d)]
                       result))
          result @test-spin]
      (is (= 99 result) "Should receive delivered value"))))

(deftest test-deferred-inline-delivery-attempt
  (testing "Most direct reproduction: deliver immediately after starting await"
    (let [test-spin (spin
                     (let [d (sync/deferred)
                           ;; Deliver in a future to avoid blocking
                           delivery-future (future
                                             (Thread/sleep 50)
                                             (sync/deliver! d :delivered-value))
                           result (await d)]
                       ;; NOTE: We don't wait for delivery-future because with ImmediateExecutor,
                       ;; that would create a circular wait (future waiting for itself).
                       ;; The delivery-future will complete on its own after deliver! returns.
                       result))
          result @test-spin]
      (is (= :delivered-value result)))))

(deftest test-deferred-synchronous-cps-delivery
  (testing "TRUE REPRODUCTION: Deliver synchronously within CPS execution (like aseq)"
    (let [test-spin (spin
                     (let [d (sync/deferred)
                           ;; Create a nested CPS function that will deliver
                           ;; This mimics what happens in aseq: cps-fn calls yield-handler calls resolve-fn
                           inner-cps-fn (fn [resolve-callback _reject-callback]
                                          ;; Simulate async-fetch completing
                                          (resolve-callback :inner-result)
                                          :org.replikativ.spindel.spin/incomplete)
                           ;; Resolve callback that delivers to deferred
                           resolve-callback (fn [value]
                                              (d value))
                           ;; Execute inner CPS (like calling cps-fn in anext)
                           cps-result (inner-cps-fn resolve-callback identity)
                           ;; Now await the deferred (like anext does)
                           result (await d)]
                       result))
          result @test-spin]
      (is (= :inner-result result)))))
