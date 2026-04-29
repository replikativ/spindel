(ns org.replikativ.spindel.spin.parallel-test
  "Tests for parallel combinator"
  (:refer-clojure :exclude [await])
  #?(:clj
     (:require [clojure.test :refer [deftest is testing use-fixtures]]
               [org.replikativ.spindel.engine.core :as ec]
               [org.replikativ.spindel.engine.protocols :as rtp]
               [org.replikativ.spindel.engine.executor :as sched]
               [org.replikativ.spindel.engine.context :as ctx]
               [org.replikativ.spindel.spin.sync :as sync]
               [org.replikativ.spindel.spin.core :as spin-core]
               [org.replikativ.spindel.spin.combinators :refer [parallel]]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.effects.await :refer [await]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
               [org.replikativ.spindel.test-helpers.async-stub :as async-stub]
               [is.simm.partial-cps.async :as pcps-async])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]]
               [org.replikativ.spindel.engine.core :as ec]
               [org.replikativ.spindel.engine.context :as ctx]
               [org.replikativ.spindel.spin.sync :as sync]
               [org.replikativ.spindel.spin.combinators :refer [parallel]]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.effects.await :refer [await]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; CLJ-only fixture
#?(:clj
   (use-fixtures :each
     (fn [f]
       (let [execution-ctx (ctx/create-execution-context {:executor (sched/thread-pool-executor 4)})]
         (try
           (binding [ec/*execution-context* execution-ctx]
             (f))
           (finally
             (ctx/stop-context! execution-ctx)))))))

;; =============================================================================
;; Cross-platform basic parallel tests (async pattern)
;; =============================================================================

(deftest test-parallel-two-immediate-spins
  (testing "Parallel two immediately-completing spins"
    (async done
      (with-ctx [_ctx]
        (let [t1 (spin :a)
              t2 (spin :b)
              par-spin (parallel t1 t2)]
          (run-spin! par-spin
                     (fn [result]
                       (is (= [:a :b] result) "Should combine results in order")
                       (done))
                     (fn [err]
                       (is false (str "Parallel failed: " err))
                       (done))))))))

(deftest test-parallel-three-spins-sum
  (testing "Parallel three spins and sum results"
    (async done
      (with-ctx [_ctx]
        (let [t1 (spin 1)
              t2 (spin 2)
              t3 (spin 3)
              outer-spin (spin
                           (let [results (await (parallel t1 t2 t3))]
                             (apply + results)))]
          (run-spin! outer-spin
                     (fn [result]
                       (is (= 6 result) "Should sum all results")
                       (done))
                     (fn [err]
                       (is false (str "Parallel failed: " err))
                       (done))))))))

(deftest test-parallel-basic
  (testing "Parallel returns vector of results"
    (async done
      (with-ctx [_ctx]
        (let [t1 (spin :first)
              t2 (spin :second)
              t3 (spin :third)
              par-spin (parallel t1 t2 t3)]
          (run-spin! par-spin
                     (fn [result]
                       (is (= [:first :second :third] result) "Should return vector of results")
                       (done))
                     (fn [err]
                       (is false (str "Parallel failed: " err))
                       (done))))))))

(deftest test-await-parallel-in-spin
  (testing "Await parallel inside a spin"
    (async done
      (with-ctx [_ctx]
        (let [outer-spin (spin
                           (let [t1 (spin 10)
                                 t2 (spin 20)
                                 t3 (spin 30)
                                 results (await (parallel t1 t2 t3))]
                             (apply + results)))]
          (run-spin! outer-spin
                     (fn [result]
                       (is (= 60 result) "Should be able to await parallel in spin")
                       (done))
                     (fn [err]
                       (is false (str "Spin failed: " err))
                       (done))))))))

(deftest test-parallel-merge-maps
  (testing "Parallel with merge on results"
    (async done
      (with-ctx [_ctx]
        (let [outer-spin (spin
                           (let [t1 (spin {:a 1})
                                 t2 (spin {:b 2})
                                 results (await (parallel t1 t2))]
                             (apply merge results)))]
          (run-spin! outer-spin
                     (fn [result]
                       (is (= {:a 1 :b 2} result) "Should be able to merge results")
                       (done))
                     (fn [err]
                       (is false (str "Spin failed: " err))
                       (done))))))))

(deftest test-nested-parallel
  (testing "Nested parallel calls"
    (async done
      (with-ctx [_ctx]
        (let [outer-spin (spin
                           (let [inner1 (parallel (spin 1) (spin 2))
                                 inner2 (parallel (spin 3) (spin 4))
                                 outer (await (parallel inner1 inner2))]
                             outer))]
          (run-spin! outer-spin
                     (fn [result]
                       (is (= [[1 2] [3 4]] result) "Should support nested parallel")
                       (done))
                     (fn [err]
                       (is false (str "Spin failed: " err))
                       (done))))))))

;; =============================================================================
;; CLJ-only tests: require Thread/sleep, future, promise, thread-pool-executor
;; =============================================================================

#?(:clj
   (deftest test-parallel-with-deferreds
     (testing "Parallel waits for all deferreds to complete"
       (let [d1 (sync/deferred)
             d2 (sync/deferred)
             par-spin (parallel d1 d2)
             result (promise)]

         ;; Start awaiting result in background
         (future
           (deliver result @par-spin))

         ;; Let some time pass
         (Thread/sleep 10)

         ;; Result should not be ready yet
         (is (not (realized? result)) "Should not complete before deferreds")

         ;; Deliver first deferred
         (d1 :first)
         (Thread/sleep 10)
         (is (not (realized? result)) "Should not complete with only one deferred")

         ;; Deliver second deferred
         (d2 :second)
         (Thread/sleep 50)

         ;; Now result should be ready
         (is (realized? result) "Should complete after both deferreds")
         (is (= [:first :second] @result) "Should combine results")))))

#?(:clj
   (deftest test-parallel-with-deferreds-three
     (testing "Parallel waits for all deferreds"
       (let [d1 (sync/deferred)
             d2 (sync/deferred)
             d3 (sync/deferred)
             parallel-spin (parallel d1 d2 d3)
             result (promise)]

         ;; Start awaiting
         (future
           (deliver result @parallel-spin))

         ;; Deliver in reverse order
         (d3 :third)
         (Thread/sleep 10)
         (d2 :second)
         (Thread/sleep 10)
         (d1 :first)
         (Thread/sleep 50)

         ;; Should complete with results in original order
         (is (realized? result) "Should complete after all deferreds")
         (is (= [:first :second :third] @result) "Should maintain order")))))

#?(:clj
   (deftest test-parallel-mixed-immediate-deferred
     (testing "Parallel with mix of immediate spins and deferreds"
       (let [immediate (spin :immediate)
             d (sync/deferred)
             par-spin (parallel immediate d)
             result (promise)]

         (future
           (deliver result @par-spin))

         (Thread/sleep 10)
         ;; Should not complete yet (waiting for deferred)
         (is (not (realized? result)) "Should wait for deferred")

         (d :deferred)
         (Thread/sleep 50)

         (is (realized? result) "Should complete after deferred")
         (is (= [:immediate :deferred] @result) "Should combine results")))))

#?(:clj
   (deftest test-parallel-first-error-fails
     (testing "Parallel fails when any child fails"
       (let [t1 (spin :ok)
             t2 (spin (throw (ex-info "test error" {:test true})))
             par-spin (parallel t1 t2)]
         (is (thrown-with-msg? Exception #"test error"
                               @par-spin)
             "Should propagate error")))))

;; =============================================================================
;; CLJ-only: Context switching tests (forked context scenario)
;; =============================================================================

#?(:clj
   (deftest test-parallel-with-forked-context
     (testing "Parallel where spins use actually forked contexts (like inference)"
       (let [parent-ctx (ctx/create-execution-context
                         {:executor (sched/thread-pool-executor 4)})]
         (binding [ec/*execution-context* parent-ctx]
           (let [batch-spins (repeatedly 3
                              (fn []
                                (spin
                                  (let [snap (ctx/snapshot-context parent-ctx)
                                        forked-ctx (ctx/restore-snapshot snap :drain-events? false)]
                                    (binding [ec/*execution-context* forked-ctx]
                                      (let [subspin (spin (* 5 6))]
                                        (await subspin)))))))
                 result @(parallel (first batch-spins)
                                   (second batch-spins)
                                   (nth batch-spins 2))]
             (is (= [30 30 30] result) "Should complete with forked context")))))))

#?(:clj
   (deftest test-parallel-with-forked-context-and-trampoline
     (testing "Parallel with forked context AND trampoline binding (exact inference scenario)"
       (let [parent-ctx (ctx/create-execution-context
                         {:executor (sched/thread-pool-executor 4)})]
         (binding [ec/*execution-context* parent-ctx]
           (let [batch-spins (repeatedly 3
                              (fn []
                                (spin
                                  (let [snap (ctx/snapshot-context parent-ctx)
                                        forked-ctx (ctx/restore-snapshot snap :drain-events? false)]
                                    (binding [ec/*execution-context* forked-ctx
                                              pcps-async/*in-trampoline* false]
                                      (let [subspin (spin (* 7 8))]
                                        (await subspin)))))))
                 result @(parallel (first batch-spins)
                                   (second batch-spins)
                                   (nth batch-spins 2))]
             (is (= [56 56 56] result) "Should complete with forked context and trampoline")))))))

#?(:clj
   (deftest test-parallel-awaiting-same-shared-spin
     (testing "Parallel where multiple batch spins await the SAME shared spin (like inference prog)"
       (let [parent-ctx (ctx/create-execution-context
                         {:executor (sched/thread-pool-executor 4)})]
         (binding [ec/*execution-context* parent-ctx]
           (let [shared-spin (spin (+ 10 20))
                 batch-spins (repeatedly 3
                              (fn []
                                (spin
                                  (let [snap (ctx/snapshot-context parent-ctx)
                                        forked-ctx (ctx/restore-snapshot snap :drain-events? false)]
                                    (binding [ec/*execution-context* forked-ctx
                                              pcps-async/*in-trampoline* false]
                                      (await shared-spin))))))
                 result @(parallel (first batch-spins)
                                   (second batch-spins)
                                   (nth batch-spins 2))]
             (is (= [30 30 30] result) "Should complete when awaiting same shared spin")))))))

#?(:clj
   (deftest test-parallel-with-model-like-spin
     (testing "Parallel where model spin uses nested await (like probabilistic models)"
       (let [parent-ctx (ctx/create-execution-context
                         {:executor (sched/thread-pool-executor 4)})]
         (binding [ec/*execution-context* parent-ctx]
           (let [model-spin (spin
                              (let [inner-spin (spin (* 2 3))]
                                (+ 100 (await inner-spin))))
                 batch-spins (repeatedly 3
                              (fn []
                                (spin
                                  (let [snap (ctx/snapshot-context parent-ctx)
                                        forked-ctx (ctx/restore-snapshot snap :drain-events? false)]
                                    (binding [ec/*execution-context* forked-ctx
                                              pcps-async/*in-trampoline* false]
                                      (await model-spin))))))
                 result @(parallel (first batch-spins)
                                   (second batch-spins)
                                   (nth batch-spins 2))]
             (is (= [106 106 106] result) "Should complete with model-like spin")))))))

#?(:clj
   (deftest test-parallel-with-async-model
     (testing "Parallel where model spin uses async-fetch (truly pauses)"
       (let [parent-ctx (ctx/create-execution-context
                         {:executor (sched/thread-pool-executor 4)})]
         (binding [ec/*execution-context* parent-ctx]
           (let [model-spin (spin
                              (let [async-val (await (async-stub/async-fetch 42 5))]
                                (* 2 async-val)))
                 batch-spins (repeatedly 3
                              (fn []
                                (spin
                                  (let [snap (ctx/snapshot-context parent-ctx)
                                        forked-ctx (ctx/restore-snapshot snap :drain-events? false)
                                        result (binding [ec/*execution-context* forked-ctx
                                                         pcps-async/*in-trampoline* false]
                                                 (await model-spin))]
                                    (rtp/enqueue! parent-ctx
                                      {:type :spin-completion :id (spin-core/spin-id model-spin)})
                                    result))))
                 result @(parallel (first batch-spins)
                                   (second batch-spins)
                                   (nth batch-spins 2))]
             (is (= [84 84 84] result) "Should complete with async model")))))))

#?(:clj
   (deftest test-parallel-with-multiple-async-in-model
     (testing "Parallel where model spin awaits multiple async operations"
       (let [parent-ctx (ctx/create-execution-context
                         {:executor (sched/thread-pool-executor 4)})]
         (binding [ec/*execution-context* parent-ctx]
           (let [model-spin (spin
                              (let [a (await (async-stub/async-fetch 10 5))
                                    b (await (async-stub/async-fetch 20 5))]
                                (+ a b)))
                 batch-spins (repeatedly 3
                              (fn []
                                (spin
                                  (let [snap (ctx/snapshot-context parent-ctx)
                                        forked-ctx (ctx/restore-snapshot snap :drain-events? false)]
                                    (binding [ec/*execution-context* forked-ctx
                                              pcps-async/*in-trampoline* false]
                                      (await model-spin))))))
                 result @(parallel (first batch-spins)
                                   (second batch-spins)
                                   (nth batch-spins 2))]
             (is (= [30 30 30] result) "Should complete with multiple async in model")))))))

#?(:clj
   (deftest test-parallel-model-created-outside-binding
     (testing "Parallel where model is created OUTSIDE the execution context (like test setup)"
       (let [parent-ctx (ctx/create-execution-context
                         {:executor (sched/thread-pool-executor 4)})
             model-spin (binding [ec/*execution-context* parent-ctx]
                          (spin
                            (let [inner (spin (* 5 5))]
                              (await inner))))]
         (binding [ec/*execution-context* parent-ctx]
           (let [batch-spins (repeatedly 3
                              (fn []
                                (spin
                                  (let [snap (ctx/snapshot-context parent-ctx)
                                        forked-ctx (ctx/restore-snapshot snap :drain-events? false)]
                                    (binding [ec/*execution-context* forked-ctx
                                              pcps-async/*in-trampoline* false]
                                      (await model-spin))))))
                 result @(parallel (first batch-spins)
                                   (second batch-spins)
                                   (nth batch-spins 2))]
             (is (= [25 25 25] result) "Should complete with externally created model")))))))
