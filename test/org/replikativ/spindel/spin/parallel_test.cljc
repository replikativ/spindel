(ns org.replikativ.spindel.spin.parallel-test
  "Tests for parallel combinator"
  (:refer-clojure :exclude [await])
  #?(:clj
     (:require [clojure.test :refer [deftest is testing use-fixtures]]
               [org.replikativ.spindel.engine.core :as ec]
               [org.replikativ.spindel.engine.protocols :as rtp]
               [org.replikativ.spindel.engine.executor :as sched]
               [org.replikativ.spindel.engine.context :as ctx]
               [org.replikativ.spindel.engine.impl.simple :as simple]
               [org.replikativ.spindel.signal :refer [signal]]
               [org.replikativ.spindel.spin.sync :as sync]
               [org.replikativ.spindel.spin.core :as spin-core]
               [org.replikativ.spindel.spin.combinators :refer [parallel]]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.effects.await :refer [await]]
               [org.replikativ.spindel.effects.track :refer [track]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!
                                                            await-engine-idle!]]
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
               [org.replikativ.spindel.effects.track :refer [track]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!
                                                            await-engine-idle!]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.signal :refer [signal]])))

;; CLJ-only fixture. Uses close-context! (rather than stop-context!) so the
;; thread-pool-executor created here is shut down after each test. With
;; stop-context! the pool's 4 daemon threads would leak per test, which on
;; this 20+ test namespace pushes JVM thread count past 200 and starts
;; preventing newly-submitted executor tasks from running — causing the
;; tail of the namespace to flake regardless of test logic.
#?(:clj
   (use-fixtures :each
     (fn [f]
       (let [execution-ctx (ctx/create-execution-context {:executor (sched/thread-pool-executor 4)})]
         (try
           (binding [ec/*execution-context* execution-ctx]
             (f))
           (finally
             (ctx/close-context! execution-ctx)))))))

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
;; Reactive re-completion: a child that re-completes :error must propagate
;; =============================================================================

(deftest test-parallel-reactive-child-error-propagates
  (testing "A parallel child that first completes :ok then re-completes :error
            must make parallel re-complete :error — not re-cache (ok <the-error>)"
    (async done
           (with-ctx [ctx]
             (let [;; mode signal: :ok → child returns a value;
                   ;;              :fail → child throws on re-run
                   mode (signal :ok)
                   ;; reactive child: tracks `mode`, throws when it flips to :fail
                   child-a (spin
                            (let [{m :new} (track mode)]
                              (if (= m :fail)
                                (throw (ex-info "child-a re-completed with error" {:boom true}))
                                :a-value)))
                   child-b (spin :b-value)
                   ;; parent awaits the parallel; its await cont re-fires when
                   ;; parallel re-completes after child-a re-runs.
                   outcomes (atom [])
                   parent (spin
                           (let [r (await (parallel child-a child-b))]
                             r))]
               (run-spin! parent
                          (fn [v] (swap! outcomes conj [:ok v]))
                          (fn [e] (swap! outcomes conj [:error e])))
               (await-engine-idle!
                ctx
                (fn []
                  ;; Initial completion: parallel resolved [:a-value :b-value].
                  (is (= [[:ok [:a-value :b-value]]] @outcomes)
                      "parallel should initially complete :ok")
                  ;; Flip the signal — child-a re-runs and throws.
                  (reset! mode :fail)
                  (await-engine-idle!
                   ctx
                   (fn []
                     (is (= 2 (count @outcomes))
                         "parent should be resumed once more by the re-completion")
                     (let [[variant payload] (second @outcomes)]
                       (is (= :error variant)
                           "parallel must re-complete :error when a child re-completes :error")
                       (is (and (instance? #?(:clj clojure.lang.ExceptionInfo
                                              :cljs cljs.core/ExceptionInfo)
                                           payload)
                                (:boom (ex-data payload)))
                           "the error payload must be the child's exception, not an ok-wrapped value"))
                     (done))))))))))

;; =============================================================================
;; CLJ-only tests: require Thread/sleep, future, promise, thread-pool-executor
;; =============================================================================

;; These tests use deterministic synchronization via a poll-until helper that
;; blocks until either an expected condition is true or a hard timeout fires.
;; The previous Thread/sleep approach assumed a fixed delay was always enough
;; for the engine to settle; that turns flaky on cold JVMs and busy CI runners.
;; await-drain-complete! alone is not enough here because parallel submits
;; child invocations to the executor — those tasks aren't tracked in the
;; engine's :pending queue or :nodes :running? flag, so the drain check can
;; return while children are still queued on the pool.
#?(:clj
   (defn- wait-until!
     "Block (up to timeout-ms) until pred returns truthy. CLJ-only — these
     tests sit inside #?(:clj …) blocks; CLJS uses cljs.test/async + done."
     ([pred] (wait-until! pred 5000))
     ([pred timeout-ms]
      (let [deadline (+ (System/currentTimeMillis) timeout-ms)]
        (loop []
          (cond
            (pred) true
            (>= (System/currentTimeMillis) deadline) false
            :else (do (java.util.concurrent.locks.LockSupport/parkNanos (* 100 1000))
                      (recur))))))))

#?(:clj
   (deftest test-parallel-with-deferreds
     (testing "Parallel waits for all deferreds to complete"
       (let [ctx ec/*execution-context*
             d1 (sync/deferred)
             d2 (sync/deferred)
             par-spin (parallel d1 d2)
             result (atom :pending)]

         ;; Invoke parallel directly so its body runs and registers child awaits.
         (par-spin
          (fn [v] (reset! result [:ok v]))
          (fn [e] (reset! result [:err e])))

         ;; Wait briefly to give children a chance to start, then verify still pending.
         (simple/await-drain-complete! ctx)
         (is (= :pending @result) "Should not complete before any deferred")

         ;; Deliver first; still pending (waiting for d2).
         (d1 :first)
         (simple/await-drain-complete! ctx)
         (is (= :pending @result) "Should not complete with only one deferred")

         ;; Deliver second; wait until result is delivered.
         (d2 :second)
         (is (wait-until! #(not= :pending @result)) "parallel should complete")
         (is (= [:ok [:first :second]] @result) "Should combine results")))))

#?(:clj
   (deftest test-parallel-with-deferreds-three
     (testing "Parallel waits for all deferreds"
       (let [ctx ec/*execution-context*
             d1 (sync/deferred)
             d2 (sync/deferred)
             d3 (sync/deferred)
             parallel-spin (parallel d1 d2 d3)
             result (atom :pending)]

         (parallel-spin
          (fn [v] (reset! result [:ok v]))
          (fn [e] (reset! result [:err e])))

         (d3 :third)
         (simple/await-drain-complete! ctx)
         (is (= :pending @result))

         (d2 :second)
         (simple/await-drain-complete! ctx)
         (is (= :pending @result))

         (d1 :first)
         (is (wait-until! #(not= :pending @result)) "parallel should complete")
         (is (= [:ok [:first :second :third]] @result) "Should maintain order")))))

#?(:clj
   (deftest test-parallel-mixed-immediate-deferred
     (testing "Parallel with mix of immediate spins and deferreds"
       (let [ctx ec/*execution-context*
             immediate (spin :immediate)
             d (sync/deferred)
             par-spin (parallel immediate d)
             result (atom :pending)]

         (par-spin
          (fn [v] (reset! result [:ok v]))
          (fn [e] (reset! result [:err e])))

         ;; After drain, the immediate child is done but parallel still waits
         ;; on the deferred.
         (simple/await-drain-complete! ctx)
         (is (= :pending @result) "Should wait for deferred")

         (d :deferred)
         (is (wait-until! #(not= :pending @result)) "parallel should complete")
         (is (= [:ok [:immediate :deferred]] @result) "Should combine results")))))

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

;; =============================================================================
;; CLJ-only: fork-isolation of a REACTIVE parallel
;; =============================================================================
;;
;; Regression guard for the #5 fix (parallel results moved off a permanent
;; engine side-key onto the spin's node). The reactive phase reads/updates the
;; node's cached result, which is per-context (overlay-copied on fork) — so a
;; signal change in a fork must update only the fork's parallel result and
;; leave the parent's untouched.

#?(:clj
   (deftest test-parallel-reactive-fork-isolation
     (testing "A reactive parallel's result updates per-context: changing a
               tracked signal in a fork must not mutate the parent's result"
       (let [parent (ctx/create-execution-context
                     {:executor (sched/thread-pool-executor 4)})]
         (try
           (let [par (binding [ec/*execution-context* parent]
                       (let [sig (signal 10)
                             p   (parallel (spin (:new (track sig))) (spin :static))]
                         @p
                         (simple/await-drain-complete! parent)
                         {:sig sig :p p}))
                 {:keys [sig p]} par
                 ;; The same `parallel` results never live in a side key.
                 _ (is (not (contains? (rtp/get-state parent []) :parallel/results))
                       "parallel must not create a :parallel/results engine key")
                 fork (ctx/fork-context parent)]
             ;; Mutate the tracked signal ONLY in the fork, then drain the fork.
             (binding [ec/*execution-context* fork]
               (reset! sig 99)
               (simple/await-drain-complete! fork))
             (let [pid          (spin-core/spin-id p)
                   parent-result (:payload (binding [ec/*execution-context* parent]
                                             (ec/spin-current-result pid)))
                   fork-result   (:payload (binding [ec/*execution-context* fork]
                                             (ec/spin-current-result pid)))]
               (is (= [10 :static] parent-result)
                   "parent's parallel result must be unchanged by the fork")
               (is (= [99 :static] fork-result)
                   "fork's parallel result must reflect the fork-local signal change")))
           (finally
             (ctx/close-context! parent)))))))
