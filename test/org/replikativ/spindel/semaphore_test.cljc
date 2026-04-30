(ns org.replikativ.spindel.semaphore-test
  "Tests for fork-safe semaphores with execution context.
   CLJ-only: requires Thread/sleep, future, promise, and blocking deref."
  (:refer-clojure :exclude [await])
  #?(:clj
     (:require [clojure.test :refer [deftest is testing use-fixtures]]
               [org.replikativ.spindel.engine.core :as ec]
               [org.replikativ.spindel.engine.context :as ctx]
               [org.replikativ.spindel.engine.executor :as sched]
               [org.replikativ.spindel.semaphore :as sem]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.effects.await :refer [await]])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]])))

;; =============================================================================
;; All semaphore tests are CLJ-only due to:
;; - Thread/sleep for timing
;; - future/promise for concurrent testing
;; - blocking deref with timeout
;; =============================================================================

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
;; Basic semaphore creation and deref
;; =============================================================================

#?(:clj
   (deftest test-semaphore-creation
     (testing "Create semaphore with initial permits"
       (let [s (sem/semaphore 5)]
         (is (= 5 @s) "Should have 5 initial permits")))))

#?(:clj
   (deftest test-semaphore-deref
     (testing "Deref returns current available permits"
       (let [s (sem/semaphore 10)]
         (is (= 10 @s) "Initial permits should be 10")))))

;; =============================================================================
;; Acquire and release
;; =============================================================================

#?(:clj
   (deftest test-acquire-immediate
     (testing "Acquire when permits are available completes immediately"
       (let [s (sem/semaphore 3)
             result @(spin
                      (let [status (await (sem/acquire s))]
                        status))]
         (is (= :acquired result) "Should acquire immediately")
         (is (= 2 @s) "Permits should decrease to 2")))))

#?(:clj
   (deftest test-acquire-release
     (testing "Acquire decreases permits, release increases them"
       (let [s (sem/semaphore 5)]
         @(spin (await (sem/acquire s)))
         (is (= 4 @s) "After acquire, permits should be 4")

         (sem/release s)
         (is (= 5 @s) "After release, permits should be back to 5")))))

#?(:clj
   (deftest test-multiple-acquires
     (testing "Multiple acquires decrease permits correctly"
       (let [s (sem/semaphore 10)]
         @(spin
           (await (sem/acquire s))
           (await (sem/acquire s))
           (await (sem/acquire s)))
         (is (= 7 @s) "After 3 acquires, should have 7 permits")))))

;; =============================================================================
;; Queueing when no permits available
;; =============================================================================

#?(:clj
   (deftest test-acquire-waits-when-no-permits
     (testing "Acquire waits when no permits available"
       (let [s (sem/semaphore 1)
             waiter-started (promise)
             waiter-completed (promise)]

         ;; First spin acquires the only permit
         @(spin (await (sem/acquire s)))
         (is (= 0 @s) "No permits available")

         ;; Second spin should wait
         (let [ctx ec/*execution-context*
               sem-id (.-id s)]
           (future
             (binding [ec/*execution-context* ctx]
               (deliver waiter-started :started)
               (let [result @(spin (await (sem/acquire s)))]
                 (deliver waiter-completed result))))

           ;; Wait for the waiter to actually enqueue itself in the
           ;; semaphore's waiting-queue. Polling on the queue is
           ;; deterministic — no wall-clock guesses.
           (deref waiter-started 1000 :timeout)
           (let [deadline (+ (System/currentTimeMillis) 1000)]
             (loop []
               (let [queued (count (ec/get-state [:semaphores sem-id :waiting-queue]))]
                 (cond
                   (pos? queued) :enqueued
                   (>= (System/currentTimeMillis) deadline) :timeout
                   :else (do (Thread/yield) (recur)))))))

         ;; Waiter should not complete yet
         (is (not (realized? waiter-completed)) "Waiter should be blocked")

         ;; Release permit
         (sem/release s)

         ;; Waiter should now complete
         (is (= :acquired (deref waiter-completed 1000 :timeout))
             "Waiter should acquire after release")))))

#?(:clj
   (deftest test-fifo-queueing
     (testing "Multiple waiters are all eventually served"
       (let [s (sem/semaphore 1)
             results (atom [])
             n-waiters 3]

         ;; Acquire the only permit
         @(spin (await (sem/acquire s)))

         ;; Start waiters that acquire, do work, and release within a single spin.
         ;; Using spins (not futures) avoids cross-thread release races.
         (let [waiter-spins
               (doall
                 (for [i (range n-waiters)]
                   (spin
                     (await (sem/acquire s))
                     (swap! results conj i)
                     (sem/release s)
                     i)))
               sem-id (.-id s)
               ctx ec/*execution-context*
               ;; Kick off each spin on its own thread so the body runs and
               ;; registers an await on the semaphore. We deref these futures
               ;; later, so each spin runs on exactly one thread.
               waiter-futures
               (doall
                 (for [ws waiter-spins]
                   (future (binding [ec/*execution-context* ctx] @ws))))]

           ;; Wait until all waiters have actually enqueued — polling the
           ;; semaphore's waiting-queue is deterministic, no wall-clock guess.
           (let [deadline (+ (System/currentTimeMillis) 2000)]
             (loop []
               (let [queued (count (ec/get-state [:semaphores sem-id :waiting-queue]))]
                 (cond
                   (= queued n-waiters) :all-queued
                   (>= (System/currentTimeMillis) deadline)
                   (throw (ex-info "Waiters never queued"
                                   {:queued queued :expected n-waiters}))
                   :else (do (Thread/yield) (recur))))))

           ;; Release initial permit - this should wake first waiter
           (sem/release s)

           ;; Wait for the futures we kicked off (one per waiter spin).
           (doseq [f waiter-futures] (deref f 5000 :timeout))

           ;; Should see all three results (order may vary due to scheduling)
           (is (= n-waiters (count @results)) "All waiters should complete")
           (is (= (set (range n-waiters)) (set @results)) "All waiters should have run exactly once"))))))

;; =============================================================================
;; Holding pattern (automatic release)
;; =============================================================================

#?(:clj
   (deftest test-holding-success
     (testing "Holding automatically releases on success"
       (let [s (sem/semaphore 2)
             result @(sem/holding s
                       (spin
                        (let [permits-during @s]
                          ;; During execution, one permit is held
                          permits-during)))]
         (is (= 1 result) "Should see 1 permit available during execution")
         (is (= 2 @s) "Permit should be released after completion")))))

#?(:clj
   (deftest test-holding-failure
     (testing "Holding automatically releases even on error"
       (let [s (sem/semaphore 3)]
         (try
           @(sem/holding s
              (spin
               (throw (ex-info "Test error" {}))))
           (catch Exception _e
             :caught))

         ;; Permit should be released despite error
         (is (= 3 @s) "Permit should be released even on error")))))

#?(:clj
   (deftest test-nested-holding
     (testing "Nested holding calls with same semaphore"
       (let [s (sem/semaphore 5)
             result @(sem/holding s
                       (spin
                        (let [outer-permits @s]
                          (await (sem/holding s
                                   (spin
                                    (let [inner-permits @s]
                                      {:outer outer-permits
                                       :inner inner-permits})))))))]
         (is (= 4 (:outer result)) "Outer should see 4 permits (1 held)")
         (is (= 3 (:inner result)) "Inner should see 3 permits (2 held)")
         (is (= 5 @s) "All permits should be released after completion")))))

;; =============================================================================
;; Concurrency and resource limiting
;; =============================================================================

#?(:clj
   (deftest test-concurrent-limit
     (testing "Semaphore limits concurrent access to N"
       (let [s (sem/semaphore 2)
             active-count (atom 0)
             max-active (atom 0)
             spins 10]

         ;; Launch 10 spins that all try to acquire
         (let [futures (doall
                        (for [_i (range spins)]
                          (future
                            (binding [ec/*execution-context* ec/*execution-context*]
                              @(sem/holding s
                                 (spin
                                  ;; Atomically increment and capture max - this is crucial!
                                  (let [current (swap! active-count inc)]
                                    (swap! max-active (fn [m] (max m current)))
                                    (Thread/sleep 50)
                                    (swap! active-count dec))))))))]

           ;; Wait for all to complete
           (doseq [f futures]
             (deref f 5000 :timeout)))

         ;; Should never have more than 2 active at once
         (is (<= @max-active 2) "Should never exceed semaphore limit")
         (is (= 0 @active-count) "All spins should complete")
         (is (= 2 @s) "All permits should be released")))))

;; =============================================================================
;; Error conditions
;; =============================================================================

#?(:clj
   (deftest test-over-release-error
     (testing "Releasing more permits than max throws error"
       (let [s (sem/semaphore 2)]
         ;; Try to release without acquiring
         (is (thrown-with-msg? Exception #"over-released"
               (sem/release s))
             "Should throw on over-release")))))

#?(:clj
   (deftest test-create-with-zero-permits
     (testing "Cannot create semaphore with zero or negative permits"
       (is (thrown? AssertionError
             (sem/semaphore 0))
           "Should fail assertion for 0 permits")

       (is (thrown? AssertionError
             (sem/semaphore -1))
           "Should fail assertion for negative permits"))))

;; =============================================================================
;; Fork-safety (runtime independence)
;; =============================================================================

#?(:clj
   (deftest test-semaphore-uses-dynamic-runtime
     (testing "Semaphore uses dynamically bound runtime, not captured"
       (let [ctx1 (ctx/create-execution-context {:executor (sched/thread-pool-executor 4)})]

         ;; Create semaphore in ctx1
         (binding [ec/*execution-context* ctx1]
           (let [s (sem/semaphore 5)]

             ;; Use in ctx1
             @(spin (await (sem/acquire s)))
             (is (= 4 @s) "Should have 4 permits in ctx1")

             ;; Verify semaphore still works with same context
             (binding [ec/*execution-context* ctx1]
               (is (= 4 @s) "Should still see 4 permits in same context"))))))))
