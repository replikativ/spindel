(ns org.replikativ.spindel.partial-cps-integration-test
  "Integration tests for partial-cps async blocks within spindel spins.

  This test suite validates the integration between spindel's spin system
  and partial-cps's lightweight async blocks. The key design principles:

  1. **Two-tier execution model**:
     - `spin` macro: Full dependency tracking, caching, incremental recomputation
     - `async` macro: Lightweight CPS, no tracking overhead, for inner loops

  2. **Passthrough semantics**:
     - When `await` receives an IFn (like an async thunk), it passes through
     - The async block handles its own CPS internally
     - Effect handlers inside async can still use spindel events if needed

  3. **Event-based resumption**:
     - Effect handlers inside async can use `:deferred-delivery` events
     - This allows async blocks to suspend and resume via spindel's event system

  Performance characteristics (approximate):
  - Pure partial-cps async: ~200ns
  - spin + await async: ~19µs (spin overhead)
  - spin + await spin: ~33µs (+ dependency tracking)

  See CLAUDE.md for architectural details."
  (:require [clojure.test :refer [deftest testing is]]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.impl.simple :as simple]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.spin.continuation :as cont]
            [org.replikativ.spindel.effects.await :refer [await]]
            [is.simm.partial-cps.async :as pcps :refer [async]]))

;; =============================================================================
;; Test Helpers
;; =============================================================================

(defn run-spin
  "Execute a spin and return its result with timeout.
  Returns the result or :timeout if not completed within ms."
  ([ctx t] (run-spin ctx t 1000))
  ([ctx t timeout-ms]
   (let [result (promise)]
     (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
       (t #(deliver result %) #(deliver result [:error %]))
       (simple/trigger-drain! ctx (:executor ctx)))
     (deref result timeout-ms :timeout))))

(defn async-sleep
  "Creates an async thunk that suspends and resumes via spindel's deferred-delivery.

  This demonstrates how effect handlers inside async blocks can integrate
  with spindel's event system for proper suspension/resumption.

  Args:
    ms - Milliseconds to sleep
    value - Value to return after sleep

  Returns: An async thunk (fn [resolve reject] ...) that:
    1. Creates a Deferred
    2. Schedules a timer to deliver to the Deferred
    3. Awaits the Deferred, which suspends the async computation"
  [ms value]
  (fn [resolve _reject]
    (let [runtime (rtc/current-execution-context)]
      (if runtime
        ;; In spindel context - use Deferred for proper integration
        (let [d (sync/deferred)]
          ;; Schedule timer to deliver to deferred
          (future
            (Thread/sleep ms)
            (binding [rtc/*execution-context* runtime]
              (d value)
              (simple/trigger-drain! runtime (:executor runtime))))
          ;; Await the deferred - this suspends correctly
          (d resolve (fn [e] (throw e))))

        ;; Not in spindel context - simple async
        (do
          (future
            (Thread/sleep ms)
            (resolve value))
          :org.replikativ.spindel.spin/incomplete)))))

;; =============================================================================
;; Basic Integration Tests
;; =============================================================================

(deftest test-sync-async-passthrough
  (testing "Synchronous async block passes through correctly"
    (let [ctx (ctx/create-execution-context)
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin (await (async (+ 1 2 3)))))]
      (is (= 6 (run-spin ctx t))
          "async block returning immediate value should work")))

  (testing "Nested sync async blocks"
    (let [ctx (ctx/create-execution-context)
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin (await (async
                             (let [a (pcps/await (async 10))
                                   b (pcps/await (async 20))]
                               (+ a b))))))]
      (is (= 30 (run-spin ctx t))
          "nested pcps/await inside async should work"))))

(deftest test-async-with-deferred-delivery
  (testing "Async block with deferred-delivery event"
    (let [ctx (ctx/create-execution-context)
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin (await (async
                             (pcps/await (async-sleep 10 :slept))
                             :done))))]
      (is (= :done (run-spin ctx t 500))
          "async block should suspend and resume via deferred-delivery"))))

(deftest test-spin-inside-async
  (testing "Creating spindel spin inside async block"
    (let [ctx (ctx/create-execution-context)
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin (await (async
                             ;; Create a spindel spin inside async
                             ;; and await it via pcps/await (treats it as IFn)
                             (let [inner (spin (* 7 8))]
                               (pcps/await inner))))))]
      (is (= 56 (run-spin ctx t))
          "spindel spin created inside async should be awaitable"))))

;; =============================================================================
;; Sequential Async Operations
;; =============================================================================

(deftest test-sequential-async-awaits
  (testing "Multiple sequential pcps/await calls"
    (let [ctx (ctx/create-execution-context)
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin (await (async
                             (let [a (pcps/await (async 10))
                                   b (pcps/await (async 20))
                                   c (pcps/await (async 30))]
                               (+ a b c))))))]
      (is (= 60 (run-spin ctx t))
          "sequential awaits should accumulate correctly")))

  (testing "Loop with pcps/await"
    (let [ctx (ctx/create-execution-context)
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin (await (async
                             (loop [i 0 sum 0]
                               (if (< i 5)
                                 (let [v (pcps/await (async i))]
                                   (recur (inc i) (+ sum v)))
                                 sum))))))]
      (is (= 10 (run-spin ctx t))  ; 0+1+2+3+4 = 10
          "loop with pcps/await should work"))))

;; =============================================================================
;; Error Handling
;; =============================================================================

(deftest test-error-propagation
  (testing "Error in async block propagates to spin"
    (let [ctx (ctx/create-execution-context)
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin (await (async
                             (throw (ex-info "test error" {:code 42}))))))
          result (run-spin ctx t)]
      (is (vector? result) "Should return error vector")
      (is (= :error (first result)) "First element should be :error")
      (is (= 42 (-> result second ex-data :code))
          "Error data should be preserved")))

  (testing "Error in nested async propagates"
    (let [ctx (ctx/create-execution-context)
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin (await (async
                             (pcps/await (async
                                           (throw (ex-info "nested error" {}))))))))
          result (run-spin ctx t)]
      (is (= :error (first result))
          "Nested error should propagate"))))

;; =============================================================================
;; Mixed Spin and Async
;; =============================================================================

(deftest test-mixed-spin-async
  (testing "Alternating spin and async awaits"
    (let [ctx (ctx/create-execution-context)
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin
                (let [;; await a spin
                      a (await (spin 10))
                      ;; await an async block
                      b (await (async (+ a 5)))
                      ;; await another spin using result from async
                      c (await (spin (* b 2)))]
                  c)))]
      (is (= 30 (run-spin ctx t))  ; (10 + 5) * 2 = 30
          "Mixed spin/async should work correctly")))

  (testing "Async block creating multiple spins"
    (let [ctx (ctx/create-execution-context)
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin (await (async
                             (let [t1 (spin 10)
                                   t2 (spin 20)
                                   ;; await both spins
                                   v1 (pcps/await t1)
                                   v2 (pcps/await t2)]
                               (+ v1 v2))))))]
      (is (= 30 (run-spin ctx t))
          "async block can create and await multiple spins"))))

;; =============================================================================
;; Passthrough Behavior Tests
;; =============================================================================

(deftest test-ifn-passthrough
  (testing "Plain IFn thunk is passed through"
    (let [ctx (ctx/create-execution-context)
          ;; Create a simple thunk that resolves immediately
          thunk (fn [resolve _reject] (resolve 42))
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin (await thunk)))]
      (is (= 42 (run-spin ctx t))
          "Plain IFn should be passed through and called")))

  (testing "Async macro produces IFn that passes through"
    (let [ctx (ctx/create-execution-context)
          ;; async macro returns an IFn
          async-thunk (async (* 6 7))
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin (await async-thunk)))]
      (is (= 42 (run-spin ctx t))
          "async thunk should pass through await"))))

;; =============================================================================
;; Context Availability Tests
;; =============================================================================

(deftest test-runtime-context-in-async
  (testing "Runtime context available inside async block"
    (let [ctx (ctx/create-execution-context)
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin (await (async
                             ;; Check that runtime is accessible
                             (let [ctx (rtc/current-execution-context)]
                               (if ctx :has-runtime :no-runtime))))))]
      (is (= :has-runtime (run-spin ctx t))
          "Runtime should be accessible inside async via dynamic binding")))

  (testing "Spin ID available in async block"
    (let [ctx (ctx/create-execution-context)
          captured-id (atom nil)
          t (binding [rtc/*execution-context* ctx rtc/*execution-context* ctx]
              (spin (await (async
                             (reset! captured-id rtc/*spin-id*)
                             :done))))]
      (run-spin ctx t)
      (is (some? @captured-id)
          "*spin-id* should be bound inside async block"))))
