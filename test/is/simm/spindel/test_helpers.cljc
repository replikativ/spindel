(ns is.simm.spindel.test-helpers
  "Cross-platform test utilities for spindel.

  Provides a unified `async` macro that works identically on CLJ and CLJS,
  allowing tests to be written once and run on both platforms.

  Key features:
  - `async` macro: Cross-platform async test blocks
  - `with-ctx`: Helper macro for test context setup
  - `test-spin`: Convenience macro for simple spin assertions

  Example usage:

    (deftest my-test
      (async done
        (with-ctx [ctx]
          (let [t (spin (+ 1 2))]
            (t (fn [result]
                 (is (= 3 result))
                 (done))
               (fn [error]
                 (is false (str \"Error: \" error))
                 (done)))))))

  For simple synchronous spin tests, you can also use:

    (deftest simple-test
      (test-spin (spin (+ 1 2)) 3))"
  (:require [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.runtime.context :as ctx]
            [is.simm.spindel.runtime.impl.simple :as simple]
            #?(:clj [clojure.test :as ct]
               :cljs [cljs.test :as ct]))
  #?(:cljs (:require-macros [is.simm.spindel.test-helpers])))

;; =============================================================================
;; Cross-Platform Async Macro
;; =============================================================================

#?(:clj
   (defmacro async
     "Cross-platform async test block.

     Creates a block where async operations can complete before the test finishes.
     The `done` callback MUST be called exactly once to signal completion.

     Platform behavior:
     - CLJ: Creates a promise, executes body, blocks until done is called (10s timeout)
     - CLJS: Delegates to cljs.test/async

     Usage:
       (deftest my-test
         (async done
           (some-async-op
             (fn [result]
               (is (= expected result))
               (done)))))"
     [done-sym & body]
     (if (:js-globals &env)
       ;; CLJS - use cljs.test/async (must be fully qualified for macro expansion)
       `(cljs.test/async ~done-sym ~@body)
       ;; CLJ - use promise-based blocking
       `(let [p# (promise)
              ~done-sym (fn []
                          (when-not (realized? p#)
                            (deliver p# :done)))]
          (try
            ~@body
            (let [result# (deref p# 10000 :timeout)]
              (when (= result# :timeout)
                (throw (ex-info "Async test timed out after 10 seconds" {}))))
            (catch Throwable t#
              ;; Ensure promise is delivered on error to prevent deadlock
              (deliver p# :error)
              (throw t#)))))))

;; =============================================================================
;; Context Helpers
;; =============================================================================

(defn create-test-context
  "Create an execution context suitable for testing.

   Returns a fresh ExecutionContext with default settings."
  []
  (ctx/create-execution-context))

#?(:clj
   (defmacro with-ctx
     "Execute body with a fresh test context bound.

     Binds both *execution-context* and *execution-context* for full compatibility.
     The context is available as a local binding.

     Usage:
       (with-ctx [ctx]
         (let [t (spin (+ 1 2))]
           ...))"
     [[ctx-sym] & body]
     `(let [~ctx-sym (create-test-context)]
        (binding [rtc/*execution-context* ~ctx-sym
                  rtc/*execution-context* ~ctx-sym]
          ~@body))))

;; =============================================================================
;; Spin Execution Helpers
;; =============================================================================

(defn run-spin!
  "Execute a spin with callbacks.

   Invokes the spin and triggers event draining.
   Use within a with-ctx block or with *execution-context* bound.

   Arguments:
   - t: The spin to execute
   - on-success: Called with result value
   - on-error: Called with error

   Example:
     (with-ctx [ctx]
       (let [t (spin (+ 1 2))]
         (run-spin! t
           (fn [result] (is (= 3 result)) (done))
           (fn [error] (is false) (done)))))"
  [t on-success on-error]
  (let [ctx (rtc/current-execution-context)]
    (t on-success on-error)
    (simple/trigger-drain! ctx (:executor ctx))))

#?(:clj
   (defmacro test-spin
     "Convenience macro for testing a synchronous spin result.

     For spins that complete synchronously (no external async operations),
     this provides a simple one-liner test.

     Usage:
       (deftest my-test
         (with-ctx [ctx]
           (test-spin (spin (+ 1 2)) 3)))

     Note: This only works for synchronous spins. For async spins,
     use the full `async` + callback pattern."
     [spin-expr expected]
     `(let [result# (atom nil)
            error# (atom nil)]
        (run-spin! ~spin-expr
                   #(reset! result# %)
                   #(reset! error# %))
        (if @error#
          (throw (ex-info "Spin failed" {:error @error#}))
          (ct/is (= ~expected @result#))))))

;; =============================================================================
;; Async Test Helpers
;; =============================================================================

#?(:clj
   (defmacro async-test
     "Complete async test helper combining async, with-ctx, and run-spin!.

     Provides the most ergonomic way to write async spin tests.

     Usage:
       (deftest my-test
         (async-test [ctx done]
           (let [t (spin (+ 1 2))]
             (run-spin! t
               (fn [result]
                 (is (= 3 result))
                 (done))
               (fn [error]
                 (is false (str \"Error: \" error))
                 (done))))))"
     [[ctx-sym done-sym] & body]
     `(async ~done-sym
        (with-ctx [~ctx-sym]
          ~@body))))

;; =============================================================================
;; Assertion Helpers
;; =============================================================================

(defn assert-spin-succeeds
  "Assert a spin succeeds and call done.

   Convenience wrapper for the common pattern of:
   - Running a spin
   - Asserting success with expected value
   - Calling done on success or failure

   Usage:
     (async done
       (with-ctx [ctx]
         (assert-spin-succeeds (spin (+ 1 2)) 3 done)))"
  [t expected done]
  (run-spin! t
             (fn [result]
               (ct/is (= expected result))
               (done))
             (fn [error]
               (ct/is false (str "Spin failed: " error))
               (done))))

(defn assert-spin-fails
  "Assert a spin fails and call done.

   Usage:
     (async done
       (with-ctx [ctx]
         (assert-spin-fails (spin (throw (ex-info \"oops\" {}))) done)))"
  [t done]
  (run-spin! t
             (fn [result]
               (ct/is false (str "Expected failure, got: " result))
               (done))
             (fn [_error]
               (ct/is true "Spin failed as expected")
               (done))))
