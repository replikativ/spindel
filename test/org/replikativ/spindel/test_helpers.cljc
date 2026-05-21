(ns org.replikativ.spindel.test-helpers
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
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.state-backend :as backend]
            #?(:clj [clojure.test :as ct]
               :cljs [cljs.test :as ct]))
  #?(:cljs (:require-macros [org.replikativ.spindel.test-helpers])))

;; Cleanup queue used by the `async` macro to defer `stop-context!` for any
;; `with-ctx` nested inside it. Without this, with-ctx's finally fires the
;; moment the synchronous body returns — *before* the async work has
;; completed — and `executor/alive-fn` (CLJS) or any future stop-aware path
;; would then drop the very callbacks the test is waiting on. When this var
;; holds an atom-of-vec, with-ctx pushes its cleanup onto it instead of
;; running it inline, and `async` runs everything after `done` resolves.
(def ^:dynamic *async-cleanups* nil)

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
       ;; CLJS - use cljs.test/async, with cleanup atom so nested with-ctx
       ;; can defer stop-context! until after `done` fires.
       `(let [cleanups# (atom [])
              done?# (atom false)]
          (cljs.test/async raw-done#
                           (binding [*async-cleanups* cleanups#]
                             (let [~done-sym (fn []
                                               ;; Idempotent: `done` MUST run exactly once, but
                                               ;; run-spin!'s callback is a reactive subscription
                                               ;; that can re-fire — guard so cleanups + raw-done
                                               ;; run a single time (mirrors the CLJ branch's
                                               ;; realized? guard).
                                               (when (compare-and-set! done?# false true)
                                                 (doseq [c# @cleanups#]
                                                   (try (c#) (catch :default _#)))
                                                 (raw-done#)))]
                               ~@body))))
       ;; CLJ - use promise-based blocking, with cleanups deferred until
       ;; after the deref so any with-ctx inside body keeps its context
       ;; alive while async work completes.
       `(let [p# (promise)
              cleanups# (atom [])
              ~done-sym (fn []
                          (when-not (realized? p#)
                            (deliver p# :done)))]
          (binding [*async-cleanups* cleanups#]
            (try
              ~@body
              (let [result# (deref p# 15000 :timeout)]
                (when (= result# :timeout)
                  (throw (ex-info "Async test timed out after 15 seconds" {}))))
              (catch Throwable t#
                (deliver p# :error)
                (throw t#))
              (finally
                (doseq [c# @cleanups#]
                  (try (c#) (catch Throwable _#))))))))))

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

     Binds *execution-context* to a fresh context.
     The context is available as a local binding.
     Automatically stops the context's drain thread on exit.

     Usage:
       (with-ctx [ctx]
         (let [t (spin (+ 1 2))]
           ...))"
     [[ctx-sym] & body]
     `(let [~ctx-sym (create-test-context)
            cleanups# *async-cleanups*]
        (if cleanups#
          ;; Inside async: defer stop-context! to run after `done` fires,
          ;; so async work isn't truncated by an early teardown.
          (do
            (swap! cleanups# conj #(ctx/stop-context! ~ctx-sym))
            (binding [ec/*execution-context* ~ctx-sym]
              ~@body))
          ;; Standalone (sync test): stop on body return, as before.
          (try
            (binding [ec/*execution-context* ~ctx-sym]
              ~@body)
            (finally
              (ctx/stop-context! ~ctx-sym)))))))

;; =============================================================================
;; Spin Execution Helpers
;; =============================================================================

(defn run-spin!
  "Execute a spin with callbacks.

   Invokes the spin with callbacks. Event draining is handled automatically
   by the background drain thread in the execution context.
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
  ;; Invoke the spin. On JVM, wrap callbacks to preserve *report-counters*
  ;; so that assertions fired from drain/executor threads are properly counted.
  #?(:clj
     (let [counters ct/*report-counters*]
       (t (fn [v] (binding [ct/*report-counters* counters] (on-success v)))
          (fn [e] (binding [ct/*report-counters* counters] (on-error e)))))
     :cljs
     (t on-success on-error)))

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
;; Drain-Idle Wait Helper
;; =============================================================================

(defn- engine-idle?
  "True when the engine for `ctx` has no pending events and no drain
  in progress — i.e. every drain triggered up to this point has
  finished. Reads one consistent snapshot from the state backend.

  We deliberately do NOT require all spins to have completed: tests
  routinely keep a spin suspended on `await` while exercising signal
  propagation, and that legitimately leaves `running? = true` on the
  suspended spin without there being any drain work outstanding.
  The pending+draining check is the right notion of \"the runtime
  has finished processing the events I enqueued.\""
  [ctx]
  (let [state (backend/backend-deref (:backend ctx))]
    (and (empty? (get state :engine/pending))
         (not (get state :engine/draining?)))))

(defn await-engine-idle!
  "Cross-platform drain barrier. Invokes `then` (zero-arg) once the
  engine reports idle (no pending events, no in-flight body, no
  drain in progress). On JVM, blocks the calling thread; on CLJS,
  polls via `setTimeout` and resolves asynchronously.

  `*execution-context*` is bound to `ctx` while `then` runs, so
  signal mutations / context reads inside the callback work even
  when CLJS has unwound the surrounding `with-ctx` binding before
  the setTimeout fires.

  Use inside an `async`/`with-ctx` block to sequence assertions that
  must happen *after* the drain triggered by a signal mutation or
  resource delivery has run to completion.

  Example:
    (reset! my-signal :new-value)
    (await-engine-idle! ctx
      (fn []
        (is (= :expected @observed))
        (done)))"
  ([ctx then]
   (await-engine-idle! ctx then {}))
  ([ctx then {:keys [timeout-ms poll-ms]
              :or {timeout-ms 2000 poll-ms 5}}]
   #?(:clj
      (do
        (simple/await-drain-complete! ctx :timeout-ms timeout-ms)
        (binding [ec/*execution-context* ctx] (then)))
      :cljs
      (let [start (.getTime (js/Date.))
            invoke-then (fn []
                          (binding [ec/*execution-context* ctx]
                            (then)))]
        (letfn [(check []
                  (cond
                    (engine-idle? ctx)
                    (invoke-then)

                    (> (- (.getTime (js/Date.)) start) timeout-ms)
                    (do (ct/is false
                               (str "await-engine-idle! timed out after " timeout-ms "ms"))
                        (invoke-then))

                    :else
                    (js/setTimeout check poll-ms)))]
          (js/setTimeout check poll-ms))))))

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
