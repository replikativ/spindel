(ns org.replikativ.spindel.test-helpers.async-stub
  "Test helpers for simulating truly asynchronous operations.

  These stubs simulate external async operations (like HTTP requests, database
  queries, etc.) that complete on a different thread/tick from when they're called."
  (:require [org.replikativ.spindel.spin.core :as spin]
            [org.replikativ.spindel.spin.continuation :as cont]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            [is.simm.partial-cps.async :as async]))

(defn async-fetch
  "Simulates an async fetch operation that completes after a delay.

  Returns a Spin that will complete asynchronously on a separate thread.
  The value is delivered after a short delay (default 10ms) to ensure truly
  asynchronous behavior.

  This simulates real-world async operations like:
  - HTTP requests
  - Database queries
  - File I/O
  - External service calls

  Usage:
    (spin/spin
      (let [result (await (async-fetch 42))]
        (println \"Got:\" result)))  ; Prints after ~10ms delay

  Parameters:
    value - The value to return after the delay
    delay-ms - Optional delay in milliseconds (default 10)"
  ([value]
   (async-fetch value 10))
  ([value delay-ms]
   (let [spin-id (keyword (str "async-fetch-" value))]
     (spin/make-spin
      (fn [resolve reject]
        (let [runtime (rtc/current-execution-context)]
          ;; Use runtime's delayed execution mechanism (same as sleep combinator)
          ;; This properly integrates with the event queue and executor
          ;; CRITICAL: Bind *execution-context* to captured runtime when callback fires.
          ;; The callback runs on a thread pool thread with NO bindings, so we must
          ;; restore the context that was active when async-fetch was called.
          (rtc/schedule-delayed-execution! runtime delay-ms
            #(binding [rtc/*execution-context* runtime
                       async/*in-trampoline* false]
               (cont/resume resolve value)))
          ;; Return incomplete - continuation will be invoked later via scheduled execution
          spin/incomplete))
      spin-id))))

(defn async-fetch-error
  "Simulates an async fetch that fails with an error.

  Returns a Spin that will reject asynchronously after a delay.

  Usage:
    (spin/spin
      (try
        (await (async-fetch-error \"boom\"))
        (catch Exception e
          (println \"Error:\" (.getMessage e)))))

  Parameters:
    error-msg - Error message for the exception
    delay-ms - Optional delay in milliseconds (default 10)"
  ([error-msg]
   (async-fetch-error error-msg 10))
  ([error-msg delay-ms]
   (spin/make-spin
    (fn [resolve reject]
      (let [runtime (rtc/current-execution-context)]
        ;; Use runtime's delayed execution mechanism (same as sleep combinator)
        (rtc/schedule-delayed-execution! runtime delay-ms
          #(binding [async/*in-trampoline* false]
             (cont/resume reject (ex-info error-msg {}))))
        ;; Return incomplete - continuation will be invoked later via scheduled execution
        spin/incomplete))
    :async-fetch-error)))

(defn async-increment
  "Simulates an async operation that increments a number.

  Useful for testing chains of async operations.

  Usage:
    (spin/spin
      (loop [n 0 acc []]
        (if (< n 3)
          (let [incremented (await (async-increment n))]
            (recur (inc n) (conj acc incremented)))
          acc)))  ; => [1 2 3]"
  ([n]
   (async-increment n 10))
  ([n delay-ms]
   (async-fetch (inc n) delay-ms)))

(defn async-identity
  "Simulates an async operation that returns its input unchanged.

  Useful for testing that async operations don't transform values unexpectedly.

  Usage:
    (spin/spin
      (let [result (await (async-identity {:foo :bar}))]
        (is (= {:foo :bar} result))))"
  ([value]
   (async-identity value 10))
  ([value delay-ms]
   (async-fetch value delay-ms)))

;; =============================================================================
;; Test Fixture - Provides execution context for async tests
;; =============================================================================

(defn with-execution-context
  "Test fixture that creates and binds an execution context for all tests.

  This fixture ensures that RuntimeAtoms and other runtime-dependent features
  work properly in tests by providing the required *execution-context* binding.

  Usage in test namespace:
    (use-fixtures :each async-stub/with-execution-context)

  Or for all tests in the namespace:
    (use-fixtures :once async-stub/with-execution-context)"
  [f]
  (let [ctx (ctx/create-execution-context)]
    (binding [rtc/*execution-context* ctx]
      (f))))
