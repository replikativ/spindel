(ns is.simm.spindel.test-async
  "Test utilities for async event processing.

  Provides helpers to wait for async event draining when using ThreadPoolExecutor.
  Required because signal mutations and spin completions enqueue events that are
  processed asynchronously on executor threads."
  (:require [is.simm.spindel.runtime.protocols :as rtp]
            [is.simm.spindel.runtime.impl.atoms]  ; Register :atoms impl
            #?(:clj [is.simm.spindel.runtime.core :as rtc])))

(defn await-drain
  "Wait for runtime's event queue to drain completely.

  Polls the queue until empty, with timeout protection.
  Use after signal mutations or spin completions when testing with ThreadPoolExecutor.

  Options:
  - :timeout-ms - Max wait time in milliseconds (default 5000)
  - :poll-interval-ms - How often to check queue (default 10)

  Returns: true if drained, false if timeout

  Example:
    (swap! counter inc)
    (await-drain rt)  ; Wait for signal-change event to be processed
    (is (= 2 @doubled))  ; Now safe to assert"
  ([runtime]
   (await-drain runtime {}))
  ([runtime {:keys [timeout-ms poll-interval-ms]
             :or {timeout-ms 5000
                  poll-interval-ms 10}}]
   #?(:clj
      (let [start-time (System/currentTimeMillis)]
        (loop [iteration 0]
          (let [queue (rtp/get-state runtime [:engine/pending])
                draining? (rtp/get-state runtime [:engine/draining?])
                elapsed (- (System/currentTimeMillis) start-time)]
            (cond
              ;; Success: queue empty and not currently draining
              (and (empty? queue) (not draining?))
              true

              ;; Timeout
              (> elapsed timeout-ms)
              false

              ;; Still working, wait and retry
              :else
              (do
                (Thread/sleep poll-interval-ms)
                (recur (inc iteration)))))))
      :cljs
      ;; CLJS version - busy wait for now (async would need promises)
      (let [start-time (.now js/Date)]
        (loop []
          (let [queue (rtp/get-state runtime [:engine/pending])
                draining? (rtp/get-state runtime [:engine/draining?])
                elapsed (- (.now js/Date) start-time)]
            (cond
              (and (empty? queue) (not draining?))
              true

              (> elapsed timeout-ms)
              false

              :else
              (recur))))))))

(defn await-stable
  "Wait for runtime to reach stable state (no events for quiet-ms).

  Useful for cascading updates where multiple events are generated.
  Ensures all downstream effects have settled before assertions.

  Options:
  - :quiet-ms - How long queue must be empty (default 50)
  - :timeout-ms - Max total wait time (default 5000)
  - :poll-interval-ms - How often to check (default 10)

  Returns: true if stable, false if timeout

  Example:
    (swap! counter inc)  ; Triggers multiple dependent spins
    (await-stable rt)    ; Wait for all cascading updates
    (is (= 90 @tripled)) ; Now safe to assert final state"
  ([runtime]
   (await-stable runtime {}))
  ([runtime {:keys [quiet-ms timeout-ms poll-interval-ms]
             :or {quiet-ms 50
                  timeout-ms 5000
                  poll-interval-ms 10}}]
   #?(:clj
      (let [start-time (System/currentTimeMillis)
            last-change (atom (System/currentTimeMillis))]
        (loop []
          (let [queue (rtp/get-state runtime [:engine/pending])
                draining? (rtp/get-state runtime [:engine/draining?])
                now (System/currentTimeMillis)
                quiet-time (- now @last-change)
                elapsed (- now start-time)]
            (cond
              ;; Success: quiet for required duration
              (and (>= quiet-time quiet-ms)
                   (empty? queue)
                   (not draining?))
              true

              ;; Timeout
              (> elapsed timeout-ms)
              false

              ;; Activity detected, reset quiet timer
              (or (seq queue) draining?)
              (do
                (reset! last-change now)
                (Thread/sleep poll-interval-ms)
                (recur))

              ;; Still in quiet period, keep waiting
              :else
              (do
                (Thread/sleep poll-interval-ms)
                (recur))))))
      :cljs
      ;; CLJS version
      (let [start-time (.now js/Date)
            last-change (atom (.now js/Date))]
        (loop []
          (let [queue (rtp/get-state runtime [:engine/pending])
                draining? (rtp/get-state runtime [:engine/draining?])
                now (.now js/Date)
                quiet-time (- now @last-change)
                elapsed (- now start-time)]
            (cond
              (and (>= quiet-time quiet-ms)
                   (empty? queue)
                   (not draining?))
              true

              (> elapsed timeout-ms)
              false

              (or (seq queue) draining?)
              (do
                (reset! last-change now)
                (recur))

              :else
              (recur))))))))

#?(:clj
   (defmacro async-test-fixture
     "Fixture macro for tests that need async event processing.

     Creates a runtime with ThreadPoolExecutor and ensures proper cleanup.
     Use as a let-style binding form.

     Example:
       (deftest my-test
         (async-test-fixture [rt]
           (binding [rtc/*execution-context* ctx]
             (let [sig (signal 0)
                   doubled (spin (* 2 (track sig)))]
               @doubled  ; => 0
               (swap! sig inc)
               (await-drain rt)
               (is (= 2 @doubled))))))"
     [[binding-sym] & body]
     `(let [~binding-sym (ctx/create-execution-context)]
        (try
          ~@body
          (finally
            ;; Shutdown executor to prevent thread leaks
            (when-let [executor# (rtp/get-executor ~binding-sym)]
              (when (satisfies? rtp/PExecutor executor#)
                (.shutdown (:thread-pool executor#)))))))))
