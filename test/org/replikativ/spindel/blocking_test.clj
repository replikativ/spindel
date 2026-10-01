(ns org.replikativ.spindel.blocking-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.blocking :as blocking]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]])
  (:import [java.util.concurrent Executors RejectedExecutionException SynchronousQueue
            ThreadPoolExecutor ThreadPoolExecutor$AbortPolicy ThreadPoolExecutor$CallerRunsPolicy TimeUnit]))

(def ^:dynamic *conveyed* nil)

(defn- until
  "Poll `pred` every 5 ms for up to 5 s; its last value."
  [pred]
  (loop [n 0] (or (pred) (when (< n 1000) (Thread/sleep 5) (recur (inc n))))))

(defn- busy-pool
  "A one-thread pool whose thread waits for `gate`."
  ^ThreadPoolExecutor [gate]
  (let [pool (Executors/newFixedThreadPool 1)]
    (.submit pool ^Runnable (fn [] @gate))
    pool))

(deftest the-value-of-f-on-a-worker-thread
  (with-ctx [_]
    (let [thread (promise)
          s (spin (inc (await (blocking/blocking (fn [] (deliver thread (Thread/currentThread)) 41)))))]
      (is (= 42 (deref s 5000 ::timeout)))
      (is (not (re-find #"spindel-drain" (.getName ^Thread @thread))) "not the drain thread"))))

(deftest a-throw-rejects
  (with-ctx [_]
    (let [s (spin (try (await (blocking/blocking #(throw (ex-info "boom" {:code 7}))))
                       (catch Exception e (:code (ex-data e)))))]
      (is (= 7 (deref s 5000 ::timeout))))))

(deftest every-call-is-fresh-work
  (with-ctx [_]
    (let [n (atom 0)
          f #(swap! n inc)
          s (spin [(await (blocking/blocking f)) (await (blocking/blocking f))])]
      (is (= [1 2] (deref s 5000 ::timeout)) "two calls of the same f run twice"))))

(deftest the-callers-bindings-are-conveyed
  (with-ctx [_]
    (let [b (binding [*conveyed* :yes] (blocking/blocking (fn [] *conveyed*)))
          s (spin (await b))]
      (is (= :yes (deref s 5000 ::timeout))))))

(deftest losing-a-race-interrupts-the-worker
  ;; the other racer wins only once the worker is running: no timing assumption
  (with-ctx [c]
    (let [started (sync/deferred)
          interrupted (promise)
          b (blocking/blocking (fn []
                                 (binding [ec/*execution-context* c] (sync/deliver! started true))
                                 (try (Thread/sleep 30000) :slept
                                      (catch InterruptedException _ (deliver interrupted true)))))
          s (comb/race (spin (await b)) (spin (await started) ::other-won))]
      (is (= ::other-won (deref s 5000 ::timeout)))
      (is (true? (deref interrupted 5000 false)) "the worker was interrupted"))))

(deftest cancelling-interrupts-the-worker
  (with-ctx [_]
    (let [started (promise)
          interrupted (promise)
          b (blocking/blocking (fn []
                                 (deliver started true)
                                 (try (Thread/sleep 30000)
                                      (catch InterruptedException _ (deliver interrupted true)))))
          s (spin (await b))]
      (future (try @s (catch Throwable _ nil)))
      (is (true? (deref started 5000 false)))
      (spin-core/cancel-spin! b)
      (is (true? (deref interrupted 5000 false))))))

(deftest cancelled-while-queued-it-never-runs
  (with-ctx [_]
    (let [gate (promise)
          pool (busy-pool gate)
          ran (atom false)
          b (blocking/blocking #(reset! ran true) {:pool pool})
          s (spin (await b))]
      (future (try @s (catch Throwable _ nil)))
      (is (until #(= 1 (.size (.getQueue pool)))) "the work is queued behind the busy thread")
      (spin-core/cancel-spin! b)
      (deliver gate :go)
      (.shutdown pool)
      (is (.awaitTermination pool 5 TimeUnit/SECONDS))
      (is (false? @ran) "the queued work never ran"))))

(deftest a-pool-that-refuses-the-work-rejects-the-spin
  (with-ctx [_]
    (let [gate (promise)
          pool (ThreadPoolExecutor. 1 1 0 TimeUnit/SECONDS (SynchronousQueue.) (ThreadPoolExecutor$AbortPolicy.))
          _ (.submit pool ^Runnable (fn [] @gate))
          s (spin (try (await (blocking/blocking (fn [] :ran) {:pool pool}))
                       (catch RejectedExecutionException _ ::rejected)))]
      (is (= ::rejected (deref s 5000 ::timeout)))
      (deliver gate :go)
      (.shutdown pool))))

(deftest a-second-await-while-running-is-refused
  ;; a blocking Spin is a call: two parents of the same unfinished Spin would
  ;; run f twice; the second execution is refused instead
  (with-ctx [_]
    (let [started (promise)
          release (promise)
          calls (atom 0)
          b (blocking/blocking (fn [] (swap! calls inc) (deliver started true) (deref release 10000 :never)))
          s1 (spin (await b))
          s2 (spin (try (await b) (catch Exception e (:type (ex-data e)))))]
      (future (try @s1 (catch Throwable _ nil)))
      (is (true? (deref started 5000 false)))
      (let [r2 (deref (future (try @s2 (catch Throwable e (:type (ex-data e))))) 5000 ::timeout)]
        (deliver release :v)
        (is (= ::blocking/awaited-while-running r2)))
      (is (= 1 @calls) "f ran once"))))

(deftest done-it-reads-its-result-again
  (with-ctx [_]
    (let [calls (atom 0)
          b (blocking/blocking (fn [] (swap! calls inc)))
          s (spin [(await b) (await b)])]
      (is (= [1 1] (deref s 5000 ::timeout)))
      (is (= 1 @calls)))))

(deftest built-in-a-parent-run-in-a-fork
  (with-ctx [main]
    (let [b (blocking/blocking (fn [] 7))
          fork (ctx/fork-context main)
          s (binding [ec/*execution-context* fork] (spin (inc (await b))))]
      (is (= 8 (binding [ec/*execution-context* fork] (deref s 5000 ::timeout)))
          "the fork that runs it gets the value"))))

(deftest a-caller-runs-pool-is-refused
  (let [pool (ThreadPoolExecutor. 1 1 0 TimeUnit/SECONDS (SynchronousQueue.) (ThreadPoolExecutor$CallerRunsPolicy.))]
    (with-ctx [_]
      (is (thrown? clojure.lang.ExceptionInfo (blocking/blocking (fn [] 1) {:pool pool}))))
    (.shutdown pool)))

(deftest blocking-work-does-not-hold-the-drain
  ;; the point of the primitive: a Spin waiting on slow I/O leaves the
  ;; context's other Spins running
  (with-ctx [_]
    (let [release (promise)
          slow (spin (await (blocking/blocking #(deref release 10000 :never))))
          fast (spin (+ 1 (await (comb/sleep 10 1))))]
      (future (try @slow (catch Throwable _ nil)))
      (is (= 2 (deref fast 2000 ::stuck)) "another Spin of the context completes meanwhile")
      (deliver release :done)
      (is (= :done (deref slow 5000 ::timeout))))))

(deftest many-at-once
  (with-ctx [_]
    (let [n 200
          s (apply comb/parallel (for [i (range n)]
                                   (blocking/blocking (fn [] (Thread/sleep 50) i))))
          t0 (System/currentTimeMillis)
          r (deref s 10000 ::timeout)]
      (is (= (vec (range n)) r))
      (is (< (- (System/currentTimeMillis) t0) 5000) "they block concurrently, not one by one"))))
