(ns org.replikativ.spindel.blocking-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.blocking :as blocking]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]))

(def ^:dynamic *conveyed* nil)

(deftest the-value-of-f-on-a-worker-thread
  (with-ctx [_]
    (let [thread (promise)
          s (spin (inc (await (blocking/blocking (fn [] (deliver thread (Thread/currentThread)) 41)))))]
      (is (= 42 (deref s 5000 ::timeout)))
      (is (not (re-find #"spindel-drain" (.getName ^Thread @thread))) "not the drain thread")
      (when (.isVirtual ^Thread @thread)
        (is true "a virtual thread")))))

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

(deftest losing-a-timeout-interrupts-the-worker
  (with-ctx [_]
    (let [started (promise)
          interrupted (promise)
          s (comb/timeout (blocking/blocking
                           (fn []
                             (deliver started true)
                             (try (Thread/sleep 30000) :slept
                                  (catch InterruptedException _
                                    (deliver interrupted true)
                                    :interrupted))))
                          1000 ::fallback)]
      (future (try @s (catch Throwable _ nil)))
      (is (true? (deref started 5000 false)) "the worker started before the deadline")
      (is (= ::fallback (deref s 5000 ::timeout)))
      (is (true? (deref interrupted 5000 false)) "the worker was interrupted"))))

(deftest cancelled-before-it-starts-it-never-runs
  ;; a pool with its one thread busy keeps the work queued
  (with-ctx [_]
    (let [pool (java.util.concurrent.Executors/newFixedThreadPool 1)
          gate (promise)
          ran (atom false)
          _ (.submit pool ^Runnable (fn [] @gate))
          b (blocking/blocking #(reset! ran true) {:pool pool})
          s (spin (await b))]
      (future (try @s (catch Throwable _ nil)))
      (Thread/sleep 200)
      (spin-core/cancel-spin! b)
      (Thread/sleep 100)
      (deliver gate :go)
      (Thread/sleep 300)
      (is (false? @ran) "the queued work was cancelled, not run")
      (.shutdown pool))))

(deftest two-waiters-share-one-run
  (with-ctx [_]
    (let [calls (atom 0)
          release (promise)
          b (blocking/blocking (fn [] (swap! calls inc) (deref release 10000 :never)))
          s1 (spin (await b))
          s2 (spin (await b))]
      (future (try @s1 (catch Throwable _ nil)))
      (future (try @s2 (catch Throwable _ nil)))
      (Thread/sleep 200)
      (deliver release :v)
      (is (= [:v :v] [(deref s1 5000 ::timeout) (deref s2 5000 ::timeout)]))
      (is (= 1 @calls) "f ran once"))))

(deftest cancelling-through-one-awaiter-cancels-the-shared-spin
  ;; the engine's structured cancellation: a parent that is cancelled cancels
  ;; the Spin it awaits, for every awaiter of it, and the worker stops
  (with-ctx [_]
    (let [interrupted (promise)
          b (blocking/blocking (fn [] (try (Thread/sleep 30000)
                                           (catch InterruptedException _ (deliver interrupted true)))))
          s1 (comb/timeout (spin (await b)) 300 ::gave-up)
          s2 (spin (try (await b) (catch Exception e (:type (ex-data e)))))]
      (future (try @s2 (catch Throwable _ nil)))
      (is (= ::gave-up (deref s1 5000 ::timeout)))
      (is (true? (deref interrupted 5000 false)))
      (is (= spin-core/spin-cancelled (deref s2 5000 ::timeout))))))

(deftest built-in-a-parent-run-in-a-fork
  (with-ctx [main]
    (let [b (blocking/blocking (fn [] 7))
          fork (ctx/fork-context main)
          s (binding [ec/*execution-context* fork] (spin (inc (await b))))]
      (is (= 8 (binding [ec/*execution-context* fork] (deref s 5000 ::timeout)))
          "the fork that runs it gets the value"))))

(deftest a-caller-runs-pool-is-refused
  (let [pool (java.util.concurrent.ThreadPoolExecutor.
              1 1 0 java.util.concurrent.TimeUnit/SECONDS
              (java.util.concurrent.SynchronousQueue.)
              (java.util.concurrent.ThreadPoolExecutor$CallerRunsPolicy.))]
    (with-ctx [_]
      (is (thrown? clojure.lang.ExceptionInfo (blocking/blocking (fn [] 1) {:pool pool}))))
    (.shutdown pool)))

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
          s (apply comb/parallel (vec (for [i (range n)]
                                  (blocking/blocking (fn [] (Thread/sleep 50) i)))))
          t0 (System/currentTimeMillis)
          r (deref s 10000 ::timeout)]
      (is (= (vec (range n)) r))
      (is (< (- (System/currentTimeMillis) t0) 5000) "they block concurrently, not one by one"))))
