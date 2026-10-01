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

(deftest a-second-await-restarts-the-work
  ;; the engine re-runs a resource Spin's body for a second awaiter: the
  ;; first worker is interrupted, f runs again, and the Spin completes once
  (with-ctx [_]
    (let [first-started (promise)
          first-interrupted (promise)
          calls (atom 0)
          after-await (atom {:a 0 :b 0})
          b (blocking/blocking
             (fn []
               (let [n (swap! calls inc)]
                 (if (= 1 n)
                   (do (deliver first-started true)
                       (try (Thread/sleep 30000) :first
                            (catch InterruptedException _ (deliver first-interrupted true) :first-interrupted)))
                   :second))))
          s1 (spin (let [v (await b)] (swap! after-await update :a inc) v))
          s2 (spin (let [v (await b)] (swap! after-await update :b inc) v))]
      (future (try @s1 (catch Throwable _ nil)))
      (is (true? (deref first-started 5000 false)))
      (is (= :second (deref s2 5000 ::timeout)))
      (is (= :second (deref s1 5000 ::timeout)) "both awaiters see the one completion")
      (is (true? (deref first-interrupted 5000 false)) "the superseded worker was interrupted")
      (Thread/sleep 200)
      (is (= {:a 1 :b 1} @after-await) "each parent continued exactly once")
      (is (= 2 @calls)))))

(deftest repeated-queued-cancellation-leaves-no-tokens
  ;; a fresh busy pool per round: a queue of one is this round's work
  (with-ctx [c]
    (let [tokens #(count (binding [ec/*execution-context* c] (ec/get-state [:engine/cancelled-tokens])))]
      (dotimes [_ 20]
        (let [gate (promise)
              pool (busy-pool gate)
              b (blocking/blocking (fn [] :never) {:pool pool})
              s (spin (await b))]
          (future (try @s (catch Throwable _ nil)))
          (is (until #(= 1 (.size (.getQueue pool)))))
          (spin-core/cancel-spin! b)
          (deliver gate :go)
          (.shutdown pool)))
      (is (until #(zero? (tokens))) "every cancelled reader was retired"))))

(deftest a-queued-restart-leaves-no-tokens
  ;; a second awaiter supersedes a still-queued first execution
  (with-ctx [c]
    (let [tokens #(count (binding [ec/*execution-context* c] (ec/get-state [:engine/cancelled-tokens])))
          gate (promise)
          pool (busy-pool gate)
          b (blocking/blocking (fn [] :ran) {:pool pool})
          s1 (spin (await b))
          s2 (spin (await b))]
      (future (try @s1 (catch Throwable _ nil)))
      (is (until #(= 1 (.size (.getQueue pool)))))
      (future (try @s2 (catch Throwable _ nil)))
      (Thread/sleep 100)
      (deliver gate :go)
      (is (= :ran (deref s2 5000 ::timeout)))
      (is (= :ran (deref s1 5000 ::timeout)))
      (is (until #(zero? (tokens))) "the superseded execution's reader was retired")
      (.shutdown pool))))

(deftest two-forks-run-it-independently
  (with-ctx [main]
    (let [gate-a (promise)
          calls (atom 0)
          b (blocking/blocking (fn [] (if (= 1 (swap! calls inc)) (deref gate-a 10000 :never) :b)))
          fa (ctx/fork-context main)
          fb (ctx/fork-context main)
          sa (binding [ec/*execution-context* fa] (spin (await b)))
          sb (binding [ec/*execution-context* fb] (spin (await b)))]
      (future (binding [ec/*execution-context* fa] (try @sa (catch Throwable _ nil))))
      (is (until #(= 1 @calls)) "fork A's work started")
      (is (= :b (binding [ec/*execution-context* fb] (deref sb 5000 ::timeout))) "fork B ran its own")
      (deliver gate-a :a)
      (is (= :a (binding [ec/*execution-context* fa] (deref sa 5000 ::timeout)))
          "fork A was not cancelled by fork B"))))

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
