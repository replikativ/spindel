(ns org.replikativ.spindel.v2.port.blocking-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture outcome wait-until]]))

(use-fixtures :each checked-fixture)

(import '[java.util.concurrent Executors RejectedExecutionException SynchronousQueue
          ThreadPoolExecutor ThreadPoolExecutor$AbortPolicy ThreadPoolExecutor$CallerRunsPolicy TimeUnit])

(def ^:dynamic *conveyed* nil)

(defn- busy-pool ^ThreadPoolExecutor [gate]
  (let [pool (Executors/newFixedThreadPool 1)]
    (.submit pool ^Runnable (fn [] @gate))
    pool))

(deftest the-value-of-f-on-a-worker-thread
  (let [host-thread (Thread/currentThread)
        worker (promise)
        s (spin (inc (await (comb/blocking (fn []
                                             (deliver worker (Thread/currentThread))
                                             41)))))]
    (is (= 42 (v2/value s 5000 ::timeout)))
    (let [thread (deref worker 5000 nil)]
      (is (some? thread))
      (is (not= host-thread thread) "f runs on a worker thread"))))

(deftest a-throw-rejects
  (do
    (let [s (spin (try (await (comb/blocking #(throw (ex-info "boom" {:code 7}))))
                       (catch Exception e (:code (ex-data e)))))]
      (is (= 7 (v2/value s 5000 ::timeout))))))

(deftest every-call-is-fresh-work
  (do
    (let [n (atom 0)
          f #(swap! n inc)
          s (spin [(await (comb/blocking f)) (await (comb/blocking f))])]
      (is (= [1 2] (v2/value s 5000 ::timeout)) "two calls of the same f run twice"))))

(deftest the-callers-bindings-are-conveyed
  (do
    (let [b (binding [*conveyed* :yes] (comb/blocking (fn [] *conveyed*)))
          s (spin (await b))]
      (is (= :yes (v2/value s 5000 ::timeout))))))

(deftest a-pool-that-refuses-the-work-rejects-the-spin
  (do
    (let [gate (promise)
          pool (ThreadPoolExecutor. 1 1 0 TimeUnit/SECONDS (SynchronousQueue.) (ThreadPoolExecutor$AbortPolicy.))
          _ (.submit pool ^Runnable (fn [] @gate))
          s (spin (try (await (comb/blocking (fn [] :ran) {:pool pool}))
                       (catch RejectedExecutionException _ ::rejected)))]
      (is (= ::rejected (v2/value s 5000 ::timeout)))
      (deliver gate :go)
      (.shutdown pool))))

(deftest done-it-reads-its-result-again
  (do
    (let [calls (atom 0)
          b (comb/blocking (fn [] (swap! calls inc)))
          s (spin [(await b) (await b)])]
      (is (= [1 1] (v2/value s 5000 ::timeout)))
      (is (= 1 @calls)))))

(deftest a-caller-runs-pool-is-refused
  (let [pool (ThreadPoolExecutor. 1 1 0 TimeUnit/SECONDS (SynchronousQueue.) (ThreadPoolExecutor$CallerRunsPolicy.))]
    (do
      (is (thrown? clojure.lang.ExceptionInfo (comb/blocking (fn [] 1) {:pool pool}))))
    (.shutdown pool)))

(deftest blocking-work-does-not-hold-the-drain
  ;; the point of the primitive: a Spin waiting on slow I/O leaves the
  ;; context's other Spins running
  (do
    (let [release (promise)
          slow (spin (await (comb/blocking #(deref release 10000 :never))))
          fast (spin (+ 1 (await (comb/sleep 10 1))))]
      (future (try @slow (catch Throwable _ nil)))
      (is (= 2 (v2/value fast 2000 ::stuck)) "another Spin of the context completes meanwhile")
      (deliver release :done)
      (is (= :done (v2/value slow 5000 ::timeout))))))

(deftest many-at-once
  (do
    (let [n 200
          s (apply comb/parallel (for [i (range n)]
                                   (comb/blocking (fn [] (Thread/sleep 50) i))))
          t0 (System/currentTimeMillis)
          r (v2/value s 10000 ::timeout)]
      (is (= (vec (range n)) r))
      (is (< (- (System/currentTimeMillis) t0) 5000) "they block concurrently, not one by one"))))

(deftest losing-a-race-interrupts-the-worker
  (let [started (v2/deferred) interrupted (promise)
        b (comb/blocking (fn []
                           (v2/deliver! started true)
                           (try (Thread/sleep 30000) :slept
                                (catch InterruptedException _ (deliver interrupted true)))))
        s (comb/race b (spin (await started) ::other-won))]
    (is (= ::other-won (v2/value s 5000 ::timeout)))
    (is (true? (deref interrupted 5000 false)))))

(deftest cancelling-interrupts-the-worker
  (let [started (promise) interrupted (promise)
        b (comb/blocking (fn [] (deliver started true)
                           (try (Thread/sleep 30000)
                                (catch InterruptedException _ (deliver interrupted true)))))
        t (task (await b))]
    (is (true? (deref started 5000 false)))
    (v2/cancel-task! t)
    (is (true? (deref interrupted 5000 false)))
    (is (v2/cancelled? (second (outcome t))))))

(deftest cancelled-while-queued-it-never-runs
  (let [ran (atom 0)]
    (dotimes [_ 1]
      (let [gate (promise) pool (busy-pool gate)
            b (comb/blocking #(swap! ran inc) {:pool pool})
            t (task (await b))]
        (try
          (is (wait-until #(= 1 (.size (.getQueue pool)))))
          (v2/cancel-task! t)
          (is (v2/cancelled? (second (outcome t))))
          (finally (deliver gate :go) (.shutdown pool)
                   (is (.awaitTermination pool 5 TimeUnit/SECONDS))))))
    (is (zero? @ran))))

(deftest repeated-queued-cancellation-never-runs-the-work
  (let [ran (atom 0)]
    (dotimes [_ 20]
      (let [gate (promise) pool (busy-pool gate)
            b (comb/blocking #(swap! ran inc) {:pool pool})
            t (task (await b))]
        (try
          (is (wait-until #(= 1 (.size (.getQueue pool)))))
          (v2/cancel-task! t)
          (is (v2/cancelled? (second (outcome t))))
          (finally (deliver gate :go) (.shutdown pool)
                   (is (.awaitTermination pool 5 TimeUnit/SECONDS))))))
    (is (zero? @ran))))

(deftest two-forks-run-it-independently
  (let [gate-a (promise) calls (atom 0)
        b (comb/blocking (fn [] (if (= 1 (swap! calls inc)) (deref gate-a 10000 :never) :b)))
        fa (v2/fork! v2/*world*) fb (v2/fork! v2/*world*)]
    (try
      (let [a-result (promise)
            stop (v2/value-async (v2/in-world fa b) (fn [v err?] (deliver a-result [v err?])))]
        (is (wait-until #(= 1 @calls)))
        (is (= :b (v2/value (v2/in-world fb b) 5000 ::timeout)))
        (deliver gate-a :a)
        (is (= [:a false] (deref a-result 5000 ::timeout)))
        (stop))
      (finally (deliver gate-a :a) (v2/release-world! fa) (v2/release-world! fb)))))

(deftest built-in-a-parent-run-in-a-fork
  (let [b (comb/blocking (fn [] 7)) child (v2/fork! v2/*world*) cb (v2/in-world child b)]
    (try
      (binding [v2/*world* child]
        (is (= 8 (v2/value (spin (inc (await cb))) 5000 ::timeout))))
      (finally (v2/release-world! child)))))
