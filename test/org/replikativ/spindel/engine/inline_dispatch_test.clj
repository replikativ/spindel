(ns org.replikativ.spindel.engine.inline-dispatch-test
  "executor/dispatch!, run-framed!, call-unframed and spread!: engine work that
  becomes ready on a thread already running an executor's work stays on that
  thread; explicit fan-out spreads over the executor's threads."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.fault :as fault]
            [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.spin.cps :refer [spin]]))

(defn- counting
  "An executor delegating to `base` that counts its tasks."
  [base hops]
  (reify ex/PExecutor
    (execute! [_ f] (swap! hops inc) (ex/execute! base f))
    (execute-after! [_ d f] (ex/execute-after! base d f))))

(defn- on-executor
  "Run `f` as a task of `executor` (in a frame) and wait for its value."
  [executor f]
  (let [p (promise)]
    (ex/dispatch! executor #(deliver p (try (f) (catch Throwable t t))))
    (deref p 5000 ::timeout)))

(deftest dispatch-outside-a-frame-goes-to-the-executor
  (let [hops (atom 0)
        e (counting (ex/default-executor) hops)
        here (Thread/currentThread)
        there (on-executor e #(Thread/currentThread))]
    (is (= 1 @hops))
    (is (not (identical? here there)))))

(deftest dispatch-inside-a-frame-runs-after-the-current-task-on-its-thread
  (let [hops (atom 0)
        e (counting (ex/default-executor) hops)
        log (atom [])
        p (promise)]
    (ex/dispatch! e (fn []
                      (let [t (Thread/currentThread)]
                        (ex/dispatch! e (fn []
                                          (swap! log conj [:queued (identical? t (Thread/currentThread))])
                                          (deliver p true)))
                        (swap! log conj [:current-done]))))
    (is (true? (deref p 5000 ::timeout)))
    (is (= [[:current-done] [:queued true]] @log))
    (is (= 1 @hops) "only the first dispatch left the calling thread")))

(deftest a-long-chain-neither-grows-the-stack-nor-keeps-one-task
  (let [hops (atom 0)
        e (counting (ex/default-executor) hops)
        n 20000
        depths (atom #{})
        p (promise)]
    (letfn [(step [i]
              (swap! depths conj (count (.getStackTrace (Thread/currentThread))))
              (if (= i n)
                (deliver p i)
                (ex/dispatch! e #(step (inc i)))))]
      (ex/dispatch! e #(step 0)))
    (is (= n (deref p 10000 ::timeout)))
    (is (< (- (apply max @depths) (apply min @depths)) 50) "constant stack depth")
    (testing "the chain is handed back to the executor every 256 tasks"
      (is (< 1 @hops (inc (quot n 200)))))))

(defn- with-faults
  "Call `f` with engine faults collected; returns [result faults]."
  [f]
  (let [faults (atom [])
        before (fault/current-fault-reporter)]
    (fault/set-fault-reporter! (fn [event data] (swap! faults conj [event data])))
    (try [(f) faults]
         (finally (fault/set-fault-reporter! before)))))

(deftest every-failing-task-is-reported-and-the-queue-still-runs
  (let [e (ex/default-executor)
        p (promise)
        [ran faults] (with-faults
                       (fn []
                         (ex/dispatch! e (fn []
                                           (ex/dispatch! e #(throw (ex-info "second" {})))
                                           (ex/dispatch! e #(deliver p :ran))
                                           (throw (ex-info "first" {}))))
                         (deref p 5000 ::timeout)))]
    (is (= :ran ran))
    (Thread/sleep 50)
    (is (= #{"first" "second"} (set (map (comp ex-message :error second) @faults))))))

(deftest an-interrupt-in-a-queued-task-is-reported-and-restored
  (let [e (ex/synchronous-executor)
        flags (atom [])
        [_ faults] (with-faults
                     (fn []
                       (ex/run-framed! e (fn []
                                           (ex/dispatch! e #(throw (InterruptedException. "x")))
                                           (ex/dispatch! e #(swap! flags conj (Thread/interrupted)))))))]
    (is (= [true] @flags) "the flag survives into the next task")
    (is (= [true] (map (comp :interrupted? second) @faults)))))

(deftest a-synchronous-executor-pumps-long-chains-without-nesting
  (let [e (ex/synchronous-executor)
        n 5000
        depths (atom [])]
    (ex/run-framed! e (fn []
                        (letfn [(step [i]
                                  (swap! depths conj (count (.getStackTrace (Thread/currentThread))))
                                  (when (< i n) (ex/dispatch! e #(step (inc i)))))]
                          (step 0))))
    (is (= (inc n) (count @depths)))
    (is (< (- (apply max @depths) (apply min @depths)) 50))))

(deftest a-refused-handoff-keeps-the-tail-here
  (let [refusing (reify ex/PExecutor
                   (execute! [_ _] (throw (java.util.concurrent.RejectedExecutionException. "full")))
                   (execute-after! [_ _ _] nil))
        ran (atom 0)
        [_ faults] (with-faults
                     (fn []
                       (ex/run-framed! refusing (fn []
                                                  (dotimes [_ 600]
                                                    (ex/dispatch! refusing #(swap! ran inc)))))))]
    (is (= 600 @ran))
    (is (seq (filter (comp :handoff-rejected? second) @faults)))))

(deftest another-executor-is-not-run-inline
  (let [hops (atom 0)
        a (ex/default-executor)
        b (counting (ex/default-executor) hops)
        p (promise)]
    (ex/dispatch! a (fn [] (ex/dispatch! b #(deliver p (Thread/currentThread)))))
    (is (instance? Thread (deref p 5000 ::timeout)))
    (is (= 1 @hops))))

(deftest call-unframed-hands-queued-work-to-the-executor
  (testing "a blocking wait on work already queued in this frame"
    (let [e (ex/default-executor)
          result (on-executor e (fn []
                                  (let [p (promise)]
                                    (ex/dispatch! e #(deliver p :done))
                                    (ex/call-unframed #(deref p 5000 ::timeout)))))]
      (is (= :done result)))))

(deftest a-deref-of-a-running-spin-whose-continuation-is-queued-here
  (testing "resume queues the continuation in this frame; @ then waits for it"
    (let [e (ex/default-executor)
          world (ctx/create-execution-context :executor e)
          parked (promise)
          _ (sp/open! world {:purpose :test :seed 1 :fork-opts {:systems :none}
                             :handlers {:x #(deliver parked %)}})
          s (binding [ec/*execution-context* world]
              (spin (+ 1 (sp/savepoint :x 0))))
          started (future (binding [ec/*execution-context* world] (deref s 5000 ::timeout)))
          p (deref parked 5000 ::timeout)]
      (is (not= ::timeout p))
      (is (= 42 (on-executor e (fn []
                                 (sp/resume p 41)
                                 (binding [ec/*execution-context* world]
                                   (deref s 5000 ::timeout))))))
      (is (= 42 (deref started 5000 ::timeout))))))

(deftest call-unframed-sends-dispatches-to-the-executor
  (let [hops (atom 0)
        e (counting (ex/default-executor) hops)
        result (on-executor e (fn []
                                (let [before @hops
                                      p (promise)]
                                  ;; blocking on work dispatched from a frame
                                  ;; is only safe unframed
                                  (ex/call-unframed #(ex/dispatch! e (fn [] (deliver p :done))))
                                  [(deref p 5000 ::timeout) (- @hops before)])))]
    (is (= [:done 1] result))))

(deftest spread-runs-every-index-once-over-several-threads
  (let [e (ex/default-executor)
        n 64
        seen (atom {})
        latch (java.util.concurrent.CountDownLatch. n)]
    (ex/spread! e n (fn [i]
                      ;; long enough that the shares overlap
                      (Thread/sleep 5)
                      (swap! seen update i (fnil conj []) (Thread/currentThread))
                      (.countDown latch))
                4)
    (is (.await latch 10 java.util.concurrent.TimeUnit/SECONDS))
    (is (= (set (range n)) (set (keys @seen))))
    (is (every? #(= 1 (count %)) (vals @seen)))
    (is (= 4 (count (into #{} (mapcat val) @seen))) "one thread per share")))

(deftest spread-isolates-a-failing-index
  (let [e (ex/default-executor)
        seen (atom #{})
        latch (java.util.concurrent.CountDownLatch. 3)
        [_ faults] (with-faults
                     (fn []
                       (ex/spread! e 4 (fn [i]
                                         (when (zero? i) (throw (ex-info "index 0" {})))
                                         (swap! seen conj i)
                                         (.countDown latch))
                                   2)
                       (.await latch 5 java.util.concurrent.TimeUnit/SECONDS)))]
    (is (= #{1 2 3} @seen))
    (is (= ["index 0"] (map (comp ex-message :error second) @faults)))))

(deftest spread-with-fewer-tasks-than-shares
  (let [e (ex/default-executor)
        seen (atom [])
        latch (java.util.concurrent.CountDownLatch. 2)]
    (ex/spread! e 2 (fn [i] (swap! seen conj i) (.countDown latch)) 8)
    (is (.await latch 5 java.util.concurrent.TimeUnit/SECONDS))
    (is (= #{0 1} (set @seen)))
    (ex/spread! e 0 (fn [_] (throw (ex-info "never" {}))))))

(deftest a-blocking-deref-inside-a-frame-does-not-deadlock
  (let [e (ex/default-executor)
        world (ctx/create-execution-context :executor e)
        result (on-executor e (fn []
                                (binding [ec/*execution-context* world]
                                  @(spin (+ 1 2)))))]
    (is (= 3 result))))

(deftest a-savepoint-run-leaves-the-calling-thread-once
  (testing "start, savepoint resume and completion run on one executor task"
    (let [hops (atom 0)
          e (counting (ex/default-executor) hops)
          world (ctx/create-execution-context)
          task (binding [ec/*execution-context* world]
                 (spin (+ 1 (sp/savepoint :x 41))))
          root (ctx/create-execution-context :executor e)
          s (sp/open! root {:purpose :test :seed 1 :fork-opts {:systems :none}})
          p (promise)]
      ((trace/run s task (fn [sp _] {:value (:savepoint/payload sp) :note {}}) {})
       #(deliver p %) #(deliver p %))
      (let [t (deref p 5000 ::timeout)]
        (is (= 42 (:trace/result t)))
        (is (= 1 @hops)))
      (let [closed (promise)]
        ((sp/close! s) #(deliver closed %) #(deliver closed %))
        (deref closed 5000 ::timeout)))))

(deftest a-refused-blocking-handoff-runs-the-queued-work-here-first
  (let [refusing (reify ex/PExecutor
                   (execute! [_ _] (throw (java.util.concurrent.RejectedExecutionException. "full")))
                   (execute-after! [_ _ _] nil))
        result (atom nil)]
    (with-faults
      (fn []
        (ex/run-framed! refusing (fn []
                                   (let [p (promise)]
                                     (ex/dispatch! refusing #(deliver p :done))
                                     (reset! result (ex/call-unframed #(deref p 1000 ::timeout))))))))
    (is (= :done @result))))

(deftest a-deref-that-does-not-wait-hands-nothing-over
  (let [hops (atom 0)
        e (counting (ex/default-executor) hops)
        world (ctx/create-execution-context :executor e)
        s (binding [ec/*execution-context* world] (spin (+ 1 2)))
        _ (binding [ec/*execution-context* world] (deref s 5000 ::timeout))
        result (on-executor e (fn []
                                (let [before @hops]
                                  (ex/dispatch! e (fn []))
                                  (binding [ec/*execution-context* world]
                                    [@s (- @hops before)]))))]
    (is (= [3 0] result) "a cached deref leaves the queued task where it is")))

(deftest a-wrapper-declaring-inline-execution-pumps-locally
  (let [base (ex/synchronous-executor)
        wrapper (reify
                  ex/PExecutor
                  (execute! [_ f] (ex/execute! base f))
                  (execute-after! [_ d f] (ex/execute-after! base d f))
                  ex/PRunsInline
                  (runs-inline? [_] true))
        n 2000
        depths (atom [])]
    (ex/run-framed! wrapper (fn []
                              (letfn [(step [i]
                                        (swap! depths conj (count (.getStackTrace (Thread/currentThread))))
                                        (when (< i n) (ex/dispatch! wrapper #(step (inc i)))))]
                                (step 0))))
    (is (= (inc n) (count @depths)))
    (is (< (- (apply max @depths) (apply min @depths)) 50))))
