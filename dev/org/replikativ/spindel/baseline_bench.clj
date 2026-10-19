(ns org.replikativ.spindel.baseline-bench
  "Run: clojure -J-Xmx3g -M:bench -m org.replikativ.spindel.baseline-bench
   Honor the shared-machine JVM lock before invoking. Timing/allocation use an
   unwrapped backend; a separate identical run counts backend calls. Root swaps
   are one write at [], not attributed to hidden subpaths. CAS in ExecutionContext
   bypasses PStateBackend and is excluded. Allocation is calling-thread bytes;
   all measured propagation uses the synchronous executor on that thread."
  (:refer-clojure :exclude [await])
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.statemachine.counting-backend :as cb])
  (:import [java.lang.management ManagementFactory]
           [com.sun.management ThreadMXBean]))

(defn graph [kind a]
  (case kind
    :B1 (mapv (fn [_] (spin (iv/get-new (track a)))) (range 100))
    :B2 (let [head (spin (iv/get-new (track a)))]
          [(reduce (fn [prev _] (spin (inc (await prev)))) head (range 50))])
    :B3 (let [b (spin (* 2 (iv/get-new (track a))))
              c (spin (* 3 (iv/get-new (track a))))
              d (spin (+ (await b) (await c)))
              e (spin (* 2 (await d)))
              f (spin (* 3 (await d)))
              g (spin (+ (await e) (await f)))]
          [d g])))

(defn exercise! [a n]
  (dotimes [_ n] (swap! a inc)))

(defn run-one [kind n warmup counted?]
  (let [base (ctx/create-execution-context :executor (ex/synchronous-executor))
        [rt counts] (if counted? (cb/instrument base) [base nil])
        ^ThreadMXBean bean (ManagementFactory/getThreadMXBean)
        tid (.getId (Thread/currentThread))]
    (when-not (.isThreadAllocatedMemorySupported bean)
      (throw (ex-info "Thread allocation counters unavailable" {})))
    (.setThreadAllocatedMemoryEnabled bean true)
    (try
      (binding [ec/*execution-context* rt cps/*in-trampoline* false]
        (let [a (sig/signal 0)
              roots (graph kind a)]
          (doseq [s roots] @s)
          (exercise! a warmup)
          (when counts (reset! counts {}))
          (let [bytes (.getThreadAllocatedBytes bean tid)
                start (System/nanoTime)]
            (exercise! a n)
            (let [elapsed (- (System/nanoTime) start)
                  allocated (- (.getThreadAllocatedBytes bean tid) bytes)
                  counters (when counts @counts)
                  values (mapv deref roots)
                  expected (case kind
                             :B1 (vec (repeat 100 (+ n warmup)))
                             :B2 [(+ n warmup 50)]
                             :B3 [(* 5 (+ n warmup)) (* 25 (+ n warmup))])]
              {:consistent? (= expected values)
               :observed values :expected expected
               :ns-per-op (/ (double elapsed) n)
               :bytes-per-op (/ (double allocated) n)
               :calls-per-op (when counters
                               (into {} (map (fn [[op paths]]
                                               [op (into {} (map (fn [[p c]] [p (/ (double c) n)]) paths))]) counters)))}))))
      (finally (ctx/close-context! rt)))))

(defn benchmark [kind n warmup]
  (let [timing (run-one kind n warmup false)
        counted (run-one kind n warmup true)
        paths (:calls-per-op counted)]
    {:benchmark kind :operations n :warmup warmup
     :consistent? (and (:consistent? timing) (:consistent? counted))
     :observed (:observed timing) :expected (:expected timing)
     :ns-per-op (:ns-per-op timing) :bytes-per-op (:bytes-per-op timing)
     :reads-per-op (reduce + 0 (vals (:reads paths)))
     :writes-per-op (reduce + 0 (vals (:writes paths)))
     ;; Actual state transitions include context CAS that bypasses the API.
     :commits-per-op (get-in paths [:atom-commits []] 0)
     :context-cas-commits-per-op (- (get-in paths [:atom-commits []] 0)
                                    (get-in paths [:commits []] 0))
     :paths-per-op paths}))

(defn -main [& [output]]
  (let [n (Long/parseLong (System/getProperty "spindel.bench.ops" "10000"))
        warmup (Long/parseLong (System/getProperty "spindel.bench.warmup" "500"))
        output (or output "/tmp/claude-1000/-home-christian-weilbach-Development-spindel/9901311f-e8f8-4999-9f8c-4b480d4aeb2d/scratchpad/step0/bench.edn")
        metadata {:java (System/getProperty "java.version")
                  :revision (str/trim (:out (shell/sh "git" "rev-parse" "HEAD")))
                  :max-heap-bytes (.maxMemory (Runtime/getRuntime))
                  :processors (.availableProcessors (Runtime/getRuntime))
                  :allocation :calling-thread :executor :synchronous
                  :counter-scope :backend-api-calls-excluding-context-cas}
        results (mapv (fn [kind]
                        (let [r (benchmark kind n warmup)]
                          (prn r) (flush) r)) [:B1 :B2 :B3])
        report (assoc metadata :results results)]
    (io/make-parents output)
    (spit output (str (pr-str report) "\n"))
    (prn {:output output})
    (shutdown-agents)))
