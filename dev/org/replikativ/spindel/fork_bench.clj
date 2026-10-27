(ns org.replikativ.spindel.fork-bench
  "Fork+discard cost with retained live siblings and a populated parent."
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.yggdrasil :as ygg])
  (:import [java.lang.management ManagementFactory]
           [com.sun.management ThreadMXBean]))

(defn measure [n f]
  (let [^ThreadMXBean bean (ManagementFactory/getThreadMXBean)
        tid (.getId (Thread/currentThread))]
    (.setThreadAllocatedMemoryEnabled bean true)
    (let [bytes (.getThreadAllocatedBytes bean tid) start (System/nanoTime)]
      (dotimes [i n] (f i))
      {:operations n :ns-per-op (/ (double (- (System/nanoTime) start)) n)
       :bytes-per-op (/ (double (- (.getThreadAllocatedBytes bean tid) bytes)) n)})))

(defn fork-discard! [_]
  (let [h (ygg/fork! {:systems :none :sync? true})]
    (ygg/discard-fork! h {:sync? true})))

(defn run-one [live-worlds entities parked n]
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
    (try
      (binding [ec/*execution-context* rt cps/*in-trampoline* false]
        ;; Keep all handles strongly reachable through measurement. This is the
        ;; number of live worlds, not the number of worlds ever allocated.
        (let [signals (mapv (fn [i] (let [s (sig/signal i)] (sig/get-signal-value s) s)) (range (- entities (* 2 parked))))
              blocked (mapv (fn [_]
                              (let [d (sync/deferred) s (spin (await d))]
                                (s identity #(throw %))
                                [d s])) (range parked))
              siblings (mapv (fn [_] (ygg/fork! {:systems :none :sync? true})) (range live-worlds))]
          (try
            (assert (= entities (+ (count (rtp/get-state rt [:nodes]))
                                   (count (rtp/get-state rt [:atoms])))))
            (assert (= parked (count (filter :running? (vals (rtp/get-state rt [:nodes]))))))
            (dotimes [i 200] (fork-discard! i))
            (let [measured (measure n fork-discard!)]
              (java.lang.ref.Reference/reachabilityFence signals)
              (java.lang.ref.Reference/reachabilityFence blocked)
              (java.lang.ref.Reference/reachabilityFence siblings)
              (assoc measured
                     :node-rows (count (rtp/get-state rt [:nodes]))
                     :atom-rows (count (rtp/get-state rt [:atoms]))
                     :live-worlds live-worlds :entities entities :parked-runs parked
                     :retained-fixture (+ (count signals) (count blocked) (count siblings))))
            (finally
              (doseq [h siblings] (ygg/discard-fork! h {:sync? true}))))))
      (finally (ctx/close-context! rt)))))

(defn benchmark []
  (mapv (fn [[worlds entities parked]]
          (let [r (run-one worlds entities parked 1000)] (prn r) (flush) r))
        [[1000 0 0] [5000 0 0] [1000 10000 1000]]))

(defn -main [& _] (benchmark) (shutdown-agents))
