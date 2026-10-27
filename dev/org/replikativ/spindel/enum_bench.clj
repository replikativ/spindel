(ns org.replikativ.spindel.enum-bench
  "One root per 100k walk. No retained handles after each completed cycle."
  (:require [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.yggdrasil :as ygg]))

(declare census)

(defn full-gc! [rt]
  ;; GC and Cleaner dispatch are asynchronous. A fixed short sleep measures the
  ;; callback backlog rather than retention at 100k. Require stable table counts
  ;; across three further collections; report a timeout as invalid measurement.
  (let [start (System/nanoTime)]
    (dotimes [_ 3] (System/gc) (Thread/sleep 200))
    (loop [previous (census rt) stable 0]
      (System/gc)
      (Thread/sleep 500)
      (let [counts (census rt)
            stable (if (= previous counts) (inc stable) 0)
            elapsed (/ (- (System/nanoTime) start) 1e6)]
        (if (or (>= stable 3) (>= elapsed 30000))
          (let [runtime (Runtime/getRuntime)]
            {:retained-bytes (- (.totalMemory runtime) (.freeMemory runtime))
             :gc-stable? (>= stable 3) :gc-wait-ms elapsed :census counts})
          (recur counts stable))))))

(defn cycle! [kind i]
  (case kind
    :spin @(spin i)
    :fork (let [h (ygg/fork! {:systems :none :sync? true})]
            (binding [ec/*execution-context* (:child-ctx h)] @(spin i))
            (ygg/discard-fork! h {:sync? true}))))

(defn census [rt]
  (into {} (for [path [:nodes :atoms :await-conts :track-subscriptions :subscriptions :spin-tracking :incremental]]
             [path (count (rtp/get-state rt [path]))])))

(defn run-one [kind]
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
    (try
      (binding [ec/*execution-context* rt cps/*in-trampoline* false]
        (loop [from 0 points []]
          (if-let [to (first (drop (count points) [10000 100000]))]
            (let [start (System/nanoTime)]
              (doseq [i (range from to)] (cycle! kind i))
              (let [elapsed (- (System/nanoTime) start)
                    point (merge {:cycles to :segment-cycles (- to from)
                                  :elapsed-ns elapsed
                                  :cycles-per-second (/ (* 1e9 (- to from)) elapsed)} (full-gc! rt))]
                (prn {:enumeration kind :point point}) (flush)
                (recur to (conj points point))))
            {:kind kind :points points
             :cycles-per-second (/ 1e14 (reduce + (map :elapsed-ns points)))})))
      (finally (ctx/close-context! rt)))))

(defn benchmark [] (mapv run-one [:fork :spin]))
(defn -main [& _] (benchmark) (shutdown-agents))
