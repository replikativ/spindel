(ns org.replikativ.spindel.enum-bench
  "One root per 100k walk. No retained handles after each completed cycle."
  (:require [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.lifetime-gate-rules :as rules]
            [org.replikativ.spindel.lifetime-load-monitor :as load]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.yggdrasil :as ygg]))

(defn census [rt]
  (if-not rt {}
          (assoc (into {} (for [path (remove #{[:following-worlds-live]} rules/census-paths)] [path (count (rtp/get-state rt path))]))
                 [:following-worlds-live] (if (ec/following-forks? rt) 1 0))))

(defn gc-count []
  (reduce + (map #(max 0 (.getCollectionCount ^java.lang.management.GarbageCollectorMXBean %))
                 (java.lang.management.ManagementFactory/getGarbageCollectorMXBeans))))

(defn drain-keyword-interns! []
  ;; A fresh intern expunges cleared weak entries in Clojure's global table.
  ;; One fresh intern after clearing weak references, as in the causal control.
  (clojure.lang.Keyword/intern (str "spindel-bench-drain-" (java.util.UUID/randomUUID))))

(defn stabilize-gc! [rt]
  (let [start (System/nanoTime) empty-paths (if rt rules/required-empty #{})]
    (loop [observations []]
      (let [before (gc-count)
            _ (System/gc)
            _ (Thread/sleep (get-in rules/measurement-protocol [:gc :sample-pause-ms]))
            after (gc-count)
            runtime (Runtime/getRuntime)
            counts (census rt)
            elapsed (/ (- (System/nanoTime) start) 1e6)
            observation {:gc-before before :gc-after after :gc-completed? (> after before)
                         :elapsed-ms elapsed :heap-bytes (- (.totalMemory runtime) (.freeMemory runtime))
                         :census counts}
            observations (conj observations observation)
            stable? (rules/stable-observations? observations empty-paths)
            cleanup? (every? #(zero? (get counts % -1)) empty-paths)]
        (if (or stable? (>= elapsed (get-in rules/measurement-protocol [:gc :deadline-ms])))
          {:retained-bytes (:heap-bytes observation) :gc-stable? (boolean stable?)
           :gc-completed? (every? :gc-completed? (take-last 3 observations))
           :cleanup-complete? cleanup? :expected-empty empty-paths
           :gc-wait-ms elapsed :census counts :observations observations
           :stabilisation (if stable? :stable :deadline)}
          (recur observations))))))

(defn full-gc! [rt]
  ;; First finish ordinary GC/engine cleanup so dead keywords have cleared.
  ;; Then perform exactly the attribution's causal control and stabilize again.
  (let [before (stabilize-gc! rt)]
    (drain-keyword-interns!)
    (assoc (stabilize-gc! rt) :keyword-intern-drained? true :pre-intern-gc before)))

(defn cycle! [kind i]
  (case kind
    :spin @(spin i)
    :fork (let [h (ygg/fork! {:systems :none :sync? true})]
            (binding [ec/*execution-context* (:child-ctx h)] @(spin i))
            (ygg/discard-fork! h {:sync? true}))))

(defn run-one [kind]
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
    (try
      (binding [ec/*execution-context* rt cps/*in-trampoline* false]
        (loop [from 0 points []]
          (if-let [to (first (drop (count points) [10000 100000]))]
            (let [elapsed (binding [load/*window* (pr-str [:enumeration kind from to])]
                            (load/timed #(let [start (System/nanoTime)]
                                           (doseq [i (range from to)] (cycle! kind i))
                                           (- (System/nanoTime) start))))]
              (let [point (merge {:cycles to :segment-cycles (- to from)
                                  :elapsed-ns elapsed
                                  :cycles-per-second (/ (* 1e9 (- to from)) elapsed)} (full-gc! rt))]
                (prn {:enumeration kind :point point}) (flush)
                (recur to (conj points point))))
            {:kind kind :points points
             :cycles-per-second (/ 1e14 (reduce + (map :elapsed-ns points)))})))
      (finally (ctx/close-context! rt)))))

(defn warm-shape! [kind]
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
    (try
      (binding [ec/*execution-context* rt cps/*in-trampoline* false]
        (dotimes [i (get-in rules/measurement-protocol [:enumeration :warmup])] (cycle! kind i)))
      (finally (ctx/close-context! rt))))
  (full-gc! nil))

(defn benchmark []
  (doseq [kind [:fork :spin]] (warm-shape! kind))
  (mapv run-one [:fork :spin]))
(defn -main [& _] (benchmark) (shutdown-agents))
