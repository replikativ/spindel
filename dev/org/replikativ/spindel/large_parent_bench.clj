(ns org.replikativ.spindel.large-parent-bench
  "Focused MULT control, adapted from impl/perf/artifacts/mult-probe.clj.
   Parent and operation handles stay alive; construction/reclamation are untimed."
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.spin.core :as sc]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.fork-bench :as bench]
            [org.replikativ.spindel.enum-bench :as enumeration]
            [org.replikativ.spindel.lifetime-gate-rules :as rules]))

(defn fresh-spin [i] (spin (+ i 1)))
(defn awaiting-spin [s] (spin (await s)))

(defn run-batch [world path n]
  (binding [ec/*execution-context* world cps/*in-trampoline* false]
    (let [children (mapv fresh-spin (range n))
          parents (when (= path :uncached-await) (mapv awaiting-spin children))
          results (long-array n)
          work (or parents children)
          f (case path
              :uncached-await (fn [i] (aset results i (long @(nth work i))))
              :execution-event (fn [i]
                                 (let [s (nth work i)]
                                   (simple/process-event! world
                                                          {:type :spin-execution :id (sc/spin-id s) :spin s
                                                           :resolve-fn #(aset results i (long %)) :reject-fn #(throw %)}))))
          nodes-at-start (count (rtp/get-state world [:nodes]))
          cpu (java.lang.management.ManagementFactory/getThreadMXBean)
          _ (.setThreadCpuTimeEnabled cpu true)
          before (.getCurrentThreadCpuTime cpu)
          r (bench/measure n f)
          cpu-ns (- (.getCurrentThreadCpuTime cpu) before)
          checksum (reduce + results)]
      (assert (= (reduce + (range 1 (inc n))) checksum))
      (java.lang.ref.Reference/reachabilityFence children)
      (java.lang.ref.Reference/reachabilityFence parents)
      (doseq [s (concat parents children)] (simple/full-cleanup-spin! world (sc/spin-id s)))
      (assoc r :cpu-ns-per-op (/ (double cpu-ns) n)
             :nodes-at-start nodes-at-start :checksum checksum))))

(defn sample [mode path population shape-warmup?]
  (let [root (ctx/create-execution-context :executor (ex/synchronous-executor))]
    (try
      (binding [ec/*execution-context* root cps/*in-trampoline* false]
        (let [handles (mapv (fn [i] (let [s (fresh-spin i)] @s s)) (range population))
              _ (assert (= population (count (rtp/get-state root [:nodes]))))
              world (if (= mode :root) root (ctx/fork-context root :mode mode))]
          (try
            (run-batch world path 300)
            (enumeration/full-gc! nil)
            (let [r (assoc (run-batch world path 300)
                           :mode mode :path path :parent-nodes population :shape-warmup? shape-warmup?)]
              (assert (= population (count (rtp/get-state root [:nodes]))))
              (java.lang.ref.Reference/reachabilityFence handles)
              r)
            (finally (when-not (identical? world root) (ctx/close-context! world))))))
      (finally (ctx/close-context! root)))))

(defn warm-shapes! []
  ;; Preserve the attribution's eight-shape prewarm, including empty-root controls.
  (doseq [population [0 10000]
          mode (if (zero? population) [:root] [:root :following :frozen])
          path [:uncached-await :execution-event]]
    (sample mode path population true)))

(defn benchmark []
  (warm-shapes!)
  (mapv (fn [[mode path]]
          (let [samples (vec (repeatedly 3 #(sample mode path 10000 false)))
                row (assoc (second (sort-by :ns-per-op samples))
                           :bytes-per-op (second (sort (map :bytes-per-op samples)))
                           :samples samples)]
            (prn row) (flush) row)) rules/large-parent-shapes))
