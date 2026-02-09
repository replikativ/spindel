(ns org.replikativ.spindel.bench.scheduling-bench
  "Scheduling benchmark — mirrors Kyo's SchedulingBench.

  Creates fibers that perform deep chains of awaits.
  Measures scheduler throughput under load.

  Note: Kyo uses 1K fibers × 1K cede points. Spindel's await semantics
  differ (no explicit cede), so we measure deep spin chains."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.bench.harness :as h]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]))

(def ^:const FIBERS 100)
(def ^:const DEPTH 100)

(defn run-bench
  "Run scheduling benchmark with criterium."
  ([] (run-bench :quick))
  ([mode]
   (let [bench-f (if (= mode :quick) h/quick-bench-fn h/bench-fn)]
     (h/with-bench-ctx [ctx]
       (bench-f
         (str "scheduling " FIBERS "x" DEPTH " deep chain")
         (fn []
           ;; Build chains inside bench fn — each iteration creates fresh spins
           ;; to measure spin creation + deep await overhead
           (let [chains (doall
                          (for [_ (range FIBERS)]
                            (loop [s (spin :done)
                                   d DEPTH]
                              (if (<= d 0)
                                s
                                (let [prev s]
                                  (recur (spin (await prev)) (dec d)))))))]
             (doseq [c chains]
               @c))))))))
