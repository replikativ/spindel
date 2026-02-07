(ns org.replikativ.spindel.bench.fan-out-bench
  "Fan-Out benchmark — mirrors Kyo's CollectParBench.

  Creates 1,000 spins and collects results via the parallel combinator.
  Measures parallel dispatch + collection overhead."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.bench.harness :as h]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.combinators :refer [parallel]]
            [org.replikativ.spindel.effects.await :refer [await]]))

(def ^:const N 1000)

(defn run-bench
  "Run fan-out benchmark with criterium."
  ([] (run-bench :quick))
  ([mode]
   (let [bench-f (if (= mode :quick) h/quick-bench-fn h/bench-fn)]
     (h/with-bench-ctx [ctx]
       (bench-f
         (str "fan-out " N " parallel collect")
         (fn []
           ;; Create N spins and await all via parallel
           (let [spins (doall (for [i (range N)]
                                (spin i)))]
             @(spin (await (apply parallel spins))))))))))
