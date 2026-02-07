(ns org.replikativ.spindel.bench.fork-join-bench
  "Fork-Join benchmark — mirrors Kyo's ForkJoinBench.

  Creates 10,000 spins that return a unit value, then derefs all of them.
  Measures spin creation + deref overhead."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.bench.harness :as h]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]))

(def ^:const N 10000)

(defn run-bench
  "Run fork-join benchmark with criterium."
  ([] (run-bench :quick))
  ([mode]
   (let [bench-f (if (= mode :quick) h/quick-bench-fn h/bench-fn)]
     (h/with-bench-ctx [ctx]
       (bench-f
         (str "fork-join " N " spins")
         (fn []
           ;; Create N spins and deref each one
           (let [spins (doall (for [_ (range N)]
                                (spin :done)))]
             (doseq [s spins]
               @s))))))))
