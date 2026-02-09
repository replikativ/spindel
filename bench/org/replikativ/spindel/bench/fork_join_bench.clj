(ns org.replikativ.spindel.bench.fork-join-bench
  "Fork-Join benchmark — mirrors Kyo's ForkJoinBench.

  Creates 10,000 spins that return a unit value, then awaits/derefs all of them.
  Measures spin creation + await/deref overhead.

  Two variants:
  - await: faithful to real Spindel usage (spin + await inside CPS body)
  - deref: JVM-only convenience path (@spin)"
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.bench.harness :as h]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]))

(def ^:const N 10000)

(defn run-bench
  "Run fork-join benchmark with criterium."
  ([] (run-bench :quick))
  ([mode]
   (let [bench-f (if (= mode :quick) h/quick-bench-fn h/bench-fn)]
     (h/with-bench-ctx [ctx]
       ;; Variant 1: await-based (faithful to real Spindel usage)
       ;; Each child spin completes synchronously; with inline await optimization,
       ;; the parent resumes inline without event queue round-trips.
       (bench-f
         (str "fork-join " N " spins (await)")
         (fn []
           @(spin
              (loop [i 0]
                (when (< i N)
                  (await (spin :done))
                  (recur (inc i)))))))

       ;; Variant 2: deref-based (original, for comparison)
       ;; Each @spin goes through the event queue.
       (bench-f
         (str "fork-join " N " spins (deref)")
         (fn []
           (let [spins (doall (for [_ (range N)]
                                (spin :done)))]
             (doseq [s spins]
               @s))))))))
