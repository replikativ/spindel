(ns org.replikativ.spindel.bench.diamond-bench
  "Diamond dependency benchmark — Spindel-unique.

  Signal S → spins A and B → spin C awaits both.
  Change S, measure: C sees consistent snapshot (both A and B updated).
  Measures per-update propagation latency through a diamond DAG.

  Neither Kyo nor Kotlin solve this — they require manual coordination."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.bench.harness :as h]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.state.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]))

(defn run-bench
  "Run diamond glitch-free benchmark with criterium.

  Benchmarks a single signal update propagating through a diamond DAG."
  ([] (run-bench :quick))
  ([mode]
   (let [bench-f (if (= mode :quick) h/quick-bench-fn h/bench-fn)]
     (h/with-bench-ctx [ctx]
       ;; Setup: create diamond DAG outside the benchmarked fn
       (let [s (sig/signal 0)
             a (spin (* 2 (:new (track s))))
             b (spin (+ 10 (:new (track s))))
             c (spin (+ (await a) (await b)))
             counter (atom 0)]
         ;; Initial execution
         @c
         (bench-f
           "diamond single-update propagation"
           (fn []
             ;; Benchmark: one signal update through the diamond
             (reset! s (swap! counter inc))
             (h/await-drain! ctx)
             @c)))))))
