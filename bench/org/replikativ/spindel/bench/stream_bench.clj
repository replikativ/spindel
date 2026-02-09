(ns org.replikativ.spindel.bench.stream-bench
  "Stream benchmark — mirrors Kyo's StreamBench.

  Chain of signal → spin transformations (filter, map, reduce).
  Measures reactive pipeline overhead per update.

  Kyo equivalent: Stream.init(seq).filter.map.fold"
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.bench.harness :as h]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]))

(def ^:const N 1000)

(defn run-bench
  "Run stream pipeline benchmark with criterium.

  Benchmarks per-update cost through a filter→map→fold reactive pipeline."
  ([] (run-bench :quick))
  ([mode]
   (let [bench-f (if (= mode :quick) h/quick-bench-fn h/bench-fn)]
     (h/with-bench-ctx [ctx]
       ;; Setup pipeline outside benchmark fn
       (let [source (sig/signal (vec (range N)))
             ;; Filter: keep even numbers
             filtered (spin
                        (let [{:keys [new]} (track source)]
                          (filterv even? new)))
             ;; Map: double each value
             mapped (spin
                      (let [vals (await filtered)]
                        (mapv #(* 2 %) vals)))
             ;; Fold: sum all values
             folded (spin
                      (let [vals (await mapped)]
                        (reduce + 0 vals)))
             counter (atom 0)]
         ;; Initial execution
         @folded
         (bench-f
           (str "stream " N " filter/map/fold")
           (fn []
             ;; Benchmark: update source, pipeline re-executes
             (let [n (swap! counter inc)]
               (reset! source (vec (range n (+ n N))))
               (h/await-drain! ctx)
               @folded))))))))
