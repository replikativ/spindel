(ns org.replikativ.spindel.bench.signal-propagation-bench
  "Multi-level signal propagation benchmark — Spindel-unique.

  Chain of N signals: S₁ → S₂ → ... → Sₙ
  Each level is a spin tracking the previous signal/spin.
  Measures end-to-end propagation latency vs chain depth.

  Kyo Signal has no DAG — would need manual Promise chaining."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.bench.harness :as h]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]))

(defn run-bench
  "Run signal propagation benchmark with criterium.

  Tests propagation latency at chain depths 1, 2, 4, 8, 16."
  ([] (run-bench :quick))
  ([mode]
   (let [bench-f (if (= mode :quick) h/quick-bench-fn h/bench-fn)
         depths [1 2 4 8 16]]
     (mapv
       (fn [depth]
         (h/with-bench-ctx [ctx]
           (let [source (sig/signal 0)
                 ;; Build chain: each spin tracks previous via await
                 chain (reduce
                         (fn [prev-spin _]
                           (spin (inc (await prev-spin))))
                         (spin (:new (track source)))
                         (range (dec depth)))]
             ;; Initial execution
             @chain
             (bench-f
               (str "propagation depth=" depth)
               (fn []
                 (swap! source inc)
                 (h/await-drain! ctx)
                 @chain)))))
       depths))))
