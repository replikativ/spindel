(ns org.replikativ.spindel.bench.rendezvous-bench
  "Rendezvous benchmark — mirrors Kyo's RendezvousBench.

  Producer changes a signal, consumer spin tracks it.
  Measures per-handoff latency for signal-based producer-consumer.

  Kyo equivalent: Promise-based producer-consumer with AtomicRef."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.bench.harness :as h]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]))

(defn run-bench
  "Run rendezvous benchmark with criterium.

  Benchmarks single signal handoff latency."
  ([] (run-bench :quick))
  ([mode]
   (let [bench-f (if (= mode :quick) h/quick-bench-fn h/bench-fn)]
     (h/with-bench-ctx [ctx]
       ;; Setup outside benchmark fn
       (let [sig (sig/signal 0)
             consumer (spin
                        (let [{:keys [new]} (track sig)]
                          new))
             counter (atom 0)]
         ;; Initial execution
         @consumer
         (bench-f
           "rendezvous single-handoff"
           (fn []
             ;; Benchmark: one signal update + consumer tracks it
             (reset! sig (swap! counter inc))
             (h/await-drain! ctx)
             @consumer)))))))
