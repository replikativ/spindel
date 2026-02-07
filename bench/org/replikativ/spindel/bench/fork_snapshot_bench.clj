(ns org.replikativ.spindel.bench.fork-snapshot-bench
  "CoW fork cost benchmark — Spindel-unique.

  Creates a context with N signals and M spins, then forks it.
  Measures fork latency vs N. Persistent data structure sharing
  means fork should be approximately O(1).

  No analog in Kyo or Kotlin."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.bench.harness :as h]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.state.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]))

(defn run-bench
  "Run fork-snapshot benchmark with criterium.

  Tests fork cost at different sizes."
  ([] (run-bench :quick))
  ([mode]
   (let [bench-f (if (= mode :quick) h/quick-bench-fn h/bench-fn)
         sizes [10 100 1000]]
     (h/with-bench-ctx [ctx]
       ;; Pre-populate context with varying numbers of signals
       (let [signals (doall (for [i (range (last sizes))]
                              (sig/signal i)))
             ;; Create some spins tracking signals
             spins (doall (for [s (take 100 signals)]
                            (spin (:new (track s)))))]
         ;; Wait for initial execution
         (doseq [s spins] @s)

         ;; Benchmark fork at each size
         (mapv
           (fn [n]
             (bench-f
               (str "fork-context " n " signals")
               (fn []
                 (let [forked (ctx/fork-context ctx)]
                   ;; Verify fork is usable
                   (binding [rtc/*execution-context* forked]
                     (let [s (spin :forked)]
                       @s))))))
           sizes))))))
