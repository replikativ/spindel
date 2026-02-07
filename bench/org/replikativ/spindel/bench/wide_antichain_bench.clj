(ns org.replikativ.spindel.bench.wide-antichain-bench
  "Wide antichain (fan-out) benchmark — Spindel-unique.

  1 signal → N independent observer spins.
  Measures propagation latency vs fan-out width N.
  Shows parallel Phase 1 speedup from CountDownLatch dispatch.

  N = 1, 2, 4, 8, 16, 32, 64

  Kyo Signal notifies observers sequentially via Promise swap."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.bench.harness :as h]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.state.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]))

(defn run-bench
  "Run wide antichain benchmark with criterium.

  Tests propagation latency with 1, 2, 4, 8, 16, 32, 64 observers."
  ([] (run-bench :quick))
  ([mode]
   (let [bench-f (if (= mode :quick) h/quick-bench-fn h/bench-fn)
         widths [1 2 4 8 16 32 64]]
     (mapv
       (fn [n]
         (h/with-bench-ctx [ctx]
           (let [source (sig/signal 0)
                 ;; Create N independent observer spins
                 observers (doall
                             (for [_ (range n)]
                               (spin (* 2 (:new (track source))))))]
             ;; Initial execution
             (doseq [o observers] @o)
             (bench-f
               (str "antichain width=" n)
               (fn []
                 (swap! source inc)
                 (h/await-drain! ctx)
                 ;; Deref all observers to ensure they completed
                 (doseq [o observers] @o))))))
       widths))))
