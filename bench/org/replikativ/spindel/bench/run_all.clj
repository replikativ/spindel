(ns org.replikativ.spindel.bench.run-all
  "Runner for all Spindel benchmarks.

  Usage:
    ;; Quick mode (development iteration):
    clj -A:bench -M -m org.replikativ.spindel.bench.run-all

    ;; Full mode (publication-quality numbers):
    clj -A:bench -M -m org.replikativ.spindel.bench.run-all full

    ;; Save results to EDN:
    clj -A:bench -M -m org.replikativ.spindel.bench.run-all full results.edn

    ;; From REPL:
    (require '[org.replikativ.spindel.bench.run-all :as bench])
    (bench/run-all :quick)
    (bench/run-all :full)"
  (:require [org.replikativ.spindel.bench.harness :as h]
            [org.replikativ.spindel.bench.fork-join-bench :as fork-join]
            [org.replikativ.spindel.bench.fan-out-bench :as fan-out]
            [org.replikativ.spindel.bench.scheduling-bench :as scheduling]
            [org.replikativ.spindel.bench.rendezvous-bench :as rendezvous]
            [org.replikativ.spindel.bench.stream-bench :as stream]
            [org.replikativ.spindel.bench.diamond-bench :as diamond]
            [org.replikativ.spindel.bench.fork-snapshot-bench :as fork-snapshot]
            [org.replikativ.spindel.bench.signal-propagation-bench :as signal-prop]
            [org.replikativ.spindel.bench.wide-antichain-bench :as wide-antichain]))

(def comparable-benchmarks
  "Benchmarks with Kyo/Kotlin equivalents."
  [{:name "fork-join"    :run-fn fork-join/run-bench}
   {:name "fan-out"      :run-fn fan-out/run-bench}
   {:name "scheduling"   :run-fn scheduling/run-bench}
   {:name "rendezvous"   :run-fn rendezvous/run-bench}
   {:name "stream"       :run-fn stream/run-bench}])

(def spindel-benchmarks
  "Spindel-unique benchmarks."
  [{:name "diamond"            :run-fn diamond/run-bench}
   {:name "fork-snapshot"      :run-fn fork-snapshot/run-bench}
   {:name "signal-propagation" :run-fn signal-prop/run-bench}
   {:name "wide-antichain"     :run-fn wide-antichain/run-bench}])

(defn run-all
  "Run all benchmarks and print summary.

  Mode: :quick or :full"
  ([] (run-all :quick))
  ([mode]
   (println "\n")
   (println (apply str (repeat 72 "=")))
   (println " SPINDEL BENCHMARK SUITE")
   (println (str " Mode: " (name mode)))
   (println (str " JVM:  " (System/getProperty "java.version")))
   (println (str " OS:   " (System/getProperty "os.name") " "
                 (System/getProperty "os.arch")))
   (println (apply str (repeat 72 "=")))

   (println "\n--- Comparable Benchmarks (Kyo arena equivalents) ---")
   (let [comparable-results (doall
                              (mapcat (fn [{:keys [run-fn]}]
                                        (let [r (run-fn mode)]
                                          (if (sequential? r) r [r])))
                                      comparable-benchmarks))]

     (println "\n--- Spindel-Unique Benchmarks ---")
     (let [spindel-results (doall
                             (mapcat (fn [{:keys [run-fn]}]
                                       (let [r (run-fn mode)]
                                         (if (sequential? r) r [r])))
                                     spindel-benchmarks))
           all-results (concat comparable-results spindel-results)]

       (h/print-summary all-results)

       ;; Return results for programmatic use
       all-results))))

(defn run-comparable
  "Run only the Kyo-comparable benchmarks."
  ([] (run-comparable :quick))
  ([mode]
   (println "\n--- Comparable Benchmarks (Kyo arena equivalents) ---")
   (let [results (doall
                   (mapcat (fn [{:keys [run-fn]}]
                             (let [r (run-fn mode)]
                               (if (sequential? r) r [r])))
                           comparable-benchmarks))]
     (h/print-summary results)
     results)))

(defn run-spindel
  "Run only the Spindel-unique benchmarks."
  ([] (run-spindel :quick))
  ([mode]
   (println "\n--- Spindel-Unique Benchmarks ---")
   (let [results (doall
                   (mapcat (fn [{:keys [run-fn]}]
                             (let [r (run-fn mode)]
                               (if (sequential? r) r [r])))
                           spindel-benchmarks))]
     (h/print-summary results)
     results)))

(defn -main
  "CLI entry point."
  [& args]
  (let [mode (if (= "full" (first args)) :full :quick)
        output-file (second args)
        results (run-all mode)]
    (when output-file
      (spit output-file (pr-str (h/results->edn results)))
      (println (str "\nResults written to: " output-file)))
    (shutdown-agents)))
