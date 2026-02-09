(ns org.replikativ.spindel.bench.harness
  "Reusable benchmark harness for Spindel performance measurements.

  Provides context setup/teardown, criterium wrappers, and result collection."
  (:require [criterium.core :as crit]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.simple :as simple]))

;; =============================================================================
;; Context Management
;; =============================================================================

(defmacro with-bench-ctx
  "Execute body with a fresh execution context bound.

  Creates context, binds *execution-context*, runs body, then stops context.
  Returns the result of body.

  Usage:
    (with-bench-ctx [ctx]
      (let [s (sig/signal 0)]
        (criterium/bench @s)))"
  [[ctx-sym] & body]
  `(let [~ctx-sym (ctx/create-execution-context)]
     (try
       (binding [ec/*execution-context* ~ctx-sym]
         ~@body)
       (finally
         (ctx/stop-context! ~ctx-sym)))))

;; =============================================================================
;; Benchmark Helpers
;; =============================================================================

(defn bench-fn
  "Run a criterium benchmark and return the results map.

  Options:
    :warmup-jit-period - JIT warmup time in seconds (default: 5)
    :samples - Number of samples (default: 30)
    :target-execution-time - Target time per sample in ns (default: 1e9 = 1s)"
  ([name f]
   (bench-fn name f {}))
  ([name f opts]
   (println (str "\n=== " name " ==="))
   (let [results (crit/benchmark* f
                   (merge {:warmup-jit-period (* 5 1e9)
                           :samples 30
                           :target-execution-time (* 1 1e9)}
                          opts))]
     (crit/report-result results)
     (assoc results :bench-name name))))

(defn quick-bench-fn
  "Run a quick criterium benchmark (fewer samples, faster).

  Good for development iteration. Use bench-fn for final numbers."
  ([name f]
   (quick-bench-fn name f {}))
  ([name f opts]
   (println (str "\n=== " name " (quick) ==="))
   (let [results (crit/quick-benchmark* f
                   (merge {:warmup-jit-period (* 2 1e9)
                           :samples 10
                           :target-execution-time (* 0.5 1e9)}
                          opts))]
     (crit/report-result results)
     (assoc results :bench-name name))))

(defn await-drain!
  "Wait for all pending events to drain in the context."
  ([ctx]
   (await-drain! ctx 5000))
  ([ctx timeout-ms]
   (simple/await-drain-complete! ctx :timeout-ms timeout-ms)))

;; =============================================================================
;; Result Collection & Reporting
;; =============================================================================

(defn mean-time
  "Extract mean execution time in seconds from criterium results."
  [results]
  (first (:mean results)))

(defn mean-time-ms
  "Extract mean execution time in milliseconds from criterium results."
  [results]
  (* 1000.0 (mean-time results)))

(defn mean-time-us
  "Extract mean execution time in microseconds from criterium results."
  [results]
  (* 1e6 (mean-time results)))

(defn ops-per-sec
  "Calculate operations per second from criterium results."
  [results]
  (/ 1.0 (mean-time results)))

(defn format-result
  "Format a single benchmark result as a summary string."
  [results]
  (let [mean-us (mean-time-us results)]
    (format "%-40s %12.2f us  (%,.0f ops/s)"
            (:bench-name results)
            mean-us
            (ops-per-sec results))))

(defn print-summary
  "Print a summary table of all benchmark results."
  [all-results]
  (println "\n" (apply str (repeat 72 "=")))
  (println " BENCHMARK SUMMARY")
  (println (apply str (repeat 72 "=")))
  (println (format "%-40s %12s  %s" "Benchmark" "Mean" "Throughput"))
  (println (apply str (repeat 72 "-")))
  (doseq [r all-results]
    (println (format-result r)))
  (println (apply str (repeat 72 "="))))

(defn results->edn
  "Convert benchmark results to a serializable EDN map."
  [all-results]
  {:timestamp (System/currentTimeMillis)
   :jvm-version (System/getProperty "java.version")
   :os (System/getProperty "os.name")
   :results (mapv (fn [r]
                    {:name (:bench-name r)
                     :mean-ns (* 1e9 (mean-time r))
                     :variance-ns (* 1e9 (first (:variance r)))
                     :samples (:sample-count r)
                     :ops-per-sec (ops-per-sec r)})
                  all-results)})
