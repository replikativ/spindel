(ns org.replikativ.spindel.lifetime.measurement-protocol-test
  (:require [clojure.test :refer [deftest is]]
            [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.enum-bench :as enumeration]
            [org.replikativ.spindel.lifecycle-bench :as lifecycle]
            [org.replikativ.spindel.large-parent-bench :as large]
            [org.replikativ.spindel.lifetime-gates-check :as checks]
            [org.replikativ.spindel.lifetime-gate-rules :as rules]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.core :as ec]))

(deftest measurement-gate-regressions
  ;; Include the pure CLI gate suite in the ordinary JVM test run.
  (clojure.test/test-all-vars 'org.replikativ.spindel.lifetime-gates-check))

(deftest checkpoint-drains-once-between-stabilizations
  (if-let [drain (ns-resolve 'org.replikativ.spindel.enum-bench 'drain-keyword-interns!)]
    (let [calls (atom 0) collections (atom 0)]
      (with-redefs-fn {drain #(swap! calls inc)
                       #'enumeration/gc-count #(swap! collections inc)
                       #'rules/measurement-protocol (-> rules/measurement-protocol
                                                        (assoc-in [:gc :sample-pause-ms] 0)
                                                        (assoc-in [:gc :heap-tolerance] 1.0))}
        #(let [point (enumeration/full-gc! nil)]
           (is (:keyword-intern-drained? point))
           (is (= 1 @calls))
           (is (rules/gc-stable? (:pre-intern-gc point) #{})))))
    (is false "Checkpoint has no intern-table drain")))

(deftest lifecycle-keeps-children-and-warmup-handles
  (let [r (lifecycle/run-one :L-child 5 2)]
    (is (= 14 (:retained-handles r)))
    (is (= 0 (:cleanup-calls r)))
    (is (= 15 (:checksum r)))))

(deftest lifecycle-rejects-foreign-cleanup
  (with-redefs-fn {#'org.replikativ.spindel.lifecycle-bench/body-fn
                   (fn [& _]
                     (fn [i] (simple/full-cleanup-spin! ec/*execution-context* :foreign) i))}
    #(is (thrown-with-msg? clojure.lang.ExceptionInfo #"Cleanup contaminated"
                           (lifecycle/run-one :L0 1 0)))))

(deftest large-parent-fixtures-keep-live-parent
  ;; Small operation batch; covers native root/following/frozen paths without
  ;; turning correctness tests into the 10k-node performance measurement.
  (doseq [mode [:root :following :frozen] path [:uncached-await :execution-event]]
    (let [root (ctx/create-execution-context :executor (ex/synchronous-executor))]
      (try
        (binding [ec/*execution-context* root cps/*in-trampoline* false]
          (let [handles (mapv large/fresh-spin (range 3))
                _ (doseq [s handles] @s)
                world (if (= mode :root) root (ctx/fork-context root :mode mode))]
            (try
              (let [r (large/run-batch world path 2)]
                (is (= 3 (:checksum r)))
                (is (= (+ 3 (if (= path :uncached-await) 4 2)) (:nodes-at-start r))))
              (finally (when-not (identical? world root) (ctx/close-context! world))))
            (java.lang.ref.Reference/reachabilityFence handles)))
        (finally (ctx/close-context! root))))))
