(ns check-inference
  (:require [collection-bench :as bench]
            [org.replikativ.foerster.core :as infer]
            [org.replikativ.foerster.measure :as measure]
            [org.replikativ.foerster.trace :as trace]
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.atom :as sa]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.executor :as executor]))

(defn check-path [model choices]
  (let [world (sp/create-execution-context :executor (executor/synchronous-executor))]
    (try
      (sp/with-context world
        (let [state (sa/atom [])
              result @(infer/smc-infer
                       (model state 4) 4
                       {:world-policy :fork :seed 29 :resample-threshold 1.01
                        :policy (trace/policy
                                 {:constraints (into {} (map-indexed (fn [i x] [[:x i] x]) choices))})})
              expected (reduce + (map #(+ (Math/log 0.5) (Math/log (if % 0.8 0.2))) choices))
              values (mapv measure/get-value (measure/get-contexts result))]
          (assert (empty? @state))
          (assert (every? #(= {:values choices :state choices} %) values))
          (assert (< (Math/abs (- expected (measure/log-marginal result))) 1.0e-10))
          true))
      (finally (context/close-context! world)))))

(defn check-all []
  (let [checked
        (for [kind [:mapv :doseq :loop-vector]
              a [false true] b [false true] c [false true] d [false true]]
          (check-path (bench/cached-inference-model kind) [a b c d]))]
    {:paths-checked (count (doall checked)) :values-isolation-and-joint-scores :passed}))
