(ns org.replikativ.spindel.inference.random-test
  "A seeded run draws the same numbers however its particles and chains are
  scheduled: every draw made in a world reads a stream keyed by the world's
  seed and what is drawn."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.inference.benchmark-test :refer [run-infer weighted-values]]
            [org.replikativ.spindel.inference.inference :as infer]
            [org.replikativ.spindel.inference.kernel :as k]
            [org.replikativ.spindel.inference.smc :as smc]
            [org.replikativ.spindel.inference.effects :refer [sample observe]]
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [anglican.runtime :as ar]))

(defn- model []
  (spin
   (let [x (sample (ar/normal 0 1))]
     (observe (ar/normal x 1) 2.0)
     (let [z (sample (ar/normal 0 1))]
       (observe (ar/normal z 1) -2.0)
       [x z]))))

(defn- runs
  "`n` runs of `make` under `seed` on a 4-thread executor."
  [n seed make]
  (let [exec (executor/thread-pool-executor {:threads 4})]
    (try
      (vec (repeatedly n #(weighted-values (run-infer seed (fn [] (make exec))))))
      (finally (.close ^java.lang.AutoCloseable exec)))))

(deftest parallel-chains-are-reproducible
  (let [make (fn [exec] (infer/kernel-infer (model)
                                            (k/random-walk-mh-kernel 300 {:step-size 0.5 :samples :all :burn 50})
                                            4 {:executor exec}))
        [a b c] (runs 3 13 make)]
    (is (= a b c) "the same seed, the same chains")
    (is (not= a (first (runs 1 14 make))) "another seed, other chains")))

(deftest parallel-particles-are-reproducible
  (let [make (fn [exec] (smc/smc (model) 200 {:executor exec}))
        [a b c] (runs 3 21 make)]
    (is (= a b c))
    (is (not= a (first (runs 1 22 make))))))
