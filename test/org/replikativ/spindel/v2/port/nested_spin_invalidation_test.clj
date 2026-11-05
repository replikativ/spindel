(ns org.replikativ.spindel.v2.port.nested-spin-invalidation-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin await track]]
            [org.replikativ.spindel.v2.port.support :refer [checking with-world outcome]]))

(use-fixtures :each checking)

(deftest test-nested-spin-closure-update
  (with-world [w]
    (let [multiplier (v2/signal 2)
          outer (spin (let [n (:new (track multiplier))
                            inner (spin (* 10 n))]
                        (await inner)))]
      (is (= [:ok 20] (outcome outer)))
      (swap! multiplier inc)
      (is (= [:ok 30] (outcome outer)) "The nested spin uses the fresh capture"))))

(deftest test-child-invalidation-on-parent-rerun
  (with-world [w]
    (let [trigger (v2/signal :initial) executions (atom 0)
          parent (spin (let [n (:new (track trigger))
                             child (spin (swap! executions inc) n)]
                         (await child)))]
      (is (= [:ok :initial] (outcome parent)))
      (is (= 1 @executions))
      (reset! trigger :updated)
      (is (= [:ok :updated] (outcome parent)))
      (is (= 2 @executions) "The child executes with the new capture"))))
