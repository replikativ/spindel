(ns org.replikativ.spindel.engine.drain-thread-test
  "`on-drain-thread?` follows the thread running a drain, not the
   `*in-drain?*` binding that `future` and `bound-fn` carry."
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.spin.cps :refer [spin]]))

(deftest the-drain-thread-is-the-one-draining
  ;; captured where work runs off the drain, binding it false
  (let [off-drain (binding [simple/*in-drain?* false]
                    (bound-fn [] [simple/*in-drain?* (simple/on-drain-thread?)]))
        observed (binding [ec/*execution-context* (ctx/create-execution-context)]
                   @(spin (await (comb/sleep 1))
                          {:continuation [simple/*in-drain?* (simple/on-drain-thread?)]
                           :future @(future [simple/*in-drain?* (simple/on-drain-thread?)])
                           :bound-fn (off-drain)}))]
    (is (= [false false] (off-drain)) "outside any drain")
    (is (= [true true] (:continuation observed)))
    (is (= [true false] (:future observed)) "a future carries the binding, not the drain")
    (is (= [false true] (:bound-fn observed)) "a bound-fn run on the drain is on it")))
