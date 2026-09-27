(ns org.replikativ.spindel.engine.orphan-reap-test
  "The generation sweep drops a complete orphan that has no await
  continuations. The GC path marks a spin `:orphaned?` while the spin is not
  quiescent, and the spin can then finish with no await conts. The sweep is
  the only later pass for such a spin."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]))

(deftest a-generation-sweep-reaps-an-orphan-with-no-await-conts
  (let [c (ctx/create-execution-context)]
    (try
      (binding [ec/*execution-context* c]
        (let [orphan (spin 42)
              oid    (spin-core/spin-id orphan)
              other  (spin 7)
              kid    (spin-core/spin-id other)]
          (is (= 42 @orphan))
          (is (= 7 @other))
          (simple/await-drain-complete! c)
          (ec/swap-state! [:nodes oid] #(assoc % :orphaned? true))
          (testing "the orphan is complete and has no await conts"
            (is (:completed? (ec/get-state [:nodes oid])))
            (is (empty? (ec/get-state [:await-conts oid]))))
          (simple/clear-all-await-continuations! c)
          (testing "the sweep drops the orphan"
            (is (not (contains? (ec/get-state [:nodes]) oid))))
          (testing "the sweep keeps a complete spin that is not an orphan"
            (is (some? (ec/get-state [:nodes kid]))))))
      (finally
        (ctx/stop-context! c)))))
