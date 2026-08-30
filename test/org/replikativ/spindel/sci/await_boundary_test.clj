(ns org.replikativ.spindel.sci.await-boundary-test
  (:require [clojure.test :refer [deftest is testing]]
            [sci.core :as sci]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.sci.macro :as sci-macro]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]))

(deftest sci-await-registers-and-cancels-in-the-owning-spin
  (testing "the SCI/native CPS boundary preserves owner identity and finally"
    (let [ctx (context/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [gate (sync/deferred)
                cleaned (atom false)
                sci-ctx (sci-macro/create-spin-macro-context
                         {:runtime ctx
                          :sci-opts {:bindings {'gate gate 'cleaned cleaned}}})
                worker (sci/eval-string*
                        sci-ctx
                        "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                                  '[org.replikativ.spindel.effects.await :refer [await]])
                         (spin (try (await gate)
                                    (finally (reset! cleaned true))))")
                sid (spin-core/spin-id worker)
                rejected (promise)]
            (worker (fn [_] (is false "cancelled worker resolved"))
                    #(deliver rejected %))
            (simple/await-drain-complete! ctx :timeout-ms 2000)
            (is (seq (ec/get-state [:await-conts sid])))
            (is (empty? (ec/get-state [:await-conts nil])))
            (spin-core/cancel-spin! worker)
            (is (true? @cleaned))
            (is (= spin-core/spin-cancelled
                   (:type (ex-data (deref rejected 2000 nil)))))))
        (finally
          (context/close-context! ctx))))))

(deftest sci-sequential-await-keeps-owner-identity-after-resume
  (testing "continuation re-entry binds the same world and Spin"
    (let [ctx (context/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [left (sync/deferred)
                right (sync/deferred)
                sci-ctx (sci-macro/create-spin-macro-context
                         {:runtime ctx
                          :sci-opts {:bindings {'left left 'right right}}})
                worker (sci/eval-string*
                        sci-ctx
                        "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                                  '[org.replikativ.spindel.effects.await :refer [await]])
                         (spin [(await left) (await right)])")
                sid (spin-core/spin-id worker)
                resolved (promise)]
            (worker #(deliver resolved %) #(deliver resolved %))
            (simple/await-drain-complete! ctx :timeout-ms 2000)
            (is (seq (ec/get-state [:await-conts sid])))
            (sync/deliver! left :left)
            (simple/await-drain-complete! ctx :timeout-ms 2000)
            (is (seq (ec/get-state [:await-conts sid])))
            (is (empty? (ec/get-state [:await-conts nil])))
            (sync/deliver! right :right)
            (is (= [:left :right] (deref resolved 2000 nil)))))
        (finally
          (context/close-context! ctx))))))
