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
            (binding [ec/*spin-id* :unrelated-producer]
              (sync/deliver! left :left))
            (simple/await-drain-complete! ctx :timeout-ms 2000)
            (is (seq (ec/get-state [:await-conts sid])))
            (is (empty? (ec/get-state [:await-conts :unrelated-producer])))
            (is (empty? (ec/get-state [:await-conts nil])))
            (sync/deliver! right :right)
            (is (= [:left :right] (deref resolved 2000 nil)))))
        (finally
          (context/close-context! ctx))))))

(deftest sci-callback-resume-respects-world-lineage
  (testing "an unrelated ambient room cannot capture another room's continuation"
    (let [owner-ctx (context/create-execution-context)
          foreign-ctx (context/create-execution-context)]
      (try
        (binding [ec/*execution-context* owner-ctx]
          (let [callback (atom nil)
                operation (fn [resolve _reject]
                            (reset! callback resolve)
                            spin-core/incomplete)
                sci-ctx (sci-macro/create-spin-macro-context
                         {:runtime owner-ctx
                          :sci-opts {:bindings {'operation operation}}})
                worker (sci/eval-string*
                        sci-ctx
                        "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                                  '[org.replikativ.spindel.effects.await :refer [await]])
                         (spin (await operation))")
                sid (spin-core/spin-id worker)
                resolved (promise)]
            (worker #(deliver resolved %) #(deliver resolved %))
            (is (fn? @callback))
            (binding [ec/*execution-context* foreign-ctx
                      ec/*spin-id* :foreign-producer]
              (@callback :value))
            (is (= :value (deref resolved 2000 nil)))
            (is (= :value (:payload (ec/spin-current-result sid))))
            (binding [ec/*execution-context* foreign-ctx]
              (is (nil? (ec/spin-current-result sid))))))
        (finally
          (context/close-context! owner-ctx)
          (context/close-context! foreign-ctx)))))

  (testing "a legitimate descendant fork receives its own resumed result"
    (let [owner-ctx (context/create-execution-context)]
      (try
        (binding [ec/*execution-context* owner-ctx]
          (let [callback (atom nil)
                operation (fn [resolve _reject]
                            (reset! callback resolve)
                            spin-core/incomplete)
                sci-ctx (sci-macro/create-spin-macro-context
                         {:runtime owner-ctx
                          :sci-opts {:bindings {'operation operation}}})
                worker (sci/eval-string*
                        sci-ctx
                        "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                                  '[org.replikativ.spindel.effects.await :refer [await]])
                         (spin (await operation))")
                sid (spin-core/spin-id worker)]
            (worker identity identity)
            (let [fork-ctx (context/fork-context owner-ctx)]
              (binding [ec/*execution-context* fork-ctx
                        ec/*spin-id* :fork-producer]
                (@callback :fork-value))
              (is (nil? (ec/spin-current-result sid)))
              (binding [ec/*execution-context* fork-ctx]
                (is (= :fork-value (:payload (ec/spin-current-result sid))))))))
        (finally
          (context/close-context! owner-ctx)))))

  (testing "the low-level bridge rejects direct use outside a Spin"
    (let [ctx (context/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [sci-ctx (sci-macro/create-spin-macro-context {:runtime ctx})
                bridge (sci/resolve
                        sci-ctx
                        'org.replikativ.spindel.engine.core/invoke-sci-awaitable)]
            (is (thrown-with-msg?
                 clojure.lang.ExceptionInfo
                 #"requires an owning Spin"
                 (bridge (fn [_resolve _reject] spin-core/incomplete)
                         {} identity identity)))))
        (finally
          (context/close-context! ctx))))))
