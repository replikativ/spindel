(ns org.replikativ.spindel.sci.world-test
  (:require [clojure.test :refer [deftest is testing]]
            [sci.core :as sci]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.component :as component]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.sci.world :as world]
            [org.replikativ.spindel.spin.core :as spin-core]))

(deftest interpreter-without-spindel-primitives-keeps-fork-selected-heap
  (let [parent (context/create-execution-context)
        loaded (atom [])
        interrupted (atom 0)]
    (try
      (let [ref (world/create! parent {:spindel-primitives? false
                                       :interrupt-fn #(swap! interrupted inc)
                                       :sci-opts {:runtime-mode :standard
                                                  :load-fn (fn [request] (swap! loaded conj (:namespace request)) nil)
                                                  :namespaces {'fixture.runtime {'answer (constantly 42)}}}})
            interpreter (world/context-in parent ref)]
        (binding [ec/*execution-context* parent]
          (is (= 42 (world/eval-string* ref "(require '[fixture.runtime :as rt]) (rt/answer)")))
          (world/eval-string* ref "(def memory (atom [:parent])) (defn saved [] @memory)")
          (is (= [:parent] (world/eval-string* ref "(saved)"))))
        (is (pos? @interrupted))
        (doseq [symbol ['org.replikativ.spindel.spin.core/make-spin
                        'org.replikativ.spindel.engine.core/current-execution-context
                        'org.replikativ.spindel.effects.await/await
                        'is.simm.partial-cps.async/invoke-continuation]]
          (is (nil? (sci/eval-form interpreter (list 'resolve (list 'quote symbol))))))
        (is (thrown? Exception (sci/eval-string* interpreter "(require 'fixture.missing)")))
        (is (= ['fixture.missing] @loaded))
        (let [child (context/fork-context parent :mode :frozen)]
          (try
            (binding [ec/*execution-context* child]
              (is (= [:parent :child] (world/eval-string* ref "(swap! memory conj :child)")))
              (is (= [:parent :child] (world/eval-string* ref "(saved)"))))
            (binding [ec/*execution-context* parent]
              (is (= [:parent] (world/eval-string* ref "(saved)"))))
            (is (not (identical? interpreter (world/context-in child ref))))
            (finally (context/close-context! child)))))
      (finally (context/close-context! parent)))))

(deftest interpreter-surface-option-refuses-ambiguous-values
  (let [runtime (context/create-execution-context)]
    (try
      (doseq [value [nil :false 0 "false"]]
        (is (= ::world/invalid-options
               (try (world/create! runtime {:spindel-primitives? value}) nil
                    (catch clojure.lang.ExceptionInfo error (:type (ex-data error)))))))
      (is (empty? (binding [ec/*execution-context* runtime] (component/registered))))
      (finally (context/close-context! runtime)))))

(deftest staged-interpreter-replacement-preserves-state-and-stable-resolvers
  (let [parent (context/create-execution-context)]
    (try
      (let [ref (world/create! parent)
            original (world/context-in parent ref)
            _ (sci/eval-string* original "(def state (atom [:original])) (defn saved [] @state)")
            before (context/fork-context parent :mode :frozen)
            staged (sci/fork original)]
        (try
          (sci/eval-string* staged "(swap! state conj :staged)")
          (is (= [:original] (sci/eval-string* original "(saved)")))
          (is (identical? staged (world/replace-context! parent ref original staged)))
          (is (identical? staged (world/context-in parent ref)))
          (is (= [:original :staged]
                 (binding [ec/*execution-context* parent]
                   (world/eval-string* ref "(saved)"))))
          (let [task (binding [ec/*execution-context* parent]
                       (world/eval-string*
                        ref
                        "(require '[org.replikativ.spindel.spin.cps :refer [spin]])
                         (spin (saved))"))]
            (is (= [:original :staged] (binding [ec/*execution-context* parent] @task)))
            (is (= [:original] (sci/eval-string* (world/context-in before ref) "(saved)"))))
          (let [after (context/fork-context parent :mode :frozen)]
            (try
              (is (= [:original :staged]
                     (sci/eval-string* (world/context-in after ref) "(saved)")))
              (is (= ::world/stale-context
                     (try (world/replace-context! after ref staged (sci/fork staged)) nil
                          (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
              (let [child-context (world/context-in after ref)
                    child-stage (sci/fork child-context)]
                (sci/eval-string* child-stage "(swap! state conj :child)")
                (world/replace-context! after ref child-context child-stage)
                (is (= [:original :staged :child]
                       (sci/eval-string* (world/context-in after ref) "(saved)")))
                (is (= [:original :staged] (sci/eval-string* (world/context-in parent ref) "(saved)"))))
              (finally (context/close-context! after))))
          (is (= ::world/stale-context
                 (try (world/replace-context! parent ref original (sci/fork original)) nil
                      (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
          (is (identical? staged (world/context-in parent ref)))
          (finally (context/close-context! before))))
      (finally (context/close-context! parent)))))

(deftest interpreter-replacement-refuses-missing-and-noninterpreter-components
  (let [runtime (context/create-execution-context)]
    (try
      (let [ref (world/create! runtime)
            original (world/context-in runtime ref)
            replacement (sci/fork original)
            other (binding [ec/*execution-context* runtime]
                    (component/register! (component/shared :not-an-interpreter)))]
        (is (= ::world/not-interpreter
               (try (world/replace-context! runtime other original replacement) nil
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
        (is (= :not-an-interpreter (component/resolve-in runtime other)))
        (is (= ::world/invalid-replacement
               (try (world/replace-context! runtime ref original {}) nil
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
        (is (identical? original (world/context-in runtime ref)))
        (binding [ec/*execution-context* runtime] (component/unregister! ref))
        (is (= ::world/not-interpreter
               (try (world/replace-context! runtime ref original replacement) nil
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
        (is (not (contains? (binding [ec/*execution-context* runtime] (component/registered)) (:id ref)))))
      (finally (context/close-context! runtime)))))

(deftest competing-interpreter-publications-have-one-identity-fenced-winner
  (let [runtime (context/create-execution-context)
        gate (promise)]
    (try
      (let [ref (world/create! runtime)
            original (world/context-in runtime ref)
            alternatives [(sci/fork original) (sci/fork original)]
            contenders (mapv (fn [replacement]
                               (future
                                 @gate
                                 (try (world/replace-context! runtime ref original replacement)
                                      :published
                                      (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
                             alternatives)]
        (deliver gate true)
        (is (= {:published 1 ::world/stale-context 1} (frequencies (mapv deref contenders))))
        (is (some #(identical? % (world/context-in runtime ref)) alternatives)))
      (finally
        (deliver gate true)
        (context/close-context! runtime)))))

(deftest inherited-native-capabilities-follow-the-selected-world
  (let [parent (context/create-execution-context)]
    (try
      (binding [ec/*execution-context* parent]
        (ec/swap-state! [:probe] (constantly [])))
      (let [probe-tool
            (binding [ec/*execution-context* parent]
              (spin-core/make-spin
               (fn [resolve _reject]
                 (ec/swap-state!
                  [:probe]
                  #(conj % (:fork-id (ec/current-execution-context))))
                 (resolve :ok))
               :probe-tool))
            interpreter-ref
            (world/create! parent {:native-spins {'probe-tool probe-tool}})
            child (context/fork-context parent :mode :frozen)]
        (try
          (let [task
                (binding [ec/*execution-context* child]
                  (world/eval-string*
                   interpreter-ref
                   "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                              '[org.replikativ.spindel.effects.await :refer [await]])
                    (spin (await probe-tool))"))]
            (is (= :ok (binding [ec/*execution-context* child] @task)))
            (is (= [(:fork-id child)]
                   (binding [ec/*execution-context* child]
                     (ec/get-state [:probe]))))
            (is (= []
                   (binding [ec/*execution-context* parent]
                     (ec/get-state [:probe])))))
          (finally
            (context/close-context! child))))
      (finally
        (context/close-context! parent)))))

(deftest causal-callback-egress-is-limited-to-descendants
  (let [parent (context/create-execution-context)
        unrelated (context/create-execution-context)
        callback (atom nil)
        result (promise)
        worker
        (binding [ec/*execution-context* parent]
          (spin-core/make-spin
           (fn [resolve _reject]
             (reset! callback resolve)
             spin-core/incomplete)
           :causal-worker))]
    (try
      (binding [ec/*execution-context* parent
                ec/*callback-egress-policy* :causal-follow]
        (worker #(deliver result %) #(deliver result %)))
      (let [child (context/fork-context parent :mode :frozen)]
        (try
          (binding [ec/*execution-context* unrelated]
            (@callback :unrelated))
          (is (= ::pending (deref result 20 ::pending)))
          (binding [ec/*execution-context* child]
            (@callback :descendant))
          (is (= :descendant (deref result 1000 ::timeout)))
          (finally
            (context/close-context! child))))
      (finally
        (context/close-context! unrelated)
        (context/close-context! parent)))))

(deftest suspended-sci-spin-resumes-independently-in-forked-worlds
  (testing "the copied Spindel continuation selects the paired SCI heap"
    (let [parent (context/create-execution-context)
          callback (atom nil)
          operation (fn [resolve _reject]
                      (reset! callback resolve)
                      spin-core/incomplete)]
      (try
        (let [interpreter-ref
              (world/create!
               parent
               {:sci-opts {:bindings {'operation operation}}})
              interpreter (world/context-in parent interpreter-ref)
              worker
              (binding [ec/*execution-context* parent]
                (sci/eval-string*
                 interpreter
                 "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                           '[org.replikativ.spindel.effects.await :refer [await]])
                  (def state (atom []))
                  (def ^:dynamic *scope* :root)
                  (spin
                    (binding [*scope* :bound]
                      (let [value (await operation)]
                        (swap! state conj [*scope* value])
                        @state)))"))
              spin-id (spin-core/spin-id worker)
              parent-result (promise)]
          (binding [ec/*execution-context* parent]
            (worker #(deliver parent-result %) #(deliver parent-result %)))
          (simple/await-drain-complete! parent :timeout-ms 2000)
          (is (fn? @callback))
          (let [child (context/fork-context parent :mode :frozen)
                child-interpreter (world/context-in child interpreter-ref)]
            (try
              (is (not (identical? interpreter child-interpreter)))
              (binding [ec/*execution-context* child]
                (@callback :child))
              (simple/await-drain-complete! child :timeout-ms 2000)
              (is (= [[:bound :child]]
                     (:payload
                      (binding [ec/*execution-context* child]
                        (ec/spin-current-result spin-id)))))
              (is (= ::pending (deref parent-result 20 ::pending))
                  "child completion must not fire the parent's egress callback")
              (is (nil? (binding [ec/*execution-context* parent]
                          (ec/spin-current-result spin-id))))
              (is (= [[:bound :child]]
                     (sci/eval-string* child-interpreter "@state")))
              (is (= [] (sci/eval-string* interpreter "@state")))
              (binding [ec/*execution-context* parent]
                (@callback :parent))
              (simple/await-drain-complete! parent :timeout-ms 2000)
              (is (= [[:bound :parent]]
                     (:payload
                      (binding [ec/*execution-context* parent]
                        (ec/spin-current-result spin-id)))))
              (is (= [[:bound :parent]] @parent-result))
              (is (= [[:bound :parent]]
                     (sci/eval-string* interpreter "@state")))
              (is (= [[:bound :child]]
                     (sci/eval-string* child-interpreter "@state")))
              (finally
                (context/close-context! child)))))
        (finally
          (context/close-context! parent))))))

(deftest materialized-particle-fork-retargets-sci-continuations
  (let [parent (context/create-execution-context)
        callback (atom nil)
        operation (fn [resolve _reject]
                    (reset! callback resolve)
                    spin-core/incomplete)]
    (try
      (let [interpreter-ref
            (world/create!
             parent
             {:sci-opts {:bindings {'operation operation}}})
            parent-interpreter (world/context-in parent interpreter-ref)
            worker
            (binding [ec/*execution-context* parent]
              (sci/eval-string*
               parent-interpreter
               "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                          '[org.replikativ.spindel.effects.await :refer [await]])
                (def samples (atom []))
                (spin (let [x (await operation)]
                        (swap! samples conj x)))"))
            result (promise)]
        (binding [ec/*execution-context* parent
                  ec/*callback-egress-policy* :causal-follow]
          (worker #(deliver result %) #(deliver result %)))
        (let [particle (context/materialized-fork-context parent :clean-in-flight? false)
              particle-interpreter (world/context-in particle interpreter-ref)]
          (try
            (is (= (:fork-id parent) (:fork-id (:parent-ctx particle))))
            (is (not (identical? parent-interpreter particle-interpreter)))
            (binding [ec/*execution-context* particle]
              (@callback :particle))
            (simple/await-drain-complete! particle :timeout-ms 2000)
            (is (= [:particle]
                   (sci/eval-string* particle-interpreter "@samples")))
            (is (= [] (sci/eval-string* parent-interpreter "@samples")))
            (is (= [:particle] (deref result 1000 ::timeout)))
            (finally
              (context/close-context! particle)))))
      (finally
        (context/close-context! parent)))))
