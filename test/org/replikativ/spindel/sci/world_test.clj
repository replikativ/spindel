(ns org.replikativ.spindel.sci.world-test
  (:require [clojure.test :refer [deftest is testing]]
            [sci.core :as sci]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.inference.coordinator :as coordinator]
            [org.replikativ.spindel.sci.world :as world]
            [org.replikativ.spindel.spin.core :as spin-core]))

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
        (let [particle (coordinator/fork-particle-context parent)
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
