(ns org.replikativ.spindel.sci.nested-world-test
  "Characterize recursive interpreter construction through explicit capabilities."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.sci.boundary :as boundary]
            [org.replikativ.spindel.sci.macro :as macro]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [sci.core :as sci]))

(deftest sci-program-can-construct-and-run-a-spindel-sci-child-world
  (let [root (ctx/create-execution-context)
        nested-opts (atom nil)
        worlds (atom {})
        interpreters (atom {})
        resolve-world (fn [world-id]
                        (or (get @worlds world-id)
                            (throw (ex-info "Unknown interpreter world"
                                            {:world-id world-id}))))
        world-ns
        {'fork! (fn []
                  (let [world-id (random-uuid)
                        handle (ygg/fork! {:purpose :interpreter
                                           :mode :frozen
                                           :sync? true})]
                    (swap! worlds assoc world-id handle)
                    world-id))
         'interpreter!
         (fn [world-id]
           (let [interpreter-id (random-uuid)
                 interpreter
                 (sci/with-detached-context
                   #(macro/create-spin-macro-context
                     {:runtime (:child-ctx (resolve-world world-id))
                      :sci-opts @nested-opts}))]
             (swap! interpreters assoc interpreter-id interpreter)
             interpreter-id))
         'eval-spin
         (fn [world-id interpreter-id source]
           (let [runtime (:child-ctx (resolve-world world-id))
                 interpreter (or (get @interpreters interpreter-id)
                                 (throw
                                  (ex-info "Unknown nested interpreter"
                                           {:interpreter-id interpreter-id})))
                 task (binding [ec/*execution-context* runtime]
                        (sci/eval-string* interpreter source))]
             (boundary/wrap-spin-for-sci task runtime)))}
        opts {:namespaces {'spindel.world world-ns}}
        _ (reset! nested-opts opts)
        outer (macro/create-spin-macro-context
               {:runtime root :sci-opts opts})]
    (try
      (let [nested-source
            "(require '[org.replikativ.spindel.spin.cps :refer [spin]]) (spin 41)"
            outer-source
            (str
             "(require '[spindel.world :as world] "
             "         '[org.replikativ.spindel.spin.cps :refer [spin]] "
             "         '[org.replikativ.spindel.effects.await :refer [await]]) "
             "(let [child (world/fork!) "
             "      interpreter (world/interpreter! child) "
             "      nested-task (world/eval-spin child interpreter "
             (pr-str nested-source)
             ") "
             "      task (spin (inc (await nested-task)))] "
             "  {:world-id child :task task :value @task})")
            {:keys [world-id task value] :as result}
            (binding [ec/*execution-context* root]
              (sci/eval-string* outer outer-source))
            world (resolve-world world-id)
            task-id (spin-core/spin-id task)]
        (testing "the interpreter and its computation are constructed by SCI"
          (is (= 42 value))
          (is (= 42 (:payload (binding [ec/*execution-context* root]
                                (ec/spin-current-result task-id))))
              "the nested boundary returns completion to the caller world")
          (is (nil? (binding [ec/*execution-context* (:child-ctx world)]
                      (ec/spin-current-result task-id)))
              "the nested task runtime does not steal the caller's completion")
          (is (= :interpreter
                 (:fork/purpose (ygg/fork-descriptor world))))
          (is (= (:fork-id root)
                 (:fork/parent (ygg/fork-descriptor world)))))
        (testing "the parent retains affine settlement authority"
          (is (ygg/open-fork? world))
          (binding [ec/*execution-context* root]
            (is (nil? (ygg/discard-fork! world {:sync? true}))))
          (is (not (ygg/open-fork? world))))
        (is (= #{:world-id :task :value} (set (keys result))))
        (is (uuid? world-id)
            "SCI receives an opaque identifier, never the affine handle"))
      (finally
        (ctx/stop-context! root)))))
