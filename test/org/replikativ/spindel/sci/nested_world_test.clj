(ns org.replikativ.spindel.sci.nested-world-test
  "Characterize recursive interpreter construction through explicit capabilities."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.sci.boundary :as boundary]
            [org.replikativ.spindel.sci.macro :as macro]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [sci.core :as sci]))

(deftest sci-program-can-construct-and-run-a-spindel-sci-child-world
  (let [root (ctx/create-execution-context)
        nested-opts (atom nil)
        world-ns
        {'fork! (fn []
                  (ygg/fork! {:purpose :interpreter :sync? true}))
         'interpreter
         (fn [fork]
           (macro/create-spin-macro-context
            {:runtime (:child-ctx fork)
             :sci-opts @nested-opts}))
         'eval-spin
         (fn [fork interpreter source]
           (let [runtime (:child-ctx fork)
                 task (binding [ec/*execution-context* runtime]
                        (sci/eval-string* interpreter source))]
             (boundary/wrap-spin-for-sci task runtime)))}
        opts {:namespaces {'spindel.world world-ns}}
        _ (reset! nested-opts opts)
        outer (macro/create-spin-macro-context
               {:runtime root :sci-opts opts})]
    (try
      (let [{:keys [world value] :as result}
            (binding [ec/*execution-context* root]
              (sci/eval-string*
               outer
               (str
                "(require '[spindel.world :as world] "
                "         '[org.replikativ.spindel.spin.cps :refer [spin]] "
                "         '[org.replikativ.spindel.effects.await :refer [await]]) "
                "(let [child (world/fork!) "
                "      interpreter (world/interpreter child) "
                "      task (world/eval-spin "
                "            child interpreter "
                "            \"(require '[org.replikativ.spindel.spin.cps :refer [spin]]) (spin 41)\")] "
                "  {:world child :value @(spin (inc (await task)))})")))]
        (testing "the interpreter and its computation are constructed by SCI"
          (is (= 42 value))
          (is (= :interpreter
                 (:fork/purpose (ygg/fork-descriptor world))))
          (is (= (:fork-id root)
                 (:fork/parent (ygg/fork-descriptor world)))))
        (testing "the parent retains affine settlement authority"
          (is (ygg/open-fork? world))
          (binding [ec/*execution-context* root]
            (is (nil? (ygg/discard-fork! world {:sync? true}))))
          (is (not (ygg/open-fork? world))))
        (is (= #{:world :value} (set (keys result)))))
      (finally
        (ctx/stop-context! root)))))
