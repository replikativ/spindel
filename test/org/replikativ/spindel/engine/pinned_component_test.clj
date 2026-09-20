(ns org.replikativ.spindel.engine.pinned-component-test
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.component :as component]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]))

(deftest a-fork-reads-the-version-its-source-pinned
  (let [root (context/create-execution-context)
        ;; one store for every world: {version parameters}
        store (atom {0 {:w 1.0}})
        read (fn [s version] (get @s version))]
    (try
      (let [params (binding [ec/*execution-context* root]
                     (component/register! :policy/params (component/pinned store 0 read)))
            rollout (context/fork-context root :mode :frozen)]
        (testing "a training step makes a new version and moves the trainer's pin"
          (swap! store assoc 1 {:w 2.0})
          (binding [ec/*execution-context* root]
            (component/repin! params 1)
            (is (= {:w 2.0} (component/resolve params)))
            (is (= 1 (component/pinned-version params)))))
        (testing "the rollout forked before keeps the version it started under"
          (is (= {:w 1.0} (component/resolve-in rollout params)))
          (is (= 0 (component/pinned-version rollout params))))
        (testing "and a fork taken now starts under the new one"
          (is (= 1 (component/pinned-version (context/fork-context root :mode :frozen)
                                             params)))))
      (finally (context/stop-context! root)))))

(deftest only-a-pinned-component-is-repinned
  (let [root (context/create-execution-context)]
    (try
      (binding [ec/*execution-context* root]
        (let [ref (component/register! :plain (component/shared {:a 1}))]
          (is (nil? (component/pinned-version ref)))
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Not a pinned"
                                (component/repin! ref 1)))))
      (finally (context/stop-context! root)))))
