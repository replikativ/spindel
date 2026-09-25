(ns org.replikativ.spindel.atom-missing-state-test
  "An atom's state lives in the context that created it and in that context's
   forks. Rebinding within that lineage is how forking works and must stay
   silent; an access from outside it (a sibling, or an ancestor of the
   creating context) finds no state and is signalled."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.atom :as ratom]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as sched]
            [org.replikativ.spindel.spin.sync :as sync]))

(use-fixtures :each
  (fn [f]
    (let [prev @ratom/missing-state-mode]
      (reset! ratom/missing-state-mode :throw)
      (try (f) (finally (reset! ratom/missing-state-mode prev))))))

(defn- missing? [f]
  (try (f) false
       (catch clojure.lang.ExceptionInfo e
         (= ::ratom/missing-state (:type (ex-data e))))))

(deftest rebinding-within-the-lineage-is-silent
  (let [root (ctx/create-execution-context :executor (sched/default-executor))]
    (try
      (binding [ec/*execution-context* root]
        (let [a (ratom/create-atom 1)
              child (ctx/fork-context root)
              grandchild (ctx/fork-context child)]
          (testing "a fork reads through to the creating context and writes its own copy"
            (binding [ec/*execution-context* grandchild]
              (is (= 1 @a))
              (swap! a inc)
              (is (= 2 @a)))
            (is (= 1 @a) "the creating context is untouched"))
          (testing "a deferred delivered in a fork of its context"
            (let [d (sync/deferred)]
              (binding [ec/*execution-context* child]
                (is (= :v (sync/deliver! d :v))))))
          (testing "a mailbox posted in a fork of its context"
            (let [m (sync/mailbox)]
              (binding [ec/*execution-context* grandchild]
                (is (nil? (sync/post! m :msg)))
                (is (nil? (m :msg))))))))
      (finally (ctx/stop-context! root)))))

(deftest access-from-outside-the-lineage-is-signalled
  (let [root (ctx/create-execution-context :executor (sched/default-executor))]
    (try
      (binding [ec/*execution-context* root]
        (let [left (ctx/fork-context root)
              right (ctx/fork-context root)
              a (binding [ec/*execution-context* left] (ratom/create-atom 0))
              d (binding [ec/*execution-context* left] (sync/deferred))]
          (testing "a sibling world has no state for the atom"
            (binding [ec/*execution-context* right]
              (is (missing? #(deref a)))
              (is (missing? #(swap! a inc)))))
          (testing "nor does the parent of the context that created it"
            (is (missing? #(deref a)))
            (is (missing? #(sync/deliver! d :v))))
          (testing "a mailbox, posted from outside its world"
            (let [m (binding [ec/*execution-context* left] (sync/mailbox))]
              (binding [ec/*execution-context* right]
                (is (missing? #(sync/post! m :msg)))
                (is (missing? #(m :msg))))
              (is (missing? #(sync/post! m :msg)) "nor from the parent")
              (binding [ec/*execution-context* left]
                (is (nil? (sync/post! m :msg)) "its own world posts"))))
          (testing "the creating world still works"
            (binding [ec/*execution-context* left]
              (is (= 0 @a))
              (is (= :v (sync/deliver! d :v)))))))
      (finally (ctx/stop-context! root)))))

(deftest the-default-mode-warns-and-keeps-the-old-behaviour
  (reset! ratom/missing-state-mode :warn)
  (let [root (ctx/create-execution-context :executor (sched/default-executor))]
    (try
      (binding [ec/*execution-context* root]
        (let [child (ctx/fork-context root)
              a (binding [ec/*execution-context* child] (ratom/create-atom 7))]
          (is (nil? @a) "a warning, and the nil it always answered")))
      (finally (ctx/stop-context! root)))))
