(ns org.replikativ.spindel.sci.context-test
  "SCI code names its execution context, never holds it: the world is the one
  the host binds around an evaluation."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.sci.macro :as macro]
            [org.replikativ.spindel.sci.world :as world]
            [org.replikativ.spindel.spin.core :as spin-core]
            [sci.core :as sci]))

(def ^:private prelude
  "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
            '[org.replikativ.spindel.effects.await :refer [await]]
            '[org.replikativ.spindel.engine.core :as ec]) ")

(deftest sci-code-sees-the-current-world-by-name
  (let [rt (context/create-execution-context)
        sci-ctx (macro/create-spin-macro-context {})]
    (try
      (binding [ec/*execution-context* rt]
        (sci/eval-string* sci-ctx prelude)
        (testing "the context is a name, with nothing in it"
          (is (identical? macro/current-world (sci/eval-string* sci-ctx "(ec/current-execution-context)")))
          (is (identical? macro/current-world (sci/eval-string* sci-ctx "ec/*execution-context*")))
          (is (= [nil nil nil false]
                 (sci/eval-string* sci-ctx "(let [c (ec/current-execution-context)] [(:running c) (:backend c) (:parent-ctx c) (map? c)])")))
          (is (thrown? Exception (sci/eval-string* sci-ctx "(swap! (:running (ec/current-execution-context)) not)")))
          (is (true? @(:running rt)) "the engine is untouched"))
        (testing "spins still run"
          (is (= 42 @(sci/eval-string* sci-ctx "(spin (* 6 (await (spin 7))))")))))
      (testing "without a bound world, naming it fails as the host fn does"
        (is (thrown? Exception (sci/eval-string* sci-ctx "(ec/current-execution-context)"))))
      (finally (context/close-context! rt)))))

(deftest a-held-world-name-follows-the-binding-into-forks
  (let [parent (context/create-execution-context)
        interpreter (world/create! parent {})
        _ (binding [ec/*execution-context* parent]
            (world/eval-string* interpreter (str prelude "(def held (ec/current-execution-context))")))
        ;; the fork copies the interpreter, `held` included
        child (context/fork-context parent :mode :frozen)]
    (try
      (let [s (binding [ec/*execution-context* child]
                (world/eval-string* interpreter "(ec/with-context held (spin 5))"))
            id (spin-core/spin-id s)]
        (is (= 5 (binding [ec/*execution-context* child] @s)))
        (is (some? (binding [ec/*execution-context* child] (ec/get-state [:nodes id]))))
        (is (nil? (binding [ec/*execution-context* parent] (ec/get-state [:nodes id])))
            "a name held from the parent's evaluation does not reach the parent"))
      (finally
        (context/close-context! child)
        (context/close-context! parent)))))

(deftest host-vars-are-out-of-reach
  (let [rt (context/create-execution-context)
        sci-ctx (macro/create-spin-macro-context {})]
    (try
      (binding [ec/*execution-context* rt]
        (testing "Var and Namespace are names, not interop surfaces"
          (doseq [code ["(@(clojure.lang.Var/find 'clojure.core/eval) '(+ 1 2))"
                        "(clojure.lang.Var/getThreadBindings)"
                        "(clojure.lang.Namespace/find 'clojure.core)"]]
            (is (thrown? Exception (sci/eval-string* sci-ctx code)) code)))
        (is (false? (sci/eval-string* sci-ctx "(instance? clojure.lang.Var 1)")) "the name still resolves"))
      (finally (context/close-context! rt)))))

(deftest bound-fns-run-in-the-fork-they-are-called-in
  (let [parent (context/create-execution-context)
        interpreter (world/create! parent {})
        _ (binding [ec/*execution-context* parent]
            (world/eval-string* interpreter (str prelude "(def x 0) (def f (is.simm.partial-cps.runtime/bound-fn (fn [] (spin 1)))) (def read-x (is.simm.partial-cps.runtime/bound-fn (fn [] x)))")))
        child (context/fork-context parent :mode :frozen)
        unrelated (context/create-execution-context)]
    (try
      (let [s (binding [ec/*execution-context* child] (world/eval-string* interpreter "(f)"))
            id (spin-core/spin-id s)]
        (is (some? (binding [ec/*execution-context* child] (ec/get-state [:nodes id]))))
        (is (nil? (binding [ec/*execution-context* parent] (ec/get-state [:nodes id])))))
      (testing "and on the fork's interpreter: its vars, not the parent's"
        (is (= 1 (binding [ec/*execution-context* child] (world/eval-string* interpreter "(def x 1) (read-x)"))))
        (is (= 0 (binding [ec/*execution-context* parent] (world/eval-string* interpreter "(read-x)")))))
      (testing "called from an unrelated world, it keeps its own"
        (let [g (binding [ec/*execution-context* parent] (world/eval-string* interpreter "f"))
              id (spin-core/spin-id (binding [ec/*execution-context* unrelated] (g)))]
          (is (some? (binding [ec/*execution-context* parent] (ec/get-state [:nodes id]))))
          (is (nil? (binding [ec/*execution-context* unrelated] (ec/get-state [:nodes id]))))))
      (finally
        (context/close-context! unrelated)
        (context/close-context! child)
        (context/close-context! parent)))))
