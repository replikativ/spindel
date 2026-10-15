(ns org.replikativ.spindel.sci.boundary-test
  "The functional SCI context holds no world: its spins register in the world
   the host selected for the evaluation, created by the calling spin."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.sci.boundary :as boundary]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [sci.core :as sci]))

(defn- make-spin-source [id]
  (str "(require '[spindel.spin :as spin])"
       "(spin/make-spin (fn [resolve reject] (resolve 42)) " id ")"))

(defn- node [world id] (rtp/get-state world [:nodes id]))

(deftest spins-register-in-the-selected-world
  (testing "an unrelated world"
    (let [a (ctx/create-execution-context)
          b (ctx/create-execution-context)
          ;; built while a was the world, as an older caller would
          sci-ctx (boundary/create-spindel-sci-context {:runtime a})
          s (binding [ec/*execution-context* b]
              (sci/eval-string* sci-ctx (make-spin-source ::in-b)))]
      (is (= 42 (binding [ec/*execution-context* b] @s)))
      (is (some? (node b ::in-b)))
      (is (nil? (node a ::in-b)) "the world it was built in is untouched")))
  (testing "a fork"
    (let [a (ctx/create-execution-context)
          fork (ctx/fork-context a)
          sci-ctx (boundary/create-spindel-sci-context {:runtime a})]
      (binding [ec/*execution-context* fork]
        (sci/eval-string* sci-ctx (make-spin-source ::in-fork)))
      (is (some? (node fork ::in-fork)))
      (is (nil? (node a ::in-fork)) "the fork does not write into its parent"))))

(deftest no-world-no-spin
  (let [a (ctx/create-execution-context)
        sci-ctx (boundary/create-spindel-sci-context {:runtime a})]
    (is (thrown? Exception (sci/eval-string* sci-ctx (make-spin-source ::nowhere))))
    (is (nil? (node a ::nowhere)) "not in the world it was built in")))

(deftest the-calling-spin-creates-the-spin
  (let [a (ctx/create-execution-context)
        sci-ctx (boundary/create-spindel-sci-context {})
        [parent child] (binding [ec/*execution-context* a]
                         @(spin [ec/*spin-id*
                                 (spin-core/spin-id
                                  (sci/eval-string* sci-ctx (make-spin-source ::child)))]))]
    (is (= ::child child))
    (is (= parent (:created-by (node a child))))
    (is (contains? (:created-spins (node a parent)) child))))

(deftest an-explicit-handle-keeps-its-world-to-itself
  ;; Lock-in: interop is gated to the class allowlist, which does not name
  ;; BoundaryTask (this passes before the fix too).
  (let [a (ctx/create-execution-context)
        task (binding [ec/*execution-context* a] (spin 7))
        handle (boundary/wrap-spin-for-sci task a)
        sci-ctx (boundary/create-spindel-sci-context {})
        call (fn [source] ((binding [ec/*execution-context* a] (sci/eval-string* sci-ctx source)) handle))]
    (doseq [source ["(fn [h] (.-runtime h))"
                    "(fn [h] (.runtime h))"
                    "(fn [h] (.-task h))"]]
      (is (thrown-with-msg? Exception #"not allowed"
                            (binding [ec/*execution-context* a] (call source)))
          source))
    (testing "a hint makes the read look on the hinted class, which has no such field"
      (is (thrown? Exception (binding [ec/*execution-context* a]
                               (call "(fn [h] (.-runtime ^clojure.lang.IFn h))")))))
    (testing "the handle still runs"
      (is (= 7 (binding [ec/*execution-context* a] @handle))))))
