(ns org.replikativ.spindel.fork-coherence-test
  "What a fork sees of its parent after the fork, pinned as behaviour.

  A following fork (the default) is a workspace: it falls through to the
  parent per path until it touches that path, and a read inside a spin
  touches it. Nothing is pushed into the child, and one view can combine a
  path it pinned with a path the parent has since recomputed. That is the
  contract for an isolated agent that follows along; it is not a coherent
  view. A frozen fork is: it is the parent at fork time plus its own writes."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.signal :refer [signal]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]))

(defn- in [c f] (binding [ec/*execution-context* c] (f)))

(defn- eventually
  "Poll `f` until it returns `expected` or 3 s pass; returns the last value."
  [expected f]
  (loop [waited 0]
    (let [v (f)]
      (if (or (= expected v) (>= waited 3000))
        v
        (do (Thread/sleep 20) (recur (+ waited 20)))))))

(defn- quiet
  "Let the engine run for a moment, for assertions that something did NOT
  happen."
  []
  (Thread/sleep 300))

(deftest a-childs-writes-stay-in-the-child
  (let [p (ctx/create-execution-context)
        a (in p #(signal 1))
        c (ctx/fork-context p)]
    (in c #(reset! a 5))
    (is (= 5 (in c #(deref a))))
    (is (= 1 (in p #(deref a))))))

(deftest following-falls-through-until-the-child-touches-a-path
  (let [p (ctx/create-execution-context)
        a (in p #(signal 1))
        e (in p #(spin (* 10 (:new (track a)))))
        _ (in p #(deref e))
        c (ctx/fork-context p)]
    (in p #(reset! a 2))
    (testing "untouched: the parent's later value, and what the parent derived from it"
      (is (= 2 (eventually 2 #(in c (fn [] (deref a))))))
      (is (= 20 (eventually 20 #(in c (fn [] @(spin (await e))))))))
    (testing "a read inside a spin touches the path: the child keeps its value"
      (in c #(deref (spin (:new (track a)))))
      (in p #(reset! a 3))
      (is (= 30 (eventually 30 #(in p (fn [] (deref e))))))
      (quiet)
      (is (= 2 (in c #(deref a))) "pinned at the value the child read"))))

(deftest nothing-is-pushed-into-the-child
  (let [p (ctx/create-execution-context)
        a (in p #(signal 1))
        child-runs (atom [])
        parent-runs (atom [])
        c (ctx/fork-context p)]
    (in c #(deref (spin (let [v (:new (track a))] (swap! child-runs conj v) v))))
    (in p #(deref (spin (let [v (:new (track a))] (swap! parent-runs conj v) v))))
    (in p #(reset! a 2))
    (is (= [1 2] (eventually [1 2] #(deref parent-runs))))
    (quiet)
    (is (= [1] @child-runs) "the child's spin is not re-run by a parent change")))

(deftest a-following-view-can-mix-pinned-and-recomputed-paths
  (let [p (ctx/create-execution-context)
        a (in p #(signal 1))
        d (in p #(spin (* 10 (:new (track a)))))
        _ (in p #(deref d))
        c (ctx/fork-context p)]
    ;; the child pins a at 1 by reading it in a spin; d stays untouched
    (in c #(deref (spin (:new (track a)))))
    (in p #(reset! a 2))
    (is (= 20 (eventually 20 #(in p (fn [] (deref d))))))
    (quiet)
    (is (= [1 20] [(in c #(deref a)) (in c #(deref (spin (await d))))])
        "a = 1 next to d = 10·a = 20: the view is per path, not coherent")))

(deftest a-frozen-fork-is-the-parent-at-fork-time
  (let [p (ctx/create-execution-context)
        a (in p #(signal 1))
        d (in p #(spin (* 10 (:new (track a)))))
        _ (in p #(deref d))
        c (ctx/fork-context p :mode :frozen)]
    (in p #(reset! a 2))
    (is (= 20 (eventually 20 #(in p (fn [] (deref d))))))
    (quiet)
    (is (= [1 10] [(in c #(deref a)) (in c #(deref (spin (await d))))]))
    (testing "and its own writes"
      (in c #(reset! a 4))
      (is (= 40 (eventually 40 #(in c (fn [] (deref (spin (await d)))))))))))
