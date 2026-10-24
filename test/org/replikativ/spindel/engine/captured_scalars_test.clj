(ns org.replikativ.spindel.engine.captured-scalars-test
  "A re-registered spin re-runs only when its captured environment changed.
  A captured number is boxed afresh each time the enclosing body computes
  it (a double, a Long outside the JVM's small-Long cache), so identity
  alone called it changed: every keyed child capturing one re-ran each
  time its parent's body ran again."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]))

(deftest equal-captured-scalars-keep-the-cached-child
  (let [ctx (ctx/create-execution-context)
        runs (atom {})
        child (fn [i x k]
                (spin (swap! runs update i (fnil inc 0)) [i x k]))
        n 300]
    (try
      (binding [ec/*execution-context* ctx]
        (let [parent (spin
                      (loop [i 0 acc 0]
                        (if (= i n)
                          acc
                          (let [[j] (await (addressing/with-key i
                                             (child i (* 1.5 i) (keyword (str "k" i)))))]
                            (recur (inc i) (+ acc j))))))]
          (is (= (reduce + (range n)) @parent))
          ;; the parent's body runs again from its start: every child is
          ;; re-registered with captures equal to the first run's
          (ec/spin-mark-dirty! (spin-core/spin-id parent))
          (is (= (reduce + (range n)) @parent))
          (is (= #{1} (set (vals @runs)))
              (str "children re-run: " (sort (keep (fn [[i c]] (when (> c 1) i)) @runs))))))
      (finally (ctx/stop-context! ctx)))))
