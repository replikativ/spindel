(ns spindel.v2.pres.tree-test
  "The generic tree's override points (R3) against the copier: every composite of the tree that some
  bundle overrides with override! is an Over field (listed in `over-targets`), so a part's own proof can
  replace the generic one there."
  (:require [clojure.test :refer [deftest is]]
            [clojure.set :as set]
            [clojure.string :as str]
            [spindel.v2.top]
            [spindel.v2.progress.measures]
            [spindel.v2.completion.quiet]
            [spindel.v2.completion.quiet-world]
            [spindel.v2.completion.stable]
            [spindel.v2.completion.open-scopes]
            [spindel.v2.completion.drained]
            [spindel.v2.inv.acyclic]
            [spindel.v2.pres.tree :as tree]))

(defn- bundles []
  (for [ns (all-ns) :when (str/starts-with? (str (ns-name ns)) "spindel.v2")
        [_ v] (ns-interns ns) :let [x (try @v (catch Throwable _ nil))]
        :when (and (map? x) (not (sorted? x)) (contains? x :pred) (contains? x :overrides))]
    x))

(deftest over-fields-cover-the-overrides
  (let [targets (set (mapcat #(keys @(:overrides %)) (bundles)))
        comps (:composites @tree/tree)]
    (is (set/subset? (set/intersection comps targets) tree/over-targets))
    (is (= (set (:over @tree/tree)) (set/intersection comps tree/over-targets)))))
