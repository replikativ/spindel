(ns org.replikativ.spindel.catalog-merge-base-test
  (:require [clojure.test :refer [is]]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [org.replikativ.spindel.test-async :refer [deftest-async <?]]
            [yggdrasil.protocols :as yp]
            #?(:clj [is.simm.partial-cps.async :refer [async]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.test-async :refer [deftest-async <?]]
                            [is.simm.partial-cps.async :refer [async]])))

(defn- catalog [parents]
  (let [graph {:nodes (into {} (map (fn [[id ids]] [id {:parent-ids (set ids)}])) parents)}]
    (reify yp/Graphable
      (commit-graph [_] #?(:clj graph :cljs (async graph)))
      (commit-graph [_ _] #?(:clj graph :cljs (async graph))))))

(deftest-async independent-catalogs-have-a-common-base
  (let [child (catalog {"base" [] "child" ["base"]})
        parent (catalog {"base" [] "parent" ["base"]})]
    (is (= "base" (<? (#'ygg/catalog-merge-base child "child" parent "parent"))))))

(deftest-async imported-history-advances-the-actual-merge-base
  (let [child (catalog {"base" [] "observed" ["base"] "child" ["observed"]})
        parent (catalog {"base" [] "observed" ["base"] "later" ["observed"]})]
    (is (= "observed" (<? (#'ygg/catalog-merge-base child "child" parent "later")))
        "The creation-time base is not the base after observing parent history")))

(deftest-async missing-tip-does-not-invent-an-ancestor
  (let [system (catalog {"base" []})]
    (is (nil? (<? (#'ygg/catalog-merge-base system "missing" system "base"))))))

(deftest-async redundant-parent-does-not-select-an-older-base
  (let [child (catalog {"base" [] "observed" ["base"] "child" ["observed" "base"]})
        parent (catalog {"base" [] "observed" ["base"] "parent" ["observed" "base"]})]
    (is (= "observed" (<? (#'ygg/catalog-merge-base child "child" parent "parent"))))))
