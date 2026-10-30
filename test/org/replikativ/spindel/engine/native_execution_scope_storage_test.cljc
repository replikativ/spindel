(ns org.replikativ.spindel.engine.native-execution-scope-storage-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.lifetime :as lifetime]))

(def scope-storage-keys
  [:execution-scope-rows :execution-scope-parent-buckets
   :execution-scope-parent-memberships :execution-scope-owned-memberships
   :execution-scope-run-memberships])

(defn- scope-storage [rt]
  (select-keys (owned/storage-stats rt) scope-storage-keys))

(deftest scope-churn-reclaims-real-owner-and-membership-tables
  (let [rt (owned/runtime)
        baseline (scope-storage rt)]
    (try
      (is (= (zipmap scope-storage-keys (repeat 0)) baseline))
      (let [closed (loop [remaining 128 kept []]
                     (if (zero? remaining) kept
                         (let [cap (lifetime/open-scope! rt :explicit)]
                           (is (= 1 (:execution-scope-rows (scope-storage rt))))
                           (is (nil? (lifetime/close-scope! rt cap)))
                           (is (= baseline (scope-storage rt)))
                           (recur (dec remaining) (conj kept cap)))))
            open (vec (repeatedly 32 #(lifetime/open-scope! rt :explicit)))
            child (lifetime/open-scope! rt :nested (first open))
            grandchild (lifetime/open-scope! rt :nested child)]
        (is (= 34 (:scope-balance (owned/snapshot rt))))
        (is (= 34 (:execution-scope-rows (scope-storage rt))))
        (is (= 3 (:execution-scope-parent-buckets (scope-storage rt))))
        (is (= 34 (:execution-scope-parent-memberships (scope-storage rt))))
        (doseq [cap open] (is (nil? (lifetime/close-scope! rt cap))))
        (doseq [cap (conj closed child grandchild)]
          (is (nil? (lifetime/close-scope! rt cap))))
        (is (= 128 (count closed)) "Escaped immutable capabilities remain held throughout churn")
        (is (= baseline (scope-storage rt)))
        (is (= 1 (count (:scopes (owned/snapshot rt)))))
        (is (zero? (:scope-balance (owned/snapshot rt))))
        (is (= 162 (:next-scope (owned/snapshot rt)))))
      (finally (context/release-context! rt)))))
