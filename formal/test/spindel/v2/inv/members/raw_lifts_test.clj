(ns spindel.v2.inv.members.raw-lifts-test
  "Loading spindel.v2.inv.members.raw-lifts kernel-checks the raw lifts of the h-mem2 bundle current-members and its T22 host
  await and T8 observe cases."
  (:require [clojure.test :refer [deftest is]]
            [spindel.v2.inv.members.raw-lifts]))

(def theorems '[current-members-host-guarded-transition-lift current-members-raw-lift current-members-host-await-raw current-members-transition-host-await current-members-t8-observe-any-kind])

(deftest proved-without-sorry
  (let [src (slurp "src/spindel/v2/inv/members/raw_lifts.clj")]
    (is (not (re-find #"sorry" src)))
    (doseq [t theorems] (is (re-find (re-pattern (str "\\(a/theorem " t " ")) src) (str t)))))
