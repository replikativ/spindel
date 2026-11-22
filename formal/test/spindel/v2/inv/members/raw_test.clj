(ns spindel.v2.inv.members.raw-test
  "Loading spindel.v2.inv.members.raw kernel-checks release-world and the assembly over the step items (raw) for the h-mem2 bundle current-members."
  (:require [clojure.test :refer [deftest is]]
            [spindel.v2.inv.members.raw]))

(def theorems '[current-members-host-free current-members-revoke-roots current-members-t21-release-world current-members-transition current-members-raw])

(deftest proved-without-sorry
  (let [src (slurp "src/spindel/v2/inv/members/raw.clj")]
    (is (not (re-find #"sorry" src)))
    (doseq [t theorems] (is (re-find (re-pattern (str "\\(a/theorem " t " ")) src) (str t)))))
