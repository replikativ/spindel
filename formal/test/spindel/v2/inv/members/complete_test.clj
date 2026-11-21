(ns spindel.v2.inv.members.complete-test
  "Loading spindel.v2.inv.members.complete kernel-checks T12 complete and settle for the h-mem2 bundle current-members."
  (:require [clojure.test :refer [deftest is]]
            [spindel.v2.inv.members.complete]))

(def theorems '[current-members-complete-task-x current-members-se-fold current-members-undo2 current-members-dis current-members-settle-step current-members-settle-loop current-members-settle-x
                current-members-complete-comp-x current-members-complete-pre current-members-complete-raw-x current-members-t12-complete])

(deftest proved-without-sorry
  (let [src (slurp "src/spindel/v2/inv/members/complete.clj")]
    (is (not (re-find #"sorry" src)))
    (doseq [t theorems] (is (re-find (re-pattern (str "\\(a/theorem " t " ")) src) (str t)))))
