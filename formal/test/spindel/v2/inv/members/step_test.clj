(ns spindel.v2.inv.members.step-test
  "Loading spindel.v2.inv.members.step kernel-checks the Rule R lemmas for the h-mem2 bundle current-members 
  detach, the demote fold, the pass, the filter, the loop; then the step invariant chain and unconditional L5 safety."
  (:require [clojure.test :refer [deftest is]]
            [spindel.v2.inv.members.step]))

(def theorems '[current-members-detach-source current-members-detach current-members-demote-x current-members-nh-demote current-members-demote-fold current-members-members-round-frame-init current-members-pass-end
                current-members-normalize-round current-members-normalize current-members-filter-k current-members-filter current-members-rule-r step-current-members step-chain chain-empty
                step-current-members-total l5-safety-total step-h-mem2-total])

(deftest proved-without-sorry
  (let [src (slurp "src/spindel/v2/inv/members/step.clj")]
    (is (not (re-find #"sorry" src)))
    (doseq [t theorems] (is (re-find (re-pattern (str "\\(a/theorem " t " ")) src) (str t)))))
