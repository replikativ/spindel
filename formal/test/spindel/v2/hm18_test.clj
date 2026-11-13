(ns spindel.v2.hm18-test
  "Loading spindel.v2.hm18 kernel-checks the Rule R lemmas for the h-mem2 bundle h3 
  detach, the demote fold, the pass, the filter, the loop; then the step invariant p3m and unconditional L5 safety."
  (:require [clojure.test :refer [deftest is]]
            [spindel.v2.hm18]))

(def theorems '[h18-detach-source h18-detach h18-demote-x h18-nh-demote h18-demote-fold h18-fb-init h18-pass-end
                h18-norm-round h18-normalize h18-filter-k h18-filter h18-rule-r step-h3 step-p3m p3m-empty
                step-h3-total l5-safety-total step-h-mem2-total])

(deftest proved-without-sorry
  (let [src (slurp "src/spindel/v2/hm18.clj")]
    (is (not (re-find #"sorry" src)))
    (doseq [t theorems] (is (re-find (re-pattern (str "\\(a/theorem " t " ")) src) (str t)))))
