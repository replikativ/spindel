(ns spindel.v2.hm16-test
  "Loading spindel.v2.hm16 kernel-checks T12 complete and settle for the h-mem2 bundle h3."
  (:require [clojure.test :refer [deftest is]]
            [spindel.v2.hm16]))

(def theorems '[h16-complete-task-x h16-se-fold h16-undo2 h16-dis h16-settle-step h16-settle-loop h16-settle-x
                h16-complete-comp-x h16-complete-pre h16-complete-raw-x h16-t12-h3])

(deftest proved-without-sorry
  (let [src (slurp "src/spindel/v2/hm16.clj")]
    (is (not (re-find #"sorry" src)))
    (doseq [t theorems] (is (re-find (re-pattern (str "\\(a/theorem " t " ")) src) (str t)))))
