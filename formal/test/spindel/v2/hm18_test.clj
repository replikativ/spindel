(ns spindel.v2.hm18-test
  "Loading spindel.v2.hm18 kernel-checks the Rule R lemmas for the h-mem2 bundle h3 (so far: detach)."
  (:require [clojure.test :refer [deftest is]]
            [spindel.v2.hm18]))

(def theorems '[h18-detach-source h18-detach])

(deftest proved-without-sorry
  (let [src (slurp "src/spindel/v2/hm18.clj")]
    (is (not (re-find #"sorry" src)))
    (doseq [t theorems] (is (re-find (re-pattern (str "\\(a/theorem " t " ")) src) (str t)))))
