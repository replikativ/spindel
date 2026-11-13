(ns spindel.v2.hm17-test
  "Loading spindel.v2.hm17 kernel-checks release-world for the h-mem2 bundle h3."
  (:require [clojure.test :refer [deftest is]]
            [spindel.v2.hm17]))

(def theorems '[h17-host-free h17-revoke-roots h17-t-release-world])

(deftest proved-without-sorry
  (let [src (slurp "src/spindel/v2/hm17.clj")]
    (is (not (re-find #"sorry" src)))
    (doseq [t theorems] (is (re-find (re-pattern (str "\\(a/theorem " t " ")) src) (str t)))))
