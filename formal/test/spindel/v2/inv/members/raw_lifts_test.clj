(ns spindel.v2.inv.members.raw-lifts-test
  "Loading spindel.v2.inv.members.raw-lifts kernel-checks the raw lifts of the h-mem2 bundle h3 and its T22 host
  await and T8 observe cases."
  (:require [clojure.test :refer [deftest is]]
            [spindel.v2.inv.members.raw-lifts]))

(def theorems '[h15-raw0g-lift h15-raw-lift h15-host-await-raw-h3 h15-raw0-host-await-h3 h15-t8-full-h3])

(deftest proved-without-sorry
  (let [src (slurp "src/spindel/v2/inv/members/raw_lifts.clj")]
    (is (not (re-find #"sorry" src)))
    (doseq [t theorems] (is (re-find (re-pattern (str "\\(a/theorem " t " ")) src) (str t)))))
