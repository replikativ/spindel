(ns spindel.v2.ar-test
  "Loading spindel.v2.ar kernel-checks AR (every alive run of a computation is its C.run, I10's computation part)
  through the step: `step-ar` (g7, ga, ar of the input, rule-r-safe of the raw world) and `ar-i10-comp`
  (the literal `inv-i10-comp`). The random tripwire is hm3_test's `ar-random`."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.ar]))

(def theorems
  '[ar-sample ar-intro ar-use ar-comp-upd ar-run-upd-m ar-run-upd-a ar-comp-ins-fresh ar-k-clear ar-none-of-dead
    ar-clear-comp-run ar-retire-with ar-job-apply ar-run-cascade ar-park-if ar-take-park ar-add-run-scope ar-spawn-rows
    ar-startable-none ar-start-raw t5-ar ar-cancel-pred-none ar-dispatch-raw t11-ar ar-demote-finish ar-demote
    ar-normalize raw-ar ar-rule-r step-ar ar-empty ar-i10-comp])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
