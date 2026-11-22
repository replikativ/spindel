(ns spindel.v2.inv.alive-runs-test
  "Loading spindel.v2.inv.alive-runs kernel-checks AR (every alive run of a computation is its C.run, I10's computation part)
  through the step: `step-alive-run-latest` (i7-idle, acts-parked, alive-run-latest of the input, rule-r-safe of the raw world) and `alive-run-latest-i10-comp`
  (the literal `inv-i10-comp`). The random tripwire is hm3_test's `ar-random`."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.inv.alive-runs]))

(def theorems
  '[alive-run-latest-well-formed alive-run-latest-intro alive-run-latest-use alive-run-latest-comp-upd alive-run-latest-run-upd-m alive-run-latest-run-upd-a alive-run-latest-comp-ins-fresh alive-run-latest-k-clear alive-run-latest-none-of-dead
    alive-run-latest-clear-comp-run alive-run-latest-t13-retire-with-subtree alive-run-latest-job-apply alive-run-latest-run-cascade alive-run-latest-park-if alive-run-latest-take-park alive-run-latest-add-run-scope alive-run-latest-spawn-rows
    alive-run-latest-startable-none alive-run-latest-start-raw alive-run-latest-t5-start alive-run-latest-cancel-pred-none alive-run-latest-dispatch-raw alive-run-latest-t11-dispatch alive-run-latest-demote-finish alive-run-latest-demote
    alive-run-latest-normalize alive-run-latest-raw alive-run-latest-rule-r step-alive-run-latest alive-run-latest-empty alive-run-latest-i10-comp])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
