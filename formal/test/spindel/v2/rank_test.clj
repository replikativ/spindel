(ns spindel.v2.rank-test
  "Loading spindel.v2.rank kernel-checks the I12 height-adjustment theorems; ranks-ok itself is
  checked after every step of the engine scenarios and the random driver (engine-test)."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.rank]))

(def theorems
  '[tbl-all-mem-mono tbl-any-app tbl-any-mono tbl-find-upd-ne comp-rank-set-ne crank-upd-eq comp-rank-set-eq
    comp-has-set-rank raise-inv-done rank-edge-ok-of-lt pend-skip raise-inv-skip dep-cred-mem rjobs-covers
    covers-transfer lt-of-ble-false pend-raise raise-inv-raise raise-loop-ranks pend-of-ranks raise-inv-start
    ranks-ins-noncomp raise-run-ranks await-new-dep-ranks react-add-ranks])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
