(ns spindel.v2.layer2.skip-test
  "Loading spindel.v2.layer2.skip kernel-checks that skipping ids keeps the layer-1 bundle: the worlds
  of a family share one allocator, so each sees `next-id` jump between its own items."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.layer2.skip]))

(deftest theorems-kernel-checked
  (doseq [t '[chain-start-skip chain-to-i10-current-skip chain-to-i11a-skip chain-to-i1-scopes-skip chain-to-i5-dep-final-skip chain-to-i1-detached-closed-skip chain-to-i1-runs-skip chain-to-i8-closed-skip chain-to-comp-facts-skip chain-to-i14-ordered-skip
              chain-to-marks-waiting-skip chain-to-marks-waiting-skip-ids]]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
