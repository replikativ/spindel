(ns spindel.v2.skip-test
  "Loading spindel.v2.skip kernel-checks that skipping ids keeps the layer-1 bundle: the worlds
  of a family share one allocator, so each sees `next-id` jump between its own items."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.skip]))

(deftest theorems-kernel-checked
  (doseq [t '[p3b-skip p3c-skip p3d-skip p3e-skip p3f-skip p3g-skip p3h-skip p3i-skip p3j-skip p3k-skip
              p3l-skip p3l-skip-ids]]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
