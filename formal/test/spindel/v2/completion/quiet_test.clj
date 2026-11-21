(ns spindel.v2.completion.quiet-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.completion.quiet]))

(def theorems '[step-stays-released step-released step-host-roots-revoked step-k k-empty zero-handles-hz host-roots-revoked-t21-release-world host-roots-revoked-transition])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
