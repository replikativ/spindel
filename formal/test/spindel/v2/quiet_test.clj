(ns spindel.v2.quiet-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.quiet]))

(def theorems '[step-grel step-released step-gk step-k k-empty])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
