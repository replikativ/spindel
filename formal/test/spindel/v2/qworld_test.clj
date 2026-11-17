(ns spindel.v2.qworld-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.qworld]))

(def theorems '[step-gc step-gc-rest gc-empty step-qinv qinv-empty quiet-rows])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
