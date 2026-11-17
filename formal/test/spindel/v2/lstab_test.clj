(ns spindel.v2.lstab-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.lstab]))

(def theorems
  '[th-find-upd gst-task-upd gst-task-tcr gst-task-tcl gst-rest-scope-ins gst-rest-task-ins gst-rest-filter
    gst-complete-body gst-complete-raw t12-gst raw-gst gst-normalize gst-rule-r step-gst
    task-complete-stable scope-complete-stable])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
