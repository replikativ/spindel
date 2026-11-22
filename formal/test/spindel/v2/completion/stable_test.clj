(ns spindel.v2.completion.stable-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.completion.stable]))

(def theorems
  '[th-find-upd task-unheld-scope-absent-task-upd task-unheld-scope-absent-task-tcr task-unheld-scope-absent-task-tcl task-unheld-scope-absent-rest-scope-ins task-unheld-scope-absent-rest-task-ins task-unheld-scope-absent-rest-filter
    task-unheld-scope-absent-complete-body task-unheld-scope-absent-complete-raw task-unheld-scope-absent-t12-complete task-unheld-scope-absent-raw task-unheld-scope-absent-normalize task-unheld-scope-absent-rule-r step-task-unheld-scope-absent
    task-complete-stable scope-complete-stable])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
