(ns spindel.v2.acyc-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.acyc :as acyc]))

(def theorems
  '[cy-acyc-sub cy-acyc-fresh cy-acyc-reparent cy-acyc-of cy-acyc-intro gcy-scope-ins-fresh gcy-set-parent
    gcy-add-run-scope t-detach-gcy t-open-scope-gcy gcy-spawn-rows raw-gcy gcy-normalize gcy-rule-r step-gcy gcy-empty
    step-acyc acyc-empty step-acyclic step-acyclic-reach])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

(deftest acyclic-executable
  (is (true? (acyc/scopes-acyclic s/empty-world)))
  (let [cyc (assoc s/empty-world :scopes [(s/->ScopeRow 2 0 s/scope-root true)
                                          (s/->ScopeRow 5 6 s/scope-run true)
                                          (s/->ScopeRow 6 5 s/scope-explicit true)])]
    (is (false? (acyc/scopes-acyclic cyc)) "5 -> 6 -> 5")))
