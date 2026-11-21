(ns spindel.v2.inv.acyclic-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.inv.acyclic :as acyc]))

(def theorems
  '[cy-acyc-sub cy-acyc-fresh cy-acyc-reparent cy-acyc-of cy-acyc-intro scope-parents-acyclic-scope-ins-fresh scope-parents-acyclic-set-parent
    scope-parents-acyclic-add-run-scope scope-parents-acyclic-t-detach scope-parents-acyclic-t-open-scope scope-parents-acyclic-spawn-rows scope-parents-acyclic-raw scope-parents-acyclic-normalize scope-parents-acyclic-rule-r step-scope-parents-acyclic scope-parents-acyclic-empty
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
