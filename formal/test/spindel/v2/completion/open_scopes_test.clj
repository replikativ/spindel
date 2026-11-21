(ns spindel.v2.completion.open-scopes-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.completion.open-scopes :as os]))

(def theorems
  '[wi-mono rp-within keep-within open-scopes-have-runs-rest-keep open-scopes-have-runs-scope-ins open-scopes-have-runs-open open-scopes-have-runs-set-parent sub-conv sub-within cur-cases
    open-scopes-have-runs-exempt-run-upd open-scopes-have-runs-add-run-scope open-scopes-have-runs-t-open-scope open-scopes-have-runs-t-detach open-scopes-have-runs-remove-if-empty open-scopes-have-runs-retire-run open-scopes-have-runs-filter
    open-scopes-have-runs-raw open-scopes-have-runs-normalize open-scopes-have-runs-rule-r step-open-scopes-have-runs open-scopes-have-runs-empty])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

;; executable: an open explicit scope under a run scope is witnessed by the run; once the run row is gone (an
;; unguarded deletion, not a step) the invariant fails
(deftest gos-executable
  (is (true? (os/open-scopes-have-runs-rest s/empty-world)))
  (let [w (assoc s/empty-world
                 :scopes [(s/->ScopeRow 2 0 s/scope-root true) (s/->ScopeRow 5 2 s/scope-run true) (s/->ScopeRow 6 5 s/scope-explicit true)]
                 :runs [(s/->RunRow 4 3 0 0 5 0 0 false 0 [] [])])]
    (is (true? (os/open-scopes-have-runs-rest w)))
    (is (false? (os/open-scopes-have-runs-rest (assoc w :runs []))) "no run: the open run and explicit scopes have no witness")
    (is (true? (os/open-scopes-have-runs-rest (assoc w :runs [] :scopes (mapv #(assoc % :open false) (:scopes w))))) "closed: no obligation")))
