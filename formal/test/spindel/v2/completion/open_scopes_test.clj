(ns spindel.v2.completion.open-scopes-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.completion.open-scopes :as os]))

(def theorems
  '[wi-mono rp-within keep-within gos-rest-keep gos-scope-ins gos-open gos-set-parent sub-conv sub-within cur-cases
    gox-run-upd gos-add-run-scope t-open-scope-gos t-detach-gos gos-remove-if-empty gos-retire-local gos-filter
    raw-gos gos-normalize gos-rule-r step-gos gos-empty])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

;; executable: an open explicit scope under a run scope is witnessed by the run; once the run row is gone (an
;; unguarded deletion, not a step) the invariant fails
(deftest gos-executable
  (is (true? (os/gos-rest s/empty-world)))
  (let [w (assoc s/empty-world
                 :scopes [(s/->ScopeRow 2 0 s/scope-root true) (s/->ScopeRow 5 2 s/scope-run true) (s/->ScopeRow 6 5 s/scope-explicit true)]
                 :runs [(s/->RunRow 4 3 0 0 5 0 0 false 0 [] [])])]
    (is (true? (os/gos-rest w)))
    (is (false? (os/gos-rest (assoc w :runs []))) "no run: the open run and explicit scopes have no witness")
    (is (true? (os/gos-rest (assoc w :runs [] :scopes (mapv #(assoc % :open false) (:scopes w))))) "closed: no obligation")))
