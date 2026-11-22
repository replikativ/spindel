(ns spindel.v2.inv.members.dispatch-test
  "Loading spindel.v2.inv.members.dispatch kernel-checks T11 dispatch through `raw` for the h-mem2 bundle current-members. The
  statements are the reviewed contracts of notes/hm14-contracts.edn; the three edge-predicate
  helpers planned there are replaced by the copied bundle `edge-kind-kept` (kind and creditor of an edge id)."
  (:require [clojure.test :refer [deftest is]]
            [clojure.edn :as edn]
            [spindel.v2.inv.members.dispatch]))

(def manifest (edn/read-string (slurp "notes/hm14-contracts.edn")))
(def contracts
  (into {} (map (juxt :name :type))
        (filter #(#{"current-members-acts-alive-no-holder"
            "current-members-add-run-scope-hand"
            "current-members-cancel-pred"
            "current-members-cancel-pred-no-holder"
            "current-members-consume-entry"
            "current-members-cut-suffix"
            "current-members-dispatch-raw"
            "current-members-entry-after-cut-keys"
            "current-members-entry-edge-facts"
            "current-members-entry-free-after-cut"
            "current-members-free-dep-no-holder"
            "current-members-host-guarded-transition-dispatch-outcome"
            "current-members-new-run-of"
            "current-members-raw-dispatch-accepted"
            "current-members-raw-dispatch-outcome"
            "current-members-t11-dispatch-outcome"
            "h14-cancel-pred-entry-keys"
            "h14-edge-predicate-cascade"
            "h14-edge-predicate-job-apply"} (str (:name %))) (concat (:helper-contracts manifest) (:public-contracts manifest)))))
(def replaced '#{h14-edge-predicate-job-apply h14-edge-predicate-cascade h14-cancel-pred-entry-keys})
(def forms
  (let [rdr (java.io.PushbackReader. (java.io.StringReader. (slurp "src/spindel/v2/inv/members/dispatch.clj"))) eof (Object.)]
    (vec (take-while #(not (identical? % eof)) (repeatedly #(read {:eof eof} rdr))))))
(def statements
  (into {} (for [[op nm binders type] forms :when (= op 'a/theorem)] [nm (list 'forall binders type)])))

(deftest statements-are-the-contracts
  (is (= 19 (count contracts)))
  (doseq [[nm type] contracts :when (not (replaced nm))]
    (is (= type (statements nm)) (str nm)))
  (is (not-any? statements replaced)))

(deftest no-sorry
  (is (not (re-find #"sorry" (slurp "src/spindel/v2/inv/members/dispatch.clj")))))
