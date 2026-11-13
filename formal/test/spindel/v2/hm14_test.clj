(ns spindel.v2.hm14-test
  "Loading spindel.v2.hm14 kernel-checks T11 dispatch through `raw` for the h-mem2 bundle h3. The
  statements are the reviewed contracts of notes/hm14-contracts.edn; the three edge-predicate
  helpers planned there are replaced by the copied bundle `kc` (kind and creditor of an edge id)."
  (:require [clojure.test :refer [deftest is]]
            [clojure.edn :as edn]
            [spindel.v2.hm14]))

(def manifest (edn/read-string (slurp "notes/hm14-contracts.edn")))
(def contracts
  (into {} (map (juxt :name :type))
        (filter #(.startsWith (str (:name %)) "h14-") (concat (:helper-contracts manifest) (:public-contracts manifest)))))
(def replaced '#{h14-edge-predicate-job-apply h14-edge-predicate-cascade h14-cancel-pred-entry-keys})
(def forms
  (let [rdr (java.io.PushbackReader. (java.io.StringReader. (slurp "src/spindel/v2/hm14.clj"))) eof (Object.)]
    (vec (take-while #(not (identical? % eof)) (repeatedly #(read {:eof eof} rdr))))))
(def statements
  (into {} (for [[op nm binders type] forms :when (= op 'a/theorem)] [nm (list 'forall binders type)])))

(deftest statements-are-the-contracts
  (is (= 19 (count contracts)))
  (doseq [[nm type] contracts :when (not (replaced nm))]
    (is (= type (statements nm)) (str nm)))
  (is (not-any? statements replaced)))

(deftest no-sorry
  (is (not (re-find #"sorry" (slurp "src/spindel/v2/hm14.clj")))))
