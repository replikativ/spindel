(ns spindel.v2.pres.tree-test
  "The generic tree (spindel.v2.pres.tree): every lemma of the step's closure that calls others has
  its generic lemma, every context default exists, and a part converted to the tree (gl) has no
  copier overrides or patches left."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.inv.copier :as c]
            [spindel.v2.inv.i10-task]
            [spindel.v2.pres.tree :as tree]))

(defn- declared? [s] (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str s)))))

(deftest every-node-has-its-generic-lemma
  (is (< 150 (count (:nodes @tree/tree))))
  (doseq [x (:nodes @tree/tree)] (is (declared? (tree/pres-name x)) (str x))))

(deftest contexts-have-defaults
  (doseq [[x {:keys [own?]}] tree/contexts :when (not own?)]
    (is (declared? (symbol (str "ctx-" (subs (name (tree/pres-name x)) 5)))) (str x))))

(deftest gl-is-not-copied
  (is (empty? @(:overrides c/GL)))
  (is (empty? @(:patches c/GL)))
  (is (= '{inv-cancel-run-local gl-cancel-run-local-o, inv-complete-raw gl-complete-raw-o,
           inv-retire-local gl-retire-local-o, inv-spawn-rows gl-spawn-rows-o,
           inv-start-raw gl-start-raw, inv-new-run-of gl-new-run-of}
         (get-in @tree/parts ['gl :over]))))
