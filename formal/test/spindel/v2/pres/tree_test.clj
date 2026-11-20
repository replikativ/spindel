(ns spindel.v2.pres.tree-test
  "The generic tree (spindel.v2.pres.tree): every lemma of the step's closure that calls others has
  its generic lemma (and a bare one, for a node with an own context), every context default exists,
  the parts converted to the tree (gl, g9) have no copier overrides or patches left, and an own
  context reaches only the parts that need it."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.inv.copier :as c]
            [spindel.v2.inv.i10-task]
            [spindel.v2.inv.i9-res]
            [spindel.v2.pres.tree :as tree]))

(defn- declared? [s] (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str s)))))

(deftest every-node-has-its-generic-lemma
  (is (< 150 (count (:nodes @tree/tree))))
  (doseq [x (:nodes @tree/tree)]
    (is (declared? (tree/pres-name x)) (str x))
    (when (get-in tree/contexts [x :own])
      (is (declared? (symbol (str (tree/pres-name x) "-bare"))) (str x)))))

(deftest contexts-have-defaults
  (doseq [x (keys tree/contexts)]
    (is (declared? (symbol (str "ctx-" (subs (name (tree/pres-name x)) 5)))) (str x))))

(deftest own-contexts-are-opt-in
  ;; gl needs T12's guard (its complete-raw takes the result's tag), g9 needs T17's (its arm-park
  ;; takes the arming run); neither takes the other's
  (is (tree/takes? c/GL 't12-inv))
  (is (not (tree/takes? c/GL 't17-inv)))
  (is (tree/takes? c/G9 't17-inv))
  (is (not (tree/takes? c/G9 't12-inv)))
  (is (not (tree/takes? c/G9 'inv-dispatch-raw))))

(deftest gl-is-not-copied
  (is (empty? @(:overrides c/GL)))
  (is (empty? @(:patches c/GL)))
  (is (= '{inv-cancel-run-local gl-cancel-run-local-o, inv-complete-raw gl-complete-raw-o,
           inv-retire-local gl-retire-local-o, inv-spawn-rows gl-spawn-rows-o,
           inv-start-raw gl-start-raw, inv-new-run-of gl-new-run-of}
         (get-in @tree/parts ['gl :over]))))

(deftest g9-is-not-copied
  (is (empty? @(:overrides c/G9)))
  (is (empty? @(:patches c/G9)))
  (is (= '{inv-cancel-run-local g9-cancel-run-local, inv-ack-raw g9-ack-raw-o, inv-arm-park g9-arm-park}
         (get-in @tree/parts ['g9 :over]))))
