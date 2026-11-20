(ns spindel.v2.pres.tree-test
  "The generic tree (spindel.v2.pres.tree): every lemma of the step's closure that calls others has
  its shared generic lemma; a part gets its own (pres-x@part) only on its context paths; a gate gives
  a part's continuations its fact; the parts converted to the tree (gl, g9, g8) have no copier overrides
  or patches left."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.inv.copier :as c]
            [spindel.v2.inv.i10-task]
            [spindel.v2.inv.i9-res]
            [spindel.v2.inv.i8 :as i8]
            [spindel.v2.pres.tree :as tree]))

(defn- declared? [s] (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str s)))))

(deftest every-node-has-its-generic-lemma
  (is (< 150 (count (:nodes @tree/tree))))
  (doseq [x (:nodes @tree/tree)] (is (declared? (tree/pres-name x)) (str x))))

(deftest part-lemmas-only-on-context-paths
  ;; gl takes T12's guard and passes it to complete-raw; g9 takes T17's and passes it to arm-park
  (is (tree/variant? c/GL 't12-inv))
  (is (declared? (tree/pres-name c/GL 't12-inv)))   ; pres-t12@gl
  (is (not (tree/variant? c/GL 't17-inv)))
  (is (tree/variant? c/G9 't17-inv))
  (is (not (tree/variant? c/G9 't12-inv)))
  (is (not (tree/variant? c/G9 'inv-dispatch-raw)))
  (is (= 10 (count (filter #(and (tree/variant? (if (= 'gl (first %)) c/GL c/G9) (second %)))
                           (for [p '[gl g9] x (:nodes @tree/tree)] [p x]))))))

(deftest a-gate-gives-the-continuation-its-fact
  ;; a part taking C0's gate: raw0's continuations receive root-ok-if (checked for any Q)
  (let [B (c/mk-bundle 'tgate [] "tgate-" {})]
    (tree/part! B :gates '{c0-gate-inv hc0})
    (is (tree/variant? B 'raw0-inv))
    (doseq [x '[c0-gate-inv raw0-inv]]
      (when-not (declared? (tree/pres-name B x)) (@#'tree/ev (tree/pres-form B x)))
      (is (declared? (tree/pres-name B x)) (str x)))
    (swap! tree/parts dissoc 'tgate)))

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

(deftest g8-is-not-copied
  (is (empty? @(:overrides i8/G8)))
  (is (empty? @(:patches i8/G8)))
  ;; the companion ga reaches the cascades from raw (raw -> raw0g -> raw0 -> the transitions)
  (doseq [x '[raw-inv raw0g-inv raw0-inv t15-full-inv inv-complete-raw inv-cancel-pred]]
    (is (tree/variant? i8/G8 x) (str x)))
  (is (not (tree/variant? i8/G8 'inv-job-apply)))
  ;; raw0, raw0g, T14, ... only forward ga: inferred, not declared
  (is (not (contains? (:own (get @tree/parts 'g8)) 'raw0-inv)))
  (is (= '[(= (ga w) true)] (vec (take-nth 2 (rest (get (tree/table-own i8/G8) 'raw0-inv)))))))
