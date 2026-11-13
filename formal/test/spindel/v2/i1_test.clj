(ns spindel.v2.i1-test
  "Loading spindel.v2.i1 kernel-checks literal I1's scope clause through the step
  (`step-lit-i1-scope-total`, bundle p3e = p3d && g1, g1 = inv-sample && lit-i1-scope); g1 and the
  full literal I1 (lit-i1-scope and inv-i1's owner/entity clauses) run as a tripwire on the random
  drivers of engine-test, with the Z#52 guards (subtree-empty's parent-outside, open-ok) never
  refusing in practice."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.i1 :as i1]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[anc-close-closed cleanup-closed scope-up-of-mem scope-not-admitted live-parent filter-lit-i1-scope
    g1-scope-ins-fresh g1-remove-if-empty g1-add-run-scope g1-spawn-rows t-open-scope-g1 t-detach-g1
    raw-g1 g1-normalize g1-rule-r-round step-g1 g1-empty p3e-empty step-p3e step-lit-i1-scope-total])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

(defn drive [seed runs steps d0?]
  (let [rng (java.util.Random. seed)]
    (dotimes [run runs]
      (loop [i 0 w (et/prefix-world)]
        (when (< i steps)
          (let [item (loop [k 0]
                       (let [x (et/random-item rng w)]
                         (if (or (not d0?) (it/d0-ok? w x) (> k 50)) x (recur (inc k)))))
                w2 (:world (en/world-step w item))]
            (is (true? (i1/g1 w2)) (str "g1 seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (inv/inv-i1 w2)) (str "inv-i1 seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (i1/p3e (et/prefix-world))))
  (drive 20261141 15 50 false)
  (drive 20261142 15 50 true))
