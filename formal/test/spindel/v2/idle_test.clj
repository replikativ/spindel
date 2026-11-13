(ns spindel.v2.idle-test
  "Loading spindel.v2.idle kernel-checks I7 (idle shape) through the step; the bundles g7 and
  inv-i7 run as a tripwire on the random drivers of engine-test (unrestricted and D0-respecting)."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.idle :as idle]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[g7k-comp-upd g7k-run-upd g7-mark-edge-o g7-insert-edge-fresh g7-comp-ins-fresh g7-run-upd-at
    g7-track-raw t7-g7 g7-add-run-scope g7-spawn-rows g7-start-raw g7-react-add g7-react-edges g7-react-one
    g7-cut-suffix g7-new-run-of g7-dispatch-raw t11-g7 g7-park-if g7-await-step g7-await-wire g7-await-post
    g7-await-raw t6-g7 sched-g7 t-finalize-g7 g7-take-park t-take-g7 raw-g7
    ;; cascade completeness for demote
    kd-cancel casc-kill demote-dead g7-demote-finish g7-demote g7-norm-round g7-norm-loop g7-normalize
    g7-rule-r step-g7 g7-empty g7-i7 step-lit-i7])

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
            (is (true? (idle/g7 w2)) (str "g7 seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (inv/inv-i7 w2)) (str "i7 seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (idle/g7 (et/prefix-world))))
  (drive 20261109 20 60 false)
  (drive 20261110 20 60 true))
