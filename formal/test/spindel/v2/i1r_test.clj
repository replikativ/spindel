(ns spindel.v2.i1r-test
  "Loading spindel.v2.i1r kernel-checks literal I1 with every clause through the step
  (`step-lit-i1-total`, bundle p3h = p3g && gr0). The bundle gr0 and inv-i1 run as a tripwire on the
  random drivers of engine-test."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.i1r :as i1r]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[grx-run-upd-x grx-cleanup-set grx-cancel-run-local grx-retire-with grx-remove-if-empty gr0-add-run-scope gr0-arm-raw
    gr0-ack-raw track-cascade gr0-complete-raw raw-gr0 no-run-of gr0-demote-aa gr0-normalize-aa run-kept gr0-filter
    gr0-rule-r step-gr0 gr0-empty i1-runs-of p3h-empty step-p3h step-lit-i1-total])

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
                w2 (:world (en/world-step w item))
                tag (str "seed " seed " run " run " step " i " " (pr-str item))]
            (is (true? (i1r/gr0 w2)) (str "gr0 " tag))
            (is (true? (inv/inv-i1 w2)) (str "inv-i1 " tag))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (i1r/p3h (et/prefix-world))))
  (drive 20261171 15 50 false)
  (drive 20261172 15 50 true))
