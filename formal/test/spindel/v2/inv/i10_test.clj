(ns spindel.v2.inv.i10-test
  "Loading spindel.v2.inv.i10 kernel-checks literal I10 (one current run per computation) through the
  step: the bundle i10-current (with the transport bundle i10-current-transport and the exemption parameters of i10-current-exempt) is
  preserved by every step with no honest hypothesis beyond P3's chain-start (`step-chain-to-i10-current`). The bundle runs as
  a tripwire on the random drivers of engine-test."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.inv.i10 :as i10]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[i10-current-exempt-cascade i10-current-exempt-run-cascade i10-current-exempt-job-apply i10-current-exempt-cancel-run-local i10-current-exempt-t13-retire-with-subtree i10-current-exempt-cancel-pred i10-current-exempt-dispatch-raw
    i10-current-exempt-t11-dispatch i10-current-exempt-spawn-rows i10-current-exempt-complete-raw i10-current-exempt-t12-complete i10-current-exempt-new-run-of i10-current-start-raw i10-current-t5-start i10-current-transition i10-current-raw
    i10-current-exempt-demote i10-current-exempt-normalize-round i10-current-exempt-normalize i10-current-exempt-rule-r step-i10-current i10-current-empty i10-current-lit-i10 step-lit-i10-current
    chain-to-i10-current-empty step-chain-to-i10-current step-lit-i10-current-total])

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
            (is (true? (i10/i10-current w2)) (str "i10-current seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (inv/lit-i10-current w2)) (str "lit-i10-current seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (i10/i10-current (et/prefix-world))))
  (drive 20261121 20 60 false)
  (drive 20261122 20 60 true))
