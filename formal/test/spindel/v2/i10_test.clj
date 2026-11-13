(ns spindel.v2.i10-test
  "Loading spindel.v2.i10 kernel-checks literal I10 (one current run per computation) through the
  step: the bundle g10r (with the transport bundle nq and the exemption parameters of g10) is
  preserved by every step with no honest hypothesis beyond P3's p3b (`step-p3c`). The bundle runs as
  a tripwire on the random drivers of engine-test."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.i10 :as i10]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[g10-cascade g10-run-cascade g10-job-apply g10-cancel-run-local g10-retire-with g10-cancel-pred g10-dispatch-raw
    t11-g10 g10-spawn-rows g10-complete-raw t12-g10 g10-new-run-of g10r-start-raw t5-g10r raw0-g10r raw-g10r
    g10-demote g10-norm-round g10-normalize g10-rule-r step-g10 g10r-empty g10r-lit-i10 step-lit-i10-current
    p3c-empty step-p3c step-lit-i10-current-total])

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
            (is (true? (i10/g10r w2)) (str "g10r seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (inv/lit-i10-current w2)) (str "lit-i10-current seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (i10/g10r (et/prefix-world))))
  (drive 20261121 20 60 false)
  (drive 20261122 20 60 true))
