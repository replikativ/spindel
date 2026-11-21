(ns spindel.v2.inv.i11-test
  "Loading spindel.v2.inv.i11 kernel-checks I11a through the step (`step-i11a-total`, bundle chain-to-i11a =
  chain-to-i10-current && root-scope-reserved && inv-i11a); root-scope-reserved and inv-i11a run as a tripwire on the random drivers of engine-test."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.inv.i11 :as i11]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[step-root-scope-reserved root-scope-reserved-empty root-scope-reserved-raw root-scope-reserved-t-detach root-scope-reserved-add-run-scope obl-converged reach-roots-obl root-succ i11a-of
    chain-to-i11a-empty step-chain-to-i11a step-i11a-total])

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
            (is (true? (i11/root-scope-reserved w2)) (str "root-scope-reserved seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (inv/inv-i11a w2)) (str "inv-i11a seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (i11/root-scope-reserved (et/prefix-world))))
  (drive 20261131 15 50 false)
  (drive 20261132 15 50 true))
