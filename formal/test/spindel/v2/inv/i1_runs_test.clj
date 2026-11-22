(ns spindel.v2.inv.i1-runs-test
  "Loading spindel.v2.inv.i1-runs kernel-checks literal I1 with every clause through the step
  (`step-lit-i1-total`, bundle chain-to-i1-runs = chain-to-i1-detached-closed && i1-runs). The bundle i1-runs and inv-i1 run as a tripwire on the
  random drivers of engine-test."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.inv.i1-runs :as i1r]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[i1-runs-exempt-run-upd-x i1-runs-exempt-cleanup-set i1-runs-exempt-cancel-run-local i1-runs-exempt-t13-retire-with-subtree i1-runs-exempt-remove-if-empty i1-runs-add-run-scope i1-runs-arm-raw
    i1-runs-ack-raw track-cascade i1-runs-complete-raw i1-runs-raw no-run-of i1-runs-demote-aa i1-runs-normalize-aa run-kept i1-runs-filter
    i1-runs-rule-r step-i1-runs i1-runs-empty lit-i1-runs-of chain-to-i1-runs-empty step-chain-to-i1-runs step-lit-i1-total])

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
            (is (true? (i1r/i1-runs w2)) (str "i1-runs " tag))
            (is (true? (inv/inv-i1 w2)) (str "inv-i1 " tag))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (i1r/chain-to-i1-runs (et/prefix-world))))
  (drive 20261171 15 50 false)
  (drive 20261172 15 50 true))
