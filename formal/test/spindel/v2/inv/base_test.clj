(ns spindel.v2.inv.base-test
  "Loading spindel.v2.inv.base kernel-checks P3 (Rule R's filter is edge-safe in every round of every
  step) and the step theorems with no honest hypothesis; the combined bundle chain-start and the
  reference invariants run as a tripwire on the random drivers of engine-test."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.rule :as r]
            [spindel.v2.inv.copier :as lit]
            [spindel.v2.inv.base :as p3]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[marks-on-dep-write-raw marks-on-dep-mark-from step-marks-on-dep refs-not-edges-cancel-run-local refs-not-edges-add-run-scope refs-not-edges-spawn-rows refs-not-edges-retire-after
    refs-not-edges-t17-arm refs-not-edges-t-detach refs-not-edges-t-open-scope step-refs-not-edges act-runs-alive-cancel-run-local act-runs-alive-complete-raw act-runs-alive-t12-complete act-runs-alive-retire-run
    act-runs-alive-await-raw act-runs-alive-t6-await act-runs-alive-take-park act-runs-alive-t-take step-act-runs-alive refs-not-edges-edge-sep p3-refs-of round-facts-round
    rounds-safe-loop-round-facts rule-r-safe-round-facts chain-start-empty step-rule-r-safe step-chain-start step-well-formed-total step-acts-total step-rank-total
    step-ranks-total step-p3-refs step-normalized-p3 step-i4-p3 step-lit-i10-task-total step-lit-i9-res-total
    step-lit-i7-total
    ;; I5 (seen <= version)
    i5-seen-filter-world i5-seen-fire-observe i5-seen-dep-consumed i5-seen-consume-entry i5-seen-dispatch-raw i5-seen-track-raw i5-seen-await-step
    step-i5-seen i5-seen-empty step-i5-seen-total i5-seen-i5 step-i5-total])

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
                raw (:world (en/raw w item))
                w2 (:world (en/world-step w item))]
            (is (true? (r/rule-r-safe raw)) (str "rule-r-safe seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (p3/chain-start w2)) (str "chain-start seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (lit/p3-refs w2)) (str "p3-refs seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (p3/i5-seen w2)) (str "i5-seen seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (p3/chain-start (et/prefix-world))))
  (is (true? (p3/i5-seen (et/prefix-world))))
  (drive 20261111 20 60 false)
  (drive 20261112 20 60 true))
