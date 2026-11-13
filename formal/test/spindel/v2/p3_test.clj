(ns spindel.v2.p3-test
  "Loading spindel.v2.p3 kernel-checks P3 (Rule R's filter is edge-safe in every round of every
  step) and the step theorems with no honest hypothesis; the combined bundle p3b and the
  reference invariants run as a tripwire on the random drivers of engine-test."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.rule :as r]
            [spindel.v2.lit :as lit]
            [spindel.v2.p3 :as p3]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[mdb-write-raw mdb-mark-from step-mdb esb-cancel-run-local esb-add-run-scope esb-spawn-rows esb-retire-after
    t17-esb t-detach-esb t-open-scope-esb step-esb aha-cancel-run-local aha-complete-raw t12-aha aha-retire-local
    aha-await-raw t6-aha aha-take-park t-take-aha step-aha esb-edge-sep p3-refs-of ri-round
    rr-safe-ri rule-r-safe-ri p3b-empty step-rule-r-safe step-p3b step-inv-total step-acts-total step-rank-total
    step-ranks-total step-p3-refs step-normalized-p3 step-i4-p3 step-lit-i10-task-total step-lit-i9-res-total
    step-lit-i7-total
    ;; I5 (seen <= version)
    svb-filter-world svb-fire-observe svb-dep-consumed svb-consume-entry svb-dispatch-raw svb-track-raw svb-await-step
    step-svb svb-empty step-svb-total svb-i5 step-i5-total])

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
            (is (true? (p3/p3b w2)) (str "p3b seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (lit/p3-refs w2)) (str "p3-refs seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (p3/svb w2)) (str "svb seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (p3/p3b (et/prefix-world))))
  (is (true? (p3/svb (et/prefix-world))))
  (drive 20261111 20 60 false)
  (drive 20261112 20 60 true))
