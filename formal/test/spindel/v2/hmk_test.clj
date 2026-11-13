(ns spindel.v2.hmk-test
  "Loading spindel.v2.hmk kernel-checks the h-mark bundle `hmk hxm` (marked edges are dep edges
  whose debtor is a computation that is waiting in the strong form, or exempt) over every
  primitive and the overridden composite lemmas. Tripwire: `hmk []` after every step of the random
  drivers and every commit of the oracle samples 7-13. Loading spindel.v2.hmk2 checks T2, T12 + settle,
  Rule R's demote and the step (`step-p3l`, `step-h-mark-total`)."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.hmk :as hmk]
            [spindel.v2.hmk2]
            [spindel.v2.oracle :as o]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[hmk-comp-upd-m hkr-mark-edge hkr-unmark-edge hkr-remove-edge hkr-drop-edges hkr-filter-world hkr-comp-del
    hmk-fire-edge hmk-fire-dep hmk-cancel-acts hmk-fold-drop-act hmk-finalize-debtor hmk-close-local hmk-track-raw
    hmk-react-loop hmk-revoke-roots hmk-detach hsw-cancel-pred hmk-cut-suffix hmk-consume-entry hmk-dispatch-raw t11-hmk
    hmk-fold-mark-x hmk-discharge hk-fold-J hk-fold-wif hmk-mfr hmk-create-comp-raw t3-hmk t3-top-hmk hk-h-mark hmk-empty
    t1-full-hmk t1-top-hmk t7-hmk t8-full-hmk t8-unobserve-hmk t9-hmk t15-full-hmk t17-hmk t18-hmk t19-hmk t20-pin-hmk
    t20-unpin-hmk t4-hmk t4-top-hmk t5-hmk t6-hmk sched-hmk t22-hmk t22-un-hmk t-handle-new-hmk t-deliver-hmk t-post-hmk
    t-take-hmk t-release-hmk t-finalize-hmk t-cancel-hmk t-release-world-hmk t-open-scope-hmk t-close-scope-hmk
    t-detach-hmk t-finally-enter-hmk t-finally-exit-hmk t-slice-exit-hmk hmk-cancel-losers
    ;; spindel.v2.hmk2: T2, T12 + settle, demote, the step
    ek-fire-edge ek-settle-edge hk-sv-fold hk-cs-fold hk-root-fire hk-root-fold hk-tg-ek hk-write-wif hmk-write-raw-x t2-hmk
    hmk-dis hk-wt-nready hk-se-fold hk-settle-step hk-settle-loop hmk-settle-x hmk-complete-body-x hmk-complete-raw-x t12-hmk
    hmk-demote-x hmk-demote-fold hk-nmd-pass hmk-norm-round hmk-normalize-x hmk-rule-r raw0-hmk raw-hmk step-hmk
    p3l-empty step-p3l step-h-mark-total p3l-h-mark])

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
            (is (true? (hmk/hmk '() w2)) (str "hmk seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest hmk-random
  (drive 20261811 12 80 false)
  (drive 20261812 12 80 true))

(deftest hmk-oracle
  (doseq [n [7 8 9 10 11 12 13]]
    (let [log (o/read-log (str "test/spindel/v2/oracle/log-sample-" n ".edn"))]
      (reduce (fn [w [i c]]
                (let [w2 (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c)))))]
                  (is (true? (hmk/hmk '() w2)) (str "hmk sample " n " commit " i))
                  w2))
              s/empty-world (map-indexed vector log)))))
