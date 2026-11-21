(ns spindel.v2.inv.marks-test
  "Loading spindel.v2.inv.marks kernel-checks the h-mark bundle `marks-waiting hxm` (marked edges are dep edges
  whose debtor is a computation that is waiting in the strong form, or exempt) over every
  primitive and the overridden composite lemmas. Tripwire: `marks-waiting []` after every step of the random
  drivers and every commit of the oracle samples 7-13. Loading spindel.v2.inv.marks-step checks T2, T12 + settle,
  Rule R's demote and the step (`step-chain-to-marks-waiting`, `step-h-mark-total`)."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.inv.marks :as hmk]
            [spindel.v2.inv.marks-step]
            [spindel.v2.oracle :as o]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[marks-waiting-comp-upd-m hkr-mark-edge hkr-unmark-edge hkr-remove-edge hkr-drop-edges hkr-filter-world hkr-comp-del
    marks-waiting-fire-edge marks-waiting-fire-dep marks-waiting-cancel-acts marks-waiting-fold-drop-act marks-waiting-t10-finalize-debtor marks-waiting-close-local marks-waiting-track-raw
    marks-waiting-react-loop marks-waiting-revoke-roots marks-waiting-detach done-epoch-below-cancel-pred marks-waiting-cut-suffix marks-waiting-consume-entry marks-waiting-dispatch-raw marks-waiting-t11-dispatch
    marks-waiting-fold-mark-x marks-waiting-discharge hk-fold-J hk-fold-wif marks-waiting-mfr marks-waiting-create-comp-raw marks-waiting-t3-create marks-waiting-t3-create-top hk-h-mark marks-waiting-empty
    marks-waiting-t1-create-nonstream marks-waiting-t1-create-nonstream-top marks-waiting-t7-track marks-waiting-t8-observe-any-kind marks-waiting-t8-unobserve marks-waiting-t9-fire marks-waiting-t15-resource-ack marks-waiting-t17-arm marks-waiting-t18-resource-fire marks-waiting-t19 marks-waiting-t20-pin
    marks-waiting-t20-unpin marks-waiting-t4-spawn marks-waiting-t4-spawn-top marks-waiting-t5-start marks-waiting-t6-await marks-waiting-t-schedule marks-waiting-t22-host-await marks-waiting-t22-host-unawait marks-waiting-t-handle-new marks-waiting-t-deliver marks-waiting-t-post
    marks-waiting-t-take marks-waiting-t-release marks-waiting-t-finalize marks-waiting-t14-host-cancel marks-waiting-t21-release-world marks-waiting-t-open-scope marks-waiting-t-close-scope
    marks-waiting-t-detach marks-waiting-t-finally-enter marks-waiting-t-finally-exit marks-waiting-t-slice-exit marks-waiting-cancel-losers
    ;; spindel.v2.inv.marks-step: T2, T12 + settle, demote, the step
    ek-fire-edge ek-settle-edge hk-sv-fold hk-cs-fold hk-root-fire hk-root-fold hk-tg-ek hk-write-wif marks-waiting-write-raw-x marks-waiting-t2-write
    marks-waiting-dis waiting-strongly-nready hk-se-fold hk-settle-step hk-settle-loop marks-waiting-settle-x marks-waiting-complete-body-x marks-waiting-complete-raw-x marks-waiting-t12-complete
    marks-waiting-demote-x marks-waiting-demote-fold hk-nmd-pass marks-waiting-normalize-round marks-waiting-normalize-x marks-waiting-rule-r marks-waiting-transition marks-waiting-raw step-marks-waiting
    chain-to-marks-waiting-empty step-chain-to-marks-waiting step-h-mark-total chain-to-marks-waiting-h-mark])

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
            (is (true? (hmk/marks-waiting '() w2)) (str "marks-waiting seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest hmk-random
  (drive 20261811 12 80 false)
  (drive 20261812 12 80 true))

(deftest hmk-oracle
  (doseq [n [7 8 9 10 11 12 13]]
    (let [log (o/read-log (str "test/spindel/v2/oracle/log-sample-" n ".edn"))]
      (reduce (fn [w [i c]]
                (let [w2 (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c)))))]
                  (is (true? (hmk/marks-waiting '() w2)) (str "marks-waiting sample " n " commit " i))
                  w2))
              s/empty-world (map-indexed vector log)))))
