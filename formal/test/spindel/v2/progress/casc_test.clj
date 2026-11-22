(ns spindel.v2.progress.casc-test
  "Loading spindel.v2.progress.casc and spindel.v2.inv.acts kernel-checks P4 (cascade completion,
  `cascade-done-ok`), P2 (normalization ends normalized, `normalized-ok`) and the activation
  invariant `acts-parked` that discharges their hypothesis in every step (`step-acts`,
  `step-normalized-acts-parked`, `cascade-done-acts-parked`), including every composite lemma restated from the step tree
  (`restate!`). The runtime tests keep the flags as tripwires: `acts-parked`, `acts-alive`, `cascade-done` and
  `normalized` after every step of the engine-test random driver."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.rule :as r]
            [spindel.v2.engine :as en]
            [spindel.v2.progress.casc :as c]
            [spindel.v2.inv.acts :as ac]
            [spindel.v2.engine-test :as et]))

(def theorems
  '[;; P4
    cascade-bound-rest-mono cascade-bound-of-bnd cancel-acts-cascade-bound cancel-alive-lt retire-rows-lt cascade-step-pot cascade-empties
    cascade-fuel-above cascade-done-ok
    ;; P2
    round-lt demote-lt cascade-first-lt round-bound-round-lv normalize-loop-ok normalized-ok acts-alive-normalize
    acts-alive-filter last-input-loop-ok rule-r-normalized-ok step-normalized-ok step-i4-ok
    ;; the activation invariant
    acts-parked-acts-alive acts-parked-exempt-act-ins acts-parked-exempt-park acts-parked-exempt-restore acts-parked-cancel-acts-hand acts-parked-await-raw-hand acts-parked-take-park-hand
    acts-parked-empty step-acts raw-acts-alive step-normalized-acts-parked step-i4-acts-parked cascade-done-acts-parked])

(defn- present? [t] (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))))

(deftest theorems-kernel-checked
  (doseq [t theorems] (is (present? t) (str t)))
  (is (< 30 (count @(:copied c/BC))))
  (is (< 100 (count @(:copied ac/GA))))
  (doseq [t (concat @(:copied c/BC) @(:copied ac/GA) @(:copied ac/GX))] (is (present? t) (str t))))

(deftest invariant-runs
  (is (true? (ac/acts-parked s/empty-world)))
  (is (true? (c/acts-alive s/empty-world))))

;; the tripwires along the random driver of engine-test
(deftest random-steps-tripwire
  (let [rng (java.util.Random. 20261104)
        n (atom 0)]
    (dotimes [run 20]
      (loop [i 0 w (et/prefix-world)]
        (when (< i 40)
          (let [item (et/random-item rng w)
                raw (en/raw w item)
                w2 (:world (en/world-step w item))
                msg (str "run " run " step " i " " (pr-str item))]
            (when (:accepted raw)
              (swap! n inc)
              (is (true? (c/acts-alive (:world raw))) (str "acts-alive raw " msg))
              (is (true? (r/normalized (r/normalize (r/rule-r-last-input (:world raw))))) (str "normalized " msg)))
            (is (true? (ac/acts-parked w2)) (str "acts-parked " msg))
            (is (true? (r/cascade-done w2 (mapv (fn [x] [0 (:id x) false]) (:runs w2)))) (str "cascade-done " msg))
            (recur (inc i) w2)))))
    (is (< 100 @n))))
