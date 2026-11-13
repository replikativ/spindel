(ns spindel.v2.casc-test
  "Loading spindel.v2.casc and spindel.v2.acts kernel-checks P4 (cascade completion,
  `casc-done-ok`), P2 (normalization ends normalized, `normalized-ok`) and the activation
  invariant `ga` that discharges their hypothesis in every step (`step-acts`,
  `step-normalized-ga`, `casc-done-ga`), including every copied composite lemma (`bc-copy!`,
  `copy!`). The runtime tests keep the flags as tripwires: `ga`, `acts-alive`, `casc-done` and
  `normalized` after every step of the engine-test random driver."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.rule :as r]
            [spindel.v2.engine :as en]
            [spindel.v2.casc :as c]
            [spindel.v2.acts :as ac]
            [spindel.v2.engine-test :as et]))

(def theorems
  '[;; P4
    bc-rest-mono bc-of-bnd cancel-acts-bc cancel-alive-lt retire-rows-lt casc-step-pot casc-empties
    casc-fuel-above casc-done-ok
    ;; P2
    round-lt demote-lt cascade-first-lt bn-round-lv norm-loop-ok normalized-ok acts-alive-normalize
    acts-alive-filter rr-pre-ok rule-r-normalized-ok step-normalized-ok step-i4-ok
    ;; the activation invariant
    ga-acts-alive gx-act-ins gx-park gx-restore ga-cancel-acts-o ga-await-raw-o ga-take-park-o
    ga-empty step-acts raw-acts-alive step-normalized-ga step-i4-ga casc-done-ga])

(defn- present? [t] (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))))

(deftest theorems-kernel-checked
  (doseq [t theorems] (is (present? t) (str t)))
  (is (< 30 (count @c/bc-copied)))
  (is (< 100 (count @(:copied ac/GA))))
  (doseq [t (concat @c/bc-copied @(:copied ac/GA) @(:copied ac/GX))] (is (present? t) (str t))))

(deftest invariant-runs
  (is (true? (ac/ga s/empty-world)))
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
              (is (true? (r/normalized (r/normalize (r/rule-r-pre (:world raw))))) (str "normalized " msg)))
            (is (true? (ac/ga w2)) (str "ga " msg))
            (is (true? (r/casc-done w2 (mapv (fn [x] [0 (:id x) false]) (:runs w2)))) (str "casc-done " msg))
            (recur (inc i) w2)))))
    (is (< 100 @n))))
