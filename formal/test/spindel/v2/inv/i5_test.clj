(ns spindel.v2.inv.i5-test
  "Loading spindel.v2.inv.i5 kernel-checks literal I5's dep-final clause through the step
  (`step-lit-i5-dep-final-total`: no armed dep edge has a final debtor after any step from a chain-to-i5-dep-final
  world, chain-to-i5-dep-final = chain-to-i1-scopes && i5-dep-final []). The bundle and the literal clause run as a tripwire on the random
  drivers of engine-test (both, and the D0-respecting one), with the exempt list empty."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.inv.i5 :as i5]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[deb-final-st i5-dep-final-lit i5-dep-final-edge-upd i5-dep-final-source-upd-at i5-dep-final-insert-edge-checked i5-dep-final-filter-world
    jw-fire-edge jw-fold jw-start close-end i5-dep-final-wake-final i5-dep-final-fold-all i5-dep-final-task-fold i5-dep-final-ctask i5-dep-final-deliver-fire
    i5-dep-final-dep-consumed i5-dep-final-fire-edge i5-dep-final-consume-entry i5-dep-final-dispatch-raw i5-dep-final-close-source i5-dep-final-detach-source i5-dep-final-debtor-side
    i5-dep-final-complete-body i5-dep-final-t-deliver i5-dep-final-react-add i5-dep-final-track-raw i5-dep-final-write-raw i5-dep-final-t-post i5-dep-final-t-release i5-dep-final-t-take
    jw6-await-wire jw6-fast fast-not-final i5-dep-final-await-raw i5-dep-final-raw i5-dep-final-normalize i5-dep-final-rule-r step-i5-dep-final i5-dep-final-empty
    chain-to-i5-dep-final-empty step-chain-to-i5-dep-final step-lit-i5-dep-final-total])

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
            (is (true? (i5/i5-dep-final [] w2)) (str "i5-dep-final seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (inv/lit-i5-dep-final w2)) (str "lit-i5-dep-final seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (i5/chain-to-i5-dep-final (et/prefix-world))))
  (drive 20261151 15 50 false)
  (drive 20261152 15 50 true))
