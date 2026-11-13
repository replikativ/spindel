(ns spindel.v2.i5-test
  "Loading spindel.v2.i5 kernel-checks literal I5's dep-final clause through the step
  (`step-lit-i5-dep-final-total`: no armed dep edge has a final debtor after any step from a p3f
  world, p3f = p3e && g5 []). The bundle and the literal clause run as a tripwire on the random
  drivers of engine-test (both, and the D0-respecting one), with the exempt list empty."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.i5 :as i5]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[deb-final-st g5-lit g5-edge-upd g5-source-upd-at g5-insert-edge-checked g5-filter-world
    jw-fire-edge jw-fold jw-start close-end g5-wake-final g5-fold-all g5-task-fold g5-ctask g5-deliver-fire
    g5-dep-consumed g5-fire-edge g5-consume-entry g5-dispatch-raw g5-close-source g5-detach-source g5-debtor-side
    g5-complete-body t-deliver-g5 g5-react-add g5-track-raw g5-write-raw t-post-g5 t-release-g5 t-take-g5
    jw6-await-wire jw6-fast fast-not-final g5-await-raw raw-g5 g5-normalize g5-rule-r step-g5 g5-empty
    p3f-empty step-p3f step-lit-i5-dep-final-total])

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
            (is (true? (i5/g5 [] w2)) (str "g5 seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (inv/lit-i5-dep-final w2)) (str "lit-i5-dep-final seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (i5/p3f (et/prefix-world))))
  (drive 20261151 15 50 false)
  (drive 20261152 15 50 true))
