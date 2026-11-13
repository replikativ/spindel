(ns spindel.v2.hm-test
  "Loading spindel.v2.hm kernel-checks the auxiliary bundle `gd` of the h-mark plan through
  `world-step` (step-gd, step-p3j: p3j = p3i && gd, no honest hypothesis) and its watch bundle
  `hkw` (T11). Tripwire: `gd` (the bundle as executable Bool) after every step of the random
  drivers and every commit of the oracle samples 7-13."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.hm :as hm]
            [spindel.v2.oracle :as o]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[gd-c-mono gdk-comp-m gdk-run-m gdk-run-ins gd-comp-ins gd-park-if gd-take-park gd-add-run-scope gd-spawn-rows
    gd-start-raw t5-gd hkw-cancel-pred gd-new-run-of gd-dispatch-raw t11-gd gd-complete-body gd-complete-raw t12-gd
    gd-react-one gd-react-loop gd-demand-reactive gd-await-raw t6-gd t22-gd t8-full-gd raw-gd gd-normalize
    gd-rule-r step-gd gd-empty step-p3j p3j-empty gd-facts step-gd-facts-total
    reach-closure-inv reach-run-inv hm-dirty-back hm-cone-back])

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
            (is (true? (hm/gd w2)) (str "gd seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest gd-random
  (drive 20261711 12 80 false)
  (drive 20261712 12 80 true))

(deftest gd-oracle
  (doseq [n [7 8 9 10 11 12 13]]
    (let [log (o/read-log (str "test/spindel/v2/oracle/log-sample-" n ".edn"))]
      (reduce (fn [w [i c]]
                (let [w2 (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c)))))]
                  (is (true? (hm/gd w2)) (str "gd sample " n " commit " i))
                  w2))
              s/empty-world (map-indexed vector log)))))
