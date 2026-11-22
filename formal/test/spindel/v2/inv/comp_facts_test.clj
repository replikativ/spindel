(ns spindel.v2.inv.comp-facts-test
  "Loading spindel.v2.inv.comp-facts kernel-checks the auxiliary bundle `comp-facts` of the h-mark plan through
  `world-step` (step-comp-facts, step-chain-to-comp-facts: chain-to-comp-facts = chain-to-i8-closed && comp-facts, no honest hypothesis) and its watch bundle
  `dispatch-epoch-kept` (T11). Tripwire: `comp-facts` (the bundle as executable Bool) after every step of the random
  drivers and every commit of the oracle samples 7-13."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.inv.comp-facts :as hm]
            [spindel.v2.oracle :as o]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[comp-facts-c-mono gdk-comp-m gdk-run-m gdk-run-ins comp-facts-comp-ins comp-facts-park-if comp-facts-take-park comp-facts-add-run-scope comp-facts-spawn-rows
    comp-facts-start-raw comp-facts-t5-start dispatch-epoch-kept-cancel-pred comp-facts-new-run-of comp-facts-dispatch-raw comp-facts-t11-dispatch comp-facts-complete-body comp-facts-complete-raw comp-facts-t12-complete
    comp-facts-react-one comp-facts-react-loop comp-facts-demand-reactive comp-facts-await-raw comp-facts-t6-await comp-facts-t22-host-await comp-facts-t8-observe-any-kind comp-facts-raw comp-facts-normalize
    comp-facts-rule-r step-comp-facts comp-facts-empty step-chain-to-comp-facts chain-to-comp-facts-empty comp-facts-facts step-comp-facts-facts-total
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
            (is (true? (hm/comp-facts w2)) (str "comp-facts seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest gd-random
  (drive 20261711 12 80 false)
  (drive 20261712 12 80 true))

(deftest gd-oracle
  (doseq [n [7 8 9 10 11 12 13]]
    (let [log (o/read-log (str "test/spindel/v2/oracle/log-sample-" n ".edn"))]
      (reduce (fn [w [i c]]
                (let [w2 (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c)))))]
                  (is (true? (hm/comp-facts w2)) (str "comp-facts sample " n " commit " i))
                  w2))
              s/empty-world (map-indexed vector log)))))
