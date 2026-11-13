(ns spindel.v2.i8-test
  "Loading spindel.v2.i8 kernel-checks literal I8 (closed scopes) through the step (`step-lit-i8-total`,
  bundle p3i = p3h && g8 []). The bundle, literal I8 and the guard's tripwire `cur-open-ok` (an alive
  normal task run's current scope is open: the `cur-closed` refusal never fires, obligation P10) run on
  the random drivers of engine-test and on every commit of the oracle samples 7-13."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.i8 :as i8]
            [spindel.v2.oracle :as o]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[g8-close-local i8k-close g8-cancel-run-local-x g8-retire-with-x g8-job g8-cascade g8-cascade-done
    g8-run-cascade-ga step-g8 g8-empty p3i-empty step-p3i step-lit-i8-total])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

(defn- checks [w tag]
  (is (true? (i8/g8 [] w)) (str "g8 " tag))
  (is (true? (inv/lit-i8-runs w)) (str "lit-i8-runs " tag))
  (is (true? (inv/lit-i8-sources w)) (str "lit-i8-sources " tag))
  (is (true? (i8/cur-open-ok w)) (str "cur-open-ok " tag)))

(defn drive [seed runs steps d0?]
  (let [rng (java.util.Random. seed)]
    (dotimes [run runs]
      (loop [i 0 w (et/prefix-world)]
        (when (< i steps)
          (let [item (loop [k 0]
                       (let [x (et/random-item rng w)]
                         (if (or (not d0?) (it/d0-ok? w x) (> k 50)) x (recur (inc k)))))
                w2 (:world (en/world-step w item))]
            (checks w2 (str "seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (i8/p3i (et/prefix-world))))
  (drive 20261181 15 50 false)
  (drive 20261182 15 50 true))

;; the oracle samples in the table format (7-12, explicit items): every commit's world
(deftest bundle-oracle
  (doseq [n [7 8 9 10 11 12 13]]
    (let [log (o/read-log (str "test/spindel/v2/oracle/log-sample-" n ".edn"))]
      (reduce (fn [w [i c]]
                (let [w2 (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c)))))]
                  (checks w2 (str "sample " n " commit " i))
                  w2))
              s/empty-world (map-indexed vector log)))))
