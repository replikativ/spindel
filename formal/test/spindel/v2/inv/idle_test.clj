(ns spindel.v2.inv.idle-test
  "Loading spindel.v2.inv.idle kernel-checks I7 (idle shape) through the step; the bundles i7-idle and
  inv-i7 run as a tripwire on the random drivers of engine-test (unrestricted and D0-respecting)."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.inv.idle :as idle]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[i7-idle-keys-ok-comp-upd i7-idle-keys-ok-run-upd i7-idle-mark-edge-hand i7-idle-insert-edge-fresh i7-idle-comp-ins-fresh i7-idle-run-upd-at
    i7-idle-track-raw i7-idle-t7-track i7-idle-add-run-scope i7-idle-spawn-rows i7-idle-start-raw i7-idle-react-add i7-idle-react-edges i7-idle-react-one
    i7-idle-cut-suffix i7-idle-new-run-of i7-idle-dispatch-raw i7-idle-t11-dispatch i7-idle-park-if i7-idle-await-step i7-idle-await-wire i7-idle-await-post
    i7-idle-await-raw i7-idle-t6-await i7-idle-t-schedule i7-idle-t-finalize i7-idle-take-park i7-idle-t-take i7-idle-raw
    ;; cascade completeness for demote
    kd-cancel cascade-kill demote-dead i7-idle-demote-finish i7-idle-demote i7-idle-normalize-round i7-idle-normalize-loop i7-idle-normalize
    i7-idle-rule-r step-i7-idle i7-idle-empty i7-idle-i7 step-lit-i7])

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
            (is (true? (idle/i7-idle w2)) (str "i7-idle seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (inv/inv-i7 w2)) (str "i7 seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (idle/i7-idle (et/prefix-world))))
  (drive 20261109 20 60 false)
  (drive 20261110 20 60 true))
