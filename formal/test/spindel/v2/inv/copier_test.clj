(ns spindel.v2.inv.copier-test
  "Loading spindel.v2.inv.copier kernel-checks the literal-invariant theorems; the bundles run as a
  tripwire on the random drivers of engine-test (unrestricted and D0-respecting)."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.inv.acts :as acts]
            [spindel.v2.inv.copier :as lit]
            [spindel.v2.inv.i10-task]
            [spindel.v2.inv.i9-res]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[i10-task-cancel-run-local i10-task-retire-run i10-task-complete-raw i10-task-t12-complete i10-task-spawn-rows i10-task-start-raw i10-task-new-run-of
    i10-task-dispatch-raw i10-task-filter-world-hand i10-task-rule-r i10-task-raw step-i10-task i10-task-empty i10-task-i10-task step-lit-i10-task
    ;; I9 resources
    i9-res-cancel-run-local i9-res-ack-raw i9-res-t17-arm step-i9-res i9-res-empty step-lit-i9-res
    ;; P3 core
    live-close edge-not-admitted dep-cred-live cred-kept filter-keeps-ends-ok filter-keeps-marked-ok filter-safe-of-refs])

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
            (is (true? (acts/acts-parked w2)) (str "acts-parked seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (lit/i10-task w2)) (str "i10-task seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (lit/i9-res w2)) (str "i9-res seed " seed " run " run " step " i " " (pr-str item)))
            ;; P3: the reference invariants of filter-safe-of-refs hold in every step's world (tripwire)
            (is (true? (lit/p3-refs w2)) (str "p3-refs seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest bundles-random
  (is (true? (lit/i10-task (et/prefix-world))))
  (is (true? (lit/i9-res (et/prefix-world))))
  (drive 20261107 20 60 false)
  (drive 20261108 20 60 true))
