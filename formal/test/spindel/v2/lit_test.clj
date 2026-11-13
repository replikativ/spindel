(ns spindel.v2.lit-test
  "Loading spindel.v2.lit kernel-checks the literal-invariant theorems; the bundles run as a
  tripwire on the random drivers of engine-test (unrestricted and D0-respecting)."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.acts :as acts]
            [spindel.v2.lit :as lit]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[gl-cancel-run-local gl-retire-local gl-complete-raw t12-gl gl-spawn-rows gl-start-raw gl-new-run-of
    gl-dispatch-raw gl-filter-world-o gl-rule-r raw-gl step-gl gl-empty gl-i10-task step-lit-i10-task
    ;; I9 resources
    g9-cancel-run-local g9-ack-raw t17-g9 step-g9 g9-empty step-lit-i9-res
    ;; P3 core
    live-close edge-not-admitted dep-cred-live cred-kept fs-ref-ok fs-mark-ok filter-safe-of-refs])

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
            (is (true? (acts/ga w2)) (str "ga seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (lit/gl w2)) (str "gl seed " seed " run " run " step " i " " (pr-str item)))
            (is (true? (lit/g9 w2)) (str "g9 seed " seed " run " run " step " i " " (pr-str item)))
            ;; P3: the reference invariants of filter-safe-of-refs hold in every step's world (tripwire)
            (is (true? (lit/p3-refs w2)) (str "p3-refs seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest bundles-random
  (is (true? (lit/gl (et/prefix-world))))
  (is (true? (lit/g9 (et/prefix-world))))
  (drive 20261107 20 60 false)
  (drive 20261108 20 60 true))
