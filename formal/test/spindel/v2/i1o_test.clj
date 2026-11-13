(ns spindel.v2.i1o-test
  "Loading spindel.v2.i1o kernel-checks literal I1's owner clauses for tasks, computations and
  sources through the step (`step-lit-i1-owners-total`) and the termination of Rule R's loop with
  no orphan (`rule-r-no-orphans`). The bundle gso and the clauses run as a tripwire on the random
  drivers of engine-test; the step's worlds never end Rule R with an orphan."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.rule :as ru]
            [spindel.v2.i1o :as i1o]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[nzb-normalize detach-lt oc-normalize-lt oc-round-lt rr-no-orphans rule-r-no-orphans
    gso-create-source-cur t1-top-gso gso-serve-or raw-gso gso-normalize gso-rule-r step-gso gso-empty
    i1-own-of p3g-empty step-p3g step-lit-i1-owners-total])

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
                w2 (:world (en/world-step w item))
                tag (str "seed " seed " run " run " step " i " " (pr-str item))]
            (is (true? (i1o/gso w2)) (str "gso " tag))
            (is (true? (i1o/i1-own w2)) (str "i1-own " tag))
            (is (true? (ru/no-orphans w2)) (str "no-orphans " tag))
            (recur (inc i) w2)))))))

(deftest bundle-random
  (is (true? (i1o/p3g (et/prefix-world))))
  (drive 20261161 15 50 false)
  (drive 20261162 15 50 true))
