(ns spindel.v2.hm3-test
  "Loading spindel.v2.hm3 kernel-checks the h-mem2 bundle `h3 xm` (member edges of a current activation exist,
  are armed, structured, first-held, and their debtors are alive tasks or strongly waiting computations, unless
  exempt), its transfer and primitive lemmas, the first fire overrides, and the derivation of h-mem2
  (`h3-h-mem2`: h3 [] and gd's rof give h-mem2; `h3-l5-safety`). Tripwire: `h3 []` after every step of the
  random drivers and every commit of the oracle samples 7-13 (the step proof is open: notes/PLAN.md, branch hm3)."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.hm3 :as h3]
            [spindel.v2.oracle :as o]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[h3-sample h3-intro h3-m-rel h3-s-edge h3-x-rel h3-r-rel h3-a-rel h3-rest-rel h3r-cs h3r-ts h3r-rs h3r-es h3r-nid
    h3r-comp-upd h3-comp-upd-m h3r-edge-upd h3r-ce-upd h3r-mark-edge h3r-unmark-edge h3-r-acts h3r-acts h3r-act-del
    h3r-act-upd h3r-run-upd h3r-task-upd h3r-run-ins h3r-task-ins h3r-comp-ins h3r-run-del h3r-comp-del h3r-es-sub
    h3r-insert-edge-fresh h3r-insert-edge-checked h3r-comp-dec h3r-edge-del h3r-remove-edge h3r-drop-cred h3r-drop-act
    h3r-drop-edges h3-edge-upd-m h3-run-upd-m h3-task-upd-m h3-act-upd-m h3-unmark-edge h3-remove-edge h3-drop-cred
    h3-drop-act h3-drop-edges h3-run-del h3-ob-use h3-free-cred h3r-edge-upd-free h3-free-inc h3-invalidate h3-resume
    h3-fill-slot h3-rest-xm h3-undo-x h3-mem-y h3-h-mem2 h3-l5-safety])

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
            (is (true? (h3/h3 '() w2)) (str "h3 seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

;; AR (not yet a theorem; the T6 override needs it): every alive run of a computation is that computation's C.run
(defn ar? [w]
  (every? (fn [r] (or (= (:act r) s/act-done)
                      (every? (fn [c] (or (not= (:id c) (:of r)) (= (:run c) (:id r)))) (:comps w))))
          (:runs w)))

(defn drive-ar [seed runs steps d0?]
  (let [rng (java.util.Random. seed)]
    (dotimes [run runs]
      (loop [i 0 w (et/prefix-world)]
        (when (< i steps)
          (let [item (loop [k 0]
                       (let [x (et/random-item rng w)]
                         (if (or (not d0?) (it/d0-ok? w x) (> k 50)) x (recur (inc k)))))
                w2 (:world (en/world-step w item))]
            (is (ar? w2) (str "AR seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest ar-random
  (drive-ar 20261141 15 80 false)
  (drive-ar 20261142 15 80 true))

(deftest h3-random
  (drive 20261141 15 80 false)
  (drive 20261142 15 80 true)
  (drive 20261811 12 80 false))

(deftest h3-oracle
  (doseq [n [7 8 9 10 11 12 13]]
    (let [log (o/read-log (str "test/spindel/v2/oracle/log-sample-" n ".edn"))]
      (reduce (fn [w [i c]]
                (let [w2 (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c)))))]
                  (is (true? (h3/h3 '() w2)) (str "h3 sample " n " commit " i))
                  w2))
              s/empty-world (map-indexed vector log)))))
