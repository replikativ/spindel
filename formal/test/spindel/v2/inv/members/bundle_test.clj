(ns spindel.v2.inv.members.bundle-test
  "Loading spindel.v2.inv.members.bundle kernel-checks the h-mem2 bundle `current-members xm` (member edges of a current activation exist,
  are armed, structured, first-held, and their debtors are alive tasks or strongly waiting computations, unless
  exempt), its transfer and primitive lemmas, the first fire overrides, and the derivation of h-mem2
  (`current-members-h-mem2`: current-members [] and gd's rof give h-mem2; `current-members-l5-safety`). Tripwire: `current-members []` after every step of the
  random drivers and every commit of the oracle samples 7-13 (the step proof is open: notes/history/PLAN.md, branch hm3)."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.inv.members.bundle :as h3]
            [spindel.v2.oracle :as o]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[current-members-well-formed current-members-intro current-members-m-rel current-members-s-edge current-members-x-rel current-members-r-rel current-members-a-rel current-members-rest-rel current-members-rest-cs current-members-rest-ts current-members-rest-rs current-members-rest-es current-members-rest-nid
    current-members-rest-comp-upd current-members-comp-upd-m current-members-rest-edge-upd current-members-rest-ce-upd current-members-rest-mark-edge current-members-rest-unmark-edge current-members-r-acts current-members-rest-acts current-members-rest-act-del
    current-members-rest-act-upd current-members-rest-run-upd current-members-rest-task-upd current-members-rest-run-ins current-members-rest-task-ins current-members-rest-comp-ins current-members-rest-run-del current-members-rest-comp-del current-members-rest-es-sub
    current-members-rest-insert-edge-fresh current-members-rest-insert-edge-checked current-members-rest-comp-dec current-members-rest-edge-del current-members-rest-remove-edge current-members-rest-drop-cred current-members-rest-drop-act
    current-members-rest-drop-edges current-members-edge-upd-m current-members-run-upd-m current-members-task-upd-m current-members-act-upd-m current-members-unmark-edge current-members-remove-edge current-members-drop-cred
    current-members-drop-act current-members-drop-edges current-members-run-del current-members-ob-use current-members-free-cred current-members-rest-edge-upd-free current-members-free-inc current-members-invalidate current-members-resume
    current-members-fill-slot current-members-rest-xm current-members-undo-x current-members-mem-y current-members-h-mem2 current-members-l5-safety])

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
            (is (true? (h3/current-members '() w2)) (str "current-members seed " seed " run " run " step " i " " (pr-str item)))
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
                  (is (true? (h3/current-members '() w2)) (str "current-members sample " n " commit " i))
                  w2))
              s/empty-world (map-indexed vector log)))))
