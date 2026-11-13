(ns spindel.v2.l5-test
  "Loading spindel.v2.l5 kernel-checks the discharge of L5's state facts (h-cur from g10r, ...).
  Here: the settle worklist's fuel regression (found by branch l5), the former h-mark
  counterexample (resolved by Z#59), and the state facts (h-cur, h-mark at every step; h-mem at
  quiescent points is in progress_test) plus I5's dep-final clause as the model has it
  (`i5-dep-final-mem`) as a tripwire on the random drivers and the oracle samples 7-13."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.progress :as pr]
            [spindel.v2.l5 :as l5]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]
            [spindel.v2.oracle :as o]))

(def theorems '[l5-cur-ok l5-h-cur l5-safety-p3c l5-step-p3c task-base-q mem-y-q h-mem-of2 l5-safety-inv es-nm-upd nm-settle-edge sd-settle-edge sd-pop settle-loop-done settle-done-ok])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

;; ---------------------------------------------------------------------------
;; Settle fuel (model bug, fixed in engine.clj `settle-fuel`). Computation 19 awaits computation
;; 14 at eight sites (eight dep edges on 14), 39 awaits 19, 45 awaits 39. A write to signal 3
;; invalidates 14 and marks the eight edges 19 -> 14, 39 -> 19 and 45 -> 39. 14 re-runs and
;; completes with the same result: an unchanged settle. `settle-next` lists 19 once per marked
;; edge (eight times), then 39 and 45: ten pops. The former fuel 2 + |comps| (= 7) ran out
;; before 39 was settled: edge 45 -> 39 stayed marked although 39 was live, and 45 kept
;; pending = 1 with done-epoch = epoch forever (not live, not needs-run: stuck). The fuel is now
;; 2 + |edges| (every pop comes from a distinct marked edge, unmarked by its debtor's settle).
(def settle-dup
  (into it/base
        [[14 2 14 [1] 1] [4 14 1 15] [17 14 16] [21 16] [3 16 3 1 18] [20 16 1 5]   ; 14 tracks signal 3
         [14 2 19 [1] 1] [4 19 1 20] [17 19 21] [21 21]
         [18 21 [14] 0 1 23 []] [18 21 [14] 0 1 25 []] [18 21 [14] 0 1 27 []] [18 21 [14] 0 1 29 []]
         [18 21 [14] 0 1 31 []] [18 21 [14] 0 1 33 []] [18 21 [14] 0 1 35 []] [18 21 [14] 0 1 37 []]
         [20 21 1 6]                                                                  ; 19: eight dep edges on 14
         [14 2 39 [1] 1] [4 39 1 40] [17 39 41] [21 41] [18 41 [19] 0 1 43 []] [20 41 1 7]   ; 39 awaits 19
         [14 2 45 [1] 1] [4 45 1 46] [17 45 47] [21 47] [18 47 [39] 0 1 49 []] [20 47 1 8]   ; 45 awaits 39
         [2 3 0]                                                                      ; write: mark
         [19 14 51] [21 51] [3 51 3 1 53] [20 51 1 5]]))                              ; 14 re-runs, same result

(deftest settle-fuel-duplicates
  (let [w (reduce (fn [w item]
                    (is (it/d0-ok? w item) (str "D0 " (pr-str item)))
                    (let [o (en/world-step w item)] (is (true? (:accepted o)) (pr-str item)) (:world o)))
                  s/empty-world settle-dup)]
    (is (empty? (filter :marked (:edges w))) "every marked edge is unmarked by the settle")
    (is (true? (pr/h-mark w)))
    (is (every? #(or (= 4 (:id %)) (and (zero? (:pending %)) (= (:epoch %) (:done-epoch %)))) (:comps w))
        "14, 19, 39, 45 are live again")))

;; ---------------------------------------------------------------------------
;; Reactivation fuel (model bug, fixed in engine.clj `react-fuel`). 14 tracks signal 3, 19 awaits
;; 14, 25 awaits 19 at eight sites; unobserving all three demotes them (validity: 25 has eight
;; entries on 19). Observing 25 again reactivates 25, queues 19 eight times, reactivates 19 and
;; queues 14 last. The former fuel 2 + |comps| (= 6) ran out first: 14 stayed idle with no edge
;; on signal 3 while 19 (live) had a dep edge on it, so the write to 3 left 19 and 25 live with
;; their old results (stale). The fuel now counts the validity entries.
(def react-dup
  (into it/base
        [[14 2 14 [1] 1] [4 14 1 15] [17 14 16] [21 16] [3 16 3 1 18] [20 16 1 5]   ; 14 tracks 3
         [14 2 19 [1] 1] [4 19 1 20] [17 19 21] [21 21] [18 21 [14] 0 1 23 []] [20 21 1 6]  ; 19 awaits 14
         [14 2 25 [1] 1] [4 25 1 26] [17 25 27] [21 27]
         [18 27 [19] 0 1 29 []] [18 27 [19] 0 1 31 []] [18 27 [19] 0 1 33 []] [18 27 [19] 0 1 35 []]
         [18 27 [19] 0 1 37 []] [18 27 [19] 0 1 39 []] [18 27 [19] 0 1 41 []] [18 27 [19] 0 1 43 []]
         [20 27 1 7]                                                                  ; 25: eight edges on 19
         [5 26] [5 20] [5 15]                                                         ; all three demoted
         [4 25 1 45]]))                                                               ; reactivation of 25

(deftest react-fuel-duplicates
  (let [w (reduce (fn [w item]
                    (is (it/d0-ok? w item) (str "D0 " (pr-str item)))
                    (let [o (en/world-step w item)] (is (true? (:accepted o)) (pr-str item)) (:world o)))
                  s/empty-world react-dup)
        idle? (fn [w c] (:idle (first (filter #(= c (:id %)) (:comps w)))))
        live? (fn [w c] (some #(and (= c (:id %)) (not (:idle %)) (= (:epoch %) (:done-epoch %)) (zero? (:pending %))) (:comps w)))]
    (is (every? #(false? (idle? w %)) [14 19 25]) "the whole chain is reactivated")
    (is (some #(and (= 1 (:kind %)) (= 14 (:creditor %)) (= 3 (:debtor %))) (:edges w)) "14 depends on signal 3 again")
    (let [w2 (:world (en/world-step w [2 3 9]))]
      (is (not-any? #(live? w2 %) [14 19 25]) "a write to 3 invalidates the chain (no stale result)"))))

;; ---------------------------------------------------------------------------
;; h-mark was FALSE before Z#59 (branch rest), and with it L5's safety half at a quiescent D0 world:
;; computation 16 awaits signals 14 and 15 in one `all` await (dep edges 21 on 14 and 22 on 15, both
;; at site 0) and completes; computation 23 awaits 16 (edge 28) and completes. Writes to 14 and 15
;; fired both edges of 16 (28 marked). T11 then picked the entry by `at` (22) and kept the fired
;; sibling 21 (the cut kept at <= E.at); the restarted run completed without re-awaiting, so 16 was
;; live with a leftover fired edge, and a later write to 14 marked 28 again through it (the dirty
;; set followed dep edges in any phase): 23 stayed pending with done-epoch = epoch forever.
;; RESOLVED by Z#59 (engine e735039, oracle sample 13 is the engine's trace): (b) T11's E is the
;; earliest fired dep edge in creation order (21) and every dep edge created after it is cut,
;; the sibling 22 at E's own site included; (a) a write marks only from computations whose dep
;; edge on the written source fires (was armed). A write to 15 (no edge left) marks nothing; a
;; write to 14 fires the re-armed E, invalidates 16 (needs-run, eligible), and 23 waits on it.
(def fired-sibling
  (into it/base
        [[1 2 0 0 14] [1 2 0 0 15]                                          ; signals 14, 15
         [14 2 16 [1] 1] [4 16 1 17] [17 16 18] [21 18]
         [18 18 [14 15] 1 1 20 []] [20 18 1 5]                              ; 16: await-all [14 15] (edges 21, 22), live
         [14 2 23 [1] 1] [4 23 1 24] [17 23 25] [21 25] [18 25 [16] 0 1 27 []] [20 25 1 6]  ; 23 awaits 16 (edge 28)
         [2 14 7] [2 15 8]                                                  ; both edges of 16 fired; 28 marked
         [19 16 29] [21 29] [20 29 1 5]]))                                  ; 16 restarts (entry 21), completes: live

(defn- find-row [w t id] (first (filter #(= id (:id %)) (get w t))))
(defn- cone [w c0]
  (loop [todo [c0] seen #{}]
    (if-let [x (first todo)]
      (if (seen x) (recur (rest todo) seen) (recur (concat (rest todo) (pr/csucc w x)) (conj seen x)))
      seen)))
(defn- l5-holds? [w c0]
  (let [bl (set (en/blocked-set w)) cn (cone w c0)]
    (boolean (or (some bl cn)
                 (some (fn [x] (when-let [c (find-row w :comps x)] (and (not (:idle c)) (en/needs-run w c) (en/eligible w c)))) cn)
                 (some (fn [x] (and (some? (find-row w :tasks x)) (en/blk-base w x) (not (bl x)))) cn)))))
(defn- live? [c] (and (not (:idle c)) (= (:epoch c) (:done-epoch c)) (zero? (:pending c))))

(deftest h-mark-fired-sibling-resolved
  (let [ws (reductions (fn [w item]
                         (is (it/d0-ok? w item) (str "D0 " (pr-str item)))
                         (let [o (en/world-step w item)] (is (true? (:accepted o)) (pr-str item)) (:world o)))
                       s/empty-world fired-sibling)
        w (last ws)
        e21 (find-row w :edges 21)]
    (is (every? true? (map pr/h-mark ws)) "h-mark after every step")
    (is (and (= s/ph-armed (:phase e21)) (= 16 (:creditor e21)) (= 14 (:debtor e21)))
        "E = 21 (the earliest fired edge in creation order) is re-armed for the restart")
    (is (nil? (find-row w :edges 22)) "its sibling 22 at the same site is cut (Z#59)")
    (is (live? (find-row w :comps 16)))
    (is (live? (find-row w :comps 23)))
    (let [w2 (:world (en/world-step w [2 15 9]))]
      (is (empty? (filter :marked (:edges w2))) "a write to 15 marks nothing")
      (is (live? (find-row w2 :comps 23)))
      (let [w3 (reduce (fn [w item] (let [o (en/world-step w item)] (is (true? (:accepted o)) (pr-str item)) (:world o)))
                       w2 [[2 14 10] [21 6] [20 6 1 1] [21 9] [20 9 1 1]])   ; write 14, quiesce
            c16 (find-row w3 :comps 16)]
        (is (true? (:marked (find-row w3 :edges 28))) "a write to 14 fires E: 16 invalidated, 28 marked")
        (is (and (not (live? c16)) (en/needs-run w3 c16) (en/eligible w3 c16)) "16 is dirty, needs-run and eligible")
        (is (true? (pr/h-mark w3)))
        (is (true? (pr/quiescent w3)))
        (is (true? (l5-holds? w3 23)) "L5's safety half holds for 23")))))

;; Tripwire: h-mark and h-mem2 on every commit of the oracle samples 7-13 (sample 13 is the engine's
;; trace of the former counterexample)
(deftest l5-facts-samples
  (doseq [n [7 8 9 10 11 12 13]]
    (let [lg (o/read-log (str "test/spindel/v2/oracle/log-sample-" n ".edn"))
          ws (reductions (fn [w c] (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c))))))
                         s/empty-world lg)]
      (is (every? true? (map pr/h-mark ws)) (str "h-mark, sample " n))
      (is (every? true? (map l5/h-mem2 ws)) (str "h-mem2, sample " n)))))

;; ---------------------------------------------------------------------------
;; Tripwire: h-cur, h-mark and h-mem2 (L5's state facts as step invariants) and I5's dep-final clause for non-members at
;; every step of the random drivers

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
            (is (true? (pr/h-cur w2)) (str "h-cur " tag))
            (is (true? (pr/h-mark w2)) (str "h-mark " tag))
            (is (true? (l5/h-mem2 w2)) (str "h-mem2 " tag))
            (is (true? (l5/i5-dep-final-mem w2)) (str "i5-dep-final-mem " tag))
            (recur (inc i) w2)))))))

(deftest l5-facts-random
  (drive 20261141 15 80 false)
  (drive 20261142 15 80 true)
  (drive 109 22 80 true))
