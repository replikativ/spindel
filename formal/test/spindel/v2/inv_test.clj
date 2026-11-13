(ns spindel.v2.inv-test
  "Loading spindel.v2.inv kernel-checks the invariant theorems. The tests run the invariant
  predicates (`inv-all`) as a tripwire after every step of random item sequences, both
  unrestricted and D0-respecting (while a run holds the slice only its body items occur), with
  the spec's literal readings (`lit-*`) as a second tripwire since the alignment pass
  (Z#38-Z#42), and replay the former counterexamples to the literal readings: each D0 trace
  now ends with the literal reading true, or its offending item is refused (Z#40). See the
  findings in notes/PLAN.md."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.step :as st]
            [spindel.v2.engine :as en]
            [spindel.v2.retain :as retain]
            [spindel.v2.inv :as inv]
            [spindel.v2.engine-test :as et]))

(def theorems
  '[i13-fire-dep-live i13-fire-dep-stale i13-fire-wait-stale i13-complete-stale i13-complete-raw-stale
    step-l1 step-l1-comp step-l1-run
    ;; I10 D0
    sl-rule-r i10-raw0 i10-raw step-i10-slice i10-slice-empty i10-slice-count step-d0
    ;; I9
    s9-cancel-acts s9-rule-r i9-raw0 i9-raw step-i9 i9-empty
    ;; I5 (wait half)
    i5-wait-of-sample step-i5-wait])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t))))
        (str t))))

;; ---------------------------------------------------------------------------
;; The former counterexamples to the literal readings, resolved by the alignment pass
;; (spec Z#38-Z#42): each D0 trace from `empty-world` now ends in a world where the literal
;; reading holds; where the spec now refuses the offending item, the trace's last item is
;; refused (`refused-last`).

;; three sources (3 signal, 11 deferred, 12 mailbox, 13 semaphore), computation 4 observed by
;; edge 5 with run 6 (scope 7), task 8 with run 9 (scope 10); next-id 14; no slice held
(def base
  [[1 2 0 0 3] [14 2 4 [1] 1] [4 4 1 5] [17 4 6] [16 2 1 8 []]
   [1 2 2 0 11] [1 2 3 0 12] [1 2 4 1 13]])

(def counterexamples
  {;; I1 (Z#38): run 9 parks inside a finally region, is cancelled (unwinding, kept by cleanup[9]
   ;; with its run scope 10), then release-world closes the root scope; cleanup[9] retains scope
   ;; 10's ancestor chain (the root scope 2) as storage, so the parent exists
   'lit-i1-scope (into base [[21 9] [35 9] [18 9 [11] 0 1 14 []] [30 9] [31]])
   ;; I10 (Z#42): run 6 parks in a finally region; unobserve demotes fresh computation 4, whose
   ;; current run 6 (cancelled in the round, kept in cleanup) is made stale by the epoch step;
   ;; observe + start: run 17 is the only current run
   'lit-i10-current (into base [[21 6] [35 6] [18 6 [11] 0 1 14 []] [5 5] [4 4 1 16] [17 4 17]])
   ;; I7 (Z#40): the cleanup slice of demoted computation 4's run may not create a source
   'lit-i7-basis (into base [[21 6] [35 6] [18 6 [11] 0 1 14 []] [5 5] [29 6] [0 6 2 0 16]])
   ;; I8 sources (Z#40): run 9's cleanup slice (after release-world) may not create a source
   'lit-i8-sources (into base [[21 9] [35 9] [18 9 [11] 0 1 14 []] [31] [29 9] [0 9 2 0 16]])
   ;; I8 runs (Z#41): task 14 spawned in run 9 (run scope 16, parent 10) is detached to the root
   ;; scope, which re-parents scope 16 under it; cancelling run 9 closes scope 10's subtree
   ;; without 16, so task 14's run spawns task 19 into an open scope
   'lit-i8-runs (into base [[21 9] [15 9 1 14 []] [18 9 [11] 0 1 17 []] [34 14 2] [30 9] [21 15] [15 15 1 19 []]])
   ;; I9 (Z#40): the cleanup slice of cancelled run 6 may not arm a resource (offload)
   'lit-i9-res (into base [[21 6] [35 6] [18 6 [11] 0 1 14 []] [5 5] [29 6] [8 6 2 0 16]])
   ;; I5 (Z#39): computation 4's run awaits task 8 (dep edge 15, member of activation 14); host
   ;; cancel of task 8's run makes it final: the dep creditor gets err ::cancelled (run 6
   ;; resumes) and the edge is removed
   'lit-i5-dep-final (into base [[21 6] [18 6 [8] 1 3 14 [8]] [30 9]])})

(def refused-last '#{lit-i7-basis lit-i8-sources lit-i9-res})

(defn d0-ok? [w item]
  (let [sl (filter :slice (:runs w))]
    (or (empty? sl)
        (and (#{0 3 8 13 15 18 20 27 32 35 36 37} (first item)) (= (second item) (:stamp (first sl)))))))

(def lits '[lit-i1-scope lit-i10-current lit-i7-basis lit-i8-sources lit-i8-runs lit-i9-res lit-i5-dep-final])
(defn lits-failing [w] (vec (remove #((ns-resolve 'spindel.v2.inv %) w) lits)))

(deftest literal-readings-resolved
  (doseq [[lit items] counterexamples]
    (testing (str lit)
      (let [n (count items)
            w (reduce (fn [w [i it]]
                        (is (d0-ok? w it) (str "D0 " (pr-str it)))
                        (let [o (en/world-step w it)
                              refuse? (and (refused-last lit) (= i (dec n)))]
                          (is (= (not refuse?) (:accepted o)) (str (if refuse? "refused " "accepted ") (pr-str it)))
                          (:world o)))
                      s/empty-world (map-indexed vector items))]
        (is (true? ((ns-resolve 'spindel.v2.inv lit) w)) (str lit " holds"))
        (is (= [] (lits-failing w)) "every literal reading holds")
        (is (true? (inv/inv-all w)) "the model's invariants hold")))))

;; ---------------------------------------------------------------------------
;; Tripwire on random items (the generator of engine-test)

(defn drive [seed runs steps d0?]
  (let [rng (java.util.Random. seed)]
    (dotimes [run runs]
      (loop [i 0 w (et/prefix-world)]
        (when (< i steps)
          (let [item (loop [k 0]
                       (let [it (et/random-item rng w)]
                         (if (or (not d0?) (d0-ok? w it) (> k 50)) it (recur (inc k)))))
                w2 (:world (en/world-step w item))]
            (is (true? (inv/inv-all w2)) (str "inv-all seed " seed " run " run " step " i " " (pr-str item)))
            (is (= [] (lits-failing w2)) (str "literal readings seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest tripwire-random
  (drive 20261104 20 60 false)
  (drive 20261105 20 60 true))

;; ---------------------------------------------------------------------------
;; Found by the literal I10 proof (spindel.v2.lit): `complete` with a result tag other than
;; ok/err (tag 0 = none) was accepted, so task 14 (spawned by computation 4's run 6, kept by its
;; basis) ended with result none and no run, against I10 ("a task has a run until it
;; completes"). The model now refuses such a malformed item (`complete-refused`).
(deftest complete-tag-none-refused
  (let [items (into base [[21 6] [15 6 1 14 []] [20 6 1 3] [21 15] [20 15 0 5]])
        n (count items)
        w (reduce (fn [w [i it]]
                    (let [o (en/world-step w it)]
                      (is (= (not= i (dec n)) (:accepted o)) (pr-str it))
                      (:world o)))
                  s/empty-world (map-indexed vector items))]
    (is (true? (inv/inv-i10-task w)))
    (is (true? (inv/inv-all w)))))

;; ---------------------------------------------------------------------------
;; Literal I5 (no armed dep edge on a final debtor) was false after Z#48 (finding of the p3 pass):
;; reactivation (§3.4) re-armed the dep edges of an idle computation's validity entries even when
;; the debtor became final meanwhile. Computation 10 tracks signal 7 (owned by task 4's run scope
;; 6), completes and is demoted (validity (7, 0)); task 4 completes, T13 closes scope 6 and
;; signal 7 (final); observing 10 again reactivates it. Z#51 (engine and model): reactivation
;; takes no dep edge on a final debtor (consumed, no id allocated); 10 is live with no dep edge.
(def i5-reactivation
  [[1 2 2 0 3]          ; deferred 3
   [16 2 1 4 []]        ; task 4, run 5, run scope 6
   [21 5]               ; run 5 takes the slice
   [0 5 0 0 7]          ; signal 7, owned by scope 6
   [18 5 [3] 0 1 8 []]  ; run 5 awaits deferred 3 (activation 8) and parks
   [14 2 10 [1] 1]      ; computation 10
   [4 10 1 11]          ; observe 10 (edge 11)
   [17 10 12]           ; start 10: run 12, run scope 13
   [21 12]
   [3 12 7 0 14]        ; run 12 tracks signal 7 (dep edge 14)
   [20 12 1 5]          ; run 12 completes
   [5 11]               ; unobserve: 10 is demoted (validity [(7, 0)])
   [25 3 9]             ; deliver 3: run 5 resumes
   [21 5]
   [20 5 1 0]           ; task 4 completes: run 5 retires, scope 6 and signal 7 close
   [4 10 1 15]])        ; observe 10 again: reactivation takes no edge onto the closed signal 7 (Z#51)

(deftest literal-i5-reactivation-resolved
  (let [w (reduce (fn [w it]
                    (is (d0-ok? w it) (str "D0 " (pr-str it)))
                    (let [o (en/world-step w it)] (is (true? (:accepted o)) (pr-str it)) (:world o)))
                  s/empty-world i5-reactivation)]
    (is (true? (inv/lit-i5-dep-final w)) "Z#51: no armed dep edge on the closed signal 7")
    (is (not-any? #(and (= 1 (:kind %)) (= 7 (:debtor %))) (:edges w)) "no dep edge onto 7")
    (is (= 16 (:next-id w)) "the consumed edge allocates no id (observe edge 15 only)")
    (is (some #(and (= 10 (:id %)) (not (:idle %)) (= (:epoch %) (:done-epoch %))) (:comps w)) "10 is reactivated (live)")
    (is (= [] (lits-failing w)) "every literal reading holds")
    (is (true? (inv/inv-all w)) "the model's invariants hold")))

;; ---------------------------------------------------------------------------
;; Literal I1 (scope parent), the former counterexample (found by branch i10): cleanup[R]'s rows
;; held its run scope's ancestors as computed when the entry was made (Z#38), and detach re-parents
;; a task's run scope later (Z#41), so Rule R removed the new parent while the entry kept the
;; scope. RESOLVED by Z#52: the chain is the run scope's CURRENT chain, read from the parent fields
;; at every Rule R pass (retain `scope-ancestors` in `cleanup-contrib`), not stored; the entry stores
;; the subtree rows only. Scope 24 (closed, the new parent of 10) is kept by cleanup[15].

(def i1-reparent
  (into base
        [[21 9]                       ; task 8's run 9 (scope 10, parent root 2) takes the slice
         [15 9 1 14 []]               ; spawns task 14: run 15, scope 16 (parent 10)
         [18 9 [11] 0 1 17 []]        ; run 9 parks on the deferred 11
         [21 15] [35 15]              ; run 15 enters a finally region
         [18 15 [11] 0 1 19 []]       ; and parks
         [30 15]                      ; host cancel: run 15 unwinds; cleanup[15] rows = (16)
         [16 2 1 21 []] [21 22]       ; task 21's run 22 (scope 23)
         [32 22 24]                   ; opens the explicit scope 24 (parent 23)
         [18 22 [11] 0 1 25 []]       ; and parks
         [34 8 24]                    ; detach task 8 to scope 24: scope 10's parent := 24
         [33 24]]))                   ; close 24: run 9 is cancelled and retires; 24 is not kept

(deftest literal-i1-reparent-resolved
  (let [w (reduce (fn [w it]
                    (is (d0-ok? w it) (str "D0 " (pr-str it)))
                    (let [o (en/world-step w it)] (is (true? (:accepted o)) (pr-str it)) (:world o)))
                  s/empty-world i1-reparent)]
    (is (true? (inv/lit-i1-scope w)) "scope 10's parent 24 is kept")
    (is (some #(and (= 10 (:id %)) (= 24 (:parent %))) (:scopes w)))
    (is (some #(and (= 24 (:id %)) (not (:open %))) (:scopes w)) "24 is closed and kept")
    (is (some #(and (= 15 (:run %)) (= '(16) (seq (:rows %)))) (:cleanup w)) "the entry stores no chain (Z#52)")
    (is (= #{10 24 23 2} (set (retain/scope-ancestors w 16))) "the current chain of run scope 16")
    (is (= [] (lits-failing w)) "every literal reading holds")
    (is (true? (inv/inv-all w)) "the model's invariants hold")))

;; Z#52, second half: a run scope is removed no earlier than its run's retirement (T13 step 4),
;; even when an ancestor's close empties its subtree first. In the trace above, closing 24 cancels
;; and retires run 9 and closes the subtree 24 -> 10 -> 16; run 15 (scope 16) is unwinding, so the
;; subtree is not empty (`subtree-empty` counts run rows scoped in it) and Rule R keeps 16 (cleanup[15]
;; holds the run row, hence its scope). 16 goes in the slice-exit item that retires 15 (T13 step 4);
;; 10 and 24, closed and no longer kept, go in the same commit's Rule R pass.
(deftest z52-run-scope-held-until-retirement
  (let [scopes (fn [w] (set (map :id (:scopes w))))
        w0 (reduce (fn [w it] (:world (en/world-step w it))) s/empty-world i1-reparent)
        w1 (:world (en/world-step w0 [29 15]))
        w2 (:world (en/world-step w1 [36 15]))
        o3 (en/world-step w2 [37 15])
        w3 (:world o3)]
    (is (every? #(contains? (scopes %) 16) [w0 w1 w2]) "scope 16 is held while run 15 unwinds")
    (is (some #(and (= 15 (:id %)) (= 16 (:scope %))) (:runs w2)))
    (is (true? (:accepted o3)))
    (is (not-any? #(= 15 (:id %)) (:runs w3)) "slice-exit retires run 15 (T13)")
    (is (empty? (filter #{10 16 24} (scopes w3))) "16 goes at the retirement; 10 and 24 with it")
    (is (every? inv/lit-i1-scope [w0 w1 w2 w3]))))

;; ---------------------------------------------------------------------------
;; Literal I5's dep-final clause for unfilled activation members: RESOLVED by Z#53/Z#54 (was the
;; counterexample of branch l5: computation 17's run 19 awaited mailbox 14, owned by task 8's
;; run scope 10, through a member dep edge; cancelling task 8 detached (closed) 14 and T10 kept the
;; armed member edge, so run 19 stayed parked on a final debtor).
;; Z#54: `await` on a mailbox is refused (the engine logs it as `take`); the take parks run 19 on a
;; wait edge. Z#53: closing a source wakes its waiters and fills its unfilled members, with err
;; ::closed (Nat 2) for a mailbox/semaphore/undelivered deferred; so run 19 resumes and no armed dep
;; edge has a final debtor. The dep-member form of the old trace awaits an undelivered deferred.
(def i5-member-prefix
  [[21 9]                      ; task 8's run 9 takes the slice
   [0 9 3 0 14]                ; mailbox 14, owned by run scope 10
   [18 9 [11] 0 1 15 []]       ; run 9 parks on deferred 11
   [14 2 17 [1] 1]             ; computation 17
   [4 17 1 18]                 ; observed (edge 18)
   [17 17 19] [21 19]])        ; run 19 (scope 20) takes the slice

(def i5-member-final
  (into base (concat i5-member-prefix
                     [[27 19 14 1 21]     ; Z#54: run 19 takes mailbox 14: activation 21, wait edge 22, parks
                      [30 9]])))          ; host cancel of run 9: scope 10 goes, mailbox 14 is detached (closed)

(def i5-member-deferred
  (into base (concat (assoc i5-member-prefix 1 [0 9 2 0 14])   ; deferred 14 (undelivered), owned by scope 10
                     [[18 19 [14] 0 1 21 []]  ; run 19 awaits it: activation 21, member dep edge 22, parks
                      [30 9]])))

(defn- run-items [items]
  (reduce (fn [w it]
            (is (d0-ok? w it) (str "D0 " (pr-str it)))
            (let [o (en/world-step w it)] (is (true? (:accepted o)) (pr-str it)) (:world o)))
          s/empty-world items))

(deftest literal-i5-member-final-resolved
  (testing "Z#54: await on a mailbox is refused (no commit)"
    (let [w (run-items (into base i5-member-prefix))
          o (en/world-step w [18 19 [14] 0 1 21 []])]
      (is (false? (:accepted o)))
      (is (= w (:world o)))))
  (doseq [[nm items] [["take on a mailbox" i5-member-final] ["await on an undelivered deferred" i5-member-deferred]]]
    (testing nm
      (let [w (run-items items)
            r19 (some #(when (= 19 (:id %)) %) (:runs w))]
        (is (some #(and (= 14 (:id %)) (not (:open %))) (:sources w)) "14 is closed (final)")
        (is (= (s/->RunResult s/res-err 2) (st/deb-result w 14)) "Z#53: it delivers err ::closed (2)")
        (is (= s/act-active (:act r19)) "Z#53: the close woke run 19 (activation 21 filled, resumed)")
        (is (not-any? #(= 21 (:id %)) (:acts w)))
        (is (not-any? #(= 22 (:id %)) (:edges w)) "the member edge is consumed")
        (is (true? (inv/lit-i5-dep-final w)))
        (is (= [] (lits-failing w)))
        (is (true? (inv/inv-all w)) "the model's invariants hold")))))
