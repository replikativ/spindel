(ns spindel.v2.progress
  "Progress (spec §6 L2, L5 safety half) as kernel-checked measure lemmas over the model's step
  `world-step` (Init only).

  L2, the join measure. For a run row r:
    mu-f r = |r.finalizers| + pend r      pend r = 1 if r has a finalizer or holds the slice, else 0
    mu-z r = |r.resources|
  mu-f counts the remaining finalizers plus the cleanup slice that still has to return (Z#35: one
  cleanup slice runs the whole chain, each region's exit is a `finally-exit`, the slice's return is
  `slice-exit`); mu-z counts the outstanding resources. The measure of a cancelled-unretired run
  (`act = done`, row still present) is the pair (mu-f, mu-z), ordered lexicographically as the spec's
  two phases (finalizers, then resources); both components are monotone, so the sum and the product
  order decrease as well.

  Theorems (all under the safety bundle `p3b` of spindel.v2.p3 and `sok`, which is proved
  invariant here):
    sok                   every run that holds the slice is alive or unwinding (a completed run holds
                          no slice); `step-sok`, `sok-empty`
    step-mu-le      (b)   a run that is done in w is, after any step, absent or done with mu-f and
                          mu-z each at most its value in w (no transition increases the measure of an
                          existing cancelled run; runs that become done in the step are new to the
                          measure, their measure is whatever their cancel left)
    finally-exit-dec (a)  an accepted `finally-exit` of a done run drops its mu-f by one
    slice-exit-dec  (a)   an accepted `slice-exit r` drops mu-f (from 1 to 0)
    ack-dec         (a)   an accepted resource acknowledgement (T15) drops its owner's mu-z
    slice-exit-retires, ack-retires (c)
                          when that event leaves the run with mu = (0, 0) (no finalizer, no slice, no
                          resource) the run is retired (T13) in the same step: no row with its id
                          remains in the step's world
  The resource fire of an offload return (T18) does not change the measure: a done run's resources
  are cancelling or fired (I9), the fire only enables the acknowledgement (T15), which drops mu-z.
  `finalize r` (the cleanup slice is scheduled) leaves mu-f unchanged (pend was already 1).

  Paper argument (not formalized; the model has no executions): fair execution => every cleanup
  entry is retired and `release-world` completes. Take a done run r. By (b) its measure
  (mu-f, mu-z) never increases; by (a) every finalizer exit, slice return and acknowledgement
  strictly decreases it, lexicographically. Under the environment assumptions of L2 (B9: every
  cleanup slice is finite, so a scheduled cleanup slice performs its `finally-exit`s and returns;
  a fair scheduler issues `finalize r` while r has a finalizer and no slice is held; every offload
  returns and every resource is acknowledged) a step that decreases mu(r) is always eventually taken
  while mu(r) > (0, 0), so by well-foundedness of N x N (lex) mu(r) reaches (0, 0) after finitely
  many steps, and by (c) r is retired in that step. Release-world (T21) cancels every remaining run
  (new entries of the measure), each of which is then retired by the same argument; the world
  measure (the sum of mu over the finitely many done runs) decreases with every such event and
  never increases for existing runs, so `release-world` completes.

  L5, safety half (`l5-safety`, `l5-dirty`): in a quiescent world (`quiescent`: every run parked
  or done, none holding the slice), a computation c0 that is not idle and not live (in particular
  a dirty one) has in its cone (`csucc`: dep debtors and the debtors of the unfilled members of the
  current run, transitively; generic `Reach`) an entity that is Blocked (`Derive`, the least
  fixpoint of §4.5.6), or a non-idle, needs-run, eligible computation (T11 is enabled), or a task
  whose current run is parked and that is not Blocked. Proof: induction on rank (I12, `ranks-ok`
  in p3b) over the waiting computations of the cone; a minimal one is eligible if it needs a run
  (its dirty dep debtors have smaller ranks), has no marked in-edge if done-epoch = epoch, and
  otherwise its current run is parked and every member is a leaf, a parked task or a smaller
  waiting computation, so it is Blocked unless a task is not. Three state facts are hypotheses,
  checked as tripwires at every quiescent point of the random drivers (progress_test), not yet
  proved through the step: `h-cur` (a done current run has set done-epoch), `h-mark` (a marked
  edge is a dep edge on a waiting computation), `h-mem` (an unfilled member of a parked computation
  run is a leaf, a task with a parked current run, or a waiting computation it has a dep edge on).
  Paper argument for the third disjunct: a parked, non-Blocked task has a member that is neither a
  leaf nor Blocked; in a quiescent world that member is a parked task or a waiting computation, and
  following such members never ends in a source or resource; the cone is finite, so the walk
  revisits an entity: a cyclic wait, i.e. a user deadlock (X#8). The liveness half (a fair
  scheduler eventually starts every eligible computation) stays a paper argument (A#8).

  How: the bundle `mb mux mf mz mg w` = inv-sample w, mux < next-id, and every run row satisfies
  `slice-ok` and the tracking constraint `mu-at` on the rows with id mux (mode mg: 0 = such rows are
  done with mu-f <= mf and mu-z <= mz, 1 = there is no such row, otherwise off). Every composite
  inv-sample lemma of `raw-inv` and `inv-normalize` is re-checked for the bundle by spindel.v2.lit's
  `lcopy!`; run edits by a row function that cannot raise the measure go through `mb-run-upd`
  (with a per-function lemma `<f>-mb`), the ones that can (arm, finally-enter, park, take-park,
  schedule, finalize) only touch an alive run, or a cleanup-ready one (`mb-run-upd-ne`,
  `mb-run-upd-q`); their callers are overridden."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.rank :refer :all]
            [spindel.v2.rank-step :refer :all]
            [spindel.v2.casc :refer :all]
            [spindel.v2.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.lit :refer :all]
            [spindel.v2.idle :refer :all]
            [spindel.v2.p3 :refer :all]))

;; ===========================================================================
;; Part A. The measure and the bundle
;; ===========================================================================

(a/defn fins-len [fs :- (List Finalizer)] Nat (match fs [nil 0] [(cons h t) (+ (fins-len t) 1)]))
(a/defn pend [r :- RunRow] Nat (if (Bool.or (Bool.not (fins-empty (:finalizers r))) (:slice r)) 1 0))
(a/defn mu-f [r :- RunRow] Nat (+ (fins-len (:finalizers r)) (pend r)))
(a/defn mu-z [r :- RunRow] Nat (nat-len (:resources r)))
(a/defn run-done [r :- RunRow] Bool (Nat.beq (:act r) act-done))
;; a run that holds the slice is alive or unwinding (a completed run holds none)
(a/defn slice-ok [r :- RunRow] Bool
  (Bool.or (Bool.not (:slice r)) (Bool.or (Bool.not (run-done r)) (run-unwinding r))))
;; the tracking constraint on the rows with id mux
(a/defn mu-at [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, r :- RunRow] Bool
  (Bool.or (Bool.not (Nat.beq (:id r) mux))
   (Bool.or (Nat.blt 1 mg)
    (Bool.and (Nat.beq mg 0)
     (Bool.and (run-done r) (Bool.and (Nat.ble (mu-f r) mf) (Nat.ble (mu-z r) mz)))))))
(a/defn mb-row [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, r :- RunRow] Bool
  (Bool.and (slice-ok r) (mu-at mux mf mz mg r)))
(a/defn mb-rest [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World] Bool
  (Bool.and (Nat.blt mux (:next-id w)) (tbl-all (mb-row mux mf mz mg) (:runs w))))
(a/defn mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World] Bool
  (Bool.and (inv-sample w) (mb-rest mux mf mz mg w)))
;; the untracked bundle: slice-ok for every run
(a/defn sok [w :- World] Bool (mb 0 0 0 2 w))

(a/theorem mb-sample [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World]
  (=> (= (mb mux mf mz mg w) true) (= (inv-sample w) true))
  (intro h) (simp only [mb Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem mb-rest-of [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World]
  (=> (= (mb mux mf mz mg w) true) (= (mb-rest mux mf mz mg w) true))
  (intro h) (simp only [mb Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem mb-intro [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World]
  (=> (= (inv-sample w) true) (= (mb-rest mux mf mz mg w) true) (= (mb mux mf mz mg w) true))
  (intros h1 h2) (simp only [mb h1 h2 Bool.and_self]))
(a/theorem mb-parts [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World]
  (=> (= (mb mux mf mz mg w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (mb-sample mux mf mz mg w h))))
(a/theorem mb-rest-parts [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World]
  (=> (= (mb-rest mux mf mz mg w) true)
      (And (< mux (:next-id w)) (= (tbl-all (mb-row mux mf mz mg) (:runs w)) true)))
  (intro h) (simp only [mb-rest Bool.and_eq_true Nat.blt_eq] at h) (exact h))
(a/theorem mb-rest-mk [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World]
  (=> (< mux (:next-id w)) (= (tbl-all (mb-row mux mf mz mg) (:runs w)) true) (= (mb-rest mux mf mz mg w) true))
  (intros h1 h2) (simp only [mb-rest Bool.and_eq_true Nat.blt_eq]) (exact (And.intro h1 h2)))

;; ===========================================================================
;; Part B. Rows: which run-row functions keep the bundle's row predicate
;; ===========================================================================

(a/theorem mu-at-ne [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, r :- RunRow]
  (=> (= (Nat.beq (:id r) mux) false) (= (mu-at mux mf mz mg r) true))
  (intro h) (simp only [mu-at h Bool.not_false Bool.true_or]))

(a/theorem mu-at-mono [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, r :- RunRow, r2 :- RunRow]
  (=> (= (:id r2) (:id r)) (=> (= (run-done r) true) (= (run-done r2) true)) (<= (mu-f r2) (mu-f r)) (<= (mu-z r2) (mu-z r))
      (= (mu-at mux mf mz mg r) true) (= (mu-at mux mf mz mg r2) true))
  (intros hi hd hf hz h)
  (cases hx (Nat.beq (:id r) mux))
  (case [false] (exact (mu-at-ne mux mf mz mg r2 (Eq.trans (congrArg (fn [n :- Nat] (Nat.beq n mux)) hi) hx))))
  (case [true]
    (have hx2 (= (Nat.beq (:id r2) mux) true)) (exact (Eq.trans (congrArg (fn [n :- Nat] (Nat.beq n mux)) hi) hx))
    (simp only [mu-at hx Bool.not_true Bool.false_or] at h)
    (simp only [mu-at hx2 Bool.not_true Bool.false_or])
    (cases hb (Nat.blt 1 mg))
    (case [true] (simp only [Bool.true_or]))
    (case [false]
      (simp only [hb Bool.false_or Bool.and_eq_true Nat.ble_eq] at h)
      (simp only [Bool.false_or Bool.and_eq_true Nat.ble_eq])
      (exact (And.intro (And.left h)
               (And.intro (hd (And.left (And.right h)))
                 (And.intro (Nat.le_trans hf (And.left (And.right (And.right h))))
                            (Nat.le_trans hz (And.right (And.right (And.right h)))))))))))

(a/theorem mb-row-mono [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, r :- RunRow, r2 :- RunRow]
  (=> (= (:id r2) (:id r)) (=> (= (slice-ok r) true) (= (slice-ok r2) true))
      (=> (= (run-done r) true) (= (run-done r2) true)) (<= (mu-f r2) (mu-f r)) (<= (mu-z r2) (mu-z r))
      (= (mb-row mux mf mz mg r) true) (= (mb-row mux mf mz mg r2) true))
  (intros hi hs hd hf hz h)
  (simp only [mb-row Bool.and_eq_true] at h)
  (simp only [mb-row Bool.and_eq_true])
  (exact (And.intro (hs (And.left h)) (mu-at-mono mux mf mz mg r r2 hi hd hf hz (And.right h)))))

;; x is untracked: the mode is off, or x is not the tracked id
(a/defn untracked [mux :- Nat, mg :- Nat, x :- Nat] Bool (Bool.or (Nat.blt 1 mg) (Bool.not (Nat.beq x mux))))

(a/theorem mu-at-un [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, r :- RunRow]
  (=> (= (untracked mux mg (:id r)) true) (= (mu-at mux mf mz mg r) true))
  (intro h)
  (cases hb (Nat.blt 1 mg))
  (case [true] (simp only [mu-at hb Bool.true_or Bool.or_true]))
  (case [false]
    (simp only [untracked hb Bool.false_or] at h)
    (simp only [mu-at h Bool.true_or])))

;; an alive row is untracked
(a/theorem mb-row-alive-un [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, r :- RunRow]
  (=> (= (mb-row mux mf mz mg r) true) (= (run-done r) false) (= (untracked mux mg (:id r)) true))
  (intros h hd)
  (cases hx (Nat.beq (:id r) mux))
  (case [false] (simp only [untracked hx Bool.not_false Bool.or_true]))
  (case [true]
    (cases hb (Nat.blt 1 mg))
    (case [true] (simp only [untracked hb Bool.true_or]))
    (case [false]
      (simp [mb-row mu-at hx hb hd] at h))))

;; ---- the measure under row functions

(a/theorem mu-f-off [r :- RunRow, r2 :- RunRow]
  (=> (= (:finalizers r2) (:finalizers r)) (= (:slice r2) false) (<= (mu-f r2) (mu-f r)))
  (intros hf hs)
  (simp only [mu-f pend hf hs Bool.or_false])
  (cases he (fins-empty (:finalizers r)))
  (all_goals (cases hl (:slice r)))
  (all_goals (simp only [he hl Bool.not_true Bool.not_false Bool.or_true Bool.or_false Bool.true_or Bool.false_or]))
  (all_goals (omega)))

;; mu-f on the raw fields
(a/defn mfv [fs :- (List Finalizer), s :- Bool] Nat (+ (fins-len fs) (if (Bool.or (Bool.not (fins-empty fs)) s) 1 0)))
(a/theorem fe-nil [] (= (fins-empty (List.nil Finalizer)) true) (rfl))
(a/theorem fe-cons [h :- Finalizer, t :- (List Finalizer)] (= (fins-empty (List.cons Finalizer h t)) false) (rfl))
(a/theorem bite-le [b :- Bool] (<= (if b 1 0) 1) (cases b) (all_goals (simp)))
(a/theorem mfv-pop [fs :- (List Finalizer), s :- Bool, s2 :- Bool]
  (=> (=> (= s2 true) (= s true)) (<= (mfv (fins-tail fs) s2) (mfv fs s)))
  (intro hs) (cases fs)
  (case [nil] (cases s) (all_goals (cases s2))
    (all_goals (simp only [mfv fins-tail fins-len fe-nil Bool.not_true Bool.not_false Bool.or_true Bool.or_false Bool.true_or Bool.false_or]))
    (all_goals (try (omega)))
    (have c := (hs (rfl))) (simp at c))
  (case [cons fh ft]
    (have b := (bite-le (Bool.or (Bool.not (fins-empty ft)) s2)))
    (simp only [mfv fins-tail fins-len fe-cons Bool.not_false Bool.true_or])
    (cases s) (all_goals (simp only [Bool.true_or Bool.or_true Bool.not_false])) (all_goals (omega))))

(a/theorem mu-f-pop [r :- RunRow, r2 :- RunRow]
  (=> (= (:finalizers r2) (fins-tail (:finalizers r))) (=> (= (:slice r2) true) (= (:slice r) true)) (<= (mu-f r2) (mu-f r)))
  (intros hf hs)
  (have e1 (= (mu-f r2) (mfv (:finalizers r2) (:slice r2)))) (rfl)
  (have e2 (= (mu-f r) (mfv (:finalizers r) (:slice r)))) (rfl)
  (rw [e1 e2 hf])
  (exact (mfv-pop (:finalizers r) (:slice r) (:slice r2) hs)))

(a/theorem nat-del-len [z :- Nat, xs :- (List Nat)] (<= (nat-len (nat-del z xs)) (nat-len xs))
  (induction xs)
  (case [nil] (simp only [nat-del nat-len]) (exact (Nat.le_refl 0)))
  (case [cons h t ih]
    (cases hb (Nat.beq h z))
    (all_goals (simp only [nat-del nat-len hb]))
    (omega) (omega)))

(a/theorem wake-done-eq [r :- RunRow] (= (run-done (run-wake r)) (run-done r))
  (cases hp (Nat.beq (:act r) act-parked))
  (case [false] (simp only [run-done run-wake wake-act hp]))
  (case [true]
    (have e (= (:act r) act-parked)) (exact (Nat.eq_of_beq_eq_true hp))
    (simp only [run-done run-wake wake-act hp e])))

(a/theorem done-of-eq [r :- RunRow, r2 :- RunRow] (=> (= (run-done r2) (run-done r)) (= (run-done r) true) (= (run-done r2) true))
  (intros e h) (exact (Eq.trans e h)))
(a/theorem sok-of-eq [r :- RunRow, r2 :- RunRow]
  (=> (= (:slice r2) (:slice r)) (= (run-done r2) (run-done r)) (= (run-unwinding r2) (run-unwinding r))
      (= (slice-ok r) true) (= (slice-ok r2) true))
  (intros e1 e2 e3 h) (simp only [slice-ok e1 e2 e3]) (exact h))

(a/theorem run-wake-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, r :- RunRow]
  (=> (= (mb-row mux mf mz mg r) true) (= (mb-row mux mf mz mg (run-wake r)) true))
  (intro h)
  (exact (mb-row-mono mux mf mz mg r (run-wake r) (rfl) (sok-of-eq r (run-wake r) (rfl) (wake-done-eq r) (rfl))
           (done-of-eq r (run-wake r) (wake-done-eq r)) (Nat.le_refl _) (Nat.le_refl _) h)))

(a/theorem run-complete-row-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, r :- RunRow]
  (=> (= (mb-row mux mf mz mg r) true) (= (mb-row mux mf mz mg (run-complete-row r)) true))
  (intro h)
  (have s (forall [hs :- (= (slice-ok r) true)] (= (slice-ok (run-complete-row r)) true)))
  (intro hs) (simp only [slice-ok run-complete-row Bool.not_false Bool.true_or])
  (have d (forall [hd :- (= (run-done r) true)] (= (run-done (run-complete-row r)) true)))
  (intro hd) (simp only [run-done run-complete-row act-done Nat.beq_refl])
  (exact (mb-row-mono mux mf mz mg r (run-complete-row r) (rfl) s d (mu-f-off r (run-complete-row r) (rfl) (rfl)) (Nat.le_refl _) h)))

(a/theorem run-cancel-row-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, r :- RunRow]
  (=> (= (mb-row mux mf mz mg r) true) (= (mb-row mux mf mz mg (run-cancel-row r)) true))
  (intro h)
  (have s (forall [hs :- (= (slice-ok r) true)] (= (slice-ok (run-cancel-row r)) true)))
  (intro hs) (simp only [slice-ok run-cancel-row run-unwinding mode-unwinding Nat.beq_refl Bool.or_true])
  (have d (forall [hd :- (= (run-done r) true)] (= (run-done (run-cancel-row r)) true)))
  (intro hd) (simp only [run-done run-cancel-row act-done Nat.beq_refl])
  (exact (mb-row-mono mux mf mz mg r (run-cancel-row r) (rfl) s d (Nat.le_refl _) (Nat.le_refl _) h)))

(a/theorem run-unres-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, z :- Nat, r :- RunRow]
  (=> (= (mb-row mux mf mz mg r) true) (= (mb-row mux mf mz mg (run-unres z r)) true))
  (intro h)
  (exact (mb-row-mono mux mf mz mg r (run-unres z r) (rfl) (fn [hs :- (= (slice-ok r) true)] hs) (fn [hd :- (= (run-done r) true)] hd)
           (Nat.le_refl _) (nat-del-len z (:resources r)) h)))

(a/theorem run-fin-pop-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, r :- RunRow]
  (=> (= (mb-row mux mf mz mg r) true) (= (mb-row mux mf mz mg (run-fin-pop r)) true))
  (intro h)
  (exact (mb-row-mono mux mf mz mg r (run-fin-pop r) (rfl) (fn [hs :- (= (slice-ok r) true)] hs) (fn [hd :- (= (run-done r) true)] hd)
           (mu-f-pop r (run-fin-pop r) (rfl) (fn [q :- (= (:slice r) true)] q)) (Nat.le_refl _) h)))

(a/theorem run-fin-pop-end-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, r :- RunRow]
  (=> (= (mb-row mux mf mz mg r) true) (= (mb-row mux mf mz mg (run-fin-pop-end r)) true))
  (intro h)
  (have s (forall [hs :- (= (slice-ok r) true)] (= (slice-ok (run-fin-pop-end r)) true)))
  (intro hs) (simp only [slice-ok run-fin-pop-end Bool.not_false Bool.true_or])
  (exact (mb-row-mono mux mf mz mg r (run-fin-pop-end r) (rfl) s (fn [hd :- (= (run-done r) true)] hd)
           (mu-f-pop r (run-fin-pop-end r) (rfl) (fn [q :- (= (:slice (run-fin-pop-end r)) true)] (Bool.noConfusion q))) (Nat.le_refl _) h)))

;; ===========================================================================
;; Part C. The bundle under the primitive edits
;; ===========================================================================

(a/theorem mb-rest-next [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, v :- Nat]
  (=> (= (mb-rest mux mf mz mg w) true) (<= (:next-id w) v) (= (mb-rest mux mf mz mg (set-next-id w v)) true))
  (intros h hv)
  (have p := (mb-rest-parts mux mf mz mg w h))
  (exact (mb-rest-mk mux mf mz mg (set-next-id w v) (Nat.lt_of_lt_of_le (And.left p) hv) (And.right p))))
(a/theorem mb-rest-bump [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World]
  (=> (= (mb-rest mux mf mz mg w) true) (= (mb-rest mux mf mz mg (bump w)) true))
  (intro h) (simp only [bump]) (exact (mb-rest-next mux mf mz mg w (+ (:next-id w) 1) h (Nat.le_succ (:next-id w)))))

(a/theorem mb-rest-mark-edge [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, x :- Nat]
  (= (mb-rest mux mf mz mg (mark-edge w x)) (mb-rest mux mf mz mg w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem mb-rest-unmark-edge [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, x :- Nat]
  (= (mb-rest mux mf mz mg (unmark-edge w x)) (mb-rest mux mf mz mg w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem mb-rest-remove-edge [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, x :- Nat]
  (= (mb-rest mux mf mz mg (remove-edge w x)) (mb-rest mux mf mz mg w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))

;; a run edit by a row function that keeps the row predicate
(a/theorem mb-run-upd [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (=> (= (mb-row mux mf mz mg r) true) (= (mb-row mux mf mz mg (f r)) true)))]
  (=> (= (mb mux mf mz mg w) true) (= (mb mux mf mz mg (run-upd w x f)) true))
  (intro h)
  (have p := (mb-rest-parts mux mf mz mg w (mb-rest-of mux mf mz mg w h)))
  (have q (= (tbl-all (mb-row mux mf mz mg) (tbl-upd run-id x f (:runs w))) true))
  (exact (tbl-all-upd RunRow run-id x f (mb-row mux mf mz mg) (mb-row mux mf mz mg)
           (fn [r :- RunRow, a1 :- (= (mb-row mux mf mz mg r) true), a2 :- (= (Nat.beq (run-id r) x) true)] (hk r a1))
           (fn [r :- RunRow, a1 :- (= (mb-row mux mf mz mg r) true), a2 :- (= (Nat.beq (run-id r) x) false)] a1)
           (:runs w) (And.right p)))
  (have r1 (= (mb-rest mux mf mz mg (run-upd w x f)) true))
  (exact (mb-rest-mk mux mf mz mg (run-upd w x f) (And.left p) q))
  (exact (mb-intro mux mf mz mg _ (inv-run-upd w x f hf (mb-sample mux mf mz mg w h)) r1)))

;; a run edit of an untracked id by a row function that keeps slice-ok
(a/theorem mb-run-upd-ne [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                          hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                          hne :- (= (untracked mux mg x) true),
                          hs :- (forall [r :- RunRow] (=> (= (slice-ok r) true) (= (slice-ok (f r)) true)))]
  (=> (= (mb mux mf mz mg w) true) (= (mb mux mf mz mg (run-upd w x f)) true))
  (intro h)
  (have p := (mb-rest-parts mux mf mz mg w (mb-rest-of mux mf mz mg w h)))
  (have hin (forall [r :- RunRow] (=> (= (mb-row mux mf mz mg r) true) (= (Nat.beq (run-id r) x) true) (= (mb-row mux mf mz mg (f r)) true))))
  (intros r a1 a2)
  (have ex (= (:id (f r)) x)) (exact (Eq.trans (hf r) (Nat.eq_of_beq_eq_true a2)))
  (have u (= (untracked mux mg (:id (f r))) true)) (rw [ex]) (exact hne)
  (simp only [mb-row Bool.and_eq_true] at a1)
  (simp only [mb-row Bool.and_eq_true])
  (exact (And.intro (hs r (And.left a1)) (mu-at-un mux mf mz mg (f r) u)))
  (have q (= (tbl-all (mb-row mux mf mz mg) (tbl-upd run-id x f (:runs w))) true))
  (exact (tbl-all-upd RunRow run-id x f (mb-row mux mf mz mg) (mb-row mux mf mz mg) hin
           (fn [r :- RunRow, a1 :- (= (mb-row mux mf mz mg r) true), a2 :- (= (Nat.beq (run-id r) x) false)] a1)
           (:runs w) (And.right p)))
  (have r1 (= (mb-rest mux mf mz mg (run-upd w x f)) true))
  (exact (mb-rest-mk mux mf mz mg (run-upd w x f) (And.left p) q))
  (exact (mb-intro mux mf mz mg _ (inv-run-upd w x f hf (mb-sample mux mf mz mg w h)) r1)))

;; a run edit of the rows with id x, all of which satisfy Q
(a/theorem mb-run-upd-q [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                         hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         Q :- (=> RunRow Bool), hq :- (= (tbl-all (same-id-then run-id x Q) (:runs w)) true),
                         hk :- (forall [r :- RunRow] (=> (= (Q r) true) (= (mb-row mux mf mz mg r) true) (= (mb-row mux mf mz mg (f r)) true)))]
  (=> (= (mb mux mf mz mg w) true) (= (mb mux mf mz mg (run-upd w x f)) true))
  (intro h)
  (have p := (mb-rest-parts mux mf mz mg w (mb-rest-of mux mf mz mg w h)))
  (have hin (forall [r :- RunRow] (=> (= (mb-row mux mf mz mg r) true) (= (same-id-then run-id x Q r) true) (= (Nat.beq (run-id r) x) true)
                                      (= (mb-row mux mf mz mg (f r)) true))))
  (intros r a1 a2 a3)
  (simp only [same-id-then a3 Bool.not_true Bool.false_or] at a2)
  (exact (hk r a2 a1))
  (have q (= (tbl-all (mb-row mux mf mz mg) (tbl-upd run-id x f (:runs w))) true))
  (exact (all-upd2 RunRow run-id x f (mb-row mux mf mz mg) (same-id-then run-id x Q) (mb-row mux mf mz mg) hin
           (fn [r :- RunRow, a1 :- (= (mb-row mux mf mz mg r) true), a2 :- (= (same-id-then run-id x Q r) true), a3 :- (= (Nat.beq (run-id r) x) false)] a1)
           (:runs w) (And.right p) hq))
  (have r1 (= (mb-rest mux mf mz mg (run-upd w x f)) true))
  (exact (mb-rest-mk mux mf mz mg (run-upd w x f) (And.left p) q))
  (exact (mb-intro mux mf mz mg _ (inv-run-upd w x f hf (mb-sample mux mf mz mg w h)) r1)))

;; a fresh run row (id next-id, which is not mux) that satisfies slice-ok
(a/theorem mb-run-ins [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, r :- RunRow, hs :- (= (slice-ok r) true)]
  (=> (= (run-id r) (:next-id w)) (= (mb mux mf mz mg w) true) (= (mb mux mf mz mg (bump (run-ins w r))) true))
  (intros hr h)
  (have p := (mb-rest-parts mux mf mz mg w (mb-rest-of mux mf mz mg w h)))
  (have hn (= (Nat.beq (:id r) mux) false))
  (have e (= (:id r) (:next-id w))) (exact hr)
  (have l := (And.left p))
  (cases hb (Nat.beq (:id r) mux))
  (case [false] (rfl))
  (case [true] (have q := (Nat.eq_of_beq_eq_true hb)) (omega))
  (have hrow (= (mb-row mux mf mz mg r) true)) (simp only [mb-row hs (mu-at-ne mux mf mz mg r hn) Bool.and_self])
  (have r0 (= (mb-rest mux mf mz mg (run-ins w r)) true))
  (have q (= (tbl-all (mb-row mux mf mz mg) (List.cons RunRow r (:runs w))) true))
  (simp only [tbl-all hrow (And.right p) Bool.and_self])
  (exact (mb-rest-mk mux mf mz mg (run-ins w r) (And.left p) q))
  (exact (mb-intro mux mf mz mg _ (inv-run-ins-fresh w r hr (mb-sample mux mf mz mg w h)) (mb-rest-bump mux mf mz mg _ r0))))

(a/theorem mb-rest-run-del [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, x :- Nat]
  (=> (= (mb-rest mux mf mz mg w) true) (= (mb-rest mux mf mz mg (run-del w x)) true))
  (intro h)
  (have p := (mb-rest-parts mux mf mz mg w h))
  (exact (mb-rest-mk mux mf mz mg (run-del w x) (And.left p)
             (tbl-all-del RunRow run-id x (mb-row mux mf mz mg) (mb-row mux mf mz mg)
               (fn [r :- RunRow, a1 :- (= (mb-row mux mf mz mg r) true), a2 :- (= (Nat.beq (run-id r) x) false)] a1)
               (:runs w) (And.right p)))))

(a/theorem mb-rest-filter [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, K :- (=> Nat Bool)]
  (=> (= (mb-rest mux mf mz mg w) true) (= (mb-rest mux mf mz mg (filter-world K w)) true))
  (intro h)
  (have p := (mb-rest-parts mux mf mz mg w h))
  (exact (mb-rest-mk mux mf mz mg (filter-world K w) (And.left p)
           (tbl-all-keep-same RunRow K run-id (mb-row mux mf mz mg) (:runs w) (And.right p)))))

;; ---- facts for the run edits that may raise the measure (they touch an alive run, or a
;; cleanup-ready one)

(a/theorem mb-row-mem [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, r :- RunRow]
  (=> (= (mb mux mf mz mg w) true) (List.Mem r (:runs w)) (= (mb-row mux mf mz mg r) true))
  (intros h hm)
  (exact (tbl-all-mem RunRow (mb-row mux mf mz mg) r (:runs w) (And.right (mb-rest-parts mux mf mz mg w (mb-rest-of mux mf mz mg w h))) hm)))
(a/theorem mb-un-alive [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, r :- RunRow]
  (=> (List.Mem r (:runs w)) (= (run-done r) false) (= (mb mux mf mz mg w) true) (= (untracked mux mg (:id r)) true))
  (intros hm hd h) (exact (mb-row-alive-un mux mf mz mg r (mb-row-mem mux mf mz mg w r h hm) hd)))
(a/theorem sok-slice-done [r :- RunRow]
  (=> (= (slice-ok r) true) (= (:slice r) true) (= (run-unwinding r) false) (= (run-done r) false))
  (intros h hs hu)
  (simp only [slice-ok hs hu Bool.not_true Bool.false_or Bool.or_false] at h)
  (cases hd (run-done r)) (case [false] (rfl)) (case [true] (simp [hd] at h)))
(a/theorem mb-un-slice [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, r :- RunRow]
  (=> (List.Mem r (:runs w)) (= (:slice r) true) (= (run-unwinding r) false) (= (mb mux mf mz mg w) true)
      (= (untracked mux mg (:id r)) true))
  (intros hm hs hu h)
  (have row := (mb-row-mem mux mf mz mg w r h hm))
  (have so (= (slice-ok r) true)) (simp only [mb-row Bool.and_eq_true] at row) (exact (And.left row))
  (exact (mb-un-alive mux mf mz mg w r hm (sok-slice-done r so hs hu) h)))
(a/theorem normal-not-done [r :- RunRow] (=> (= (run-normal r) true) (= (run-done r) false))
  (intro h) (simp only [run-normal run-alive Bool.and_eq_true] at h)
  (cases hd (run-done r)) (case [false] (rfl)) (case [true] (simp only [run-done] at hd) (simp [hd] at h)))

(a/theorem run-arm-sok [n :- Nat] (forall [r :- RunRow] (=> (= (slice-ok r) true) (= (slice-ok (run-arm n r)) true)))
  (intros r h) (exact h))
(a/theorem run-fin-push-sok [fz :- Finalizer] (forall [r :- RunRow] (=> (= (slice-ok r) true) (= (slice-ok (run-fin-push fz r)) true)))
  (intros r h) (exact h))
(a/theorem run-park-row-sok [] (forall [r :- RunRow] (=> (= (slice-ok r) true) (= (slice-ok (run-park-row r)) true)))
  (intros r h) (simp only [slice-ok run-park-row Bool.not_false Bool.true_or]))
(a/theorem run-tick-park-sok [] (forall [r :- RunRow] (=> (= (slice-ok r) true) (= (slice-ok (run-tick-park r)) true)))
  (intros r h) (simp only [slice-ok run-tick-park Bool.not_false Bool.true_or]))

;; the scheduling choice gives the slice to an alive run, `finalize` to a cleanup-ready one
(a/defn q-alive [r :- RunRow] Bool (Bool.not (run-done r)))
(a/defn q-cleanup [r :- RunRow] Bool (Bool.and (run-unwinding r) (Bool.not (fins-empty (:finalizers r)))))
(a/theorem enter-alive-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat]
  (forall [r :- RunRow] (=> (= (q-alive r) true) (= (mb-row mux mf mz mg r) true) (= (mb-row mux mf mz mg (run-enter-row r)) true)))
  (intros r hq h)
  (have hd (= (run-done r) false)) (exact (bnot-true _ hq))
  (have u := (mb-row-alive-un mux mf mz mg r h hd))
  (have so (= (slice-ok (run-enter-row r)) true)) (simp only [slice-ok run-enter-row run-done] at hd) (simp only [slice-ok run-enter-row run-done hd Bool.not_false Bool.true_or Bool.or_true])
  (simp only [mb-row so Bool.true_and]) (exact (mu-at-un mux mf mz mg (run-enter-row r) u)))
(a/theorem enter-cleanup-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat]
  (forall [r :- RunRow] (=> (= (q-cleanup r) true) (= (mb-row mux mf mz mg r) true) (= (mb-row mux mf mz mg (run-enter-row r)) true)))
  (intros r hq h)
  (simp only [q-cleanup Bool.and_eq_true] at hq)
  (have so (forall [hs :- (= (slice-ok r) true)] (= (slice-ok (run-enter-row r)) true)))
  (intro hs) (have u2 (= (run-unwinding (run-enter-row r)) true)) (exact (And.left hq)) (simp only [slice-ok u2 Bool.or_true])
  (have e (= (fins-empty (:finalizers r)) false)) (exact (bnot-true _ (And.right hq)))
  (have fl (<= (mu-f (run-enter-row r)) (mu-f r)))
  (have e1 (= (mu-f (run-enter-row r)) (mfv (:finalizers r) true))) (rfl)
  (have e2 (= (mu-f r) (mfv (:finalizers r) (:slice r)))) (rfl)
  (rw [e1 e2]) (simp only [mfv e Bool.not_false Bool.true_or]) (exact (Nat.le_refl _))
  (exact (mb-row-mono mux mf mz mg r (run-enter-row r) (rfl) so (fn [hd :- (= (run-done r) true)] hd) fl (Nat.le_refl _) h)))
(a/theorem sched-q [w :- World, r :- RunRow] (=> (= (sched-ok w r) true) (= (q-alive r) true))
  (intro h) (simp only [sched-ok Bool.and_eq_true] at h)
  (have e (= (:act r) act-active)) (exact (Nat.eq_of_beq_eq_true (And.left h)))
  (simp only [q-alive run-done e act-active act-done]))
(a/theorem cleanup-q [w :- World, r :- RunRow] (=> (= (cleanup-ready w r) true) (= (q-cleanup r) true))
  (intro h) (simp only [cleanup-ready Bool.and_eq_true] at h)
  (simp only [q-cleanup Bool.and_eq_true]) (exact (And.intro (And.left (And.right h)) (And.left (And.right (And.right h))))))
(a/theorem found-uniq [w :- World, rid :- Nat, r :- RunRow, Q :- (=> RunRow Bool)]
  (=> (= (inv-sample w) true) (= (run-find w rid) (Option.some RunRow r)) (= (Q r) true)
      (= (tbl-all (same-id-then run-id rid Q) (:runs w)) true))
  (intros h hf hq)
  (have hm := (tbl-find-mem RunRow run-id rid r (:runs w) hf))
  (have e := (tbl-find-id RunRow run-id rid r (:runs w) hf))
  (have u := (uniq-all RunRow run-id Q r (:runs w) (lit-runs-nodup w h) hm hq))
  (rw [e] at u) (exact u))

;; ===========================================================================
;; Part D. The bundle copy over the raw step and the normalization
;; ===========================================================================

(def MB (mk-bundle 'mb '[mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat] "mb-"
          {'inv-run-upd ['(fn [q :- RunRow, hq :- (= (mb-row mux mf mz mg q) true)] hq) 4]
           'inv-run-ins-fresh ['(Eq.refl true) 2]}))
;; row-function lemmas (and the alias heads the patches emit) take the bundle parameters
(def ^:private mb-fns '{run-wake run-wake-mb run-complete-row run-complete-row-mb run-cancel-row run-cancel-row-mb
                        run-unres run-unres-mb run-fin-pop run-fin-pop-mb run-fin-pop-end run-fin-pop-end-mb})
(swap! (:renames MB) merge
       '{inv-parts mb-parts inv-run-upd mb-run-upd inv-run-ins-fresh mb-run-ins
         mb-run-upd-m mb-run-upd mb-run-upd-ne-src mb-run-upd-ne}
       (into {} (map (fn [l] [l l]) (vals mb-fns))))

(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-set-pins
            inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-edge-upd inv-drop-cred inv-drop-edges
            inv-comp-del-unref inv-comp-upd inv-drop-act inv-task-upd]]
  (prim! MB o nil))
(doseq [o '[inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-comp-ins-fresh inv-act-ins-fresh inv-task-ins-fresh]]
  (prim! MB o (list 'mb-rest-bump 'mux 'mf 'mz 'mg (list (symbol (str/replace (subs (name o) 4) "-fresh" "")) 'w 'r)
                    (list 'Eq.trans '(rfl) 'R))))
(prim! MB 'inv-bump '(mb-rest-bump mux mf mz mg w R))
(prim! MB 'mark-edge-inv-sample '(Eq.trans (mb-rest-mark-edge mux mf mz mg w x) R))
(prim! MB 'unmark-edge-inv-sample '(Eq.trans (mb-rest-unmark-edge mux mf mz mg w x) R))
(prim! MB 'inv-remove-edge '(Eq.trans (mb-rest-remove-edge mux mf mz mg w x) R))
(prim! MB 'insert-edge-fresh-inv-sample '(mb-rest-bump mux mf mz mg (insert-edge w (edge-set-id (:next-id w) e)) (Eq.trans (rfl) R)))
(prim! MB 'inv-run-del '(mb-rest-run-del mux mf mz mg w x R))
(prim! MB 'inv-filter-world '(mb-rest-filter mux mf mz mg w K R))

;; the generic source patch: a run edit by a row function of `mb-fns` uses that function's lemma
(defn- mfhead [f] (if (seq? f) (first f) f))
(defn- mlemma-app [f lem] (if (seq? f) (apply list lem (rest f)) lem))
(defn mb-patch [form]
  (->> (#'spindel.v2.idle/fix-f form)
       (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (contains? mb-fns (mfhead (nth y 3 nil)))))
                    (fn [[_ w x f hid & more]] (apply list 'mb-run-upd-m w x f hid (mlemma-app f (mb-fns (mfhead f))) more)))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! MB n mb-patch))

;; add a binder to a source theorem and an argument to one call in its proof
(defn- add-hyp [binder call-head pos arg]
  (fn [[hd nm binders & more]]
    (mb-patch (apply list hd nm (into binders binder)
                     (subst-forms (fn [y] (and (seq? y) (= call-head (first y))))
                                  (fn [y] (let [v (vec y)] (apply list (concat (subvec v 0 (inc pos)) [arg] (subvec v (inc pos))))))
                                  more)))))

;; finally-enter: a normal run
(override! MB 't-finally-enter-inv '[]
  '(a/theorem t-finally-enter-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, st :- Nat]
     (=> (= (mb mux mf mz mg w) true) (= (mb mux mf mz mg (:world (t-finally-enter w st))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t-finally-enter ht refuse]) (exact h)
     (cases hg (run-normal r))
     (simp only [t-finally-enter ht hg refuse]) (exact h)
     (simp only [t-finally-enter ht hg accept])
     (exact (mb-run-upd-ne mux mf mz mg w (:id r) (run-fin-push (Finalizer.mk 0 (:effect-index r) (List.nil Nat))) (run-fin-push-id _)
              (mb-un-alive mux mf mz mg w r (And.left (tok-facts w st r ht)) (normal-not-done r hg) h)
              (run-fin-push-sok (Finalizer.mk 0 (:effect-index r) (List.nil Nat))) h))))

;; T6 parks its (normal) token run; take parks it as well
(override! MB 'inv-park-if '[]
  '(a/theorem mb-park-if [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, a :- Nat, rid :- Nat,
                          hne :- (= (untracked mux mg rid) true)]
     (=> (= (mb mux mf mz mg w) true) (= (mb mux mf mz mg (park-if w a rid)) true))
     (intro h)
     (cases ha (act-has w a))
     (simp only [park-if ha]) (exact h)
     (simp only [park-if ha]) (exact (mb-run-upd-ne mux mf mz mg w rid run-park-row run-park-row-id hne run-park-row-sok h))))
(patch! MB 'inv-await-post (add-hyp '[hne :- (= (untracked mux mg rid) true)] 'inv-park-if 3 'hne))
(patch! MB 'inv-await-raw (add-hyp '[hne :- (= (untracked mux mg (:id r)) true)] 'inv-await-post 4 'hne))
(override! MB 't6-inv '[inv-await-raw]
  '(a/theorem t6-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat,
                     fresh :- Nat, mine :- (List Nat)]
     (=> (= (mb mux mf mz mg w) true) (= (mb mux mf mz mg (:world (t6-await w st ds mode k fresh mine))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t6-await ht refuse]) (exact h)
     (cases hg (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
     (simp only [t6-await ht hg refuse]) (exact h)
     (simp only [t6-await ht hg accept])
     (have hn (= (run-normal r) true)) (simp only [await-ok Bool.and_eq_true] at hg) (exact (And.left (And.right (And.left hg))))
     (exact (mb-await-raw mux mf mz mg w r ds mode k mine
              (mb-un-alive mux mf mz mg w r (And.left (tok-facts w st r ht)) (normal-not-done r hn) h) h))))
(patch! MB 'inv-take-park
  (fn [[hd nm binders & more]]
    (apply list hd nm (into binders '[hne :- (= (untracked mux mg (:id r)) true)])
           (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y))))
                        (fn [[_ w x f hid h]] (list 'mb-run-upd-ne-src w x f hid 'hne 'run-tick-park-sok h))
                        more))))
(override! MB 't-take-inv '[inv-take-park inv-take-now]
  '(a/theorem t-take-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
     (=> (= (mb mux mf mz mg w) true) (= (mb mux mf mz mg (:world (t-take w st x k fresh))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t-take ht refuse]) (exact h)
     (cases hs (source-find w x)) (case' [some s]) (case' [none])
     (simp only [t-take ht hs refuse]) (exact h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (takeable s))))
     (simp only [t-take ht hs hg refuse]) (exact h)
     (cases hv (take-ready s))
     (simp only [t-take ht hs hg hv accept])
     (have hn (= (run-normal r) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.left (And.right hg)))
     (exact (mb-take-park mux mf mz mg w r x k (mb-un-alive mux mf mz mg w r (And.left (tok-facts w st r ht)) (normal-not-done r hn) h) h))
     (simp only [t-take ht hs hg hv accept]) (exact (mb-take-now mux mf mz mg w r x h))))

;; T17 arm (Z#55): the resource on the (normal, untracked) token run, then its park (take-park)
(patch! MB 'raw0-inv (fn [form] (mb-patch (subst-forms #(= % '(t17-inv w _ _ _ _ h)) (fn [_] '(t17-inv w _ _ _ _ hc h)) form))))
(override! MB 'inv-arm-park '[inv-take-park inv-resource-ins-fresh]
  '(a/theorem mb-arm-park [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, r :- RunRow, kind :- Nat, k :- Nat,
                           hne :- (= (untracked mux mg (:id r)) true)]
     (=> (= (mb mux mf mz mg w) true) (= (mb mux mf mz mg (arm-park w r kind k)) true))
     (intro h)
     (have h1 (= (mb mux mf mz mg (arm-raw w r kind)) true))
     (simp only [arm-raw])
     (exact (mb-run-upd-ne mux mf mz mg _ (:id r) (run-arm (:next-id w)) (run-arm-run-id _) hne (run-arm-sok (:next-id w))
              (mb-resource-ins-fresh mux mf mz mg w (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed) (rfl) h)))
     (simp only [arm-park])
     (exact (mb-take-park mux mf mz mg _ (run-arm (:next-id w) r) (:next-id w) k hne h1))))
(override! MB 't17-inv '[inv-arm-park]
  '(a/theorem t17-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
     (=> (= (in-cleanup w st) false) (= (mb mux mf mz mg w) true) (= (mb mux mf mz mg (:world (t17-arm w st kind k fresh))) true))
     (intros hc h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t17-arm ht refuse]) (exact h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind))))
     (simp only [t17-arm ht hg refuse]) (exact h)
     (have hn (= (run-normal r) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.left (And.right hg)))
     (simp only [t17-arm ht hg accept])
     (exact (mb-arm-park mux mf mz mg w r kind k (mb-un-alive mux mf mz mg w r (And.left (tok-facts w st r ht)) (normal-not-done r hn) h) h))))

;; the scheduling choice (an alive run) and finalize (a cleanup-ready run) give the slice
(override! MB 'sched-inv '[]
  '(a/theorem sched-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, rid :- Nat]
     (=> (= (mb mux mf mz mg w) true) (= (mb mux mf mz mg (:world (t-schedule w rid))) true))
     (intro h)
     (cases hf (run-find w rid)) (case' [some r]) (case' [none])
     (simp only [t-schedule hf refuse]) (exact h)
     (cases hg (sched-ok w r))
     (simp only [t-schedule hf hg refuse]) (exact h)
     (simp only [t-schedule hf hg accept])
     (exact (mb-run-upd-q mux mf mz mg w rid run-enter-row run-enter-row-id q-alive
              (found-uniq w rid r q-alive (mb-sample mux mf mz mg w h) hf (sched-q w r hg)) (enter-alive-mb mux mf mz mg) h))))
(override! MB 't-finalize-inv '[]
  '(a/theorem t-finalize-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, rid :- Nat]
     (=> (= (mb mux mf mz mg w) true) (= (mb mux mf mz mg (:world (t-finalize w rid))) true))
     (intro h)
     (cases hf (run-find w rid)) (case' [some r]) (case' [none])
     (simp only [t-finalize hf refuse]) (exact h)
     (cases hg (cleanup-ready w r))
     (simp only [t-finalize hf hg refuse]) (exact h)
     (simp only [t-finalize hf hg accept])
     (exact (mb-run-upd-q mux mf mz mg w rid run-enter-row run-enter-row-id q-cleanup
              (found-uniq w rid r q-cleanup (mb-sample mux mf mz mg w h) hf (cleanup-q w r hg)) (enter-cleanup-mb mux mf mz mg) h))))

(lcopy! MB 'raw-inv)
(lcopy! MB 'inv-normalize)

;; ---- Rule R and the step

(a/theorem mb-rule-r-round [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World]
  (=> (= (mb mux mf mz mg w) true) (= (filter-safe (normalize w)) true) (= (mb mux mf mz mg (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (mb-filter-world mux mf mz mg _ (keep-fn (normalize w)) (mb-normalize mux mf mz mg w h) hf)))

(a/theorem mb-rr-loop [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (mb mux mf mz mg w0) true) (= (rr-safe fuel w0) true) (= (mb mux mf mz mg (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (mb-rule-r-round mux mf mz mg w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (mb-rule-r-round mux mf mz mg w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))

(a/theorem mb-rule-r [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World]
  (=> (= (mb mux mf mz mg w) true) (= (rule-r-safe w) true) (= (mb mux mf mz mg (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (mb-rr-loop mux mf mz mg (rr-fuel w) w h hs)))

(a/theorem step-mb [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, it :- Item]
  (=> (= (mb mux mf mz mg w) true) (= (rule-r-safe (:world (raw w it))) true) (= (mb mux mf mz mg (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (mb-rule-r mux mf mz mg (:world (raw w it)) (raw-mb mux mf mz mg w it h) hs))))

;; Theorem: the bundle (in each mode) is preserved by every step
(a/theorem step-mb-total [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, it :- Item]
  (=> (= (p3b w) true) (= (mb mux mf mz mg w) true) (= (mb mux mf mz mg (:world (world-step w it))) true))
  (intros h hb) (exact (step-mb mux mf mz mg w it hb (step-rule-r-safe w it h))))

;; the bundle after an accepted raw0 outcome carries over to the step's world (the loser cancel,
;; then Rule R)
(a/theorem mb-step-of-raw0 [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, w :- World, it :- Item]
  (=> (= (host-item it) false) (= (p3b w) true) (= (:accepted (raw0 w it)) true) (= (mb mux mf mz mg (:world (raw0 w it))) true)
      (= (mb mux mf mz mg (:world (world-step w it))) true))
  (intros hh h ha hb)
  (have eg := (raw0g-of w it hh))
  (have a2 (= (:accepted (raw w it)) true)) (simp only [raw post eg ha accept])
  (have e1 (= (:world (raw w it)) (cancel-losers w (:world (raw0 w it))))) (simp only [raw post eg ha accept])
  (have e2 := (step-accepted w it a2))
  (rw [e2])
  (have hr (= (mb mux mf mz mg (:world (raw w it))) true)) (rw [e1]) (exact (mb-cancel-losers mux mf mz mg w _ hb))
  (exact (mb-rule-r mux mf mz mg _ hr (step-rule-r-safe w it h))))

(a/theorem sok-empty [] (= (sok empty-world) true) (rfl))

;; Theorem: slice-ok for every run is invariant (a completed run never holds the slice)
(a/theorem step-sok [w :- World, it :- Item]
  (=> (= (p3b w) true) (= (sok w) true) (= (sok (:world (world-step w it))) true))
  (intros h hs) (exact (step-mb-total 0 0 0 2 w it h hs)))

;; ===========================================================================
;; Part E. L2: the measure lemmas
;; ===========================================================================

(a/defn mu-bound [mf :- Nat, mz :- Nat, r :- RunRow] Bool
  (Bool.and (run-done r) (Bool.and (Nat.ble (mu-f r) mf) (Nat.ble (mu-z r) mz))))

(a/theorem mb-row-track [x :- Nat, mf :- Nat, mz :- Nat, q :- RunRow]
  (=> (= (mb-row x mf mz 0 q) true) (= (:id q) x)
      (And (= (run-done q) true) (And (<= (mu-f q) mf) (<= (mu-z q) mz))))
  (intros h e)
  (have hx (= (Nat.beq (:id q) x) true)) (rw [e]) (exact (Nat.beq_refl x))
  (simp [mb-row mu-at hx] at h)
  (exact (And.right h)))

(a/theorem mb-row-gone [x :- Nat, mf :- Nat, mz :- Nat, q :- RunRow]
  (=> (= (mb-row x mf mz 1 q) true) (= (:id q) x) False)
  (intros h e)
  (have hx (= (Nat.beq (:id q) x) true)) (rw [e]) (exact (Nat.beq_refl x))
  (simp [mb-row mu-at hx] at h))

(a/theorem sok-row [w :- World, q :- RunRow] (=> (= (sok w) true) (List.Mem q (:runs w)) (= (slice-ok q) true))
  (intros h hm)
  (have r := (mb-row-mem 0 0 0 2 w q h hm))
  (simp only [mb-row Bool.and_eq_true] at r) (exact (And.left r)))

(a/theorem row-snap [x :- Nat, mf :- Nat, mz :- Nat, q :- RunRow]
  (=> (= (slice-ok q) true) (= (same-id-then run-id x (mu-bound mf mz) q) true) (= (mb-row x mf mz 0 q) true))
  (intros hs hq)
  (cases hx (Nat.beq (:id q) x))
  (case [false] (simp only [mb-row hs (mu-at-ne x mf mz 0 q hx) Bool.and_self]))
  (case [true]
    (have hx2 (= (Nat.beq (run-id q) x) true)) (exact hx)
    (simp only [same-id-then hx2 Bool.not_true Bool.false_or mu-bound] at hq)
    (simp only [mb-row mu-at hs hx hq Bool.not_true Bool.false_or Nat.beq_refl Bool.true_and Bool.or_true])))

;; a done run's current measure is a bound for the bundle in mode 0
(a/theorem mb-row-sok [mux :- Nat, mf :- Nat, mz :- Nat, mg :- Nat, q :- RunRow]
  (=> (= (mb-row mux mf mz mg q) true) (= (slice-ok q) true))
  (intro h) (simp only [mb-row Bool.and_eq_true] at h) (exact (And.left h)))

(a/theorem mb-of-done [w :- World, r :- RunRow]
  (=> (= (sok w) true) (List.Mem r (:runs w)) (= (run-done r) true) (= (mb (:id r) (mu-f r) (mu-z r) 0 w) true))
  (intros h hm hd)
  (have hs := (mb-sample 0 0 0 2 w h))
  (have hb (= (mu-bound (mu-f r) (mu-z r) r) true)) (simp [mu-bound hd])
  (have u (= (tbl-all (same-id-then run-id (:id r) (mu-bound (mu-f r) (mu-z r))) (:runs w)) true))
  (exact (uniq-all RunRow run-id (mu-bound (mu-f r) (mu-z r)) r (:runs w) (lit-runs-nodup w hs) hm hb))
  (have so (= (tbl-all (mb-row 0 0 0 2) (:runs w)) true)) (exact (And.right (mb-rest-parts 0 0 0 2 w (mb-rest-of 0 0 0 2 w h))))
  (have step (forall [q :- RunRow] (=> (= (mb-row 0 0 0 2 q) true) (= (same-id-then run-id (:id r) (mu-bound (mu-f r) (mu-z r)) q) true)
                                       (= (mb-row (:id r) (mu-f r) (mu-z r) 0 q) true))))
  (intros q a1 a2) (exact (row-snap (:id r) (mu-f r) (mu-z r) q (mb-row-sok 0 0 0 2 q a1) a2))
  (have rows (= (tbl-all (mb-row (:id r) (mu-f r) (mu-z r) 0) (:runs w)) true))
  (exact (tbl-all-mono2 RunRow (mb-row 0 0 0 2) (same-id-then run-id (:id r) (mu-bound (mu-f r) (mu-z r))) (mb-row (:id r) (mu-f r) (mu-z r) 0)
           step (:runs w) so u))
  (exact (mb-intro (:id r) (mu-f r) (mu-z r) 0 w hs (mb-rest-mk (:id r) (mu-f r) (mu-z r) 0 w (run-below w r hs hm) rows))))

;; Theorem (L2 b): no step increases the measure of a run that is done (cancelled or completed,
;; not retired): afterwards every row with its id is done, with mu-f and mu-z at most as before
(a/theorem step-mu-le [w :- World, it :- Item, r :- RunRow, r2 :- RunRow]
  (=> (= (p3b w) true) (= (sok w) true) (List.Mem r (:runs w)) (= (run-done r) true)
      (List.Mem r2 (:runs (:world (world-step w it)))) (= (:id r2) (:id r))
      (And (= (run-done r2) true) (And (<= (mu-f r2) (mu-f r)) (<= (mu-z r2) (mu-z r)))))
  (intros h hs hm hd hm2 he)
  (have b := (step-mb-total (:id r) (mu-f r) (mu-z r) 0 w it h (mb-of-done w r hs hm hd)))
  (exact (mb-row-track (:id r) (mu-f r) (mu-z r) r2 (mb-row-mem (:id r) (mu-f r) (mu-z r) 0 _ r2 b hm2) he)))

;; ---- (a) and (c): the progress events

;; a row within the bound
(a/theorem row-bound [x :- Nat, mf :- Nat, mz :- Nat, q :- RunRow]
  (=> (= (slice-ok q) true) (= (run-done q) true) (<= (mu-f q) mf) (<= (mu-z q) mz) (= (mb-row x mf mz 0 q) true))
  (intros hs hd hf hz)
  (have b1 (= (Nat.ble (mu-f q) mf) true)) (simp only [Nat.ble_eq]) (exact hf)
  (have b2 (= (Nat.ble (mu-z q) mz) true)) (simp only [Nat.ble_eq]) (exact hz)
  (simp only [mb-row mu-at hs hd b1 b2 Nat.beq_refl Bool.and_self Bool.or_true]))

;; a run edit of the rows with id x (all of which satisfy Q) that leaves them within mf/mz
(a/theorem mb-upd-tight [x :- Nat, mf :- Nat, mz :- Nat, w :- World, g :- (=> RunRow RunRow),
                         hg :- (forall [q :- RunRow] (= (run-id (g q)) (run-id q))),
                         Q :- (=> RunRow Bool),
                         hk :- (forall [q :- RunRow] (=> (= (Q q) true) (= (slice-ok q) true) (= (mb-row x mf mz 0 (g q)) true)))]
  (=> (= (sok w) true) (< x (:next-id w)) (= (tbl-all (same-id-then run-id x Q) (:runs w)) true)
      (= (mb x mf mz 0 (run-upd w x g)) true))
  (intros h hx hq)
  (have hs := (mb-sample 0 0 0 2 w h))
  (have so (= (tbl-all (mb-row 0 0 0 2) (:runs w)) true)) (exact (And.right (mb-rest-parts 0 0 0 2 w (mb-rest-of 0 0 0 2 w h))))
  (have hin (forall [q :- RunRow] (=> (= (mb-row 0 0 0 2 q) true) (= (same-id-then run-id x Q q) true) (= (Nat.beq (run-id q) x) true)
                                      (= (mb-row x mf mz 0 (g q)) true))))
  (intros q a1 a2 a3) (simp only [same-id-then a3 Bool.not_true Bool.false_or] at a2) (exact (hk q a2 (mb-row-sok 0 0 0 2 q a1)))
  (have hout (forall [q :- RunRow] (=> (= (mb-row 0 0 0 2 q) true) (= (same-id-then run-id x Q q) true) (= (Nat.beq (run-id q) x) false)
                                       (= (mb-row x mf mz 0 q) true))))
  (intros q a1 a2 a3) (simp only [mb-row (mb-row-sok 0 0 0 2 q a1) (mu-at-ne x mf mz 0 q a3) Bool.and_self])
  (have rows := (all-upd2 RunRow run-id x g (mb-row 0 0 0 2) (same-id-then run-id x Q) (mb-row x mf mz 0) hin hout (:runs w) so hq))
  (exact (mb-intro x mf mz 0 _ (inv-run-upd w x g hg hs) (mb-rest-mk x mf mz 0 (run-upd w x g) hx rows))))

(a/theorem sub-one-lt [n :- Nat, a :- Nat] (=> (= (+ a 1) n) (< (- n 1) n)) (intro h) (omega))

;; finalizer exit: the head region pops while the cleanup slice is held
(a/theorem mfv-pop-held [fs :- (List Finalizer)]
  (=> (= (fins-empty fs) false) (= (+ (mfv (fins-tail fs) true) 1) (mfv fs true)))
  (intro he) (cases fs)
  (case [nil] (simp [fins-empty] at he))
  (case [cons fh ft] (simp only [mfv fins-tail fins-len fe-cons Bool.not_false Bool.or_true Bool.true_or])))
(a/theorem pop-held [q :- RunRow]
  (=> (= (:slice q) true) (= (fins-empty (:finalizers q)) false) (= (+ (mu-f (run-fin-pop q)) 1) (mu-f q)))
  (intros hs he)
  (have e1 (= (mu-f (run-fin-pop q)) (mfv (fins-tail (:finalizers q)) (:slice q)))) (rfl)
  (have e2 (= (mu-f q) (mfv (:finalizers q) (:slice q)))) (rfl)
  (rw [e1 e2 hs]) (exact (mfv-pop-held (:finalizers q) he)))

(a/defn q-fx [mf :- Nat, mz :- Nat, q :- RunRow] Bool
  (Bool.and (run-done q) (Bool.and (:slice q) (Bool.and (Bool.not (fins-empty (:finalizers q)))
   (Bool.and (Nat.beq (mu-f q) mf) (Nat.beq (mu-z q) mz))))))

(a/theorem fx-row [x :- Nat, mf :- Nat, mz :- Nat]
  (forall [q :- RunRow] (=> (= (q-fx mf mz q) true) (= (slice-ok q) true) (= (mb-row x (- mf 1) mz 0 (run-fin-pop q)) true)))
  (intros q hq hs)
  (simp only [q-fx Bool.and_eq_true] at hq)
  (have p := (pop-held q (And.left (And.right hq)) (bnot-true _ (And.left (And.right (And.right hq))))))
  (have e1 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right (And.right hq))))))
  (have e2 := (Nat.eq_of_beq_eq_true (And.right (And.right (And.right (And.right hq))))))
  (have l1 (<= (mu-f (run-fin-pop q)) (- mf 1))) (omega)
  (have l2 (<= (mu-z (run-fin-pop q)) mz)) (exact (Nat.le_of_eq e2))
  (exact (row-bound x (- mf 1) mz (run-fin-pop q) hs (And.left hq) l1 l2)))

;; Theorem (L2 a): an accepted `finally-exit` of a done run (its cleanup slice runs the head
;; finalizer) drops mu-f by one; mu-z does not grow
(a/theorem finally-exit-dec [w :- World, st :- Nat, r :- RunRow, r2 :- RunRow]
  (=> (= (p3b w) true) (= (sok w) true) (= (tok-run w st) (Option.some RunRow r)) (= (run-done r) true)
      (= (:accepted (raw0 w (Item.finally-exit st))) true)
      (List.Mem r2 (:runs (:world (world-step w (Item.finally-exit st))))) (= (:id r2) (:id r))
      (And (< (mu-f r2) (mu-f r)) (<= (mu-z r2) (mu-z r))))
  (intros h hs ht hd ha hm2 he)
  (have tf := (tok-facts w st r ht))
  (have hsam := (mb-sample 0 0 0 2 w hs))
  (cases hfe (fins-empty (:finalizers r)))
  (case [true] (simp [raw0 t-finally-exit ht hfe refuse] at ha))
  (case [false]
    (have e0 (= (:world (raw0 w (Item.finally-exit st))) (run-upd w (:id r) run-fin-pop)))
    (simp only [raw0 t-finally-exit ht hfe accept])
    (have hq (= (q-fx (mu-f r) (mu-z r) r) true))
    (simp [q-fx hd (And.right tf) hfe])
    (have u (= (tbl-all (same-id-then run-id (:id r) (q-fx (mu-f r) (mu-z r))) (:runs w)) true))
    (exact (uniq-all RunRow run-id (q-fx (mu-f r) (mu-z r)) r (:runs w) (lit-runs-nodup w hsam) (And.left tf) hq))
    (have b0 := (mb-upd-tight (:id r) (- (mu-f r) 1) (mu-z r) w run-fin-pop run-fin-pop-id (q-fx (mu-f r) (mu-z r))
                  (fx-row (:id r) (mu-f r) (mu-z r)) hs (run-below w r hsam (And.left tf)) u))
    (have b1 (= (mb (:id r) (- (mu-f r) 1) (mu-z r) 0 (:world (raw0 w (Item.finally-exit st)))) true)) (rw [e0]) (exact b0)
    (have b2 := (mb-step-of-raw0 (:id r) (- (mu-f r) 1) (mu-z r) 0 w (Item.finally-exit st) (rfl) h ha b1))
    (have t := (mb-row-track (:id r) (- (mu-f r) 1) (mu-z r) r2 (mb-row-mem (:id r) (- (mu-f r) 1) (mu-z r) 0 _ r2 b2 hm2) he))
    (have p := (pop-held r (And.right tf) hfe))
    (exact (And.intro (Nat.lt_of_le_of_lt (And.left (And.right t)) (sub-one-lt (mu-f r) (mu-f (run-fin-pop r)) p))
                      (And.right (And.right t))))))

;; ---- T13 on a run whose measure is (0, 0): afterwards no row has its id (bundle mode 1)

(a/theorem retirable-of-mu0 [q :- RunRow]
  (=> (= (run-done q) true) (<= (mu-f q) 0) (<= (mu-z q) 0) (= (retirable q) true))
  (intros hd hf hz)
  (have e (= (mu-f q) (mfv (:finalizers q) (:slice q)))) (rfl)
  (have a (= (:act q) act-done)) (exact (Nat.eq_of_beq_eq_true hd))
  (cases hl (:finalizers q))
  (case [cons fh ft] (rw [e hl] at hf) (simp only [mfv fins-len] at hf) (omega))
  (case [nil]
    (cases hs (:slice q))
    (case [true] (rw [e hl hs] at hf) (simp only [mfv fins-len fe-nil Bool.not_true Bool.false_or] at hf) (simp at hf))
    (case [false]
      (cases hr (:resources q))
      (case [cons zh zt] (simp only [mu-z hr nat-len] at hz) (omega))
      (case [nil] (simp only [retirable a hs hl hr fins-empty nats-empty act-done Nat.beq_refl Bool.not_false Bool.and_self])))))

(a/defn run-not-id [x :- Nat, r :- RunRow] Bool (Bool.not (Nat.beq (:id r) x)))
(a/theorem rows-none [x :- Nat, rs :- (List RunRow)]
  (=> (= (tbl-find run-id x rs) (Option.none RunRow)) (= (tbl-all (run-not-id x) rs) true))
  (induction rs)
  (case [nil] (intro h) (simp [tbl-all]))
  (case [cons q t ih]
    (intro h)
    (cases hb (Nat.beq (run-id q) x))
    (case [true] (simp [tbl-find hb] at h))
    (case [false]
      (simp only [tbl-find hb] at h)
      (have hb2 (= (Nat.beq (:id q) x) false)) (exact hb)
      (simp only [tbl-all run-not-id hb2 Bool.not_false (ih h) Bool.and_self]))))

(a/theorem row-un-gone [x :- Nat, q :- RunRow]
  (=> (= (slice-ok q) true) (= (Nat.beq (:id q) x) false) (= (mb-row x 0 0 1 q) true))
  (intros hs hn) (simp only [mb-row hs (mu-at-ne x 0 0 1 q hn) Bool.and_self]))

;; from mode 0 with bound (0, 0) to mode 1 (gone) when no row has the id
(a/theorem mb-gone-of [x :- Nat, w :- World]
  (=> (= (mb x 0 0 0 w) true) (= (tbl-all (run-not-id x) (:runs w)) true) (= (mb x 0 0 1 w) true))
  (intros h hn)
  (have p := (mb-rest-parts x 0 0 0 w (mb-rest-of x 0 0 0 w h)))
  (have rows (= (tbl-all (mb-row x 0 0 1) (:runs w)) true))
  (exact (tbl-all-mono2 RunRow (mb-row x 0 0 0) (run-not-id x) (mb-row x 0 0 1)
           (fn [q :- RunRow, a1 :- (= (mb-row x 0 0 0 q) true), a2 :- (= (run-not-id x q) true)]
             (row-un-gone x q (mb-row-sok x 0 0 0 q a1) (bnot-true _ a2)))
           (:runs w) (And.right p) hn))
  (exact (mb-intro x 0 0 1 w (mb-sample x 0 0 0 w h) (mb-rest-mk x 0 0 1 w (And.left p) rows))))

(a/theorem mb-del-gone [x :- Nat, w :- World]
  (=> (= (mb x 0 0 0 w) true) (= (mb x 0 0 1 (run-del w x)) true))
  (intro h)
  (have p := (mb-rest-parts x 0 0 0 w (mb-rest-of x 0 0 0 w h)))
  (have rows (= (tbl-all (mb-row x 0 0 1) (tbl-del run-id x (:runs w))) true))
  (exact (tbl-all-del RunRow run-id x (mb-row x 0 0 0) (mb-row x 0 0 1)
           (fn [q :- RunRow, a1 :- (= (mb-row x 0 0 0 q) true), a2 :- (= (Nat.beq (run-id q) x) false)]
             (row-un-gone x q (mb-row-sok x 0 0 0 q a1) a2))
           (:runs w) (And.right p)))
  (exact (mb-intro x 0 0 1 _ (inv-run-del w x (mb-sample x 0 0 0 w h)) (mb-rest-mk x 0 0 1 (run-del w x) (And.left p) rows))))

(a/theorem mb-retire-local-gone [x :- Nat, w :- World, r :- RunRow]
  (=> (= (mb x 0 0 0 w) true) (= (run-id r) x) (= (mb x 0 0 1 (retire-local w r)) true))
  (intros h e)
  (rw [← e] at h) (rw [← e])
  (simp only [retire-local retire-with])
  (exact (mb-remove-if-empty (run-id r) 0 0 1 _ (scope-subtree w (:scope r))
           (mb-cleanup-del (run-id r) 0 0 1 _ (:id r)
             (mb-del-gone (run-id r) _
               (mb-close-local (run-id r) 0 0 0 _ (scope-subtree w (:scope r)) (mb-clear-comp-run (run-id r) 0 0 0 w r h)))))))

(a/theorem mb-job-retire-gone [x :- Nat, w :- World]
  (=> (= (mb x 0 0 0 w) true) (= (mb x 0 0 1 (job-apply w (Job.jretire x))) true))
  (intro h)
  (cases hf (run-find w x)) (case' [some r]) (case' [none])
  (simp only [job-apply hf]) (exact (mb-gone-of x w h (rows-none x (:runs w) hf)))
  (have e := (tbl-find-id RunRow run-id x r (:runs w) hf))
  (have hm := (tbl-find-mem RunRow run-id x r (:runs w) hf))
  (have t := (mb-row-track x 0 0 r (mb-row-mem x 0 0 0 w r h hm) e))
  (have ret := (retirable-of-mu0 r (And.left t) (And.left (And.right t)) (And.right (And.right t))))
  (simp only [job-apply hf ret])
  (exact (mb-retire-local-gone x w r h e)))

;; T13 on x as a one-job cascade (retire-full) when x's rows have measure (0, 0)
(a/theorem mb-retire-gone [x :- Nat, w :- World]
  (=> (= (mb x 0 0 0 w) true) (= (mb x 0 0 1 (run-cascade w (List.cons Job (Job.jretire x) (List.nil Job)))) true))
  (intro h)
  (have e (= (run-cascade w (List.cons Job (Job.jretire x) (List.nil Job)))
             (:world (cascade (List.append Nat (rep-list (job-zeros (List.cons Job (Job.jretire x) (List.nil Job))) (List.cons Nat 0 (tbl-ids run-id (:runs w))))
                                (rep-list (tbl-ids run-id (:runs w))
                                  (List.cons Nat 0 (List.cons Nat 0 (List.append Nat (tbl-ids run-id (:runs w)) (tbl-ids run-id (:runs w)))))))
                              (job-apply w (Job.jretire x))
                              (List.append Job (List.nil Job) (job-next w (Job.jretire x)))))))
  (rfl)
  (rw [e])
  (exact (mb-cascade x 0 0 1 _ (job-apply w (Job.jretire x)) _ (mb-job-retire-gone x w h))))

;; ---- slice-exit (Z#35/Z#49): the cleanup slice returns, with no region left

(a/theorem fe-true-nil [fs :- (List Finalizer)] (=> (= (fins-empty fs) true) (= fs (List.nil Finalizer)))
  (intro h) (cases fs) (case [nil] (rfl)) (case [cons fh ft] (simp [fins-empty] at h)))
(a/theorem mu-f-pos-slice [q :- RunRow] (=> (= (:slice q) true) (< 0 (mu-f q)))
  (intro hs)
  (have e (= (mu-f q) (mfv (:finalizers q) (:slice q)))) (rfl)
  (rw [e hs]) (simp only [mfv Bool.or_true]) (omega))

(a/defn q-sx [mz :- Nat, q :- RunRow] Bool (Bool.and (exit-ready q) (Nat.beq (mu-z q) mz)))
(a/theorem sx-row [x :- Nat, mz :- Nat]
  (forall [q :- RunRow] (=> (= (q-sx mz q) true) (= (slice-ok q) true) (= (mb-row x 0 mz 0 (run-fin-pop-end q)) true)))
  (intros q hq hs)
  (simp only [q-sx exit-ready Bool.and_eq_true] at hq)
  (have hn := (fe-true-nil (:finalizers q) (And.right (And.right (And.left hq)))))
  (have so (= (slice-ok (run-fin-pop-end q)) true)) (simp only [slice-ok run-fin-pop-end Bool.not_false Bool.true_or])
  (have hd (= (run-done (run-fin-pop-end q)) true)) (exact (And.left (And.left hq)))
  (have l1 (<= (mu-f (run-fin-pop-end q)) 0))
  (have e1 (= (mu-f (run-fin-pop-end q)) (mfv (fins-tail (:finalizers q)) false))) (rfl)
  (rw [e1 hn]) (simp only [mfv fins-tail fins-len fe-nil Bool.not_true Bool.false_or]) (exact (Nat.le_refl 0))
  (have l2 (<= (mu-z (run-fin-pop-end q)) mz)) (exact (Nat.le_of_eq (Nat.eq_of_beq_eq_true (And.right hq))))
  (exact (row-bound x 0 mz (run-fin-pop-end q) so hd l1 l2)))

;; Theorem (L2 a): an accepted `slice-exit` (a done run's cleanup slice returns with no region
;; open) drops mu-f to 0 (from 1); mu-z does not grow
(a/theorem slice-exit-dec [w :- World, rid :- Nat, r :- RunRow, r2 :- RunRow]
  (=> (= (p3b w) true) (= (sok w) true) (= (run-find w rid) (Option.some RunRow r))
      (= (:accepted (raw0 w (Item.slice-exit rid))) true)
      (List.Mem r2 (:runs (:world (world-step w (Item.slice-exit rid))))) (= (:id r2) rid)
      (And (< (mu-f r2) (mu-f r)) (<= (mu-z r2) (mu-z r))))
  (intros h hs hf ha hm2 he)
  (have hsam := (mb-sample 0 0 0 2 w hs))
  (have hm := (tbl-find-mem RunRow run-id rid r (:runs w) hf))
  (have ei := (tbl-find-id RunRow run-id rid r (:runs w) hf))
  (cases hg (exit-ready r))
  (case [false] (simp [raw0 t-slice-exit hf hg refuse] at ha))
  (case [true]
    (have e0 (= (:world (raw0 w (Item.slice-exit rid)))
                (run-cascade (run-upd w rid run-fin-pop-end) (List.cons Job (Job.jretire rid) (List.nil Job)))))
    (simp only [raw0 t-slice-exit hf hg accept retire-full])
    (have hq (= (q-sx (mu-z r) r) true)) (simp only [q-sx hg Nat.beq_refl Bool.and_self])
    (have u := (uniq-all RunRow run-id (q-sx (mu-z r)) r (:runs w) (lit-runs-nodup w hsam) hm hq))
    (rw [ei] at u)
    (have lt (< rid (:next-id w))) (rw [← ei]) (exact (run-below w r hsam hm))
    (have b0 := (mb-upd-tight rid 0 (mu-z r) w run-fin-pop-end run-fin-pop-end-id (q-sx (mu-z r)) (sx-row rid (mu-z r)) hs lt u))
    (have b1 (= (mb rid 0 (mu-z r) 0 (:world (raw0 w (Item.slice-exit rid)))) true))
    (rw [e0]) (exact (mb-run-cascade rid 0 (mu-z r) 0 _ _ b0))
    (have b2 := (mb-step-of-raw0 rid 0 (mu-z r) 0 w (Item.slice-exit rid) (rfl) h ha b1))
    (have t := (mb-row-track rid 0 (mu-z r) r2 (mb-row-mem rid 0 (mu-z r) 0 _ r2 b2 hm2) he))
    (simp only [exit-ready Bool.and_eq_true] at hg)
    (have p := (mu-f-pos-slice r (And.left (And.right hg))))
    (exact (And.intro (Nat.lt_of_le_of_lt (And.left (And.right t)) p) (And.right (And.right t))))))

;; Theorem (L2 c): when the slice-exit leaves the run with no resource (measure (0, 0)), the
;; run is retired in the same step (T13): no row with its id remains
(a/theorem slice-exit-retires [w :- World, rid :- Nat, r :- RunRow, r2 :- RunRow]
  (=> (= (p3b w) true) (= (sok w) true) (= (run-find w rid) (Option.some RunRow r)) (= (mu-z r) 0)
      (= (:accepted (raw0 w (Item.slice-exit rid))) true)
      (List.Mem r2 (:runs (:world (world-step w (Item.slice-exit rid))))) (= (:id r2) rid) False)
  (intros h hs hf hz ha hm2 he)
  (have hsam := (mb-sample 0 0 0 2 w hs))
  (have hm := (tbl-find-mem RunRow run-id rid r (:runs w) hf))
  (have ei := (tbl-find-id RunRow run-id rid r (:runs w) hf))
  (cases hg (exit-ready r))
  (case [false] (simp [raw0 t-slice-exit hf hg refuse] at ha))
  (case [true]
    (have e0 (= (:world (raw0 w (Item.slice-exit rid)))
                (run-cascade (run-upd w rid run-fin-pop-end) (List.cons Job (Job.jretire rid) (List.nil Job)))))
    (simp only [raw0 t-slice-exit hf hg accept retire-full])
    (have hq (= (q-sx 0 r) true)) (simp only [q-sx hg hz Nat.beq_refl Bool.and_self])
    (have u := (uniq-all RunRow run-id (q-sx 0) r (:runs w) (lit-runs-nodup w hsam) hm hq))
    (rw [ei] at u)
    (have lt (< rid (:next-id w))) (rw [← ei]) (exact (run-below w r hsam hm))
    (have b0 := (mb-upd-tight rid 0 0 w run-fin-pop-end run-fin-pop-end-id (q-sx 0) (sx-row rid 0) hs lt u))
    (have b1 (= (mb rid 0 0 1 (:world (raw0 w (Item.slice-exit rid)))) true))
    (rw [e0]) (exact (mb-retire-gone rid _ b0))
    (have b2 := (mb-step-of-raw0 rid 0 0 1 w (Item.slice-exit rid) (rfl) h ha b1))
    (exact (mb-row-gone rid 0 0 r2 (mb-row-mem rid 0 0 1 _ r2 b2 hm2) he))))

(a/theorem by-sub-lt [a :- Nat, n :- Nat] (=> (<= a (- n 1)) (< 0 n) (< a n)) (intros h1 h2) (omega))

;; ---- resource acknowledgement (T15): the resource leaves its run's `resources`

(a/theorem nat-del-lt [z :- Nat, xs :- (List Nat)]
  (=> (= (nat-mem z xs) true) (< (nat-len (nat-del z xs)) (nat-len xs)))
  (induction xs)
  (case [nil] (intro h) (simp [nat-mem] at h))
  (case [cons x t ih]
    (intro h)
    (cases hb (Nat.beq x z))
    (case [true] (have l := (nat-del-len z t)) (simp only [nat-del nat-len hb]) (omega))
    (case [false] (simp only [nat-mem hb] at h) (have l := (ih h)) (simp only [nat-del nat-len hb]) (omega))))

(a/defn q-ack [z :- Nat, mf :- Nat, mz :- Nat, q :- RunRow] Bool
  (Bool.and (run-done q) (Bool.and (Nat.beq (mu-f q) mf) (Bool.and (Nat.beq (mu-z q) mz) (nat-mem z (:resources q))))))
(a/theorem ack-row [x :- Nat, z :- Nat, mf :- Nat, mz :- Nat]
  (forall [q :- RunRow] (=> (= (q-ack z mf mz q) true) (= (slice-ok q) true) (= (mb-row x mf (- mz 1) 0 (run-unres z q)) true)))
  (intros q hq hs)
  (simp only [q-ack Bool.and_eq_true] at hq)
  (have e1 := (Nat.eq_of_beq_eq_true (And.left (And.right hq))))
  (have e2 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right hq)))))
  (have lt := (nat-del-lt z (:resources q) (And.right (And.right (And.right hq)))))
  (have l1 (<= (mu-f (run-unres z q)) mf)) (exact (Nat.le_of_eq e1))
  (have l2 (<= (mu-z (run-unres z q)) (- mz 1)))
  (have e3 (= (mu-z (run-unres z q)) (nat-len (nat-del z (:resources q))))) (rfl)
  (have e4 (= (mu-z q) (nat-len (:resources q)))) (rfl)
  (rw [e3]) (rw [e4] at e2) (omega)
  (exact (row-bound x mf (- mz 1) (run-unres z q) hs (And.left hq) l1 l2)))

;; the acknowledged resource is listed in its owner's resources (g9, part of p3b)
(a/theorem ack-listed [w :- World, z :- Nat, zr :- ResRow, r :- RunRow]
  (=> (= (p3b w) true) (= (resource-find w z) (Option.some ResRow zr)) (List.Mem r (:runs w)) (= (:id r) (:owner zr))
      (= (nat-mem z (:resources r)) true))
  (intros h hf hm he)
  (have g := (g9-rest-of w (And.left (And.right (And.right (And.right (p3b-parts w h)))))))
  (simp only [g9-rest Bool.and_eq_true] at g)
  (have zm := (tbl-find-mem ResRow resource-id z zr (:res w) hf))
  (have zi := (tbl-find-id ResRow resource-id z zr (:res w) hf))
  (have l1 := (tbl-all-mem ResRow (res-listed (:runs w)) zr (:res w) (And.left (And.right g)) zm))
  (simp only [res-listed] at l1)
  (have l2 := (tbl-all-mem RunRow (listed-in zr) r (:runs w) l1 hm))
  (have hb (= (Nat.beq (:id r) (:owner zr)) true)) (rw [he]) (exact (Nat.beq_refl _))
  (simp only [listed-in hb Bool.not_true Bool.false_or] at l2)
  (have zi2 (= (:id zr) z)) (exact zi)
  (rw [zi2] at l2) (exact l2))

;; the world after T15's raw part, as the cascade of its retire-full
(a/theorem ack-world [w :- World, z :- Nat, zr :- ResRow]
  (=> (= (ack-tok-ok w z) true) (= (resource-find w z) (Option.some ResRow zr))
      (= (:world (raw0 w (Item.resource-ack z)))
         (run-cascade (ack-raw w z (:owner zr)) (List.cons Job (Job.jretire (:owner zr)) (List.nil Job)))))
  (intros hk hf) (simp only [raw0 t15-full hk hf accept retire-full]))

;; the bound after ack-raw, from the owner's rows
(a/theorem ack-raw-bound [w :- World, z :- Nat, zr :- ResRow, r :- RunRow, mf :- Nat, mz :- Nat]
  (=> (= (p3b w) true) (= (sok w) true) (= (ack-tok-ok w z) true) (= (resource-find w z) (Option.some ResRow zr))
      (List.Mem r (:runs w)) (= (:id r) (:owner zr)) (= (q-ack z mf mz r) true)
      (= (mb (:owner zr) mf (- mz 1) 0 (ack-raw w z (:owner zr))) true))
  (intros h hs hk hf hm he hq)
  (have hsam := (mb-sample 0 0 0 2 w hs))
  (have hu (= (tbl-all (no-debtor z) (:edges w)) true)) (simp only [ack-tok-ok Bool.and_eq_true] at hk) (exact (And.right hk))
  (have s2 := (mb-resource-del 0 0 0 2 w z hu hs))
  (have u := (uniq-all RunRow run-id (q-ack z mf mz) r (:runs w) (lit-runs-nodup w hsam) hm hq))
  (have he2 (= (run-id r) (:owner zr))) (exact he)
  (rw [he2] at u)
  (have lt (< (:owner zr) (:next-id w))) (rw [← he]) (exact (run-below w r hsam hm))
  (have b0 := (mb-upd-tight (:owner zr) mf (- mz 1) (resource-del w z) (run-unres z) (run-unres-run-id z) (q-ack z mf mz)
                (ack-row (:owner zr) z mf mz) s2 lt u))
  (simp only [ack-raw])
  (exact (mb-cleanup-upd (:owner zr) mf (- mz 1) 0 _ (:owner zr) (cleanup-drop z) b0)))

;; Theorem (L2 a): an accepted resource acknowledgement (T15) drops its owner's mu-z (the
;; resource leaves the run's outstanding resources); mu-f does not grow
(a/theorem ack-dec [w :- World, z :- Nat, zr :- ResRow, r :- RunRow, r2 :- RunRow]
  (=> (= (p3b w) true) (= (sok w) true) (= (resource-find w z) (Option.some ResRow zr))
      (List.Mem r (:runs w)) (= (:id r) (:owner zr)) (= (run-done r) true)
      (= (:accepted (raw0 w (Item.resource-ack z))) true)
      (List.Mem r2 (:runs (:world (world-step w (Item.resource-ack z))))) (= (:id r2) (:id r))
      (And (< (mu-z r2) (mu-z r)) (<= (mu-f r2) (mu-f r))))
  (intros h hs hf hm he hd ha hm2 he2)
  (cases hk (ack-tok-ok w z))
  (case [false] (simp [raw0 t15-full hk refuse] at ha))
  (case [true]
    (have lm := (ack-listed w z zr r h hf hm he))
    (have hq (= (q-ack z (mu-f r) (mu-z r) r) true)) (simp only [q-ack hd lm Nat.beq_refl Bool.and_self])
    (have b0 := (ack-raw-bound w z zr r (mu-f r) (mu-z r) h hs hk hf hm he hq))
    (have b1 (= (mb (:owner zr) (mu-f r) (- (mu-z r) 1) 0 (:world (raw0 w (Item.resource-ack z)))) true))
    (rw [(ack-world w z zr hk hf)]) (exact (mb-run-cascade (:owner zr) (mu-f r) (- (mu-z r) 1) 0 _ _ b0))
    (have b2 := (mb-step-of-raw0 (:owner zr) (mu-f r) (- (mu-z r) 1) 0 w (Item.resource-ack z) (rfl) h ha b1))
    (have he3 (= (:id r2) (:owner zr))) (exact (Eq.trans he2 he))
    (have t := (mb-row-track (:owner zr) (mu-f r) (- (mu-z r) 1) r2 (mb-row-mem (:owner zr) (mu-f r) (- (mu-z r) 1) 0 _ r2 b2 hm2) he3))
    (have pos (< 0 (mu-z r)))
    (have e4 (= (mu-z r) (nat-len (:resources r)))) (rfl)
    (have l := (nat-del-lt z (:resources r) lm)) (rw [e4]) (omega)
    (have l3 := (And.right (And.right t)))
    (exact (And.intro (by-sub-lt (mu-z r2) (mu-z r) l3 pos) (And.left (And.right t))))))

;; Theorem (L2 c): when the acknowledgement leaves the run with no finalizer, no slice and no
;; resource (it was the last outstanding one), the run is retired in the same step (T13)
(a/theorem ack-retires [w :- World, z :- Nat, zr :- ResRow, r :- RunRow, r2 :- RunRow]
  (=> (= (p3b w) true) (= (sok w) true) (= (resource-find w z) (Option.some ResRow zr))
      (List.Mem r (:runs w)) (= (:id r) (:owner zr)) (= (run-done r) true) (= (mu-f r) 0) (= (mu-z r) 1)
      (= (:accepted (raw0 w (Item.resource-ack z))) true)
      (List.Mem r2 (:runs (:world (world-step w (Item.resource-ack z))))) (= (:id r2) (:id r)) False)
  (intros h hs hf hm he hd h0 h1 ha hm2 he2)
  (cases hk (ack-tok-ok w z))
  (case [false] (simp [raw0 t15-full hk refuse] at ha))
  (case [true]
    (have lm := (ack-listed w z zr r h hf hm he))
    (have hq (= (q-ack z 0 1 r) true)) (simp only [q-ack hd lm h0 h1 Nat.beq_refl Bool.and_self])
    (have b0 := (ack-raw-bound w z zr r 0 1 h hs hk hf hm he hq))
    (have b1 (= (mb (:owner zr) 0 0 1 (:world (raw0 w (Item.resource-ack z)))) true))
    (rw [(ack-world w z zr hk hf)]) (exact (mb-retire-gone (:owner zr) _ b0))
    (have b2 := (mb-step-of-raw0 (:owner zr) 0 0 1 w (Item.resource-ack z) (rfl) h ha b1))
    (have he3 (= (:id r2) (:owner zr))) (exact (Eq.trans he2 he))
    (exact (mb-row-gone (:owner zr) 0 0 r2 (mb-row-mem (:owner zr) 0 0 1 _ r2 b2 hm2) he3))))

;; ===========================================================================
;; Part F. L5, the safety half
;; ===========================================================================

;; a computation that is demanded (not idle) and whose result is unavailable (not live): dirty or
;; fresh-and-not-live; `comp-dirty` implies it
(a/defn comp-waiting [c :- CompRow] Bool (Bool.and (Bool.not (:idle c)) (Bool.not (comp-live c))))
(a/defn waiting-at [w :- World, y :- Nat] Bool (match (comp-find w y) [none false] [(some d) (comp-waiting d)]))
;; no slice is runnable: every run is parked or done, and none holds the slice
(a/defn run-quiet [r :- RunRow] Bool
  (Bool.and (Bool.not (:slice r)) (Bool.or (Nat.beq (:act r) act-parked) (Nat.beq (:act r) act-done))))
(a/defn quiescent [w :- World] Bool (tbl-all run-quiet (:runs w)))
;; the cone: debtors through dep edges and through the unfilled members of the current run
(a/defn csucc [w :- World, x :- Nat] (List Nat) (List.append Nat (dep-debtors (:edges w) x) (blk-deps w x)))

;; Three state facts the proof uses, run as tripwires (progress_test): not proved through the step.
;; h-cur: a computation's current run that is done has set its result (done-epoch = epoch);
;; h-mark: a marked edge is a dep edge whose debtor is a waiting computation (marks come from a
;;   computation being marked, settle unmarks);
;; h-mem: an unfilled member of a computation's parked current run is a source or resource, a task
;;   whose current run is parked (the member fires at its completion), or a waiting computation
;;   the creditor has a dep edge on (fast path / settle deliver to a live one).
(a/defn cur-ok [w :- World, c :- CompRow] Bool
  (match (run-find w (:run c)) [none true]
    [(some r) (Bool.or (Bool.not (Nat.beq (:epoch r) (:epoch c)))
                (Bool.or (Bool.not (Nat.beq (:act r) act-done)) (Nat.beq (:done-epoch c) (:epoch c))))]))
(a/defn h-cur [w :- World] Bool (tbl-all (cur-ok w) (:comps w)))
(a/defn mark-ok [w :- World, e :- EdgeRow] Bool
  (Bool.or (Bool.not (:marked e)) (Bool.and (Nat.beq (:kind e) ek-dep) (waiting-at w (:debtor e)))))
(a/defn h-mark [w :- World] Bool (tbl-all (mark-ok w) (:edges w)))
(a/defn mem-y-ok [w :- World, x :- Nat, y :- Nat] Bool
  (Bool.or (blk-leaf w y)
   (Bool.or (Bool.and (task-has w y) (blk-base w y))
            (Bool.and (waiting-at w y) (reach-mem y (dep-debtors (:edges w) x))))))
(a/defn mem-ok [w :- World, c :- CompRow] Bool
  (Bool.or (Bool.not (blk-base w (:id c))) (tbl-all (mem-y-ok w (:id c)) (blk-deps w (:id c)))))
(a/defn h-mem [w :- World] Bool (tbl-all (mem-ok w) (:comps w)))

;; ---- lemmas

(a/theorem dd-mem [es :- (List EdgeRow), x :- Nat, e :- EdgeRow]
  (=> (List.Mem e es) (= (Nat.beq (:creditor e) x) true) (= (Nat.beq (:kind e) ek-dep) true)
      (= (reach-mem (:debtor e) (dep-debtors es x)) true))
  (induction es)
  (case [nil] (intros hm hc hk) (cases hm))
  (case [cons q t ih]
    (intros hm hc hk)
    (cases hm)
    (case [head] (simp only [dep-debtors hc hk Bool.and_self reach-mem Nat.beq_refl]))
    (case [tail hm2]
      (have r := (ih hm2 hc hk))
      (cases hq (Bool.and (Nat.beq (:creditor q) x) (Nat.beq (:kind q) ek-dep)))
      (all_goals (simp [dep-debtors hq reach-mem r])))))

;; a dep debtor of x has a smaller rank (I12, `ranks-ok`)
(a/theorem dd-rank [w :- World, x :- Nat, y :- Nat, es :- (List EdgeRow)]
  (=> (= (tbl-all (rank-edge-ok w) es) true) (= (reach-mem y (dep-debtors es x)) true)
      (= (comp-has w x) true) (= (comp-has w y) true) (< (comp-rank w y) (comp-rank w x)))
  (induction es)
  (case [nil] (intros h1 h2 h3 h4) (simp [dep-debtors reach-mem] at h2))
  (case [cons q t ih]
    (intros h1 h2 h3 h4)
    (simp only [tbl-all Bool.and_eq_true] at h1)
    (cases hq (Bool.and (Nat.beq (:creditor q) x) (Nat.beq (:kind q) ek-dep)))
    (case [false] (simp only [dep-debtors hq] at h2) (exact (ih (And.right h1) h2 h3 h4)))
    (case [true]
      (simp only [dep-debtors hq reach-mem] at h2)
      (cases hb (Nat.beq y (:debtor q)))
      (case [false] (simp only [hb] at h2) (exact (ih (And.right h1) h2 h3 h4)))
      (case [true]
        (simp only [Bool.and_eq_true] at hq)
        (have ec := (Nat.eq_of_beq_eq_true (And.left hq)))
        (have ed := (Nat.eq_of_beq_eq_true hb))
        (have r := (And.left h1))
        (rw [← ec] at h3) (rw [ed] at h4)
        (simp only [rank-edge-ok (And.right hq) h3 h4 Bool.not_true Bool.false_or Nat.blt_eq] at r)
        (rw [ed ← ec]) (exact r)))))

(a/theorem by-rank-eq [w :- World, x :- Nat, m :- CompRow]
  (=> (= (comp-find w x) (Option.some CompRow m)) (= (comp-rank w x) (:rank m)))
  (intro hf) (simp only [comp-rank hf]))
(a/theorem rank-of-find [w :- World, x :- Nat, m :- CompRow]
  (=> (= (comp-find w x) (Option.some CompRow m)) (And (= (comp-has w x) true) (= (comp-rank w x) (:rank m))))
  (intro hf)
  (exact (And.intro (tbl-find-has CompRow comp-id x m (:comps w) hf) (by-rank-eq w x m hf))))

(a/theorem reach-dep [w :- World, c0 :- Nat, x :- Nat, y :- Nat]
  (=> (Reach (csucc w) (List.cons Nat c0 (List.nil Nat)) x) (= (reach-mem y (dep-debtors (:edges w) x)) true)
      (Reach (csucc w) (List.cons Nat c0 (List.nil Nat)) y))
  (intros hx hy)
  (have m (= (reach-mem y (csucc w x)) true)) (simp only [csucc reach-mem-append hy Bool.true_or])
  (exact (Reach.step (csucc w) (List.cons Nat c0 (List.nil Nat)) x y hx (Iff.mp (reach-mem-iff y (csucc w x)) m))))
(a/theorem reach-blk [w :- World, c0 :- Nat, x :- Nat, y :- Nat]
  (=> (Reach (csucc w) (List.cons Nat c0 (List.nil Nat)) x) (List.Mem y (blk-deps w x))
      (Reach (csucc w) (List.cons Nat c0 (List.nil Nat)) y))
  (intros hx hy)
  (have b := (Iff.mpr (reach-mem-iff y (blk-deps w x)) hy))
  (have m (= (reach-mem y (csucc w x)) true)) (simp only [csucc reach-mem-append b Bool.or_true])
  (exact (Reach.step (csucc w) (List.cons Nat c0 (List.nil Nat)) x y hx (Iff.mp (reach-mem-iff y (csucc w x)) m))))

(a/theorem count-zero [A :- Type, p :- (=> A Bool), xs :- (List A)]
  (=> (forall [a :- A] (=> (List.Mem a xs) (= (p a) false))) (= (tbl-count p xs) 0))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-count]))
  (case [cons q t ih]
    (intro h)
    (have h1 := (h q (List.Mem.head t)))
    (have h2 := (ih (fn [a :- A, ha :- (List.Mem a t)] (h a (List.Mem.tail q ha)))))
    (simp only [tbl-count h1 h2])))

(a/theorem dirty-waiting [d :- CompRow] (=> (= (comp-dirty d) true) (= (comp-waiting d) true))
  (intro h) (simp only [comp-dirty Bool.and_eq_true] at h) (simp only [comp-waiting (And.left h) (And.left (And.right h)) Bool.and_self]))

;; the hypotheses of L5 that negate its three conclusions, over the cone of c0
(a/defn none-blocked [w :- World, c0 :- Nat] Prop
  (forall [y :- Nat] (=> (Reach (csucc w) (List.cons Nat c0 (List.nil Nat)) y) (Not (Derive (blk-base w) (blk-deps w) (blk-leaf w) y)))))
(a/defn none-eligible [w :- World, c0 :- Nat] Prop
  (forall [y :- Nat, d :- CompRow] (=> (= (comp-find w y) (Option.some CompRow d)) (Reach (csucc w) (List.cons Nat c0 (List.nil Nat)) y)
                                       (= (:idle d) false) (= (needs-run w d) true) (= (eligible w d) false))))
(a/defn tasks-blocked [w :- World, c0 :- Nat] Prop
  (forall [y :- Nat] (=> (Reach (csucc w) (List.cons Nat c0 (List.nil Nat)) y) (= (task-has w y) true) (= (blk-base w y) true)
                         (Derive (blk-base w) (blk-deps w) (blk-leaf w) y))))

;; one computation of the cone: if every waiting computation of smaller rank in the cone is
;; excluded, so is this one
(a/theorem l5-step [w :- World, c0 :- Nat, x :- Nat, m :- CompRow]
  (=> (= (p3b w) true) (= (quiescent w) true) (= (h-cur w) true) (= (h-mark w) true) (= (h-mem w) true)
      (none-blocked w c0) (none-eligible w c0) (tasks-blocked w c0)
      (= (comp-find w x) (Option.some CompRow m)) (Reach (csucc w) (List.cons Nat c0 (List.nil Nat)) x)
      (forall [y :- Nat, d :- CompRow] (=> (= (comp-find w y) (Option.some CompRow d)) (< (:rank d) (:rank m))
                                           (Reach (csucc w) (List.cons Nat c0 (List.nil Nat)) y) (= (comp-waiting d) false)))
      (= (comp-waiting m) false))
  (intros h hq hc hk hme n1 n2 n3 hf hr ih)
  (simp only [none-blocked] at n1)
  (simp only [none-eligible] at n2)
  (simp only [tasks-blocked] at n3)
  (simp only [quiescent] at hq)
  (simp only [h-cur] at hc)
  (simp only [h-mark] at hk)
  (simp only [h-mem] at hme)
  (have hs := (ga-sample w (And.left (p3b-parts w h))))
  (have pex := (And.left (inv-parts w hs)))
  (simp only [pending-exact pending-exact-in] at pex)
  (have hrk := (rk-ranks w (And.left (And.right (p3b-parts w h)))))
  (have hm := (tbl-find-mem CompRow comp-id x m (:comps w) hf))
  (have hid := (tbl-find-id CompRow comp-id x m (:comps w) hf))
  (have hid2 (= (:id m) x)) (exact hid)
  (have hfr := (rank-of-find w x m hf))
  ;; a waiting dep debtor of x has a smaller rank and is in the cone: excluded by the IH
  (have small (forall [y :- Nat, d :- CompRow] (=> (= (comp-find w y) (Option.some CompRow d)) (= (reach-mem y (dep-debtors (:edges w) x)) true)
                                                   (= (comp-waiting d) false))))
  (intros y d hd hy)
  (have r2 := (rank-of-find w y d hd))
  (have lt := (dd-rank w x y (:edges w) hrk hy (And.left hfr) (And.left r2)))
  (rw [(And.right hfr) (And.right r2)] at lt)
  (exact (ih y d hd lt (reach-dep w c0 x y hr hy)))
  (cases hw (comp-waiting m))
  (case [false] (rfl))
  (case [true]
    (have wt := hw)
    (simp only [comp-waiting Bool.and_eq_true] at wt)
    (have hidle := (bnot-true _ (And.left wt)))
    (have hlive := (bnot-true _ (And.right wt)))
    (cases hn (needs-run w m))
    ;; needs-run: every dirty dep debtor is excluded, so m is eligible
    (case [true]
      (have pe (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (dep-ok-for w (blocked-set w) (:id m) e) true))))
      (intros e he)
      (cases hdo (dep-of (:id m) e))
      (case [false] (simp only [dep-ok-for hdo Bool.not_false Bool.true_or]))
      (case [true]
        (cases hd (comp-find w (:debtor e)))
        (case [none] (simp only [dep-ok-for debtor-settled hd Bool.or_true]))
        (case [some d]
          (have hdo2 := hdo)
          (simp only [dep-of Bool.and_eq_true] at hdo2)
          (have hcx (= (Nat.beq (:creditor e) x) true)) (rw [← hid2]) (exact (And.right hdo2))
          (have dd := (dd-mem (:edges w) x e he hcx (And.left hdo2)))
          (have wd := (small (:debtor e) d hd dd))
          (have nd (= (comp-dirty d) false))
          (cases hdd (comp-dirty d)) (case [false] (rfl)) (case [true] (have c := (dirty-waiting d hdd)) (rw [wd] at c) (simp at c))
          (simp only [dep-ok-for debtor-settled hdo hd nd Bool.not_false Bool.true_or Bool.or_true])))
      (have el (= (eligible w m) true)) (simp only [eligible]) (exact (all-of-mem EdgeRow _ (:edges w) pe))
      (have ne := (n2 x m hf hr hidle hn))
      (rw [el] at ne) (simp at ne))
    (case [false]
      (cases hde (Nat.beq (:done-epoch m) (:epoch m)))
      ;; done-epoch = epoch: every marked in-edge has a waiting debtor of smaller rank, so pending = 0
      (case [true]
        (have mk (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (marks (:id m) e) false))))
        (intros e he)
        (cases hmk (marks (:id m) e))
        (case [false] (rfl))
        (case [true]
          (simp only [marks Bool.and_eq_true] at hmk)
          (have mo := (tbl-all-mem EdgeRow (mark-ok w) e (:edges w) hk he))
          (simp only [mark-ok (And.right hmk) Bool.not_true Bool.false_or Bool.and_eq_true] at mo)
          (have hcx (= (Nat.beq (:creditor e) x) true)) (rw [← hid2]) (exact (And.left hmk))
          (have dd := (dd-mem (:edges w) x e he hcx (And.left mo)))
          (have wa := (And.right mo))
          (cases hd (comp-find w (:debtor e)))
          (case [none] (simp [waiting-at hd] at wa))
          (case [some d]
            (simp only [waiting-at hd] at wa)
            (have wd := (small (:debtor e) d hd dd))
            (rw [wd] at wa) (simp at wa)))
        (have c0e := (count-zero EdgeRow (marks (:id m)) (:edges w) mk))
        (have pe := (tbl-all-mem CompRow (comp-exact (:edges w)) m (:comps w) pex hm))
        (simp only [comp-exact marked-in c0e] at pe)
        (have lv (= (comp-live m) true)) (simp only [comp-live hidle hde pe Bool.not_false Bool.and_self])
        (rw [lv] at hlive) (simp at hlive))
      ;; otherwise C.run is current: parked (quiescent), so m is Blocked unless a member is not
      (case [false]
        (have rc (= (run-current-of-comp w m) true))
        (cases hb (run-current-of-comp w m)) (case [true] (rfl)) (case [false] (simp [needs-run hde hb] at hn))
        (cases hrf (run-find w (:run m)))
        (case [none] (simp [run-current-of-comp hrf] at rc))
        (case [some r]
          (simp only [run-current-of-comp hrf] at rc)
          (have rm := (tbl-find-mem RunRow run-id (:run m) r (:runs w) hrf))
          (have qr := (tbl-all-mem RunRow run-quiet r (:runs w) hq rm))
          (simp only [run-quiet Bool.and_eq_true Bool.or_eq_true] at qr)
          (have qo := (And.right qr))
          (cases qo)
          (case [inl hp]
            (have hb (= (blk-base w x) true)) (simp only [blk-base hf run-parked-of hrf hp rc Bool.and_self])
            (have mo := (tbl-all-mem CompRow (mem-ok w) m (:comps w) hme hm))
            (simp only [mem-ok hid2] at mo)
            (simp only [hb Bool.not_true Bool.false_or] at mo)
            (have hd (forall [y :- Nat] (=> (List.Mem y (blk-deps w x)) (= (blk-leaf w y) false) (Derive (blk-base w) (blk-deps w) (blk-leaf w) y))))
            (intros y hy hl)
            (have my := (tbl-all-mem Nat (mem-y-ok w x) y (blk-deps w x) mo hy))
            (simp only [mem-y-ok hl Bool.false_or Bool.or_eq_true Bool.and_eq_true] at my)
            (cases my)
            (case [inl tk] (exact (n3 y (reach-blk w c0 x y hr hy) (And.left tk) (And.right tk))))
            (case [inr cp]
              (cases hd2 (comp-find w y))
              (case [none] (have c := (And.left cp)) (simp [waiting-at hd2] at c))
              (case [some d]
                (have c := (And.left cp)) (simp only [waiting-at hd2] at c)
                (have wd := (small y d hd2 (And.right cp)))
                (rw [wd] at c) (simp at c)))
            (exact (False.elim (n1 x hr (Derive.mk (blk-base w) (blk-deps w) (blk-leaf w) x hb hd)))))
          (case [inr hdn]
            (have co := (tbl-all-mem CompRow (cur-ok w) m (:comps w) hc hm))
            (simp only [cur-ok hrf rc hdn Bool.not_true Bool.false_or] at co)
            (rw [co] at hde) (simp at hde)))))))

(a/theorem lt-of-lt-succ [a :- Nat, b :- Nat, k :- Nat] (=> (< a b) (< b (+ k 1)) (< a k)) (intros h1 h2) (omega))

;; well-founded by rank (I12): induction on a bound of the computation's rank
(a/theorem l5-core [w :- World, c0 :- Nat, h :- (= (p3b w) true), hq :- (= (quiescent w) true), hc :- (= (h-cur w) true),
                    hk :- (= (h-mark w) true), hme :- (= (h-mem w) true),
                    n1 :- (none-blocked w c0), n2 :- (none-eligible w c0), n3 :- (tasks-blocked w c0), n :- Nat]
  (forall [x :- Nat, m :- CompRow] (=> (= (comp-find w x) (Option.some CompRow m)) (< (:rank m) n)
                                       (Reach (csucc w) (List.cons Nat c0 (List.nil Nat)) x) (= (comp-waiting m) false)))
  (induction n)
  (case [zero] (intros x m hf hlt hr) (exact (absurd hlt (Nat.not_lt_zero _))))
  (case [succ k ih]
    (intros x m hf hlt hr)
    (exact (l5-step w c0 x m h hq hc hk hme n1 n2 n3 hf hr
             (fn [y :- Nat, d :- CompRow, hd :- (= (comp-find w y) (Option.some CompRow d)), hl :- (< (:rank d) (:rank m)),
                  hy :- (Reach (csucc w) (List.cons Nat c0 (List.nil Nat)) y)]
               (ih y d hd (lt-of-lt-succ (:rank d) (:rank m) k hl hlt) hy))))))

;; Theorem (L5, safety half): in a quiescent world (no runnable slice), a demanded computation c0
;; whose result is unavailable (not idle, not live; in particular a dirty one) has in its cone
;; (dep debtors and unfilled members, transitively) an entity that is Blocked (§4.5.6, the least
;; fixpoint `Derive`, i.e. blocked on non-computation debtors), or an eligible needs-run
;; computation (T11 can run it), or a task whose current run is parked and that is not Blocked (a
;; wait that no source, resource or runnable computation can end: a user deadlock, see the ns
;; docstring). Stated contrapositively: the three negations are absurd. Given the state facts
;; h-cur, h-mark, h-mem (tripwire-checked, not proved through the step).
(a/theorem l5-safety [w :- World, c0 :- Nat, c :- CompRow]
  (=> (= (p3b w) true) (= (quiescent w) true) (= (h-cur w) true) (= (h-mark w) true) (= (h-mem w) true)
      (= (comp-find w c0) (Option.some CompRow c)) (= (comp-waiting c) true)
      (none-blocked w c0) (none-eligible w c0) (tasks-blocked w c0) False)
  (intros h hq hc hk hme hf hw n1 n2 n3)
  (have r0 (Reach (csucc w) (List.cons Nat c0 (List.nil Nat)) c0))
  (exact (Reach.root (csucc w) (List.cons Nat c0 (List.nil Nat)) c0 (List.Mem.head (List.nil Nat))))
  (have z := (l5-core w c0 h hq hc hk hme n1 n2 n3 (+ (:rank c) 1) c0 c hf (Nat.lt_succ_self (:rank c)) r0))
  (rw [z] at hw) (simp at hw))

(a/theorem l5-dirty [w :- World, c0 :- Nat, c :- CompRow]
  (=> (= (p3b w) true) (= (quiescent w) true) (= (h-cur w) true) (= (h-mark w) true) (= (h-mem w) true)
      (= (comp-find w c0) (Option.some CompRow c)) (= (comp-dirty c) true)
      (none-blocked w c0) (none-eligible w c0) (tasks-blocked w c0) False)
  (intros h hq hc hk hme hf hd n1 n2 n3)
  (exact (l5-safety w c0 c h hq hc hk hme hf (dirty-waiting c hd) n1 n2 n3)))
