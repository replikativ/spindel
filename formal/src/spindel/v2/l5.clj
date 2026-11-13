(ns spindel.v2.l5
  "L5 (safety half) without hypotheses on the step's worlds, kernel-checked (Init only).

  spindel.v2.progress proves `l5-safety` under three state facts (h-cur, h-mark, h-mem).
    h-cur  follows from i10's bundle g10r (E2: a current run of C is C.run and is alive or
           C.done-epoch = C.epoch; rof: C.run names a run of C): `l5-h-cur`; `l5-safety-p3c`,
           `l5-step-p3c` state L5 on p3c worlds with h-mark and h-mem as the remaining hypotheses.
    h-mem  is not a step invariant (a task member's run may be running); `h-mem2` (the task's
           run is alive) is, on every tripwire, and gives h-mem at a quiescent point
           (`h-mem-of2`). `l5-safety-inv`: L5 from p3c, h-mark and h-mem2, the two state facts
           still to prove through the step (both hold after every step of the random drivers).
  Part B: I5's dep-final clause with the unfilled-member exemption (`i5-dep-final-mem`, tripwire); since
  Z#53/Z#54 the literal clause holds as well (inv_test `literal-i5-member-final-resolved`), proved
  through the step in spindel.v2.i5 (`step-lit-i5-dep-final-total`). h-mark was false in the model
  before Z#59 (a group await's fired sibling survived T11 and re-marked its creditor on a later
  write); Z#59 (marking only from armed fires, T11's cut by creation order) resolved it (l5_test
  `h-mark-fired-sibling-resolved`, oracle sample 13). h-mark and h-mem2 are tripwires (random drivers,
  samples 7-13); their proofs through the step are open (notes/PLAN.md, branch z59).
  Part C: the settle worklist empties within its fuel (`settle-done-ok`, the former honest flag;
  needed for h-mark at T12): potential |queue| + #marked edges, every pop unmarks all marked
  out-edges of the settled computation (`sd-fold`), the settle edits mark no edge and keep ids,
  kinds and debtors (`es-nm`), `settle-next` adds at most one creditor per unmarked edge."
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
            [spindel.v2.casc :refer :all]
            [spindel.v2.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.lit :refer :all]
            [spindel.v2.idle :refer :all]
            [spindel.v2.p3 :refer :all]
            [spindel.v2.i10 :refer :all]
            [spindel.v2.i11 :refer :all]
            [spindel.v2.progress :refer :all]))

;; ===========================================================================
;; Part A. h-cur from g10r
;; ===========================================================================

(a/theorem l5-cur-ok [w :- World, c :- CompRow]
  (=> (= (g10r w) true) (List.Mem c (:comps w)) (= (cur-ok w c) true))
  (intros h mc)
  (have hs := (g10-sample _ _ w h))
  (cases hrf (run-find w (:run c)))
  (case [none] (simp only [cur-ok hrf]))
  (case [some r]
    (have mr := (tbl-find-mem RunRow run-id (:run c) r (:runs w) hrf))
    (have hid := (tbl-find-id RunRow run-id (:run c) r (:runs w) hrf))
    (have hid2 (= (:id r) (:run c))) (exact hid)
    (have hz := (run-id-pos w r hs mr))
    (have hk0 (= (reach-mem (:id (rk10 r)) (List.nil Nat)) false)) (rfl)
    (have pc := (rc-parts _ _ (rk10 r) (ck10 c) (g10-rc _ _ w r c h mr mc) hk0))
    (have ho := (rof-is (rk10 r) (ck10 c) (And.right pc) hz hid2))
    (have ho2 (= (Nat.beq (:of (rk10 r)) (:id (ck10 c))) true)) (rw [ho]) (exact (Nat.beq_refl _))
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [cur-ok hrf he Bool.not_false Bool.true_or]))
    (case [true]
      (have he2 (= (Nat.beq (:epoch (rk10 r)) (:epoch (ck10 c))) true)) (exact he)
      (have ce := (cur-eq _ (rk10 r) (ck10 c) (And.left pc) ho2 he2))
      (have cf := (And.right (And.right ce)))
      (simp only [cur-fin rk10 ck10 reach-mem run-alive Bool.false_or] at cf)
      (simp only [cur-ok hrf he Bool.not_true Bool.false_or])
      (exact cf))))

(a/theorem l5-h-cur [w :- World] (=> (= (g10r w) true) (= (h-cur w) true))
  (intro h)
  (simp only [h-cur])
  (exact (all-of-mem CompRow _ (:comps w) (fn [c :- CompRow, mc :- (List.Mem c (:comps w))] (l5-cur-ok w c h mc)))))

;; L5 (safety half) on every world the step reaches from p3c: h-cur is discharged, h-mark and
;; h-mem remain hypotheses (tripwire-checked; see notes/PLAN.md, branch l5, for their proof plan)
(a/theorem l5-safety-p3c [w :- World, c0 :- Nat, c :- CompRow]
  (=> (= (p3c w) true) (= (quiescent w) true) (= (h-mark w) true) (= (h-mem w) true)
      (= (comp-find w c0) (Option.some CompRow c)) (= (comp-waiting c) true)
      (none-blocked w c0) (none-eligible w c0) (tasks-blocked w c0) False)
  (intros h hq hk hme hf hw n1 n2 n3)
  (have p := (p3c-parts w h))
  (exact (l5-safety w c0 c (And.left p) hq (l5-h-cur w (And.right p)) hk hme hf hw n1 n2 n3)))

(a/theorem l5-step-p3c [w :- World, it :- Item, c0 :- Nat, c :- CompRow]
  (=> (= (p3c w) true)
      (= (quiescent (:world (world-step w it))) true) (= (h-mark (:world (world-step w it))) true)
      (= (h-mem (:world (world-step w it))) true)
      (= (comp-find (:world (world-step w it)) c0) (Option.some CompRow c)) (= (comp-waiting c) true)
      (none-blocked (:world (world-step w it)) c0) (none-eligible (:world (world-step w it)) c0)
      (tasks-blocked (:world (world-step w it)) c0) False)
  (intros h hq hk hme hf hw n1 n2 n3)
  (exact (l5-safety-p3c (:world (world-step w it)) c0 c (step-p3c w it h) hq hk hme hf hw n1 n2 n3)))

;; ---- h-mem as a step invariant: at a non-quiescent point a task member's run may be running,
;; so the fact the step keeps says "alive"; at a quiescent point alive means parked

(a/defn task-alive-at [w :- World, y :- Nat] Bool
  (match (task-find w y) [none false] [(some t) (opt-test run-alive (run-find w (:run t)))]))
(a/defn mem-y-ok2 [w :- World, x :- Nat, y :- Nat] Bool
  (Bool.or (blk-leaf w y)
   (Bool.or (Bool.and (task-has w y) (task-alive-at w y))
            (Bool.and (waiting-at w y) (reach-mem y (dep-debtors (:edges w) x))))))
(a/defn mem-ok2 [w :- World, c :- CompRow] Bool
  (Bool.or (Bool.not (blk-base w (:id c))) (tbl-all (mem-y-ok2 w (:id c)) (blk-deps w (:id c)))))
(a/defn h-mem2 [w :- World] Bool (tbl-all (mem-ok2 w) (:comps w)))

(a/theorem task-base-q [w :- World, y :- Nat]
  (=> (= (inv-sample w) true) (= (quiescent w) true) (= (task-has w y) true) (= (task-alive-at w y) true)
      (= (blk-base w y) true))
  (intros hs hq tk al)
  (cases hc (comp-find w y))
  (case [some c]
    (have mc := (tbl-find-mem CompRow comp-id y c (:comps w) hc))
    (have ic := (tbl-find-id CompRow comp-id y c (:comps w) hc))
    (have ic2 (= (:id c) y)) (exact ic)
    (have ne := (comp-task-ne w c y hs mc tk))
    (rw [ic2] at ne) (simp [Nat.beq_refl] at ne))
  (case [none]
    (simp only [task-alive-at] at al)
    (cases ht (task-find w y))
    (case [none] (simp only [ht] at al) (simp at al))
    (case [some t]
      (simp only [ht] at al)
      (cases hr (run-find w (:run t)))
      (case [none] (simp only [hr opt-test] at al) (simp at al))
      (case [some r]
        (simp only [hr opt-test run-alive] at al)
        (have mr := (tbl-find-mem RunRow run-id (:run t) r (:runs w) hr))
        (have qr := (tbl-all-mem RunRow run-quiet r (:runs w) hq mr))
        (simp only [run-quiet Bool.and_eq_true Bool.or_eq_true] at qr)
        (have qo := (And.right qr))
        (cases qo)
        (case [inl hp] (simp only [blk-base hc ht hr opt-test run-parked hp]))
        (case [inr hd] (have z := (bnot-true _ al)) (rw [hd] at z) (simp at z))))))

(a/theorem mem-y-q [w :- World, x :- Nat, y :- Nat]
  (=> (= (inv-sample w) true) (= (quiescent w) true) (= (mem-y-ok2 w x y) true) (= (mem-y-ok w x y) true))
  (intros hs hq h)
  (simp only [mem-y-ok2 Bool.or_eq_true] at h)
  (cases h)
  (case [inl a] (simp only [mem-y-ok a Bool.true_or]))
  (case [inr b]
    (cases b)
    (case [inl a]
      (simp only [Bool.and_eq_true] at a)
      (have bb := (task-base-q w y hs hq (And.left a) (And.right a)))
      (simp only [mem-y-ok (And.left a) bb Bool.and_self Bool.true_or Bool.or_true]))
    (case [inr c] (simp only [mem-y-ok c Bool.or_true]))))

;; at a quiescent point, h-mem2 gives h-mem
(a/theorem h-mem-of2 [w :- World] (=> (= (inv-sample w) true) (= (quiescent w) true) (= (h-mem2 w) true) (= (h-mem w) true))
  (intros hs hq h)
  (simp only [h-mem2] at h)
  (simp only [h-mem])
  (apply (tbl-all-mem-mono CompRow (mem-ok2 w) (mem-ok w) (:comps w) _ h))
  (intros c mc hc)
  (simp only [mem-ok2 Bool.or_eq_true] at hc)
  (simp only [mem-ok Bool.or_eq_true])
  (cases hc)
  (case [inl a] (exact (Or.inl a)))
  (case [inr b]
    (apply Or.inr)
    (exact (tbl-all-mem-mono Nat (mem-y-ok2 w (:id c)) (mem-y-ok w (:id c)) (blk-deps w (:id c))
             (fn [y :- Nat, my :- (List.Mem y (blk-deps w (:id c))), hy :- (= (mem-y-ok2 w (:id c) y) true)] (mem-y-q w (:id c) y hs hq hy))
             b))))

;; L5 from p3c and the two step invariants h-mark and h-mem2 (both tripwire-checked at every step)
(a/theorem l5-safety-inv [w :- World, c0 :- Nat, c :- CompRow]
  (=> (= (p3c w) true) (= (quiescent w) true) (= (h-mark w) true) (= (h-mem2 w) true)
      (= (comp-find w c0) (Option.some CompRow c)) (= (comp-waiting c) true)
      (none-blocked w c0) (none-eligible w c0) (tasks-blocked w c0) False)
  (intros h hq hk hme hf hw n1 n2 n3)
  (have hs := (ga-sample w (And.left (p3b-parts w (And.left (p3c-parts w h))))))
  (exact (l5-safety-p3c w c0 c h hq hk (h-mem-of2 w hs hq hme) hf hw n1 n2 n3)))

;; ===========================================================================
;; Part B. I5's dep-final clause as the model has it (tripwire)
;; ===========================================================================

;; Literal I5 (`lit-i5-dep-final`: no armed dep edge has a final debtor) was false for unfilled
;; activation members before Z#53 (T10 kept them armed); closing a source now fills them first
;; (rule.clj `wake-closed`), inv_test `literal-i5-member-final-resolved`. The weaker reading below
;; (an armed dep edge on a final debtor is an unfilled member) stays as a tripwire.
(a/defn dep-final-mem-ok [w :- World, e :- EdgeRow] Bool
  (Bool.or (dep-final-ok w e) (tbl-any (act-has-member (:id e)) (:acts w))))
(a/defn i5-dep-final-mem [w :- World] Bool (tbl-all (dep-final-mem-ok w) (:edges w)))

;; ===========================================================================
;; Part C. The settle worklist empties within its fuel (`settle-done`)
;; ===========================================================================

;; Potential: |queue| + #marked edges. A pop of d settles d: every marked out-edge of d is
;; unmarked (each id of `tbl-scan edge-id (out-dep d)` is unmarked by its settle-edge, no edit of
;; a settle marks an edge or changes an edge's kind or debtor), and `settle-next` lists at most
;; one creditor per such edge. So |queue| + #marked drops by >= 1 per pop, and it starts below
;; 2 + |edges| (`settle-fuel`).

(a/defn sd-marked [e :- EdgeRow] Bool (:marked e))
(a/defn em-other [d :- Nat, e :- EdgeRow] Bool (Bool.and (:marked e) (Bool.not (out-dep d e))))
(a/defn sd-row [d :- Nat, ys :- (List Nat), e :- EdgeRow] Bool (Bool.or (Bool.not (out-marked d e)) (reach-mem (:id e) ys)))
;; es2 arises from es by edits that mark no edge and keep ids, kinds and debtors
(a/defn es-nm [es :- (List EdgeRow), es2 :- (List EdgeRow)] Prop
  (forall [d :- Nat, ys :- (List Nat)]
    (And (=> (= (tbl-all (sd-row d ys) es) true) (= (tbl-all (sd-row d ys) es2) true))
         (<= (tbl-count (em-other d) es2) (tbl-count (em-other d) es)))))

(a/theorem es-nm-refl [es :- (List EdgeRow)] (es-nm es es)
  (simp only [es-nm])
  (intros d ys)
  (exact (And.intro (fn [h :- (= (tbl-all (sd-row d ys) es) true)] h) (Nat.le_refl _))))

(a/theorem es-nm-trans [es1 :- (List EdgeRow), es2 :- (List EdgeRow), es3 :- (List EdgeRow)]
  (=> (es-nm es1 es2) (es-nm es2 es3) (es-nm es1 es3))
  (intros h1 h2)
  (simp only [es-nm] at h1 h2)
  (simp only [es-nm])
  (intros d ys)
  (have a1 := (h1 d ys))
  (have a2 := (h2 d ys))
  (exact (And.intro (fn [h :- (= (tbl-all (sd-row d ys) es1) true)] ((And.left a2) ((And.left a1) h)))
                    (Nat.le_trans (And.right a2) (And.right a1)))))

(a/theorem count-upd-mono [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), p :- (=> A Bool),
                           hf :- (forall [r :- A] (=> (= (p (f r)) true) (= (p r) true))), xs :- (List A)]
  (<= (tbl-count p (tbl-upd idf x f xs)) (tbl-count p xs))
  (induction xs)
  (case [nil] (simp [tbl-count tbl-upd]))
  (case [cons h t ih]
    (cases hx (Nat.beq (idf h) x))
    (case [false] (simp only [tbl-upd hx tbl-count-cons]) (omega))
    (case [true]
      (simp only [tbl-upd hx tbl-count-cons])
      (cases hp (p (f h)))
      (case [false] (simp only [hp b2n]) (cases hq (p h)) (all_goals (simp only [hq b2n])) (omega) (omega))
      (case [true] (simp only [hp (hf h hp) b2n]) (omega)))))

;; an edge function that keeps id, kind and debtor and marks nothing
(a/defn ekeep [f :- (=> EdgeRow EdgeRow), e :- EdgeRow] Bool
  (Bool.and (Nat.beq (:id (f e)) (:id e))
   (Bool.and (Nat.beq (:kind (f e)) (:kind e))
    (Bool.and (Nat.beq (:debtor (f e)) (:debtor e)) (Bool.or (Bool.not (:marked (f e))) (:marked e))))))

(a/theorem ekeep-row [f :- (=> EdgeRow EdgeRow), e :- EdgeRow, d :- Nat, ys :- (List Nat)]
  (=> (= (ekeep f e) true) (= (sd-row d ys e) true) (= (sd-row d ys (f e)) true))
  (intros hk hr)
  (simp only [ekeep Bool.and_eq_true] at hk)
  (have e1 := (Nat.eq_of_beq_eq_true (And.left hk)))
  (have e2 := (Nat.eq_of_beq_eq_true (And.left (And.right hk))))
  (have e3 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right hk)))))
  (have m := (And.right (And.right (And.right hk))))
  (simp only [sd-row out-marked out-dep e1 e2 e3]) (simp only [sd-row out-marked out-dep] at hr)
  (cases hm (:marked (f e)))
  (case [false] (simp only [Bool.and_false Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [hm Bool.not_true Bool.false_or] at m)
    (simp only [m Bool.and_true] at hr) (simp only [Bool.and_true]) (exact hr)))

(a/theorem ekeep-cnt [f :- (=> EdgeRow EdgeRow), e :- EdgeRow, d :- Nat]
  (=> (= (ekeep f e) true) (= (em-other d (f e)) true) (= (em-other d e) true))
  (intros hk hr)
  (simp only [ekeep Bool.and_eq_true] at hk)
  (have e2 := (Nat.eq_of_beq_eq_true (And.left (And.right hk))))
  (have e3 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right hk)))))
  (have m := (And.right (And.right (And.right hk))))
  (simp only [em-other out-dep e2 e3 Bool.and_eq_true] at hr)
  (simp only [em-other out-dep Bool.and_eq_true])
  (have hm := (And.left hr))
  (simp only [hm Bool.not_true Bool.false_or] at m)
  (exact (And.intro m (And.right hr))))

(a/theorem es-nm-upd [x :- Nat, f :- (=> EdgeRow EdgeRow), hf :- (forall [e :- EdgeRow] (= (ekeep f e) true)), es :- (List EdgeRow)]
  (es-nm es (tbl-upd edge-id x f es))
  (simp only [es-nm])
  (intros d ys)
  (apply And.intro)
  (intro h)
  (exact (tbl-all-upd EdgeRow edge-id x f (sd-row d ys) (sd-row d ys)
           (fn [r :- EdgeRow, p :- (= (sd-row d ys r) true), q :- (= (Nat.beq (edge-id r) x) true)] (ekeep-row f r d ys (hf r) p))
           (fn [r :- EdgeRow, p :- (= (sd-row d ys r) true), q :- (= (Nat.beq (edge-id r) x) false)] p) es h))
  (exact (count-upd-mono EdgeRow edge-id x f (em-other d) (fn [r :- EdgeRow, p :- (= (em-other d (f r)) true)] (ekeep-cnt f r d (hf r) p)) es)))

(a/theorem es-nm-del [x :- Nat, es :- (List EdgeRow)] (es-nm es (tbl-del edge-id x es))
  (simp only [es-nm])
  (intros d ys)
  (apply And.intro)
  (intro h)
  (exact (tbl-all-del EdgeRow edge-id x (sd-row d ys) (sd-row d ys)
           (fn [r :- EdgeRow, p :- (= (sd-row d ys r) true), q :- (= (Nat.beq (edge-id r) x) false)] p) es h))
  (exact (tbl-count-del-le EdgeRow edge-id x (em-other d) es)))

(a/theorem es-nm-filter [q :- (=> EdgeRow Bool), es :- (List EdgeRow)] (es-nm es (tbl-filter q es))
  (simp only [es-nm])
  (intros d ys)
  (apply And.intro)
  (intro h)
  (exact (tbl-all-filter EdgeRow (sd-row d ys) q es h))
  (exact (tbl-count-filter-le EdgeRow q (em-other d) es)))

;; ---- the edits of a settle mark no edge

(a/theorem ekeep-phase [p :- Nat] (forall [e :- EdgeRow] (= (ekeep (edge-set-phase p) e) true))
  (intro e) (cases hm (:marked e)) (all_goals (simp [ekeep edge-set-phase hm Nat.beq_refl])))
(a/theorem ekeep-rearm [v :- Nat, ver :- Nat] (forall [e :- EdgeRow] (= (ekeep (edge-rearm v ver) e) true))
  (intro e) (cases hm (:marked e)) (all_goals (simp [ekeep edge-rearm hm Nat.beq_refl])))
(a/theorem ekeep-seen [n :- Nat] (forall [e :- EdgeRow] (= (ekeep (edge-set-seen n) e) true))
  (intro e) (cases hm (:marked e)) (all_goals (simp [ekeep edge-set-seen hm Nat.beq_refl])))
(a/theorem ekeep-unmark [] (forall [e :- EdgeRow] (= (ekeep (edge-set-marked false) e) true))
  (intro e) (simp [ekeep edge-set-marked Nat.beq_refl]))

(a/theorem nm-edge-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow), hf :- (forall [e :- EdgeRow] (= (ekeep f e) true))]
  (es-nm (:edges w) (:edges (edge-upd w x f)))
  (exact (es-nm-upd x f hf (:edges w))))

(a/theorem nm-remove-edge [w :- World, x :- Nat] (es-nm (:edges w) (:edges (remove-edge w x)))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact (es-nm-refl _)))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact (es-nm-del x (:edges w))))
    (case [true] (simp only [remove-edge hf hm]) (exact (es-nm-del x (:edges w))))))

(a/theorem nm-unmark-edge [w :- World, x :- Nat] (es-nm (:edges w) (:edges (unmark-edge w x)))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact (es-nm-refl _)))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact (es-nm-refl _)))
    (case [true] (simp only [unmark-edge hf hm]) (exact (nm-edge-upd w x (edge-set-marked false) ekeep-unmark)))))

(a/theorem nm-invalidate [w :- World, e :- EdgeRow] (es-nm (:edges w) (:edges (invalidate w e)))
  (simp only [invalidate]) (exact (nm-edge-upd w (:id e) (edge-set-phase ph-fired) (ekeep-phase ph-fired))))

(a/theorem nm-dep-consumed [w :- World, e :- EdgeRow] (es-nm (:edges w) (:edges (dep-consumed w e)))
  (cases hf (deb-final w (:debtor e)))
  (case [false] (simp only [dep-consumed hf])
    (exact (nm-edge-upd w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
             (ekeep-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e))))))
  (case [true] (simp only [dep-consumed hf]) (exact (nm-remove-edge w (:id e)))))

(a/theorem nm-drop-act [w :- World, a :- Nat] (es-nm (:edges w) (:edges (drop-act w a)))
  (exact (es-nm-filter (cred-ne a) (:edges w))))

(a/theorem nm-resume [w :- World, a :- ActRow] (es-nm (:edges w) (:edges (resume w a)))
  (exact (nm-drop-act w (:id a))))

(a/theorem nm-fill-slot [w :- World, a :- ActRow, x :- Nat, v :- RunResult] (es-nm (:edges w) (:edges (fill-slot w a x v)))
  (cases hm (act-ready (act-fill x v a)))
  (case [false] (simp only [fill-slot hm]) (exact (es-nm-refl _)))
  (case [true] (simp only [fill-slot hm]) (exact (nm-resume w a))))

(a/theorem nm-deliver-dep [w :- World, e :- EdgeRow, a :- ActRow] (es-nm (:edges w) (:edges (deliver-dep w e a)))
  (simp only [deliver-dep])
  (exact (es-nm-trans _ _ _ (nm-dep-consumed w e) (nm-fill-slot (dep-consumed w e) a (:id e) (deb-result w (:debtor e))))))

(a/theorem nm-fire-dep [w :- World, e :- EdgeRow] (es-nm (:edges w) (:edges (fire-dep w e)))
  (cases ha (act-with-member (:id e) (:acts w)))
  (case [none] (simp only [fire-dep ha]) (exact (nm-invalidate w e)))
  (case [some a]
    (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
    (case [false] (simp only [fire-dep ha hc]) (exact (nm-invalidate w e)))
    (case [true] (simp only [fire-dep ha hc]) (exact (nm-deliver-dep w e a)))))

(a/theorem nm-fire-wait [res :- RunResult, w :- World, e :- EdgeRow] (es-nm (:edges w) (:edges (fire-wait res w e)))
  (cases hz (Nat.beq (:creditor e) 0))
  (case [true] (simp only [fire-wait hz]) (exact (nm-remove-edge w (:id e))))
  (case [false]
    (simp only [fire-wait hz])
    (have u := (nm-edge-upd w (:id e) (edge-set-phase ph-fired) (ekeep-phase ph-fired)))
    (cases ha (act-find w (:creditor e)))
    (case [none] (simp only [fire-wait-act ha]) (exact u))
    (case [some a]
      (cases hc (run-current w (:run a)))
      (case [false] (simp only [fire-wait-act ha hc]) (exact u))
      (case [true] (simp only [fire-wait-act ha hc])
        (exact (es-nm-trans _ _ _ u (nm-fill-slot (edge-upd w (:id e) (edge-set-phase ph-fired)) a (:id e) res)))))))

(a/theorem nm-fire-observe [w :- World, e :- EdgeRow] (es-nm (:edges w) (:edges (fire-observe w e)))
  (cases hn (observe-new e (deb-version w (:debtor e))))
  (case [false] (simp only [fire-observe hn]) (exact (es-nm-refl _)))
  (case [true] (simp only [fire-observe hn])
    (exact (nm-edge-upd w (:id e) (edge-set-seen (deb-version w (:debtor e))) (ekeep-seen (deb-version w (:debtor e)))))))

(a/theorem nm-fire-edge [res :- RunResult, w :- World, x :- Nat] (es-nm (:edges w) (:edges (fire-edge res w x)))
  (cases hf (edge-find w x))
  (case [none] (simp only [fire-edge hf]) (exact (es-nm-refl _)))
  (case [some e]
    (cases hp (Nat.beq (:phase e) ph-armed))
    (case [false] (simp only [fire-edge hf hp]) (exact (es-nm-refl _)))
    (case [true]
      (cases k1 (Nat.beq (:kind e) ek-dep))
      (case [true] (simp only [fire-edge hf hp k1]) (exact (nm-fire-dep w e)))
      (case [false]
        (cases k2 (Nat.beq (:kind e) ek-wait))
        (case [true] (simp only [fire-edge hf hp k1 k2]) (exact (nm-fire-wait res w e)))
        (case [false]
          (cases k3 (Nat.beq (:kind e) ek-observe))
          (case [true] (simp only [fire-edge hf hp k1 k2 k3]) (exact (nm-fire-observe w e)))
          (case [false] (simp only [fire-edge hf hp k1 k2 k3 fire-savepoint-todo]) (exact (es-nm-refl _))))))))

(a/theorem nm-nat-fold [f :- (=> World Nat World), hf :- (forall [w :- World, x :- Nat] (es-nm (:edges w) (:edges (f w x)))), xs :- (List Nat)]
  (forall [w :- World] (es-nm (:edges w) (:edges (nat-fold f w xs))))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold]) (exact (es-nm-refl _)))
  (case [cons h t ih] (intro w) (simp only [nat-fold]) (exact (es-nm-trans _ _ _ (hf w h) (ih (f w h))))))

(a/theorem nm-settle-host [w :- World, d :- Nat] (es-nm (:edges w) (:edges (settle-host w d)))
  (simp only [settle-host])
  (exact (nm-nat-fold (fire-edge (deb-result w d)) (fn [w1 :- World, x :- Nat] (nm-fire-edge (deb-result w d) w1 x)) _ w)))

;; the fire part of a settle-edge
(a/defn settle-fire [ver :- Nat, w :- World, e :- EdgeRow] World
  (if (Nat.beq (:phase e) ph-armed) (if (Bool.or (edge-behind ver e) (member-current w e)) (fire-dep w e) w) w))
(a/theorem nm-settle-fire [ver :- Nat, w :- World, e :- EdgeRow] (es-nm (:edges w) (:edges (settle-fire ver w e)))
  (cases hp (Nat.beq (:phase e) ph-armed))
  (case [false] (simp only [settle-fire hp]) (exact (es-nm-refl _)))
  (case [true]
    (cases hc (Bool.or (edge-behind ver e) (member-current w e)))
    (case [false] (simp only [settle-fire hp hc]) (exact (es-nm-refl _)))
    (case [true] (simp only [settle-fire hp hc]) (exact (nm-fire-dep w e)))))
(a/theorem inv-settle-fire [ver :- Nat, w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (inv-sample (settle-fire ver w e)) true))
  (intro h)
  (cases hp (Nat.beq (:phase e) ph-armed))
  (case [false] (simp only [settle-fire hp]) (exact h))
  (case [true]
    (cases hc (Bool.or (edge-behind ver e) (member-current w e)))
    (case [false] (simp only [settle-fire hp hc]) (exact h))
    (case [true] (simp only [settle-fire hp hc]) (exact (inv-fire-dep w e h)))))
(a/theorem settle-edge-eq [changed :- Bool, ver :- Nat, w :- World, x :- Nat, e :- EdgeRow]
  (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (settle-edge changed ver w x) (unmark-edge (settle-fire ver w e) x)))
  (intro hf) (simp only [settle-edge hf settle-fire]))

(a/theorem nm-settle-edge [changed :- Bool, ver :- Nat, w :- World, x :- Nat] (es-nm (:edges w) (:edges (settle-edge changed ver w x)))
  (cases hf (edge-find w x))
  (case [none] (simp only [settle-edge hf]) (exact (es-nm-refl _)))
  (case [some e]
    (have se := (settle-edge-eq changed ver w x e hf)) (simp only [se])
    (exact (es-nm-trans _ _ _ (nm-settle-fire ver w e) (nm-unmark-edge (settle-fire ver w e) x)))))

;; ---- a settle-edge of x leaves no marked out-edge of d with id x

(a/theorem sd-row-drop [d :- Nat, x :- Nat, ys :- (List Nat), e :- EdgeRow]
  (=> (= (sd-row d (List.cons Nat x ys) e) true) (= (Nat.beq (:id e) x) false) (= (sd-row d ys e) true))
  (intros h hb) (simp only [sd-row reach-mem-cons hb Bool.false_or] at h) (simp only [sd-row]) (exact h))

(a/theorem sd-row-unm [d :- Nat, ys :- (List Nat), e :- EdgeRow] (=> (= (:marked e) false) (= (sd-row d ys e) true))
  (intro h) (simp only [sd-row out-marked h Bool.and_false Bool.not_false Bool.true_or]))

(a/theorem find-none-ne [x :- Nat, es :- (List EdgeRow), e :- EdgeRow]
  (=> (= (tbl-find edge-id x es) (Option.none EdgeRow)) (List.Mem e es) (= (Nat.beq (:id e) x) false))
  (induction es)
  (case [nil] (intros h m) (cases m))
  (case [cons h t ih]
    (intros hf m)
    (cases hx (Nat.beq (edge-id h) x))
    (case [true] (simp [tbl-find hx] at hf))
    (case [false]
      (simp only [tbl-find hx] at hf)
      (cases m)
      (case [head] (exact hx))
      (case [tail m2] (exact (ih hf m2))))))

(a/theorem l5-edge-nodup [w :- World] (=> (= (inv-sample w) true) (= (nat-nodup (tbl-ids edge-id (:edges w))) true))
  (intro h)
  (have p := (And.right (And.right (inv-parts w h))))
  (simp only [ids-ok Bool.and_eq_true] at p)
  (have q := (ids-unique-edges w (And.left p)))
  (simp only [edge-ids-nodup] at q)
  (exact q))

(a/theorem sd-unmark [w :- World, x :- Nat, d :- Nat, ys :- (List Nat)]
  (=> (= (inv-sample w) true) (= (tbl-all (sd-row d (List.cons Nat x ys)) (:edges w)) true)
      (= (tbl-all (sd-row d ys) (:edges (unmark-edge w x))) true))
  (intros hs h)
  (cases hf (edge-find w x))
  (case [none]
    (simp only [unmark-edge hf])
    (apply (all-of-mem EdgeRow _ (:edges w)))
    (intros e m)
    (exact (sd-row-drop d x ys e (tbl-all-mem EdgeRow _ e _ h m) (find-none-ne x (:edges w) e hf m))))
  (case [some e1]
    (cases hm (:marked e1))
    (case [true]
      (simp only [unmark-edge hf hm])
      (exact (tbl-all-upd EdgeRow edge-id x (edge-set-marked false) (sd-row d (List.cons Nat x ys)) (sd-row d ys)
               (fn [r :- EdgeRow, p :- (= (sd-row d (List.cons Nat x ys) r) true), q :- (= (Nat.beq (edge-id r) x) true)]
                 (sd-row-unm d ys (edge-set-marked false r) (Eq.refl false)))
               (fn [r :- EdgeRow, p :- (= (sd-row d (List.cons Nat x ys) r) true), q :- (= (Nat.beq (edge-id r) x) false)]
                 (sd-row-drop d x ys r p q))
               (:edges w) h)))
    (case [false]
      (simp only [unmark-edge hf hm])
      (have m1 := (tbl-find-mem EdgeRow edge-id x e1 (:edges w) hf))
      (have i1 := (tbl-find-id EdgeRow edge-id x e1 (:edges w) hf))
      (have hq (= (Bool.not (:marked e1)) true)) (simp only [hm Bool.not_false])
      (have u := (uniq-all EdgeRow edge-id (fn [r :- EdgeRow] (Bool.not (:marked r))) e1 (:edges w) (l5-edge-nodup w hs) m1 hq))
      (rw [i1] at u)
      (apply (all-of-mem EdgeRow _ (:edges w)))
      (intros e m)
      (have a := (tbl-all-mem EdgeRow _ e _ u m))
      (simp only [same-id-then Bool.or_eq_true] at a)
      (cases a)
      (case [inl b] (exact (sd-row-drop d x ys e (tbl-all-mem EdgeRow _ e _ h m) (bnot-true _ b))))
      (case [inr b] (exact (sd-row-unm d ys e (bnot-true _ b)))))))

(a/theorem sd-settle-edge [changed :- Bool, ver :- Nat, w :- World, x :- Nat, d :- Nat, ys :- (List Nat)]
  (=> (= (inv-sample w) true) (= (tbl-all (sd-row d (List.cons Nat x ys)) (:edges w)) true)
      (= (tbl-all (sd-row d ys) (:edges (settle-edge changed ver w x))) true))
  (intros hs h)
  (cases hf (edge-find w x))
  (case [none]
    (simp only [settle-edge hf])
    (apply (all-of-mem EdgeRow _ (:edges w)))
    (intros e m)
    (exact (sd-row-drop d x ys e (tbl-all-mem EdgeRow _ e _ h m) (find-none-ne x (:edges w) e hf m))))
  (case [some e]
    (have se := (settle-edge-eq changed ver w x e hf)) (simp only [se])
    (have n := (nm-settle-fire ver w e))
    (simp only [es-nm] at n)
    (exact (sd-unmark (settle-fire ver w e) x d ys (inv-settle-fire ver w e hs) ((And.left (n d (List.cons Nat x ys))) h)))))

(a/theorem sd-fold [changed :- Bool, ver :- Nat, d :- Nat, xs :- (List Nat)]
  (forall [w :- World] (=> (= (inv-sample w) true) (= (tbl-all (sd-row d xs) (:edges w)) true)
                           (= (tbl-all (sd-row d (List.nil Nat)) (:edges (nat-fold (settle-edge changed ver) w xs))) true)))
  (induction xs)
  (case [nil] (intros w hs h) (simp only [nat-fold]) (exact h))
  (case [cons x t ih]
    (intros w hs h)
    (simp only [nat-fold])
    (exact (ih (settle-edge changed ver w x) (inv-settle-edge changed ver w x hs) (sd-settle-edge changed ver w x d t hs h)))))

(a/theorem scan-mem-dep [d :- Nat, es :- (List EdgeRow), e :- EdgeRow]
  (=> (List.Mem e es) (= (out-dep d e) true) (= (reach-mem (:id e) (tbl-scan edge-id (out-dep d) es)) true))
  (induction es)
  (case [nil] (intros m h) (cases m))
  (case [cons h t ih]
    (intros m ho)
    (cases m)
    (case [head] (simp only [tbl-scan ho reach-mem-cons edge-id Nat.beq_refl Bool.true_or]))
    (case [tail m2]
      (have r := (ih m2 ho))
      (cases hp (out-dep d h))
      (case [false] (simp only [tbl-scan hp]) (exact r))
      (case [true] (simp only [tbl-scan hp reach-mem-cons r Bool.or_true])))))

(a/theorem sd-init [d :- Nat, es :- (List EdgeRow)] (= (tbl-all (sd-row d (tbl-scan edge-id (out-dep d) es)) es) true)
  (apply (all-of-mem EdgeRow _ es))
  (intros e m)
  (cases ho (out-dep d e))
  (case [false] (simp only [sd-row out-marked ho Bool.false_and Bool.not_false Bool.true_or]))
  (case [true] (simp only [sd-row (scan-mem-dep d es e m ho) Bool.or_true])))

(a/theorem sd-zero [d :- Nat, es :- (List EdgeRow)]
  (=> (= (tbl-all (sd-row d (List.nil Nat)) es) true) (= (tbl-count (out-marked d) es) 0))
  (intro h)
  (apply (count-zero EdgeRow (out-marked d) es))
  (intros e m)
  (have r := (tbl-all-mem EdgeRow _ e _ h m))
  (simp only [sd-row reach-mem Bool.or_false] at r)
  (exact (bnot-true _ r)))

(a/theorem sd-split [d :- Nat, es :- (List EdgeRow)]
  (= (tbl-count sd-marked es) (+ (tbl-count (em-other d) es) (tbl-count (out-marked d) es)))
  (induction es)
  (case [nil] (simp [tbl-count]))
  (case [cons h t ih]
    (simp only [tbl-count-cons])
    (cases hm (:marked h))
    (case [false] (simp only [sd-marked em-other out-marked hm Bool.false_and Bool.and_false b2n]) (omega))
    (case [true]
      (cases ho (out-dep d h))
      (case [false] (simp only [sd-marked em-other out-marked hm ho Bool.not_false Bool.and_true Bool.false_and b2n]) (omega))
      (case [true] (simp only [sd-marked em-other out-marked hm ho Bool.not_true Bool.and_false Bool.and_true b2n]) (omega)))))

;; ---- the potential drops with every pop

(a/theorem sd-pop [w :- World, d :- Nat, changed :- Bool]
  (=> (= (inv-sample w) true)
      (<= (+ (tbl-count sd-marked (:edges (settle-one w d changed))) (tbl-count (out-marked d) (:edges w)))
          (tbl-count sd-marked (:edges w))))
  (intro hs)
  (simp only [settle-one])
  (have n1 := (nm-nat-fold (settle-edge changed (deb-version w d)) (fn [w1 :- World, x :- Nat] (nm-settle-edge changed (deb-version w d) w1 x))
                (tbl-scan edge-id (out-dep d) (:edges w)) w))
  (have n2 := (nm-settle-host (nat-fold (settle-edge changed (deb-version w d)) w (tbl-scan edge-id (out-dep d) (:edges w))) d))
  (have s1 := (sd-fold changed (deb-version w d) d (tbl-scan edge-id (out-dep d) (:edges w)) w hs (sd-init d (:edges w))))
  (simp only [es-nm] at n1 n2)
  (have s2 := ((And.left (n2 d (List.nil Nat))) s1))
  (have z := (sd-zero d _ s2))
  (have c1 := (And.right (n1 d (List.nil Nat))))
  (have c2 := (And.right (n2 d (List.nil Nat))))
  (have p1 := (sd-split d (:edges w)))
  (have p2 := (sd-split d (:edges (settle-host (nat-fold (settle-edge changed (deb-version w d)) w (tbl-scan edge-id (out-dep d) (:edges w))) d))))
  (omega))

(a/theorem filter-len-le [p :- (=> Nat Bool), xs :- (List Nat)] (<= (List.length (tbl-filter p xs)) (List.length xs))
  (induction xs)
  (case [nil] (simp [tbl-filter]))
  (case [cons h t ih] (cases hp (p h)) (all_goals (simp only [tbl-filter hp List.length])) (omega) (omega)))

(a/theorem count-le-len [A :- Type, p :- (=> A Bool), xs :- (List A)] (<= (tbl-count p xs) (List.length xs))
  (induction xs)
  (case [nil] (simp [tbl-count]))
  (case [cons h t ih] (simp only [tbl-count-cons List.length]) (cases hp (p h)) (all_goals (simp only [hp b2n])) (omega) (omega)))

(a/theorem ids-len [A :- Type, idf :- (=> A Nat), xs :- (List A)] (= (List.length (tbl-ids idf xs)) (List.length xs))
  (induction xs)
  (case [nil] (simp [tbl-ids]))
  (case [cons h t ih] (simp only [tbl-ids List.length ih])))

(a/theorem next-len [w :- World, w2 :- World, d :- Nat]
  (<= (List.length (settle-next w w2 d)) (tbl-count (out-marked d) (:edges w)))
  (simp only [settle-next])
  (have a := (filter-len-le (ready-id w2) (tbl-scan edge-cred (out-marked d) (:edges w))))
  (have b := (scan-length-eq EdgeRow edge-cred (out-marked d) (:edges w)))
  (omega))

(a/theorem settle-loop-done [fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)]
    (=> (= (inv-sample w) true) (< (+ (List.length q) (tbl-count sd-marked (:edges w))) (List.length fuel))
        (= (:rest (settle-loop fuel w q)) (List.nil Nat))))
  (induction fuel)
  (case [nil] (intros w q hs hl) (simp only [List.length] at hl) (omega))
  (case [cons h f ih]
    (intros w q hs hl)
    (cases q)
    (case [nil] (simp only [settle-loop]))
    (case [cons d t]
      (simp only [settle-loop])
      (have p := (sd-pop w d false hs))
      (have n := (next-len w (settle-one w d false) d))
      (have l1 := (list-length-append t (settle-next w (settle-one w d false) d)))
      (simp only [List.length] at hl)
      (apply (ih (settle-one w d false) (List.append Nat t (settle-next w (settle-one w d false) d)) (inv-settle-one w d false hs)))
      (omega))))

(a/theorem by-settle-bound [w :- World, d :- Nat, changed :- Bool]
  (=> (<= (+ (tbl-count sd-marked (:edges (settle-one w d changed))) (tbl-count (out-marked d) (:edges w))) (tbl-count sd-marked (:edges w)))
      (<= (List.length (settle-next w (settle-one w d changed) d)) (tbl-count (out-marked d) (:edges w)))
      (<= (tbl-count sd-marked (:edges w)) (List.length (:edges w)))
      (= (List.length (tbl-ids edge-id (:edges w))) (List.length (:edges w)))
      (< (+ (List.length (settle-next w (settle-one w d changed) d)) (tbl-count sd-marked (:edges (settle-one w d changed))))
         (List.length (settle-fuel w))))
  (intros p n c i) (simp only [settle-fuel List.length]) (omega))

;; Theorem: the settle worklist empties within its fuel (the former honest flag `settle-done`)
(a/theorem settle-done-ok [w :- World, d :- Nat, changed :- Bool]
  (=> (= (inv-sample w) true) (= (settle-done w d changed) true))
  (intro hs)
  (have p := (sd-pop w d changed hs))
  (have n := (next-len w (settle-one w d changed) d))
  (have c := (count-le-len EdgeRow sd-marked (:edges w)))
  (have i := (ids-len EdgeRow edge-id (:edges w)))
  (have L := (settle-loop-done (settle-fuel w) (settle-one w d changed) (settle-next w (settle-one w d changed) d)
               (inv-settle-one w d changed hs)
               (by-settle-bound w d changed p n c i)))
  (simp only [settle-done settle-res L]))
