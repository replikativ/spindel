(ns spindel.v2.hm3
  "h-mem2 through `world-step` (P11, second half), kernel-checked (Init only). IN PROGRESS: the bundle, its
  transfer and primitive lemmas, the copier setup, the first fire overrides and the derivation of h-mem2 are
  proved; the step theorem is not (notes/PLAN.md, branch hm3, lists the remaining overrides).

  Bundle `h3 xm` = inv-sample && for every activation A and every run row R with id A.run (key rk3 = id/of/epoch):
    ab    A.run < next-id;
    ao    R.of < next-id;  e1a  R.epoch <= C.epoch for every computation row C with id R.of (i10's E1);
    ob    unless R.of is exempt (in xm), when a row C with id R.of has C.epoch <= R.epoch (R is C's current run):
          C's rows have done-epoch < epoch (`h3-cs`), and every member x of A is exempt by id or names an edge,
          and every edge E with id x is
            structural (`h3-s`): armed, a dep edge's creditor is R.of, another kind's creditor is A, and A is
              the first activation with member x (`act-with-member`: the one a fire of E reaches), and
            unless E's debtor is exempt (`h3-m`): a task debtor's run is alive, a computation debtor is reached
              by a dep edge and all its rows are strongly waiting (hmk's `hk-wt`).
  The exemption list holds computation ids (an exempt computation's activations), debtor ids and member ids
  (ids are global and unique). Theorems:
    h3-h-mem2      h3 [] w, gd w -> h-mem2 w          (gd's rof: C.run names a run of C)
    h3-l5-safety   p3c w, gd w, h3 [] w, quiescent w, h-mark w, ... -> False   (L5, safety half)
  Part B: `h3-rest-rel` (transfer through any change of computations, tasks, runs, edges and allocator with the
  activations kept, given per-table conditions; free edges may change or go: `h3-free`); per-table forms and
  the primitive edits. Part C: full-bundle forms, lit's copier bundle `H3` (prefix hm3-) with the source patch.
  Part D: fires (invalidate, resume, fill-slot; exemption monotone and the undo of a free member-id exemption).
  Part F: h-mem2 and L5 from the bundle."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [clojure.walk :as walk]
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
            [spindel.v2.p3 :refer :all]
            [spindel.v2.i10 :refer :all]
            [spindel.v2.i11 :refer :all]
            [spindel.v2.i1 :refer :all]
            [spindel.v2.i8 :refer :all]
            [spindel.v2.hm :refer :all]
            [spindel.v2.progress :refer :all]
            [spindel.v2.l5 :refer :all]
            [spindel.v2.hmk :refer :all]
            [spindel.v2.i14 :refer :all]
            [spindel.v2.hmk2 :refer :all]))

;; ===========================================================================
;; Part A. The predicate
;; ===========================================================================

;; run keys: what the invariant reads of a run row (other than `alive`, read for task runs only)
(a/structure RK3 [] (id Nat) (of Nat) (epoch Nat))
(a/defn rk3 [r :- RunRow] RK3 (RK3.mk (:id r) (:of r) (:epoch r)))
;; computation row c is k.of's and k is at or above its epoch (current, given e1a)
(a/defn h3-cur [k :- RK3, c :- CompRow] Bool (Bool.and (Nat.beq (:id c) (:of k)) (Nat.ble (:epoch c) (:epoch k))))
;; e1a for one row
(a/defn h3-e1 [k :- RK3, c :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id c) (:of k))) (Nat.ble (:epoch k) (:epoch c))))
(a/defn h3-first [i :- Nat, a :- ActRow] Bool (Nat.beq (:id a) i))
;; a run row with id rid that is alive; every task row with id y has an alive run
(a/defn h3-ral [rid :- Nat, r :- RunRow] Bool (Bool.and (Nat.beq (:id r) rid) (run-alive r)))
(a/defn h3-tk [rs :- (List RunRow), y :- Nat, t :- TaskRow] Bool
  (Bool.or (Bool.not (Nat.beq (:id t) y)) (tbl-any (h3-ral (:run t)) rs)))
;; structure of a member edge (independent of the debtor's state): armed, a dep edge's creditor is the
;; run's computation, any other's the activation, and the activation is the first one with this member
(a/defn h3-s [as :- (List ActRow), a :- ActRow, k :- RK3, e :- EdgeRow] Bool
  (Bool.and (Nat.beq (:phase e) ph-armed)
   (Bool.and (Bool.or (Bool.not (Nat.beq (:kind e) ek-dep)) (Nat.beq (:creditor e) (:of k)))
    (Bool.and (Bool.or (Nat.beq (:kind e) ek-dep) (Nat.beq (:creditor e) (:id a)))
              (opt-test (h3-first (:id a)) (act-with-member (:id e) as))))))
;; the debtor of a member edge: a task's run is alive, a computation is strongly waiting (and the edge is a dep edge)
(a/defn h3-m [cs :- (List CompRow), ts :- (List TaskRow), rs :- (List RunRow), e :- EdgeRow] Bool
  (Bool.and (tbl-all (h3-tk rs (:debtor e)) ts)
            (Bool.or (Bool.not (tbl-has comp-id (:debtor e) cs))
                     (Bool.and (Nat.beq (:kind e) ek-dep) (tbl-all (hk-wif (:debtor e)) cs)))))
(a/defn h3-eok [xm :- (List Nat), w :- World, a :- ActRow, k :- RK3, x :- Nat, e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:id e) x))
    (Bool.and (h3-s (:acts w) a k e) (Bool.or (reach-mem (:debtor e) xm) (h3-m (:comps w) (:tasks w) (:runs w) e)))))
;; a member x exempt by id, or its edge exists and every edge with its id is good
(a/defn h3-x [xm :- (List Nat), w :- World, a :- ActRow, k :- RK3, x :- Nat] Bool
  (Bool.or (reach-mem x xm) (Bool.and (tbl-has edge-id x (:edges w)) (tbl-all (h3-eok xm w a k x) (:edges w)))))
;; the computation of a current run has not completed this epoch
(a/defn h3-cs [k :- RK3, c :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id c) (:of k))) (Nat.blt (:done-epoch c) (:epoch c))))
(a/defn h3-ob [xm :- (List Nat), w :- World, a :- ActRow, k :- RK3] Bool
  (Bool.or (reach-mem (:of k) xm)
    (Bool.or (Bool.not (tbl-any (h3-cur k) (:comps w)))
             (Bool.and (tbl-all (h3-cs k) (:comps w)) (tbl-all (h3-x xm w a k) (act-contrib a))))))
(a/defn h3-r [xm :- (List Nat), w :- World, a :- ActRow, k :- RK3] Bool
  (Bool.or (Bool.not (Nat.beq (:id k) (:run a)))
   (Bool.and (Nat.blt (:of k) (:next-id w)) (Bool.and (tbl-all (h3-e1 k) (:comps w)) (h3-ob xm w a k)))))
(a/defn h3-rr [xm :- (List Nat), w :- World, a :- ActRow, r :- RunRow] Bool (h3-r xm w a (rk3 r)))
(a/defn h3-a [xm :- (List Nat), w :- World, a :- ActRow] Bool
  (Bool.and (Nat.blt (:run a) (:next-id w)) (tbl-all (h3-rr xm w a) (:runs w))))
(a/defn h3-rest [xm :- (List Nat), w :- World] Bool (tbl-all (h3-a xm w) (:acts w)))
(a/defn h3 [xm :- (List Nat), w :- World] Bool (Bool.and (inv-sample w) (h3-rest xm w)))

(a/theorem h3-sample [xm :- (List Nat), w :- World] (=> (= (h3 xm w) true) (= (inv-sample w) true))
  (intro h) (simp only [h3 Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem h3-rest-of [xm :- (List Nat), w :- World] (=> (= (h3 xm w) true) (= (h3-rest xm w) true))
  (intro h) (simp only [h3 Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem h3-intro [xm :- (List Nat), w :- World] (=> (= (inv-sample w) true) (= (h3-rest xm w) true) (= (h3 xm w) true))
  (intros h1 h2) (simp only [h3 h1 h2 Bool.and_self]))
(a/theorem h3-parts [xm :- (List Nat), w :- World]
  (=> (= (h3 xm w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (h3-sample xm w h))))

;; ===========================================================================
;; Part B. Transfer: a change of the computations, tasks, runs, edges and the allocator (the
;; activations kept) that keeps what the invariant reads
;; ===========================================================================

;; an edge e2 with e's id, kind, creditor and debtor, armed when e is
(a/defn h3-ekq [e2 :- EdgeRow, e :- EdgeRow] Bool
  (Bool.and (Nat.beq (:id e) (:id e2))
   (Bool.and (Nat.beq (:kind e) (:kind e2))
    (Bool.and (Nat.beq (:creditor e) (:creditor e2))
     (Bool.and (Nat.beq (:debtor e) (:debtor e2))
               (Bool.or (Bool.not (Nat.beq (:phase e) ph-armed)) (Nat.beq (:phase e2) ph-armed)))))))
;; a run row r with r2's keys
(a/defn h3-rkq [r2 :- RunRow, r :- RunRow] Bool
  (Bool.and (Nat.beq (:id r) (:id r2)) (Bool.and (Nat.beq (:of r) (:of r2)) (Nat.beq (:epoch r) (:epoch r2)))))

(a/theorem h3-m-rel [xm :- (List Nat), w :- World, w2 :- World, e :- EdgeRow]
  (=> (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-has comp-id y (:comps w2)) true) (= (tbl-has comp-id y (:comps w)) true)))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) (:comps w)) true) (= (tbl-all (hk-wif y) (:comps w2)) true)))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true) (= (tbl-all (h3-tk (:runs w2) y) (:tasks w2)) true)))
      (< (:debtor e) (:next-id w)) (= (reach-mem (:debtor e) xm) false)
      (= (h3-m (:comps w) (:tasks w) (:runs w) e) true) (= (h3-m (:comps w2) (:tasks w2) (:runs w2) e) true))
  (intros hc1 hc4 ht hb hx h)
  (simp only [h3-m Bool.and_eq_true] at h)
  (have p3 := (ht _ hb (And.left h)))
  (have q := (And.right h))
  (have p4 (= (Bool.or (Bool.not (tbl-has comp-id (:debtor e) (:comps w2))) (Bool.and (Nat.beq (:kind e) ek-dep) (tbl-all (hk-wif (:debtor e)) (:comps w2)))) true))
  (cases hh (tbl-has comp-id (:debtor e) (:comps w2)))
  (simp only [Bool.not_false Bool.true_or])
  (simp only [(hc1 _ hb hh) Bool.not_true Bool.false_or Bool.and_eq_true] at q)
  (simp only [Bool.not_true Bool.false_or (And.left q) (hc4 _ hb hx (And.right q)) Bool.and_self])
  (simp only [h3-m p3 p4 Bool.and_self]))

(a/theorem h3-m-edge [cs :- (List CompRow), ts :- (List TaskRow), rs :- (List RunRow), e :- EdgeRow, e2 :- EdgeRow]
  (=> (= (h3-ekq e2 e) true) (= (h3-m cs ts rs e) true) (= (h3-m cs ts rs e2) true))
  (intros hq h)
  (simp only [h3-ekq Bool.and_eq_true] at hq)
  (have ek := (Nat.eq_of_beq_eq_true (And.left (And.right hq))))
  (have ed := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right (And.right hq))))))
  (simp only [h3-m] at h) (simp only [h3-m])
  (rw [← ek ← ed]) (exact h))
(a/theorem h3-s-edge [as :- (List ActRow), a :- ActRow, k :- RK3, e :- EdgeRow, e2 :- EdgeRow]
  (=> (= (h3-ekq e2 e) true) (= (h3-s as a k e) true) (= (h3-s as a k e2) true))
  (intros hq h)
  (simp only [h3-ekq Bool.and_eq_true] at hq)
  (have ei := (Nat.eq_of_beq_eq_true (And.left hq)))
  (have ek := (Nat.eq_of_beq_eq_true (And.left (And.right hq))))
  (have ec := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right hq)))))
  (have ep := (And.right (And.right (And.right (And.right hq)))))
  (simp only [h3-s Bool.and_eq_true] at h)
  (have p1 (= (Nat.beq (:phase e2) ph-armed) true))
  (simp only [(And.left h) Bool.not_true Bool.false_or] at ep) (exact ep)
  (simp only [h3-s Bool.and_eq_true p1 Bool.true_and])
  (rw [← ei ← ek ← ec])
  (exact (And.right h)))

;; ids of a table of w are below the allocator
(a/theorem h3-has-lt [A :- Type, idf :- (=> A Nat), d :- Nat, n :- Nat, xs :- (List A)]
  (=> (= (tbl-all (id-in-range n) (tbl-ids idf xs)) true) (= (tbl-has idf d xs) true) (< d n))
  (intros hr hh)
  (have hm (= (nat-mem d (tbl-ids idf xs)) true)) (rw [nat-mem-ids]) (exact hh)
  (have r := (all-nat-mem (id-in-range n) d _ hr hm))
  (simp only [id-in-range Bool.and_eq_true Nat.blt_eq] at r)
  (exact (And.right r)))
(a/theorem h3-deb-below0 [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))
  (intros h hm)
  (have ho := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                (And.left (And.right (inv-parts w h))) hm))
  (simp only [edge-ok deb-ok Bool.and_eq_true Bool.or_eq_true] at ho)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (have hdo := (And.right ho))
  (cases hdo)
  (case [inl h1] (exact (h3-has-lt CompRow comp-id (:debtor e) (:next-id w) (:comps w) (And.left (And.right hb)) h1)))
  (case [inr h2]
    (cases h2)
    (case [inl h3] (exact (h3-has-lt TaskRow task-id (:debtor e) (:next-id w) (:tasks w) (And.left (And.right (And.right hb))) h3)))
    (case [inr h4]
      (cases h4)
      (case [inl h5] (exact (h3-has-lt SourceRow source-id (:debtor e) (:next-id w) (:sources w)
                              (And.left (And.right (And.right (And.right (And.right hb))))) h5)))
      (case [inr h6] (exact (h3-has-lt ResRow resource-id (:debtor e) (:next-id w) (:res w)
                              (And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right hb)))))))) (And.right h6)))))))

;; an edge of w has a debtor below the allocator
(a/theorem h3-deb-below [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))
  (intros hs me)
  (exact (h3-deb-below0 w e hs me)))
(a/theorem h3-db-of [w :- World] (=> (= (inv-sample w) true) (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))))
  (intros hs e me) (exact (h3-deb-below0 w e hs me)))


;; ---- edge removals: the removed ids are no member of a current, non-exempt activation
(a/defn h3-fr [xm :- (List Nat), w :- World, x :- Nat, a :- ActRow, r :- RunRow] Bool
  (Bool.or (Bool.not (Nat.beq (:id r) (:run a)))
   (Bool.or (reach-mem (:of r) xm)
    (Bool.or (Bool.not (tbl-any (h3-cur (rk3 r)) (:comps w)))
     (Bool.or (Bool.not (reach-mem x (act-contrib a))) (reach-mem x xm))))))
(a/defn h3-fa [xm :- (List Nat), w :- World, x :- Nat, a :- ActRow] Bool (tbl-all (h3-fr xm w x a) (:runs w)))
(a/defn h3-free [xm :- (List Nat), w :- World, x :- Nat] Bool (tbl-all (h3-fa xm w x) (:acts w)))

(a/theorem h3-free-use [xm :- (List Nat), w :- World, x :- Nat, a :- ActRow, r :- RunRow]
  (=> (= (h3-free xm w x) true) (List.Mem a (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run a))
      (= (reach-mem (:of (rk3 r)) xm) false) (= (tbl-any (h3-cur (rk3 r)) (:comps w)) true) (= (reach-mem x (act-contrib a)) true)
      (= (reach-mem x xm) false) False)
  (intros hf ma mr ir hx hc hm hxx)
  (have q := (tbl-all-mem RunRow _ r (:runs w) (tbl-all-mem ActRow _ a (:acts w) hf ma) mr))
  (have ir2 (= (Nat.beq (:id r) (:run a)) true)) (rw [ir]) (exact (Nat.beq_refl _))
  (have hx2 (= (reach-mem (:of r) xm) false)) (exact hx)
  (simp only [h3-fr ir2 hx2 hc hm hxx Bool.not_true Bool.false_or] at q)
  (cases q))


(a/theorem h3-eok-rel [xm :- (List Nat), w :- World, w2 :- World, a :- ActRow, k :- RK3, x :- Nat, e :- EdgeRow]
  (=> (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-has comp-id y (:comps w2)) true) (= (tbl-has comp-id y (:comps w)) true)))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) (:comps w)) true) (= (tbl-all (hk-wif y) (:comps w2)) true)))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true) (= (tbl-all (h3-tk (:runs w2) y) (:tasks w2)) true)))
      (= (:acts w2) (:acts w))
      (< (:debtor e) (:next-id w))
      (= (h3-eok xm w a k x e) true) (= (h3-eok xm w2 a k x e) true))
  (intros hc1 hc4 ht ha hb h)
  (simp only [h3-eok Bool.or_eq_true Bool.and_eq_true] at h)
  (simp only [h3-eok Bool.or_eq_true Bool.and_eq_true])
  (cases h)
  (case [inl q] (exact (Or.inl q)))
  (case [inr q]
    (apply Or.inr)
    (apply And.intro) (rw [ha]) (exact (And.left q))
    (have q2 := (And.right q))
    (cases q2)
    (case [inl z] (exact (Or.inl z)))
    (case [inr z]
      (cases hx (reach-mem (:debtor e) xm))
      (case [false] (apply Or.inr)
        (exact (h3-m-rel xm w w2 e hc1 hc4 ht hb hx z)))
      (case [true] (exact (Or.inl (rfl)))))))

(a/theorem h3-eok-edge [xm :- (List Nat), w :- World, a :- ActRow, k :- RK3, x :- Nat, e :- EdgeRow, e2 :- EdgeRow]
  (=> (= (h3-ekq e2 e) true) (= (h3-eok xm w a k x e) true) (= (h3-eok xm w a k x e2) true))
  (intros hq h)
  (have hq2 := hq)
  (simp only [h3-ekq Bool.and_eq_true] at hq2)
  (have ei := (Nat.eq_of_beq_eq_true (And.left hq2)))
  (have ed := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right (And.right hq2))))))
  (simp only [h3-eok Bool.or_eq_true Bool.and_eq_true] at h)
  (simp only [h3-eok Bool.or_eq_true Bool.and_eq_true])
  (rw [← ei ← ed])
  (cases h)
  (case [inl q] (exact (Or.inl q)))
  (case [inr q]
    (apply Or.inr)
    (apply And.intro) (exact (h3-s-edge (:acts w) a k e e2 hq (And.left q)))
    (have q2 := (And.right q))
    (cases q2)
    (case [inl z] (exact (Or.inl z)))
    (case [inr z] (exact (Or.inr (h3-m-edge _ _ _ e e2 hq z))))))

(a/theorem h3-x-rel [xm :- (List Nat), w :- World, w2 :- World, a :- ActRow, k :- RK3, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w))))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-has comp-id y (:comps w2)) true) (= (tbl-has comp-id y (:comps w)) true)))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) (:comps w)) true) (= (tbl-all (hk-wif y) (:comps w2)) true)))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true) (= (tbl-all (h3-tk (:runs w2) y) (:tasks w2)) true)))
      (= (:acts w2) (:acts w))
      (forall [y :- Nat] (=> (= (tbl-has edge-id y (:edges w)) true) (Or (= (tbl-has edge-id y (:edges w2)) true) (= (h3-free xm w y) true))))
      (forall [e2 :- EdgeRow] (=> (List.Mem e2 (:edges w2))
        (Or (= (tbl-has edge-id (:id e2) (:edges w)) false) (Or (= (tbl-any (h3-ekq e2) (:edges w)) true) (= (h3-free xm w (:id e2)) true)))))
      (=> (= (reach-mem x xm) false) (= (h3-free xm w x) true) False)
      (= (h3-x xm w a k x) true) (= (h3-x xm w2 a k x) true))
  (intros hs hc1 hc4 ht ha hef heb hnf0 h0)
  (simp only [h3-x Bool.or_eq_true Bool.and_eq_true] at h0)
  (simp only [h3-x Bool.or_eq_true Bool.and_eq_true])
  (cases hxx (reach-mem x xm))
  (case [true] (exact (Or.inl (rfl))))
  (have hnf := (hnf0 hxx))
  (cases h0)
  (case [inl z] (rw [hxx] at z) (cases z))
  (rename_i h)
  (apply Or.inr)
  (apply And.intro)
  (have k1 := (hef x (And.left h)))
  (cases k1) (case [inl z] (exact z)) (case [inr z] (exact (False.elim (hnf z))))
  (apply all-of-mem)
  (intros e2 m2)
  (cases hi (Nat.beq (:id e2) x))
  (simp only [h3-eok hi Bool.not_false Bool.true_or])
  (have hb := (heb e2 m2))
  (have ex := (Nat.eq_of_beq_eq_true hi))
  (cases hb)
  (rename_i z) (rw [ex] at z) (rw [(And.left h)] at z) (cases z)
  (rename_i z)
  (cases z)
  (rename_i z)
  (apply (any-elim EdgeRow (h3-ekq e2) _ (:edges w) z))
  (intros e me hq)
  (have h1 := (tbl-all-mem EdgeRow _ e (:edges w) (And.right h) me))
  (have h2 := (h3-eok-rel xm w w2 a k x e hc1 hc4 ht ha (hs e me) h1))
  (exact (h3-eok-edge xm w2 a k x e e2 hq h2))
  (rename_i z) (rw [ex] at z) (exact (False.elim (hnf z))))

(a/theorem h3-r-rel [xm :- (List Nat), w :- World, w2 :- World, a :- ActRow, r :- RunRow]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w))))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-has comp-id y (:comps w2)) true) (= (tbl-has comp-id y (:comps w)) true)))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) (:comps w)) true) (= (tbl-all (hk-wif y) (:comps w2)) true)))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true) (= (tbl-all (h3-tk (:runs w2) y) (:tasks w2)) true)))
      (= (:acts w2) (:acts w))
      (forall [y :- Nat] (=> (= (tbl-has edge-id y (:edges w)) true) (Or (= (tbl-has edge-id y (:edges w2)) true) (= (h3-free xm w y) true))))
      (forall [e2 :- EdgeRow] (=> (List.Mem e2 (:edges w2))
        (Or (= (tbl-has edge-id (:id e2) (:edges w)) false) (Or (= (tbl-any (h3-ekq e2) (:edges w)) true) (= (h3-free xm w (:id e2)) true)))))
      (<= (:next-id w) (:next-id w2))
      (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-e1 k2) (:comps w)) true) (= (tbl-all (h3-e1 k2) (:comps w2)) true)))
      (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-any (h3-cur k2) (:comps w2)) true) (= (tbl-any (h3-cur k2) (:comps w)) true)))
      (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-cs k2) (:comps w)) true) (= (tbl-all (h3-cs k2) (:comps w2)) true)))
      (List.Mem a (:acts w)) (List.Mem r (:runs w))
      (= (h3-r xm w a (rk3 r)) true) (= (h3-r xm w2 a (rk3 r)) true))
  (intros hs hc1 hc4 ht ha hef heb hn hc2 hc3 hc5 ma mr h)
  (cases hi (Nat.beq (:id (rk3 r)) (:run a)))
  (case [false] (simp only [h3-r hi Bool.not_false Bool.true_or]))
  (case [true]
    (have ir (= (:id r) (:run a))) (exact (Nat.eq_of_beq_eq_true hi))
    (simp only [h3-r hi Bool.not_true Bool.false_or Bool.and_eq_true] at h)
    (simp only [h3-r hi Bool.not_true Bool.false_or Bool.and_eq_true])
    (have o1 := (gd-lt-of _ _ (And.left h)))
    (apply And.intro) (exact (gd-blt-of _ _ (Nat.lt_of_lt_of_le o1 hn)))
    (apply And.intro) (exact (hc2 (rk3 r) o1 (And.left (And.right h))))
    (have ob := (And.right (And.right h)))
    (simp only [h3-ob Bool.or_eq_true Bool.and_eq_true] at ob)
    (simp only [h3-ob Bool.or_eq_true Bool.and_eq_true])
    (cases hxo (reach-mem (:of (rk3 r)) xm))
    (case [true] (exact (Or.inl (rfl))))
    (case [false]
      (apply Or.inr)
      (cases hcur (tbl-any (h3-cur (rk3 r)) (:comps w2)))
      (case [false] (exact (Or.inl (rfl))))
      (case [true]
        (apply Or.inr)
        (have hcw := (hc3 (rk3 r) o1 hcur))
        (cases ob)
        (case [inl z] (rw [hxo] at z) (cases z))
        (case [inr z]
          (cases z)
          (case [inl z2] (simp only [hcw Bool.not_true] at z2) (cases z2))
          (case [inr z2]
            (apply And.intro) (exact (hc5 (rk3 r) o1 (And.left z2)))
            (have g (forall [x :- Nat] (=> (List.Mem x (act-contrib a)) (= (h3-x xm w a (rk3 r) x) true) (= (h3-x xm w2 a (rk3 r) x) true))))
            (intros x mx hx)
            (have hnf (=> (= (reach-mem x xm) false) (= (h3-free xm w x) true) False))
            (intros hxx fr) (exact (h3-free-use xm w x a r fr ma mr ir hxo hcw (Iff.mpr (reach-mem-iff x (act-contrib a)) mx) hxx))
            (exact (h3-x-rel xm w w2 a (rk3 r) x hs hc1 hc4 ht ha hef heb hnf hx))
            (exact (tbl-all-mem-mono Nat (h3-x xm w a (rk3 r)) (h3-x xm w2 a (rk3 r)) (act-contrib a) g (And.right z2)))))))))

(a/theorem h3-a-rel [xm :- (List Nat), w :- World, w2 :- World, a :- ActRow]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w))))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-has comp-id y (:comps w2)) true) (= (tbl-has comp-id y (:comps w)) true)))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) (:comps w)) true) (= (tbl-all (hk-wif y) (:comps w2)) true)))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true) (= (tbl-all (h3-tk (:runs w2) y) (:tasks w2)) true)))
      (= (:acts w2) (:acts w))
      (forall [y :- Nat] (=> (= (tbl-has edge-id y (:edges w)) true) (Or (= (tbl-has edge-id y (:edges w2)) true) (= (h3-free xm w y) true))))
      (forall [e2 :- EdgeRow] (=> (List.Mem e2 (:edges w2))
        (Or (= (tbl-has edge-id (:id e2) (:edges w)) false) (Or (= (tbl-any (h3-ekq e2) (:edges w)) true) (= (h3-free xm w (:id e2)) true)))))
      (<= (:next-id w) (:next-id w2))
      (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-e1 k2) (:comps w)) true) (= (tbl-all (h3-e1 k2) (:comps w2)) true)))
      (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-any (h3-cur k2) (:comps w2)) true) (= (tbl-any (h3-cur k2) (:comps w)) true)))
      (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-cs k2) (:comps w)) true) (= (tbl-all (h3-cs k2) (:comps w2)) true)))
      (forall [r2 :- RunRow] (=> (List.Mem r2 (:runs w2))
        (Or (= (Nat.ble (:next-id w) (:id r2)) true) (= (tbl-any (h3-rkq r2) (:runs w)) true))))
      (List.Mem a (:acts w))
      (= (h3-a xm w a) true) (= (h3-a xm w2 a) true))
  (intros hs hc1 hc4 ht ha hef heb hn hc2 hc3 hc5 hrk ma h)
  (simp only [h3-a Bool.and_eq_true] at h)
  (have a1 := (gd-lt-of _ _ (And.left h)))
  (simp only [h3-a Bool.and_eq_true])
  (apply And.intro) (exact (gd-blt-of _ _ (Nat.lt_of_lt_of_le a1 hn)))
  (apply all-of-mem)
  (intros r2 m2)
  (simp only [h3-rr])
  (cases hi (Nat.beq (:id r2) (:run a)))
  (simp only [h3-r rk3 hi Bool.not_false Bool.true_or])
  (have ei := (Nat.eq_of_beq_eq_true hi))
  (have hb := (hrk r2 m2))
  (cases hb)
  (rename_i z) (have z2 := (gd-le-of _ _ z)) (omega)
  (rename_i z)
  (apply (any-elim RunRow (h3-rkq r2) _ (:runs w) z))
  (intros r mr hq)
  (have hr := (tbl-all-mem RunRow _ r (:runs w) (And.right h) mr))
  (simp only [h3-rr] at hr)
  (simp only [h3-rkq Bool.and_eq_true] at hq)
  (have i1 := (Nat.eq_of_beq_eq_true (And.left hq)))
  (have ek (= (rk3 r) (rk3 r2)))
  (simp only [rk3 i1 (Nat.eq_of_beq_eq_true (And.left (And.right hq))) (Nat.eq_of_beq_eq_true (And.right (And.right hq)))])
  (rw [← ek])
  (exact (h3-r-rel xm w w2 a r hs hc1 hc4 ht ha hef heb hn hc2 hc3 hc5 ma mr hr)))

(a/theorem h3-rest-rel [xm :- (List Nat), w :- World, w2 :- World]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w))))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-has comp-id y (:comps w2)) true) (= (tbl-has comp-id y (:comps w)) true)))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) (:comps w)) true) (= (tbl-all (hk-wif y) (:comps w2)) true)))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true) (= (tbl-all (h3-tk (:runs w2) y) (:tasks w2)) true)))
      (= (:acts w2) (:acts w))
      (forall [y :- Nat] (=> (= (tbl-has edge-id y (:edges w)) true) (Or (= (tbl-has edge-id y (:edges w2)) true) (= (h3-free xm w y) true))))
      (forall [e2 :- EdgeRow] (=> (List.Mem e2 (:edges w2))
        (Or (= (tbl-has edge-id (:id e2) (:edges w)) false) (Or (= (tbl-any (h3-ekq e2) (:edges w)) true) (= (h3-free xm w (:id e2)) true)))))
      (<= (:next-id w) (:next-id w2))
      (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-e1 k2) (:comps w)) true) (= (tbl-all (h3-e1 k2) (:comps w2)) true)))
      (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-any (h3-cur k2) (:comps w2)) true) (= (tbl-any (h3-cur k2) (:comps w)) true)))
      (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-cs k2) (:comps w)) true) (= (tbl-all (h3-cs k2) (:comps w2)) true)))
      (forall [r2 :- RunRow] (=> (List.Mem r2 (:runs w2))
        (Or (= (Nat.ble (:next-id w) (:id r2)) true) (= (tbl-any (h3-rkq r2) (:runs w)) true))))
      (= (h3-rest xm w) true) (= (h3-rest xm w2) true))
  (intros hs hc1 hc4 ht ha hef heb hn hc2 hc3 hc5 hrk h)
  (simp only [h3-rest] at h)
  (simp only [h3-rest])
  (rw [ha])
  (have hm (forall [a :- ActRow] (=> (List.Mem a (:acts w)) (= (h3-a xm w a) true) (= (h3-a xm w2 a) true))))
  (intros a ma q)
  (exact (h3-a-rel xm w w2 a hs hc1 hc4 ht ha hef heb hn hc2 hc3 hc5 hrk ma q))
  (exact (tbl-all-mem-mono ActRow (h3-a xm w) (h3-a xm w2) (:acts w) hm h)))

;; all edges persist; no edge changes
(a/theorem h3-hef-all [xm :- (List Nat), w :- World, es2 :- (List EdgeRow),
                       hef :- (forall [y :- Nat] (=> (= (tbl-has edge-id y (:edges w)) true) (= (tbl-has edge-id y es2) true)))]
  (forall [y :- Nat] (=> (= (tbl-has edge-id y (:edges w)) true) (Or (= (tbl-has edge-id y es2) true) (= (h3-free xm w y) true))))
  (intros y q) (exact (Or.inl (hef y q))))
(a/theorem h3-heb-of [xm :- (List Nat), w :- World, es2 :- (List EdgeRow),
                      heb :- (forall [e2 :- EdgeRow] (=> (List.Mem e2 es2) (Or (= (tbl-has edge-id (:id e2) (:edges w)) false) (= (tbl-any (h3-ekq e2) (:edges w)) true))))]
  (forall [e2 :- EdgeRow] (=> (List.Mem e2 es2)
        (Or (= (tbl-has edge-id (:id e2) (:edges w)) false) (Or (= (tbl-any (h3-ekq e2) (:edges w)) true) (= (h3-free xm w (:id e2)) true)))))
  (intros e2 m) (have k := (heb e2 m)) (cases k) (case [inl z] (exact (Or.inl z))) (case [inr z] (exact (Or.inr (Or.inl z)))))
(a/theorem h3-hc5-refl [w :- World] (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-cs k2) (:comps w)) true) (= (tbl-all (h3-cs k2) (:comps w)) true)))
  (intros k2 hk q) (exact q))

;; ---- reflexive instances
(a/theorem h3-ekq-refl [e :- EdgeRow] (= (h3-ekq e e) true)
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [h3-ekq Nat.beq_refl hp Bool.not_false Bool.true_or Bool.and_self])
  (simp only [h3-ekq Nat.beq_refl hp Bool.or_true Bool.and_self]))
(a/theorem h3-rkq-refl [r :- RunRow] (= (h3-rkq r r) true) (simp only [h3-rkq Nat.beq_refl Bool.and_self]))
(a/theorem h3-heb-refl [es :- (List EdgeRow)]
  (forall [e2 :- EdgeRow] (=> (List.Mem e2 es) (Or (= (tbl-has edge-id (:id e2) es) false) (= (tbl-any (h3-ekq e2) es) true))))
  (intros e2 m) (exact (Or.inr (any-elim-of EdgeRow (h3-ekq e2) e2 es m (h3-ekq-refl e2)))))
(a/theorem h3-hrk-refl [n :- Nat, rs :- (List RunRow)]
  (forall [r2 :- RunRow] (=> (List.Mem r2 rs) (Or (= (Nat.ble n (:id r2)) true) (= (tbl-any (h3-rkq r2) rs) true))))
  (intros r2 m) (exact (Or.inr (any-elim-of RunRow (h3-rkq r2) r2 rs m (h3-rkq-refl r2)))))

;; ---- per-table forms
(a/theorem h3r-cs [xm :- (List Nat), w :- World, cs2 :- (List CompRow)]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w))))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-has comp-id y cs2) true) (= (tbl-has comp-id y (:comps w)) true)))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) (:comps w)) true) (= (tbl-all (hk-wif y) cs2) true)))
      (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-e1 k2) (:comps w)) true) (= (tbl-all (h3-e1 k2) cs2) true)))
      (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-any (h3-cur k2) cs2) true) (= (tbl-any (h3-cur k2) (:comps w)) true)))
      (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-cs k2) (:comps w)) true) (= (tbl-all (h3-cs k2) cs2) true)))
      (= (h3-rest xm w) true) (= (h3-rest xm (set-comps w cs2)) true))
  (intros hs hc1 hc4 hc2 hc3 hc5 h)
  (exact (h3-rest-rel xm w (set-comps w cs2) hs hc1 hc4
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true)] q)
           (rfl) (h3-hef-all xm w (:edges w) (fn [y :- Nat, q :- (= (tbl-has edge-id y (:edges w)) true)] q)) (h3-heb-of xm w (:edges w) (h3-heb-refl (:edges w))) (Nat.le_refl _)
           hc2 hc3 hc5 (h3-hrk-refl (:next-id w) (:runs w)) h)))

(a/theorem h3r-ts [xm :- (List Nat), w :- World, ts2 :- (List TaskRow)]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w))))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true) (= (tbl-all (h3-tk (:runs w) y) ts2) true)))
      (= (h3-rest xm w) true) (= (h3-rest xm (set-tasks w ts2)) true))
  (intros hs ht h)
  (exact (h3-rest-rel xm w (set-tasks w ts2) hs
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-has comp-id y (:comps w)) true)] q)
           (fn [y :- Nat, hy :- (< y (:next-id w)), hx :- (= (reach-mem y xm) false), q :- (= (tbl-all (hk-wif y) (:comps w)) true)] q)
           ht (rfl) (h3-hef-all xm w (:edges w) (fn [y :- Nat, q :- (= (tbl-has edge-id y (:edges w)) true)] q)) (h3-heb-of xm w (:edges w) (h3-heb-refl (:edges w))) (Nat.le_refl _)
           (fn [k2 :- RK3, hk :- (< (:of k2) (:next-id w)), q :- (= (tbl-all (h3-e1 k2) (:comps w)) true)] q)
           (fn [k2 :- RK3, hk :- (< (:of k2) (:next-id w)), q :- (= (tbl-any (h3-cur k2) (:comps w)) true)] q)
           (h3-hc5-refl w) (h3-hrk-refl (:next-id w) (:runs w)) h)))

(a/theorem h3r-rs [xm :- (List Nat), w :- World, rs2 :- (List RunRow)]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w))))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true) (= (tbl-all (h3-tk rs2 y) (:tasks w)) true)))
      (forall [r2 :- RunRow] (=> (List.Mem r2 rs2) (Or (= (Nat.ble (:next-id w) (:id r2)) true) (= (tbl-any (h3-rkq r2) (:runs w)) true))))
      (= (h3-rest xm w) true) (= (h3-rest xm (set-runs w rs2)) true))
  (intros hs ht hrk h)
  (exact (h3-rest-rel xm w (set-runs w rs2) hs
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-has comp-id y (:comps w)) true)] q)
           (fn [y :- Nat, hy :- (< y (:next-id w)), hx :- (= (reach-mem y xm) false), q :- (= (tbl-all (hk-wif y) (:comps w)) true)] q)
           ht (rfl) (h3-hef-all xm w (:edges w) (fn [y :- Nat, q :- (= (tbl-has edge-id y (:edges w)) true)] q)) (h3-heb-of xm w (:edges w) (h3-heb-refl (:edges w))) (Nat.le_refl _)
           (fn [k2 :- RK3, hk :- (< (:of k2) (:next-id w)), q :- (= (tbl-all (h3-e1 k2) (:comps w)) true)] q)
           (fn [k2 :- RK3, hk :- (< (:of k2) (:next-id w)), q :- (= (tbl-any (h3-cur k2) (:comps w)) true)] q)
           (h3-hc5-refl w) hrk h)))

(a/theorem h3r-es [xm :- (List Nat), w :- World, es2 :- (List EdgeRow)]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w))))
      (forall [y :- Nat] (=> (= (tbl-has edge-id y (:edges w)) true) (= (tbl-has edge-id y es2) true)))
      (forall [e2 :- EdgeRow] (=> (List.Mem e2 es2)
                                  (Or (= (tbl-has edge-id (:id e2) (:edges w)) false) (= (tbl-any (h3-ekq e2) (:edges w)) true))))
      (= (h3-rest xm w) true) (= (h3-rest xm (set-edges w es2)) true))
  (intros hs hef heb h)
  (exact (h3-rest-rel xm w (set-edges w es2) hs
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-has comp-id y (:comps w)) true)] q)
           (fn [y :- Nat, hy :- (< y (:next-id w)), hx :- (= (reach-mem y xm) false), q :- (= (tbl-all (hk-wif y) (:comps w)) true)] q)
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true)] q)
           (rfl) (h3-hef-all xm w es2 hef) (h3-heb-of xm w es2 heb) (Nat.le_refl _)
           (fn [k2 :- RK3, hk :- (< (:of k2) (:next-id w)), q :- (= (tbl-all (h3-e1 k2) (:comps w)) true)] q)
           (fn [k2 :- RK3, hk :- (< (:of k2) (:next-id w)), q :- (= (tbl-any (h3-cur k2) (:comps w)) true)] q)
           (h3-hc5-refl w) (h3-hrk-refl (:next-id w) (:runs w)) h)))

(a/theorem h3r-nid [xm :- (List Nat), w :- World, n :- Nat]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (<= (:next-id w) n) (= (h3-rest xm w) true) (= (h3-rest xm (set-next-id w n)) true))
  (intros hs hn h)
  (exact (h3-rest-rel xm w (set-next-id w n) hs
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-has comp-id y (:comps w)) true)] q)
           (fn [y :- Nat, hy :- (< y (:next-id w)), hx :- (= (reach-mem y xm) false), q :- (= (tbl-all (hk-wif y) (:comps w)) true)] q)
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true)] q)
           (rfl) (h3-hef-all xm w (:edges w) (fn [y :- Nat, q :- (= (tbl-has edge-id y (:edges w)) true)] q)) (h3-heb-of xm w (:edges w) (h3-heb-refl (:edges w))) hn
           (fn [k2 :- RK3, hk :- (< (:of k2) (:next-id w)), q :- (= (tbl-all (h3-e1 k2) (:comps w)) true)] q)
           (fn [k2 :- RK3, hk :- (< (:of k2) (:next-id w)), q :- (= (tbl-any (h3-cur k2) (:comps w)) true)] q)
           (h3-hc5-refl w) (h3-hrk-refl (:next-id w) (:runs w)) h)))
(a/theorem h3r-bump [xm :- (List Nat), w :- World]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (bump w)) true))
  (intros hs h) (exact (h3r-nid xm w (+ (:next-id w) 1) hs (Nat.le_succ _) h)))

;; ---- computation row edits: id kept, epoch not lowered, a strongly waiting row stays so
(a/theorem h3-e1-upd [k :- RK3, x :- Nat, f :- (=> CompRow CompRow),
                      hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                      hep :- (forall [c :- CompRow] (<= (:epoch c) (:epoch (f c)))), cs :- (List CompRow)]
  (=> (= (tbl-all (h3-e1 k) cs) true) (= (tbl-all (h3-e1 k) (tbl-upd comp-id x f cs)) true))
  (intro h)
  (apply (tbl-all-upd CompRow comp-id x f (h3-e1 k) (h3-e1 k) _ _ cs h))
  (intros r hr hx)
  (have e (= (:id (f r)) (:id r))) (exact (hid r))
  (simp only [h3-e1 e])
  (simp only [h3-e1] at hr)
  (cases hb (Nat.beq (:id r) (:of k)))
  (simp only [Bool.not_false Bool.true_or])
  (simp only [hb Bool.not_true Bool.false_or] at hr)
  (simp only [Bool.not_true Bool.false_or])
  (exact (gd-ble-of _ _ (Nat.le_trans (gd-le-of _ _ hr) (hep r))))
  (intros r hr hx) (exact hr))

(a/theorem h3-any-upd-back [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), P :- (=> A Bool),
                            hb :- (forall [r :- A] (=> (= (P (f r)) true) (= (P r) true))), xs :- (List A)]
  (=> (= (tbl-any P (tbl-upd idf x f xs)) true) (= (tbl-any P xs) true))
  (induction xs)
  (case [nil] (intro q) (simp [tbl-upd tbl-any] at q))
  (case [cons hd t ih]
    (intro q)
    (cases hx (Nat.beq (idf hd) x))
    (case [false]
      (simp only [tbl-upd hx tbl-any Bool.or_eq_true] at q) (simp only [tbl-any Bool.or_eq_true])
      (cases q) (case [inl z] (exact (Or.inl z))) (case [inr z] (exact (Or.inr (ih z)))))
    (case [true]
      (simp only [tbl-upd hx tbl-any Bool.or_eq_true] at q) (simp only [tbl-any Bool.or_eq_true])
      (cases q) (case [inl z] (exact (Or.inl (hb hd z)))) (case [inr z] (exact (Or.inr (ih z)))))))

(a/theorem h3-cur-back [k :- RK3, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hep :- (forall [c :- CompRow] (<= (:epoch c) (:epoch (f c)))), r :- CompRow]
  (=> (= (h3-cur k (f r)) true) (= (h3-cur k r) true))
  (intro q)
  (have e (= (:id (f r)) (:id r))) (exact (hid r))
  (simp only [h3-cur Bool.and_eq_true e] at q)
  (simp only [h3-cur Bool.and_eq_true])
  (exact (And.intro (And.left q) (gd-ble-of _ _ (Nat.le_trans (hep r) (gd-le-of _ _ (And.right q)))))))

(a/theorem h3-c2-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                      hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                      hep :- (forall [c :- CompRow] (<= (:epoch c) (:epoch (f c))))]
  (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-e1 k2) (:comps w)) true) (= (tbl-all (h3-e1 k2) (tbl-upd comp-id x f (:comps w))) true)))
  (intros k2 hk q) (exact (h3-e1-upd k2 x f hid hep (:comps w) q)))
(a/theorem h3-c3-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                      hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                      hep :- (forall [c :- CompRow] (<= (:epoch c) (:epoch (f c))))]
  (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-any (h3-cur k2) (tbl-upd comp-id x f (:comps w))) true) (= (tbl-any (h3-cur k2) (:comps w)) true)))
  (intros k2 hk q)
  (have hb (forall [r :- CompRow] (=> (= (h3-cur k2 (f r)) true) (= (h3-cur k2 r) true))))
  (intros r z) (exact (h3-cur-back k2 f hid hep r z))
  (exact (h3-any-upd-back CompRow comp-id x f (h3-cur k2) hb (:comps w) q)))
(a/theorem h3-c1-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                      hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c)))]
  (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-has comp-id y (tbl-upd comp-id x f (:comps w))) true) (= (tbl-has comp-id y (:comps w)) true)))
  (intros y hy q) (exact (Eq.trans (Eq.symm (tbl-has-upd CompRow comp-id x y f hid (:comps w))) q)))
(a/theorem h3-c5-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                      hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                      hds :- (forall [c :- CompRow] (=> (= (Nat.blt (:done-epoch c) (:epoch c)) true) (= (Nat.blt (:done-epoch (f c)) (:epoch (f c))) true)))]
  (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-cs k2) (:comps w)) true) (= (tbl-all (h3-cs k2) (tbl-upd comp-id x f (:comps w))) true)))
  (intros k2 hk q)
  (apply (tbl-all-upd CompRow comp-id x f (h3-cs k2) (h3-cs k2) _ _ (:comps w) q))
  (intros r hr hx)
  (have e (= (:id (f r)) (:id r))) (exact (hid r))
  (simp only [h3-cs e]) (simp only [h3-cs] at hr)
  (cases hb (Nat.beq (:id r) (:of k2)))
  (simp only [Bool.not_false Bool.true_or])
  (simp only [hb Bool.not_true Bool.false_or] at hr)
  (simp only [Bool.not_true Bool.false_or]) (exact (hds r hr))
  (intros r hr hx) (exact hr))
(a/theorem h3r-comp-upd [xm :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                         hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                         hep :- (forall [c :- CompRow] (<= (:epoch c) (:epoch (f c)))),
                         hm :- (forall [c :- CompRow] (=> (= (hk-wt c) true) (= (hk-wt (f c)) true))),
                         hds :- (forall [c :- CompRow] (=> (= (Nat.blt (:done-epoch c) (:epoch c)) true) (= (Nat.blt (:done-epoch (f c)) (:epoch (f c))) true)))]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (comp-upd w x f)) true))
  (intros hs h)
  (have a1 (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-has comp-id y (tbl-upd comp-id x f (:comps w))) true) (= (tbl-has comp-id y (:comps w)) true))))
  (intros y hy q) (exact (Eq.trans (Eq.symm (tbl-has-upd CompRow comp-id x y f hid (:comps w))) q))
  (have a2 (forall [y :- Nat] (=> (< y (:next-id w)) (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) (:comps w)) true) (= (tbl-all (hk-wif y) (tbl-upd comp-id x f (:comps w))) true))))
  (intros y hy hx q) (exact (hk-wif-upd y x f hid hm (:comps w) q))
  (have a3 := (h3-c2-upd w x f hid hep))
  (have a4 := (h3-c3-upd w x f hid hep))
  (have a5 := (h3-c5-upd w x f hid hds))
  (exact (h3r-cs xm w (tbl-upd comp-id x f (:comps w)) hs a1 a2 a3 a4 a5 h)))
(a/theorem h3-comp-upd-m [xm :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                          hep :- (forall [c :- CompRow] (<= (:epoch c) (:epoch (f c)))),
                          hm :- (forall [c :- CompRow] (=> (= (hk-wt c) true) (= (hk-wt (f c)) true))),
                          hds :- (forall [c :- CompRow] (=> (= (Nat.blt (:done-epoch c) (:epoch c)) true) (= (Nat.blt (:done-epoch (f c)) (:epoch (f c))) true)))]
  (=> (= (h3 xm w) true) (= (h3 xm (comp-upd w x f)) true))
  (intro h)
  (have hs := (h3-sample xm w h))
  (exact (h3-intro xm _ (inv-comp-upd w x f hid hp hs) (h3r-comp-upd xm w x f hid hep hm hds (h3-db-of w hs) (h3-rest-of xm w h)))))

;; ---- edge row edits: id, kind, creditor, debtor kept, an armed edge stays armed
(a/theorem h3-heb-upd [x :- Nat, f :- (=> EdgeRow EdgeRow), hq :- (forall [e :- EdgeRow] (= (h3-ekq (f e) e) true)), es :- (List EdgeRow)]
  (forall [e2 :- EdgeRow] (=> (List.Mem e2 (tbl-upd edge-id x f es)) (= (tbl-any (h3-ekq e2) es) true)))
  (induction es)
  (case [nil] (intros e2 m) (simp only [tbl-upd] at m) (cases m))
  (case [cons hd t ih]
    (intros e2 m)
    (cases hx (Nat.beq (edge-id hd) x))
    (case [false]
      (simp only [tbl-upd hx] at m)
      (cases m)
      (case [head] (exact (any-elim-of EdgeRow (h3-ekq hd) hd (List.cons EdgeRow hd t) (List.Mem.head t) (h3-ekq-refl hd))))
      (case [tail m2] (exact (any-cons-of EdgeRow (h3-ekq e2) hd t (ih e2 m2)))))
    (case [true]
      (simp only [tbl-upd hx] at m)
      (cases m)
      (case [head] (exact (any-elim-of EdgeRow (h3-ekq (f hd)) hd (List.cons EdgeRow hd t) (List.Mem.head t) (hq hd))))
      (case [tail m2] (exact (any-cons-of EdgeRow (h3-ekq e2) hd t (ih e2 m2)))))))
(a/theorem h3-ekq-f [f :- (=> EdgeRow EdgeRow),
                     hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                     hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                     hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                     hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                     ha :- (forall [e :- EdgeRow] (=> (= (Nat.beq (:phase e) ph-armed) true) (= (Nat.beq (:phase (f e)) ph-armed) true))),
                     e :- EdgeRow]
  (= (h3-ekq (f e) e) true)
  (have i1 (= (:id (f e)) (:id e))) (exact (hid e))
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [h3-ekq i1 (hk e) (hc e) (hd e) hp Nat.beq_refl Bool.not_false Bool.true_or Bool.and_self])
  (simp only [h3-ekq i1 (hk e) (hc e) (hd e) hp (ha e hp) Nat.beq_refl Bool.not_true Bool.or_true Bool.and_self]))
(a/theorem h3-ef-upd [xm :- (List Nat), w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                      hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e)))]
  (forall [y :- Nat] (=> (= (tbl-has edge-id y (:edges w)) true) (= (tbl-has edge-id y (tbl-upd edge-id x f (:edges w))) true)))
  (intros y q) (exact (Eq.trans (tbl-has-upd EdgeRow edge-id x y f hid (:edges w)) q)))
(a/theorem h3-eb-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                      hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                      hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                      hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                      hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                      ha :- (forall [e :- EdgeRow] (=> (= (Nat.beq (:phase e) ph-armed) true) (= (Nat.beq (:phase (f e)) ph-armed) true)))]
  (forall [e2 :- EdgeRow] (=> (List.Mem e2 (tbl-upd edge-id x f (:edges w)))
                              (Or (= (tbl-has edge-id (:id e2) (:edges w)) false) (= (tbl-any (h3-ekq e2) (:edges w)) true))))
  (intros e2 m) (exact (Or.inr (h3-heb-upd x f (h3-ekq-f f hid hk hc hd ha) (:edges w) e2 m))))
(a/theorem h3r-edge-upd [xm :- (List Nat), w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                         hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                         hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                         hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                         hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                         ha :- (forall [e :- EdgeRow] (=> (= (Nat.beq (:phase e) ph-armed) true) (= (Nat.beq (:phase (f e)) ph-armed) true)))]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (edge-upd w x f)) true))
  (intros hs h)
  (have a1 := (h3-ef-upd xm w x f hid))
  (have a2 := (h3-eb-upd w x f hid hk hc hd ha))
  (exact (h3r-es xm w (tbl-upd edge-id x f (:edges w)) hs a1 a2 h)))

;; ---- an edge edit and a computation edit together (mark-edge, unmark-edge): the condition on
;; strong waiting is a hypothesis (a pending decrement needs a safe creditor)
(a/theorem h3r-ce-upd [xm :- (List Nat), w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow), c :- Nat, g :- (=> CompRow CompRow),
                       hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                       hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                       hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                       hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                       ha :- (forall [e :- EdgeRow] (=> (= (Nat.beq (:phase e) ph-armed) true) (= (Nat.beq (:phase (f e)) ph-armed) true))),
                       gid :- (forall [q :- CompRow] (= (comp-id (g q)) (comp-id q))),
                       gep :- (forall [q :- CompRow] (<= (:epoch q) (:epoch (g q)))),
                       gds :- (forall [c :- CompRow] (=> (= (Nat.blt (:done-epoch c) (:epoch c)) true) (= (Nat.blt (:done-epoch (g c)) (:epoch (g c))) true)))]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w))))
      (forall [y :- Nat] (=> (< y (:next-id w)) (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) (:comps w)) true)
                             (= (tbl-all (hk-wif y) (tbl-upd comp-id c g (:comps w))) true)))
      (= (h3-rest xm w) true) (= (h3-rest xm (comp-upd (edge-upd w x f) c g)) true))
  (intros hs hc4 h)
  (have a1 := (h3-c1-upd w c g gid))
  (have a3 := (h3-c2-upd w c g gid gep))
  (have a4 := (h3-c3-upd w c g gid gep))
  (have ht (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true))))
  (intros y hy q) (exact q)
  (have e1 := (h3-hef-all xm w (tbl-upd edge-id x f (:edges w)) (h3-ef-upd xm w x f hid)))
  (have e2 := (h3-eb-upd w x f hid hk hc hd ha))
  (have a5 := (h3-c5-upd w c g gid gds))
  (exact (h3-rest-rel xm w (comp-upd (edge-upd w x f) c g) hs a1 hc4 ht (rfl) e1 (h3-heb-of xm w (tbl-upd edge-id x f (:edges w)) e2) (Nat.le_refl _) a3 a4 a5
           (h3-hrk-refl (:next-id w) (:runs w)) h)))

(a/theorem h3-sm-armed [b :- Bool] (forall [e :- EdgeRow] (=> (= (Nat.beq (:phase e) ph-armed) true) (= (Nat.beq (:phase (edge-set-marked b e)) ph-armed) true)))
  (intros e h) (exact h))
(a/theorem h3-ep-refl [g :- (=> CompRow CompRow), hg :- (forall [q :- CompRow] (= (:epoch (g q)) (:epoch q)))]
  (forall [q :- CompRow] (<= (:epoch q) (:epoch (g q))))
  (intro q) (rw [(hg q)]) (exact (Nat.le_refl _)))

(a/theorem h3r-mark-edge [xm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (mark-edge w x)) true))
  (intros hs h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false]
      (simp only [mark-edge hf hm])
      (exact (h3r-ce-upd xm w x (edge-set-marked true) (:creditor e) comp-inc-pending (edge-set-marked-id true)
               (fn [q :- EdgeRow] (Eq.refl (:kind q))) (fn [q :- EdgeRow] (Eq.refl (:creditor q))) (fn [q :- EdgeRow] (Eq.refl (:debtor q)))
               (h3-sm-armed true) comp-inc-pending-id (h3-ep-refl comp-inc-pending (fn [q :- CompRow] (Eq.refl (:epoch q)))) (fn [c :- CompRow, q :- (= (Nat.blt (:done-epoch c) (:epoch c)) true)] q) hs
               (fn [y :- Nat, hy :- (< y (:next-id w)), hx :- (= (reach-mem y xm) false), q :- (= (tbl-all (hk-wif y) (:comps w)) true)]
                 (hk-wif-upd y (:creditor e) comp-inc-pending comp-inc-pending-id hk-wt-inc (:comps w) q))
               h)))
    (case [true] (simp only [mark-edge hf hm]) (exact h))))

;; a pending decrement of creditor c keeps every non-exempt strongly waiting id waiting when c is safe
(a/theorem h3-c4-dec [xm :- (List Nat), cs :- (List CompRow), c :- Nat]
  (=> (= (hk-safe xm cs c) true)
      (forall [y :- Nat] (=> (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) cs) true)
                             (= (tbl-all (hk-wif y) (tbl-upd comp-id c comp-dec-pending cs)) true))))
  (intros hsf y hx q)
  (cases hcd (Nat.beq c y))
  (exact (hk-wif-pend y c comp-dec-pending hk-dec-id hk-dec-idle hk-dec-ep hk-dec-done cs (Or.inl hcd) q))
  (have e1 := (Nat.eq_of_beq_eq_true hcd))
  (simp only [hk-safe Bool.or_eq_true] at hsf)
  (cases hsf)
  (rename_i z) (rw [e1] at z) (rw [hx] at z) (cases z)
  (rename_i z) (exact (hk-wif-pend y c comp-dec-pending hk-dec-id hk-dec-idle hk-dec-ep hk-dec-done cs (Or.inr z) q)))

(a/theorem h3r-unmark-edge [xm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true) (= (hk-safe xm (:comps w) (:creditor e)) true)))
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (unmark-edge w x)) true))
  (intros hu hs h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true]
      (simp only [unmark-edge hf hm])
      (have c4 := (h3-c4-dec xm (:comps w) (:creditor e) (hu e hf hm)))
      (exact (h3r-ce-upd xm w x (edge-set-marked false) (:creditor e) comp-dec-pending (edge-set-marked-id false)
               (fn [q :- EdgeRow] (Eq.refl (:kind q))) (fn [q :- EdgeRow] (Eq.refl (:creditor q))) (fn [q :- EdgeRow] (Eq.refl (:debtor q)))
               (h3-sm-armed false) hk-dec-id (h3-ep-refl comp-dec-pending hk-dec-ep) (fn [c :- CompRow, q :- (= (Nat.blt (:done-epoch c) (:epoch c)) true)] q) hs
               (fn [y :- Nat, hy :- (< y (:next-id w)), hx :- (= (reach-mem y xm) false), q :- (= (tbl-all (hk-wif y) (:comps w)) true)]
                 (c4 y hx q))
               h)))))

;; ---- the activations change (the other tables kept): every activation a2 afterwards comes from an
;; activation a with the same id and run, its members are a's, and a member's first activation stays
(a/defn h3-ay [as :- (List ActRow), as2 :- (List ActRow), a :- ActRow, a2 :- ActRow, y :- Nat] Bool
  (Bool.and (reach-mem y (act-contrib a))
            (Bool.or (Bool.not (opt-test (h3-first (:id a)) (act-with-member y as))) (opt-test (h3-first (:id a2)) (act-with-member y as2)))))
(a/defn h3-akq [as :- (List ActRow), as2 :- (List ActRow), a2 :- ActRow, a :- ActRow] Bool
  (Bool.and (Nat.beq (:id a) (:id a2)) (Bool.and (Nat.beq (:run a) (:run a2)) (tbl-all (h3-ay as as2 a a2) (act-contrib a2)))))

(a/theorem h3-acts-nodup [w :- World] (=> (= (inv-sample w) true) (= (nat-nodup (tbl-ids act-id (:acts w))) true))
  (intro h)
  (have hi := (And.right (And.right (inv-parts w h))))
  (simp only [ids-ok ids-unique all-ids Bool.and_eq_true] at hi)
  (exact (nat-nodup-app-left _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _
           (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (And.left hi))))))))))

(a/theorem h3-r-acts [xm :- (List Nat), w :- World, as2 :- (List ActRow), a :- ActRow, a2 :- ActRow, k :- RK3]
  (=> (= (h3-akq (:acts w) as2 a2 a) true) (= (h3-r xm w a k) true) (= (h3-r xm (set-acts w as2) a2 k) true))
  (intros hq h)
  (simp only [h3-akq Bool.and_eq_true] at hq)
  (have ei := (Nat.eq_of_beq_eq_true (And.left hq)))
  (have er := (Nat.eq_of_beq_eq_true (And.left (And.right hq))))
  (have hy := (And.right (And.right hq)))
  (simp only [h3-r Bool.or_eq_true Bool.and_eq_true] at h)
  (simp only [h3-r Bool.or_eq_true Bool.and_eq_true])
  (rw [← er])
  (cases h)
  (case [inl q] (exact (Or.inl q)))
  (case [inr q]
    (apply Or.inr)
    (apply And.intro) (exact (And.left q))
    (apply And.intro) (exact (And.left (And.right q)))
    (have ob := (And.right (And.right q)))
    (simp only [h3-ob Bool.or_eq_true Bool.and_eq_true] at ob)
    (simp only [h3-ob Bool.or_eq_true Bool.and_eq_true])
    (cases ob)
    (case [inl z] (exact (Or.inl z)))
    (case [inr z]
      (apply Or.inr)
      (cases z)
      (case [inl z2] (exact (Or.inl z2)))
      (case [inr z2]
        (apply Or.inr)
        (apply And.intro) (exact (And.left z2))
        (have g (forall [y :- Nat] (=> (List.Mem y (act-contrib a2)) (= (h3-ay (:acts w) as2 a a2 y) true) (= (h3-x xm (set-acts w as2) a2 k y) true))))
        (intros y my hay)
        (simp only [h3-ay Bool.and_eq_true] at hay)
        (have hx := (tbl-all-mem Nat _ y (act-contrib a) (And.right z2) (Iff.mp (reach-mem-iff y (act-contrib a)) (And.left hay))))
        (simp only [h3-x Bool.or_eq_true Bool.and_eq_true] at hx)
        (simp only [h3-x Bool.or_eq_true Bool.and_eq_true])
        (cases hx)
        (case' [inl z3] (exact (Or.inl z3)))
        (rename_i hx)
        (apply Or.inr)
        (apply And.intro) (exact (And.left hx))
        (have g2 (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (h3-eok xm w a k y e) true) (= (h3-eok xm (set-acts w as2) a2 k y e) true))))
        (intros e me he)
        (cases hiy (Nat.beq (:id e) y))
        (case [false] (simp only [h3-eok hiy Bool.not_false Bool.true_or]))
        (case [true]
          (have ey := (Nat.eq_of_beq_eq_true hiy))
          (simp only [h3-eok hiy Bool.not_true Bool.false_or Bool.or_eq_true Bool.and_eq_true] at he)
          (simp only [h3-eok hiy Bool.not_true Bool.false_or Bool.or_eq_true Bool.and_eq_true])
          (apply And.intro)
          (have s1 := (And.left he)) (simp only [h3-s Bool.and_eq_true] at s1) (simp only [h3-s Bool.and_eq_true])
          (have f1 := (And.right (And.right (And.right s1))))
          (rw [ey] at f1)
          (have f2 := (And.right hay))
          (simp only [f1 Bool.not_true Bool.false_or] at f2)
          (have s3 := (And.left (And.right (And.right s1)))) (rw [ei] at s3)
          (rw [ey])
          (exact (And.intro (And.left s1) (And.intro (And.left (And.right s1)) (And.intro s3 f2))))
          (exact (And.right he)))
        (exact (tbl-all-mem-mono EdgeRow _ _ (:edges w) g2 (And.right hx)))
        (exact (tbl-all-mem-mono Nat _ _ (act-contrib a2) g hy))))))

(a/theorem h3-a-acts [xm :- (List Nat), w :- World, as2 :- (List ActRow), a :- ActRow, a2 :- ActRow]
  (=> (= (h3-akq (:acts w) as2 a2 a) true) (= (h3-a xm w a) true) (= (h3-a xm (set-acts w as2) a2) true))
  (intros hq h)
  (have hq2 := hq) (simp only [h3-akq Bool.and_eq_true] at hq2)
  (have er := (Nat.eq_of_beq_eq_true (And.left (And.right hq2))))
  (simp only [h3-a Bool.and_eq_true] at h)
  (simp only [h3-a Bool.and_eq_true])
  (rw [← er])
  (apply And.intro) (exact (And.left h))
  (have g (forall [r :- RunRow] (=> (List.Mem r (:runs w)) (= (h3-rr xm w a r) true) (= (h3-rr xm (set-acts w as2) a2 r) true))))
  (intros r mr hr) (simp only [h3-rr] at hr) (simp only [h3-rr]) (exact (h3-r-acts xm w as2 a a2 (rk3 r) hq hr))
  (exact (tbl-all-mem-mono RunRow _ _ (:runs w) g (And.right h))))

(a/theorem h3r-acts [xm :- (List Nat), w :- World, as2 :- (List ActRow)]
  (=> (forall [a2 :- ActRow] (=> (List.Mem a2 as2) (= (tbl-any (h3-akq (:acts w) as2 a2) (:acts w)) true)))
      (= (h3-rest xm w) true) (= (h3-rest xm (set-acts w as2)) true))
  (intros hc h)
  (simp only [h3-rest] at h) (simp only [h3-rest])
  (apply all-of-mem) (intros a2 m2)
  (apply (any-elim ActRow (h3-akq (:acts w) as2 a2) _ (:acts w) (hc a2 m2)))
  (intros a ma hq)
  (exact (h3-a-acts xm w as2 a a2 hq (tbl-all-mem ActRow _ a (:acts w) h ma))))

;; ---- the first activation with a member: deletions and fresh insertions without members keep it
(a/theorem h3-awm-del [y :- Nat, i :- Nat, x :- Nat, as :- (List ActRow)]
  (=> (= (opt-test (h3-first i) (act-with-member y as)) true) (= (Nat.beq i x) false)
      (= (opt-test (h3-first i) (act-with-member y (tbl-del act-id x as))) true))
  (induction as)
  (case [nil] (intros h hx) (simp [act-with-member opt-test] at h))
  (case [cons hd t ih]
    (intros h hx)
    (cases hm (mem-has y (:members hd)))
    (case [false]
      (simp only [act-with-member hm] at h)
      (cases hd2 (Nat.beq (act-id hd) x))
      (case [false] (simp only [tbl-del hd2 act-with-member hm]) (exact (ih h hx)))
      (case [true] (simp only [tbl-del hd2]) (exact (ih h hx))))
    (case [true]
      (simp only [act-with-member hm opt-test h3-first] at h)
      (have e1 := (Nat.eq_of_beq_eq_true h))
      (have hd2 (= (Nat.beq (act-id hd) x) false)) (simp only [act-id e1]) (exact hx)
      (simp only [tbl-del hd2 act-with-member hm opt-test h3-first]) (exact h))))
(a/theorem h3-awm-ins [y :- Nat, r :- ActRow, as :- (List ActRow)]
  (=> (= (mem-has y (:members r)) false) (= (act-with-member y (tbl-ins r as)) (act-with-member y as)))
  (intro h) (simp only [tbl-ins act-with-member h]))

(a/theorem h3-ay-self [as :- (List ActRow), as2 :- (List ActRow), a :- ActRow,
                       hf :- (forall [y :- Nat] (=> (= (opt-test (h3-first (:id a)) (act-with-member y as)) true)
                                                   (= (opt-test (h3-first (:id a)) (act-with-member y as2)) true)))]
  (= (h3-akq as as2 a a) true)
  (simp only [h3-akq Nat.beq_refl Bool.true_and])
  (apply all-of-mem)
  (intros y my)
  (simp only [h3-ay (Iff.mpr (reach-mem-iff y (act-contrib a)) my) Bool.true_and])
  (cases hq (opt-test (h3-first (:id a)) (act-with-member y as)))
  (case [false] (simp only [Bool.not_false Bool.true_or]))
  (case [true] (simp only [(hf y hq) Bool.or_true])))

(a/theorem h3-del-mem [A :- Type, idf :- (=> A Nat), x :- Nat, a :- A, xs :- (List A)]
  (=> (List.Mem a (tbl-del idf x xs)) (List.Mem a xs))
  (induction xs)
  (case [nil] (intro m) (simp only [tbl-del] at m) (cases m))
  (case [cons hd t ih]
    (intro m)
    (cases hx (Nat.beq (idf hd) x))
    (case [false]
      (simp only [tbl-del hx] at m)
      (cases m)
      (case [head] (exact (List.Mem.head t)))
      (case [tail m2] (exact (List.Mem.tail hd (ih m2)))))
    (case [true] (simp only [tbl-del hx] at m) (exact (List.Mem.tail hd (ih m))))))
(a/theorem h3-del-ne [A :- Type, idf :- (=> A Nat), x :- Nat, a :- A, xs :- (List A)]
  (=> (List.Mem a (tbl-del idf x xs)) (= (Nat.beq (idf a) x) false))
  (induction xs)
  (case [nil] (intro m) (simp only [tbl-del] at m) (cases m))
  (case [cons hd t ih]
    (intro m)
    (cases hx (Nat.beq (idf hd) x))
    (case [false]
      (simp only [tbl-del hx] at m)
      (cases m)
      (case [head] (exact hx))
      (case [tail m2] (exact (ih m2))))
    (case [true] (simp only [tbl-del hx] at m) (exact (ih m)))))

(a/theorem h3r-act-del [xm :- (List Nat), w :- World, x :- Nat]
  (=> (= (h3-rest xm w) true) (= (h3-rest xm (act-del w x)) true))
  (intro h)
  (apply (h3r-acts xm w (tbl-del act-id x (:acts w)) _ h))
  (intros a2 m2)
  (have ma := (h3-del-mem ActRow act-id x a2 (:acts w) m2))
  (have hf (forall [y :- Nat] (=> (= (opt-test (h3-first (:id a2)) (act-with-member y (:acts w))) true)
                                 (= (opt-test (h3-first (:id a2)) (act-with-member y (tbl-del act-id x (:acts w)))) true))))
  (intros y hy) (exact (h3-awm-del y (:id a2) x (:acts w) hy (h3-del-ne ActRow act-id x a2 (:acts w) m2)))
  (exact (any-elim-of ActRow (h3-akq (:acts w) (tbl-del act-id x (:acts w)) a2) a2 (:acts w) ma
           (h3-ay-self (:acts w) (tbl-del act-id x (:acts w)) a2 hf))))

;; ---- an activation update that keeps id and run and only drops members
(a/theorem h3-rm-members [y :- Nat, ms :- (List Member)] (= (reach-mem y (member-edges ms)) (mem-has y ms))
  (induction ms)
  (case [nil] (simp only [member-edges mem-has reach-mem]))
  (case [cons hd t ih]
    (cases hb (Nat.beq (:edge hd) y))
    (case [false] (have hb2 (= (Nat.beq y (:edge hd)) false)) (rw [beq-comm]) (exact hb)
      (simp only [member-edges mem-has reach-mem-cons hb hb2 ih Bool.false_or]))
    (case [true] (have hb2 (= (Nat.beq y (:edge hd)) true)) (rw [beq-comm]) (exact hb)
      (simp only [member-edges mem-has reach-mem-cons hb hb2 Bool.true_or]))))

(a/theorem h3-awm-upd [y :- Nat, x :- Nat, f :- (=> ActRow ActRow),
                       hid :- (forall [b :- ActRow] (= (act-id (f b)) (act-id b))),
                       hs :- (forall [b :- ActRow] (=> (= (mem-has y (:members (f b))) true) (= (mem-has y (:members b)) true))),
                       i :- Nat, as :- (List ActRow)]
  (=> (= (opt-test (h3-first i) (act-with-member y as)) true)
      (forall [b :- ActRow] (=> (List.Mem b as) (= (Nat.beq (act-id b) x) true) (= (Nat.beq (act-id b) i) true) (= (mem-has y (:members (f b))) true)))
      (= (opt-test (h3-first i) (act-with-member y (tbl-upd act-id x f as))) true))
  (induction as)
  (case [nil] (intros h hb) (simp [act-with-member opt-test] at h))
  (case [cons hd t ih]
    (intros h hb)
    (have hbt (forall [b :- ActRow] (=> (List.Mem b t) (= (Nat.beq (act-id b) x) true) (= (Nat.beq (act-id b) i) true) (= (mem-has y (:members (f b))) true))))
    (intros b mb h1 h2) (exact (hb b (List.Mem.tail hd mb) h1 h2))
    (cases hm (mem-has y (:members hd)))
    (case [false]
      (simp only [act-with-member hm] at h)
      (cases hx (Nat.beq (act-id hd) x))
      (case [false] (simp only [tbl-upd hx act-with-member hm]) (exact (ih h hbt)))
      (case [true]
        (have hm2 (= (mem-has y (:members (f hd))) false))
        (cases hq (mem-has y (:members (f hd)))) (rfl) (have z := (hs hd hq)) (rw [hm] at z) (cases z)
        (simp only [tbl-upd hx act-with-member hm2]) (exact (ih h hbt))))
    (case [true]
      (simp only [act-with-member hm opt-test h3-first] at h)
      (cases hx (Nat.beq (act-id hd) x))
      (case [false] (simp only [tbl-upd hx act-with-member hm opt-test h3-first]) (exact h))
      (case [true]
        (have hm2 := (hb hd (List.Mem.head t) hx h))
        (have h2 (= (Nat.beq (:id (f hd)) i) true)) (have e := (hid hd)) (simp only [act-id] at e) (rw [e]) (exact h)
        (simp only [tbl-upd hx act-with-member hm2 opt-test h3-first h2])))))

(a/theorem h3-upd-any [x :- Nat, f :- (=> ActRow ActRow), AS :- (List ActRow), AS2 :- (List ActRow), xs :- (List ActRow)]
  (=> (forall [a0 :- ActRow] (=> (List.Mem a0 xs) (= (Nat.beq (act-id a0) x) true) (= (h3-akq AS AS2 (f a0) a0) true)))
      (forall [a0 :- ActRow] (=> (List.Mem a0 xs) (= (Nat.beq (act-id a0) x) false) (= (h3-akq AS AS2 a0 a0) true)))
      (forall [a2 :- ActRow] (=> (List.Mem a2 (tbl-upd act-id x f xs)) (= (tbl-any (h3-akq AS AS2 a2) xs) true))))
  (induction xs)
  (case [nil] (intros h1 h2 a2 m) (simp only [tbl-upd] at m) (cases m))
  (case [cons hd t ih]
    (intros h1 h2 a2 m)
    (have h1t (forall [a0 :- ActRow] (=> (List.Mem a0 t) (= (Nat.beq (act-id a0) x) true) (= (h3-akq AS AS2 (f a0) a0) true))))
    (intros a0 m0 q) (exact (h1 a0 (List.Mem.tail hd m0) q))
    (have h2t (forall [a0 :- ActRow] (=> (List.Mem a0 t) (= (Nat.beq (act-id a0) x) false) (= (h3-akq AS AS2 a0 a0) true))))
    (intros a0 m0 q) (exact (h2 a0 (List.Mem.tail hd m0) q))
    (cases hx (Nat.beq (act-id hd) x))
    (case [false]
      (simp only [tbl-upd hx] at m)
      (cases m)
      (case [head] (exact (any-elim-of ActRow (h3-akq AS AS2 hd) hd (List.cons ActRow hd t) (List.Mem.head t) (h2 hd (List.Mem.head t) hx))))
      (case [tail m2] (exact (any-cons-of ActRow (h3-akq AS AS2 a2) hd t (ih h1t h2t a2 m2)))))
    (case [true]
      (simp only [tbl-upd hx] at m)
      (cases m)
      (case [head] (exact (any-elim-of ActRow (h3-akq AS AS2 (f hd)) hd (List.cons ActRow hd t) (List.Mem.head t) (h1 hd (List.Mem.head t) hx))))
      (case [tail m2] (exact (any-cons-of ActRow (h3-akq AS AS2 a2) hd t (ih h1t h2t a2 m2)))))))

(a/theorem h3r-act-upd [xm :- (List Nat), w :- World, x :- Nat, f :- (=> ActRow ActRow),
                        hid :- (forall [b :- ActRow] (= (act-id (f b)) (act-id b))),
                        hrun :- (forall [b :- ActRow] (= (:run (f b)) (:run b))),
                        hs :- (forall [b :- ActRow, y :- Nat] (=> (= (mem-has y (:members (f b))) true) (= (mem-has y (:members b)) true)))]
  (=> (= (inv-sample w) true) (= (h3-rest xm w) true) (= (h3-rest xm (act-upd w x f)) true))
  (intros hsw h)
  (have nd := (h3-acts-nodup w hsw))
  (have h1 (forall [a0 :- ActRow] (=> (List.Mem a0 (:acts w)) (= (Nat.beq (act-id a0) x) true)
                                      (= (h3-akq (:acts w) (tbl-upd act-id x f (:acts w)) (f a0) a0) true))))
  (intros a0 m0 q)
  (have i1 (= (:id (f a0)) (:id a0))) (exact (hid a0))
  (simp only [h3-akq i1 (hrun a0) Nat.beq_refl Bool.true_and])
  (apply all-of-mem) (intros y my)
  (have my2 (= (mem-has y (:members (f a0))) true)) (rw [← h3-rm-members]) (exact (Iff.mpr (reach-mem-iff y (act-contrib (f a0))) my))
  (have my3 (= (reach-mem y (act-contrib a0)) true)) (simp only [act-contrib h3-rm-members]) (exact (hs a0 y my2))
  (simp only [h3-ay my3 i1 Bool.true_and])
  (cases hq (opt-test (h3-first (:id a0)) (act-with-member y (:acts w))))
  (case [false] (simp only [Bool.not_false Bool.true_or]))
  (case [true]
    (have u := (uniq-all ActRow act-id (fn [b :- ActRow] (mem-has y (:members (f b)))) a0 (:acts w) nd m0 my2))
    (have hb (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (Nat.beq (act-id b) x) true) (= (Nat.beq (act-id b) (:id a0)) true) (= (mem-has y (:members (f b))) true))))
    (intros b mb q1 q2)
    (have ub := (tbl-all-mem ActRow _ b (:acts w) u mb))
    (have q3 (= (Nat.beq (:id b) (:id a0)) true)) (exact q2)
    (simp only [same-id-then act-id q3 Bool.not_true Bool.false_or] at ub) (exact ub)
    (simp only [(h3-awm-upd y x f hid (fn [b :- ActRow, z :- (= (mem-has y (:members (f b))) true)] (hs b y z)) (:id a0) (:acts w) hq hb) Bool.or_true]))
  (have h2 (forall [a0 :- ActRow] (=> (List.Mem a0 (:acts w)) (= (Nat.beq (act-id a0) x) false)
                                      (= (h3-akq (:acts w) (tbl-upd act-id x f (:acts w)) a0 a0) true))))
  (intros a0 m0 q)
  (apply h3-ay-self)
  (intros y hy)
  (have hb (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (Nat.beq (act-id b) x) true) (= (Nat.beq (act-id b) (:id a0)) true) (= (mem-has y (:members (f b))) true))))
  (intros b mb q1 q2)
  (have e1 := (Nat.eq_of_beq_eq_true q1)) (have e2 := (Nat.eq_of_beq_eq_true q2))
  (have e3 (= (Nat.beq (act-id a0) x) true)) (simp only [act-id] at e1 e2) (simp only [act-id]) (rw [← e2 e1]) (exact (Nat.beq_refl _))
  (rw [q] at e3) (cases e3)
  (exact (h3-awm-upd y x f hid (fn [b :- ActRow, z :- (= (mem-has y (:members (f b))) true)] (hs b y z)) (:id a0) (:acts w) hy hb))
  (exact (h3r-acts xm w (tbl-upd act-id x f (:acts w)) (h3-upd-any x f (:acts w) (tbl-upd act-id x f (:acts w)) (:acts w) h1 h2) h)))

;; ---- generic list facts
(a/theorem h3-any-upd-fwd [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), P :- (=> A Bool),
                           hm :- (forall [r :- A] (=> (= (P r) true) (= (P (f r)) true))), xs :- (List A)]
  (=> (= (tbl-any P xs) true) (= (tbl-any P (tbl-upd idf x f xs)) true))
  (induction xs)
  (case [nil] (intro q) (simp [tbl-any] at q))
  (case [cons hd t ih]
    (intro q)
    (simp only [tbl-any Bool.or_eq_true] at q)
    (cases hx (Nat.beq (idf hd) x))
    (case [false]
      (simp only [tbl-upd hx tbl-any Bool.or_eq_true])
      (cases q) (case [inl z] (exact (Or.inl z))) (case [inr z] (exact (Or.inr (ih z)))))
    (case [true]
      (simp only [tbl-upd hx tbl-any Bool.or_eq_true])
      (cases q) (case [inl z] (exact (Or.inl (hm hd z)))) (case [inr z] (exact (Or.inr (ih z)))))))
(a/theorem h3-upd-any-gen [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), Q :- (=> A A Bool),
                           hq :- (forall [r :- A] (= (Q (f r) r) true)), hr :- (forall [r :- A] (= (Q r r) true)), xs :- (List A)]
  (forall [a2 :- A] (=> (List.Mem a2 (tbl-upd idf x f xs)) (= (tbl-any (Q a2) xs) true)))
  (induction xs)
  (case [nil] (intros a2 m) (simp only [tbl-upd] at m) (cases m))
  (case [cons hd t ih]
    (intros a2 m)
    (cases hx (Nat.beq (idf hd) x))
    (case [false]
      (simp only [tbl-upd hx] at m)
      (cases m)
      (case [head] (exact (any-elim-of A (Q hd) hd (List.cons A hd t) (List.Mem.head t) (hr hd))))
      (case [tail m2] (exact (any-cons-of A (Q a2) hd t (ih a2 m2)))))
    (case [true]
      (simp only [tbl-upd hx] at m)
      (cases m)
      (case [head] (exact (any-elim-of A (Q (f hd)) hd (List.cons A hd t) (List.Mem.head t) (hq hd))))
      (case [tail m2] (exact (any-cons-of A (Q a2) hd t (ih a2 m2)))))))
(a/theorem h3-any-del [A :- Type, idf :- (=> A Nat), x :- Nat, P :- (=> A Bool),
                       hp :- (forall [r :- A] (=> (= (P r) true) (= (Nat.beq (idf r) x) false))), xs :- (List A)]
  (=> (= (tbl-any P xs) true) (= (tbl-any P (tbl-del idf x xs)) true))
  (induction xs)
  (case [nil] (intro q) (simp [tbl-any] at q))
  (case [cons hd t ih]
    (intro q)
    (simp only [tbl-any Bool.or_eq_true] at q)
    (cases hx (Nat.beq (idf hd) x))
    (case [false]
      (simp only [tbl-del hx tbl-any Bool.or_eq_true])
      (cases q) (case [inl z] (exact (Or.inl z))) (case [inr z] (exact (Or.inr (ih z)))))
    (case [true]
      (simp only [tbl-del hx])
      (cases q) (case [inl z] (rw [(hp hd z)] at hx) (cases hx)) (case [inr z] (exact (ih z))))))
(a/theorem h3-any-del-mem [A :- Type, idf :- (=> A Nat), x :- Nat, P :- (=> A Bool), r :- A, xs :- (List A)]
  (=> (List.Mem r xs) (= (P r) true) (= (Nat.beq (idf r) x) false) (= (tbl-any P (tbl-del idf x xs)) true))
  (induction xs)
  (case [nil] (intros m pr hx) (cases m))
  (case [cons hd t ih]
    (intros m pr hx)
    (cases m)
    (case [head] (simp only [tbl-del hx tbl-any pr Bool.true_or]))
    (case [tail m2]
      (cases hh (Nat.beq (idf hd) x))
      (case [false] (simp only [tbl-del hh]) (exact (any-cons-of A P hd (tbl-del idf x t) (ih m2 pr hx))))
      (case [true] (simp only [tbl-del hh]) (exact (ih m2 pr hx))))))
(a/theorem h3-any-del-back [A :- Type, idf :- (=> A Nat), x :- Nat, P :- (=> A Bool), xs :- (List A)]
  (=> (= (tbl-any P (tbl-del idf x xs)) true) (= (tbl-any P xs) true))
  (intro q)
  (apply (any-elim A P _ (tbl-del idf x xs) q))
  (intros a m pa) (exact (any-elim-of A P a xs (h3-del-mem A idf x a xs m) pa)))
(a/theorem h3-has-del [A :- Type, idf :- (=> A Nat), x :- Nat, y :- Nat, xs :- (List A)]
  (=> (= (tbl-has idf y (tbl-del idf x xs)) true) (= (tbl-has idf y xs) true))
  (induction xs)
  (case [nil] (intro q) (simp [tbl-has tbl-del] at q))
  (case [cons hd t ih]
    (intro q)
    (cases hy (Nat.beq (idf hd) y))
    (case [true] (simp only [tbl-has hy]))
    (case [false]
      (simp only [tbl-has hy])
      (cases hx (Nat.beq (idf hd) x))
      (case [false] (simp only [tbl-del hx tbl-has hy] at q) (exact (ih q)))
      (case [true] (simp only [tbl-del hx] at q) (exact (ih q))))))
(a/theorem h3-has-del-ne [A :- Type, idf :- (=> A Nat), x :- Nat, y :- Nat, xs :- (List A)]
  (=> (= (Nat.beq y x) false) (= (tbl-has idf y xs) true) (= (tbl-has idf y (tbl-del idf x xs)) true))
  (induction xs)
  (case [nil] (intros hn q) (simp [tbl-has] at q))
  (case [cons hd t ih]
    (intros hn q)
    (cases hx (Nat.beq (idf hd) x))
    (case [false]
      (simp only [tbl-del hx tbl-has])
      (cases hy (Nat.beq (idf hd) y))
      (case [true] (rfl))
      (case [false] (simp only [tbl-has hy] at q) (simp only [ih hn q])))
    (case [true]
      (simp only [tbl-del hx])
      (cases hy (Nat.beq (idf hd) y))
      (case [true] (have e1 := (Nat.eq_of_beq_eq_true hx)) (have e2 := (Nat.eq_of_beq_eq_true hy))
        (rw [← e2 e1] at hn) (rw [Nat.beq_refl] at hn) (cases hn))
      (case [false] (simp only [tbl-has hy] at q) (exact (ih hn q))))))

;; ---- run edits: id, of and epoch kept, an alive run stays alive
(a/theorem h3r-run-upd [xm :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                        hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hof :- (forall [r :- RunRow] (= (:of (f r)) (:of r))),
                        hep :- (forall [r :- RunRow] (= (:epoch (f r)) (:epoch r))),
                        hal :- (forall [r :- RunRow] (=> (= (run-alive r) true) (= (run-alive (f r)) true)))]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (run-upd w x f)) true))
  (intros hs h)
  (have hp (forall [rid :- Nat, r :- RunRow] (=> (= (h3-ral rid r) true) (= (h3-ral rid (f r)) true))))
  (intros rid r q) (simp only [h3-ral Bool.and_eq_true] at q) (have i1 (= (:id (f r)) (:id r))) (exact (hid r))
  (simp only [h3-ral i1 (And.left q) (hal r (And.right q)) Bool.and_self])
  (have ht (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true)
                                 (= (tbl-all (h3-tk (tbl-upd run-id x f (:runs w)) y) (:tasks w)) true))))
  (intros y hy q)
  (have g (forall [t :- TaskRow] (=> (List.Mem t (:tasks w)) (= (h3-tk (:runs w) y t) true) (= (h3-tk (tbl-upd run-id x f (:runs w)) y t) true))))
  (intros t mt qt)
  (simp only [h3-tk Bool.or_eq_true] at qt) (simp only [h3-tk Bool.or_eq_true])
  (cases qt)
  (case [inl z] (exact (Or.inl z)))
  (case [inr z] (exact (Or.inr (h3-any-upd-fwd RunRow run-id x f (h3-ral (:run t)) (hp (:run t)) (:runs w) z))))
  (exact (tbl-all-mem-mono TaskRow _ _ (:tasks w) g q))
  (have hq (forall [r :- RunRow] (= (h3-rkq (f r) r) true)))
  (intro r) (have i1 (= (:id (f r)) (:id r))) (exact (hid r)) (simp only [h3-rkq i1 (hof r) (hep r) Nat.beq_refl Bool.and_self])
  (have hrk (forall [r2 :- RunRow] (=> (List.Mem r2 (tbl-upd run-id x f (:runs w)))
                                       (Or (= (Nat.ble (:next-id w) (:id r2)) true) (= (tbl-any (h3-rkq r2) (:runs w)) true)))))
  (intros r2 m) (exact (Or.inr (h3-upd-any-gen RunRow run-id x f h3-rkq hq h3-rkq-refl (:runs w) r2 m)))
  (exact (h3r-rs xm w (tbl-upd run-id x f (:runs w)) hs ht hrk h)))

;; ---- task edits: id and run kept
(a/theorem h3r-task-upd [xm :- (List Nat), w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                         hid :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                         hrun :- (forall [t :- TaskRow] (= (:run (f t)) (:run t)))]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (task-upd w x f)) true))
  (intros hs h)
  (have ht (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true)
                                 (= (tbl-all (h3-tk (:runs w) y) (tbl-upd task-id x f (:tasks w))) true))))
  (intros y hy q)
  (apply (tbl-all-upd TaskRow task-id x f (h3-tk (:runs w) y) (h3-tk (:runs w) y) _ _ (:tasks w) q))
  (intros t ht hx) (have i1 (= (:id (f t)) (:id t))) (exact (hid t)) (simp only [h3-tk i1 (hrun t)]) (simp only [h3-tk] at ht) (exact ht)
  (intros t ht hx) (exact ht)
  (exact (h3r-ts xm w (tbl-upd task-id x f (:tasks w)) hs ht h)))

;; ---- fresh rows (id = next-id, then bump)
(a/theorem h3r-run-ins [xm :- (List Nat), w :- World, r :- RunRow]
  (=> (= (run-id r) (:next-id w)) (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (bump (run-ins w r))) true))
  (intros hr hs h)
  (have ht (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true)
                                 (= (tbl-all (h3-tk (tbl-ins r (:runs w)) y) (:tasks w)) true))))
  (intros y hy q)
  (have g (forall [t :- TaskRow] (=> (List.Mem t (:tasks w)) (= (h3-tk (:runs w) y t) true) (= (h3-tk (tbl-ins r (:runs w)) y t) true))))
  (intros t mt qt)
  (simp only [h3-tk Bool.or_eq_true] at qt) (simp only [h3-tk Bool.or_eq_true tbl-ins])
  (cases qt)
  (case [inl z] (exact (Or.inl z)))
  (case [inr z] (exact (Or.inr (any-cons-of RunRow (h3-ral (:run t)) r (:runs w) z))))
  (exact (tbl-all-mem-mono TaskRow _ _ (:tasks w) g q))
  (have hrk (forall [r2 :- RunRow] (=> (List.Mem r2 (tbl-ins r (:runs w)))
                                       (Or (= (Nat.ble (:next-id w) (:id r2)) true) (= (tbl-any (h3-rkq r2) (:runs w)) true)))))
  (intros r2 m)
  (simp only [tbl-ins] at m)
  (cases m)
  (case [head] (have e (= (:id r) (:next-id w))) (exact hr) (rw [e]) (exact (Or.inl (gd-ble-of _ _ (Nat.le_refl _)))))
  (case [tail m2] (exact (h3-hrk-refl (:next-id w) (:runs w) r2 m2)))
  (exact (h3-rest-rel xm w (bump (run-ins w r)) hs
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-has comp-id y (:comps w)) true)] q)
           (fn [y :- Nat, hy :- (< y (:next-id w)), hx :- (= (reach-mem y xm) false), q :- (= (tbl-all (hk-wif y) (:comps w)) true)] q)
           ht (rfl) (h3-hef-all xm w (:edges w) (fn [y :- Nat, q :- (= (tbl-has edge-id y (:edges w)) true)] q)) (h3-heb-of xm w (:edges w) (h3-heb-refl (:edges w)))
           (Nat.le_succ _)
           (fn [k2 :- RK3, hk :- (< (:of k2) (:next-id w)), q :- (= (tbl-all (h3-e1 k2) (:comps w)) true)] q)
           (fn [k2 :- RK3, hk :- (< (:of k2) (:next-id w)), q :- (= (tbl-any (h3-cur k2) (:comps w)) true)] q)
           (h3-hc5-refl w) hrk h)))

(a/theorem h3r-task-ins [xm :- (List Nat), w :- World, t :- TaskRow]
  (=> (= (task-id t) (:next-id w)) (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (bump (task-ins w t))) true))
  (intros htd hs h)
  (have ht (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true)
                                 (= (tbl-all (h3-tk (:runs w) y) (tbl-ins t (:tasks w))) true))))
  (intros y hy q)
  (have ne (= (Nat.beq (:id t) y) false))
  (have e (= (:id t) (:next-id w))) (exact htd)
  (cases hb (Nat.beq (:id t) y)) (rfl) (have e2 := (Nat.eq_of_beq_eq_true hb)) (omega)
  (simp only [tbl-ins tbl-all h3-tk ne q Bool.not_false Bool.true_or Bool.and_self])
  (exact (h3r-nid xm (task-ins w t) (+ (:next-id w) 1) hs (Nat.le_succ _) (h3r-ts xm w (tbl-ins t (:tasks w)) hs ht h))))

(a/theorem h3r-comp-ins [xm :- (List Nat), w :- World, c :- CompRow]
  (=> (= (comp-id c) (:next-id w)) (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (bump (comp-ins w c))) true))
  (intros hcd hs h)
  (have e (= (:id c) (:next-id w))) (exact hcd)
  (have a1 (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-has comp-id y (tbl-ins c (:comps w))) true) (= (tbl-has comp-id y (:comps w)) true))))
  (intros y hy q)
  (have ne (= (Nat.beq (comp-id c) y) false)) (cases hb (Nat.beq (comp-id c) y)) (rfl) (have e2 := (Nat.eq_of_beq_eq_true hb)) (simp only [comp-id] at e2) (omega)
  (simp only [tbl-ins tbl-has ne] at q) (exact q)
  (have a2 (forall [y :- Nat] (=> (< y (:next-id w)) (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) (:comps w)) true)
                                 (= (tbl-all (hk-wif y) (tbl-ins c (:comps w))) true))))
  (intros y hy hx q)
  (have ne (= (Nat.beq (:id c) y) false)) (cases hb (Nat.beq (:id c) y)) (rfl) (have e2 := (Nat.eq_of_beq_eq_true hb)) (omega)
  (simp only [tbl-ins tbl-all hk-wif ne q Bool.not_false Bool.true_or Bool.and_self])
  (have a3 (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-e1 k2) (:comps w)) true) (= (tbl-all (h3-e1 k2) (tbl-ins c (:comps w))) true))))
  (intros k2 hk q)
  (have ne (= (Nat.beq (:id c) (:of k2)) false)) (cases hb (Nat.beq (:id c) (:of k2))) (rfl) (have e2 := (Nat.eq_of_beq_eq_true hb)) (omega)
  (simp only [tbl-ins tbl-all h3-e1 ne q Bool.not_false Bool.true_or Bool.and_self])
  (have a4 (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-any (h3-cur k2) (tbl-ins c (:comps w))) true) (= (tbl-any (h3-cur k2) (:comps w)) true))))
  (intros k2 hk q)
  (have ne (= (Nat.beq (:id c) (:of k2)) false)) (cases hb (Nat.beq (:id c) (:of k2))) (rfl) (have e2 := (Nat.eq_of_beq_eq_true hb)) (omega)
  (simp only [tbl-ins tbl-any h3-cur ne Bool.false_and Bool.false_or] at q) (exact q)
  (have a5 (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-cs k2) (:comps w)) true) (= (tbl-all (h3-cs k2) (tbl-ins c (:comps w))) true))))
  (intros k2 hk q)
  (have ne (= (Nat.beq (:id c) (:of k2)) false)) (cases hb (Nat.beq (:id c) (:of k2))) (rfl) (have e2 := (Nat.eq_of_beq_eq_true hb)) (omega)
  (simp only [tbl-ins tbl-all h3-cs ne q Bool.not_false Bool.true_or Bool.and_self])
  (exact (h3r-nid xm (comp-ins w c) (+ (:next-id w) 1) hs (Nat.le_succ _) (h3r-cs xm w (tbl-ins c (:comps w)) hs a1 a2 a3 a4 a5 h))))

(a/theorem h3r-run-del [xm :- (List Nat), w :- World, x :- Nat]
  (=> (= (tbl-all (same-id-then run-id x (fn [r :- RunRow] (Bool.not (run-alive r)))) (:runs w)) true)
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (run-del w x)) true))
  (intros hna hs h)
  (have ht (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true)
                                 (= (tbl-all (h3-tk (tbl-del run-id x (:runs w)) y) (:tasks w)) true))))
  (intros y hy q)
  (have g (forall [t :- TaskRow] (=> (List.Mem t (:tasks w)) (= (h3-tk (:runs w) y t) true) (= (h3-tk (tbl-del run-id x (:runs w)) y t) true))))
  (intros t mt qt)
  (simp only [h3-tk Bool.or_eq_true] at qt) (simp only [h3-tk Bool.or_eq_true])
  (cases qt)
  (case [inl z] (exact (Or.inl z)))
  (case [inr z]
    (apply Or.inr)
    (have hp (forall [r :- RunRow] (=> (List.Mem r (:runs w)) (= (h3-ral (:run t) r) true) (= (Nat.beq (run-id r) x) false))))
    (intros r mr qr)
    (simp only [h3-ral Bool.and_eq_true] at qr)
    (have u := (tbl-all-mem RunRow _ r (:runs w) hna mr))
    (cases hb (Nat.beq (run-id r) x)) (rfl)
    (simp only [same-id-then hb Bool.not_true Bool.false_or (And.right qr)] at u) (cases u)
    (apply (any-elim RunRow (h3-ral (:run t)) _ (:runs w) z))
    (intros r mr qr)
    (exact (h3-any-del-mem RunRow run-id x (h3-ral (:run t)) r (:runs w) mr qr (hp r mr qr))))
  (exact (tbl-all-mem-mono TaskRow _ _ (:tasks w) g q))
  (have hrk (forall [r2 :- RunRow] (=> (List.Mem r2 (tbl-del run-id x (:runs w)))
                                       (Or (= (Nat.ble (:next-id w) (:id r2)) true) (= (tbl-any (h3-rkq r2) (:runs w)) true)))))
  (intros r2 m) (exact (h3-hrk-refl (:next-id w) (:runs w) r2 (h3-del-mem RunRow run-id x r2 (:runs w) m)))
  (exact (h3r-rs xm w (tbl-del run-id x (:runs w)) hs ht hrk h)))

(a/theorem h3r-comp-del [xm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (comp-del w x)) true))
  (intros hs h)
  (have a1 (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-has comp-id y (tbl-del comp-id x (:comps w))) true) (= (tbl-has comp-id y (:comps w)) true))))
  (intros y hy q) (exact (h3-has-del CompRow comp-id x y (:comps w) q))
  (have a2 (forall [y :- Nat] (=> (< y (:next-id w)) (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) (:comps w)) true)
                                 (= (tbl-all (hk-wif y) (tbl-del comp-id x (:comps w))) true))))
  (intros y hy hx q) (exact (tbl-all-del CompRow comp-id x (hk-wif y) (hk-wif y) (fn [r :- CompRow, hr :- (= (hk-wif y r) true), hx2 :- (= (Nat.beq (comp-id r) x) false)] hr) (:comps w) q))
  (have a3 (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-e1 k2) (:comps w)) true) (= (tbl-all (h3-e1 k2) (tbl-del comp-id x (:comps w))) true))))
  (intros k2 hk q) (exact (tbl-all-del CompRow comp-id x (h3-e1 k2) (h3-e1 k2) (fn [r :- CompRow, hr :- (= (h3-e1 k2 r) true), hx2 :- (= (Nat.beq (comp-id r) x) false)] hr) (:comps w) q))
  (have a4 (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-any (h3-cur k2) (tbl-del comp-id x (:comps w))) true) (= (tbl-any (h3-cur k2) (:comps w)) true))))
  (intros k2 hk q) (exact (h3-any-del-back CompRow comp-id x (h3-cur k2) (:comps w) q))
  (have a5 (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-cs k2) (:comps w)) true) (= (tbl-all (h3-cs k2) (tbl-del comp-id x (:comps w))) true))))
  (intros k2 hk q) (exact (tbl-all-del CompRow comp-id x (h3-cs k2) (h3-cs k2) (fn [r :- CompRow, hr :- (= (h3-cs k2 r) true), hx2 :- (= (Nat.beq (comp-id r) x) false)] hr) (:comps w) q))
  (exact (h3r-cs xm w (tbl-del comp-id x (:comps w)) hs a1 a2 a3 a4 a5 h)))

;; the edges es2 keep every edge of w whose id is not free, and add none
(a/theorem h3r-es-sub [xm :- (List Nat), w :- World, es2 :- (List EdgeRow)]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w))))
      (forall [y :- Nat] (=> (= (tbl-has edge-id y (:edges w)) true) (Or (= (tbl-has edge-id y es2) true) (= (h3-free xm w y) true))))
      (forall [e2 :- EdgeRow] (=> (List.Mem e2 es2) (List.Mem e2 (:edges w))))
      (= (h3-rest xm w) true) (= (h3-rest xm (set-edges w es2)) true))
  (intros hs hk hsub h)
  (have heb (forall [e2 :- EdgeRow] (=> (List.Mem e2 es2) (Or (= (tbl-has edge-id (:id e2) (:edges w)) false) (= (tbl-any (h3-ekq e2) (:edges w)) true)))))
  (intros e2 m) (exact (h3-heb-refl (:edges w) e2 (hsub e2 m)))
  (exact (h3-rest-rel xm w (set-edges w es2) hs
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-has comp-id y (:comps w)) true)] q)
           (fn [y :- Nat, hy :- (< y (:next-id w)), hx :- (= (reach-mem y xm) false), q :- (= (tbl-all (hk-wif y) (:comps w)) true)] q)
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true)] q)
           (rfl) hk (h3-heb-of xm w es2 heb) (Nat.le_refl _)
           (fn [k2 :- RK3, hk2 :- (< (:of k2) (:next-id w)), q :- (= (tbl-all (h3-e1 k2) (:comps w)) true)] q)
           (fn [k2 :- RK3, hk2 :- (< (:of k2) (:next-id w)), q :- (= (tbl-any (h3-cur k2) (:comps w)) true)] q)
           (h3-hc5-refl w) (h3-hrk-refl (:next-id w) (:runs w)) h)))

(a/theorem h3-has-of [A :- Type, idf :- (=> A Nat), y :- Nat, xs :- (List A), P :- Prop]
  (=> (= (tbl-has idf y xs) true) (forall [e :- A] (=> (List.Mem e xs) (= (idf e) y) P)) P)
  (induction xs)
  (case [nil] (intros h k) (simp [tbl-has] at h))
  (case [cons hd t ih]
    (intros h k)
    (cases hb (Nat.beq (idf hd) y))
    (case [true] (exact (k hd (List.Mem.head t) (Nat.eq_of_beq_eq_true hb))))
    (case [false] (simp only [tbl-has hb] at h)
      (exact (ih h (fn [e :- A, m :- (List.Mem e t), q :- (= (idf e) y)] (k e (List.Mem.tail hd m) q)))))))
(a/theorem h3-has-filter [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), e :- A, xs :- (List A)]
  (=> (List.Mem e xs) (= (p e) true) (= (tbl-has idf (idf e) (tbl-filter p xs)) true))
  (induction xs)
  (case [nil] (intros m q) (cases m))
  (case [cons hd t ih]
    (intros m q)
    (cases m)
    (case [head] (simp only [tbl-filter q tbl-has Nat.beq_refl]))
    (case [tail m2]
      (cases hp (p hd))
      (case [false] (simp only [tbl-filter hp]) (exact (ih m2 q)))
      (case [true] (simp only [tbl-filter hp tbl-has])
        (cases hb (Nat.beq (idf hd) (idf e))) (simp only [ih m2 q]) (rfl)))))

;; filtering the edges: every dropped edge's id is free
(a/theorem h3-filter-keep [xm :- (List Nat), w :- World, p :- (=> EdgeRow Bool)]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (p e) false) (= (h3-free xm w (:id e)) true)))
      (forall [y :- Nat] (=> (= (tbl-has edge-id y (:edges w)) true) (Or (= (tbl-has edge-id y (tbl-filter p (:edges w))) true) (= (h3-free xm w y) true)))))
  (intros hfr y q)
  (apply (h3-has-of EdgeRow edge-id y (:edges w) _ q))
  (intros e me ie)
  (cases hp (p e))
  (case [false] (apply Or.inr) (rw [← ie]) (exact (hfr e me hp)))
  (case [true] (apply Or.inl) (rw [← ie]) (exact (h3-has-filter EdgeRow edge-id p e (:edges w) me hp))))

;; ---- a fresh edge (id next-id), then bump
(a/theorem h3-has-cons [A :- Type, idf :- (=> A Nat), y :- Nat, hd :- A, xs :- (List A)]
  (=> (= (tbl-has idf y xs) true) (= (tbl-has idf y (List.cons A hd xs)) true))
  (intro q) (cases hb (Nat.beq (idf hd) y)) (simp only [tbl-has hb q]) (simp only [tbl-has hb]))
(a/theorem h3-edge-fresh [w :- World] (=> (= (inv-sample w) true) (= (tbl-has edge-id (:next-id w) (:edges w)) false))
  (intro hs)
  (have hb := (ids-below-of w hs))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (cases hq (tbl-has edge-id (:next-id w) (:edges w)))
  (rfl)
  (have z := (h3-has-lt EdgeRow edge-id (:next-id w) (:next-id w) (:edges w) (And.left (And.right (And.right (And.right (And.right (And.right hb)))))) hq))
  (omega))
(a/theorem h3r-insert-edge-fresh [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (h3-rest xm w) true) (= (h3-rest xm (insert-edge-fresh w e)) true))
  (intros hs h)
  (have hf := (h3-edge-fresh w hs))
  (have hef (forall [y :- Nat] (=> (= (tbl-has edge-id y (:edges w)) true)
                                  (= (tbl-has edge-id y (tbl-ins (edge-set-marked false (edge-set-id (:next-id w) e)) (:edges w))) true))))
  (intros y q) (exact (h3-has-cons EdgeRow edge-id y _ (:edges w) q))
  (have heb (forall [e2 :- EdgeRow] (=> (List.Mem e2 (tbl-ins (edge-set-marked false (edge-set-id (:next-id w) e)) (:edges w)))
                                        (Or (= (tbl-has edge-id (:id e2) (:edges w)) false) (= (tbl-any (h3-ekq e2) (:edges w)) true)))))
  (intros e2 m)
  (simp only [tbl-ins] at m)
  (cases m)
  (case [head] (exact (Or.inl hf)))
  (case [tail m2] (exact (h3-heb-refl (:edges w) e2 m2)))
  (exact (h3-rest-rel xm w (insert-edge-fresh w e) (h3-db-of w hs)
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-has comp-id y (:comps w)) true)] q)
           (fn [y :- Nat, hy :- (< y (:next-id w)), hx :- (= (reach-mem y xm) false), q :- (= (tbl-all (hk-wif y) (:comps w)) true)] q)
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true)] q)
           (rfl) (h3-hef-all xm w (tbl-ins (edge-set-marked false (edge-set-id (:next-id w) e)) (:edges w)) hef)
           (h3-heb-of xm w (tbl-ins (edge-set-marked false (edge-set-id (:next-id w) e)) (:edges w)) heb) (Nat.le_succ _)
           (fn [k2 :- RK3, hk2 :- (< (:of k2) (:next-id w)), q :- (= (tbl-all (h3-e1 k2) (:comps w)) true)] q)
           (fn [k2 :- RK3, hk2 :- (< (:of k2) (:next-id w)), q :- (= (tbl-any (h3-cur k2) (:comps w)) true)] q)
           (h3-hc5-refl w) (h3-hrk-refl (:next-id w) (:runs w)) h)))
(a/theorem h3r-insert-edge-checked [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (h3-rest xm w) true) (= (h3-rest xm (insert-edge-checked w e)) true))
  (intros hs h)
  (cases hk (edge-ok-in w e))
  (case [false] (simp only [insert-edge-checked hk]) (exact h))
  (case [true] (simp only [insert-edge-checked hk]) (exact (h3r-insert-edge-fresh xm w e hs h))))

;; ---- a pending decrement of a safe creditor
(a/theorem h3r-comp-dec [xm :- (List Nat), w :- World, c :- Nat]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (hk-safe xm (:comps w) c) true) (= (h3-rest xm w) true) (= (h3-rest xm (comp-upd w c comp-dec-pending)) true))
  (intros hs hsf h)
  (have a1 := (h3-c1-upd w c comp-dec-pending hk-dec-id))
  (have c4 := (h3-c4-dec xm (:comps w) c hsf))
  (have a2 (forall [y :- Nat] (=> (< y (:next-id w)) (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) (:comps w)) true)
                                 (= (tbl-all (hk-wif y) (tbl-upd comp-id c comp-dec-pending (:comps w))) true))))
  (intros y hy hx q) (exact (c4 y hx q))
  (have a3 := (h3-c2-upd w c comp-dec-pending hk-dec-id (h3-ep-refl comp-dec-pending hk-dec-ep)))
  (have a4 := (h3-c3-upd w c comp-dec-pending hk-dec-id (h3-ep-refl comp-dec-pending hk-dec-ep)))
  (have a5 := (h3-c5-upd w c comp-dec-pending hk-dec-id (fn [q :- CompRow, z :- (= (Nat.blt (:done-epoch q) (:epoch q)) true)] z)))
  (exact (h3r-cs xm w (tbl-upd comp-id c comp-dec-pending (:comps w)) hs a1 a2 a3 a4 a5 h)))

;; ---- deleting the edges with id x (x free)
(a/theorem h3r-edge-del [xm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-free xm w x) true) (= (h3-rest xm w) true) (= (h3-rest xm (edge-del w x)) true))
  (intros hs hfr h)
  (have hk (forall [y :- Nat] (=> (= (tbl-has edge-id y (:edges w)) true) (Or (= (tbl-has edge-id y (tbl-del edge-id x (:edges w))) true) (= (h3-free xm w y) true)))))
  (intros y q)
  (cases hb (Nat.beq y x))
  (case [false] (exact (Or.inl (h3-has-del-ne EdgeRow edge-id x y (:edges w) hb q))))
  (case [true] (apply Or.inr) (rw [(Nat.eq_of_beq_eq_true hb)]) (exact hfr))
  (exact (h3r-es-sub xm w (tbl-del edge-id x (:edges w)) hs hk (fn [e2 :- EdgeRow, m :- (List.Mem e2 (tbl-del edge-id x (:edges w)))] (h3-del-mem EdgeRow edge-id x e2 (:edges w) m)) h)))

(a/theorem h3r-remove-edge [xm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true) (= (hk-safe xm (:comps w) (:creditor e)) true)))
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-free xm w x) true) (= (h3-rest xm w) true) (= (h3-rest xm (remove-edge w x)) true))
  (intros hu hs hfr h)
  (have h1 := (h3r-edge-del xm w x hs hfr h))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact h1))
    (case [true]
      (simp only [remove-edge hf hm])
      (have hs1 (forall [e2 :- EdgeRow] (=> (List.Mem e2 (:edges (edge-del w x))) (< (:debtor e2) (:next-id (edge-del w x))))))
      (intros e2 m) (exact (hs e2 (h3-del-mem EdgeRow edge-id x e2 (:edges w) m)))
      (exact (h3r-comp-dec xm (edge-del w x) (:creditor e) hs1 (hu e hf hm) h1)))))

;; ---- an activation's own edges (creditor a; a is no computation)
(a/theorem h3r-drop-cred [xm :- (List Nat), w :- World, a :- Nat]
  (=> (= (tbl-has comp-id a (:comps w)) false)
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (cred-ne a e) false) (= (h3-free xm w (:id e)) true)))
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (drop-cred-edges w a)) true))
  (intros hc hfr hs h)
  (have h1 := (h3r-es-sub xm w (tbl-filter (cred-ne a) (:edges w)) hs (h3-filter-keep xm w (cred-ne a) hfr)
                (fn [e2 :- EdgeRow, m :- (List.Mem e2 (tbl-filter (cred-ne a) (:edges w)))] (filter-mem EdgeRow (cred-ne a) e2 (:edges w) m)) h))
  (simp only [drop-cred-edges comp-upd set-comps set-edges (tbl-upd-absent CompRow comp-id a (comp-set-pending 0) (:comps w) hc)])
  (exact h1))
(a/theorem h3r-drop-act [xm :- (List Nat), w :- World, a :- Nat]
  (=> (= (tbl-has comp-id a (:comps w)) false)
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (cred-ne a e) false) (= (h3-free xm w (:id e)) true)))
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (drop-act w a)) true))
  (intros hc hfr hs h)
  (exact (h3r-act-del xm (drop-cred-edges w a) a (h3r-drop-cred xm w a hc hfr hs h))))

;; ---- drop-edges: the dropped edges are free, the dropped marked ones have safe creditors
(a/theorem h3-e1-resync [k :- RK3, es :- (List EdgeRow), cs :- (List CompRow)]
  (= (tbl-all (h3-e1 k) (comps-resync es cs)) (tbl-all (h3-e1 k) cs))
  (induction cs)
  (case [nil] (simp only [comps-resync]))
  (case [cons hd t ih]
    (have e (= (h3-e1 k (comp-resync es hd)) (h3-e1 k hd))) (rfl)
    (simp only [comps-resync tbl-all e ih])))
(a/theorem h3-cur-resync [k :- RK3, es :- (List EdgeRow), cs :- (List CompRow)]
  (= (tbl-any (h3-cur k) (comps-resync es cs)) (tbl-any (h3-cur k) cs))
  (induction cs)
  (case [nil] (simp only [comps-resync]))
  (case [cons hd t ih]
    (have e (= (h3-cur k (comp-resync es hd)) (h3-cur k hd))) (rfl)
    (simp only [comps-resync tbl-any e ih])))
(a/theorem h3-cs-resync [k :- RK3, es :- (List EdgeRow), cs :- (List CompRow)]
  (= (tbl-all (h3-cs k) (comps-resync es cs)) (tbl-all (h3-cs k) cs))
  (induction cs)
  (case [nil] (simp only [comps-resync]))
  (case [cons hd t ih]
    (have e (= (h3-cs k (comp-resync es hd)) (h3-cs k hd))) (rfl)
    (simp only [comps-resync tbl-all e ih])))
(a/theorem h3r-drop-edges [xm :- (List Nat), w :- World, p :- (=> EdgeRow Bool)]
  (=> (= (tbl-all (hk-dok xm (:comps w) p) (:edges w)) true) (= (pending-exact w) true)
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (p e) false) (= (h3-free xm w (:id e)) true)))
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-rest xm w) true) (= (h3-rest xm (drop-edges w p)) true))
  (intros hdk hpe hfr hs h)
  (have h1 := (h3r-es-sub xm w (tbl-filter p (:edges w)) hs (h3-filter-keep xm w p hfr)
                (fn [e2 :- EdgeRow, m :- (List.Mem e2 (tbl-filter p (:edges w)))] (filter-mem EdgeRow p e2 (:edges w) m)) h))
  (have hs1 (forall [e2 :- EdgeRow] (=> (List.Mem e2 (:edges (set-edges w (tbl-filter p (:edges w))))) (< (:debtor e2) (:next-id (set-edges w (tbl-filter p (:edges w))))))))
  (intros e2 m) (exact (hs e2 (filter-mem EdgeRow p e2 (:edges w) m)))
  (have a1 (forall [y :- Nat] (=> (< y (:next-id w)) (= (tbl-has comp-id y (comps-resync (tbl-filter p (:edges w)) (:comps w))) true) (= (tbl-has comp-id y (:comps w)) true))))
  (intros y hy q) (rw [has-resync] at q) (exact q)
  (have a2 (forall [y :- Nat] (=> (< y (:next-id w)) (= (reach-mem y xm) false) (= (tbl-all (hk-wif y) (:comps w)) true)
                                 (= (tbl-all (hk-wif y) (comps-resync (tbl-filter p (:edges w)) (:comps w))) true))))
  (intros y hy hx q)
  (cases hsf (hk-safe xm (:comps w) y))
  (case [false]
    (have ce := (hk-count-eq xm (:comps w) p y (:edges w) hdk hsf))
    (simp only [pending-exact pending-exact-in] at hpe)
    (exact (hk-wif-resync-eq y (:edges w) (tbl-filter p (:edges w)) (:comps w) ce hpe q)))
  (case [true]
    (simp only [hk-safe hx Bool.false_or] at hsf)
    (exact (hk-wif-resync-s y (tbl-filter p (:edges w)) (:comps w) hsf q)))
  (have a3 (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-e1 k2) (:comps w)) true) (= (tbl-all (h3-e1 k2) (comps-resync (tbl-filter p (:edges w)) (:comps w))) true))))
  (intros k2 hk q) (rw [h3-e1-resync]) (exact q)
  (have a4 (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-any (h3-cur k2) (comps-resync (tbl-filter p (:edges w)) (:comps w))) true) (= (tbl-any (h3-cur k2) (:comps w)) true))))
  (intros k2 hk q) (rw [h3-cur-resync] at q) (exact q)
  (have a5 (forall [k2 :- RK3] (=> (< (:of k2) (:next-id w)) (= (tbl-all (h3-cs k2) (:comps w)) true) (= (tbl-all (h3-cs k2) (comps-resync (tbl-filter p (:edges w)) (:comps w))) true))))
  (intros k2 hk q) (rw [h3-cs-resync]) (exact q)
  (exact (h3r-cs xm (set-edges w (tbl-filter p (:edges w))) (comps-resync (tbl-filter p (:edges w)) (:comps w)) hs1 a1 a2 a3 a4 a5 h1)))

;; ===========================================================================
;; Part C. Full-bundle forms of the primitives and the bundle copy
;; ===========================================================================

;; ---- row-function facts for the source patch
(a/theorem comp-inc-epoch-h3ep [c :- CompRow] (<= (:epoch c) (:epoch (comp-inc-epoch c)))
  (simp only [comp-inc-epoch]) (exact (Nat.le_succ _)))
(a/theorem comp-demand-row-h3ep [c :- CompRow] (<= (:epoch c) (:epoch (comp-demand-row c)))
  (cases hb (Nat.beq (:done-epoch c) 0))
  (simp only [comp-demand-row hb]) (exact (Nat.le_succ _))
  (simp only [comp-demand-row hb]) (exact (Nat.le_refl _)))
(a/theorem comp-replace-row-h3ep [i :- (List Nat), b :- Nat, c :- CompRow] (<= (:epoch c) (:epoch (comp-replace-row i b c)))
  (simp only [comp-replace-row]) (exact (Nat.le_succ _)))
(a/theorem comp-start-row-h3ep [rid :- Nat, c :- CompRow] (<= (:epoch c) (:epoch (comp-start-row rid c)))
  (cases hb (Bool.and (:idle c) (Bool.not (Nat.beq (:done-epoch c) 0))))
  (simp only [comp-start-row start-epoch hb]) (exact (Nat.le_refl _))
  (simp only [comp-start-row start-epoch hb]) (exact (Nat.le_succ _)))
(a/theorem h3-lt-succ [a :- Nat, b :- Nat] (=> (< a b) (< a (+ b 1))) (intro h) (omega))
(a/theorem h3-zero-lt [b :- Nat] (< 0 (+ b 1)) (omega))
(a/theorem comp-inc-epoch-h3ds [c :- CompRow] (=> (= (Nat.blt (:done-epoch c) (:epoch c)) true) (= (Nat.blt (:done-epoch (comp-inc-epoch c)) (:epoch (comp-inc-epoch c))) true))
  (intro h) (have z := (gd-lt-of _ _ h)) (simp only [comp-inc-epoch]) (exact (gd-blt-of _ _ (h3-lt-succ _ _ z))))
(a/theorem comp-demand-row-h3ds [c :- CompRow] (=> (= (Nat.blt (:done-epoch c) (:epoch c)) true) (= (Nat.blt (:done-epoch (comp-demand-row c)) (:epoch (comp-demand-row c))) true))
  (intro h) (have z := (gd-lt-of _ _ h))
  (cases hb (Nat.beq (:done-epoch c) 0))
  (simp only [comp-demand-row hb]) (exact (gd-blt-of _ _ (h3-lt-succ _ _ z)))
  (simp only [comp-demand-row hb]) (exact h))
(a/theorem comp-replace-row-h3ds [i :- (List Nat), b :- Nat, c :- CompRow] (=> (= (Nat.blt (:done-epoch c) (:epoch c)) true) (= (Nat.blt (:done-epoch (comp-replace-row i b c)) (:epoch (comp-replace-row i b c))) true))
  (intro h) (have z := (gd-lt-of _ _ h))
  (cases hb (:idle c))
  (simp only [comp-replace-row hb]) (exact (gd-blt-of _ _ (h3-lt-succ _ _ z)))
  (simp only [comp-replace-row hb]))
(a/theorem comp-start-row-h3ds [rid :- Nat, c :- CompRow] (=> (= (Nat.blt (:done-epoch c) (:epoch c)) true) (= (Nat.blt (:done-epoch (comp-start-row rid c)) (:epoch (comp-start-row rid c))) true))
  (intro h) (have z := (gd-lt-of _ _ h))
  (cases hb (Bool.and (:idle c) (Bool.not (Nat.beq (:done-epoch c) 0))))
  (simp only [comp-start-row start-epoch hb]) (exact h)
  (simp only [comp-start-row start-epoch hb]) (exact (gd-blt-of _ _ (h3-lt-succ _ _ z))))
(a/theorem run-wake-h3al [r :- RunRow] (=> (= (run-alive r) true) (= (run-alive (run-wake r)) true))
  (intro h)
  (cases hp (Nat.beq (:act r) act-parked))
  (simp only [run-alive run-wake wake-act hp]) (simp only [run-alive] at h) (exact h)
  (simp only [run-alive run-wake wake-act hp act-active act-done]))
(a/theorem h3-mh-filter [z :- Nat, p :- (=> Member Bool), ms :- (List Member)]
  (=> (= (mem-has z (tbl-filter p ms)) true) (= (mem-has z ms) true))
  (induction ms)
  (case [nil] (intro h) (simp only [tbl-filter] at h) (simp [mem-has] at h))
  (case [cons hd t ih]
    (intro h)
    (cases hb (Nat.beq (:edge hd) z))
    (case [true] (simp only [mem-has hb]))
    (case [false]
      (simp only [mem-has hb])
      (cases hp (p hd))
      (case [false] (simp only [tbl-filter hp] at h) (exact (ih h)))
      (case [true] (simp only [tbl-filter hp mem-has hb] at h) (exact (ih h))))))
(a/theorem act-fill-h3sub [y :- Nat, v :- RunResult]
  (forall [b :- ActRow, z :- Nat] (=> (= (mem-has z (:members (act-fill y v b))) true) (= (mem-has z (:members b)) true)))
  (intros b z h)
  (simp only [act-fill] at h)
  (exact (h3-mh-filter z (mem-other y) (:members b) h)))

;; ---- full-bundle forms
(a/theorem h3-edge-upd-m [xm :- (List Nat), w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                          hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                          hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                          hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                          hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                          hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e))),
                          ha :- (forall [e :- EdgeRow] (=> (= (Nat.beq (:phase e) ph-armed) true) (= (Nat.beq (:phase (f e)) ph-armed) true)))]
  (=> (= (h3 xm w) true) (= (h3 xm (edge-upd w x f)) true))
  (intro h) (have hs := (h3-sample xm w h))
  (exact (h3-intro xm _ (inv-edge-upd w x f hid hk hc hd hm hs) (h3r-edge-upd xm w x f hid hk hc hd ha (h3-db-of w hs) (h3-rest-of xm w h)))))
(a/theorem h3-run-upd-m [xm :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                         hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         hof :- (forall [r :- RunRow] (= (:of (f r)) (:of r))),
                         hep :- (forall [r :- RunRow] (= (:epoch (f r)) (:epoch r))),
                         hal :- (forall [r :- RunRow] (=> (= (run-alive r) true) (= (run-alive (f r)) true)))]
  (=> (= (h3 xm w) true) (= (h3 xm (run-upd w x f)) true))
  (intro h) (have hs := (h3-sample xm w h))
  (exact (h3-intro xm _ (inv-run-upd w x f hid hs) (h3r-run-upd xm w x f hid hof hep hal (h3-db-of w hs) (h3-rest-of xm w h)))))
(a/theorem h3-task-upd-m [xm :- (List Nat), w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                          hid :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                          hrun :- (forall [t :- TaskRow] (= (:run (f t)) (:run t)))]
  (=> (= (h3 xm w) true) (= (h3 xm (task-upd w x f)) true))
  (intro h) (have hs := (h3-sample xm w h))
  (exact (h3-intro xm _ (inv-task-upd w x f hid hs) (h3r-task-upd xm w x f hid hrun (h3-db-of w hs) (h3-rest-of xm w h)))))
(a/theorem h3-act-upd-m [xm :- (List Nat), w :- World, x :- Nat, f :- (=> ActRow ActRow),
                         hid :- (forall [b :- ActRow] (= (act-id (f b)) (act-id b))),
                         hrun :- (forall [b :- ActRow] (= (:run (f b)) (:run b))),
                         hsub :- (forall [b :- ActRow, y :- Nat] (=> (= (mem-has y (:members (f b))) true) (= (mem-has y (:members b)) true)))]
  (=> (= (h3 xm w) true) (= (h3 xm (act-upd w x f)) true))
  (intro h) (have hs := (h3-sample xm w h))
  (exact (h3-intro xm _ (inv-act-upd w x f hid hs) (h3r-act-upd xm w x f hid hrun hsub hs (h3-rest-of xm w h)))))
(a/theorem h3-unmark-edge [xm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true) (= (hk-safe xm (:comps w) (:creditor e)) true)))
      (= (h3 xm w) true) (= (h3 xm (unmark-edge w x)) true))
  (intros hu h) (have hs := (h3-sample xm w h))
  (exact (h3-intro xm _ (unmark-edge-inv-sample w x hs) (h3r-unmark-edge xm w x hu (h3-db-of w hs) (h3-rest-of xm w h)))))
(a/theorem h3-remove-edge [xm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true) (= (hk-safe xm (:comps w) (:creditor e)) true)))
      (= (h3-free xm w x) true) (= (h3 xm w) true) (= (h3 xm (remove-edge w x)) true))
  (intros hu hf h) (have hs := (h3-sample xm w h))
  (exact (h3-intro xm _ (inv-remove-edge w x hs) (h3r-remove-edge xm w x hu (h3-db-of w hs) hf (h3-rest-of xm w h)))))
(a/theorem h3-drop-cred [xm :- (List Nat), w :- World, a :- Nat]
  (=> (= (tbl-has comp-id a (:comps w)) false)
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (cred-ne a e) false) (= (h3-free xm w (:id e)) true)))
      (= (h3 xm w) true) (= (h3 xm (drop-cred-edges w a)) true))
  (intros hc hf h) (have hs := (h3-sample xm w h))
  (exact (h3-intro xm _ (inv-drop-cred w a hs) (h3r-drop-cred xm w a hc hf (h3-db-of w hs) (h3-rest-of xm w h)))))
(a/theorem h3-drop-act [xm :- (List Nat), w :- World, a :- Nat]
  (=> (= (tbl-has comp-id a (:comps w)) false)
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (cred-ne a e) false) (= (h3-free xm w (:id e)) true)))
      (= (h3 xm w) true) (= (h3 xm (drop-act w a)) true))
  (intros hc hf h) (have hs := (h3-sample xm w h))
  (exact (h3-intro xm _ (inv-drop-act w a hs) (h3r-drop-act xm w a hc hf (h3-db-of w hs) (h3-rest-of xm w h)))))
(a/theorem h3-drop-edges [xm :- (List Nat), w :- World, p :- (=> EdgeRow Bool)]
  (=> (= (tbl-all (hk-dok xm (:comps w) p) (:edges w)) true)
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (p e) false) (= (h3-free xm w (:id e)) true)))
      (= (h3 xm w) true) (= (h3 xm (drop-edges w p)) true))
  (intros hk hf h) (have hs := (h3-sample xm w h))
  (exact (h3-intro xm _ (inv-drop-edges w p hs) (h3r-drop-edges xm w p hk (And.left (h3-parts xm w h)) hf (h3-db-of w hs) (h3-rest-of xm w h)))))
(a/theorem h3-run-del [xm :- (List Nat), w :- World, x :- Nat]
  (=> (= (tbl-all (same-id-then run-id x (fn [r :- RunRow] (Bool.not (run-alive r)))) (:runs w)) true)
      (= (h3 xm w) true) (= (h3 xm (run-del w x)) true))
  (intros hn h) (have hs := (h3-sample xm w h))
  (exact (h3-intro xm _ (inv-run-del w x hs) (h3r-run-del xm w x hn (h3-db-of w hs) (h3-rest-of xm w h)))))

(def H3 (mk-bundle 'h3 '[xm :- (List Nat)] "hm3-" {}))
;; renamed to full-bundle forms with extra premises (their callers are overrides) or to a missing name
;; (a primitive the bundle does not keep in general: every caller is an override)
(swap! (:renames H3) assoc 'inv-parts 'h3-parts
       'unmark-edge-inv-sample 'h3-unmark-edge 'inv-remove-edge 'h3-remove-edge 'inv-drop-cred 'h3-drop-cred
       'inv-drop-act 'h3-drop-act 'inv-drop-edges 'h3-drop-edges 'inv-run-del 'h3-run-del
       'inv-act-ins-fresh 'h3-act-ins-NONE 'inv-filter-world 'h3-filter-world-NONE
       'inv-comp-upd 'h3-comp-upd-NONE 'inv-run-upd 'h3-run-upd-NONE 'inv-task-upd 'h3-task-upd-NONE
       'inv-act-upd 'h3-act-upd-NONE 'inv-edge-upd 'h3-edge-upd-NONE)
(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-set-pins
            inv-resource-del inv-scope-del inv-cleanup-ins inv-set-released inv-set-pending-act]]
  (prim! H3 o nil))
(prim! H3 'inv-bump '(h3r-bump xm w (h3-db-of w (h3-sample xm w h0)) R))
(prim! H3 'inv-source-ins-fresh '(h3r-bump xm (source-ins w r) (h3-db-of w (h3-sample xm w h1)) R))
(prim! H3 'inv-resource-ins-fresh '(h3r-bump xm (resource-ins w r) (h3-db-of w (h3-sample xm w h1)) R))
(prim! H3 'inv-scope-ins-fresh '(h3r-bump xm (scope-ins w r) (h3-db-of w (h3-sample xm w h1)) R))
(prim! H3 'inv-run-ins-fresh '(h3r-run-ins xm w r h0 (h3-db-of w (h3-sample xm w h1)) R))
(prim! H3 'inv-task-ins-fresh '(h3r-task-ins xm w r h0 (h3-db-of w (h3-sample xm w h1)) R))
(prim! H3 'inv-comp-ins-fresh '(h3r-comp-ins xm w r h0 (h3-db-of w (h3-sample xm w h2)) R))
(prim! H3 'mark-edge-inv-sample '(h3r-mark-edge xm w x (h3-db-of w (h3-sample xm w h0)) R))
(prim! H3 'insert-edge-fresh-inv-sample '(h3r-insert-edge-fresh xm w e (h3-sample xm w h1) R))
(prim! H3 'inv-insert-edge-checked '(h3r-insert-edge-checked xm w e (h3-sample xm w h0) R))
(prim! H3 'inv-comp-del-unref '(h3r-comp-del xm w x (h3-db-of w (h3-sample xm w h1)) R))

;; ---- the source patch: row-function edits go through the -m forms when the function keeps what h3 reads
(def ^:private h3-comp-ok '#{comp-detach-row comp-set-rank comp-inc-epoch comp-dec-handles comp-start-row comp-set-run comp-h1
                             comp-adopt-row comp-consume-adopt comp-add-basis comp-h0 comp-replace-row comp-clear-run comp-demand-row
                             comp-cut-row comp-rebasis})
(def ^:private h3-comp-ep '#{comp-inc-epoch comp-demand-row comp-replace-row comp-start-row})
(def ^:private h3-comp-hkm '#{comp-inc-epoch comp-demand-row comp-replace-row comp-start-row})
(def ^:private h3-run-ok '#{run-wake run-tick run-enter-row run-fin-pop run-tick-park run-fin-pop-end run-park-row run-unres run-arm run-fin-push})
(def ^:private h3-edge-ok '#{edge-reawait edge-set-seen edge-rearm edge-reread})
(defn- h3-fhead [f] (if (seq? f) (first f) f))
(defn- h3-lapp [f lem] (if (seq? f) (apply list lem (rest f)) lem))
(defn h3-patch [form]
  (->> (@#'spindel.v2.idle/fix-f form)
       (subst-forms (fn [y] (and (seq? y) (= 'inv-comp-upd (first y)) (>= (count y) 6) (contains? h3-comp-ok (h3-fhead (nth y 3)))))
                    (fn [[_ w x f hid hp & more]]
                      (let [h (h3-fhead f)]
                        (apply list 'h3-comp-upd-m 'xm w x f hid hp
                               (if (contains? h3-comp-ep h) (h3-lapp f (symbol (str h "-h3ep"))) '(fn [c :- CompRow] (Nat.le_refl (:epoch c))))
                               (if (contains? h3-comp-hkm h) (h3-lapp f (symbol (str h "-hkm"))) '(fn [c :- CompRow, hc :- (= (hk-wt c) true)] hc))
                               (if (contains? h3-comp-ep h) (h3-lapp f (symbol (str h "-h3ds")))
                                   '(fn [c :- CompRow, hc :- (= (Nat.blt (:done-epoch c) (:epoch c)) true)] hc))
                               more))))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (>= (count y) 5) (contains? h3-run-ok (h3-fhead (nth y 3)))))
                    (fn [[_ w x f hid & more]]
                      (apply list 'h3-run-upd-m 'xm w x f hid '(fn [r :- RunRow] (Eq.refl (:of r))) '(fn [r :- RunRow] (Eq.refl (:epoch r)))
                             (case (h3-fhead f)
                               run-wake 'run-wake-h3al
                               (run-park-row run-tick-park) '(fn [r :- RunRow, q :- (= (run-alive r) true)] (Eq.refl true))
                               '(fn [r :- RunRow, q :- (= (run-alive r) true)] q))
                             more)))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-task-upd (first y)) (>= (count y) 5) (not= 'task-clear-run (h3-fhead (nth y 3)))))
                    (fn [[_ w x f hid & more]] (apply list 'h3-task-upd-m 'xm w x f hid '(fn [t :- TaskRow] (Eq.refl (:run t))) more)))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-act-upd (first y)) (>= (count y) 5) (= 'act-fill (h3-fhead (nth y 3)))))
                    (fn [[_ w x f hid & more]]
                      (apply list 'h3-act-upd-m 'xm w x f hid '(fn [b :- ActRow] (Eq.refl (:run b))) (h3-lapp f 'act-fill-h3sub) more)))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-edge-upd (first y)) (>= (count y) 9)
                                 (or (contains? h3-edge-ok (h3-fhead (nth y 3))) (= '(edge-set-phase ph-armed) (nth y 3)))))
                    (fn [[_ w x f hid hk hc hd hm & more]]
                      (apply list 'h3-edge-upd-m 'xm w x f hid hk hc hd hm
                             (if (= 'edge-set-seen (h3-fhead f)) '(fn [e :- EdgeRow, q :- (= (Nat.beq (:phase e) ph-armed) true)] q)
                                 '(fn [e :- EdgeRow, q :- (= (Nat.beq (:phase e) ph-armed) true)] (Nat.beq_refl ph-armed)))
                             more)))))
(defn h3-patch2 [form]
  (->> (h3-patch form)
       (subst-forms (fn [y] (and (seq? y) (= 'inv-edge-set-phase (first y)) (= 'ph-armed (nth y 3 nil))))
                    (fn [[_ w x p & more]]
                      (apply list 'h3-edge-upd-m 'xm w x '(edge-set-phase ph-armed) '(edge-set-phase-edge-id ph-armed)
                             '(fn [e :- EdgeRow] (Eq.refl (:kind e))) '(fn [e :- EdgeRow] (Eq.refl (:creditor e)))
                             '(fn [e :- EdgeRow] (Eq.refl (:debtor e))) '(fn [e :- EdgeRow] (Eq.refl (:marked e)))
                             '(fn [e :- EdgeRow, q :- (= (Nat.beq (:phase e) ph-armed) true)] (Nat.beq_refl ph-armed))
                             more)))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! H3 n h3-patch2))

;; ===========================================================================
;; Part D. The fires
;; ===========================================================================

;; the obligation of a member x of activation a (run r) in a world with h3, unfolded
(a/theorem h3-ob-use [xm :- (List Nat), w :- World, a :- ActRow, r :- RunRow, x :- Nat, e :- EdgeRow]
  (=> (= (h3-rest xm w) true) (List.Mem a (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run a))
      (= (reach-mem (:of r) xm) false) (= (tbl-any (h3-cur (rk3 r)) (:comps w)) true)
      (= (reach-mem x (act-contrib a)) true) (= (reach-mem x xm) false)
      (List.Mem e (:edges w)) (= (:id e) x)
      (And (= (h3-s (:acts w) a (rk3 r) e) true) (Or (= (reach-mem (:debtor e) xm) true) (= (h3-m (:comps w) (:tasks w) (:runs w) e) true))))
  (intros h ma mr ir hx hc hm hxx me ie)
  (have ha := (tbl-all-mem ActRow _ a (:acts w) h ma))
  (simp only [h3-a Bool.and_eq_true] at ha)
  (have hr := (tbl-all-mem RunRow _ r (:runs w) (And.right ha) mr))
  (simp only [h3-rr] at hr)
  (have i2 (= (Nat.beq (:id (rk3 r)) (:run a)) true)) (simp only [rk3 ir Nat.beq_refl])
  (have hx2 (= (reach-mem (:of (rk3 r)) xm) false)) (exact hx)
  (simp only [h3-r i2 Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
  (have ob := (And.right (And.right hr)))
  (simp only [h3-ob hx2 hc Bool.not_true Bool.false_or Bool.and_eq_true] at ob)
  (have hxm := (tbl-all-mem Nat _ x (act-contrib a) (And.right ob) (Iff.mp (reach-mem-iff x (act-contrib a)) hm)))
  (simp only [h3-x hxx Bool.false_or Bool.and_eq_true] at hxm)
  (have ek := (tbl-all-mem EdgeRow _ e (:edges w) (And.right hxm) me))
  (have ie2 (= (Nat.beq (:id e) x) true)) (rw [ie]) (exact (Nat.beq_refl x))
  (simp only [h3-eok ie2 Bool.not_true Bool.false_or Bool.and_eq_true Bool.or_eq_true] at ek)
  (exact ek))

;; an edge whose creditor c is no computation and no activation is free
(a/theorem h3-free-cred [xm :- (List Nat), w :- World, c :- Nat, e :- EdgeRow]
  (=> (= (h3-rest xm w) true) (= (tbl-has comp-id c (:comps w)) false)
      (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (Nat.beq (:id b) c) false)))
      (List.Mem e (:edges w)) (= (:creditor e) c) (= (h3-free xm w (:id e)) true))
  (intros h hcc hac me ec)
  (simp only [h3-free])
  (apply all-of-mem) (intros b mb)
  (simp only [h3-fa])
  (apply all-of-mem) (intros r mr)
  (simp only [h3-fr Bool.or_eq_true])
  (cases ir (Nat.beq (:id r) (:run b)))
  (case [false] (exact (Or.inl (rfl))))
  (case [true]
    (apply Or.inr)
    (cases hx (reach-mem (:of r) xm))
    (case [true] (exact (Or.inl (rfl))))
    (case [false]
      (apply Or.inr)
      (cases hc (tbl-any (h3-cur (rk3 r)) (:comps w)))
      (case [false] (exact (Or.inl (rfl))))
      (case [true]
        (apply Or.inr)
        (cases hm (reach-mem (:id e) (act-contrib b)))
        (case [false] (exact (Or.inl (rfl))))
        (case [true]
          (apply Or.inr)
          (cases hxx (reach-mem (:id e) xm))
          (case [true] (rfl))
          (case [false]
            (have u := (h3-ob-use xm w b r (:id e) e h mb mr (Nat.eq_of_beq_eq_true ir) hx hc hm hxx me (rfl)))
            (have sk := (And.left u))
            (simp only [h3-s Bool.and_eq_true] at sk)
            (cases hk (Nat.beq (:kind e) ek-dep))
            (case [true]
              (have c1 := (And.left (And.right sk)))
              (simp only [hk Bool.not_true Bool.false_or rk3] at c1)
              (have c2 := (Nat.eq_of_beq_eq_true c1))
              (apply (any-elim CompRow (h3-cur (rk3 r)) _ (:comps w) hc))
              (intros q mq hq)
              (simp only [h3-cur rk3 Bool.and_eq_true] at hq)
              (have q1 := (Nat.eq_of_beq_eq_true (And.left hq)))
              (have z := (mem-ids-has CompRow comp-id q (:comps w) mq))
              (rw [nat-mem-ids] at z)
              (have q2 (= (comp-id q) c)) (simp only [comp-id]) (rw [q1 ← c2 ec])
              (rw [q2] at z) (rw [hcc] at z) (cases z))
            (case [false]
              (have c1 := (And.left (And.right (And.right sk))))
              (simp only [hk Bool.false_or] at c1)
              (have c2 := (Nat.eq_of_beq_eq_true c1))
              (have z := (hac b mb))
              (rw [← c2 ec] at z) (rw [Nat.beq_refl] at z) (cases z))))))))

;; ---- edge edits on a free edge (no condition on the phase)
(a/theorem h3-heb-upd-free [x :- Nat, f :- (=> EdgeRow EdgeRow), hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))), es :- (List EdgeRow)]
  (forall [e2 :- EdgeRow] (=> (List.Mem e2 (tbl-upd edge-id x f es)) (Or (= (tbl-any (h3-ekq e2) es) true) (= (Nat.beq (:id e2) x) true))))
  (induction es)
  (case [nil] (intros e2 m) (simp only [tbl-upd] at m) (cases m))
  (case [cons hd t ih]
    (intros e2 m)
    (cases hx (Nat.beq (edge-id hd) x))
    (case [false]
      (simp only [tbl-upd hx] at m)
      (cases m)
      (case [head] (exact (Or.inl (any-elim-of EdgeRow (h3-ekq hd) hd (List.cons EdgeRow hd t) (List.Mem.head t) (h3-ekq-refl hd)))))
      (case [tail m2]
        (have k := (ih e2 m2))
        (cases k)
        (case [inl z] (exact (Or.inl (any-cons-of EdgeRow (h3-ekq e2) hd t z))))
        (case [inr z] (exact (Or.inr z)))))
    (case [true]
      (simp only [tbl-upd hx] at m)
      (cases m)
      (case [head] (apply Or.inr) (have e1 (= (:id (f hd)) (:id hd))) (exact (hid hd)) (rw [e1]) (exact hx))
      (case [tail m2]
        (have k := (ih e2 m2))
        (cases k)
        (case [inl z] (exact (Or.inl (any-cons-of EdgeRow (h3-ekq e2) hd t z))))
        (case [inr z] (exact (Or.inr z)))))))
(a/theorem h3r-edge-upd-free [xm :- (List Nat), w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                              hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e)))]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (< (:debtor e) (:next-id w)))) (= (h3-free xm w x) true) (= (h3-rest xm w) true) (= (h3-rest xm (edge-upd w x f)) true))
  (intros hs hfr h)
  (have heb (forall [e2 :- EdgeRow] (=> (List.Mem e2 (tbl-upd edge-id x f (:edges w)))
        (Or (= (tbl-has edge-id (:id e2) (:edges w)) false) (Or (= (tbl-any (h3-ekq e2) (:edges w)) true) (= (h3-free xm w (:id e2)) true))))))
  (intros e2 m)
  (have k := (h3-heb-upd-free x f hid (:edges w) e2 m))
  (cases k)
  (case [inl z] (exact (Or.inr (Or.inl z))))
  (case [inr z] (apply Or.inr) (apply Or.inr) (rw [(Nat.eq_of_beq_eq_true z)]) (exact hfr))
  (exact (h3-rest-rel xm w (edge-upd w x f) hs
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-has comp-id y (:comps w)) true)] q)
           (fn [y :- Nat, hy :- (< y (:next-id w)), hx :- (= (reach-mem y xm) false), q :- (= (tbl-all (hk-wif y) (:comps w)) true)] q)
           (fn [y :- Nat, hy :- (< y (:next-id w)), q :- (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true)] q)
           (rfl) (h3-hef-all xm w (tbl-upd edge-id x f (:edges w)) (h3-ef-upd xm w x f hid)) heb (Nat.le_refl _)
           (fn [k2 :- RK3, hk2 :- (< (:of k2) (:next-id w)), q :- (= (tbl-all (h3-e1 k2) (:comps w)) true)] q)
           (fn [k2 :- RK3, hk2 :- (< (:of k2) (:next-id w)), q :- (= (tbl-any (h3-cur k2) (:comps w)) true)] q)
           (h3-hc5-refl w) (h3-hrk-refl (:next-id w) (:runs w)) h)))

;; ---- invalidate: the epoch step of the creditor ends every current activation holding the edge
(a/theorem h3-cur-inc [k :- RK3, c :- Nat, cs :- (List CompRow)]
  (=> (= (Nat.beq (:of k) c) true) (= (tbl-all (h3-e1 k) cs) true) (= (tbl-any (h3-cur k) (tbl-upd comp-id c comp-inc-epoch cs)) true) False)
  (induction cs)
  (case [nil] (intros hk he hc) (simp [tbl-upd tbl-any] at hc))
  (case [cons hd t ih]
    (intros hk he hc)
    (simp only [tbl-all Bool.and_eq_true] at he)
    (cases hx (Nat.beq (comp-id hd) c))
    (case [false]
      (simp only [tbl-upd hx tbl-any Bool.or_eq_true] at hc)
      (cases hc)
      (case [inl z]
        (simp only [h3-cur Bool.and_eq_true] at z)
        (have e1 := (Nat.eq_of_beq_eq_true (And.left z))) (have e2 := (Nat.eq_of_beq_eq_true hk))
        (have e3 (= (Nat.beq (comp-id hd) c) true)) (simp only [comp-id]) (rw [e1 e2]) (exact (Nat.beq_refl _))
        (rw [hx] at e3) (cases e3))
      (case [inr z] (exact (ih hk (And.right he) z))))
    (case [true]
      (simp only [tbl-upd hx tbl-any Bool.or_eq_true] at hc)
      (cases hc)
      (case [inl z]
        (simp only [h3-cur comp-inc-epoch Bool.and_eq_true] at z)
        (have e1 := (And.left he))
        (simp only [h3-e1 Bool.or_eq_true] at e1)
        (have i1 (= (Nat.beq (:id hd) (:of k)) true)) (exact (And.left z))
        (cases e1)
        (case [inl z1] (rw [i1] at z1) (cases z1))
        (case [inr z1]
          (have l1 := (gd-le-of _ _ z1)) (have l2 := (gd-le-of _ _ (And.right z)))
          (omega)))
      (case [inr z] (exact (ih hk (And.right he) z))))))

(a/theorem h3-free-inc [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (h3-rest xm w) true) (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) true)
      (= (h3-free xm (comp-upd w (:creditor e) comp-inc-epoch) (:id e)) true))
  (intros h me hk)
  (simp only [h3-free comp-upd set-comps])
  (apply all-of-mem) (intros b mb)
  (simp only [h3-fa])
  (apply all-of-mem) (intros r mr)
  (simp only [h3-fr Bool.or_eq_true])
  (cases ir (Nat.beq (:id r) (:run b)))
  (case [false] (exact (Or.inl (rfl))))
  (case [true]
    (apply Or.inr)
    (cases hx (reach-mem (:of r) xm))
    (case [true] (exact (Or.inl (rfl))))
    (case [false]
      (apply Or.inr)
      (cases hc (tbl-any (h3-cur (rk3 r)) (tbl-upd comp-id (:creditor e) comp-inc-epoch (:comps w))))
      (case [false] (exact (Or.inl (rfl))))
      (case [true]
        (apply Or.inr)
        (cases hm (reach-mem (:id e) (act-contrib b)))
        (case [false] (exact (Or.inl (rfl))))
        (case [true]
          (apply Or.inr)
          (cases hxx (reach-mem (:id e) xm))
          (case [true] (rfl))
          (case [false]
            (have hcw := (h3-any-upd-back CompRow comp-id (:creditor e) comp-inc-epoch (h3-cur (rk3 r))
                           (fn [q :- CompRow, z :- (= (h3-cur (rk3 r) (comp-inc-epoch q)) true)]
                             (h3-cur-back (rk3 r) comp-inc-epoch comp-inc-epoch-comp-id comp-inc-epoch-h3ep q z)) (:comps w) hc))
            (have u := (h3-ob-use xm w b r (:id e) e h mb mr (Nat.eq_of_beq_eq_true ir) hx hcw hm hxx me (rfl)))
            (have sk := (And.left u))
            (simp only [h3-s Bool.and_eq_true] at sk)
            (have c1 := (And.left (And.right sk)))
            (simp only [hk Bool.not_true Bool.false_or] at c1)
            (have hk2 (= (Nat.beq (:of (rk3 r)) (:creditor e)) true)) (rw [beq-comm]) (exact c1)
            (have ha := (tbl-all-mem ActRow _ b (:acts w) h mb))
            (simp only [h3-a Bool.and_eq_true] at ha)
            (have hr := (tbl-all-mem RunRow _ r (:runs w) (And.right ha) mr))
            (simp only [h3-rr] at hr)
            (have i2 (= (Nat.beq (:id (rk3 r)) (:run b)) true)) (simp only [rk3]) (exact ir)
            (simp only [h3-r i2 Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
            (exact (False.elim (h3-cur-inc (rk3 r) (:creditor e) (:comps w) hk2 (And.left (And.right hr)) hc)))))))))

(a/theorem h3-inval-comm [w :- World, e :- EdgeRow]
  (= (invalidate w e) (edge-upd (comp-upd w (:creditor e) comp-inc-epoch) (:id e) (edge-set-phase ph-fired))) (rfl))
(a/theorem h3-invalidate [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) true) (= (h3 xm w) true) (= (h3 xm (invalidate w e)) true))
  (intros me hk h)
  (have hs := (h3-sample xm w h))
  (have h1 := (h3-comp-upd-m xm w (:creditor e) comp-inc-epoch comp-inc-epoch-comp-id comp-inc-epoch-pending comp-inc-epoch-h3ep
                comp-inc-epoch-hkm comp-inc-epoch-h3ds h))
  (have fr := (h3-free-inc xm w e (h3-rest-of xm w h) me hk))
  (have r2 := (h3r-edge-upd-free xm (comp-upd w (:creditor e) comp-inc-epoch) (:id e) (edge-set-phase ph-fired) (edge-set-phase-edge-id ph-fired)
                (h3-db-of _ (h3-sample xm _ h1)) fr (h3-rest-of xm _ h1)))
  (rw [h3-inval-comm])
  (exact (h3-intro xm (edge-upd (comp-upd w (:creditor e) comp-inc-epoch) (:id e) (edge-set-phase ph-fired)) (inv-invalidate w e hs) r2)))

;; ---- resume: the activation goes first, then its own edges (free: their creditor is no computation and
;; no remaining activation), then the run wakes
(a/theorem h3-drop-act-comm [w :- World, x :- Nat] (= (drop-act w x) (drop-cred-edges (act-del w x) x)) (rfl))
(a/theorem h3-act-mem-has [w :- World, a :- ActRow] (=> (List.Mem a (:acts w)) (= (tbl-has act-id (:id a) (:acts w)) true))
  (intro m) (have z := (mem-ids-has ActRow act-id a (:acts w) m)) (rw [nat-mem-ids] at z) (exact z))
(a/theorem h3-resume [xm :- (List Nat), w :- World, a :- ActRow]
  (=> (List.Mem a (:acts w)) (= (h3 xm w) true) (= (h3 xm (resume w a)) true))
  (intros ma h)
  (have hs := (h3-sample xm w h))
  (have hc := (act-not-comp w (:id a) hs (h3-act-mem-has w a ma)))
  (have r1 := (h3r-act-del xm w (:id a) (h3-rest-of xm w h)))
  (have hac (forall [b :- ActRow] (=> (List.Mem b (:acts (act-del w (:id a)))) (= (Nat.beq (:id b) (:id a)) false))))
  (intros b mb) (exact (h3-del-ne ActRow act-id (:id a) b (:acts w) mb))
  (have hfr (forall [e :- EdgeRow] (=> (List.Mem e (:edges (act-del w (:id a)))) (= (cred-ne (:id a) e) false)
                                      (= (h3-free xm (act-del w (:id a)) (:id e)) true))))
  (intros e me hq)
  (have ec (= (:creditor e) (:id a))) (simp only [cred-ne] at hq) (exact (Nat.eq_of_beq_eq_true (bnot-false _ hq)))
  (exact (h3-free-cred xm (act-del w (:id a)) (:id a) e r1 hc hac me ec))
  (have r2 := (h3r-drop-cred xm (act-del w (:id a)) (:id a) hc hfr (h3-db-of w hs) r1))
  (have hs2 (forall [e :- EdgeRow] (=> (List.Mem e (:edges (drop-cred-edges (act-del w (:id a)) (:id a)))) (< (:debtor e) (:next-id (drop-cred-edges (act-del w (:id a)) (:id a)))))))
  (intros e me) (exact (h3-db-of w hs e (filter-mem EdgeRow (cred-ne (:id a)) e (:edges w) me)))
  (have r3 := (h3r-run-upd xm (drop-cred-edges (act-del w (:id a)) (:id a)) (:run a) run-wake run-wake-run-id
                (fn [r :- RunRow] (Eq.refl (:of r))) (fn [r :- RunRow] (Eq.refl (:epoch r))) run-wake-h3al hs2 r2))
  (exact (h3-intro xm (resume w a) (inv-resume w a hs) r3)))

(a/theorem h3-fill-slot [xm :- (List Nat), w :- World, a :- ActRow, x :- Nat, v :- RunResult]
  (=> (List.Mem a (:acts w)) (= (h3 xm w) true) (= (h3 xm (fill-slot w a x v)) true))
  (intros ma h)
  (cases hr (act-ready (act-fill x v a)))
  (case [false]
    (simp only [fill-slot hr])
    (exact (h3-act-upd-m xm w (:id a) (act-fill x v) (act-fill-act-id x v) (fn [b :- ActRow] (Eq.refl (:run b))) (act-fill-h3sub x v) h)))
  (case [true] (simp only [fill-slot hr]) (exact (h3-resume xm w a ma h))))

;; ---- the exemption list: monotone; an id that is no computation, no debtor and a free member leaves it
(a/theorem h3-rest-xm [xm :- (List Nat), ym :- (List Nat), w :- World]
  (=> (forall [d :- Nat] (=> (= (reach-mem d xm) true) (= (reach-mem d ym) true))) (= (h3-rest xm w) true) (= (h3-rest ym w) true))
  (intros hm h)
  (simp only [h3-rest] at h) (simp only [h3-rest])
  (have ga (forall [a :- ActRow] (=> (List.Mem a (:acts w)) (= (h3-a xm w a) true) (= (h3-a ym w a) true))))
  (intros a ma ha)
  (simp only [h3-a Bool.and_eq_true] at ha) (simp only [h3-a Bool.and_eq_true])
  (apply And.intro) (exact (And.left ha))
  (have gr (forall [r :- RunRow] (=> (List.Mem r (:runs w)) (= (h3-rr xm w a r) true) (= (h3-rr ym w a r) true))))
  (intros r mr hr)
  (simp only [h3-rr h3-r Bool.or_eq_true Bool.and_eq_true] at hr) (simp only [h3-rr h3-r Bool.or_eq_true Bool.and_eq_true])
  (cases hr)
  (case [inl z] (exact (Or.inl z)))
  (case [inr z]
    (apply Or.inr)
    (apply And.intro) (exact (And.left z))
    (apply And.intro) (exact (And.left (And.right z)))
    (have ob := (And.right (And.right z)))
    (simp only [h3-ob Bool.or_eq_true Bool.and_eq_true] at ob) (simp only [h3-ob Bool.or_eq_true Bool.and_eq_true])
    (cases ob)
    (case [inl q] (exact (Or.inl (hm _ q))))
    (case [inr q]
      (apply Or.inr)
      (cases q)
      (case [inl q2] (exact (Or.inl q2)))
      (case [inr q2]
        (apply Or.inr)
        (apply And.intro) (exact (And.left q2))
        (have gx (forall [y :- Nat] (=> (List.Mem y (act-contrib a)) (= (h3-x xm w a (rk3 r) y) true) (= (h3-x ym w a (rk3 r) y) true))))
        (intros y my hx)
        (simp only [h3-x Bool.or_eq_true Bool.and_eq_true] at hx) (simp only [h3-x Bool.or_eq_true Bool.and_eq_true])
        (cases hx)
        (case [inl q3] (exact (Or.inl (hm _ q3))))
        (case [inr q3]
          (apply Or.inr)
          (apply And.intro) (exact (And.left q3))
          (have ge (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (h3-eok xm w a (rk3 r) y e) true) (= (h3-eok ym w a (rk3 r) y e) true))))
          (intros e me he)
          (simp only [h3-eok Bool.or_eq_true Bool.and_eq_true] at he) (simp only [h3-eok Bool.or_eq_true Bool.and_eq_true])
          (cases he)
          (case [inl q4] (exact (Or.inl q4)))
          (case [inr q4]
            (apply Or.inr)
            (apply And.intro) (exact (And.left q4))
            (have q5 := (And.right q4))
            (cases q5)
            (case [inl q6] (exact (Or.inl (hm _ q6))))
            (case [inr q6] (exact (Or.inr q6))))
          (exact (tbl-all-mem-mono EdgeRow _ _ (:edges w) ge (And.right q3))))
        (exact (tbl-all-mem-mono Nat _ _ (act-contrib a) gx (And.right q2))))))
  (exact (tbl-all-mem-mono RunRow _ _ (:runs w) gr (And.right ha)))
  (exact (tbl-all-mem-mono ActRow _ _ (:acts w) ga h)))

(a/theorem h3-rm-cons-ne [d :- Nat, x :- Nat, xm :- (List Nat)]
  (=> (= (reach-mem d (List.cons Nat x xm)) true) (= (Nat.beq d x) false) (= (reach-mem d xm) true))
  (intros h hn) (simp only [reach-mem-cons hn Bool.false_or] at h) (exact h))

(a/theorem h3-undo-x [xm :- (List Nat), w :- World, x :- Nat]
  (=> (= (tbl-has comp-id x (:comps w)) false)
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (Nat.beq (:debtor e) x) false)))
      (= (h3-free xm w x) true) (= (h3-rest (List.cons Nat x xm) w) true) (= (h3-rest xm w) true))
  (intros hcx hdx hfr h)
  (simp only [h3-rest] at h) (simp only [h3-rest])
  (have ga (forall [a :- ActRow] (=> (List.Mem a (:acts w)) (= (h3-a (List.cons Nat x xm) w a) true) (= (h3-a xm w a) true))))
  (intros a ma ha)
  (simp only [h3-a Bool.and_eq_true] at ha) (simp only [h3-a Bool.and_eq_true])
  (apply And.intro) (exact (And.left ha))
  (have gr (forall [r :- RunRow] (=> (List.Mem r (:runs w)) (= (h3-rr (List.cons Nat x xm) w a r) true) (= (h3-rr xm w a r) true))))
  (intros r mr hr)
  (simp only [h3-rr] at hr) (simp only [h3-rr])
  (cases hi (Nat.beq (:id (rk3 r)) (:run a)))
  (case [false] (simp only [h3-r hi Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [h3-r hi Bool.not_true Bool.false_or Bool.and_eq_true] at hr) (simp only [h3-r hi Bool.not_true Bool.false_or Bool.and_eq_true])
    (apply And.intro) (exact (And.left hr))
    (apply And.intro) (exact (And.left (And.right hr)))
    (have ob := (And.right (And.right hr)))
    (simp only [h3-ob Bool.or_eq_true Bool.and_eq_true] at ob) (simp only [h3-ob Bool.or_eq_true Bool.and_eq_true])
    (cases hxo (reach-mem (:of (rk3 r)) xm))
    (case [true] (exact (Or.inl (rfl))))
    (case [false]
      (apply Or.inr)
      (cases hcur (tbl-any (h3-cur (rk3 r)) (:comps w)))
      (case [false] (exact (Or.inl (rfl))))
      (case [true]
        (apply Or.inr)
        (have nox (= (Nat.beq (:of (rk3 r)) x) false))
        (cases hb (Nat.beq (:of (rk3 r)) x)) (rfl)
        (apply (any-elim CompRow (h3-cur (rk3 r)) _ (:comps w) hcur))
        (intros q mq hq)
        (simp only [h3-cur Bool.and_eq_true] at hq)
        (have z := (mem-ids-has CompRow comp-id q (:comps w) mq)) (rw [nat-mem-ids] at z)
        (have q2 (= (comp-id q) x)) (exact (Eq.trans (Nat.eq_of_beq_eq_true (And.left hq)) (Nat.eq_of_beq_eq_true hb)))
        (rw [q2] at z) (rw [hcx] at z) (cases z)
        (cases ob)
        (case [inl q] (rw [(h3-rm-cons-ne _ x xm q nox)] at hxo) (cases hxo))
        (case [inr q]
          (cases q)
          (case [inl q2] (rw [hcur] at q2) (cases q2))
          (case [inr q2]
            (apply And.intro) (exact (And.left q2))
            (have gx (forall [y :- Nat] (=> (List.Mem y (act-contrib a)) (= (h3-x (List.cons Nat x xm) w a (rk3 r) y) true) (= (h3-x xm w a (rk3 r) y) true))))
            (intros y my hx)
            (simp only [h3-x Bool.or_eq_true Bool.and_eq_true] at hx) (simp only [h3-x Bool.or_eq_true Bool.and_eq_true])
            (cases hyx (Nat.beq y x))
            (case [true]
              (have ey := (Nat.eq_of_beq_eq_true hyx))
              (cases hxx (reach-mem y xm))
              (case [true] (exact (Or.inl (rfl))))
              (case [false]
                (rw [ey] at hxx my)
                (have ir (= (:id r) (:run a))) (simp only [rk3] at hi) (exact (Nat.eq_of_beq_eq_true hi))
                (exact (False.elim (h3-free-use xm w x a r hfr ma mr ir hxo hcur (Iff.mpr (reach-mem-iff x (act-contrib a)) my) hxx)))))
            (case [false]
              (cases hx)
              (case [inl q3] (exact (Or.inl (h3-rm-cons-ne _ x xm q3 hyx))))
              (case [inr q3]
                (apply Or.inr)
                (apply And.intro) (exact (And.left q3))
                (have ge (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (h3-eok (List.cons Nat x xm) w a (rk3 r) y e) true) (= (h3-eok xm w a (rk3 r) y e) true))))
                (intros e me he)
                (simp only [h3-eok Bool.or_eq_true Bool.and_eq_true] at he) (simp only [h3-eok Bool.or_eq_true Bool.and_eq_true])
                (cases he)
                (case [inl q4] (exact (Or.inl q4)))
                (case [inr q4]
                  (apply Or.inr)
                  (apply And.intro) (exact (And.left q4))
                  (have q5 := (And.right q4))
                  (cases q5)
                  (case [inl q6] (exact (Or.inl (h3-rm-cons-ne _ x xm q6 (hdx e me)))))
                  (case [inr q6] (exact (Or.inr q6))))
                (exact (tbl-all-mem-mono EdgeRow _ _ (:edges w) ge (And.right q3)))))
            (exact (tbl-all-mem-mono Nat _ _ (act-contrib a) gx (And.right q2))))))))
  (exact (tbl-all-mem-mono RunRow _ _ (:runs w) gr (And.right ha)))
  (exact (tbl-all-mem-mono ActRow _ _ (:acts w) ga h)))

;; ===========================================================================
;; Part F. The bundle gives h-mem2 (with gd's rof)
;; ===========================================================================

(a/theorem h3-rm-head [x :- Nat, t :- (List Nat)] (= (reach-mem x (List.cons Nat x t)) true)
  (simp only [reach-mem-cons Nat.beq_refl Bool.true_or]))
(a/theorem h3-debtors-all [w :- World, P :- (=> Nat Bool), xs :- (List Nat)]
  (=> (forall [x :- Nat] (=> (= (reach-mem x xs) true) (= (P (edge-debtor-of w x)) true))) (= (tbl-all P (debtors-of w xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp only [debtors-of tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (have h1 := (h hd (h3-rm-head hd t)))
    (have h2 := (ih (fn [x :- Nat, m :- (= (reach-mem x t) true)] (h x (hk-rm-cons x hd t m)))))
    (simp only [debtors-of tbl-all h1 h2 Bool.and_self])))
(a/theorem h3-dep-debtors [es :- (List EdgeRow), e :- EdgeRow, c :- Nat]
  (=> (List.Mem e es) (= (Nat.beq (:kind e) ek-dep) true) (= (:creditor e) c) (= (reach-mem (:debtor e) (dep-debtors es c)) true))
  (induction es)
  (case [nil] (intros m hk hc) (cases m))
  (case [cons hd t ih]
    (intros m hk hc)
    (cases hq (Bool.and (Nat.beq (:creditor hd) c) (Nat.beq (:kind hd) ek-dep)))
    (case [false]
      (simp only [dep-debtors hq])
      (cases m)
      (case [head] (rw [hc] at hq) (simp only [Nat.beq_refl hk Bool.and_self] at hq) (cases hq))
      (case [tail m2] (exact (ih m2 hk hc))))
    (case [true]
      (simp only [dep-debtors hq reach-mem-cons Bool.or_eq_true])
      (cases m)
      (case [head] (exact (Or.inl (Nat.beq_refl _))))
      (case [tail m2] (exact (Or.inr (ih m2 hk hc)))))))

(a/theorem h3-ral-id [rid :- Nat, q :- RunRow] (=> (= (h3-ral rid q) true) (= (Nat.beq (run-id q) rid) true))
  (intro h) (simp only [h3-ral Bool.and_eq_true] at h) (exact (And.left h)))

;; the debtor of a member edge of a current activation of c (run r = C.run at C's epoch)
(a/theorem h3-mem-y [w :- World, c :- CompRow, a :- ActRow, r :- RunRow, x :- Nat]
  (=> (= (h3 (List.nil Nat) w) true) (List.Mem c (:comps w)) (List.Mem a (:acts w)) (List.Mem r (:runs w))
      (= (:id r) (:run a)) (= (:of r) (:id c)) (= (:epoch r) (:epoch c)) (= (reach-mem x (act-contrib a)) true)
      (= (mem-y-ok2 w (:id c) (edge-debtor-of w x)) true))
  (intros h mc ma mr ei eo ee mx)
  (have hs := (h3-sample _ w h))
  (have ha := (tbl-all-mem ActRow _ a (:acts w) (h3-rest-of _ w h) ma))
  (simp only [h3-a Bool.and_eq_true] at ha)
  (have hr := (tbl-all-mem RunRow _ r (:runs w) (And.right ha) mr))
  (simp only [h3-rr] at hr)
  (have i2 (= (Nat.beq (:id (rk3 r)) (:run a)) true)) (simp only [rk3 ei Nat.beq_refl])
  (simp only [h3-r i2 Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
  (have ob := (And.right (And.right hr)))
  (have hcur (= (tbl-any (h3-cur (rk3 r)) (:comps w)) true))
  (apply (any-elim-of CompRow (h3-cur (rk3 r)) c (:comps w) mc))
  (simp only [h3-cur rk3 eo ee Nat.beq_refl Bool.true_and]) (exact (gd-ble-of _ _ (Nat.le_refl _)))
  (simp only [h3-ob hcur reach-mem Bool.not_true Bool.false_or Bool.and_eq_true] at ob)
  (have hx := (tbl-all-mem Nat _ x (act-contrib a) (And.right ob) (Iff.mp (reach-mem-iff x (act-contrib a)) mx)))
  (simp only [h3-x reach-mem Bool.false_or Bool.and_eq_true] at hx)
  (cases hf (edge-find w x))
  (case [none] (have z := (tbl-find-none-has EdgeRow edge-id x (:edges w) hf)) (rw [(And.left hx)] at z) (cases z))
  (case [some e]
    (have me := (tbl-find-mem EdgeRow edge-id x e (:edges w) hf))
    (have ie := (tbl-find-id EdgeRow edge-id x e (:edges w) hf))
    (have ie3 (= (:id e) x)) (exact ie)
    (have ie2 (= (Nat.beq (:id e) x) true)) (rw [ie3]) (exact (Nat.beq_refl x))
    (have ek := (tbl-all-mem EdgeRow _ e (:edges w) (And.right hx) me))
    (simp only [h3-eok ie2 reach-mem Bool.not_true Bool.false_or Bool.and_eq_true] at ek)
    (have sk := (And.left ek)) (simp only [h3-s Bool.and_eq_true] at sk)
    (have mk := (And.right ek)) (simp only [h3-m Bool.and_eq_true] at mk)
    (simp only [edge-debtor-of hf])
    (have ho := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                  (And.left (And.right (inv-parts w hs))) me))
    (simp only [edge-ok deb-ok Bool.and_eq_true Bool.or_eq_true] at ho)
    (have hdo := (And.right ho))
    (cases hdo)
    (case [inl hc1]
      (have q := (And.right mk))
      (simp only [hc1 Bool.not_true Bool.false_or Bool.and_eq_true] at q)
      (have cr := (And.left (And.right sk)))
      (simp only [(And.left q) Bool.not_true Bool.false_or] at cr)
      (have cr2 (= (:creditor e) (:id c))) (exact (Eq.trans (Nat.eq_of_beq_eq_true cr) eo))
      (have dd := (h3-dep-debtors (:edges w) e (:id c) me (And.left q) cr2))
      (have wt (= (waiting-at w (:debtor e)) true))
      (cases hd (comp-find w (:debtor e)))
      (case [none] (have z := (tbl-find-none-has CompRow comp-id (:debtor e) (:comps w) hd)) (rw [hc1] at z) (cases z))
      (case [some d]
        (have md := (tbl-find-mem CompRow comp-id (:debtor e) d (:comps w) hd))
        (have id := (tbl-find-id CompRow comp-id (:debtor e) d (:comps w) hd))
        (have wf := (tbl-all-mem CompRow _ d (:comps w) (And.right q) md))
        (have id3 (= (:id d) (:debtor e))) (exact id)
        (have id2 (= (Nat.beq (:id d) (:debtor e)) true)) (rw [id3]) (exact (Nat.beq_refl _))
        (simp only [hk-wif id2 Bool.not_true Bool.false_or] at wf)
        (simp only [waiting-at hd]) (exact (hk-wt-waiting d wf)))
      (simp only [mem-y-ok2 wt dd Bool.and_self Bool.or_true]))
    (case [inr h2]
      (cases h2)
      (case [inl ht]
        (have tk := (And.left mk))
        (have al (= (task-alive-at w (:debtor e)) true))
        (cases hft (task-find w (:debtor e)))
        (case [none] (have z := (tbl-find-none-has TaskRow task-id (:debtor e) (:tasks w) hft)) (rw [ht] at z) (cases z))
        (case [some t]
          (have mt := (tbl-find-mem TaskRow task-id (:debtor e) t (:tasks w) hft))
          (have it := (tbl-find-id TaskRow task-id (:debtor e) t (:tasks w) hft))
          (have it3 (= (:id t) (:debtor e))) (exact it)
          (have it2 (= (Nat.beq (:id t) (:debtor e)) true)) (rw [it3]) (exact (Nat.beq_refl _))
          (have tq := (tbl-all-mem TaskRow _ t (:tasks w) tk mt))
          (simp only [h3-tk it2 Bool.not_true Bool.false_or] at tq)
          (apply (any-elim RunRow (h3-ral (:run t)) _ (:runs w) tq))
          (intros r2 m2 q2)
          (simp only [h3-ral Bool.and_eq_true] at q2)
          (have u := (uniq-all RunRow run-id run-alive r2 (:runs w) (lit-runs-nodup w hs) m2 (And.right q2)))
          (cases hr3 (run-find w (:run t)))
          (case [none] (have z := (tbl-find-none-has RunRow run-id (:run t) (:runs w) hr3))
            (have z2 := (any-has-id RunRow run-id (h3-ral (:run t)) (:run t) (fn [q :- RunRow, hq :- (= (h3-ral (:run t) q) true)] (h3-ral-id (:run t) q hq)) (:runs w) tq))
            (rw [nat-mem-ids] at z2) (rw [z2] at z) (cases z))
          (case [some r3]
            (have m3 := (tbl-find-mem RunRow run-id (:run t) r3 (:runs w) hr3))
            (have i3 := (tbl-find-id RunRow run-id (:run t) r3 (:runs w) hr3))
            (have u3 := (tbl-all-mem RunRow _ r3 (:runs w) u m3))
            (have i4 (= (Nat.beq (run-id r3) (run-id r2)) true))
            (have i5 (= (:id r3) (:run t))) (exact i3) (have i6 (= (:id r2) (:run t))) (exact (Nat.eq_of_beq_eq_true (And.left q2)))
            (simp only [run-id i5 i6 Nat.beq_refl])
            (simp only [same-id-then i4 Bool.not_true Bool.false_or] at u3)
            (simp only [task-alive-at hft hr3 opt-test u3])))
        (simp only [mem-y-ok2 task-has ht al Bool.and_self Bool.true_or Bool.or_true]))
      (case [inr h4]
        (have lf (= (blk-leaf w (:debtor e)) true))
        (cases h4)
        (case [inl hsrc] (simp only [blk-leaf source-has hsrc Bool.true_or]))
        (case [inr hres] (simp only [blk-leaf resource-has (And.right hres) Bool.or_true]))
        (simp only [mem-y-ok2 lf Bool.true_or])))))


;; h-mem2 from the bundle with no exemption and gd's rof (C.run names a run of C)
(a/theorem h3-h-mem2 [w :- World] (=> (= (h3 (List.nil Nat) w) true) (= (gd w) true) (= (h-mem2 w) true))
  (intros h hg)
  (have hs := (h3-sample _ w h))
  (have p := (gdk-parts _ _ _ (gd-rest-of w hg)))
  (have qa := (And.right p)) (rw [all-gdkeys] at qa)
  (simp only [h-mem2])
  (apply all-of-mem)
  (intros c mc)
  (simp only [mem-ok2 Bool.or_eq_true])
  (cases hb (blk-base w (:id c)))
  (case [false] (exact (Or.inl (rfl))))
  (case [true]
    (apply Or.inr)
    (cases hf (comp-find w (:id c)))
    (case [none]
      (have z := (tbl-find-none-has CompRow comp-id (:id c) (:comps w) hf))
      (have z2 := (mem-ids-has CompRow comp-id c (:comps w) mc))
      (rw [nat-mem-ids] at z2) (rw [z2] at z) (cases z))
    (case [some c2]
      (simp only [blk-base hf run-parked-of] at hb)
      (have mc2 := (tbl-find-mem CompRow comp-id (:id c) c2 (:comps w) hf))
      (have ic2 (= (:id c2) (:id c))) (exact (tbl-find-id CompRow comp-id (:id c) c2 (:comps w) hf))
      (cases hr (run-find w (:run c2)))
      (case [none] (simp only [hr] at hb) (cases hb))
      (case [some r]
        (simp only [hr Bool.and_eq_true] at hb)
        (have mr := (tbl-find-mem RunRow run-id (:run c2) r (:runs w) hr))
        (have ir (= (:id r) (:run c2))) (exact (tbl-find-id RunRow run-id (:run c2) r (:runs w) hr))
        (have ee (= (:epoch r) (:epoch c2))) (exact (Nat.eq_of_beq_eq_true (And.right hb)))
        (have pc := (gd-c-parts _ _ _ (tbl-all-mem CompRow (fn [x :- CompRow] (gd-c (:runs w) (:next-id w) (gdkey x))) c2 (:comps w) qa mc2)))
        (have rof := (tbl-all-mem RunRow _ r (:runs w) (And.left (And.right (And.right pc))) mr))
        (have ir2 (= (Nat.beq (:id r) (:run c2)) true)) (rw [ir]) (exact (Nat.beq_refl _))
        (simp only [gd-rof gdkey ir2 Bool.not_true Bool.false_or] at rof)
        (have eo (= (:of r) (:id c2))) (exact (Nat.eq_of_beq_eq_true rof))
        (simp only [blk-deps ent-run hf])
        (apply h3-debtors-all)
        (intros x hx)
        (have g (forall [a :- ActRow, z :- Nat] (=> (List.Mem a (:acts w)) (= (act-of-run (:run c2) a) true) (= (reach-mem z (act-contrib a)) true)
                                                   (= (mem-y-ok2 w (:id c) (edge-debtor-of w z)) true))))
        (intros a z ma pa hz)
        (have ia (= (:id r) (:run a))) (simp only [act-of-run] at pa) (exact (Eq.trans ir (Eq.symm (Nat.eq_of_beq_eq_true pa))))
        (rw [← ic2])
        (exact (h3-mem-y w c2 a r z h mc2 ma mr ia eo ee hz))
        (exact (gather-prop ActRow (act-of-run (:run c2)) act-contrib (fn [z :- Nat] (= (mem-y-ok2 w (:id c) (edge-debtor-of w z)) true)) (:acts w) g x hx))))))

;; L5 (safety half) from p3c, h-mark, h3 [] and gd
(a/theorem h3-l5-safety [w :- World, c0 :- Nat, c :- CompRow]
  (=> (= (p3c w) true) (= (gd w) true) (= (h3 (List.nil Nat) w) true) (= (quiescent w) true) (= (h-mark w) true)
      (= (comp-find w c0) (Option.some CompRow c)) (= (comp-waiting c) true)
      (none-blocked w c0) (none-eligible w c0) (tasks-blocked w c0) False)
  (intros h hg hm hq hk hf hw n1 n2 n3)
  (exact (l5-safety-inv w c0 c h hq hk (h3-h-mem2 w hm hg) hf hw n1 n2 n3)))
