(ns spindel.v2.inv.marks
  "h-mark through `world-step` (P11), kernel-checked (Init only). Bundle `marks-waiting hxm`: every marked
  edge is a dep edge whose debtor is a computation row that is waiting in the strong form `waiting-strongly`
  (not idle, and done-epoch < epoch or pending /= 0), or is in the exemption list hxm. The strict
  `<` makes every epoch step a frame (no dle needed); with gd's dle it is the same as waiting.
  Marked edges' debtors are waiting (h-mark) when hxm = [] (`hk-h-mark`). Every well-formed lemma is
  restated for marks-waiting by the generic tree (Part C's table); hmk's own proofs are the table's :over."
  (:require [ansatz.core :as a]
            [spindel.v2.pres.tree :as tree]
            [spindel.v2.pres.exempt :as exempt]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.inv.rank :refer :all]
            [spindel.v2.inv.rank-step :refer :all]
            [spindel.v2.progress.casc :refer :all]
            [spindel.v2.inv.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.pres.part :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.idle :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.i10 :refer :all]
            [spindel.v2.inv.i11 :refer :all]
            [spindel.v2.inv.i1-scopes :refer :all]
            [spindel.v2.inv.i8 :refer :all]
            [spindel.v2.inv.comp-facts :refer :all]
            [spindel.v2.progress.measures :refer :all]
            [spindel.v2.progress.l5 :refer :all]))

;; ===========================================================================
;; Part A. The predicate and its transfer lemmas
;; ===========================================================================

;; strong waiting: not idle, and its result is stale (done-epoch < epoch) or a debtor is dirty
(a/defn waiting-strongly [c :- CompRow] Bool
  (Bool.and (Bool.not (:idle c)) (Bool.or (Nat.blt (:done-epoch c) (:epoch c)) (Bool.not (Nat.beq (:pending c) 0)))))
;; every row with id d is waiting
(a/defn hk-wif [d :- Nat, c :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id c) d)) (waiting-strongly c)))
;; a pending change keeps the rows with id d waiting: idle, or done-epoch < epoch
(a/defn hk-strong [c :- CompRow] Bool (Bool.or (:idle c) (Nat.blt (:done-epoch c) (:epoch c))))
(a/defn hk-sif [d :- Nat, c :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id c) d)) (hk-strong c)))
(a/defn hk-safe [hxm :- (List Nat), cs :- (List CompRow), d :- Nat] Bool (Bool.or (reach-mem d hxm) (tbl-all (hk-sif d) cs)))
(a/defn hk-e [hxm :- (List Nat), cs :- (List CompRow), e :- EdgeRow] Bool
  (Bool.or (Bool.not (:marked e))
    (Bool.and (Nat.beq (:kind e) ek-dep)
      (Bool.and (tbl-has comp-id (:debtor e) cs)
        (Bool.or (reach-mem (:debtor e) hxm) (tbl-all (hk-wif (:debtor e)) cs))))))
(a/defn marks-waiting-rest [hxm :- (List Nat), w :- World] Bool (tbl-all (hk-e hxm (:comps w)) (:edges w)))
(a/defn marks-waiting [hxm :- (List Nat), w :- World] Bool (Bool.and (well-formed w) (marks-waiting-rest hxm w)))

(a/theorem marks-waiting-well-formed [hxm :- (List Nat), w :- World] (=> (= (marks-waiting hxm w) true) (= (well-formed w) true))
  (intro h) (simp only [marks-waiting Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem marks-waiting-rest-of [hxm :- (List Nat), w :- World] (=> (= (marks-waiting hxm w) true) (= (marks-waiting-rest hxm w) true))
  (intro h) (simp only [marks-waiting Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem marks-waiting-intro [hxm :- (List Nat), w :- World] (=> (= (well-formed w) true) (= (marks-waiting-rest hxm w) true) (= (marks-waiting hxm w) true))
  (intros h1 h2) (simp only [marks-waiting h1 h2 Bool.and_self]))
(a/theorem marks-waiting-parts [hxm :- (List Nat), w :- World]
  (=> (= (marks-waiting hxm w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (marks-waiting-well-formed hxm w h))))

;; the per-edge fact, unfolded
(a/theorem hk-e-marked [hxm :- (List Nat), cs :- (List CompRow), e :- EdgeRow]
  (=> (= (hk-e hxm cs e) true) (= (:marked e) true)
      (And (= (Nat.beq (:kind e) ek-dep) true)
           (And (= (tbl-has comp-id (:debtor e) cs) true)
                (Or (= (reach-mem (:debtor e) hxm) true) (= (tbl-all (hk-wif (:debtor e)) cs) true)))))
  (intros h hm)
  (simp only [hk-e hm Bool.not_true Bool.false_or Bool.and_eq_true Bool.or_eq_true] at h)
  (exact h))
(a/theorem hk-e-unm [hxm :- (List Nat), cs :- (List CompRow), e :- EdgeRow]
  (=> (= (:marked e) false) (= (hk-e hxm cs e) true))
  (intro hm) (simp only [hk-e hm Bool.not_false Bool.true_or]))
(a/theorem hk-e-intro [hxm :- (List Nat), cs :- (List CompRow), e :- EdgeRow]
  (=> (= (Nat.beq (:kind e) ek-dep) true) (= (tbl-has comp-id (:debtor e) cs) true)
      (Or (= (reach-mem (:debtor e) hxm) true) (= (tbl-all (hk-wif (:debtor e)) cs) true))
      (= (hk-e hxm cs e) true))
  (intros h1 h2 h3)
  (cases h3)
  (case [inl q] (simp only [hk-e h1 h2 q Bool.true_or Bool.or_true Bool.and_self]))
  (case [inr q] (simp only [hk-e h1 h2 q Bool.or_true Bool.and_self])))

;; a change of the computation rows that keeps every id and every row's waiting
(a/theorem hk-e-cs [hxm :- (List Nat), cs :- (List CompRow), cs2 :- (List CompRow), e :- EdgeRow]
  (=> (forall [d :- Nat] (=> (= (tbl-has comp-id d cs) true) (= (tbl-has comp-id d cs2) true)))
      (forall [d :- Nat] (=> (= (reach-mem d hxm) false) (= (tbl-all (hk-wif d) cs) true) (= (tbl-all (hk-wif d) cs2) true)))
      (= (hk-e hxm cs e) true) (= (hk-e hxm cs2 e) true))
  (intros hh hw he)
  (cases hm (:marked e))
  (case [false] (exact (hk-e-unm hxm cs2 e hm)))
  (case [true]
    (have p := (hk-e-marked hxm cs e he hm))
    (apply (hk-e-intro hxm cs2 e (And.left p) (hh (:debtor e) (And.left (And.right p)))))
    (cases hx (reach-mem (:debtor e) hxm))
    (case [true] (exact (Or.inl (rfl))))
    (case [false]
      (have q := (And.right (And.right p)))
      (cases q)
      (case [inl z] (rw [hx] at z) (cases z))
      (case [inr z] (exact (Or.inr (hw (:debtor e) hx z)))))))
(a/theorem hk-all-cs [hxm :- (List Nat), cs :- (List CompRow), cs2 :- (List CompRow), es :- (List EdgeRow)]
  (=> (forall [d :- Nat] (=> (= (tbl-has comp-id d cs) true) (= (tbl-has comp-id d cs2) true)))
      (forall [d :- Nat] (=> (= (reach-mem d hxm) false) (= (tbl-all (hk-wif d) cs) true) (= (tbl-all (hk-wif d) cs2) true)))
      (= (tbl-all (hk-e hxm cs) es) true) (= (tbl-all (hk-e hxm cs2) es) true))
  (intros hh hw h)
  (exact (tbl-all-mono EdgeRow (hk-e hxm cs) (hk-e hxm cs2)
           (fn [e :- EdgeRow, he :- (= (hk-e hxm cs e) true)] (hk-e-cs hxm cs cs2 e hh hw he)) es h)))

;; the exemption list only matters through membership
(a/theorem hk-e-xm [hxm :- (List Nat), hym :- (List Nat), cs :- (List CompRow), e :- EdgeRow]
  (=> (forall [d :- Nat] (=> (= (reach-mem d hxm) true) (= (reach-mem d hym) true)))
      (= (hk-e hxm cs e) true) (= (hk-e hym cs e) true))
  (intros hs he)
  (cases hm (:marked e))
  (case [false] (exact (hk-e-unm hym cs e hm)))
  (case [true]
    (have p := (hk-e-marked hxm cs e he hm))
    (apply (hk-e-intro hym cs e (And.left p) (And.left (And.right p))))
    (have q := (And.right (And.right p)))
    (cases q)
    (case [inl z] (exact (Or.inl (hs (:debtor e) z))))
    (case [inr z] (exact (Or.inr z)))))
(a/theorem marks-waiting-rest-xm [hxm :- (List Nat), hym :- (List Nat), w :- World]
  (=> (forall [d :- Nat] (=> (= (reach-mem d hxm) true) (= (reach-mem d hym) true)))
      (= (marks-waiting-rest hxm w) true) (= (marks-waiting-rest hym w) true))
  (intros hs h)
  (exact (tbl-all-mono EdgeRow (hk-e hxm (:comps w)) (hk-e hym (:comps w))
           (fn [e :- EdgeRow, he :- (= (hk-e hxm (:comps w) e) true)] (hk-e-xm hxm hym (:comps w) e hs he)) (:edges w) h)))
(a/theorem marks-waiting-rest-nil [hxm :- (List Nat), w :- World] (=> (= (marks-waiting-rest (List.nil Nat) w) true) (= (marks-waiting-rest hxm w) true))
  (intro h)
  (apply (marks-waiting-rest-xm (List.nil Nat) hxm w _ h))
  (intros d hd) (simp [reach-mem] at hd))

;; ---- generic list helpers
(a/theorem hk-all-upd-mem [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), P :- (=> A Bool), Q :- (=> A Bool), xs :- (List A)]
  (=> (forall [r :- A] (=> (List.Mem r xs) (= (P r) true) (= (Nat.beq (idf r) x) true) (= (Q (f r)) true)))
      (forall [r :- A] (=> (List.Mem r xs) (= (P r) true) (= (Nat.beq (idf r) x) false) (= (Q r) true)))
      (= (tbl-all P xs) true) (= (tbl-all Q (tbl-upd idf x f xs)) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intros hin hout hp) (simp [tbl-all tbl-upd])
  (intros hin hout hp)
  (simp only [tbl-all Bool.and_eq_true] at hp)
  (have r2 := (ih (fn [r :- A, m :- (List.Mem r t)] (hin r (List.Mem.tail h m)))
                  (fn [r :- A, m :- (List.Mem r t)] (hout r (List.Mem.tail h m))) (And.right hp)))
  (cases hx (Nat.beq (idf h) x))
  (simp only [tbl-upd hx tbl-all r2 (hout h (List.Mem.head t) (And.left hp) hx) Bool.and_self])
  (simp only [tbl-upd hx tbl-all r2 (hin h (List.Mem.head t) (And.left hp) hx) Bool.and_self]))

;; ---- computation rows

(a/theorem hk-wif-upd [d :- Nat, x :- Nat, f :- (=> CompRow CompRow),
                       hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                       hm :- (forall [c :- CompRow] (=> (= (waiting-strongly c) true) (= (waiting-strongly (f c)) true))), cs :- (List CompRow)]
  (=> (= (tbl-all (hk-wif d) cs) true) (= (tbl-all (hk-wif d) (tbl-upd comp-id x f cs)) true))
  (intro h)
  (apply (tbl-all-upd CompRow comp-id x f (hk-wif d) (hk-wif d) _ _ cs h))
  (intros r hr hx)
  (have e (= (:id (f r)) (:id r))) (exact (hid r))
  (cases hd (Nat.beq (:id r) d))
  (simp only [hk-wif e hd Bool.not_false Bool.true_or])
  (simp only [hk-wif hd Bool.not_true Bool.false_or] at hr)
  (simp only [hk-wif e hd Bool.not_true Bool.false_or])
  (exact (hm r hr))
  (intros r hr hx) (exact hr))

(a/theorem marks-waiting-comp-upd-m [hxm :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                           hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                           hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                           hm :- (forall [c :- CompRow] (=> (= (waiting-strongly c) true) (= (waiting-strongly (f c)) true)))]
  (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (comp-upd w x f)) true))
  (intro h)
  (have r0 := (marks-waiting-rest-of hxm w h))
  (have r (= (marks-waiting-rest hxm (comp-upd w x f)) true))
  (simp only [marks-waiting-rest comp-upd set-comps]) (simp only [marks-waiting-rest] at r0)
  (apply (hk-all-cs hxm (:comps w) (tbl-upd comp-id x f (:comps w)) (:edges w) _ _ r0))
  (intros d hd) (rw [(tbl-has-upd CompRow comp-id x d f hid (:comps w))]) (exact hd)
  (intros d hx hd) (exact (hk-wif-upd d x f hid hm (:comps w) hd))
  (exact (marks-waiting-intro hxm _ (well-formed-comp-upd w x f hid hp (marks-waiting-well-formed hxm w h)) r)))

;; a pending change on the rows with id x: rows waiting with id d stay waiting when d /= x or
;; the rows with id x are strong (idle or done-epoch < epoch)
(a/theorem hk-wif-pend-ne [d :- Nat, x :- Nat, f :- (=> CompRow CompRow),
                           hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))), cs :- (List CompRow)]
  (=> (= (Nat.beq x d) false) (= (tbl-all (hk-wif d) cs) true) (= (tbl-all (hk-wif d) (tbl-upd comp-id x f cs)) true))
  (intros q h)
  (apply (tbl-all-upd CompRow comp-id x f (hk-wif d) (hk-wif d) _ _ cs h))
  (intros r hr hx)
  (have e (= (:id (f r)) (:id r))) (exact (hid r))
  (have e1 := (Nat.eq_of_beq_eq_true hx))
  (have e2 (= (Nat.beq (:id (f r)) d) false)) (rw [e]) (rw [(Eq.trans (Eq.refl (:id r)) e1)]) (exact q)
  (simp only [hk-wif e2 Bool.not_false Bool.true_or])
  (intros r hr hx) (exact hr))
(a/theorem hk-wif-pend-s [d :- Nat, x :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hi :- (forall [c :- CompRow] (= (:idle (f c)) (:idle c))),
                          he :- (forall [c :- CompRow] (= (:epoch (f c)) (:epoch c))),
                          hd :- (forall [c :- CompRow] (= (:done-epoch (f c)) (:done-epoch c))), cs :- (List CompRow)]
  (=> (= (tbl-all (hk-sif x) cs) true) (= (tbl-all (hk-wif d) cs) true) (= (tbl-all (hk-wif d) (tbl-upd comp-id x f cs)) true))
  (intros q h)
  (have hb := (tbl-all-mono2 CompRow (hk-wif d) (hk-sif x) (both (hk-wif d) (hk-sif x)) (both-of CompRow (hk-wif d) (hk-sif x)) cs h q))
  (apply (tbl-all-upd CompRow comp-id x f (both (hk-wif d) (hk-sif x)) (hk-wif d) _ _ cs hb))
  (intros r hr hx)
  (simp only [both Bool.and_eq_true] at hr)
  (have e (= (:id (f r)) (:id r))) (exact (hid r))
  (have hx2 (= (Nat.beq (:id r) x) true)) (exact hx)
  (have s := (And.right hr))
  (simp only [hk-sif hx2 Bool.not_true Bool.false_or hk-strong Bool.or_eq_true] at s)
  (cases hdd (Nat.beq (:id r) d))
  (simp only [hk-wif e hdd Bool.not_false Bool.true_or])
  (have w1 := (And.left hr))
  (simp only [hk-wif hdd Bool.not_true Bool.false_or waiting-strongly Bool.and_eq_true] at w1)
  (simp only [hk-wif e hdd Bool.not_true Bool.false_or waiting-strongly (hi r) (he r) (hd r)])
  (cases s)
  (rename_i si) (rw [si] at w1) (simp at w1)
  (rename_i si) (simp only [si Bool.true_or Bool.and_true]) (exact (And.left w1))
  (intros r hr hx)
  (simp only [both Bool.and_eq_true] at hr) (exact (And.left hr)))
(a/theorem hk-wif-pend [d :- Nat, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hi :- (forall [c :- CompRow] (= (:idle (f c)) (:idle c))),
                        he :- (forall [c :- CompRow] (= (:epoch (f c)) (:epoch c))),
                        hd :- (forall [c :- CompRow] (= (:done-epoch (f c)) (:done-epoch c))), cs :- (List CompRow)]
  (=> (Or (= (Nat.beq x d) false) (= (tbl-all (hk-sif x) cs) true))
      (= (tbl-all (hk-wif d) cs) true) (= (tbl-all (hk-wif d) (tbl-upd comp-id x f cs)) true))
  (intros hs h)
  (cases hs)
  (rename_i q) (exact (hk-wif-pend-ne d x f hid cs q h))
  (rename_i q) (exact (hk-wif-pend-s d x f hid hi he hd cs q h)))

;; ---- edge primitives (rest parts)

(a/theorem hkr-edge-upd [hxm :- (List Nat), w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                         hk2 :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                         hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                         hm2 :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e)))]
  (=> (= (marks-waiting-rest hxm w) true) (= (marks-waiting-rest hxm (edge-upd w x f)) true))
  (intro h)
  (simp only [marks-waiting-rest edge-upd set-edges]) (simp only [marks-waiting-rest] at h)
  (apply (tbl-all-upd EdgeRow edge-id x f (hk-e hxm (:comps w)) (hk-e hxm (:comps w)) _ _ (:edges w) h))
  (intros e he hx) (simp only [hk-e (hk2 e) (hd e) (hm2 e)]) (simp only [hk-e] at he) (exact he)
  (intros e he hx) (exact he))

;; the edge with id x, once marked, satisfies the fact
(a/defn hk-mok [hxm :- (List Nat), cs :- (List CompRow), x :- Nat, e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:id e) x)) (hk-e hxm cs (edge-set-marked true e))))

(a/theorem waiting-strongly-inc [c :- CompRow] (=> (= (waiting-strongly c) true) (= (waiting-strongly (comp-inc-pending c)) true))
  (intro h) (simp only [waiting-strongly Bool.and_eq_true] at h)
  (simp only [waiting-strongly comp-inc-pending comp-set-pending (And.left h) Bool.true_and])
  (have z (= (Nat.beq (+ (:pending c) 1) 0) false))
  (cases hb (Nat.beq (+ (:pending c) 1) 0)) (rfl) (have e := (Nat.eq_of_beq_eq_true hb)) (omega)
  (simp only [z Bool.not_false Bool.or_true]))

(a/theorem hkr-mark-edge [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (= (tbl-all (hk-mok hxm (:comps w) x) (:edges w)) true) (= (marks-waiting-rest hxm w) true) (= (marks-waiting-rest hxm (mark-edge w x)) true))
  (intros hk0 h)
  (simp only [marks-waiting-rest] at h)
  (have hb := (tbl-all-mono2 EdgeRow (hk-mok hxm (:comps w) x) (hk-e hxm (:comps w)) (both (hk-mok hxm (:comps w) x) (hk-e hxm (:comps w)))
                (both-of EdgeRow (hk-mok hxm (:comps w) x) (hk-e hxm (:comps w))) (:edges w) hk0 h))
  (have h1 (= (tbl-all (hk-e hxm (:comps w)) (tbl-upd edge-id x (edge-set-marked true) (:edges w))) true))
  (apply (tbl-all-upd EdgeRow edge-id x (edge-set-marked true) (both (hk-mok hxm (:comps w) x) (hk-e hxm (:comps w))) (hk-e hxm (:comps w)) _ _ (:edges w) hb))
  (intros r hr hx)
  (simp only [both Bool.and_eq_true] at hr)
  (have z := (And.left hr)) (have hx2 (= (Nat.beq (:id r) x) true)) (exact hx)
  (simp only [hk-mok hx2 Bool.not_true Bool.false_or] at z) (exact z)
  (intros r hr hx) (simp only [both Bool.and_eq_true] at hr) (exact (And.right hr))
  (cases hf (edge-find w x))
  (simp only [mark-edge hf marks-waiting-rest]) (exact h)
  (rename_i e)
  (cases hm (:marked e))
  (simp only [mark-edge hf hm marks-waiting-rest comp-upd edge-upd set-comps set-edges])
  (exact (hk-all-cs hxm (:comps w) (tbl-upd comp-id (:creditor e) comp-inc-pending (:comps w)) _
           (fn [d :- Nat, hd :- (= (tbl-has comp-id d (:comps w)) true)]
             (Eq.trans (tbl-has-upd CompRow comp-id (:creditor e) d comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) (:comps w)) hd))
           (fn [d :- Nat, hx :- (= (reach-mem d hxm) false), hd :- (= (tbl-all (hk-wif d) (:comps w)) true)]
             (hk-wif-upd d (:creditor e) comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) waiting-strongly-inc (:comps w) hd))
           h1))
  (simp only [mark-edge hf hm marks-waiting-rest]) (exact h))

;; a change of the pending of the rows with id c, when c is safe
(a/theorem hk-cs-pend [hxm :- (List Nat), cs :- (List CompRow), c :- Nat, f :- (=> CompRow CompRow),
                       hid :- (forall [q :- CompRow] (= (comp-id (f q)) (comp-id q))),
                       hi :- (forall [q :- CompRow] (= (:idle (f q)) (:idle q))),
                       he :- (forall [q :- CompRow] (= (:epoch (f q)) (:epoch q))),
                       hdn :- (forall [q :- CompRow] (= (:done-epoch (f q)) (:done-epoch q))), es :- (List EdgeRow)]
  (=> (= (hk-safe hxm cs c) true) (= (tbl-all (hk-e hxm cs) es) true) (= (tbl-all (hk-e hxm (tbl-upd comp-id c f cs)) es) true))
  (intros hs h)
  (apply (hk-all-cs hxm cs (tbl-upd comp-id c f cs) es _ _ h))
  (intros d hd) (exact (Eq.trans (tbl-has-upd CompRow comp-id c d f hid cs) hd))
  (intros d hx hd)
  (cases hcd (Nat.beq c d))
  (exact (hk-wif-pend d c f hid hi he hdn cs (Or.inl hcd) hd))
  (have e1 := (Nat.eq_of_beq_eq_true hcd))
  (simp only [hk-safe Bool.or_eq_true] at hs)
  (cases hs)
  (rename_i z) (rw [e1] at z) (rw [hx] at z) (cases z)
  (rename_i z) (exact (hk-wif-pend d c f hid hi he hdn cs (Or.inr z) hd)))

(a/theorem hk-dec-id [q :- CompRow] (= (comp-id (comp-dec-pending q)) (comp-id q)) (rfl))
(a/theorem hk-dec-idle [q :- CompRow] (= (:idle (comp-dec-pending q)) (:idle q)) (rfl))
(a/theorem hk-dec-ep [q :- CompRow] (= (:epoch (comp-dec-pending q)) (:epoch q)) (rfl))
(a/theorem hk-dec-done [q :- CompRow] (= (:done-epoch (comp-dec-pending q)) (:done-epoch q)) (rfl))

(a/theorem hkr-unmark-edge [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true) (= (hk-safe hxm (:comps w) (:creditor e)) true))) (= (marks-waiting-rest hxm w) true) (= (marks-waiting-rest hxm (unmark-edge w x)) true))
  (intros hu h)
  (simp only [marks-waiting-rest] at h)
  (cases hf (edge-find w x))
  (simp only [unmark-edge hf marks-waiting-rest]) (exact h)
  (rename_i e)
  (cases hm (:marked e))
  (simp only [unmark-edge hf hm marks-waiting-rest]) (exact h)
  (have s := (hu e hf hm))
  (have h1 (= (tbl-all (hk-e hxm (:comps w)) (tbl-upd edge-id x (edge-set-marked false) (:edges w))) true))
  (apply (tbl-all-upd EdgeRow edge-id x (edge-set-marked false) (hk-e hxm (:comps w)) (hk-e hxm (:comps w)) _ _ (:edges w) h))
  (intros r hr hx) (exact (hk-e-unm hxm (:comps w) (edge-set-marked false r) (rfl)))
  (intros r hr hx) (exact hr)
  (simp only [unmark-edge hf hm marks-waiting-rest comp-upd edge-upd set-comps set-edges])
  (exact (hk-cs-pend hxm (:comps w) (:creditor e) comp-dec-pending hk-dec-id hk-dec-idle hk-dec-ep hk-dec-done _ s h1)))

(a/theorem hkr-remove-edge [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true) (= (hk-safe hxm (:comps w) (:creditor e)) true))) (= (marks-waiting-rest hxm w) true) (= (marks-waiting-rest hxm (remove-edge w x)) true))
  (intros hu h)
  (simp only [marks-waiting-rest] at h)
  (have h1 (= (tbl-all (hk-e hxm (:comps w)) (tbl-del edge-id x (:edges w))) true))
  (exact (tbl-all-del EdgeRow edge-id x (hk-e hxm (:comps w)) (hk-e hxm (:comps w))
           (fn [r :- EdgeRow, hr :- (= (hk-e hxm (:comps w) r) true), hx :- (= (Nat.beq (edge-id r) x) false)] hr) (:edges w) h))
  (cases hf (edge-find w x))
  (simp only [remove-edge hf marks-waiting-rest]) (exact h)
  (rename_i e)
  (cases hm (:marked e))
  (simp only [remove-edge hf hm marks-waiting-rest edge-del set-edges]) (exact h1)
  (have s := (hu e hf hm))
  (simp only [remove-edge hf hm marks-waiting-rest comp-upd edge-del set-comps set-edges])
  (exact (hk-cs-pend hxm (:comps w) (:creditor e) comp-dec-pending hk-dec-id hk-dec-idle hk-dec-ep hk-dec-done _ s h1)))

;; ---- drop-edges: the dropped marked edges have safe creditors
(a/defn hk-dok [hxm :- (List Nat), cs :- (List CompRow), p :- (=> EdgeRow Bool), e :- EdgeRow] Bool
  (Bool.or (p e) (Bool.or (Bool.not (:marked e)) (hk-safe hxm cs (:creditor e)))))

(a/theorem hk-count-eq [hxm :- (List Nat), cs :- (List CompRow), p :- (=> EdgeRow Bool), d :- Nat, es :- (List EdgeRow)]
  (=> (= (tbl-all (hk-dok hxm cs p) es) true) (= (hk-safe hxm cs d) false)
      (= (marked-in d (tbl-filter p es)) (marked-in d es)))
  (induction es)
  (case' [cons h t ih])
  (case' [nil])
  (intros h1 h2) (simp only [tbl-filter])
  (intros h1 h2)
  (simp only [tbl-all Bool.and_eq_true] at h1)
  (have r := (ih (And.right h1) h2))
  (simp only [marked-in] at r)
  (cases hp (p h))
  (have hk1 := (And.left h1))
  (simp only [hk-dok hp Bool.false_or Bool.or_eq_true] at hk1)
  (have mk (= (marks d h) false))
  (cases hmk (:marked h))
  (simp only [marks hmk Bool.and_false])
  (cases hc (Nat.beq (:creditor h) d))
  (simp only [marks hc Bool.false_and])
  (have e1 := (Nat.eq_of_beq_eq_true hc))
  (cases hk1)
  (rename_i z) (rw [hmk] at z) (cases z)
  (rename_i z) (rw [e1] at z) (rw [h2] at z) (cases z)
  (simp only [marked-in tbl-filter hp tbl-count mk r])
  (cases hmk (marks d h))
  (simp only [marked-in tbl-filter hp tbl-count hmk r])
  (simp only [marked-in tbl-filter hp tbl-count hmk r]))

(a/theorem hk-wif-resync-s [d :- Nat, es :- (List EdgeRow), cs :- (List CompRow)]
  (=> (= (tbl-all (hk-sif d) cs) true) (= (tbl-all (hk-wif d) cs) true) (= (tbl-all (hk-wif d) (comps-resync es cs)) true))
  (induction cs)
  (case' [cons h t ih])
  (case' [nil])
  (intros h1 h2) (simp only [comps-resync tbl-all])
  (intros h1 h2)
  (simp only [tbl-all Bool.and_eq_true] at h1 h2)
  (have r := (ih (And.right h1) (And.right h2)))
  (simp only [comps-resync tbl-all r Bool.and_true])
  (have a1 := (And.left h1)) (have a2 := (And.left h2))
  (cases hd (Nat.beq (:id h) d))
  (simp only [hk-wif comp-resync comp-set-pending hd Bool.not_false Bool.true_or])
  (simp only [hk-sif hd hk-strong Bool.not_true Bool.false_or Bool.or_eq_true] at a1)
  (simp only [hk-wif hd waiting-strongly Bool.not_true Bool.false_or Bool.and_eq_true] at a2)
  (simp only [hk-wif comp-resync comp-set-pending hd waiting-strongly Bool.not_true Bool.false_or])
  (cases a1)
  (rename_i z) (rw [z] at a2) (simp at a2)
  (rename_i z) (simp only [z Bool.true_or Bool.and_true]) (exact (And.left a2)))

(a/theorem hk-wif-resync-eq [d :- Nat, es :- (List EdgeRow), es2 :- (List EdgeRow), cs :- (List CompRow)]
  (=> (= (marked-in d es2) (marked-in d es)) (= (tbl-all (comp-exact es) cs) true) (= (tbl-all (hk-wif d) cs) true)
      (= (tbl-all (hk-wif d) (comps-resync es2 cs)) true))
  (induction cs)
  (case' [cons h t ih])
  (case' [nil])
  (intros h0 h1 h2) (simp only [comps-resync tbl-all])
  (intros h0 h1 h2)
  (simp only [tbl-all Bool.and_eq_true] at h1 h2)
  (have r := (ih h0 (And.right h1) (And.right h2)))
  (simp only [comps-resync tbl-all r Bool.and_true])
  (have a1 := (And.left h1)) (have a2 := (And.left h2))
  (cases hd (Nat.beq (:id h) d))
  (simp only [hk-wif comp-resync comp-set-pending hd Bool.not_false Bool.true_or])
  (have e1 := (Nat.eq_of_beq_eq_true hd))
  (simp only [comp-exact Nat.beq_eq] at a1)
  (have e2 (= (marked-in (:id h) es2) (:pending h))) (rw [e1]) (rw [h0]) (rw [← e1]) (exact (Eq.symm a1))
  (simp only [hk-wif comp-resync comp-set-pending hd e2 Bool.not_true Bool.false_or])
  (simp only [hk-wif hd Bool.not_true Bool.false_or] at a2) (exact a2))

(a/theorem hkr-drop-edges [hxm :- (List Nat), w :- World, p :- (=> EdgeRow Bool)]
  (=> (= (tbl-all (hk-dok hxm (:comps w) p) (:edges w)) true) (= (pending-exact w) true)
      (= (marks-waiting-rest hxm w) true) (= (marks-waiting-rest hxm (drop-edges w p)) true))
  (intros hdk hpe h)
  (simp only [marks-waiting-rest] at h)
  (have h1 := (tbl-all-filter EdgeRow (hk-e hxm (:comps w)) p (:edges w) h))
  (simp only [marks-waiting-rest drop-edges set-comps set-edges])
  (apply (hk-all-cs hxm (:comps w) (comps-resync (tbl-filter p (:edges w)) (:comps w)) _ _ _ h1))
  (intros d hd) (rw [has-resync]) (exact hd)
  (intros d hx hd)
  (cases hs (hk-safe hxm (:comps w) d))
  (exact (hk-wif-resync-eq d (:edges w) (tbl-filter p (:edges w)) (:comps w) (hk-count-eq hxm (:comps w) p d (:edges w) hdk hs) hpe hd))
  (simp only [hk-safe hx Bool.false_or] at hs)
  (exact (hk-wif-resync-s d (tbl-filter p (:edges w)) (:comps w) hs hd)))

;; ---- the other primitives with a rest part
(a/theorem hkr-drop-cred [hxm :- (List Nat), w :- World, a :- Nat]
  (=> (= (tbl-has comp-id a (:comps w)) false) (= (marks-waiting-rest hxm w) true) (= (marks-waiting-rest hxm (drop-cred-edges w a)) true))
  (intros ha h)
  (simp only [marks-waiting-rest] at h)
  (simp only [marks-waiting-rest drop-cred-edges comp-upd set-comps set-edges (tbl-upd-absent CompRow comp-id a (comp-set-pending 0) (:comps w) ha)])
  (exact (tbl-all-filter EdgeRow (hk-e hxm (:comps w)) (cred-ne a) (:edges w) h)))
(a/theorem hkr-drop-act [hxm :- (List Nat), w :- World, a :- Nat]
  (=> (= (tbl-has comp-id a (:comps w)) false) (= (marks-waiting-rest hxm w) true) (= (marks-waiting-rest hxm (drop-act w a)) true))
  (intros ha h)
  (have z := (hkr-drop-cred hxm w a ha h))
  (simp only [marks-waiting-rest] at z)
  (simp only [marks-waiting-rest drop-act act-del set-acts]) (exact z))

(a/theorem hkr-comp-del [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (= (unreferenced w x) true) (= (marks-waiting-rest hxm w) true) (= (marks-waiting-rest hxm (comp-del w x)) true))
  (intros hu h)
  (simp only [marks-waiting-rest] at h) (simp only [unreferenced] at hu)
  (simp only [marks-waiting-rest comp-del set-comps])
  (apply (tbl-all-mono2 EdgeRow (edge-avoids x) (hk-e hxm (:comps w)) (hk-e hxm (tbl-del comp-id x (:comps w))) _ (:edges w) hu h))
  (intros e ha he)
  (cases hm (:marked e))
  (exact (hk-e-unm hxm _ e hm))
  (have p := (hk-e-marked hxm (:comps w) e he hm))
  (simp only [edge-avoids Bool.and_eq_true] at ha)
  (have nd := (bnot-true _ (And.right ha)))
  (have nd2 (= (Nat.beq x (:debtor e)) false)) (rw [beq-comm]) (exact nd)
  (apply (hk-e-intro hxm _ e (And.left p)))
  (rw [(tbl-has-del-ne CompRow comp-id x (:debtor e) (:comps w) nd2)]) (exact (And.left (And.right p)))
  (have q := (And.right (And.right p)))
  (cases q)
  (rename_i z) (exact (Or.inl z))
  (rename_i z)
  (exact (Or.inr (tbl-all-del CompRow comp-id x (hk-wif (:debtor e)) (hk-wif (:debtor e))
                   (fn [c :- CompRow, h1 :- (= (hk-wif (:debtor e) c) true), h2 :- (= (Nat.beq (comp-id c) x) false)] h1) (:comps w) z))))

;; a new computation row that is waiting (T3's new-comp-row: epoch 1, done-epoch 0)
(a/theorem hkr-comp-ins [hxm :- (List Nat), w :- World, r :- CompRow]
  (=> (= (waiting-strongly r) true) (= (marks-waiting-rest hxm w) true) (= (marks-waiting-rest hxm (bump (comp-ins w r))) true))
  (intros hw h)
  (simp only [marks-waiting-rest] at h)
  (simp only [marks-waiting-rest bump comp-ins set-next-id set-comps])
  (apply (hk-all-cs hxm (:comps w) (tbl-ins r (:comps w)) (:edges w) _ _ h))
  (intros d hd) (exact (has-ins-of CompRow comp-id r (:comps w) d hd))
  (intros d hx hd) (simp only [tbl-ins tbl-all hd hk-wif hw Bool.or_true Bool.and_self]))

;; a new edge is unmarked
(a/theorem hkr-insert-edge-fresh [hxm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (marks-waiting-rest hxm w) true) (= (marks-waiting-rest hxm (insert-edge-fresh w e)) true))
  (intro h)
  (simp only [marks-waiting-rest] at h)
  (simp only [marks-waiting-rest insert-edge-fresh insert-edge bump edge-ins set-next-id set-edges tbl-ins tbl-all h Bool.and_true hk-e edge-set-marked Bool.not_false Bool.true_or]))
(a/theorem hkr-insert-edge-checked [hxm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (marks-waiting-rest hxm w) true) (= (marks-waiting-rest hxm (insert-edge-checked w e)) true))
  (intro h)
  (cases hk0 (edge-ok-in w e))
  (simp only [insert-edge-checked hk0]) (exact h)
  (simp only [insert-edge-checked hk0]) (exact (hkr-insert-edge-fresh hxm w e h)))

;; the filter keeps a kept edge's debtor
(a/theorem hkr-filter-world [hxm :- (List Nat), w :- World, K :- (=> Nat Bool)]
  (=> (= (filter-safe-for K w) true) (= (marks-waiting-rest hxm w) true) (= (marks-waiting-rest hxm (filter-world K w)) true))
  (intros hs h)
  (simp only [filter-safe-for Bool.and_eq_true] at hs)
  (simp only [marks-waiting-rest] at h)
  (simp only [marks-waiting-rest filter-world])
  (have hb := (tbl-all-mono2 EdgeRow (filter-keeps-ends K) (hk-e hxm (:comps w)) (both (filter-keeps-ends K) (hk-e hxm (:comps w)))
                (both-of EdgeRow (filter-keeps-ends K) (hk-e hxm (:comps w))) (:edges w) (And.left hs) h))
  (apply (tbl-all-keep EdgeRow K edge-id (both (filter-keeps-ends K) (hk-e hxm (:comps w))) (hk-e hxm (tbl-keep K comp-id (:comps w))) _ (:edges w) hb))
  (intros e he hk1)
  (simp only [both Bool.and_eq_true] at he)
  (have f1 := (And.left he)) (have hk2 (= (K (:id e)) true)) (exact hk1)
  (simp only [filter-keeps-ends hk2 Bool.not_true Bool.false_or Bool.and_eq_true] at f1)
  (cases hm (:marked e))
  (exact (hk-e-unm hxm _ e hm))
  (have p := (hk-e-marked hxm (:comps w) e (And.right he) hm))
  (apply (hk-e-intro hxm _ e (And.left p)))
  (rw [tbl-has-keep]) (simp only [(And.right f1) (And.left (And.right p)) Bool.and_self])
  (have q := (And.right (And.right p)))
  (cases q)
  (rename_i z) (exact (Or.inl z))
  (rename_i z)
  (exact (Or.inr (tbl-all-keep CompRow K comp-id (hk-wif (:debtor e)) (hk-wif (:debtor e))
                   (fn [c :- CompRow, h1 :- (= (hk-wif (:debtor e) c) true), h2 :- (= (K (comp-id c)) true)] h1) (:comps w) z))))

;; ---- computation row functions that keep a waiting row waiting
(a/theorem waiting-strongly-mono [c :- CompRow, d :- CompRow]
  (=> (=> (= (:idle c) false)
          (And (= (:idle d) false) (And (<= (:epoch c) (:epoch d)) (And (= (:done-epoch d) (:done-epoch c)) (= (:pending d) (:pending c))))))
      (= (waiting-strongly c) true) (= (waiting-strongly d) true))
  (intros hf h)
  (cases hic (:idle c))
  (have q := (hf hic))
  (have q1 := (And.left q)) (have q2 := (And.left (And.right q)))
  (have q3 := (And.left (And.right (And.right q)))) (have q4 := (And.right (And.right (And.right q))))
  (simp only [waiting-strongly hic Bool.not_false Bool.true_and] at h)
  (simp only [waiting-strongly q1 q3 q4 Bool.not_false Bool.true_and])
  (cases hb (Nat.blt (:done-epoch c) (:epoch c)))
  (simp only [hb Bool.false_or] at h) (simp only [h Bool.or_true])
  (have l := (comp-facts-lt-of _ _ hb))
  (have l2 (= (Nat.blt (:done-epoch c) (:epoch d)) true)) (exact (comp-facts-blt-of _ _ (Nat.lt_of_lt_of_le l q2)))
  (simp only [l2 Bool.true_or])
  (simp only [waiting-strongly hic Bool.not_true Bool.false_and] at h) (cases h))

(a/theorem comp-inc-epoch-hkm [c :- CompRow] (=> (= (waiting-strongly c) true) (= (waiting-strongly (comp-inc-epoch c)) true))
  (apply (waiting-strongly-mono c (comp-inc-epoch c)))
  (intro hi) (exact (And.intro hi (And.intro (Nat.le_succ _) (And.intro (rfl) (rfl))))))
(a/theorem comp-demand-row-hkm [c :- CompRow] (=> (= (waiting-strongly c) true) (= (waiting-strongly (comp-demand-row c)) true))
  (apply (waiting-strongly-mono c (comp-demand-row c)))
  (intro hi)
  (have le (<= (:epoch c) (:epoch (comp-demand-row c))))
  (cases hd (Nat.beq (:done-epoch c) 0))
  (simp only [comp-demand-row hd]) (omega)
  (simp only [comp-demand-row hd]) (omega)
  (exact (And.intro (rfl) (And.intro le (And.intro (rfl) (rfl))))))
(a/theorem comp-replace-row-hkm [i :- (List Nat), b :- Nat, c :- CompRow] (=> (= (waiting-strongly c) true) (= (waiting-strongly (comp-replace-row i b c)) true))
  (apply (waiting-strongly-mono c (comp-replace-row i b c)))
  (intro hi)
  (have dd (= (:done-epoch (comp-replace-row i b c)) (:done-epoch c))) (simp only [comp-replace-row hi])
  (exact (And.intro (rfl) (And.intro (Nat.le_succ _) (And.intro dd (rfl))))))
(a/theorem comp-start-row-hkm [rid :- Nat, c :- CompRow] (=> (= (waiting-strongly c) true) (= (waiting-strongly (comp-start-row rid c)) true))
  (apply (waiting-strongly-mono c (comp-start-row rid c)))
  (intro hi)
  (have le (<= (:epoch c) (:epoch (comp-start-row rid c))))
  (simp only [comp-start-row start-epoch hi Bool.false_and]) (omega)
  (exact (And.intro (rfl) (And.intro le (And.intro (rfl) (rfl))))))

;; ---- the full-bundle forms of the non-frame primitives (extra premises: their users are overrides)
(a/theorem marks-waiting-mark-edge [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (= (tbl-all (hk-mok hxm (:comps w) x) (:edges w)) true) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (mark-edge w x)) true))
  (intros hk0 h) (exact (marks-waiting-intro hxm _ (well-formed-mark-edge w x (marks-waiting-well-formed hxm w h)) (hkr-mark-edge hxm w x hk0 (marks-waiting-rest-of hxm w h)))))
(a/theorem marks-waiting-unmark-edge [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true) (= (hk-safe hxm (:comps w) (:creditor e)) true))) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (unmark-edge w x)) true))
  (intros hk0 h) (exact (marks-waiting-intro hxm _ (well-formed-unmark-edge w x (marks-waiting-well-formed hxm w h)) (hkr-unmark-edge hxm w x hk0 (marks-waiting-rest-of hxm w h)))))
(a/theorem marks-waiting-remove-edge [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true) (= (hk-safe hxm (:comps w) (:creditor e)) true))) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (remove-edge w x)) true))
  (intros hk0 h) (exact (marks-waiting-intro hxm _ (well-formed-remove-edge w x (marks-waiting-well-formed hxm w h)) (hkr-remove-edge hxm w x hk0 (marks-waiting-rest-of hxm w h)))))
(a/theorem marks-waiting-drop-cred-edges [hxm :- (List Nat), w :- World, a :- Nat]
  (=> (= (tbl-has comp-id a (:comps w)) false) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (drop-cred-edges w a)) true))
  (intros ha h) (exact (marks-waiting-intro hxm _ (well-formed-drop-cred-edges w a (marks-waiting-well-formed hxm w h)) (hkr-drop-cred hxm w a ha (marks-waiting-rest-of hxm w h)))))
(a/theorem marks-waiting-drop-act [hxm :- (List Nat), w :- World, a :- Nat]
  (=> (= (tbl-has comp-id a (:comps w)) false) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (drop-act w a)) true))
  (intros ha h) (exact (marks-waiting-intro hxm _ (well-formed-drop-act w a (marks-waiting-well-formed hxm w h)) (hkr-drop-act hxm w a ha (marks-waiting-rest-of hxm w h)))))
(a/theorem marks-waiting-drop-edges [hxm :- (List Nat), w :- World, p :- (=> EdgeRow Bool)]
  (=> (= (tbl-all (hk-dok hxm (:comps w) p) (:edges w)) true) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (drop-edges w p)) true))
  (intros hk0 h)
  (exact (marks-waiting-intro hxm _ (well-formed-drop-edges w p (marks-waiting-well-formed hxm w h))
           (hkr-drop-edges hxm w p hk0 (And.left (marks-waiting-parts hxm w h)) (marks-waiting-rest-of hxm w h)))))
(a/theorem marks-waiting-comp-ins [hxm :- (List Nat), w :- World, r :- CompRow, hw :- (= (waiting-strongly r) true)]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (marks-waiting hxm w) true) (= (marks-waiting hxm (bump (comp-ins w r))) true))
  (intros h1 h2 h)
  (exact (marks-waiting-intro hxm _ (well-formed-comp-ins-fresh w r h1 h2 (marks-waiting-well-formed hxm w h)) (hkr-comp-ins hxm w r hw (marks-waiting-rest-of hxm w h)))))

;; ===========================================================================
;; Part C. The bundle copy
;; ===========================================================================

;; hmk's exempt form (spindel.v2.pres.exempt; recorded, no aliases yet)
(exempt/defexempt 'marks-waiting
  :form "marks-waiting hxm w" :ids "debtor ids: a marked dep edge on a debtor in hxm need not be strongly waiting"
  :commit "marks-waiting [] (chain-to-marks-waiting)")
(def HMK (mk-bundle 'marks-waiting '[hxm :- (List Nat)] "marks-waiting-" {'well-formed-comp-ins-fresh ['(Eq.refl true) 2]}))
(swap! (:renames HMK) assoc 'well-formed-parts 'marks-waiting-parts 'well-formed-comp-ins-fresh 'marks-waiting-comp-ins
       'well-formed-mark-edge 'marks-waiting-mark-edge 'well-formed-unmark-edge 'marks-waiting-unmark-edge 'well-formed-remove-edge 'marks-waiting-remove-edge
       'well-formed-drop-cred-edges 'marks-waiting-drop-cred-edges 'well-formed-drop-act 'marks-waiting-drop-act 'well-formed-drop-edges 'marks-waiting-drop-edges)
(defpart HMK :reads '[comps edges])
(prim! HMK 'well-formed-edge-upd '(hkr-edge-upd hxm w x f hk hd hm R))
(prim! HMK 'well-formed-filter-world '(hkr-filter-world hxm w K h1 R))
(prim! HMK 'well-formed-comp-del-unref '(hkr-comp-del hxm w x h0 R))
(prim! HMK 'well-formed-insert-edge-fresh '(hkr-insert-edge-fresh hxm w e R))
(prim! HMK 'well-formed-insert-edge-checked '(hkr-insert-edge-checked hxm w e R))

;; the row functions that change a computation's keys (hmk's sites, by lemma)
(def ^:private hk-cm '#{comp-inc-epoch comp-demand-row comp-replace-row comp-start-row comp-make-idle comp-result-row comp-react-row})
(defn- hk-fhead [f] (if (seq? f) (first f) f))
(defn- hk-lapp [f lem] (if (seq? f) (apply list lem (rest f)) lem))

;; marks-waiting on the generic tree (spindel.v2.pres.tree): its table; its own proofs follow (Parts D, E, G and
;; inv.marks-step)
(tree/part! HMK
  ;; ---- the part's own proofs (content: activations are no computations, removed edges are
  ;; unmarked, T2's dirty set, T11's strong computation, T12's completion)
  :over '{well-formed-dep-consumed        marks-waiting-dep-consumed
          well-formed-fire-dep            marks-waiting-fire-dep
          well-formed-fire-wait-act       marks-waiting-fire-wait-act
          well-formed-fire-wait           marks-waiting-fire-wait
          well-formed-fire-edge           marks-waiting-fire-edge
          well-formed-cancel-acts         marks-waiting-cancel-acts
          well-formed-t8-unobserve        marks-waiting-t8-unobserve
          well-formed-t22-host-unawait              marks-waiting-t22-host-unawait
          well-formed-finalize-loop            marks-waiting-finalize-loop
          well-formed-t10-finalize-debtor     marks-waiting-t10-finalize-debtor
          well-formed-end-link            marks-waiting-end-link
          well-formed-close-local         marks-waiting-close-local
          well-formed-debtor-side         marks-waiting-debtor-side
          well-formed-finalize-if-final        marks-waiting-finalize-if-final
          well-formed-t-deliver           marks-waiting-t-deliver
          well-formed-track-fin           marks-waiting-track-fin
          well-formed-track-raw           marks-waiting-track-raw
          well-formed-revoke-roots        marks-waiting-revoke-roots
          well-formed-react-one           marks-waiting-react-one
          well-formed-react-loop          marks-waiting-react-loop
          well-formed-detach              marks-waiting-detach
          well-formed-cut-suffix          marks-waiting-cut-suffix
          well-formed-consume-entry       marks-waiting-consume-entry
          well-formed-dispatch-raw        marks-waiting-dispatch-raw
          well-formed-t11-dispatch                 marks-waiting-t11-dispatch
          well-formed-create-comp-raw     marks-waiting-create-comp-raw
          well-formed-t3-create                  marks-waiting-t3-create
          well-formed-t3-create-top              marks-waiting-t3-create-top
          well-formed-t2-write                  marks-waiting-t2-write
          well-formed-t12-complete                 marks-waiting-t12-complete
          well-formed-write-raw           marks-waiting-write-raw-x
          well-formed-complete-raw        marks-waiting-complete-raw-x
          well-formed-complete-body       marks-waiting-complete-body-x
          well-formed-retire-one          marks-waiting-retire-one
          well-formed-t28-retire-local      marks-waiting-t28-retire-local-hand}
  ;; ---- sites: a computation edit keeps a waiting row waiting (by lemma where the row function
  ;; changes the computation's keys)
  :sites (tree/row-sites 'well-formed-comp-upd (constantly true)
                         (fn [F] (list 'marks-waiting-comp-upd-m 'hxm 'w 'x F 'hid 'hp
                                       (if (contains? hk-cm (hk-fhead F)) (hk-lapp F (symbol (str (hk-fhead F) "-hkm")))
                                           '(fn [c :- CompRow, hc :- (= (waiting-strongly c) true)] hc))
                                       'h0)))
  ;; ---- facts from the path: what hmk's own proofs take ...
  :ctx '{well-formed-drop-act       [(= (tbl-has comp-id a (:comps w)) false)]   ; activations are no computations
         well-formed-t10-finalize-debtor [(= (tbl-has comp-id d (:comps w)) false)]  ; a source or task debtor: no computation
         well-formed-t2-write             [(= (comp-facts w) true) (= (i7-idle w) true) (= (acts-parked w) true)]
         well-formed-t3-create             [(= (comp-facts w) true) (= (i7-idle w) true)]
         well-formed-t3-create-top         [(= (comp-facts w) true) (= (i7-idle w) true)]
         well-formed-t11-dispatch            [(= (comp-facts w) true)]
         well-formed-t12-complete            [(= (i10-current w) true) (= (comp-facts w) true) (= (i7-idle w) true)]
         well-formed-t28-retire-local [(= (comp-facts w) true) (= (i7-idle w) true)]}
  ;; ---- ... and the facts nodes take from above them and pass on: comp-facts, i7-idle, acts-parked, i10-current from the step's
  ;; input (T2, T3, T11, T12, T13); raw0's branches forward them (inferred)
  :own '{;; "not a computation id": the source, link or activation an edit finalizes or resumes
         well-formed-resume              [ha (= (tbl-has comp-id (:id a) (:comps w)) false)]
         well-formed-close-raw           [hx (= (tbl-has comp-id x (:comps w)) false)]
         well-formed-close-source        [hx (= (tbl-has comp-id x (:comps w)) false)]
         well-formed-close-source-ended       [hx (= (tbl-has comp-id x (:comps w)) false)]
         well-formed-detach-source       [hx (= (tbl-has comp-id x (:comps w)) false)]
         well-formed-deliver-res         [hx (= (tbl-has comp-id x (:comps w)) false)]
         well-formed-realize-link        [hx (= (tbl-has comp-id x (:comps w)) false)]
         well-formed-link-next-raw       [hx (= (tbl-has comp-id l (:comps w)) false)]
         well-formed-link-realize-raw    [hx (= (tbl-has comp-id l (:comps w)) false)]
         well-formed-append-raw          [hx (= (tbl-has comp-id old (:comps w)) false)]
         well-formed-fire-task-cancelled [hd (= (tbl-has comp-id d (:comps w)) false)]
         well-formed-raw   [hg (= (comp-facts w) true) hg7 (= (i7-idle w) true) hga (= (acts-parked w) true) hg10 (= (i10-current w) true)]
         well-formed-host-guarded-transition [hg (= (comp-facts w) true) hg7 (= (i7-idle w) true) hga (= (acts-parked w) true) hg10 (= (i10-current w) true)]
         well-formed-transition  [hg (= (comp-facts w) true) hg7 (= (i7-idle w) true) hga (= (acts-parked w) true) hg10 (= (i10-current w) true)]}
  ;; the fact through the edits before the callee (they keep the computation rows)
  :pass '{well-formed-resume              {well-formed-drop-act [ha]}
          well-formed-close-raw           {well-formed-close-source [(Eq.trans (hk-has-end-link w t _ v x) hx)]}
          well-formed-close-source        {well-formed-close-source-ended [(Eq.trans (hk-has-end-stream w x x) hx)]}
          well-formed-close-source-ended       {well-formed-t10-finalize-debtor [(Eq.trans (hk-has-wake-closed (source-upd w x source-close-row) x x) hx)]}
          well-formed-detach-source       {well-formed-t10-finalize-debtor [(Eq.trans (hk-has-wake-closed (source-upd w x source-detach-row) x x) hx)]}
          well-formed-fire-task-cancelled {well-formed-t10-finalize-debtor [(Eq.trans (hk-fold-fire-has res-cancelled (tbl-scan edge-id (on-task d) (:edges w)) w d) hd)]}
          well-formed-deliver-res         {well-formed-t10-finalize-debtor [(Eq.trans (hk-fold-fire-has res (waits-on x (:edges w)) _ x)
                                                         (Eq.trans (hk-fold-fire-has res (edges-onto x (:edges w)) (source-upd w x (source-write v)) x) hx))]}
          ;; (the edit before the callee keeps the computation rows: hx at the edited world, by rfl)
          well-formed-realize-link        {well-formed-deliver-res [(Eq.trans (Eq.refl (tbl-has comp-id x (:comps (source-upd w x (link-done-row fl n))))) hx)]}
          well-formed-link-next-raw       {well-formed-realize-link [(Eq.trans (Eq.refl (tbl-has comp-id l (:comps (bump (source-ins w (new-link (:next-id w) root-scope-id 0)))))) hx)]}
          well-formed-append-raw          {well-formed-realize-link [(Eq.trans (Eq.refl (tbl-has comp-id old (:comps (bump (source-ins (source-upd w x (stream-set-tail (:next-id w)))
                                                                                                                       (new-link (:next-id w) root-scope-id x)))))) hx)]}
          ;; ... and from the transitions: the source (or the stream's tail link) is a source row
          well-formed-t-close             {well-formed-close-raw [(hk-source-not-comp w x (base-of w h) (tbl-find-has SourceRow source-id x s (:sources w) hf))]}
          well-formed-t-link-realize      {well-formed-link-realize-raw [(hk-source-not-comp w l (base-of w h) (tbl-find-has SourceRow source-id l s (:sources w) hf))]}
          well-formed-t-append            {well-formed-append-raw [(hk-source-not-comp w (:tail s) (base-of w h)
                                                    (link-pending-has w (:tail s) (bool-and-right _ _ (bool-and-right _ _ hg))))]}})

;; ===========================================================================
;; Part D. hmk's own proofs: activations are no computations, removed edges are unmarked
;; ===========================================================================

;; ---- ids: a row of another table is no computation
(a/theorem hk-task-not-comp [w :- World, y :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has task-id y (:tasks w)) true) (= (tbl-has comp-id y (:comps w)) false))
  (intros h ha)
  (cases hc (tbl-has comp-id y (:comps w)))
  (rfl)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have u2 := (nat-nodup-app-right _ _ u))
  (have hm (= (nat-mem y (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hc)
  (have hm2 (= (nat-mem y (tbl-ids task-id (:tasks w))) true)) (rw [nat-mem-ids]) (exact ha)
  (have d := (nodup-app-disj y _ _ u2 hm))
  (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
  (have d2 := (And.left d))
  (rw [hm2] at d2) (cases d2))
(a/theorem hk-source-not-comp [w :- World, y :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has source-id y (:sources w)) true) (= (tbl-has comp-id y (:comps w)) false))
  (intros h ha)
  (cases hc (tbl-has comp-id y (:comps w)))
  (rfl)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have u2 := (nat-nodup-app-right _ _ u))
  (have hm (= (nat-mem y (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hc)
  (have hm2 (= (nat-mem y (tbl-ids source-id (:sources w))) true)) (rw [nat-mem-ids]) (exact ha)
  (have d := (nodup-app-disj y _ _ u2 hm))
  (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
  (have d2 := (And.left (And.right (And.right d))))
  (rw [hm2] at d2) (cases d2))
(a/theorem hk-final-not-comp [w :- World, d :- Nat]
  (=> (= (well-formed w) true) (= (deb-final w d) true) (= (tbl-has comp-id d (:comps w)) false))
  (intros h hf)
  (cases hs (source-find w d))
  (cases ht (task-find w d))
  (simp only [deb-final hs ht] at hf) (cases hf)
  (rename_i t) (exact (hk-task-not-comp w d h (tbl-find-has TaskRow task-id d t (:tasks w) ht)))
  (rename_i s) (exact (hk-source-not-comp w d h (tbl-find-has SourceRow source-id d s (:sources w) hs))))

;; ---- a found marked edge is a dep edge on a computation
(a/theorem hk-found [hxm :- (List Nat), w :- World, x :- Nat, e :- EdgeRow]
  (=> (= (marks-waiting-rest hxm w) true) (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true)
      (And (= (Nat.beq (:kind e) ek-dep) true) (= (tbl-has comp-id (:debtor e) (:comps w)) true)))
  (intros h hf hm)
  (have m := (tbl-find-mem EdgeRow edge-id x e (:edges w) hf))
  (simp only [marks-waiting-rest] at h)
  (have z := (hk-e-marked hxm (:comps w) e (tbl-all-mem EdgeRow (hk-e hxm (:comps w)) e (:edges w) h m) hm))
  (exact (And.intro (And.left z) (And.left (And.right z)))))
(a/theorem hk-found-nondep [hxm :- (List Nat), w :- World, x :- Nat, e :- EdgeRow]
  (=> (= (marks-waiting-rest hxm w) true) (= (edge-find w x) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) false) (= (:marked e) false))
  (intros h hf hk0)
  (cases hm (:marked e))
  (rfl)
  (have z := (And.left (hk-found hxm w x e h hf hm)))
  (rw [hk0] at z) (cases z))
(a/theorem hk-found-noncomp [hxm :- (List Nat), w :- World, x :- Nat, e :- EdgeRow]
  (=> (= (marks-waiting-rest hxm w) true) (= (edge-find w x) (Option.some EdgeRow e)) (= (tbl-has comp-id (:debtor e) (:comps w)) false) (= (:marked e) false))
  (intros h hf hk0)
  (cases hm (:marked e))
  (rfl)
  (have z := (And.right (hk-found hxm w x e h hf hm)))
  (rw [hk0] at z) (cases z))
(a/theorem hk-u-of-unm [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) false)))
      (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true) (= (hk-safe hxm (:comps w) (:creditor e)) true))))
  (intros hu e hf hm) (have z := (hu e hf)) (rw [hm] at z) (cases z))
;; the found edge with id (:id e) is e: unmarked when its kind is not dep / its debtor no computation
(a/theorem hk-u-self-nondep [hxm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (marks-waiting-rest hxm w) true) (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) false)
      (forall [e2 :- EdgeRow] (=> (= (edge-find w (:id e)) (Option.some EdgeRow e2)) (= (:marked e2) true) (= (hk-safe hxm (:comps w) (:creditor e2)) true))))
  (intros h hf hk0)
  (apply (hk-u-of-unm hxm w (:id e)))
  (intros e2 hf2) (rw [hf] at hf2) (have ee := (Option.some.inj hf2)) (rw [← ee])
  (exact (hk-found-nondep hxm w (:id e) e h hf hk0)))
(a/theorem hk-u-self-noncomp [hxm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (marks-waiting-rest hxm w) true) (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (tbl-has comp-id (:debtor e) (:comps w)) false)
      (forall [e2 :- EdgeRow] (=> (= (edge-find w (:id e)) (Option.some EdgeRow e2)) (= (:marked e2) true) (= (hk-safe hxm (:comps w) (:creditor e2)) true))))
  (intros h hf hk0)
  (apply (hk-u-of-unm hxm w (:id e)))
  (intros e2 hf2) (rw [hf] at hf2) (have ee := (Option.some.inj hf2)) (rw [← ee])
  (exact (hk-found-noncomp hxm w (:id e) e h hf hk0)))

;; ---- computation ids through edge removal and activation drops
(a/theorem hk-has-remove-edge [w :- World, x :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (remove-edge w x))) (tbl-has comp-id y (:comps w)))
  (cases hf (edge-find w x))
  (simp only [remove-edge hf])
  (rename_i e)
  (cases hm (:marked e))
  (simp only [remove-edge hf hm edge-del set-edges])
  (simp only [remove-edge hf hm comp-upd edge-del set-comps set-edges (tbl-has-upd CompRow comp-id (:creditor e) y comp-dec-pending hk-dec-id (:comps w))]))
(a/theorem hk-has-dep-consumed [w :- World, e :- EdgeRow, y :- Nat]
  (= (tbl-has comp-id y (:comps (dep-consumed w e))) (tbl-has comp-id y (:comps w)))
  (cases hd (deb-final w (:debtor e)))
  (simp only [dep-consumed hd edge-upd set-edges])
  (simp only [dep-consumed hd]) (exact (hk-has-remove-edge w (:id e) y)))
(a/theorem hk-has-drop-act [w :- World, a :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (drop-act w a))) (tbl-has comp-id y (:comps w)))
  (simp only [drop-act act-del drop-cred-edges comp-upd set-acts set-comps set-edges
              (tbl-has-upd CompRow comp-id a y (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (comp-id c))) (:comps w))]))

(a/defn hk-noc [cs :- (List CompRow), y :- Nat] Bool (Bool.not (tbl-has comp-id y cs)))
(a/theorem hk-scan-all [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), Q :- (=> Nat Bool), xs :- (List A)]
  (=> (forall [r :- A] (=> (List.Mem r xs) (= (Q (idf r)) true))) (= (tbl-all Q (tbl-scan idf p xs)) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hq) (simp only [tbl-scan tbl-all])
  (intro hq)
  (have r := (ih (fn [q :- A, m :- (List.Mem q t)] (hq q (List.Mem.tail h m)))))
  (cases hp (p h))
  (simp only [tbl-scan hp r])
  (simp only [tbl-scan hp tbl-all r (hq h (List.Mem.head t)) Bool.and_self]))
(a/theorem hk-acts-noc [w :- World, p :- (=> ActRow Bool)]
  (=> (= (well-formed w) true) (= (tbl-all (hk-noc (:comps w)) (tbl-scan act-id p (:acts w))) true))
  (intro h)
  (apply (hk-scan-all ActRow act-id p (hk-noc (:comps w)) (:acts w)))
  (intros r m)
  (simp only [hk-noc (act-not-comp w (act-id r) h (has-of-mem ActRow act-id r (:acts w) m)) Bool.not_false]))

(tree/restate! HMK '[well-formed-act-upd])
(tree/restate! HMK '[well-formed-edge-upd])
(a/theorem marks-waiting-dep-consumed [hxm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (dep-consumed w e)) true))
  (intros hf h)
  (cases hd (deb-final w (:debtor e)))
  (simp only [dep-consumed hd])
  (exact (marks-waiting-edge-upd hxm w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
           (edge-rearm-edge-id _ _) (edge-rearm-kind _ _) (edge-rearm-creditor _ _) (edge-rearm-debtor _ _) (edge-rearm-marked _ _) h))
  (simp only [dep-consumed hd])
  (exact (marks-waiting-remove-edge hxm w (:id e)
           (hk-u-self-noncomp hxm w e (marks-waiting-rest-of hxm w h) hf (hk-final-not-comp w (:debtor e) (marks-waiting-well-formed hxm w h) hd)) h)))
(tree/restate! HMK '[well-formed-invalidate well-formed-fill-slot])
(a/theorem marks-waiting-fire-dep [hxm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (fire-dep w e)) true))
  (intros hf h)
  (cases ha (act-with-member (:id e) (:acts w)))
  (simp only [fire-dep ha]) (exact (marks-waiting-invalidate hxm w e h))
  (rename_i a)
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc]) (exact (marks-waiting-invalidate hxm w e h))
  (simp only [fire-dep ha hc deliver-dep])
  (have na := (act-not-comp w (:id a) (marks-waiting-well-formed hxm w h) (has-of-mem ActRow act-id a (:acts w) (act-with-member-mem (:id e) (:acts w) a ha))))
  (have na2 (= (tbl-has comp-id (:id a) (:comps (dep-consumed w e))) false)) (rw [hk-has-dep-consumed]) (exact na)
  (exact (marks-waiting-fill-slot hxm (dep-consumed w e) a (:id e) (deb-result w (:debtor e)) na2 (marks-waiting-dep-consumed hxm w e hf h))))
(tree/restate! HMK '[well-formed-edge-set-phase well-formed-fill-slot])
(a/theorem marks-waiting-fire-wait-act [hxm :- (List Nat), res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (fire-wait-act res w e)) true))
  (intro h)
  (cases ha (act-find w (:creditor e)))
  (simp only [fire-wait-act ha]) (exact (marks-waiting-edge-set-phase hxm w (:id e) ph-fired h))
  (rename_i a)
  (have na := (act-not-comp w (:id a) (marks-waiting-well-formed hxm w h)
                (has-of-mem ActRow act-id a (:acts w) (tbl-find-mem ActRow act-id (:creditor e) a (:acts w) ha))))
  (cases hc (run-current w (:run a)))
  (simp only [fire-wait-act ha hc]) (exact (marks-waiting-edge-set-phase hxm w (:id e) ph-fired h))
  (have na2 (= (tbl-has comp-id (:id a) (:comps (edge-upd w (:id e) (edge-set-phase ph-fired)))) false)) (exact na)
  (simp only [fire-wait-act ha hc])
  (exact (marks-waiting-fill-slot hxm (edge-upd w (:id e) (edge-set-phase ph-fired)) a (:id e) res na2 (marks-waiting-edge-set-phase hxm w (:id e) ph-fired h))))
(a/theorem marks-waiting-fire-wait [hxm :- (List Nat), res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-wait) true)
      (= (marks-waiting hxm w) true) (= (marks-waiting hxm (fire-wait res w e)) true))
  (intros hf hk0 h)
  (have k1 := (Nat.eq_of_beq_eq_true hk0))
  (have nd (= (Nat.beq (:kind e) ek-dep) false)) (rw [k1])
  (cases hc (Nat.beq (:creditor e) 0))
  (simp only [fire-wait hc]) (exact (marks-waiting-fire-wait-act hxm res w e h))
  (simp only [fire-wait hc])
  (exact (marks-waiting-remove-edge hxm w (:id e) (hk-u-self-nondep hxm w e (marks-waiting-rest-of hxm w h) hf nd) h)))
(tree/restate! HMK '[well-formed-fire-observe])
(a/theorem marks-waiting-fire-edge [hxm :- (List Nat), res :- RunResult, w :- World, x :- Nat]
  (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (fire-edge res w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (simp only [fire-edge hf]) (exact h)
  (rename_i e)
  (have hi (= (:id e) x)) (exact (tbl-find-id EdgeRow edge-id x e (:edges w) hf))
  (have hf2 (= (edge-find w (:id e)) (Option.some EdgeRow e))) (rw [hi]) (exact hf)
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [fire-edge hf hp]) (exact h)
  (cases hk1 (Nat.beq (:kind e) ek-dep))
  (cases hk2 (Nat.beq (:kind e) ek-wait))
  (cases hk3 (Nat.beq (:kind e) ek-observe))
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-savepoint-todo]) (exact h)
  (simp only [fire-edge hf hp hk1 hk2 hk3]) (exact (marks-waiting-fire-observe hxm w e h))
  (simp only [fire-edge hf hp hk1 hk2]) (exact (marks-waiting-fire-wait hxm res w e hf2 hk2 h))
  (simp only [fire-edge hf hp hk1]) (exact (marks-waiting-fire-dep hxm w e hf2 h)))

(a/theorem marks-waiting-fold-drop-act [hxm :- (List Nat), xs :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (hk-noc (:comps w)) xs) true) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (nat-fold drop-act w xs)) true)))
  (induction xs)
  (case' [cons a t ih])
  (case' [nil])
  (intros w hn h) (simp only [nat-fold]) (exact h)
  (intros w hn h)
  (simp only [tbl-all Bool.and_eq_true] at hn)
  (have na := (And.left hn)) (simp only [hk-noc] at na)
  (have na2 := (bnot-true _ na))
  (have h1 := (marks-waiting-drop-act hxm w a na2 h))
  (have hn2 (= (tbl-all (hk-noc (:comps (drop-act w a))) t) true))
  (apply (tbl-all-mono Nat (hk-noc (:comps w)) (hk-noc (:comps (drop-act w a))) _ t (And.right hn)))
  (intros y hy) (simp only [hk-noc hk-has-drop-act]) (simp only [hk-noc] at hy) (exact hy)
  (simp only [nat-fold]) (exact (ih (drop-act w a) hn2 h1)))
(a/theorem marks-waiting-cancel-acts [hxm :- (List Nat), w :- World, rid :- Nat]
  (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (cancel-acts w rid)) true))
  (intro h)
  (simp only [cancel-acts])
  (exact (marks-waiting-fold-drop-act hxm (tbl-scan act-id (act-of-run rid) (:acts w)) w
           (hk-acts-noc w (act-of-run rid) (marks-waiting-well-formed hxm w h)) h)))
(a/theorem marks-waiting-t8-unobserve [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (:world (t8-unobserve w x))) true))
  (intro h)
  (cases hf (edge-find w x))
  (simp only [t8-unobserve hf refuse]) (exact h)
  (rename_i e)
  (cases hk0 (Nat.beq (:kind e) ek-observe))
  (simp only [t8-unobserve hf hk0 refuse]) (exact h)
  (have k1 := (Nat.eq_of_beq_eq_true hk0))
  (have nd (= (Nat.beq (:kind e) ek-dep) false)) (rw [k1])
  (have hu := (hk-u-of-unm hxm w x (fn [e2 :- EdgeRow, hf2 :- (= (edge-find w x) (Option.some EdgeRow e2))]
                                      (hk-found-nondep hxm w x e2 (marks-waiting-rest-of hxm w h) hf2
                                        (Eq.trans (congrArg (fn [q :- EdgeRow] (Nat.beq (:kind q) ek-dep)) (Eq.symm (Option.some.inj (Eq.trans (Eq.symm hf) hf2)))) nd)))))
  (simp only [t8-unobserve hf hk0 accept]) (exact (marks-waiting-remove-edge hxm w x hu h)))
(a/theorem marks-waiting-t22-host-unawait [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (:world (t22-host-unawait w x))) true))
  (intro h)
  (cases hf (edge-find w x))
  (simp only [t22-host-unawait hf refuse]) (exact h)
  (rename_i e)
  (cases hk0 (Bool.and (Nat.beq (:kind e) ek-wait) (Nat.beq (:creditor e) 0)))
  (simp only [t22-host-unawait hf hk0 refuse]) (exact h)
  (simp only [Bool.and_eq_true] at hk0)
  (have k1 := (Nat.eq_of_beq_eq_true (And.left hk0)))
  (have nd (= (Nat.beq (:kind e) ek-dep) false)) (rw [k1])
  (have hu := (hk-u-of-unm hxm w x (fn [e2 :- EdgeRow, hf2 :- (= (edge-find w x) (Option.some EdgeRow e2))]
                                      (hk-found-nondep hxm w x e2 (marks-waiting-rest-of hxm w h) hf2
                                        (Eq.trans (congrArg (fn [q :- EdgeRow] (Nat.beq (:kind q) ek-dep)) (Eq.symm (Option.some.inj (Eq.trans (Eq.symm hf) hf2)))) nd)))))
  (have hk2 (= (Bool.and (Nat.beq (:kind e) ek-wait) (Nat.beq (:creditor e) 0)) true)) (simp only [hk0 Bool.and_self])
  (simp only [t22-host-unawait hf hk2 accept]) (exact (marks-waiting-remove-edge hxm w x hu h)))

;; ---- computation ids through the fires (no fire inserts or deletes a computation)
(a/theorem hk-has-fill-slot [w :- World, a :- ActRow, x :- Nat, v :- RunResult, y :- Nat]
  (= (tbl-has comp-id y (:comps (fill-slot w a x v))) (tbl-has comp-id y (:comps w)))
  (cases hm (act-ready (act-fill x v a)))
  (simp only [fill-slot hm act-upd set-acts])
  (simp only [fill-slot hm resume run-upd set-runs]) (exact (hk-has-drop-act w (:id a) y)))
(a/theorem hk-has-invalidate [w :- World, e :- EdgeRow, y :- Nat]
  (= (tbl-has comp-id y (:comps (invalidate w e))) (tbl-has comp-id y (:comps w)))
  (simp only [invalidate comp-upd edge-upd set-comps set-edges
              (tbl-has-upd CompRow comp-id (:creditor e) y comp-inc-epoch (fn [c :- CompRow] (Eq.refl (comp-id c))) (:comps w))]))
(a/theorem hk-has-fire-dep [w :- World, e :- EdgeRow, y :- Nat]
  (= (tbl-has comp-id y (:comps (fire-dep w e))) (tbl-has comp-id y (:comps w)))
  (cases ha (act-with-member (:id e) (:acts w)))
  (simp only [fire-dep ha]) (exact (hk-has-invalidate w e y))
  (rename_i a)
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc]) (exact (hk-has-invalidate w e y))
  (simp only [fire-dep ha hc deliver-dep])
  (exact (Eq.trans (hk-has-fill-slot (dep-consumed w e) a (:id e) (deb-result w (:debtor e)) y) (hk-has-dep-consumed w e y))))
(a/theorem hk-has-fire-wait-act [res :- RunResult, w :- World, e :- EdgeRow, y :- Nat]
  (= (tbl-has comp-id y (:comps (fire-wait-act res w e))) (tbl-has comp-id y (:comps w)))
  (cases ha (act-find w (:creditor e)))
  (simp only [fire-wait-act ha edge-upd set-edges])
  (rename_i a)
  (cases hc (run-current w (:run a)))
  (simp only [fire-wait-act ha hc edge-upd set-edges])
  (simp only [fire-wait-act ha hc])
  (exact (hk-has-fill-slot (edge-upd w (:id e) (edge-set-phase ph-fired)) a (:id e) res y)))
(a/theorem hk-has-fire-edge [res :- RunResult, w :- World, x :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (fire-edge res w x))) (tbl-has comp-id y (:comps w)))
  (cases hf (edge-find w x))
  (simp only [fire-edge hf])
  (rename_i e)
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [fire-edge hf hp])
  (cases hk1 (Nat.beq (:kind e) ek-dep))
  (cases hk2 (Nat.beq (:kind e) ek-wait))
  (cases hk3 (Nat.beq (:kind e) ek-observe))
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-savepoint-todo])
  (cases ho (observe-new e (deb-version w (:debtor e))))
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-observe ho])
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-observe ho edge-upd set-edges])
  (cases hc (Nat.beq (:creditor e) 0))
  (simp only [fire-edge hf hp hk1 hk2 fire-wait hc]) (exact (hk-has-fire-wait-act res w e y))
  (simp only [fire-edge hf hp hk1 hk2 fire-wait hc]) (exact (hk-has-remove-edge w (:id e) y))
  (simp only [fire-edge hf hp hk1]) (exact (hk-has-fire-dep w e y)))
(a/theorem hk-fold-has [f :- (=> World Nat World),
                        hf :- (forall [w :- World, x :- Nat, y :- Nat] (= (tbl-has comp-id y (:comps (f w x))) (tbl-has comp-id y (:comps w)))),
                        xs :- (List Nat)]
  (forall [w :- World, y :- Nat] (= (tbl-has comp-id y (:comps (nat-fold f w xs))) (tbl-has comp-id y (:comps w))))
  (induction xs)
  (case' [cons a t ih])
  (case' [nil])
  (intros w y) (simp only [nat-fold])
  (intros w y) (simp only [nat-fold]) (exact (Eq.trans (ih (f w a) y) (hf w a y))))
(a/theorem hk-noc-all [cs :- (List CompRow), cs2 :- (List CompRow), xs :- (List Nat)]
  (=> (forall [y :- Nat] (= (tbl-has comp-id y cs2) (tbl-has comp-id y cs)))
      (= (tbl-all (hk-noc cs) xs) true) (= (tbl-all (hk-noc cs2) xs) true))
  (intros he h)
  (apply (tbl-all-mono Nat (hk-noc cs) (hk-noc cs2) _ xs h))
  (intros y hy) (simp only [hk-noc] at hy) (simp only [hk-noc (he y)]) (exact hy))
;; a fold whose step needs its element to be no computation
(a/theorem marks-waiting-fold-noc [hxm :- (List Nat), f :- (=> World Nat World),
                         hf :- (forall [w :- World, x :- Nat] (=> (= (tbl-has comp-id x (:comps w)) false) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (f w x)) true))),
                         hh :- (forall [w :- World, x :- Nat, y :- Nat] (= (tbl-has comp-id y (:comps (f w x))) (tbl-has comp-id y (:comps w)))),
                         xs :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (hk-noc (:comps w)) xs) true) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (nat-fold f w xs)) true)))
  (induction xs)
  (case' [cons a t ih])
  (case' [nil])
  (intros w hn h) (simp only [nat-fold]) (exact h)
  (intros w hn h)
  (simp only [tbl-all Bool.and_eq_true] at hn)
  (have na := (And.left hn)) (simp only [hk-noc] at na)
  (have na2 := (bnot-true _ na))
  (simp only [nat-fold])
  (exact (ih (f w a) (hk-noc-all (:comps w) (:comps (f w a)) t (hh w a) (And.right hn)) (hf w a na2 h))))
(a/theorem hk-fold-fire-has [res :- RunResult, xs :- (List Nat), w :- World, y :- Nat]
  (= (tbl-has comp-id y (:comps (nat-fold (fire-edge res) w xs))) (tbl-has comp-id y (:comps w)))
  (exact (hk-fold-has (fire-edge res) (fn [w2 :- World, x :- Nat, y2 :- Nat] (hk-has-fire-edge res w2 x y2)) xs w y)))

;; ---- T10 finalize: the dropped edges are on a debtor that is no computation, so unmarked
(a/theorem hk-has-finalize-one [w :- World, d :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (finalize-one w d))) (tbl-has comp-id y (:comps w)))
  (simp only [finalize-one drop-edges set-comps set-edges has-resync]))
(a/theorem marks-waiting-finalize-one [hxm :- (List Nat), w :- World, d :- Nat]
  (=> (= (tbl-has comp-id d (:comps w)) false) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (finalize-one w d)) true))
  (intros hd h)
  (simp only [finalize-one])
  (apply (marks-waiting-drop-edges hxm w (finalize-keeps (:acts w) d) _ h))
  (have r := (marks-waiting-rest-of hxm w h)) (simp only [marks-waiting-rest] at r)
  (apply (tbl-all-mono EdgeRow (hk-e hxm (:comps w)) (hk-dok hxm (:comps w) (finalize-keeps (:acts w) d)) _ (:edges w) r))
  (intros e he)
  (cases hk0 (finalize-keeps (:acts w) d e))
  (cases hm (:marked e))
  (simp only [hk-dok hk0 hm Bool.not_false Bool.true_or Bool.false_or])
  (have p := (hk-e-marked hxm (:comps w) e he hm))
  (have hk1 := hk0) (simp only [finalize-keeps] at hk1)
  (have hd0 := (bnot-false _ hk1))
  (simp only [finalize-drops Bool.and_eq_true] at hd0)
  (have de := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right hd0)))))
  (have z := (And.left (And.right p))) (rw [de] at z) (rw [hd] at z) (cases z)
  (simp only [hk-dok hk0 Bool.true_or]))
(a/theorem hk-append-nil [xs :- (List Nat)] (= (List.append Nat xs (List.nil Nat)) xs)
  (induction xs) (case [nil] (rfl)) (case [cons h t ih] (simp only [List.append ih])))
(a/theorem marks-waiting-finalize-loop [hxm :- (List Nat), fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat)]
    (=> (= (tbl-all (hk-noc (:comps w)) ds) true) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (:world (finalize-loop fuel w ds))) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w ds hn hw) (simp only [finalize-loop]) (exact hw)
  (intros w ds hn hw)
  (cases ds)
  (simp only [finalize-loop]) (exact hw)
  (rename_i d t)
  (simp only [tbl-all Bool.and_eq_true] at hn)
  (have na := (And.left hn)) (simp only [hk-noc] at na)
  (have na2 := (bnot-true _ na))
  (have hn2 := (hk-noc-all (:comps w) (:comps (finalize-one w d)) t (fn [y :- Nat] (hk-has-finalize-one w d y)) (And.right hn)))
  (have hn3 (= (tbl-all (hk-noc (:comps (finalize-one w d)))
                 (List.append Nat t (tbl-filter (final-comp-id (finalize-one w d)) (tbl-scan edge-cred (finalize-drops (:acts w) d) (:edges w))))) true))
  (rw [filter-final-nil]) (rw [hk-append-nil]) (exact hn2)
  (simp only [finalize-loop])
  (exact (ih _ _ hn3 (marks-waiting-finalize-one hxm w d na2 hw))))
(a/theorem marks-waiting-t10-finalize-debtor [hxm :- (List Nat), w :- World, d :- Nat]
  (=> (= (tbl-has comp-id d (:comps w)) false) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (t10-finalize-debtor w d)) true))
  (intros hd h)
  (have hn (= (tbl-all (hk-noc (:comps w)) (List.cons Nat d (List.nil Nat))) true)) (simp only [tbl-all hk-noc hd Bool.not_false Bool.and_self])
  (exact (marks-waiting-finalize-loop hxm (finalize-fuel w) w _ hn h)))
(a/theorem hk-finalize-loop-has [fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat), y :- Nat] (= (tbl-has comp-id y (:comps (:world (finalize-loop fuel w ds)))) (tbl-has comp-id y (:comps w))))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w ds y) (simp only [finalize-loop])
  (intros w ds y)
  (cases ds)
  (simp only [finalize-loop])
  (rename_i d t)
  (simp only [finalize-loop])
  (exact (Eq.trans (ih _ _ y) (hk-has-finalize-one w d y))))
(a/theorem hk-has-t10-finalize-debtor [w :- World, d :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (t10-finalize-debtor w d))) (tbl-has comp-id y (:comps w)))
  (simp only [t10-finalize-debtor])
  (exact (hk-finalize-loop-has (finalize-fuel w) w (List.cons Nat d (List.nil Nat)) y)))

;; ---- the callers of t10-finalize-debtor: the finalized debtor is a source or a task
(a/theorem hk-has-wake-closed [w :- World, d :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (wake-closed w d))) (tbl-has comp-id y (:comps w)))
  (simp only [wake-closed]) (exact (hk-fold-fire-has (deb-result w d) _ w y)))
(a/theorem hk-has-close-source-ended [w :- World, x :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (close-source-ended w x))) (tbl-has comp-id y (:comps w)))
  (simp only [close-source-ended])
  (exact (Eq.trans (hk-has-t10-finalize-debtor (wake-closed (source-upd w x source-close-row) x) x y)
                   (hk-has-wake-closed (source-upd w x source-close-row) x y))))
;; C0: a link's realization (deliver-res) and a stream's end keep the computations
(a/theorem hk-has-deliver-res [w :- World, x :- Nat, v :- Nat, rr :- RunResult, y :- Nat]
  (= (tbl-has comp-id y (:comps (deliver-res w x v rr))) (tbl-has comp-id y (:comps w)))
  (simp only [deliver-res])
  (exact (Eq.trans (hk-has-t10-finalize-debtor _ x y) (Eq.trans (hk-fold-fire-has rr _ _ y) (hk-fold-fire-has rr _ (source-upd w x (source-write v)) y)))))
(a/theorem hk-has-end-link [w :- World, x :- Nat, fl :- Bool, v :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (end-link w x fl v))) (tbl-has comp-id y (:comps w)))
  (cases hp (link-pending w x))
  (simp only [end-link hp])
  (simp only [end-link hp realize-link]) (exact (hk-has-deliver-res _ x _ _ y)))
(a/theorem hk-has-end-stream [w :- World, x :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (end-stream w x))) (tbl-has comp-id y (:comps w)))
  (cases hf (source-find w x)) (case' [some s]) (case' [none])
  (simp only [end-stream hf])
  (cases hk (Nat.beq (:kind s) sk-stream))
  (simp only [end-stream hf hk])
  (simp only [end-stream hf hk]) (exact (hk-has-end-link w _ false 0 y)))
(a/theorem hk-has-close-source [w :- World, x :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (close-source w x))) (tbl-has comp-id y (:comps w)))
  (simp only [close-source]) (exact (Eq.trans (hk-has-close-source-ended _ x y) (hk-has-end-stream w x y))))
(a/theorem link-pending-has [w :- World, x :- Nat] (=> (= (link-pending w x) true) (= (tbl-has source-id x (:sources w)) true))
  (intro h)
  (cases hf (source-find w x)) (case' [some s]) (case' [none])
  (simp only [link-pending hf opt-test] at h) (cases h)
  (exact (tbl-find-has SourceRow source-id x s (:sources w) hf)))
(a/theorem hk-has-detach-source [w :- World, x :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (detach-source w x))) (tbl-has comp-id y (:comps w)))
  (simp only [detach-source])
  (exact (Eq.trans (hk-has-t10-finalize-debtor (wake-closed (source-upd w x source-detach-row) x) x y)
                   (hk-has-wake-closed (source-upd w x source-detach-row) x y))))
(a/theorem hk-sources-noc [w :- World, p :- (=> SourceRow Bool)]
  (=> (= (well-formed w) true) (= (tbl-all (hk-noc (:comps w)) (tbl-scan source-id p (:sources w))) true))
  (intro h)
  (apply (hk-scan-all SourceRow source-id p (hk-noc (:comps w)) (:sources w)))
  (intros r m)
  (simp only [hk-noc (hk-source-not-comp w (source-id r) h (has-of-mem SourceRow source-id r (:sources w) m)) Bool.not_false]))

(tree/restate! HMK '[well-formed-nat-fold well-formed-source-upd])
(tree/restate! HMK '[well-formed-source-upd well-formed-deliver-res])
(a/theorem marks-waiting-end-link [hxm :- (List Nat), w :- World, x :- Nat, fl :- Bool, v :- Nat]
  (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (end-link w x fl v)) true))
  (intro h)
  (cases hp (link-pending w x))
  (simp only [end-link hp]) (exact h)
  (have hx := (hk-source-not-comp w x (marks-waiting-well-formed hxm w h) (link-pending-has w x hp)))
  (simp only [end-link hp realize-link])
  (exact (marks-waiting-deliver-res hxm (source-upd w x (link-done-row fl 0)) x _ _ hx (marks-waiting-source-upd hxm w x (link-done-row fl 0) (link-done-row-id fl 0) h))))
(tree/restate! HMK '[well-formed-source-upd])
(tree/restate! HMK '[well-formed-source-ins-fresh])
(tree/restate! HMK '[well-formed-source-ins-fresh well-formed-source-upd])
(tree/restate! HMK '[well-formed-wake-closed well-formed-source-upd])
(tree/restate! HMK '[well-formed-end-stream])
(tree/restate! HMK '[well-formed-nat-fold well-formed-close-scope-id well-formed-close-source])
(a/theorem marks-waiting-close-local [hxm :- (List Nat), w :- World, sub :- (List Nat)]
  (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (close-local w sub)) true))
  (intro h)
  (have h1 := (marks-waiting-nat-fold hxm close-scope-id (marks-waiting-close-scope-id hxm) sub w h))
  (have n0 := (hk-sources-noc w (source-owned-in sub) (marks-waiting-well-formed hxm w h)))
  (have n1 := (hk-noc-all (:comps w) (:comps (nat-fold close-scope-id w sub)) (tbl-scan source-id (source-owned-in sub) (:sources w))
                (fn [y :- Nat] (hk-fold-has close-scope-id (fn [w2 :- World, x2 :- Nat, y2 :- Nat] (Eq.refl (tbl-has comp-id y2 (:comps w2)))) sub w y))
                n0))
  (simp only [close-local])
  (exact (marks-waiting-fold-noc hxm close-source (fn [w2 :- World, x2 :- Nat, hx :- (= (tbl-has comp-id x2 (:comps w2)) false), h2 :- (= (marks-waiting hxm w2) true)]
                                          (marks-waiting-close-source hxm w2 x2 hx h2))
           hk-has-close-source (tbl-scan source-id (source-owned-in sub) (:sources w)) (nat-fold close-scope-id w sub) n1 h1)))
(tree/restate! HMK '[well-formed-nat-fold])
(tree/restate! HMK '[well-formed-task-upd well-formed-invalidate-dependents well-formed-fire-waits-cancelled well-formed-clear-rtasks well-formed-fire-task-cancelled])
(a/theorem marks-waiting-debtor-side [hxm :- (List Nat), w :- World, r :- RunRow]
  (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (debtor-side w r)) true))
  (intro h)
  (cases hc (comp-find w (:of r)))
  (have hd := (tbl-find-none-has CompRow comp-id (:of r) (:comps w) hc))
  (simp only [debtor-side hc])
  (exact (marks-waiting-clear-rtasks hxm _ (:of r) (marks-waiting-fire-task-cancelled hxm (task-upd w (:of r) task-cancel-result) (:of r) hd
           (marks-waiting-task-upd hxm w (:of r) task-cancel-result task-cancel-result-id h))))
  (rename_i c)
  (cases he (Nat.beq (:epoch r) (:epoch c)))
  (simp only [debtor-side hc he]) (exact h)
  (simp only [debtor-side hc he])
  (exact (marks-waiting-invalidate-dependents hxm (fire-waits-cancelled w (:of r)) (:of r) (marks-waiting-fire-waits-cancelled hxm w (:of r) h))))
(a/theorem marks-waiting-finalize-if-final [hxm :- (List Nat), w :- World, d :- Nat]
  (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (finalize-if-final w d)) true))
  (intro h)
  (cases hf (deb-final w d))
  (simp only [finalize-if-final hf]) (exact h)
  (simp only [finalize-if-final hf]) (exact (marks-waiting-t10-finalize-debtor hxm w d (hk-final-not-comp w d (marks-waiting-well-formed hxm w h) hf) h)))
(tree/restate! HMK '[well-formed-nat-fold well-formed-deliver-fire])
(a/theorem marks-waiting-t-deliver [hxm :- (List Nat), w :- World, x :- Nat, v :- Nat]
  (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (:world (t-deliver w x v))) true))
  (intro h)
  (cases hs (source-find w x))
  (simp only [t-deliver hs refuse]) (exact h)
  (rename_i s)
  (have hx := (hk-source-not-comp w x (marks-waiting-well-formed hxm w h) (tbl-find-has SourceRow source-id x s (:sources w) hs)))
  (cases hg (deliverable s))
  (simp only [t-deliver hs hg refuse]) (exact h)
  (have h1 := (marks-waiting-nat-fold hxm (fire-edge (RunResult.mk res-ok v)) (marks-waiting-fire-edge hxm (RunResult.mk res-ok v)) (waits-on x (:edges w))
                (deliver-fire w x v) (marks-waiting-deliver-fire hxm w x v h)))
  (have hx2 (= (tbl-has comp-id x (:comps (nat-fold (fire-edge (RunResult.mk res-ok v)) (deliver-fire w x v) (waits-on x (:edges w))))) false))
  (exact (Eq.trans (hk-fold-fire-has (RunResult.mk res-ok v) (waits-on x (:edges w)) (deliver-fire w x v) x)
           (Eq.trans (hk-fold-fire-has (RunResult.mk res-ok v) (edges-onto x (:edges w)) (source-upd w x (source-write v)) x) hx)))
  (simp only [t-deliver hs hg accept deliver-raw])
  (exact (marks-waiting-t10-finalize-debtor hxm _ x hx2 h1)))

;; ---- T7: the removed track edge is unmarked (a new edge, or a site edge on the source)
(a/theorem hk-find-upd [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A),
                        hid :- (forall [r :- A] (= (idf (f r)) (idf r))), xs :- (List A), q :- A]
  (=> (= (tbl-find idf x xs) (Option.some A q)) (= (tbl-find idf x (tbl-upd idf x f xs)) (Option.some A (f q))))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hf) (simp only [tbl-find] at hf) (cases hf)
  (intro hf)
  (cases hx (Nat.beq (idf h) x))
  (simp only [tbl-find hx] at hf) (simp only [tbl-upd tbl-find hx (ih hf)])
  (simp only [tbl-find hx] at hf) (have z := (Option.some.inj hf))
  (have hx2 (= (Nat.beq (idf (f h)) x) true)) (rw [(hid h)]) (exact hx)
  (simp only [tbl-upd tbl-find hx hx2]) (rw [z]))
(a/theorem hk-find-fresh [w :- World, e :- EdgeRow, e2 :- EdgeRow]
  (=> (= (edge-find (insert-edge-fresh w e) (:next-id w)) (Option.some EdgeRow e2)) (= (:marked e2) false))
  (intro hf)
  (simp only [edge-find insert-edge-fresh insert-edge bump edge-ins set-next-id set-edges tbl-ins tbl-find edge-set-marked edge-set-id edge-id Nat.beq_refl] at hf)
  (have z := (Option.some.inj hf))
  (rw [← z]))
(a/theorem marks-waiting-track-fin [hxm :- (List Nat), s :- SourceRow, y :- Nat, w :- World]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w y) (Option.some EdgeRow e)) (= (:marked e) false)))
      (= (marks-waiting hxm w) true) (= (marks-waiting hxm (track-fin s y w)) true))
  (intros hu h)
  (cases ho (:open s))
  (simp only [track-fin ho]) (exact (marks-waiting-remove-edge hxm w y (hk-u-of-unm hxm w y hu) h))
  (simp only [track-fin ho]) (exact h))
(tree/restate! HMK '[well-formed-insert-edge-fresh well-formed-edge-upd well-formed-run-upd])
(a/theorem marks-waiting-track-raw [hxm :- (List Nat), w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat]
  (=> (= (comp-has w (:of r)) true) (= (source-find w x) (Option.some SourceRow s))
      (= (marks-waiting hxm w) true) (= (marks-waiting hxm (track-raw w r x s k)) true))
  (intros hc hs h)
  (have hxn := (hk-source-not-comp w x (marks-waiting-well-formed hxm w h) (tbl-find-has SourceRow source-id x s (:sources w) hs)))
  (have h2 (= (marks-waiting hxm (match (site-edge (:edges w) (:of r) (:effect-index r) x)
                          [none (track-new w r x s k)]
                          [(some e) (comp-upd (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s)))
                                              (:of r) (comp-consume-adopt (:effect-index r) x))])) true))
  (cases he (site-edge (:edges w) (:of r) (:effect-index r) x))
  (simp only [track-new])
  (have h3 := (marks-waiting-insert-edge-fresh hxm w (track-edge r x s k) (track-edge-ok w r x s k hc hs) h))
  (have h4 := (marks-waiting-track-fin hxm s (:next-id w) (insert-edge-fresh w (track-edge r x s k))
                (fn [e2 :- EdgeRow, hf2 :- (= (edge-find (insert-edge-fresh w (track-edge r x s k)) (:next-id w)) (Option.some EdgeRow e2))]
                  (hk-find-fresh w (track-edge r x s k) e2 hf2)) h3))
  (exact (marks-waiting-comp-upd-m hxm (track-fin s (:next-id w) (insert-edge-fresh w (track-edge r x s k))) (:of r)
           (comp-consume-adopt (:effect-index r) x) (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _)
           (fn [c :- CompRow, hc2 :- (= (waiting-strongly c) true)] hc2) h4))
  (rename_i e)
  (have sm := (site-edge-mem (:edges w) (:of r) (:effect-index r) x e he))
  (have fs := (find-self EdgeRow edge-id e (:edges w) (l5-edge-nodup w (marks-waiting-well-formed hxm w h)) (And.left sm)))
  (have fs2 (= (edge-find w (:id e)) (Option.some EdgeRow e))) (exact fs)
  (have de := (Nat.eq_of_beq_eq_true (And.right sm)))
  (have hdn (= (tbl-has comp-id (:debtor e) (:comps w)) false)) (rw [de]) (exact hxn)
  (have um := (hk-found-noncomp hxm w (:id e) e (marks-waiting-rest-of hxm w h) fs2 hdn))
  (have h3 := (marks-waiting-edge-upd hxm w (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) (edge-reread-kind _ _)
                (edge-reread-creditor _ _) (edge-reread-debtor _ _) (edge-reread-marked _ _) h))
  (have fu := (hk-find-upd EdgeRow edge-id (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) (:edges w) e fs))
  (have h4 := (marks-waiting-track-fin hxm s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s))
                (fn [e2 :- EdgeRow, hf2 :- (= (edge-find (edge-upd w (:id e) (edge-reread (track-cont r k) s)) (:id e)) (Option.some EdgeRow e2))]
                  (Eq.trans (congrArg (fn [q :- EdgeRow] (:marked q)) (Eq.symm (Option.some.inj (Eq.trans (Eq.symm fu) hf2))))
                            (Eq.trans (edge-reread-marked (track-cont r k) s e) um)))
                h3))
  (exact (marks-waiting-comp-upd-m hxm (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s))) (:of r)
           (comp-consume-adopt (:effect-index r) x) (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _)
           (fn [c :- CompRow, hc2 :- (= (waiting-strongly c) true)] hc2) h4))
  (simp only [track-raw])
  (exact (marks-waiting-run-upd hxm _ (:id r) run-tick run-tick-run-id h2)))

;; ---- release-world: every remaining edge is a host edge, never marked
(a/theorem hk-dok-host [hxm :- (List Nat), cs :- (List CompRow), e :- EdgeRow]
  (=> (= (hk-e hxm cs e) true) (= (hk-dok hxm cs not-host e) true))
  (intro he)
  (cases hm (:marked e))
  (simp only [hk-dok hm Bool.not_false Bool.true_or Bool.or_true])
  (have p := (hk-e-marked hxm cs e he hm))
  (have k1 := (Nat.eq_of_beq_eq_true (And.left p)))
  (simp only [hk-dok not-host host-cred])
  (rw [k1]))
(tree/restate! HMK '[well-formed-set-pending-act well-formed-set-pins well-formed-drop-edges well-formed-set-released])
(a/theorem marks-waiting-revoke-roots [hxm :- (List Nat), w :- World]
  (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (revoke-roots w)) true))
  (intro h)
  (have h1 := (marks-waiting-set-released hxm w true h))
  (have r := (marks-waiting-rest-of hxm _ h1)) (simp only [marks-waiting-rest] at r)
  (have p := (tbl-all-mono EdgeRow (hk-e hxm (:comps (set-released w true))) (hk-dok hxm (:comps (set-released w true)) not-host)
               (fn [e :- EdgeRow, he :- (= (hk-e hxm (:comps (set-released w true)) e) true)] (hk-dok-host hxm (:comps (set-released w true)) e he))
               (:edges (set-released w true)) r))
  (simp only [revoke-roots])
  (exact (marks-waiting-set-pending-act hxm _ 0 (marks-waiting-set-pins hxm _ _ (marks-waiting-drop-edges hxm (set-released w true) not-host p h1)))))

;; ---- reactivation: comp-react-row on an idle computation (no marked edge on it is justified by waiting)
(a/theorem marks-waiting-comp-react [hxm :- (List Nat), w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) true) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (comp-upd w (:id c) comp-react-row)) true))
  (intros hm hi h)
  (have r0 := (marks-waiting-rest-of hxm w h))
  (have r (= (marks-waiting-rest hxm (comp-upd w (:id c) comp-react-row)) true))
  (simp only [marks-waiting-rest comp-upd set-comps]) (simp only [marks-waiting-rest] at r0)
  (apply (hk-all-cs hxm (:comps w) (tbl-upd comp-id (:id c) comp-react-row (:comps w)) (:edges w) _ _ r0))
  (intros d hd) (rw [(tbl-has-upd CompRow comp-id (:id c) d comp-react-row comp-react-row-id (:comps w))]) (exact hd)
  (intros d hx hd)
  (cases hcd (Nat.beq (:id c) d))
  (exact (hk-wif-pend-ne d (:id c) comp-react-row comp-react-row-id (:comps w) hcd hd))
  (have z := (tbl-all-mem CompRow (hk-wif d) c (:comps w) hd hm))
  (simp only [hk-wif hcd waiting-strongly hi Bool.not_true Bool.false_or Bool.false_and] at z) (cases z)
  (exact (marks-waiting-intro hxm _ (well-formed-comp-upd w (:id c) comp-react-row comp-react-row-id comp-react-row-pending (marks-waiting-well-formed hxm w h)) r)))
(tree/restate! HMK '[well-formed-react-edges])
(a/theorem marks-waiting-react-one [hxm :- (List Nat), w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) true) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (react-one w c)) true))
  (intros hm hi h)
  (simp only [react-one])
  (exact (marks-waiting-react-edges hxm (:validity c) (comp-upd w (:id c) comp-react-row) (:id c) (marks-waiting-comp-react hxm w c hm hi h))))
(a/theorem marks-waiting-react-loop [hxm :- (List Nat), fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)] (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (react-loop fuel w q)) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w q hw) (simp only [react-loop]) (exact hw)
  (intros w q hw)
  (cases q)
  (simp only [react-loop]) (exact hw)
  (rename_i x t)
  (cases hc (comp-find w x))
  (simp only [react-loop hc]) (exact (ih w t hw))
  (rename_i c)
  (cases hi (:idle c))
  (simp only [react-loop hc hi]) (exact (ih w t hw))
  (simp only [react-loop hc hi])
  (exact (ih _ _ (marks-waiting-react-one hxm w c (tbl-find-mem CompRow comp-id x c (:comps w) hc) hi hw))))

;; ---- Rule R's detach: a detached source is no computation
(tree/restate! HMK '[well-formed-wake-closed well-formed-source-upd])
(tree/restate! HMK '[well-formed-nat-fold well-formed-detach-comp well-formed-detach-task well-formed-detach-source])
(a/theorem marks-waiting-detach [hxm :- (List Nat), w :- World]
  (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (detach w)) true))
  (intro h)
  (have n0 := (hk-sources-noc w (source-orphan w) (marks-waiting-well-formed hxm w h)))
  (have h1 := (marks-waiting-fold-noc hxm detach-source (fn [w2 :- World, x2 :- Nat, hx :- (= (tbl-has comp-id x2 (:comps w2)) false), h2 :- (= (marks-waiting hxm w2) true)]
                                                (marks-waiting-detach-source hxm w2 x2 hx h2))
                hk-has-detach-source (tbl-scan source-id (source-orphan w) (:sources w)) w n0 h))
  (simp only [detach])
  (exact (marks-waiting-nat-fold hxm detach-comp (marks-waiting-detach-comp hxm) (tbl-scan comp-id (comp-orphan w) (:comps w)) _
           (marks-waiting-nat-fold hxm detach-task (marks-waiting-detach-task hxm) (tbl-scan task-id (task-orphan w) (:tasks w)) _ h1))))

;; ===========================================================================
;; Part E. T11: the dispatched computation C is strong (done-epoch < epoch) from the needs-run
;; guard and gd's dle; watch bundle done-epoch-below c (rows with id c keep done-epoch < epoch: every comp-facts-cmono
;; edit keeps it) through the predecessor's cancel; the entry edge keeps its debtor (p3's edge-debtor-kept)
;; ===========================================================================

(a/defn done-epoch-below-one [hsc :- Nat, k :- GDK] Bool (Bool.or (Bool.not (Nat.beq (:id k) hsc)) (Nat.blt (:done k) (:epoch k))))
(a/defn done-epoch-below-rest [hsc :- Nat, w :- World] Bool (tbl-all (done-epoch-below-one hsc) (gdkeys (:comps w))))
(a/defn done-epoch-below [hsc :- Nat, w :- World] Bool (Bool.and (well-formed w) (done-epoch-below-rest hsc w)))
(a/theorem done-epoch-below-well-formed [hsc :- Nat, w :- World] (=> (= (done-epoch-below hsc w) true) (= (well-formed w) true))
  (intro h) (simp only [done-epoch-below Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem done-epoch-below-rest-of [hsc :- Nat, w :- World] (=> (= (done-epoch-below hsc w) true) (= (done-epoch-below-rest hsc w) true))
  (intro h) (simp only [done-epoch-below Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem done-epoch-below-intro [hsc :- Nat, w :- World] (=> (= (well-formed w) true) (= (done-epoch-below-rest hsc w) true) (= (done-epoch-below hsc w) true))
  (intros h1 h2) (simp only [done-epoch-below h1 h2 Bool.and_self]))
(a/theorem done-epoch-below-parts [hsc :- Nat, w :- World]
  (=> (= (done-epoch-below hsc w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (done-epoch-below-well-formed hsc w h))))
(a/theorem done-epoch-below-rest-same [hsc :- Nat, w :- World, w2 :- World]
  (=> (= (gdkeys (:comps w2)) (gdkeys (:comps w))) (= (done-epoch-below-rest hsc w) true) (= (done-epoch-below-rest hsc w2) true))
  (intros e h) (simp only [done-epoch-below-rest e]) (simp only [done-epoch-below-rest] at h) (exact h))
(a/theorem done-epoch-below-one-mono [hsc :- Nat, k :- GDK, d :- GDK]
  (=> (= (comp-facts-cmono k d) true) (= (done-epoch-below-one hsc k) true) (= (done-epoch-below-one hsc d) true))
  (intros hm h)
  (simp only [comp-facts-cmono Bool.and_eq_true Bool.or_eq_true] at hm)
  (have hid := (Nat.eq_of_beq_eq_true (And.left hm)))
  (have hep := (comp-facts-le-of _ _ (And.left (And.right (And.right hm)))))
  (have hd := (And.right (And.right (And.right hm))))
  (simp only [done-epoch-below-one hid]) (simp only [done-epoch-below-one Bool.or_eq_true] at h)
  (cases h)
  (rename_i a1) (simp only [a1 Bool.true_or])
  (rename_i a1)
  (have q1 := (comp-facts-lt-of _ _ a1))
  (have r1 (= (Nat.blt (:done d) (:epoch d)) true))
  (cases hd)
  (rename_i z) (rw [(Nat.eq_of_beq_eq_true z)]) (exact (comp-facts-blt-of _ _ (Nat.lt_of_lt_of_le q1 hep)))
  (rename_i z) (rw [(Nat.eq_of_beq_eq_true z)]) (apply comp-facts-blt-of) (omega)
  (simp only [r1 Bool.or_true]))
(a/theorem done-epoch-below-comp-upd [hsc :- Nat, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hk :- (forall [c :- CompRow] (= (gdkey (f c)) (gdkey c)))]
  (=> (= (done-epoch-below hsc w) true) (= (done-epoch-below hsc (comp-upd w x f)) true))
  (intro h)
  (exact (done-epoch-below-intro hsc _ (well-formed-comp-upd w x f hid hp (done-epoch-below-well-formed hsc w h))
           (done-epoch-below-rest-same hsc w (comp-upd w x f) (gdkeys-upd x f hk (:comps w)) (done-epoch-below-rest-of hsc w h)))))
(a/theorem done-epoch-below-comp-upd-m [hsc :- Nat, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                          hm :- (forall [c :- CompRow] (= (comp-facts-cmono (gdkey c) (gdkey (f c))) true))]
  (=> (= (done-epoch-below hsc w) true) (= (done-epoch-below hsc (comp-upd w x f)) true))
  (intro h)
  (have q := (done-epoch-below-rest-of hsc w h))
  (have r2 (= (done-epoch-below-rest hsc (comp-upd w x f)) true))
  (simp only [done-epoch-below-rest comp-upd set-comps]) (simp only [done-epoch-below-rest] at q)
  (rw [all-gdkeys] at q) (rw [all-gdkeys])
  (exact (tbl-all-upd CompRow comp-id x f (fn [c :- CompRow] (done-epoch-below-one hsc (gdkey c))) (fn [c :- CompRow] (done-epoch-below-one hsc (gdkey c)))
           (fn [c :- CompRow, h1 :- (= (done-epoch-below-one hsc (gdkey c)) true), h2 :- (= (Nat.beq (comp-id c) x) true)]
             (done-epoch-below-one-mono hsc (gdkey c) (gdkey (f c)) (hm c) h1))
           (fn [c :- CompRow, h1 :- (= (done-epoch-below-one hsc (gdkey c)) true), h2 :- (= (Nat.beq (comp-id c) x) false)] h1)
           (:comps w) q))
  (exact (done-epoch-below-intro hsc _ (well-formed-comp-upd w x f hid hp (done-epoch-below-well-formed hsc w h)) r2)))
(a/theorem hswr-mark-edge [hsc :- Nat, w :- World, x :- Nat] (=> (= (done-epoch-below-rest hsc w) true) (= (done-epoch-below-rest hsc (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (simp only [mark-edge hf]) (exact h)
  (rename_i e)
  (cases hm (:marked e))
  (simp only [mark-edge hf hm])
  (exact (done-epoch-below-rest-same hsc w (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending)
           (gdkeys-upd (:creditor e) comp-inc-pending comp-facts-key-inc-pending (:comps w)) h))
  (simp only [mark-edge hf hm]) (exact h))
(a/theorem hswr-unmark-edge [hsc :- Nat, w :- World, x :- Nat] (=> (= (done-epoch-below-rest hsc w) true) (= (done-epoch-below-rest hsc (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (simp only [unmark-edge hf]) (exact h)
  (rename_i e)
  (cases hm (:marked e))
  (simp only [unmark-edge hf hm]) (exact h)
  (simp only [unmark-edge hf hm])
  (exact (done-epoch-below-rest-same hsc w (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending)
           (gdkeys-upd (:creditor e) comp-dec-pending comp-facts-key-dec-pending (:comps w)) h)))
(a/theorem hswr-remove-edge [hsc :- Nat, w :- World, x :- Nat] (=> (= (done-epoch-below-rest hsc w) true) (= (done-epoch-below-rest hsc (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (simp only [remove-edge hf]) (exact h)
  (rename_i e)
  (cases hm (:marked e))
  (simp only [remove-edge hf hm]) (exact (done-epoch-below-rest-same hsc w (edge-del w x) (rfl) h))
  (simp only [remove-edge hf hm])
  (exact (done-epoch-below-rest-same hsc w (comp-upd (edge-del w x) (:creditor e) comp-dec-pending)
           (gdkeys-upd (:creditor e) comp-dec-pending comp-facts-key-dec-pending (:comps w)) h)))
(a/theorem hswr-drop-cred [hsc :- Nat, w :- World, a :- Nat] (=> (= (done-epoch-below-rest hsc w) true) (= (done-epoch-below-rest hsc (drop-cred-edges w a)) true))
  (intro h) (simp only [drop-cred-edges])
  (exact (done-epoch-below-rest-same hsc w (comp-upd (set-edges w (tbl-filter (cred-ne a) (:edges w))) a (comp-set-pending 0))
           (gdkeys-upd a (comp-set-pending 0) (comp-facts-key-set-pending 0) (:comps w)) h)))
(a/theorem hswr-drop-act [hsc :- Nat, w :- World, a :- Nat] (=> (= (done-epoch-below-rest hsc w) true) (= (done-epoch-below-rest hsc (drop-act w a)) true))
  (intro h) (simp only [drop-act])
  (exact (done-epoch-below-rest-same hsc (drop-cred-edges w a) (act-del (drop-cred-edges w a) a) (rfl) (hswr-drop-cred hsc w a h))))
(a/theorem hswr-drop-edges [hsc :- Nat, w :- World, p :- (=> EdgeRow Bool)] (=> (= (done-epoch-below-rest hsc w) true) (= (done-epoch-below-rest hsc (drop-edges w p)) true))
  (intro h) (simp only [drop-edges])
  (exact (done-epoch-below-rest-same hsc w (set-comps (set-edges w (tbl-filter p (:edges w))) (comps-resync (tbl-filter p (:edges w)) (:comps w)))
           (gdkeys-resync (tbl-filter p (:edges w)) (:comps w)) h)))
(a/theorem hswr-comp-del [hsc :- Nat, w :- World, x :- Nat] (=> (= (done-epoch-below-rest hsc w) true) (= (done-epoch-below-rest hsc (comp-del w x)) true))
  (intro h) (simp only [done-epoch-below-rest comp-del set-comps gdkeys-del]) (simp only [done-epoch-below-rest] at h)
  (exact (tbl-all-del GDK gdk-id x (done-epoch-below-one hsc) (done-epoch-below-one hsc) (fn [k :- GDK, h1 :- (= (done-epoch-below-one hsc k) true), h2 :- (= (Nat.beq (gdk-id k) x) false)] h1) _ h)))
(a/theorem hswr-filter-world [hsc :- Nat, w :- World, K :- (=> Nat Bool)] (=> (= (done-epoch-below-rest hsc w) true) (= (done-epoch-below-rest hsc (filter-world K w)) true))
  (intro h) (simp only [done-epoch-below-rest filter-world gdkeys-keep]) (simp only [done-epoch-below-rest] at h)
  (exact (tbl-all-keep GDK K gdk-id (done-epoch-below-one hsc) (done-epoch-below-one hsc) (fn [k :- GDK, h1 :- (= (done-epoch-below-one hsc k) true), h2 :- (= (K (gdk-id k)) true)] h1) _ h)))
(a/theorem hswr-insert-edge-checked [hsc :- Nat, w :- World, e :- EdgeRow]
  (=> (= (done-epoch-below-rest hsc w) true) (= (done-epoch-below-rest hsc (insert-edge-checked w e)) true))
  (intro h)
  (cases hk (edge-ok-in w e))
  (simp only [insert-edge-checked hk]) (exact h)
  (simp only [insert-edge-checked hk]) (exact h))

(def HSW (mk-bundle 'done-epoch-below '[hsc :- Nat] "done-epoch-below-" {}))
(swap! (:renames HSW) assoc 'well-formed-parts 'done-epoch-below-parts)
(doseq [o '[well-formed-scope-upd well-formed-pub-upd well-formed-source-upd well-formed-resource-upd well-formed-cleanup-upd well-formed-cleanup-del well-formed-set-pins
            well-formed-resource-del well-formed-scope-del well-formed-cleanup-ins well-formed-act-upd well-formed-task-upd well-formed-edge-upd well-formed-run-upd well-formed-run-del
            well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-resource-ins-fresh well-formed-scope-ins-fresh well-formed-act-ins-fresh well-formed-task-ins-fresh well-formed-run-ins-fresh
            well-formed-bump well-formed-insert-edge-fresh well-formed-fork-del]]
  (prim! HSW o nil))
(prim! HSW 'well-formed-insert-edge-checked '(hswr-insert-edge-checked hsc w e R))
(prim! HSW 'well-formed-remove-edge '(hswr-remove-edge hsc w x R))
(prim! HSW 'well-formed-mark-edge '(hswr-mark-edge hsc w x R))
(prim! HSW 'well-formed-unmark-edge '(hswr-unmark-edge hsc w x R))
(prim! HSW 'well-formed-drop-cred-edges '(hswr-drop-cred hsc w a R))
(prim! HSW 'well-formed-drop-act '(hswr-drop-act hsc w a R))
(prim! HSW 'well-formed-drop-edges '(hswr-drop-edges hsc w p R))
(prim! HSW 'well-formed-comp-del-unref '(hswr-comp-del hsc w x R))
(prim! HSW 'well-formed-filter-world '(hswr-filter-world hsc w K R))
(def ^:private hk-gd-cm '#{comp-inc-epoch comp-demand-row comp-replace-row comp-make-idle comp-demote-row comp-clear-run})
;; done-epoch-below on the generic tree: a computation edit keeps done-epoch-below by gd's key lemmas
(tree/part! HSW
  :sites (tree/row-sites 'well-formed-comp-upd (constantly true)
                         (fn [F] (if (contains? hk-gd-cm (hk-fhead F))
                                   (list 'done-epoch-below-comp-upd-m 'hsc 'w 'x F 'hid 'hp (hk-lapp F (symbol (str (hk-fhead F) "-gcm"))) 'h0)
                                   (list 'done-epoch-below-comp-upd 'hsc 'w 'x F 'hid 'hp '(fn [c :- CompRow] (Eq.refl (gdkey c))) 'h0)))))
(tree/restate! HSW '[well-formed-cancel-pred])

(a/theorem done-epoch-below-sif [hsc :- Nat, w :- World] (=> (= (done-epoch-below-rest hsc w) true) (= (tbl-all (hk-sif hsc) (:comps w)) true))
  (intro h)
  (simp only [done-epoch-below-rest] at h) (rw [all-gdkeys] at h)
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) h))
  (intros c hc)
  (simp only [done-epoch-below-one gdkey Bool.or_eq_true] at hc)
  (cases hc)
  (rename_i z) (simp only [hk-sif z Bool.true_or])
  (rename_i z) (simp only [hk-sif hk-strong z Bool.or_true]))
(a/theorem done-epoch-below-start [w :- World, c :- CompRow]
  (=> (= (comp-facts w) true) (List.Mem c (:comps w)) (= (Nat.beq (:done-epoch c) (:epoch c)) false) (= (done-epoch-below (:id c) w) true))
  (intros h hm hd)
  (have hs := (comp-facts-well-formed w h))
  (have p := (gdk-parts _ _ _ (comp-facts-rest-of w h)))
  (have q := (And.right p)) (rw [all-gdkeys] at q)
  (have hc0 := (tbl-all-mem CompRow (fn [x :- CompRow] (comp-facts-c (:runs w) (:next-id w) (gdkey x))) c (:comps w) q hm))
  (have dl := (And.left (comp-facts-c-parts _ _ _ hc0))) (simp only [comp-facts-dle gdkey Bool.and_eq_true] at dl)
  (have l1 := (comp-facts-le-of _ _ (And.left dl)))
  (have ne (Not (= (:done-epoch c) (:epoch c))))
  (intro eq) (rw [eq] at hd) (rw [Nat.beq_refl] at hd) (cases hd)
  (have qc (= (done-epoch-below-one (:id c) (gdkey c)) true))
  (simp only [done-epoch-below-one gdkey]) (apply (Eq.trans (congrArg (fn [b :- Bool] (Bool.or (Bool.not (Nat.beq (:id c) (:id c))) b)) (comp-facts-blt-of _ _ (Nat.lt_of_le_of_ne l1 ne)))))
  (simp only [Bool.or_true])
  (have u := (comp-facts-same-id w c (fn [x :- CompRow] (done-epoch-below-one (:id c) (gdkey x))) hs hm qc))
  (have r (= (done-epoch-below-rest (:id c) w) true))
  (simp only [done-epoch-below-rest])
  (rw [all-gdkeys])
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) u))
  (intros x hx)
  (cases hi (Nat.beq (comp-id x) (:id c)))
  (have hi2 (= (Nat.beq (:id x) (:id c)) false)) (exact hi) (simp only [done-epoch-below-one gdkey hi2 Bool.not_false Bool.true_or])
  (simp only [same-id-then hi Bool.not_true Bool.false_or] at hx) (exact hx)
  (exact (done-epoch-below-intro _ w hs r)))

(a/theorem hk-dok-cut [hxm :- (List Nat), cs :- (List CompRow), c :- Nat, has :- Bool, cid :- Nat, r :- EdgeRow]
  (=> (= (tbl-all (hk-sif c) cs) true) (= (hk-dok hxm cs (keep-prefix c has cid) r) true))
  (intro hs)
  (cases hk0 (keep-prefix c has cid r))
  (have hk1 := hk0) (simp only [keep-prefix] at hk1)
  (have s1 := (bnot-false _ hk1))
  (simp only [suffix-edge dep-of Bool.and_eq_true] at s1)
  (have ec := (Nat.eq_of_beq_eq_true (And.right (And.left s1))))
  (simp only [hk-dok hk0 hk-safe ec hs Bool.or_true Bool.false_or])
  (simp only [hk-dok hk0 Bool.true_or]))
(tree/restate! HMK '[well-formed-drop-edges])
(a/theorem marks-waiting-cut-suffix [hxm :- (List Nat), w :- World, c :- Nat, has :- Bool, cut :- Nat, cid :- Nat]
  (=> (= (tbl-all (hk-sif c) (:comps w)) true) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (cut-suffix w c has cut cid)) true))
  (intros hs h)
  (have p := (all-of-mem EdgeRow (hk-dok hxm (:comps w) (keep-prefix c has cid)) (:edges w)
               (fn [r :- EdgeRow, m :- (List.Mem r (:edges w))] (hk-dok-cut hxm (:comps w) c has cid r hs))))
  (have h1 := (marks-waiting-drop-edges hxm w (keep-prefix c has cid) p h))
  (simp only [cut-suffix])
  (exact (marks-waiting-comp-upd-m hxm (drop-edges w (keep-prefix c has cid)) c
           (comp-cut-row has cut (bases-of (tbl-filter (suffix-edge c has cid) (:edges w))))
           (comp-cut-row-id has cut _) (comp-cut-row-pending has cut _)
           (fn [q :- CompRow, hq :- (= (waiting-strongly q) true)] hq) h1)))
(a/theorem hk-edge-debtor-kept-found [kxy :- Nat, kxd :- Nat, w :- World, e2 :- EdgeRow]
  (=> (= (edge-debtor-kept-rest kxy kxd w) true) (= (edge-find w kxy) (Option.some EdgeRow e2)) (= (:debtor e2) kxd))
  (intros h hf)
  (simp only [edge-debtor-kept-rest Bool.and_eq_true] at h)
  (have m := (tbl-find-mem EdgeRow edge-id kxy e2 (:edges w) hf))
  (have i := (tbl-find-id EdgeRow edge-id kxy e2 (:edges w) hf))
  (have z := (tbl-all-mem EdgeRow (deb-at kxy kxd) e2 (:edges w) (And.right h) m))
  (have i2 (= (Nat.beq (:id e2) kxy) true)) (simp only [Nat.beq_eq]) (exact i)
  (simp only [deb-at i2 Bool.not_true Bool.false_or] at z)
  (exact (Nat.eq_of_beq_eq_true z)))
(a/theorem hk-u-edge-debtor-kept [hxm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (marks-waiting hxm w) true) (= (edge-debtor-kept-rest (:id e) (:debtor e) w) true) (= (deb-final w (:debtor e)) true)
      (forall [e2 :- EdgeRow] (=> (= (edge-find w (:id e)) (Option.some EdgeRow e2)) (= (:marked e2) true) (= (hk-safe hxm (:comps w) (:creditor e2)) true))))
  (intros h k hf)
  (have nc := (hk-final-not-comp w (:debtor e) (marks-waiting-well-formed hxm w h) hf))
  (apply (hk-u-of-unm hxm w (:id e)))
  (intros e2 hf2)
  (have dd := (hk-edge-debtor-kept-found (:id e) (:debtor e) w e2 k hf2))
  (have nc2 (= (tbl-has comp-id (:debtor e2) (:comps w)) false)) (rw [dd]) (exact nc)
  (exact (hk-found-noncomp hxm w (:id e) e2 (marks-waiting-rest-of hxm w h) hf2 nc2)))
(tree/restate! HMK '[well-formed-edge-upd well-formed-edge-set-phase])
(a/theorem marks-waiting-consume-entry [hxm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (edge-debtor-kept-rest (:id e) (:debtor e) w) true) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (consume-entry w e)) true))
  (intros k h)
  (cases hf (deb-final w (:debtor e)))
  (cases hr (Nat.beq (:cont e) cont-restart))
  (simp only [consume-entry hr hf])
  (exact (marks-waiting-edge-upd hxm w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
           (edge-rearm-edge-id _ _) (edge-rearm-kind _ _) (edge-rearm-creditor _ _) (edge-rearm-debtor _ _) (edge-rearm-marked _ _) h))
  (simp only [consume-entry hr hf])
  (exact (marks-waiting-edge-set-phase hxm w (:id e) ph-armed h))
  (simp only [consume-entry hf])
  (exact (marks-waiting-remove-edge hxm w (:id e) (hk-u-edge-debtor-kept hxm w e h k hf) h)))
(tree/restate! HMK '[well-formed-cancel-pred well-formed-new-run-of])
(a/theorem marks-waiting-dispatch-raw [hxm :- (List Nat), w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (Nat.beq (:done-epoch c) (:epoch c)) false) (= (comp-facts w) true) (= (marks-waiting hxm w) true)
      (= (marks-waiting hxm (dispatch-raw w c)) true))
  (intros hm hd hg h)
  (have s0 := (done-epoch-below-start w c hg hm hd))
  (have s1 := (done-epoch-below-sif (:id c) (cancel-pred w c) (done-epoch-below-rest-of _ _ (done-epoch-below-cancel-pred (:id c) w c s0))))
  (have h1 := (marks-waiting-cancel-pred hxm w c h))
  (cases he (entry-edge w (:id c)))
  (simp only [dispatch-raw he])
  (exact (marks-waiting-new-run-of hxm (cut-suffix (cancel-pred w c) (:id c) false 0 0) c 0
           (marks-waiting-cut-suffix hxm (cancel-pred w c) (:id c) false 0 0 s1 h1)))
  (rename_i e)
  (have k0 := (edge-debtor-kept-of-mem w e (comp-facts-well-formed w hg) (entry-mem w (:id c) e he)))
  (have k1 := (edge-debtor-kept-cut-suffix (:id e) (:debtor e) (cancel-pred w c) (:id c) true (:at e) (:id e)
                (edge-debtor-kept-cancel-pred (:id e) (:debtor e) w c k0)))
  (simp only [dispatch-raw he])
  (exact (marks-waiting-new-run-of hxm (consume-entry (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e) c (entry-ei e)
           (marks-waiting-consume-entry hxm (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e
             (edge-debtor-kept-rest-of _ _ _ k1)
             (marks-waiting-cut-suffix hxm (cancel-pred w c) (:id c) true (:at e) (:id e) s1 h1)))))
(a/theorem marks-waiting-t11-dispatch [hxm :- (List Nat), w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (comp-facts w) true) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (:world (t11-dispatch w cid fresh))) true))
  (intros hg h)
  (cases hc (comp-find w cid))
  (simp only [t11-dispatch hc refuse]) (exact h)
  (rename_i c)
  (cases hgg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))))
  (simp only [t11-dispatch hc hgg refuse]) (exact h)
  (have hg2 := hgg) (simp only [Bool.and_eq_true needs-run] at hg2)
  (have hd := (bnot-true _ (And.left (And.left (And.right (And.right hg2))))))
  (simp only [t11-dispatch hc hgg accept])
  (exact (marks-waiting-dispatch-raw hxm w c (tbl-find-mem CompRow comp-id cid c (:comps w) hc) hd hg h)))

;; ===========================================================================
;; Part F. The bundle gives h-mark
;; ===========================================================================

(a/theorem waiting-strongly-waiting [c :- CompRow] (=> (= (waiting-strongly c) true) (= (comp-waiting c) true))
  (intro h)
  (simp only [waiting-strongly Bool.and_eq_true Bool.or_eq_true] at h)
  (have i := (bnot-true _ (And.left h)))
  (have l (= (comp-live c) false))
  (have q := (And.right h))
  (cases q)
  (rename_i z)
  (have ne (= (Nat.beq (:done-epoch c) (:epoch c)) false))
  (cases hb (Nat.beq (:done-epoch c) (:epoch c))) (rfl)
  (have e := (Nat.eq_of_beq_eq_true hb)) (have z2 := (comp-facts-lt-of _ _ z)) (omega)
  (simp only [comp-live ne Bool.false_and Bool.and_false])
  (rename_i z)
  (have np := (bnot-true _ z))
  (simp only [comp-live np Bool.and_false])
  (simp only [comp-waiting i l Bool.not_false Bool.and_self]))
(a/theorem hk-mark-ok [w :- World, e :- EdgeRow]
  (=> (= (hk-e (List.nil Nat) (:comps w) e) true) (= (mark-ok w e) true))
  (intro h)
  (cases hm (:marked e))
  (simp only [mark-ok hm Bool.not_false Bool.true_or])
  (have p := (hk-e-marked (List.nil Nat) (:comps w) e h hm))
  (have q := (And.right (And.right p)))
  (have wa (= (tbl-all (hk-wif (:debtor e)) (:comps w)) true))
  (cases q) (rename_i z) (simp [reach-mem] at z) (rename_i z) (exact z)
  (cases hf (comp-find w (:debtor e)))
  (have z := (tbl-find-none-has CompRow comp-id (:debtor e) (:comps w) hf))
  (rw [(And.left (And.right p))] at z) (cases z)
  (rename_i c)
  (have m := (tbl-find-mem CompRow comp-id (:debtor e) c (:comps w) hf))
  (have i := (tbl-find-id CompRow comp-id (:debtor e) c (:comps w) hf))
  (have z := (tbl-all-mem CompRow (hk-wif (:debtor e)) c (:comps w) wa m))
  (have i2 (= (Nat.beq (:id c) (:debtor e)) true)) (simp only [Nat.beq_eq]) (exact i)
  (simp only [hk-wif i2 Bool.not_true Bool.false_or] at z)
  (simp only [mark-ok hm waiting-at hf (And.left p) (waiting-strongly-waiting c z) Bool.not_true Bool.false_or Bool.and_self]))
(a/theorem hk-h-mark [w :- World] (=> (= (marks-waiting (List.nil Nat) w) true) (= (h-mark w) true))
  (intro h)
  (have r := (marks-waiting-rest-of _ w h)) (simp only [marks-waiting-rest] at r)
  (simp only [h-mark])
  (exact (tbl-all-mono EdgeRow (hk-e (List.nil Nat) (:comps w)) (mark-ok w)
           (fn [e :- EdgeRow, he :- (= (hk-e (List.nil Nat) (:comps w) e) true)] (hk-mark-ok w e he)) (:edges w) r)))
(a/theorem marks-waiting-empty [] (= (marks-waiting (List.nil Nat) empty-world) true) (rfl))

;; ===========================================================================
;; Part G. The mark fold (T2, T3): at the end every target id is marked, the edge keys and the
;; computations' idle/epoch/done-epoch are kept, a marked creditor is waiting
;; ===========================================================================

(a/defn hk-jm [P :- (=> Nat Bool), r :- EdgeRow] Bool (Bool.or (Bool.not (P (:id r))) (:marked r)))
(a/defn hk-or-id [y :- Nat, P :- (=> Nat Bool), z :- Nat] Bool (Bool.or (Nat.beq z y) (P z)))
(a/defn hk-in [ts :- (List Nat), P :- (=> Nat Bool), z :- Nat] Bool (Bool.or (reach-mem z ts) (P z)))
(a/defn hk-none [z :- Nat] Bool false)

(a/theorem hk-jm-mono [P :- (=> Nat Bool), Q :- (=> Nat Bool), r :- EdgeRow]
  (=> (forall [z :- Nat] (=> (= (Q z) true) (= (P z) true))) (= (hk-jm P r) true) (= (hk-jm Q r) true))
  (intros hq h)
  (cases hm (:marked r))
  (simp only [hk-jm hm Bool.or_false] at h)
  (have p0 := (bnot-true _ h))
  (cases hq0 (Q (:id r)))
  (simp only [hk-jm hq0 hm Bool.not_false Bool.true_or])
  (have z := (hq (:id r) hq0)) (rw [p0] at z) (cases z)
  (simp only [hk-jm hm Bool.or_true]))
(a/theorem hk-jm-marked [P :- (=> Nat Bool), r :- EdgeRow] (= (hk-jm P (edge-set-marked true r)) true)
  (simp only [hk-jm edge-set-marked Bool.or_true]))
(a/theorem hk-jm-other [y :- Nat, P :- (=> Nat Bool), r :- EdgeRow]
  (=> (= (Nat.beq (:id r) y) false) (= (hk-jm P r) true) (= (hk-jm (hk-or-id y P) r) true))
  (intros hr hj) (simp only [hk-jm hk-or-id hr Bool.false_or]) (simp only [hk-jm] at hj) (exact hj))
(a/theorem hk-jm-same [y :- Nat, P :- (=> Nat Bool), i :- Nat, r :- EdgeRow]
  (=> (= i y) (= (same-id-then edge-id i (fn [q :- EdgeRow] (:marked q)) r) true) (= (hk-jm P r) true) (= (hk-jm (hk-or-id y P) r) true))
  (intros hi hs hj)
  (cases hr (Nat.beq (:id r) y))
  (exact (hk-jm-other y P r hr hj))
  (have hr2 (= (Nat.beq (edge-id r) i) true)) (rw [hi]) (exact hr)
  (simp only [same-id-then hr2 Bool.not_true Bool.false_or] at hs)
  (simp only [hk-jm hs Bool.or_true]))
(a/theorem hk-mark-J [w :- World, y :- Nat, P :- (=> Nat Bool)]
  (=> (= (well-formed w) true) (= (tbl-all (hk-jm P) (:edges w)) true) (= (tbl-all (hk-jm (hk-or-id y P)) (:edges (mark-edge w y))) true))
  (intros hs h)
  (cases hf (edge-find w y))
  (have nh := (has-false-ne EdgeRow edge-id y (:edges w) (tbl-find-none-has EdgeRow edge-id y (:edges w) hf)))
  (simp only [mark-edge hf])
  (exact (tbl-all-mono2 EdgeRow (fn [q :- EdgeRow] (Bool.not (Nat.beq (edge-id q) y))) (hk-jm P) (hk-jm (hk-or-id y P))
           (fn [r :- EdgeRow, h1 :- (= (Bool.not (Nat.beq (edge-id r) y)) true), h2 :- (= (hk-jm P r) true)] (hk-jm-other y P r (bnot-true _ h1) h2))
           (:edges w) nh h))
  (rename_i e0)
  (cases hm (:marked e0))
  (simp only [mark-edge hf hm edge-upd comp-upd set-comps set-edges])
  (exact (tbl-all-upd EdgeRow edge-id y (edge-set-marked true) (hk-jm P) (hk-jm (hk-or-id y P))
           (fn [r :- EdgeRow, h1 :- (= (hk-jm P r) true), h2 :- (= (Nat.beq (edge-id r) y) true)] (hk-jm-marked (hk-or-id y P) r))
           (fn [r :- EdgeRow, h1 :- (= (hk-jm P r) true), h2 :- (= (Nat.beq (edge-id r) y) false)] (hk-jm-other y P r h2 h1))
           (:edges w) h))
  (simp only [mark-edge hf hm])
  (have i := (tbl-find-id EdgeRow edge-id y e0 (:edges w) hf))
  (have u := (uniq-all EdgeRow edge-id (fn [q :- EdgeRow] (:marked q)) e0 (:edges w) (l5-edge-nodup w hs) (tbl-find-mem EdgeRow edge-id y e0 (:edges w) hf) hm))
  (exact (tbl-all-mono2 EdgeRow (same-id-then edge-id (edge-id e0) (fn [q :- EdgeRow] (:marked q))) (hk-jm P) (hk-jm (hk-or-id y P))
           (fn [r :- EdgeRow, h1 :- (= (same-id-then edge-id (edge-id e0) (fn [q :- EdgeRow] (:marked q)) r) true), h2 :- (= (hk-jm P r) true)]
             (hk-jm-same y P (edge-id e0) r i h1 h2))
           (:edges w) u h)))
(a/theorem hk-fold-J [ts :- (List Nat)]
  (forall [w :- World, P :- (=> Nat Bool)]
    (=> (= (well-formed w) true) (= (tbl-all (hk-jm P) (:edges w)) true)
        (= (tbl-all (hk-jm (hk-in ts P)) (:edges (nat-fold mark-edge w ts))) true)))
  (induction ts)
  (case' [cons y t ih])
  (case' [nil])
  (intros w P hs h)
  (simp only [nat-fold])
  (apply (tbl-all-mono EdgeRow (hk-jm P) (hk-jm (hk-in (List.nil Nat) P)) _ (:edges w) h))
  (intros r hr)
  (apply (hk-jm-mono P (hk-in (List.nil Nat) P) r _ hr))
  (intros z hz) (simp only [hk-in reach-mem Bool.false_or] at hz) (exact hz)
  (intros w P hs h)
  (simp only [nat-fold])
  (have r1 := (ih (mark-edge w y) (hk-or-id y P) (well-formed-mark-edge w y hs) (hk-mark-J w y P hs h)))
  (apply (tbl-all-mono EdgeRow (hk-jm (hk-in t (hk-or-id y P))) (hk-jm (hk-in (List.cons Nat y t) P)) _ _ r1))
  (intros r hr)
  (apply (hk-jm-mono (hk-in t (hk-or-id y P)) (hk-in (List.cons Nat y t) P) r _ hr))
  (intros z hz)
  (cases hzy (Nat.beq z y))
  (simp only [hk-in reach-mem hzy] at hz) (simp only [hk-in hk-or-id hzy Bool.false_or]) (exact hz)
  (simp only [hk-in hk-or-id hzy Bool.true_or Bool.or_true]))

;; a fact about the edges or the computations that every mark-edge keeps survives the fold
(a/theorem hk-fold-mark-q [Q :- (=> World Bool),
                           hq :- (forall [w :- World, y :- Nat] (=> (= (well-formed w) true) (= (Q w) true) (= (Q (mark-edge w y)) true))),
                           ts :- (List Nat)]
  (forall [w :- World] (=> (= (well-formed w) true) (= (Q w) true) (= (Q (nat-fold mark-edge w ts)) true)))
  (induction ts)
  (case' [cons y t ih])
  (case' [nil])
  (intros w hs h) (simp only [nat-fold]) (exact h)
  (intros w hs h) (simp only [nat-fold]) (exact (ih (mark-edge w y) (well-formed-mark-edge w y hs) (hq w y hs h))))
(a/theorem hk-any-mark [p :- (=> EdgeRow Bool), hp :- (forall [r :- EdgeRow] (=> (= (p r) true) (= (p (edge-set-marked true r)) true))),
                        w :- World, y :- Nat]
  (=> (= (tbl-any p (:edges w)) true) (= (tbl-any p (:edges (mark-edge w y))) true))
  (intro h)
  (cases hf (edge-find w y))
  (simp only [mark-edge hf]) (exact h)
  (rename_i e0)
  (cases hm (:marked e0))
  (simp only [mark-edge hf hm edge-upd comp-upd set-comps set-edges])
  (exact (any-upd-mono EdgeRow edge-id y (edge-set-marked true) p hp (:edges w) h))
  (simp only [mark-edge hf hm]) (exact h))
(a/theorem hk-cs-mark [R :- (=> CompRow Bool), hR :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-inc-pending c)) true))),
                       w :- World, y :- Nat]
  (=> (= (tbl-all R (:comps w)) true) (= (tbl-all R (:comps (mark-edge w y))) true))
  (intro h)
  (cases hf (edge-find w y))
  (simp only [mark-edge hf]) (exact h)
  (rename_i e0)
  (cases hm (:marked e0))
  (simp only [mark-edge hf hm edge-upd comp-upd set-comps set-edges])
  (exact (tbl-all-upd CompRow comp-id (:creditor e0) comp-inc-pending R R
           (fn [c :- CompRow, h1 :- (= (R c) true), h2 :- (= (Nat.beq (comp-id c) (:creditor e0)) true)] (hR c h1))
           (fn [c :- CompRow, h1 :- (= (R c) true), h2 :- (= (Nat.beq (comp-id c) (:creditor e0)) false)] h1) (:comps w) h))
  (simp only [mark-edge hf hm]) (exact h))

;; a creditor with a marked in-edge, awake, is waiting
(a/theorem hk-beq-succ [n :- Nat] (= (Nat.beq (+ n 1) 0) false)
  (cases hb (Nat.beq (+ n 1) 0)) (rfl) (have e := (Nat.eq_of_beq_eq_true hb)) (omega))
(a/theorem hk-count-pos [A :- Type, p :- (=> A Bool), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (Nat.beq (tbl-count p xs) 0) false))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hx) (simp [tbl-any] at hx)
  (intro hx)
  (cases hp (p h))
  (simp only [tbl-any hp Bool.false_or] at hx) (simp only [tbl-count hp (ih hx)])
  (simp only [tbl-count hp hk-beq-succ]))
(a/theorem hk-wif-marks [w :- World, d :- Nat]
  (=> (= (pending-exact w) true) (= (awake (:comps w) d) true) (= (tbl-any (marks d) (:edges w)) true)
      (= (tbl-all (hk-wif d) (:comps w)) true))
  (intros hp ha hm)
  (simp only [pending-exact pending-exact-in] at hp) (simp only [awake] at ha)
  (have cp := (hk-count-pos EdgeRow (marks d) (:edges w) hm))
  (apply (tbl-all-mono2 CompRow (comp-exact (:edges w)) (not-idle-if-id d) (hk-wif d) _ (:comps w) hp ha))
  (intros r h1 h2)
  (cases hd (Nat.beq (:id r) d))
  (simp only [hk-wif hd Bool.not_false Bool.true_or])
  (simp only [not-idle-if-id hd Bool.not_true Bool.false_or] at h2)
  (simp only [comp-exact Nat.beq_eq] at h1)
  (have e := (Nat.eq_of_beq_eq_true hd))
  (have pz (= (Nat.beq (:pending r) 0) false)) (rw [h1]) (simp only [marked-in]) (rw [e]) (exact cp)
  (simp only [hk-wif hd waiting-strongly h2 pz Bool.not_true Bool.false_or Bool.not_false Bool.or_true Bool.true_and]))

;; ---- dep creditors and mark targets as rows
(a/defn hk-dcr [d :- Nat, m :- Nat, r :- EdgeRow] Bool
  (Bool.and (Nat.beq (:kind r) ek-dep) (Bool.and (Nat.beq (:creditor r) d) (Nat.beq (:debtor r) m))))
(a/theorem hk-dc-any [d :- Nat, m :- Nat, es :- (List EdgeRow)]
  (=> (= (reach-mem d (dep-creditors es m)) true) (= (tbl-any (hk-dcr d m) es) true))
  (induction es)
  (case' [cons h t ih])
  (case' [nil])
  (intro hx) (simp [dep-creditors reach-mem] at hx)
  (intro hx)
  (cases hc (Bool.and (Nat.beq (:debtor h) m) (Nat.beq (:kind h) ek-dep)))
  (simp only [dep-creditors hc] at hx) (simp only [tbl-any (ih hx) Bool.or_true])
  (simp only [dep-creditors hc reach-mem] at hx)
  (cases hd (Nat.beq d (:creditor h)))
  (simp only [hd] at hx) (simp only [tbl-any (ih hx) Bool.or_true])
  (simp only [Bool.and_eq_true] at hc)
  (have hd2 (= (Nat.beq (:creditor h) d) true)) (rw [beq-comm]) (exact hd)
  (simp only [tbl-any hk-dcr (And.left hc) (And.right hc) hd2 Bool.and_self Bool.true_or]))
(a/defn hk-tq [S :- (List Nat), y :- Nat, r :- EdgeRow] Bool
  (Bool.and (Nat.beq (:id r) y) (Bool.and (Nat.beq (:kind r) ek-dep) (reach-mem (:debtor r) S))))
(a/theorem hk-mt-any [S :- (List Nat), y :- Nat, es :- (List EdgeRow)]
  (=> (= (reach-mem y (mark-targets S es)) true) (= (tbl-any (hk-tq S y) es) true))
  (induction es)
  (case' [cons h t ih])
  (case' [nil])
  (intro hx) (simp [mark-targets reach-mem] at hx)
  (intro hx)
  (cases hc (Bool.and (Nat.beq (:kind h) ek-dep) (reach-mem (:debtor h) S)))
  (simp only [mark-targets hc] at hx) (simp only [tbl-any (ih hx) Bool.or_true])
  (simp only [mark-targets hc reach-mem] at hx)
  (cases hd (Nat.beq y (:id h)))
  (simp only [hd] at hx) (simp only [tbl-any (ih hx) Bool.or_true])
  (have hd2 (= (Nat.beq (:id h) y) true)) (rw [beq-comm]) (exact hd)
  (simp only [tbl-any hk-tq hd2 hc Bool.and_self Bool.true_or]))
(a/theorem hk-rm-cons [z :- Nat, x :- Nat, t :- (List Nat)] (=> (= (reach-mem z t) true) (= (reach-mem z (List.cons Nat x t)) true))
  (intro h) (cases hb (Nat.beq z x)) (simp only [reach-mem hb h]) (simp only [reach-mem hb]))
(a/theorem hk-tgt-mem [S :- (List Nat), es :- (List EdgeRow), r :- EdgeRow]
  (=> (List.Mem r es) (= (Nat.beq (:kind r) ek-dep) true) (= (reach-mem (:debtor r) S) true) (= (reach-mem (:id r) (mark-targets S es)) true))
  (induction es)
  (case [nil] (intros m hk0 hs) (cases m))
  (case [cons h t ih]
    (intros m hk0 hs)
    (cases m)
    (case [head] (simp only [mark-targets hk0 hs Bool.and_self reach-mem Nat.beq_refl]))
    (case [tail m2]
      (have z := (ih m2 hk0 hs))
      (cases hc (Bool.and (Nat.beq (:kind h) ek-dep) (reach-mem (:debtor h) S)))
      (case [false] (simp only [mark-targets hc]) (exact z))
      (case [true] (simp only [mark-targets hc]) (exact (hk-rm-cons (:id r) (:id h) _ z))))))
(a/defn hk-memof [xs :- (List Nat), y :- Nat] Bool (reach-mem y xs))
(a/theorem hk-all-self [xs :- (List Nat)] (= (tbl-all (hk-memof xs) xs) true)
  (induction xs)
  (case [nil] (simp only [tbl-all]))
  (case [cons h t ih]
    (simp only [tbl-all hk-memof reach-mem Nat.beq_refl Bool.true_and])
    (apply (tbl-all-mono Nat (hk-memof t) (hk-memof (List.cons Nat h t)) _ t ih))
    (intros y hy) (simp only [hk-memof reach-mem hy]) (simp only [hk-memof] at hy) (cases hb (Nat.beq y h)) (exact hy) (rfl)))

;; ---- the exemption fold: the targets' debtors are exempt while they are marked
(a/defn hk-tg [hxm :- (List Nat), T :- (List Nat), cs :- (List CompRow), r :- EdgeRow] Bool
  (Bool.or (Bool.not (reach-mem (:id r) T)) (hk-e hxm cs (edge-set-marked true r))))
(a/theorem hk-tg-mono [hxm :- (List Nat), T :- (List Nat), cs :- (List CompRow), cs2 :- (List CompRow), r :- EdgeRow]
  (=> (forall [d :- Nat] (=> (= (tbl-has comp-id d cs) true) (= (tbl-has comp-id d cs2) true)))
      (forall [d :- Nat] (=> (= (reach-mem d hxm) false) (= (tbl-all (hk-wif d) cs) true) (= (tbl-all (hk-wif d) cs2) true)))
      (= (hk-tg hxm T cs r) true) (= (hk-tg hxm T cs2 r) true))
  (intros hh hw h)
  (cases ht (reach-mem (:id r) T))
  (simp only [hk-tg ht Bool.not_false Bool.true_or])
  (simp only [hk-tg ht Bool.not_true Bool.false_or] at h)
  (simp only [hk-tg ht Bool.not_true Bool.false_or])
  (exact (hk-e-cs hxm cs cs2 _ hh hw h)))
(a/theorem hk-tg-mark [hxm :- (List Nat), T :- (List Nat), w :- World, y :- Nat]
  (=> (= (tbl-all (hk-tg hxm T (:comps w)) (:edges w)) true) (= (tbl-all (hk-tg hxm T (:comps (mark-edge w y))) (:edges (mark-edge w y))) true))
  (intro h)
  (cases hf (edge-find w y))
  (simp only [mark-edge hf]) (exact h)
  (rename_i e0)
  (cases hm (:marked e0))
  (simp only [mark-edge hf hm edge-upd comp-upd set-comps set-edges])
  (have hh (forall [d :- Nat] (=> (= (tbl-has comp-id d (:comps w)) true) (= (tbl-has comp-id d (tbl-upd comp-id (:creditor e0) comp-inc-pending (:comps w))) true))))
  (intros d hd) (exact (Eq.trans (tbl-has-upd CompRow comp-id (:creditor e0) d comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) (:comps w)) hd))
  (have hw (forall [d :- Nat] (=> (= (reach-mem d hxm) false) (= (tbl-all (hk-wif d) (:comps w)) true)
                                 (= (tbl-all (hk-wif d) (tbl-upd comp-id (:creditor e0) comp-inc-pending (:comps w))) true))))
  (intros d hx hd) (exact (hk-wif-upd d (:creditor e0) comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) waiting-strongly-inc (:comps w) hd))
  (apply (tbl-all-upd EdgeRow edge-id y (edge-set-marked true) (hk-tg hxm T (:comps w)) (hk-tg hxm T (tbl-upd comp-id (:creditor e0) comp-inc-pending (:comps w))) _ _ (:edges w) h))
  (intros r hr hx)
  (have hr2 (= (hk-tg hxm T (:comps w) (edge-set-marked true r)) true))
  (simp only [hk-tg edge-set-marked]) (simp only [hk-tg edge-set-marked] at hr) (exact hr)
  (exact (hk-tg-mono hxm T (:comps w) _ (edge-set-marked true r) hh hw hr2))
  (intros r hr hx) (exact (hk-tg-mono hxm T (:comps w) _ r hh hw hr))
  (simp only [mark-edge hf hm]) (exact h))
(a/theorem hk-mok-of-tg [hxm :- (List Nat), T :- (List Nat), cs :- (List CompRow), y :- Nat, r :- EdgeRow]
  (=> (= (reach-mem y T) true) (= (hk-tg hxm T cs r) true) (= (hk-mok hxm cs y r) true))
  (intros hy h)
  (cases hr (Nat.beq (:id r) y))
  (simp only [hk-mok hr Bool.not_false Bool.true_or])
  (have e := (Nat.eq_of_beq_eq_true hr))
  (have t2 (= (reach-mem (:id r) T) true)) (rw [e]) (exact hy)
  (simp only [hk-tg t2 Bool.not_true Bool.false_or] at h)
  (simp only [hk-mok hr Bool.not_true Bool.false_or]) (exact h))
(a/theorem marks-waiting-fold-mark-x [hxm :- (List Nat), T :- (List Nat), ts :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (hk-memof T) ts) true) (= (tbl-all (hk-tg hxm T (:comps w)) (:edges w)) true)
                           (= (marks-waiting hxm w) true) (= (marks-waiting hxm (nat-fold mark-edge w ts)) true)))
  (induction ts)
  (case' [cons y t ih])
  (case' [nil])
  (intros w hm ht h) (simp only [nat-fold]) (exact h)
  (intros w hm ht h)
  (simp only [tbl-all Bool.and_eq_true] at hm)
  (have hy := (And.left hm)) (simp only [hk-memof] at hy)
  (have mok := (tbl-all-mono EdgeRow (hk-tg hxm T (:comps w)) (hk-mok hxm (:comps w) y)
                 (fn [r :- EdgeRow, hr :- (= (hk-tg hxm T (:comps w) r) true)] (hk-mok-of-tg hxm T (:comps w) y r hy hr)) (:edges w) ht))
  (simp only [nat-fold])
  (exact (ih (mark-edge w y) (And.right hm) (hk-tg-mark hxm T w y ht) (marks-waiting-mark-edge hxm w y mok h))))
(a/theorem marks-waiting-discharge [hxm :- (List Nat), S :- (List Nat), w :- World]
  (=> (= (marks-waiting (List.append Nat S hxm) w) true)
      (forall [d :- Nat] (=> (= (reach-mem d S) true) (= (tbl-has comp-id d (:comps w)) true) (= (tbl-all (hk-wif d) (:comps w)) true)))
      (= (marks-waiting hxm w) true))
  (intros h hd)
  (have r := (marks-waiting-rest-of _ w h)) (simp only [marks-waiting-rest] at r)
  (have r2 (= (marks-waiting-rest hxm w) true))
  (simp only [marks-waiting-rest])
  (apply (tbl-all-mono EdgeRow (hk-e (List.append Nat S hxm) (:comps w)) (hk-e hxm (:comps w)) _ (:edges w) r))
  (intros e he)
  (cases hm (:marked e))
  (exact (hk-e-unm hxm _ e hm))
  (have p := (hk-e-marked _ (:comps w) e he hm))
  (apply (hk-e-intro hxm _ e (And.left p) (And.left (And.right p))))
  (have q := (And.right (And.right p)))
  (cases q)
  (rename_i z)
  (rw [reach-mem-append] at z) (simp only [Bool.or_eq_true] at z)
  (cases z)
  (rename_i z1) (exact (Or.inr (hd (:debtor e) z1 (And.left (And.right p)))))
  (rename_i z1) (exact (Or.inl z1))
  (rename_i z) (exact (Or.inr z))
  (exact (marks-waiting-intro hxm w (marks-waiting-well-formed _ w h) r2)))

;; ---- a creditor whose in-edge is a target is waiting after the fold
(a/defn hk-ck [d :- Nat, T :- (List Nat), r :- EdgeRow] Bool (Bool.and (Nat.beq (:creditor r) d) (reach-mem (:id r) T)))
(a/theorem hk-jm-none [es :- (List EdgeRow)] (= (tbl-all (hk-jm hk-none) es) true)
  (exact (all-of-mem EdgeRow (hk-jm hk-none) es (fn [r :- EdgeRow, m :- (List.Mem r es)] (Eq.refl true)))))
(a/theorem hk-marks-of [d :- Nat, T :- (List Nat), r :- EdgeRow]
  (=> (= (hk-jm (hk-in T hk-none) r) true) (= (hk-ck d T r) true) (= (marks d r) true))
  (intros hj hc)
  (simp only [hk-ck Bool.and_eq_true] at hc)
  (simp only [hk-jm hk-in (And.right hc) Bool.true_or Bool.not_true Bool.false_or] at hj)
  (simp only [marks (And.left hc) hj Bool.and_self]))
(a/theorem hk-fold-wif [W1 :- World, T :- (List Nat), d :- Nat]
  (=> (= (well-formed W1) true) (= (awake (:comps W1) d) true) (= (tbl-any (hk-ck d T) (:edges W1)) true)
      (= (tbl-all (hk-wif d) (:comps (nat-fold mark-edge W1 T))) true))
  (intros hs ha hk0)
  (have s2 := (well-formed-nat-fold mark-edge well-formed-mark-edge T W1 hs))
  (have a2 := (hk-fold-mark-q (fn [q :- World] (awake (:comps q) d))
                (fn [w :- World, y :- Nat, h1 :- (= (well-formed w) true), h2 :- (= (awake (:comps w) d) true)]
                  (hk-cs-mark (not-idle-if-id d) (fn [q :- CompRow, hq :- (= (not-idle-if-id d q) true)] hq) w y h2))
                T W1 hs ha))
  (have k2 := (hk-fold-mark-q (fn [q :- World] (tbl-any (hk-ck d T) (:edges q)))
                (fn [w :- World, y :- Nat, h1 :- (= (well-formed w) true), h2 :- (= (tbl-any (hk-ck d T) (:edges w)) true)]
                  (hk-any-mark (hk-ck d T) (fn [r :- EdgeRow, hr :- (= (hk-ck d T r) true)] hr) w y h2))
                T W1 hs hk0))
  (have j2 := (hk-fold-J T W1 hk-none hs (hk-jm-none (:edges W1))))
  (have m2 := (any-mono-mem EdgeRow (hk-ck d T) (marks d) (:edges (nat-fold mark-edge W1 T))
                (fn [r :- EdgeRow, m :- (List.Mem r (:edges (nat-fold mark-edge W1 T))), hr :- (= (hk-ck d T r) true)]
                  (hk-marks-of d T r (tbl-all-mem EdgeRow (hk-jm (hk-in T hk-none)) r _ j2 m) hr))
                k2))
  (exact (hk-wif-marks _ d (And.left (well-formed-parts _ s2)) a2 m2)))

;; ---- T3 replace: the replaced computation is strong, the cone's creditors have a marked in-edge
(a/defn hk-rc [c :- Nat, r :- CompRow] Bool
  (Bool.or (Bool.not (Nat.beq (:id r) c)) (Bool.and (Bool.not (:idle r)) (Nat.blt (:done-epoch r) (:epoch r)))))
(a/theorem hk-rc-replace [w :- World, c :- Nat, i :- (List Nat), b :- Nat]
  (=> (= (comp-facts w) true) (= (tbl-all (hk-rc c) (:comps (comp-upd w c (comp-replace-row i b)))) true))
  (intro h)
  (have p := (gdk-parts _ _ _ (comp-facts-rest-of w h)))
  (have q := (And.right p)) (rw [all-gdkeys] at q)
  (simp only [comp-upd set-comps])
  (apply (tbl-all-upd CompRow comp-id c (comp-replace-row i b) (fn [x :- CompRow] (comp-facts-c (:runs w) (:next-id w) (gdkey x))) (hk-rc c) _ _ (:comps w) q))
  (intros r hr hx)
  (have dl := (And.left (comp-facts-c-parts _ _ _ hr))) (simp only [comp-facts-dle gdkey Bool.and_eq_true] at dl)
  (have l1 := (comp-facts-le-of _ _ (And.left dl)))
  (cases hi (:idle r))
  (have z (= (Nat.blt (:done-epoch r) (+ (:epoch r) 1)) true)) (apply comp-facts-blt-of) (omega)
  (simp only [hk-rc comp-replace-row hi z Bool.not_false Bool.and_self Bool.or_true])
  (have z (= (Nat.blt 0 (+ (:epoch r) 1)) true)) (apply comp-facts-blt-of) (omega)
  (simp only [hk-rc comp-replace-row hi z Bool.not_false Bool.and_self Bool.or_true])
  (intros r hr hx) (have hx2 (= (Nat.beq (:id r) c) false)) (exact hx) (simp only [hk-rc hx2 Bool.not_false Bool.true_or]))
(a/theorem hk-wif-rc [c :- Nat, cs :- (List CompRow)] (=> (= (tbl-all (hk-rc c) cs) true) (= (tbl-all (hk-wif c) cs) true))
  (intro h)
  (apply (tbl-all-mono CompRow (hk-rc c) (hk-wif c) _ cs h))
  (intros r hr)
  (cases hx (Nat.beq (:id r) c))
  (simp only [hk-wif hx Bool.not_false Bool.true_or])
  (simp only [hk-rc hx Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
  (simp only [hk-wif hx waiting-strongly (And.left hr) (And.right hr) Bool.not_true Bool.false_or Bool.true_or Bool.and_self]))
(a/theorem hk-awake-replace [w :- World, c :- Nat, i :- (List Nat), b :- Nat, d :- Nat]
  (=> (= (awake (:comps w) d) true) (= (awake (:comps (comp-upd w c (comp-replace-row i b))) d) true))
  (intro h)
  (simp only [awake comp-upd set-comps]) (simp only [awake] at h)
  (apply (tbl-all-upd CompRow comp-id c (comp-replace-row i b) (not-idle-if-id d) (not-idle-if-id d) _ _ (:comps w) h))
  (intros r hr hx) (simp only [not-idle-if-id comp-replace-row Bool.not_false Bool.or_true])
  (intros r hr hx) (exact hr))
(a/theorem hk-dep-cred-has [w :- World, e :- EdgeRow]
  (=> (= (well-formed w) true) (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) true) (= (tbl-has comp-id (:creditor e) (:comps w)) true))
  (intros h hm hk0)
  (have hok := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                 (And.left (And.right (well-formed-parts w h))) hm))
  (simp only [edge-ok cred-ok hk0 Bool.and_eq_true] at hok)
  (exact (And.left hok)))
;; a computation in the cone is a dep creditor: of an edge on C or on a cone member
(a/defn hk-dcm [es :- (List EdgeRow), d :- Nat, m :- Nat] Bool (tbl-any (hk-dcr d m) es))
(a/theorem hk-cone-edge [W1 :- World, c :- Nat, d :- Nat]
  (=> (= (reach-mem d (cone-set W1 c)) true)
      (= (tbl-any (hk-dcm (:edges W1) d) (List.cons Nat c (cone-set W1 c))) true))
  (intro hd)
  (have q := (hm-cone-back W1 c d hd))
  (simp only [rinv-q Bool.or_eq_true] at q)
  (cases q)
  (rename_i z)
  (simp only [tbl-any hk-dcm (hk-dc-any d c (:edges W1) z) Bool.true_or])
  (rename_i z)
  (apply (any-elim Nat (rinv-par (dep-creditors (:edges W1)) d) _ (cone-set W1 c) z))
  (intros m mm hp)
  (simp only [rinv-par] at hp)
  (have z2 (= (hk-dcm (:edges W1) d m) true)) (simp only [hk-dcm]) (exact (hk-dc-any d m (:edges W1) hp))
  (exact (any-elim-of Nat (hk-dcm (:edges W1) d) m (List.cons Nat c (cone-set W1 c)) (List.Mem.tail c mm) z2)))

(a/theorem hk-S-has [w :- World, c :- Nat, row :- CompRow, i :- (List Nat), b :- Nat, d :- Nat]
  (=> (= (well-formed w) true) (= (comp-find w c) (Option.some CompRow row))
      (= (reach-mem d (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c))) true)
      (= (tbl-has comp-id d (:comps (comp-upd w c (comp-replace-row i b)))) true))
  (intros hs hf hd)
  (have hs1 := (well-formed-comp-upd w c (comp-replace-row i b) (comp-replace-row-id i b) (comp-replace-row-pending i b) hs))
  (cases hdc (Nat.beq d c))
  (simp only [reach-mem hdc] at hd)
  (have q := (hk-cone-edge (comp-upd w c (comp-replace-row i b)) c d hd))
  (apply (any-elim Nat (hk-dcm (:edges (comp-upd w c (comp-replace-row i b))) d) _ _ q))
  (intros m mm hm)
  (simp only [hk-dcm] at hm)
  (apply (any-elim EdgeRow (hk-dcr d m) _ _ hm))
  (intros r mr hr)
  (simp only [hk-dcr Bool.and_eq_true] at hr)
  (have z := (hk-dep-cred-has (comp-upd w c (comp-replace-row i b)) r hs1 mr (And.left hr)))
  (have ec := (Nat.eq_of_beq_eq_true (And.left (And.right hr))))
  (rw [ec] at z) (exact z)
  (have e := (Nat.eq_of_beq_eq_true hdc))
  (rw [e])
  (simp only [comp-upd set-comps (tbl-has-upd CompRow comp-id c c (comp-replace-row i b) (comp-replace-row-id i b) (:comps w))])
  (exact (tbl-find-has CompRow comp-id c row (:comps w) hf)))

(a/defn hk-dS [S :- (List Nat), r :- EdgeRow] Bool (Bool.and (Nat.beq (:kind r) ek-dep) (reach-mem (:debtor r) S)))
(a/theorem hk-tg-start [hxm :- (List Nat), W1 :- World, S :- (List Nat)]
  (=> (= (well-formed W1) true) (forall [d :- Nat] (=> (= (reach-mem d S) true) (= (tbl-has comp-id d (:comps W1)) true)))
      (= (tbl-all (hk-tg (List.append Nat S hxm) (mark-targets S (:edges W1)) (:comps W1)) (:edges W1)) true))
  (intros hs hS)
  (apply (all-of-mem EdgeRow _ (:edges W1)))
  (intros r mr)
  (cases ht (reach-mem (:id r) (mark-targets S (:edges W1))))
  (simp only [hk-tg ht Bool.not_false Bool.true_or])
  (have a := (hk-mt-any S (:id r) (:edges W1) ht))
  (apply (any-elim EdgeRow (hk-tq S (:id r)) _ _ a))
  (intros r0 m0 h0)
  (simp only [hk-tq Bool.and_eq_true] at h0)
  (have q0 (= (hk-dS S r0) true)) (simp only [hk-dS (And.left (And.right h0)) (And.right (And.right h0)) Bool.and_self])
  (have u := (uniq-all EdgeRow edge-id (hk-dS S) r0 (:edges W1) (l5-edge-nodup W1 hs) m0 q0))
  (have ur := (tbl-all-mem EdgeRow (same-id-then edge-id (edge-id r0) (hk-dS S)) r (:edges W1) u mr))
  (have i0 (= (Nat.beq (edge-id r) (edge-id r0)) true)) (rw [beq-comm]) (exact (And.left h0))
  (simp only [same-id-then i0 Bool.not_true Bool.false_or hk-dS Bool.and_eq_true] at ur)
  (simp only [hk-tg ht Bool.not_true Bool.false_or])
  (apply (hk-e-intro (List.append Nat S hxm) (:comps W1) (edge-set-marked true r) (And.left ur)))
  (exact (hS (:debtor r) (And.right ur)))
  (exact (Or.inl (rm-app-l (:debtor r) S hxm (And.right ur)))))

(a/theorem hk-cone-wif [w :- World, c :- Nat, i :- (List Nat), b :- Nat, d :- Nat]
  (=> (= (well-formed w) true) (= (i7-idle-rest w) true) (= (reach-mem d (cone-set (comp-upd w c (comp-replace-row i b)) c)) true)
      (= (tbl-all (hk-wif d) (:comps (nat-fold mark-edge (comp-upd w c (comp-replace-row i b))
                                         (mark-targets (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c))
                                                       (:edges (comp-upd w c (comp-replace-row i b))))))) true))
  (intros hs h7 hd)
  (have hs1 := (well-formed-comp-upd w c (comp-replace-row i b) (comp-replace-row-id i b) (comp-replace-row-pending i b) hs))
  (have q := (hk-cone-edge (comp-upd w c (comp-replace-row i b)) c d hd))
  (apply (any-elim Nat (hk-dcm (:edges (comp-upd w c (comp-replace-row i b))) d) _ _ q))
  (intros m mm hm)
  (simp only [hk-dcm] at hm)
  (apply (any-elim EdgeRow (hk-dcr d m) _ _ hm))
  (intros r mr hr)
  (simp only [hk-dcr Bool.and_eq_true] at hr)
  (have ec := (Nat.eq_of_beq_eq_true (And.left (And.right hr))))
  (have em := (Nat.eq_of_beq_eq_true (And.right (And.right hr))))
  (have dm (= (reach-mem (:debtor r) (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c))) true))
  (rw [em]) (exact (Iff.mpr (reach-mem-iff m _) mm))
  (have tm := (hk-tgt-mem (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) (:edges (comp-upd w c (comp-replace-row i b))) r mr (And.left hr) dm))
  (have ck (= (hk-ck d (mark-targets (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) (:edges (comp-upd w c (comp-replace-row i b)))) r) true))
  (simp only [hk-ck (And.left (And.right hr)) tm Bool.and_self])
  (have k1 := (any-elim-of EdgeRow _ r (:edges (comp-upd w c (comp-replace-row i b))) mr ck))
  (have aw0 := (cred-awake-mem w r hs h7 mr))
  (simp only [cred-awake] at aw0) (rw [ec] at aw0)
  (exact (hk-fold-wif (comp-upd w c (comp-replace-row i b)) _ d hs1 (hk-awake-replace w c i b d aw0) k1)))

(a/theorem marks-waiting-mfr [hxm :- (List Nat), w :- World, c :- Nat, row :- CompRow, i :- (List Nat), b :- Nat]
  (=> (= (comp-find w c) (Option.some CompRow row)) (= (comp-facts w) true) (= (i7-idle w) true) (= (marks-waiting hxm w) true)
      (= (marks-waiting hxm (mark-from (comp-upd w c (comp-replace-row i b)) c)) true))
  (intros hf hg h7 h)
  (have hs := (marks-waiting-well-formed hxm w h))
  (have h1 := (marks-waiting-comp-upd-m hxm w c (comp-replace-row i b) (comp-replace-row-id i b) (comp-replace-row-pending i b) (comp-replace-row-hkm i b) h))
  (have hs1 := (marks-waiting-well-formed hxm _ h1))
  (have hx1 := (marks-waiting-intro (List.append Nat (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) hxm) (comp-upd w c (comp-replace-row i b)) hs1
                 (marks-waiting-rest-xm hxm _ (comp-upd w c (comp-replace-row i b))
                   (fn [d :- Nat, hd :- (= (reach-mem d hxm) true)] (rm-app-r d (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) hxm hd))
                   (marks-waiting-rest-of hxm _ h1))))
  (have tg1 := (hk-tg-start hxm (comp-upd w c (comp-replace-row i b)) (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) hs1
                 (fn [d :- Nat, hd :- (= (reach-mem d (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c))) true)]
                   (hk-S-has w c row i b d hs hf hd))))
  (have h2 := (marks-waiting-fold-mark-x _ _ (mark-targets (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) (:edges (comp-upd w c (comp-replace-row i b))))
                (comp-upd w c (comp-replace-row i b)) (hk-all-self _) tg1 hx1))
  (have rc := (hk-fold-mark-q (fn [q :- World] (tbl-all (hk-rc c) (:comps q)))
                (fn [w2 :- World, y :- Nat, a1 :- (= (well-formed w2) true), a2 :- (= (tbl-all (hk-rc c) (:comps w2)) true)]
                  (hk-cs-mark (hk-rc c) (fn [q :- CompRow, hq :- (= (hk-rc c q) true)] hq) w2 y a2))
                (mark-targets (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) (:edges (comp-upd w c (comp-replace-row i b))))
                (comp-upd w c (comp-replace-row i b)) hs1 (hk-rc-replace w c i b hg)))
  (simp only [mark-from])
  (apply (marks-waiting-discharge hxm (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) _ h2))
  (intros d hd hh)
  (cases hdc (Nat.beq d c))
  (simp only [reach-mem hdc] at hd)
  (exact (hk-cone-wif w c i b d hs (i7-idle-rest-of w h7) hd))
  (have e := (Nat.eq_of_beq_eq_true hdc))
  (rw [e])
  (exact (hk-wif-rc c _ rc)))

(a/theorem marks-waiting-create-comp-raw [hxm :- (List Nat), w :- World, c :- Nat, owner :- Nat, inputs :- (List Nat), body :- Nat]
  (=> (= (comp-facts w) true) (= (i7-idle w) true) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (create-comp-raw w c owner inputs body)) true))
  (intros hg h7 h)
  (cases hc (comp-find w c))
  (simp only [create-comp-raw hc])
  (exact (marks-waiting-comp-ins hxm w (new-comp-row w (:next-id w) owner inputs body) (Eq.refl true) (rfl) (rfl) h))
  (rename_i row)
  (cases hi (nat-list-eq (:inputs row) inputs))
  (simp only [create-comp-raw hc hi])
  (exact (marks-waiting-mfr hxm w c row inputs body hc hg h7 h))
  (simp only [create-comp-raw hc hi])
  (exact (marks-waiting-comp-upd-m hxm w c comp-adopt-row comp-adopt-row-id comp-adopt-row-pending (fn [q :- CompRow, hq :- (= (waiting-strongly q) true)] hq) h)))
(tree/restate! HMK '[well-formed-run-upd])
(a/theorem marks-waiting-t3-create [hxm :- (List Nat), w :- World, st :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat]
  (=> (= (comp-facts w) true) (= (i7-idle w) true) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (:world (t3-create w st c inputs body))) true))
  (intros hg h7 h)
  (cases ht (tok-run w st))
  (simp only [t3-create ht refuse]) (exact h)
  (rename_i r)
  (cases hg2 (create-ok w c))
  (simp only [t3-create ht hg2 refuse]) (exact h)
  (simp only [t3-create ht hg2 accept])
  (exact (marks-waiting-run-upd hxm _ (:id r) run-tick run-tick-run-id
           (marks-waiting-comp-upd-m hxm _ (:of r) _ (comp-rebasis-id _) (comp-rebasis-pending _)
             (fn [q :- CompRow, hq :- (= (waiting-strongly q) true)] hq)
             (marks-waiting-create-comp-raw hxm w c (source-owner w r) inputs body hg h7 h)))))
(a/theorem marks-waiting-t3-create-top [hxm :- (List Nat), w :- World, scope :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat]
  (=> (= (comp-facts w) true) (= (i7-idle w) true) (= (marks-waiting hxm w) true) (= (marks-waiting hxm (:world (t3-create-top w scope c inputs body))) true))
  (intros hg h7 h)
  (cases hg2 (Bool.and (create-ok w c) (scope-open-at w scope)))
  (simp only [t3-create-top hg2 refuse]) (exact h)
  (simp only [t3-create-top hg2 accept])
  (exact (marks-waiting-create-comp-raw hxm w c scope inputs body hg h7 h)))

;; ===========================================================================
;; Part H. The restatements: every transition of transition except T2 (write) and T12 (complete), whose
;; own proofs are in spindel.v2.inv.marks-step; T3 and T11 take comp-facts and i7-idle / comp-facts
;; ===========================================================================

(tree/restate! HMK '[well-formed-t1-create-nonstream well-formed-t1-create-nonstream-top well-formed-t7-track well-formed-t8-observe-any-kind well-formed-t9-fire well-formed-t15-resource-ack well-formed-t17-arm well-formed-t18-resource-fire well-formed-t19 well-formed-t20-pin well-formed-t20-unpin well-formed-t4-spawn well-formed-t4-spawn-top well-formed-t5-start well-formed-t6-await well-formed-t-schedule well-formed-t22-host-await well-formed-t-handle-new well-formed-t-post well-formed-t-take well-formed-t-release well-formed-t-finalize well-formed-t14-host-cancel well-formed-t21-release-world well-formed-t-open-scope well-formed-t-close-scope well-formed-t-detach well-formed-t-finally-enter well-formed-t-finally-exit well-formed-t-slice-exit well-formed-cancel-losers])
