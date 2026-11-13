(ns spindel.v2.hmk
  "h-mark through `world-step` (P11), kernel-checked (Init only). Bundle `hmk hxm`: every marked
  edge is a dep edge whose debtor is a computation row that is waiting in the strong form `hk-wt`
  (not idle, and done-epoch < epoch or pending /= 0), or is in the exemption list hxm. The strict
  `<` makes every epoch step a frame (no dle needed); with gd's dle it is the same as waiting.
  Marked edges' debtors are waiting (h-mark) when hxm = [] (`hk-h-mark`)."
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
            [spindel.v2.l5 :refer :all]))

;; ===========================================================================
;; Part A. The predicate and its transfer lemmas
;; ===========================================================================

;; strong waiting: not idle, and its result is stale (done-epoch < epoch) or a debtor is dirty
(a/defn hk-wt [c :- CompRow] Bool
  (Bool.and (Bool.not (:idle c)) (Bool.or (Nat.blt (:done-epoch c) (:epoch c)) (Bool.not (Nat.beq (:pending c) 0)))))
;; every row with id d is waiting
(a/defn hk-wif [d :- Nat, c :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id c) d)) (hk-wt c)))
;; a pending change keeps the rows with id d waiting: idle, or done-epoch < epoch
(a/defn hk-strong [c :- CompRow] Bool (Bool.or (:idle c) (Nat.blt (:done-epoch c) (:epoch c))))
(a/defn hk-sif [d :- Nat, c :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id c) d)) (hk-strong c)))
(a/defn hk-safe [hxm :- (List Nat), cs :- (List CompRow), d :- Nat] Bool (Bool.or (reach-mem d hxm) (tbl-all (hk-sif d) cs)))
(a/defn hk-e [hxm :- (List Nat), cs :- (List CompRow), e :- EdgeRow] Bool
  (Bool.or (Bool.not (:marked e))
    (Bool.and (Nat.beq (:kind e) ek-dep)
      (Bool.and (tbl-has comp-id (:debtor e) cs)
        (Bool.or (reach-mem (:debtor e) hxm) (tbl-all (hk-wif (:debtor e)) cs))))))
(a/defn hmk-rest [hxm :- (List Nat), w :- World] Bool (tbl-all (hk-e hxm (:comps w)) (:edges w)))
(a/defn hmk [hxm :- (List Nat), w :- World] Bool (Bool.and (inv-sample w) (hmk-rest hxm w)))

(a/theorem hmk-sample [hxm :- (List Nat), w :- World] (=> (= (hmk hxm w) true) (= (inv-sample w) true))
  (intro h) (simp only [hmk Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem hmk-rest-of [hxm :- (List Nat), w :- World] (=> (= (hmk hxm w) true) (= (hmk-rest hxm w) true))
  (intro h) (simp only [hmk Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem hmk-intro [hxm :- (List Nat), w :- World] (=> (= (inv-sample w) true) (= (hmk-rest hxm w) true) (= (hmk hxm w) true))
  (intros h1 h2) (simp only [hmk h1 h2 Bool.and_self]))
(a/theorem hmk-parts [hxm :- (List Nat), w :- World]
  (=> (= (hmk hxm w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (hmk-sample hxm w h))))

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
(a/theorem hmk-rest-xm [hxm :- (List Nat), hym :- (List Nat), w :- World]
  (=> (forall [d :- Nat] (=> (= (reach-mem d hxm) true) (= (reach-mem d hym) true)))
      (= (hmk-rest hxm w) true) (= (hmk-rest hym w) true))
  (intros hs h)
  (exact (tbl-all-mono EdgeRow (hk-e hxm (:comps w)) (hk-e hym (:comps w))
           (fn [e :- EdgeRow, he :- (= (hk-e hxm (:comps w) e) true)] (hk-e-xm hxm hym (:comps w) e hs he)) (:edges w) h)))
(a/theorem hmk-rest-nil [hxm :- (List Nat), w :- World] (=> (= (hmk-rest (List.nil Nat) w) true) (= (hmk-rest hxm w) true))
  (intro h)
  (apply (hmk-rest-xm (List.nil Nat) hxm w _ h))
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
                       hm :- (forall [c :- CompRow] (=> (= (hk-wt c) true) (= (hk-wt (f c)) true))), cs :- (List CompRow)]
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

(a/theorem hmk-comp-upd-m [hxm :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                           hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                           hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                           hm :- (forall [c :- CompRow] (=> (= (hk-wt c) true) (= (hk-wt (f c)) true)))]
  (=> (= (hmk hxm w) true) (= (hmk hxm (comp-upd w x f)) true))
  (intro h)
  (have r0 := (hmk-rest-of hxm w h))
  (have r (= (hmk-rest hxm (comp-upd w x f)) true))
  (simp only [hmk-rest comp-upd set-comps]) (simp only [hmk-rest] at r0)
  (apply (hk-all-cs hxm (:comps w) (tbl-upd comp-id x f (:comps w)) (:edges w) _ _ r0))
  (intros d hd) (rw [(tbl-has-upd CompRow comp-id x d f hid (:comps w))]) (exact hd)
  (intros d hx hd) (exact (hk-wif-upd d x f hid hm (:comps w) hd))
  (exact (hmk-intro hxm _ (inv-comp-upd w x f hid hp (hmk-sample hxm w h)) r)))

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
  (simp only [hk-wif hdd Bool.not_true Bool.false_or hk-wt Bool.and_eq_true] at w1)
  (simp only [hk-wif e hdd Bool.not_true Bool.false_or hk-wt (hi r) (he r) (hd r)])
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
  (=> (= (hmk-rest hxm w) true) (= (hmk-rest hxm (edge-upd w x f)) true))
  (intro h)
  (simp only [hmk-rest edge-upd set-edges]) (simp only [hmk-rest] at h)
  (apply (tbl-all-upd EdgeRow edge-id x f (hk-e hxm (:comps w)) (hk-e hxm (:comps w)) _ _ (:edges w) h))
  (intros e he hx) (simp only [hk-e (hk2 e) (hd e) (hm2 e)]) (simp only [hk-e] at he) (exact he)
  (intros e he hx) (exact he))

;; the edge with id x, once marked, satisfies the fact
(a/defn hk-mok [hxm :- (List Nat), cs :- (List CompRow), x :- Nat, e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:id e) x)) (hk-e hxm cs (edge-set-marked true e))))

(a/theorem hk-wt-inc [c :- CompRow] (=> (= (hk-wt c) true) (= (hk-wt (comp-inc-pending c)) true))
  (intro h) (simp only [hk-wt Bool.and_eq_true] at h)
  (simp only [hk-wt comp-inc-pending comp-set-pending (And.left h) Bool.true_and])
  (have z (= (Nat.beq (+ (:pending c) 1) 0) false))
  (cases hb (Nat.beq (+ (:pending c) 1) 0)) (rfl) (have e := (Nat.eq_of_beq_eq_true hb)) (omega)
  (simp only [z Bool.not_false Bool.or_true]))

(a/theorem hkr-mark-edge [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (= (tbl-all (hk-mok hxm (:comps w) x) (:edges w)) true) (= (hmk-rest hxm w) true) (= (hmk-rest hxm (mark-edge w x)) true))
  (intros hk0 h)
  (simp only [hmk-rest] at h)
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
  (simp only [mark-edge hf hmk-rest]) (exact h)
  (rename_i e)
  (cases hm (:marked e))
  (simp only [mark-edge hf hm hmk-rest comp-upd edge-upd set-comps set-edges])
  (exact (hk-all-cs hxm (:comps w) (tbl-upd comp-id (:creditor e) comp-inc-pending (:comps w)) _
           (fn [d :- Nat, hd :- (= (tbl-has comp-id d (:comps w)) true)]
             (Eq.trans (tbl-has-upd CompRow comp-id (:creditor e) d comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) (:comps w)) hd))
           (fn [d :- Nat, hx :- (= (reach-mem d hxm) false), hd :- (= (tbl-all (hk-wif d) (:comps w)) true)]
             (hk-wif-upd d (:creditor e) comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) hk-wt-inc (:comps w) hd))
           h1))
  (simp only [mark-edge hf hm hmk-rest]) (exact h))

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
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true) (= (hk-safe hxm (:comps w) (:creditor e)) true))) (= (hmk-rest hxm w) true) (= (hmk-rest hxm (unmark-edge w x)) true))
  (intros hu h)
  (simp only [hmk-rest] at h)
  (cases hf (edge-find w x))
  (simp only [unmark-edge hf hmk-rest]) (exact h)
  (rename_i e)
  (cases hm (:marked e))
  (simp only [unmark-edge hf hm hmk-rest]) (exact h)
  (have s := (hu e hf hm))
  (have h1 (= (tbl-all (hk-e hxm (:comps w)) (tbl-upd edge-id x (edge-set-marked false) (:edges w))) true))
  (apply (tbl-all-upd EdgeRow edge-id x (edge-set-marked false) (hk-e hxm (:comps w)) (hk-e hxm (:comps w)) _ _ (:edges w) h))
  (intros r hr hx) (exact (hk-e-unm hxm (:comps w) (edge-set-marked false r) (rfl)))
  (intros r hr hx) (exact hr)
  (simp only [unmark-edge hf hm hmk-rest comp-upd edge-upd set-comps set-edges])
  (exact (hk-cs-pend hxm (:comps w) (:creditor e) comp-dec-pending hk-dec-id hk-dec-idle hk-dec-ep hk-dec-done _ s h1)))

(a/theorem hkr-remove-edge [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true) (= (hk-safe hxm (:comps w) (:creditor e)) true))) (= (hmk-rest hxm w) true) (= (hmk-rest hxm (remove-edge w x)) true))
  (intros hu h)
  (simp only [hmk-rest] at h)
  (have h1 (= (tbl-all (hk-e hxm (:comps w)) (tbl-del edge-id x (:edges w))) true))
  (exact (tbl-all-del EdgeRow edge-id x (hk-e hxm (:comps w)) (hk-e hxm (:comps w))
           (fn [r :- EdgeRow, hr :- (= (hk-e hxm (:comps w) r) true), hx :- (= (Nat.beq (edge-id r) x) false)] hr) (:edges w) h))
  (cases hf (edge-find w x))
  (simp only [remove-edge hf hmk-rest]) (exact h)
  (rename_i e)
  (cases hm (:marked e))
  (simp only [remove-edge hf hm hmk-rest edge-del set-edges]) (exact h1)
  (have s := (hu e hf hm))
  (simp only [remove-edge hf hm hmk-rest comp-upd edge-del set-comps set-edges])
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
  (simp only [hk-wif hd hk-wt Bool.not_true Bool.false_or Bool.and_eq_true] at a2)
  (simp only [hk-wif comp-resync comp-set-pending hd hk-wt Bool.not_true Bool.false_or])
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
      (= (hmk-rest hxm w) true) (= (hmk-rest hxm (drop-edges w p)) true))
  (intros hdk hpe h)
  (simp only [hmk-rest] at h)
  (have h1 := (tbl-all-filter EdgeRow (hk-e hxm (:comps w)) p (:edges w) h))
  (simp only [hmk-rest drop-edges set-comps set-edges])
  (apply (hk-all-cs hxm (:comps w) (comps-resync (tbl-filter p (:edges w)) (:comps w)) _ _ _ h1))
  (intros d hd) (rw [has-resync]) (exact hd)
  (intros d hx hd)
  (cases hs (hk-safe hxm (:comps w) d))
  (exact (hk-wif-resync-eq d (:edges w) (tbl-filter p (:edges w)) (:comps w) (hk-count-eq hxm (:comps w) p d (:edges w) hdk hs) hpe hd))
  (simp only [hk-safe hx Bool.false_or] at hs)
  (exact (hk-wif-resync-s d (tbl-filter p (:edges w)) (:comps w) hs hd)))

;; ---- the other primitives with a rest part
(a/theorem hkr-drop-cred [hxm :- (List Nat), w :- World, a :- Nat]
  (=> (= (tbl-has comp-id a (:comps w)) false) (= (hmk-rest hxm w) true) (= (hmk-rest hxm (drop-cred-edges w a)) true))
  (intros ha h)
  (simp only [hmk-rest] at h)
  (simp only [hmk-rest drop-cred-edges comp-upd set-comps set-edges (tbl-upd-absent CompRow comp-id a (comp-set-pending 0) (:comps w) ha)])
  (exact (tbl-all-filter EdgeRow (hk-e hxm (:comps w)) (cred-ne a) (:edges w) h)))
(a/theorem hkr-drop-act [hxm :- (List Nat), w :- World, a :- Nat]
  (=> (= (tbl-has comp-id a (:comps w)) false) (= (hmk-rest hxm w) true) (= (hmk-rest hxm (drop-act w a)) true))
  (intros ha h)
  (have z := (hkr-drop-cred hxm w a ha h))
  (simp only [hmk-rest] at z)
  (simp only [hmk-rest drop-act act-del set-acts]) (exact z))

(a/theorem hkr-comp-del [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (= (unreferenced w x) true) (= (hmk-rest hxm w) true) (= (hmk-rest hxm (comp-del w x)) true))
  (intros hu h)
  (simp only [hmk-rest] at h) (simp only [unreferenced] at hu)
  (simp only [hmk-rest comp-del set-comps])
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
  (=> (= (hk-wt r) true) (= (hmk-rest hxm w) true) (= (hmk-rest hxm (bump (comp-ins w r))) true))
  (intros hw h)
  (simp only [hmk-rest] at h)
  (simp only [hmk-rest bump comp-ins set-next-id set-comps])
  (apply (hk-all-cs hxm (:comps w) (tbl-ins r (:comps w)) (:edges w) _ _ h))
  (intros d hd) (exact (has-ins-of CompRow comp-id r (:comps w) d hd))
  (intros d hx hd) (simp only [tbl-ins tbl-all hd hk-wif hw Bool.or_true Bool.and_self]))

;; a new edge is unmarked
(a/theorem hkr-insert-edge-fresh [hxm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (hmk-rest hxm w) true) (= (hmk-rest hxm (insert-edge-fresh w e)) true))
  (intro h)
  (simp only [hmk-rest] at h)
  (simp only [hmk-rest insert-edge-fresh insert-edge bump edge-ins set-next-id set-edges tbl-ins tbl-all h Bool.and_true hk-e edge-set-marked Bool.not_false Bool.true_or]))
(a/theorem hkr-insert-edge-checked [hxm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (hmk-rest hxm w) true) (= (hmk-rest hxm (insert-edge-checked w e)) true))
  (intro h)
  (cases hk0 (edge-ok-in w e))
  (simp only [insert-edge-checked hk0]) (exact h)
  (simp only [insert-edge-checked hk0]) (exact (hkr-insert-edge-fresh hxm w e h)))

;; the filter keeps a kept edge's debtor
(a/theorem hkr-filter-world [hxm :- (List Nat), w :- World, K :- (=> Nat Bool)]
  (=> (= (filter-safe-k K w) true) (= (hmk-rest hxm w) true) (= (hmk-rest hxm (filter-world K w)) true))
  (intros hs h)
  (simp only [filter-safe-k Bool.and_eq_true] at hs)
  (simp only [hmk-rest] at h)
  (simp only [hmk-rest filter-world])
  (have hb := (tbl-all-mono2 EdgeRow (fs-ref K) (hk-e hxm (:comps w)) (both (fs-ref K) (hk-e hxm (:comps w)))
                (both-of EdgeRow (fs-ref K) (hk-e hxm (:comps w))) (:edges w) (And.left hs) h))
  (apply (tbl-all-keep EdgeRow K edge-id (both (fs-ref K) (hk-e hxm (:comps w))) (hk-e hxm (tbl-keep K comp-id (:comps w))) _ (:edges w) hb))
  (intros e he hk1)
  (simp only [both Bool.and_eq_true] at he)
  (have f1 := (And.left he)) (have hk2 (= (K (:id e)) true)) (exact hk1)
  (simp only [fs-ref hk2 Bool.not_true Bool.false_or Bool.and_eq_true] at f1)
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
(a/theorem hk-wt-mono [c :- CompRow, d :- CompRow]
  (=> (=> (= (:idle c) false)
          (And (= (:idle d) false) (And (<= (:epoch c) (:epoch d)) (And (= (:done-epoch d) (:done-epoch c)) (= (:pending d) (:pending c))))))
      (= (hk-wt c) true) (= (hk-wt d) true))
  (intros hf h)
  (cases hic (:idle c))
  (have q := (hf hic))
  (have q1 := (And.left q)) (have q2 := (And.left (And.right q)))
  (have q3 := (And.left (And.right (And.right q)))) (have q4 := (And.right (And.right (And.right q))))
  (simp only [hk-wt hic Bool.not_false Bool.true_and] at h)
  (simp only [hk-wt q1 q3 q4 Bool.not_false Bool.true_and])
  (cases hb (Nat.blt (:done-epoch c) (:epoch c)))
  (simp only [hb Bool.false_or] at h) (simp only [h Bool.or_true])
  (have l := (gd-lt-of _ _ hb))
  (have l2 (= (Nat.blt (:done-epoch c) (:epoch d)) true)) (exact (gd-blt-of _ _ (Nat.lt_of_lt_of_le l q2)))
  (simp only [l2 Bool.true_or])
  (simp only [hk-wt hic Bool.not_true Bool.false_and] at h) (cases h))

(a/theorem comp-inc-epoch-hkm [c :- CompRow] (=> (= (hk-wt c) true) (= (hk-wt (comp-inc-epoch c)) true))
  (apply (hk-wt-mono c (comp-inc-epoch c)))
  (intro hi) (exact (And.intro hi (And.intro (Nat.le_succ _) (And.intro (rfl) (rfl))))))
(a/theorem comp-demand-row-hkm [c :- CompRow] (=> (= (hk-wt c) true) (= (hk-wt (comp-demand-row c)) true))
  (apply (hk-wt-mono c (comp-demand-row c)))
  (intro hi)
  (have le (<= (:epoch c) (:epoch (comp-demand-row c))))
  (cases hd (Nat.beq (:done-epoch c) 0))
  (simp only [comp-demand-row hd]) (omega)
  (simp only [comp-demand-row hd]) (omega)
  (exact (And.intro (rfl) (And.intro le (And.intro (rfl) (rfl))))))
(a/theorem comp-replace-row-hkm [i :- (List Nat), b :- Nat, c :- CompRow] (=> (= (hk-wt c) true) (= (hk-wt (comp-replace-row i b c)) true))
  (apply (hk-wt-mono c (comp-replace-row i b c)))
  (intro hi)
  (have dd (= (:done-epoch (comp-replace-row i b c)) (:done-epoch c))) (simp only [comp-replace-row hi])
  (exact (And.intro (rfl) (And.intro (Nat.le_succ _) (And.intro dd (rfl))))))
(a/theorem comp-start-row-hkm [rid :- Nat, c :- CompRow] (=> (= (hk-wt c) true) (= (hk-wt (comp-start-row rid c)) true))
  (apply (hk-wt-mono c (comp-start-row rid c)))
  (intro hi)
  (have le (<= (:epoch c) (:epoch (comp-start-row rid c))))
  (simp only [comp-start-row start-epoch hi Bool.false_and]) (omega)
  (exact (And.intro (rfl) (And.intro le (And.intro (rfl) (rfl))))))

;; ---- the full-bundle forms of the non-frame primitives (extra premises: their users are overrides)
(a/theorem hmk-mark-edge [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (= (tbl-all (hk-mok hxm (:comps w) x) (:edges w)) true) (= (hmk hxm w) true) (= (hmk hxm (mark-edge w x)) true))
  (intros hk0 h) (exact (hmk-intro hxm _ (mark-edge-inv-sample w x (hmk-sample hxm w h)) (hkr-mark-edge hxm w x hk0 (hmk-rest-of hxm w h)))))
(a/theorem hmk-unmark-edge [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true) (= (hk-safe hxm (:comps w) (:creditor e)) true))) (= (hmk hxm w) true) (= (hmk hxm (unmark-edge w x)) true))
  (intros hk0 h) (exact (hmk-intro hxm _ (unmark-edge-inv-sample w x (hmk-sample hxm w h)) (hkr-unmark-edge hxm w x hk0 (hmk-rest-of hxm w h)))))
(a/theorem hmk-remove-edge [hxm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true) (= (hk-safe hxm (:comps w) (:creditor e)) true))) (= (hmk hxm w) true) (= (hmk hxm (remove-edge w x)) true))
  (intros hk0 h) (exact (hmk-intro hxm _ (inv-remove-edge w x (hmk-sample hxm w h)) (hkr-remove-edge hxm w x hk0 (hmk-rest-of hxm w h)))))
(a/theorem hmk-drop-cred [hxm :- (List Nat), w :- World, a :- Nat]
  (=> (= (tbl-has comp-id a (:comps w)) false) (= (hmk hxm w) true) (= (hmk hxm (drop-cred-edges w a)) true))
  (intros ha h) (exact (hmk-intro hxm _ (inv-drop-cred w a (hmk-sample hxm w h)) (hkr-drop-cred hxm w a ha (hmk-rest-of hxm w h)))))
(a/theorem hmk-drop-act [hxm :- (List Nat), w :- World, a :- Nat]
  (=> (= (tbl-has comp-id a (:comps w)) false) (= (hmk hxm w) true) (= (hmk hxm (drop-act w a)) true))
  (intros ha h) (exact (hmk-intro hxm _ (inv-drop-act w a (hmk-sample hxm w h)) (hkr-drop-act hxm w a ha (hmk-rest-of hxm w h)))))
(a/theorem hmk-drop-edges [hxm :- (List Nat), w :- World, p :- (=> EdgeRow Bool)]
  (=> (= (tbl-all (hk-dok hxm (:comps w) p) (:edges w)) true) (= (hmk hxm w) true) (= (hmk hxm (drop-edges w p)) true))
  (intros hk0 h)
  (exact (hmk-intro hxm _ (inv-drop-edges w p (hmk-sample hxm w h))
           (hkr-drop-edges hxm w p hk0 (And.left (hmk-parts hxm w h)) (hmk-rest-of hxm w h)))))
(a/theorem hmk-comp-ins [hxm :- (List Nat), w :- World, r :- CompRow, hw :- (= (hk-wt r) true)]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (hmk hxm w) true) (= (hmk hxm (bump (comp-ins w r))) true))
  (intros h1 h2 h)
  (exact (hmk-intro hxm _ (inv-comp-ins-fresh w r h1 h2 (hmk-sample hxm w h)) (hkr-comp-ins hxm w r hw (hmk-rest-of hxm w h)))))

;; ===========================================================================
;; Part C. The bundle copy
;; ===========================================================================

(def HMK (mk-bundle 'hmk '[hxm :- (List Nat)] "hmk-" {'inv-comp-ins-fresh ['(Eq.refl true) 2]}))
(swap! (:renames HMK) assoc 'inv-parts 'hmk-parts 'inv-comp-ins-fresh 'hmk-comp-ins
       'mark-edge-inv-sample 'hmk-mark-edge 'unmark-edge-inv-sample 'hmk-unmark-edge 'inv-remove-edge 'hmk-remove-edge
       'inv-drop-cred 'hmk-drop-cred 'inv-drop-act 'hmk-drop-act 'inv-drop-edges 'hmk-drop-edges)
(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del
            inv-set-pins inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-task-upd inv-run-upd inv-run-del
            inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-act-ins-fresh inv-task-ins-fresh inv-bump inv-run-ins-fresh]]
  (prim! HMK o nil))
(prim! HMK 'inv-edge-upd '(hkr-edge-upd hxm w x f hk hd hm R))
(prim! HMK 'inv-filter-world '(hkr-filter-world hxm w K h1 R))
(prim! HMK 'inv-comp-del-unref '(hkr-comp-del hxm w x h0 R))
(prim! HMK 'insert-edge-fresh-inv-sample '(hkr-insert-edge-fresh hxm w e R))
(prim! HMK 'inv-insert-edge-checked '(hkr-insert-edge-checked hxm w e R))

;; the source patch: every computation edit goes through hmk-comp-upd-m (a row function that keeps
;; a waiting row waiting; the ones that do not are overrides)
(def ^:private hk-cm '#{comp-inc-epoch comp-demand-row comp-replace-row comp-start-row comp-make-idle comp-result-row comp-react-row})
(defn- hk-fhead [f] (if (seq? f) (first f) f))
(defn- hk-lapp [f lem] (if (seq? f) (apply list lem (rest f)) lem))
(defn hmk-patch [form]
  (->> (@#'spindel.v2.idle/fix-f form)
       (subst-forms (fn [y] (and (seq? y) (= 'inv-comp-upd (first y)) (>= (count y) 6)))
                    (fn [[_ w x f hid hp & more]]
                      (let [h (hk-fhead f)]
                        (apply list 'hmk-comp-upd-m 'hxm w x f hid hp
                               (if (contains? hk-cm h) (hk-lapp f (symbol (str h "-hkm"))) '(fn [c :- CompRow, hc :- (= (hk-wt c) true)] hc))
                               more))))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! HMK n hmk-patch))

;; ===========================================================================
;; Part D. Overrides: activations are no computations, removed edges are unmarked
;; ===========================================================================

;; ---- ids: a row of another table is no computation
(a/theorem hk-task-not-comp [w :- World, y :- Nat]
  (=> (= (inv-sample w) true) (= (tbl-has task-id y (:tasks w)) true) (= (tbl-has comp-id y (:comps w)) false))
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
(a/theorem hk-src-not-comp [w :- World, y :- Nat]
  (=> (= (inv-sample w) true) (= (tbl-has source-id y (:sources w)) true) (= (tbl-has comp-id y (:comps w)) false))
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
  (=> (= (inv-sample w) true) (= (deb-final w d) true) (= (tbl-has comp-id d (:comps w)) false))
  (intros h hf)
  (cases hs (source-find w d))
  (cases ht (task-find w d))
  (simp only [deb-final hs ht] at hf) (cases hf)
  (rename_i t) (exact (hk-task-not-comp w d h (tbl-find-has TaskRow task-id d t (:tasks w) ht)))
  (rename_i s) (exact (hk-src-not-comp w d h (tbl-find-has SourceRow source-id d s (:sources w) hs))))

;; ---- a found marked edge is a dep edge on a computation
(a/theorem hk-found [hxm :- (List Nat), w :- World, x :- Nat, e :- EdgeRow]
  (=> (= (hmk-rest hxm w) true) (= (edge-find w x) (Option.some EdgeRow e)) (= (:marked e) true)
      (And (= (Nat.beq (:kind e) ek-dep) true) (= (tbl-has comp-id (:debtor e) (:comps w)) true)))
  (intros h hf hm)
  (have m := (tbl-find-mem EdgeRow edge-id x e (:edges w) hf))
  (simp only [hmk-rest] at h)
  (have z := (hk-e-marked hxm (:comps w) e (tbl-all-mem EdgeRow (hk-e hxm (:comps w)) e (:edges w) h m) hm))
  (exact (And.intro (And.left z) (And.left (And.right z)))))
(a/theorem hk-found-nondep [hxm :- (List Nat), w :- World, x :- Nat, e :- EdgeRow]
  (=> (= (hmk-rest hxm w) true) (= (edge-find w x) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) false) (= (:marked e) false))
  (intros h hf hk0)
  (cases hm (:marked e))
  (rfl)
  (have z := (And.left (hk-found hxm w x e h hf hm)))
  (rw [hk0] at z) (cases z))
(a/theorem hk-found-noncomp [hxm :- (List Nat), w :- World, x :- Nat, e :- EdgeRow]
  (=> (= (hmk-rest hxm w) true) (= (edge-find w x) (Option.some EdgeRow e)) (= (tbl-has comp-id (:debtor e) (:comps w)) false) (= (:marked e) false))
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
  (=> (= (hmk-rest hxm w) true) (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) false)
      (forall [e2 :- EdgeRow] (=> (= (edge-find w (:id e)) (Option.some EdgeRow e2)) (= (:marked e2) true) (= (hk-safe hxm (:comps w) (:creditor e2)) true))))
  (intros h hf hk0)
  (apply (hk-u-of-unm hxm w (:id e)))
  (intros e2 hf2) (rw [hf] at hf2) (have ee := (Option.some.inj hf2)) (rw [← ee])
  (exact (hk-found-nondep hxm w (:id e) e h hf hk0)))
(a/theorem hk-u-self-noncomp [hxm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (hmk-rest hxm w) true) (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (tbl-has comp-id (:debtor e) (:comps w)) false)
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
  (=> (= (inv-sample w) true) (= (tbl-all (hk-noc (:comps w)) (tbl-scan act-id p (:acts w))) true))
  (intro h)
  (apply (hk-scan-all ActRow act-id p (hk-noc (:comps w)) (:acts w)))
  (intros r m)
  (simp only [hk-noc (act-not-comp w (act-id r) h (has-of-mem ActRow act-id r (:acts w) m)) Bool.not_false]))

(override! HMK 'inv-resume '[]
  '(a/theorem hmk-resume [hxm :- (List Nat), w :- World, a :- ActRow]
     (=> (= (tbl-has comp-id (:id a) (:comps w)) false) (= (hmk hxm w) true) (= (hmk hxm (resume w a)) true))
     (intros ha h)
     (simp only [resume])
     (exact (hmk-run-upd hxm (drop-act w (:id a)) (:run a) run-wake run-wake-run-id (hmk-drop-act hxm w (:id a) ha h)))))
(override! HMK 'inv-fill-slot '[inv-resume inv-act-upd]
  '(a/theorem hmk-fill-slot [hxm :- (List Nat), w :- World, a :- ActRow, x :- Nat, v :- RunResult]
     (=> (= (tbl-has comp-id (:id a) (:comps w)) false) (= (hmk hxm w) true) (= (hmk hxm (fill-slot w a x v)) true))
     (intros ha h)
     (cases hm (act-ready (act-fill x v a)))
     (simp only [fill-slot hm]) (exact (hmk-act-upd hxm w (:id a) (act-fill x v) (act-fill-act-id x v) h))
     (simp only [fill-slot hm]) (exact (hmk-resume hxm w a ha h))))
(override! HMK 'inv-dep-consumed '[inv-edge-upd]
  '(a/theorem hmk-dep-consumed [hxm :- (List Nat), w :- World, e :- EdgeRow]
     (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (hmk hxm w) true) (= (hmk hxm (dep-consumed w e)) true))
     (intros hf h)
     (cases hd (deb-final w (:debtor e)))
     (simp only [dep-consumed hd])
     (exact (hmk-edge-upd hxm w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
              (edge-rearm-edge-id _ _) (edge-rearm-kind _ _) (edge-rearm-creditor _ _) (edge-rearm-debtor _ _) (edge-rearm-marked _ _) h))
     (simp only [dep-consumed hd])
     (exact (hmk-remove-edge hxm w (:id e)
              (hk-u-self-noncomp hxm w e (hmk-rest-of hxm w h) hf (hk-final-not-comp w (:debtor e) (hmk-sample hxm w h) hd)) h))))
(override! HMK 'inv-fire-dep '[inv-invalidate inv-dep-consumed inv-fill-slot]
  '(a/theorem hmk-fire-dep [hxm :- (List Nat), w :- World, e :- EdgeRow]
     (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (hmk hxm w) true) (= (hmk hxm (fire-dep w e)) true))
     (intros hf h)
     (cases ha (act-with-member (:id e) (:acts w)))
     (simp only [fire-dep ha]) (exact (hmk-invalidate hxm w e h))
     (rename_i a)
     (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
     (simp only [fire-dep ha hc]) (exact (hmk-invalidate hxm w e h))
     (simp only [fire-dep ha hc deliver-dep])
     (have na := (act-not-comp w (:id a) (hmk-sample hxm w h) (has-of-mem ActRow act-id a (:acts w) (act-with-member-mem (:id e) (:acts w) a ha))))
     (have na2 (= (tbl-has comp-id (:id a) (:comps (dep-consumed w e))) false)) (rw [hk-has-dep-consumed]) (exact na)
     (exact (hmk-fill-slot hxm (dep-consumed w e) a (:id e) (deb-result w (:debtor e)) na2 (hmk-dep-consumed hxm w e hf h)))))
(override! HMK 'inv-fire-wait-act '[inv-edge-set-phase inv-fill-slot]
  '(a/theorem hmk-fire-wait-act [hxm :- (List Nat), res :- RunResult, w :- World, e :- EdgeRow]
     (=> (= (hmk hxm w) true) (= (hmk hxm (fire-wait-act res w e)) true))
     (intro h)
     (cases ha (act-find w (:creditor e)))
     (simp only [fire-wait-act ha]) (exact (hmk-edge-set-phase hxm w (:id e) ph-fired h))
     (rename_i a)
     (have na := (act-not-comp w (:id a) (hmk-sample hxm w h)
                   (has-of-mem ActRow act-id a (:acts w) (tbl-find-mem ActRow act-id (:creditor e) a (:acts w) ha))))
     (cases hc (run-current w (:run a)))
     (simp only [fire-wait-act ha hc]) (exact (hmk-edge-set-phase hxm w (:id e) ph-fired h))
     (have na2 (= (tbl-has comp-id (:id a) (:comps (edge-upd w (:id e) (edge-set-phase ph-fired)))) false)) (exact na)
     (simp only [fire-wait-act ha hc])
     (exact (hmk-fill-slot hxm (edge-upd w (:id e) (edge-set-phase ph-fired)) a (:id e) res na2 (hmk-edge-set-phase hxm w (:id e) ph-fired h)))))
(override! HMK 'inv-fire-wait '[inv-fire-wait-act]
  '(a/theorem hmk-fire-wait [hxm :- (List Nat), res :- RunResult, w :- World, e :- EdgeRow]
     (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-wait) true)
         (= (hmk hxm w) true) (= (hmk hxm (fire-wait res w e)) true))
     (intros hf hk0 h)
     (have k1 := (Nat.eq_of_beq_eq_true hk0))
     (have nd (= (Nat.beq (:kind e) ek-dep) false)) (rw [k1])
     (cases hc (Nat.beq (:creditor e) 0))
     (simp only [fire-wait hc]) (exact (hmk-fire-wait-act hxm res w e h))
     (simp only [fire-wait hc])
     (exact (hmk-remove-edge hxm w (:id e) (hk-u-self-nondep hxm w e (hmk-rest-of hxm w h) hf nd) h))))
(override! HMK 'inv-fire-edge '[inv-fire-observe inv-fire-wait inv-fire-dep]
  '(a/theorem hmk-fire-edge [hxm :- (List Nat), res :- RunResult, w :- World, x :- Nat]
     (=> (= (hmk hxm w) true) (= (hmk hxm (fire-edge res w x)) true))
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
     (simp only [fire-edge hf hp hk1 hk2 hk3]) (exact (hmk-fire-observe hxm w e h))
     (simp only [fire-edge hf hp hk1 hk2]) (exact (hmk-fire-wait hxm res w e hf2 hk2 h))
     (simp only [fire-edge hf hp hk1]) (exact (hmk-fire-dep hxm w e hf2 h))))

(a/theorem hmk-fold-drop-act [hxm :- (List Nat), xs :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (hk-noc (:comps w)) xs) true) (= (hmk hxm w) true) (= (hmk hxm (nat-fold drop-act w xs)) true)))
  (induction xs)
  (case' [cons a t ih])
  (case' [nil])
  (intros w hn h) (simp only [nat-fold]) (exact h)
  (intros w hn h)
  (simp only [tbl-all Bool.and_eq_true] at hn)
  (have na := (And.left hn)) (simp only [hk-noc] at na)
  (have na2 := (bnot-true _ na))
  (have h1 := (hmk-drop-act hxm w a na2 h))
  (have hn2 (= (tbl-all (hk-noc (:comps (drop-act w a))) t) true))
  (apply (tbl-all-mono Nat (hk-noc (:comps w)) (hk-noc (:comps (drop-act w a))) _ t (And.right hn)))
  (intros y hy) (simp only [hk-noc hk-has-drop-act]) (simp only [hk-noc] at hy) (exact hy)
  (simp only [nat-fold]) (exact (ih (drop-act w a) hn2 h1)))
(override! HMK 'inv-cancel-acts '[]
  '(a/theorem hmk-cancel-acts [hxm :- (List Nat), w :- World, rid :- Nat]
     (=> (= (hmk hxm w) true) (= (hmk hxm (cancel-acts w rid)) true))
     (intro h)
     (simp only [cancel-acts])
     (exact (hmk-fold-drop-act hxm (tbl-scan act-id (act-of-run rid) (:acts w)) w
              (hk-acts-noc w (act-of-run rid) (hmk-sample hxm w h)) h))))
(override! HMK 't8-unobserve-inv '[]
  '(a/theorem t8-unobserve-hmk [hxm :- (List Nat), w :- World, x :- Nat]
     (=> (= (hmk hxm w) true) (= (hmk hxm (:world (t8-unobserve w x))) true))
     (intro h)
     (cases hf (edge-find w x))
     (simp only [t8-unobserve hf refuse]) (exact h)
     (rename_i e)
     (cases hk0 (Nat.beq (:kind e) ek-observe))
     (simp only [t8-unobserve hf hk0 refuse]) (exact h)
     (have k1 := (Nat.eq_of_beq_eq_true hk0))
     (have nd (= (Nat.beq (:kind e) ek-dep) false)) (rw [k1])
     (have hu := (hk-u-of-unm hxm w x (fn [e2 :- EdgeRow, hf2 :- (= (edge-find w x) (Option.some EdgeRow e2))]
                                         (hk-found-nondep hxm w x e2 (hmk-rest-of hxm w h) hf2
                                           (Eq.trans (congrArg (fn [q :- EdgeRow] (Nat.beq (:kind q) ek-dep)) (Eq.symm (Option.some.inj (Eq.trans (Eq.symm hf) hf2)))) nd)))))
     (simp only [t8-unobserve hf hk0 accept]) (exact (hmk-remove-edge hxm w x hu h))))
(override! HMK 't22-un-inv '[]
  '(a/theorem t22-un-hmk [hxm :- (List Nat), w :- World, x :- Nat]
     (=> (= (hmk hxm w) true) (= (hmk hxm (:world (t22-host-unawait w x))) true))
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
                                         (hk-found-nondep hxm w x e2 (hmk-rest-of hxm w h) hf2
                                           (Eq.trans (congrArg (fn [q :- EdgeRow] (Nat.beq (:kind q) ek-dep)) (Eq.symm (Option.some.inj (Eq.trans (Eq.symm hf) hf2)))) nd)))))
     (have hk2 (= (Bool.and (Nat.beq (:kind e) ek-wait) (Nat.beq (:creditor e) 0)) true)) (simp only [hk0 Bool.and_self])
     (simp only [t22-host-unawait hf hk2 accept]) (exact (hmk-remove-edge hxm w x hu h))))

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
(a/theorem hmk-fold-noc [hxm :- (List Nat), f :- (=> World Nat World),
                         hf :- (forall [w :- World, x :- Nat] (=> (= (tbl-has comp-id x (:comps w)) false) (= (hmk hxm w) true) (= (hmk hxm (f w x)) true))),
                         hh :- (forall [w :- World, x :- Nat, y :- Nat] (= (tbl-has comp-id y (:comps (f w x))) (tbl-has comp-id y (:comps w)))),
                         xs :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (hk-noc (:comps w)) xs) true) (= (hmk hxm w) true) (= (hmk hxm (nat-fold f w xs)) true)))
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
(a/theorem hmk-finalize-one [hxm :- (List Nat), w :- World, d :- Nat]
  (=> (= (tbl-has comp-id d (:comps w)) false) (= (hmk hxm w) true) (= (hmk hxm (finalize-one w d)) true))
  (intros hd h)
  (simp only [finalize-one])
  (apply (hmk-drop-edges hxm w (fin-keep (:acts w) d) _ h))
  (have r := (hmk-rest-of hxm w h)) (simp only [hmk-rest] at r)
  (apply (tbl-all-mono EdgeRow (hk-e hxm (:comps w)) (hk-dok hxm (:comps w) (fin-keep (:acts w) d)) _ (:edges w) r))
  (intros e he)
  (cases hk0 (fin-keep (:acts w) d e))
  (cases hm (:marked e))
  (simp only [hk-dok hk0 hm Bool.not_false Bool.true_or Bool.false_or])
  (have p := (hk-e-marked hxm (:comps w) e he hm))
  (have hk1 := hk0) (simp only [fin-keep] at hk1)
  (have hd0 := (bnot-false _ hk1))
  (simp only [fin-drop Bool.and_eq_true] at hd0)
  (have de := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right hd0)))))
  (have z := (And.left (And.right p))) (rw [de] at z) (rw [hd] at z) (cases z)
  (simp only [hk-dok hk0 Bool.true_or]))
(a/theorem hk-append-nil [xs :- (List Nat)] (= (List.append Nat xs (List.nil Nat)) xs)
  (induction xs) (case [nil] (rfl)) (case [cons h t ih] (simp only [List.append ih])))
(override! HMK 'inv-fin-loop '[]
  '(a/theorem hmk-fin-loop [hxm :- (List Nat), fuel :- (List Nat)]
     (forall [w :- World, ds :- (List Nat)]
       (=> (= (tbl-all (hk-noc (:comps w)) ds) true) (= (hmk hxm w) true) (= (hmk hxm (:world (fin-loop fuel w ds))) true)))
     (induction fuel)
     (case' [cons h f ih])
     (case' [nil])
     (intros w ds hn hw) (simp only [fin-loop]) (exact hw)
     (intros w ds hn hw)
     (cases ds)
     (simp only [fin-loop]) (exact hw)
     (rename_i d t)
     (simp only [tbl-all Bool.and_eq_true] at hn)
     (have na := (And.left hn)) (simp only [hk-noc] at na)
     (have na2 := (bnot-true _ na))
     (have hn2 := (hk-noc-all (:comps w) (:comps (finalize-one w d)) t (fn [y :- Nat] (hk-has-finalize-one w d y)) (And.right hn)))
     (have hn3 (= (tbl-all (hk-noc (:comps (finalize-one w d)))
                    (List.append Nat t (tbl-filter (final-comp-id (finalize-one w d)) (tbl-scan edge-cred (fin-drop (:acts w) d) (:edges w))))) true))
     (rw [filter-final-nil]) (rw [hk-append-nil]) (exact hn2)
     (simp only [fin-loop])
     (exact (ih _ _ hn3 (hmk-finalize-one hxm w d na2 hw)))))
(override! HMK 'inv-finalize-debtor '[inv-fin-loop]
  '(a/theorem hmk-finalize-debtor [hxm :- (List Nat), w :- World, d :- Nat]
     (=> (= (tbl-has comp-id d (:comps w)) false) (= (hmk hxm w) true) (= (hmk hxm (finalize-debtor w d)) true))
     (intros hd h)
     (have hn (= (tbl-all (hk-noc (:comps w)) (List.cons Nat d (List.nil Nat))) true)) (simp only [tbl-all hk-noc hd Bool.not_false Bool.and_self])
     (exact (hmk-fin-loop hxm (fin-fuel w) w _ hn h))))
(a/theorem hk-fin-loop-has [fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat), y :- Nat] (= (tbl-has comp-id y (:comps (:world (fin-loop fuel w ds)))) (tbl-has comp-id y (:comps w))))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w ds y) (simp only [fin-loop])
  (intros w ds y)
  (cases ds)
  (simp only [fin-loop])
  (rename_i d t)
  (simp only [fin-loop])
  (exact (Eq.trans (ih _ _ y) (hk-has-finalize-one w d y))))
(a/theorem hk-has-finalize-debtor [w :- World, d :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (finalize-debtor w d))) (tbl-has comp-id y (:comps w)))
  (simp only [finalize-debtor])
  (exact (hk-fin-loop-has (fin-fuel w) w (List.cons Nat d (List.nil Nat)) y)))

;; ---- the callers of finalize-debtor: the finalized debtor is a source or a task
(a/theorem hk-has-wake-closed [w :- World, d :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (wake-closed w d))) (tbl-has comp-id y (:comps w)))
  (simp only [wake-closed]) (exact (hk-fold-fire-has (deb-result w d) _ w y)))
(a/theorem hk-has-close-source [w :- World, x :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (close-source w x))) (tbl-has comp-id y (:comps w)))
  (simp only [close-source])
  (exact (Eq.trans (hk-has-finalize-debtor (wake-closed (source-upd w x source-close-row) x) x y)
                   (hk-has-wake-closed (source-upd w x source-close-row) x y))))
(a/theorem hk-has-detach-source [w :- World, x :- Nat, y :- Nat]
  (= (tbl-has comp-id y (:comps (detach-source w x))) (tbl-has comp-id y (:comps w)))
  (simp only [detach-source])
  (exact (Eq.trans (hk-has-finalize-debtor (wake-closed (source-upd w x source-detach-row) x) x y)
                   (hk-has-wake-closed (source-upd w x source-detach-row) x y))))
(a/theorem hk-sources-noc [w :- World, p :- (=> SourceRow Bool)]
  (=> (= (inv-sample w) true) (= (tbl-all (hk-noc (:comps w)) (tbl-scan source-id p (:sources w))) true))
  (intro h)
  (apply (hk-scan-all SourceRow source-id p (hk-noc (:comps w)) (:sources w)))
  (intros r m)
  (simp only [hk-noc (hk-src-not-comp w (source-id r) h (has-of-mem SourceRow source-id r (:sources w) m)) Bool.not_false]))

(override! HMK 'inv-close-source '[inv-wake-closed inv-source-upd inv-finalize-debtor]
  '(a/theorem hmk-close-source [hxm :- (List Nat), w :- World, x :- Nat]
     (=> (= (tbl-has comp-id x (:comps w)) false) (= (hmk hxm w) true) (= (hmk hxm (close-source w x)) true))
     (intros hx h)
     (have h1 := (hmk-wake-closed hxm (source-upd w x source-close-row) x (hmk-source-upd hxm w x source-close-row source-close-row-id h)))
     (have hx2 (= (tbl-has comp-id x (:comps (wake-closed (source-upd w x source-close-row) x))) false))
     (exact (Eq.trans (hk-has-wake-closed (source-upd w x source-close-row) x x) hx))
     (exact (hmk-finalize-debtor hxm (wake-closed (source-upd w x source-close-row) x) x hx2 h1))))
(override! HMK 'inv-close-local '[nat-fold-inv inv-close-scope-id inv-close-source]
  '(a/theorem hmk-close-local [hxm :- (List Nat), w :- World, sub :- (List Nat)]
     (=> (= (hmk hxm w) true) (= (hmk hxm (close-local w sub)) true))
     (intro h)
     (have h1 := (nat-fold-hmk hxm close-scope-id (hmk-close-scope-id hxm) sub w h))
     (have n0 := (hk-sources-noc w (source-owned-in sub) (hmk-sample hxm w h)))
     (have n1 := (hk-noc-all (:comps w) (:comps (nat-fold close-scope-id w sub)) (tbl-scan source-id (source-owned-in sub) (:sources w))
                   (fn [y :- Nat] (hk-fold-has close-scope-id (fn [w2 :- World, x2 :- Nat, y2 :- Nat] (Eq.refl (tbl-has comp-id y2 (:comps w2)))) sub w y))
                   n0))
     (simp only [close-local])
     (exact (hmk-fold-noc hxm close-source (fn [w2 :- World, x2 :- Nat, hx :- (= (tbl-has comp-id x2 (:comps w2)) false), h2 :- (= (hmk hxm w2) true)]
                                             (hmk-close-source hxm w2 x2 hx h2))
              hk-has-close-source (tbl-scan source-id (source-owned-in sub) (:sources w)) (nat-fold close-scope-id w sub) n1 h1))))
(override! HMK 'inv-fire-task-cancelled '[nat-fold-inv inv-fire-edge inv-finalize-debtor]
  '(a/theorem hmk-fire-task-cancelled [hxm :- (List Nat), w :- World, d :- Nat]
     (=> (= (tbl-has comp-id d (:comps w)) false) (= (hmk hxm w) true) (= (hmk hxm (fire-task-cancelled w d)) true))
     (intros hd h)
     (simp only [fire-task-cancelled])
     (have h1 := (nat-fold-hmk hxm (fire-edge res-cancelled) (hmk-fire-edge hxm res-cancelled) (tbl-scan edge-id (on-task d) (:edges w)) w h))
     (exact (hmk-finalize-debtor hxm (nat-fold (fire-edge res-cancelled) w (tbl-scan edge-id (on-task d) (:edges w))) d
              (Eq.trans (hk-fold-fire-has res-cancelled (tbl-scan edge-id (on-task d) (:edges w)) w d) hd) h1))))
(override! HMK 'inv-debtor-side '[inv-fire-task-cancelled inv-task-upd inv-invalidate-dependents inv-fire-waits-cancelled]
  '(a/theorem hmk-debtor-side [hxm :- (List Nat), w :- World, r :- RunRow]
     (=> (= (hmk hxm w) true) (= (hmk hxm (debtor-side w r)) true))
     (intro h)
     (cases hc (comp-find w (:of r)))
     (have hd := (tbl-find-none-has CompRow comp-id (:of r) (:comps w) hc))
     (simp only [debtor-side hc])
     (exact (hmk-fire-task-cancelled hxm (task-upd w (:of r) task-cancel-result) (:of r) hd
              (hmk-task-upd hxm w (:of r) task-cancel-result task-cancel-result-id h)))
     (rename_i c)
     (cases he (Nat.beq (:epoch r) (:epoch c)))
     (simp only [debtor-side hc he]) (exact h)
     (simp only [debtor-side hc he])
     (exact (hmk-invalidate-dependents hxm (fire-waits-cancelled w (:of r)) (:of r) (hmk-fire-waits-cancelled hxm w (:of r) h)))))
(override! HMK 'inv-fin-if-final '[inv-finalize-debtor]
  '(a/theorem hmk-fin-if-final [hxm :- (List Nat), w :- World, d :- Nat]
     (=> (= (hmk hxm w) true) (= (hmk hxm (fin-if-final w d)) true))
     (intro h)
     (cases hf (deb-final w d))
     (simp only [fin-if-final hf]) (exact h)
     (simp only [fin-if-final hf]) (exact (hmk-finalize-debtor hxm w d (hk-final-not-comp w d (hmk-sample hxm w h) hf) h))))
(override! HMK 't-deliver-inv '[inv-finalize-debtor nat-fold-inv inv-fire-edge inv-deliver-fire]
  '(a/theorem t-deliver-hmk [hxm :- (List Nat), w :- World, x :- Nat, v :- Nat]
     (=> (= (hmk hxm w) true) (= (hmk hxm (:world (t-deliver w x v))) true))
     (intro h)
     (cases hs (source-find w x))
     (simp only [t-deliver hs refuse]) (exact h)
     (rename_i s)
     (have hx := (hk-src-not-comp w x (hmk-sample hxm w h) (tbl-find-has SourceRow source-id x s (:sources w) hs)))
     (cases hg (deliverable s))
     (simp only [t-deliver hs hg refuse]) (exact h)
     (have h1 := (nat-fold-hmk hxm (fire-edge (RunResult.mk res-ok v)) (hmk-fire-edge hxm (RunResult.mk res-ok v)) (waits-on x (:edges w))
                   (deliver-fire w x v) (hmk-deliver-fire hxm w x v h)))
     (have hx2 (= (tbl-has comp-id x (:comps (nat-fold (fire-edge (RunResult.mk res-ok v)) (deliver-fire w x v) (waits-on x (:edges w))))) false))
     (exact (Eq.trans (hk-fold-fire-has (RunResult.mk res-ok v) (waits-on x (:edges w)) (deliver-fire w x v) x)
              (Eq.trans (hk-fold-fire-has (RunResult.mk res-ok v) (edges-onto x (:edges w)) (source-upd w x (source-write v)) x) hx)))
     (simp only [t-deliver hs hg accept deliver-raw])
     (exact (hmk-finalize-debtor hxm _ x hx2 h1))))

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
(override! HMK 'inv-track-fin '[]
  '(a/theorem hmk-track-fin [hxm :- (List Nat), s :- SourceRow, y :- Nat, w :- World]
     (=> (forall [e :- EdgeRow] (=> (= (edge-find w y) (Option.some EdgeRow e)) (= (:marked e) false)))
         (= (hmk hxm w) true) (= (hmk hxm (track-fin s y w)) true))
     (intros hu h)
     (cases ho (:open s))
     (simp only [track-fin ho]) (exact (hmk-remove-edge hxm w y (hk-u-of-unm hxm w y hu) h))
     (simp only [track-fin ho]) (exact h)))
(override! HMK 'inv-track-raw '[inv-track-fin insert-edge-fresh-inv-sample inv-edge-upd inv-run-upd]
  '(a/theorem hmk-track-raw [hxm :- (List Nat), w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat]
     (=> (= (comp-has w (:of r)) true) (= (source-find w x) (Option.some SourceRow s))
         (= (hmk hxm w) true) (= (hmk hxm (track-raw w r x s k)) true))
     (intros hc hs h)
     (have hxn := (hk-src-not-comp w x (hmk-sample hxm w h) (tbl-find-has SourceRow source-id x s (:sources w) hs)))
     (have h2 (= (hmk hxm (match (site-edge (:edges w) (:of r) (:effect-index r) x)
                             [none (track-new w r x s k)]
                             [(some e) (comp-upd (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s)))
                                                 (:of r) (comp-consume-adopt (:effect-index r) x))])) true))
     (cases he (site-edge (:edges w) (:of r) (:effect-index r) x))
     (simp only [track-new])
     (have h3 := (insert-edge-fresh-hmk hxm w (track-edge r x s k) (track-edge-ok w r x s k hc hs) h))
     (have h4 := (hmk-track-fin hxm s (:next-id w) (insert-edge-fresh w (track-edge r x s k))
                   (fn [e2 :- EdgeRow, hf2 :- (= (edge-find (insert-edge-fresh w (track-edge r x s k)) (:next-id w)) (Option.some EdgeRow e2))]
                     (hk-find-fresh w (track-edge r x s k) e2 hf2)) h3))
     (exact (hmk-comp-upd-m hxm (track-fin s (:next-id w) (insert-edge-fresh w (track-edge r x s k))) (:of r)
              (comp-consume-adopt (:effect-index r) x) (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _)
              (fn [c :- CompRow, hc2 :- (= (hk-wt c) true)] hc2) h4))
     (rename_i e)
     (have sm := (site-edge-mem (:edges w) (:of r) (:effect-index r) x e he))
     (have fs := (find-self EdgeRow edge-id e (:edges w) (l5-edge-nodup w (hmk-sample hxm w h)) (And.left sm)))
     (have fs2 (= (edge-find w (:id e)) (Option.some EdgeRow e))) (exact fs)
     (have de := (Nat.eq_of_beq_eq_true (And.right sm)))
     (have hdn (= (tbl-has comp-id (:debtor e) (:comps w)) false)) (rw [de]) (exact hxn)
     (have um := (hk-found-noncomp hxm w (:id e) e (hmk-rest-of hxm w h) fs2 hdn))
     (have h3 := (hmk-edge-upd hxm w (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) (edge-reread-kind _ _)
                   (edge-reread-creditor _ _) (edge-reread-debtor _ _) (edge-reread-marked _ _) h))
     (have fu := (hk-find-upd EdgeRow edge-id (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) (:edges w) e fs))
     (have h4 := (hmk-track-fin hxm s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s))
                   (fn [e2 :- EdgeRow, hf2 :- (= (edge-find (edge-upd w (:id e) (edge-reread (track-cont r k) s)) (:id e)) (Option.some EdgeRow e2))]
                     (Eq.trans (congrArg (fn [q :- EdgeRow] (:marked q)) (Eq.symm (Option.some.inj (Eq.trans (Eq.symm fu) hf2))))
                               (Eq.trans (edge-reread-marked (track-cont r k) s e) um)))
                   h3))
     (exact (hmk-comp-upd-m hxm (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s))) (:of r)
              (comp-consume-adopt (:effect-index r) x) (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _)
              (fn [c :- CompRow, hc2 :- (= (hk-wt c) true)] hc2) h4))
     (simp only [track-raw])
     (exact (hmk-run-upd hxm _ (:id r) run-tick run-tick-run-id h2))))

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
(override! HMK 'inv-revoke-roots '[inv-set-pending-act inv-set-pins inv-drop-edges inv-set-released]
  '(a/theorem hmk-revoke-roots [hxm :- (List Nat), w :- World]
     (=> (= (hmk hxm w) true) (= (hmk hxm (revoke-roots w)) true))
     (intro h)
     (have h1 := (hmk-set-released hxm w true h))
     (have r := (hmk-rest-of hxm _ h1)) (simp only [hmk-rest] at r)
     (have p := (tbl-all-mono EdgeRow (hk-e hxm (:comps (set-released w true))) (hk-dok hxm (:comps (set-released w true)) not-host)
                  (fn [e :- EdgeRow, he :- (= (hk-e hxm (:comps (set-released w true)) e) true)] (hk-dok-host hxm (:comps (set-released w true)) e he))
                  (:edges (set-released w true)) r))
     (simp only [revoke-roots])
     (exact (hmk-set-pending-act hxm _ 0 (hmk-set-pins hxm _ _ (hmk-drop-edges hxm (set-released w true) not-host p h1))))))

;; ---- reactivation: comp-react-row on an idle computation (no marked edge on it is justified by waiting)
(a/theorem hmk-comp-react [hxm :- (List Nat), w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) true) (= (hmk hxm w) true) (= (hmk hxm (comp-upd w (:id c) comp-react-row)) true))
  (intros hm hi h)
  (have r0 := (hmk-rest-of hxm w h))
  (have r (= (hmk-rest hxm (comp-upd w (:id c) comp-react-row)) true))
  (simp only [hmk-rest comp-upd set-comps]) (simp only [hmk-rest] at r0)
  (apply (hk-all-cs hxm (:comps w) (tbl-upd comp-id (:id c) comp-react-row (:comps w)) (:edges w) _ _ r0))
  (intros d hd) (rw [(tbl-has-upd CompRow comp-id (:id c) d comp-react-row comp-react-row-id (:comps w))]) (exact hd)
  (intros d hx hd)
  (cases hcd (Nat.beq (:id c) d))
  (exact (hk-wif-pend-ne d (:id c) comp-react-row comp-react-row-id (:comps w) hcd hd))
  (have z := (tbl-all-mem CompRow (hk-wif d) c (:comps w) hd hm))
  (simp only [hk-wif hcd hk-wt hi Bool.not_true Bool.false_or Bool.false_and] at z) (cases z)
  (exact (hmk-intro hxm _ (inv-comp-upd w (:id c) comp-react-row comp-react-row-id comp-react-row-pending (hmk-sample hxm w h)) r)))
(override! HMK 'inv-react-one '[inv-react-edges]
  '(a/theorem hmk-react-one [hxm :- (List Nat), w :- World, c :- CompRow]
     (=> (List.Mem c (:comps w)) (= (:idle c) true) (= (hmk hxm w) true) (= (hmk hxm (react-one w c)) true))
     (intros hm hi h)
     (simp only [react-one])
     (exact (hmk-react-edges hxm (:validity c) (comp-upd w (:id c) comp-react-row) (:id c) (hmk-comp-react hxm w c hm hi h)))))
(override! HMK 'inv-react-loop '[inv-react-one]
  '(a/theorem hmk-react-loop [hxm :- (List Nat), fuel :- (List Nat)]
     (forall [w :- World, q :- (List Nat)] (=> (= (hmk hxm w) true) (= (hmk hxm (react-loop fuel w q)) true)))
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
     (exact (ih _ _ (hmk-react-one hxm w c (tbl-find-mem CompRow comp-id x c (:comps w) hc) hi hw)))))

;; ---- Rule R's detach: a detached source is no computation
(override! HMK 'inv-detach-source '[inv-wake-closed inv-source-upd inv-finalize-debtor]
  '(a/theorem hmk-detach-source [hxm :- (List Nat), w :- World, x :- Nat]
     (=> (= (tbl-has comp-id x (:comps w)) false) (= (hmk hxm w) true) (= (hmk hxm (detach-source w x)) true))
     (intros hx h)
     (have h1 := (hmk-wake-closed hxm (source-upd w x source-detach-row) x (hmk-source-upd hxm w x source-detach-row source-detach-row-id h)))
     (have hx2 (= (tbl-has comp-id x (:comps (wake-closed (source-upd w x source-detach-row) x))) false))
     (exact (Eq.trans (hk-has-wake-closed (source-upd w x source-detach-row) x x) hx))
     (exact (hmk-finalize-debtor hxm (wake-closed (source-upd w x source-detach-row) x) x hx2 h1))))
(override! HMK 'inv-detach '[nat-fold-inv inv-detach-comp inv-detach-task inv-detach-source]
  '(a/theorem hmk-detach [hxm :- (List Nat), w :- World]
     (=> (= (hmk hxm w) true) (= (hmk hxm (detach w)) true))
     (intro h)
     (have n0 := (hk-sources-noc w (src-orphan w) (hmk-sample hxm w h)))
     (have h1 := (hmk-fold-noc hxm detach-source (fn [w2 :- World, x2 :- Nat, hx :- (= (tbl-has comp-id x2 (:comps w2)) false), h2 :- (= (hmk hxm w2) true)]
                                                   (hmk-detach-source hxm w2 x2 hx h2))
                   hk-has-detach-source (tbl-scan source-id (src-orphan w) (:sources w)) w n0 h))
     (simp only [detach])
     (exact (nat-fold-hmk hxm detach-comp (hmk-detach-comp hxm) (tbl-scan comp-id (comp-orphan w) (:comps w)) _
              (nat-fold-hmk hxm detach-task (hmk-detach-task hxm) (tbl-scan task-id (task-orphan w) (:tasks w)) _ h1)))))

;; ===========================================================================
;; Part E. T11: the dispatched computation C is strong (done-epoch < epoch) from the needs-run
;; guard and gd's dle; watch bundle hsw c (rows with id c keep done-epoch < epoch: every gd-cmono
;; edit keeps it) through the predecessor's cancel; the entry edge keeps its debtor (p3's kx)
;; ===========================================================================

(a/defn hsw-one [hsc :- Nat, k :- GDK] Bool (Bool.or (Bool.not (Nat.beq (:id k) hsc)) (Nat.blt (:done k) (:epoch k))))
(a/defn hsw-rest [hsc :- Nat, w :- World] Bool (tbl-all (hsw-one hsc) (gdkeys (:comps w))))
(a/defn hsw [hsc :- Nat, w :- World] Bool (Bool.and (inv-sample w) (hsw-rest hsc w)))
(a/theorem hsw-sample [hsc :- Nat, w :- World] (=> (= (hsw hsc w) true) (= (inv-sample w) true))
  (intro h) (simp only [hsw Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem hsw-rest-of [hsc :- Nat, w :- World] (=> (= (hsw hsc w) true) (= (hsw-rest hsc w) true))
  (intro h) (simp only [hsw Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem hsw-intro [hsc :- Nat, w :- World] (=> (= (inv-sample w) true) (= (hsw-rest hsc w) true) (= (hsw hsc w) true))
  (intros h1 h2) (simp only [hsw h1 h2 Bool.and_self]))
(a/theorem hsw-parts [hsc :- Nat, w :- World]
  (=> (= (hsw hsc w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (hsw-sample hsc w h))))
(a/theorem hsw-rest-same [hsc :- Nat, w :- World, w2 :- World]
  (=> (= (gdkeys (:comps w2)) (gdkeys (:comps w))) (= (hsw-rest hsc w) true) (= (hsw-rest hsc w2) true))
  (intros e h) (simp only [hsw-rest e]) (simp only [hsw-rest] at h) (exact h))
(a/theorem hsw-one-mono [hsc :- Nat, k :- GDK, d :- GDK]
  (=> (= (gd-cmono k d) true) (= (hsw-one hsc k) true) (= (hsw-one hsc d) true))
  (intros hm h)
  (simp only [gd-cmono Bool.and_eq_true Bool.or_eq_true] at hm)
  (have hid := (Nat.eq_of_beq_eq_true (And.left hm)))
  (have hep := (gd-le-of _ _ (And.left (And.right (And.right hm)))))
  (have hd := (And.right (And.right (And.right hm))))
  (simp only [hsw-one hid]) (simp only [hsw-one Bool.or_eq_true] at h)
  (cases h)
  (rename_i a1) (simp only [a1 Bool.true_or])
  (rename_i a1)
  (have q1 := (gd-lt-of _ _ a1))
  (have r1 (= (Nat.blt (:done d) (:epoch d)) true))
  (cases hd)
  (rename_i z) (rw [(Nat.eq_of_beq_eq_true z)]) (exact (gd-blt-of _ _ (Nat.lt_of_lt_of_le q1 hep)))
  (rename_i z) (rw [(Nat.eq_of_beq_eq_true z)]) (apply gd-blt-of) (omega)
  (simp only [r1 Bool.or_true]))
(a/theorem hsw-comp-upd [hsc :- Nat, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hk :- (forall [c :- CompRow] (= (gdkey (f c)) (gdkey c)))]
  (=> (= (hsw hsc w) true) (= (hsw hsc (comp-upd w x f)) true))
  (intro h)
  (exact (hsw-intro hsc _ (inv-comp-upd w x f hid hp (hsw-sample hsc w h))
           (hsw-rest-same hsc w (comp-upd w x f) (gdkeys-upd x f hk (:comps w)) (hsw-rest-of hsc w h)))))
(a/theorem hsw-comp-upd-m [hsc :- Nat, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                          hm :- (forall [c :- CompRow] (= (gd-cmono (gdkey c) (gdkey (f c))) true))]
  (=> (= (hsw hsc w) true) (= (hsw hsc (comp-upd w x f)) true))
  (intro h)
  (have q := (hsw-rest-of hsc w h))
  (have r2 (= (hsw-rest hsc (comp-upd w x f)) true))
  (simp only [hsw-rest comp-upd set-comps]) (simp only [hsw-rest] at q)
  (rw [all-gdkeys] at q) (rw [all-gdkeys])
  (exact (tbl-all-upd CompRow comp-id x f (fn [c :- CompRow] (hsw-one hsc (gdkey c))) (fn [c :- CompRow] (hsw-one hsc (gdkey c)))
           (fn [c :- CompRow, h1 :- (= (hsw-one hsc (gdkey c)) true), h2 :- (= (Nat.beq (comp-id c) x) true)]
             (hsw-one-mono hsc (gdkey c) (gdkey (f c)) (hm c) h1))
           (fn [c :- CompRow, h1 :- (= (hsw-one hsc (gdkey c)) true), h2 :- (= (Nat.beq (comp-id c) x) false)] h1)
           (:comps w) q))
  (exact (hsw-intro hsc _ (inv-comp-upd w x f hid hp (hsw-sample hsc w h)) r2)))
(a/theorem hswr-mark-edge [hsc :- Nat, w :- World, x :- Nat] (=> (= (hsw-rest hsc w) true) (= (hsw-rest hsc (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (simp only [mark-edge hf]) (exact h)
  (rename_i e)
  (cases hm (:marked e))
  (simp only [mark-edge hf hm])
  (exact (hsw-rest-same hsc w (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending)
           (gdkeys-upd (:creditor e) comp-inc-pending gd-key-inc-pending (:comps w)) h))
  (simp only [mark-edge hf hm]) (exact h))
(a/theorem hswr-unmark-edge [hsc :- Nat, w :- World, x :- Nat] (=> (= (hsw-rest hsc w) true) (= (hsw-rest hsc (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (simp only [unmark-edge hf]) (exact h)
  (rename_i e)
  (cases hm (:marked e))
  (simp only [unmark-edge hf hm]) (exact h)
  (simp only [unmark-edge hf hm])
  (exact (hsw-rest-same hsc w (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending)
           (gdkeys-upd (:creditor e) comp-dec-pending gd-key-dec-pending (:comps w)) h)))
(a/theorem hswr-remove-edge [hsc :- Nat, w :- World, x :- Nat] (=> (= (hsw-rest hsc w) true) (= (hsw-rest hsc (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (simp only [remove-edge hf]) (exact h)
  (rename_i e)
  (cases hm (:marked e))
  (simp only [remove-edge hf hm]) (exact (hsw-rest-same hsc w (edge-del w x) (rfl) h))
  (simp only [remove-edge hf hm])
  (exact (hsw-rest-same hsc w (comp-upd (edge-del w x) (:creditor e) comp-dec-pending)
           (gdkeys-upd (:creditor e) comp-dec-pending gd-key-dec-pending (:comps w)) h)))
(a/theorem hswr-drop-cred [hsc :- Nat, w :- World, a :- Nat] (=> (= (hsw-rest hsc w) true) (= (hsw-rest hsc (drop-cred-edges w a)) true))
  (intro h) (simp only [drop-cred-edges])
  (exact (hsw-rest-same hsc w (comp-upd (set-edges w (tbl-filter (cred-ne a) (:edges w))) a (comp-set-pending 0))
           (gdkeys-upd a (comp-set-pending 0) (gd-key-set-pending 0) (:comps w)) h)))
(a/theorem hswr-drop-act [hsc :- Nat, w :- World, a :- Nat] (=> (= (hsw-rest hsc w) true) (= (hsw-rest hsc (drop-act w a)) true))
  (intro h) (simp only [drop-act])
  (exact (hsw-rest-same hsc (drop-cred-edges w a) (act-del (drop-cred-edges w a) a) (rfl) (hswr-drop-cred hsc w a h))))
(a/theorem hswr-drop-edges [hsc :- Nat, w :- World, p :- (=> EdgeRow Bool)] (=> (= (hsw-rest hsc w) true) (= (hsw-rest hsc (drop-edges w p)) true))
  (intro h) (simp only [drop-edges])
  (exact (hsw-rest-same hsc w (set-comps (set-edges w (tbl-filter p (:edges w))) (comps-resync (tbl-filter p (:edges w)) (:comps w)))
           (gdkeys-resync (tbl-filter p (:edges w)) (:comps w)) h)))
(a/theorem hswr-comp-del [hsc :- Nat, w :- World, x :- Nat] (=> (= (hsw-rest hsc w) true) (= (hsw-rest hsc (comp-del w x)) true))
  (intro h) (simp only [hsw-rest comp-del set-comps gdkeys-del]) (simp only [hsw-rest] at h)
  (exact (tbl-all-del GDK gdk-id x (hsw-one hsc) (hsw-one hsc) (fn [k :- GDK, h1 :- (= (hsw-one hsc k) true), h2 :- (= (Nat.beq (gdk-id k) x) false)] h1) _ h)))
(a/theorem hswr-filter-world [hsc :- Nat, w :- World, K :- (=> Nat Bool)] (=> (= (hsw-rest hsc w) true) (= (hsw-rest hsc (filter-world K w)) true))
  (intro h) (simp only [hsw-rest filter-world gdkeys-keep]) (simp only [hsw-rest] at h)
  (exact (tbl-all-keep GDK K gdk-id (hsw-one hsc) (hsw-one hsc) (fn [k :- GDK, h1 :- (= (hsw-one hsc k) true), h2 :- (= (K (gdk-id k)) true)] h1) _ h)))
(a/theorem hswr-insert-edge-checked [hsc :- Nat, w :- World, e :- EdgeRow]
  (=> (= (hsw-rest hsc w) true) (= (hsw-rest hsc (insert-edge-checked w e)) true))
  (intro h)
  (cases hk (edge-ok-in w e))
  (simp only [insert-edge-checked hk]) (exact h)
  (simp only [insert-edge-checked hk]) (exact h))

(def HSW (mk-bundle 'hsw '[hsc :- Nat] "hsw-" {}))
(swap! (:renames HSW) assoc 'inv-parts 'hsw-parts)
(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-set-pins
            inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-task-upd inv-edge-upd inv-run-upd inv-run-del
            inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-act-ins-fresh inv-task-ins-fresh inv-run-ins-fresh
            inv-bump insert-edge-fresh-inv-sample]]
  (prim! HSW o nil))
(prim! HSW 'inv-insert-edge-checked '(hswr-insert-edge-checked hsc w e R))
(prim! HSW 'inv-remove-edge '(hswr-remove-edge hsc w x R))
(prim! HSW 'mark-edge-inv-sample '(hswr-mark-edge hsc w x R))
(prim! HSW 'unmark-edge-inv-sample '(hswr-unmark-edge hsc w x R))
(prim! HSW 'inv-drop-cred '(hswr-drop-cred hsc w a R))
(prim! HSW 'inv-drop-act '(hswr-drop-act hsc w a R))
(prim! HSW 'inv-drop-edges '(hswr-drop-edges hsc w p R))
(prim! HSW 'inv-comp-del-unref '(hswr-comp-del hsc w x R))
(prim! HSW 'inv-filter-world '(hswr-filter-world hsc w K R))
(def ^:private hk-gd-cm '#{comp-inc-epoch comp-demand-row comp-replace-row comp-make-idle comp-clear-run})
(defn hsw-patch [form]
  (->> (@#'spindel.v2.idle/fix-f form)
       (subst-forms (fn [y] (and (seq? y) (= 'inv-comp-upd (first y)) (>= (count y) 6)))
                    (fn [[_ w x f hid hp & more]]
                      (let [h (hk-fhead f)]
                        (if (contains? hk-gd-cm h)
                          (apply list 'hsw-comp-upd-m 'hsc w x f hid hp (hk-lapp f (symbol (str h "-gcm"))) more)
                          (apply list 'hsw-comp-upd 'hsc w x f hid hp '(fn [c :- CompRow] (Eq.refl (gdkey c))) more)))))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! HSW n hsw-patch))
(lcopy! HSW 'inv-cancel-pred)

(a/theorem hsw-sif [hsc :- Nat, w :- World] (=> (= (hsw-rest hsc w) true) (= (tbl-all (hk-sif hsc) (:comps w)) true))
  (intro h)
  (simp only [hsw-rest] at h) (rw [all-gdkeys] at h)
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) h))
  (intros c hc)
  (simp only [hsw-one gdkey Bool.or_eq_true] at hc)
  (cases hc)
  (rename_i z) (simp only [hk-sif z Bool.true_or])
  (rename_i z) (simp only [hk-sif hk-strong z Bool.or_true]))
(a/theorem hsw-start [w :- World, c :- CompRow]
  (=> (= (gd w) true) (List.Mem c (:comps w)) (= (Nat.beq (:done-epoch c) (:epoch c)) false) (= (hsw (:id c) w) true))
  (intros h hm hd)
  (have hs := (gd-sample w h))
  (have p := (gdk-parts _ _ _ (gd-rest-of w h)))
  (have q := (And.right p)) (rw [all-gdkeys] at q)
  (have hc0 := (tbl-all-mem CompRow (fn [x :- CompRow] (gd-c (:runs w) (:next-id w) (gdkey x))) c (:comps w) q hm))
  (have dl := (And.left (gd-c-parts _ _ _ hc0))) (simp only [gd-dle gdkey Bool.and_eq_true] at dl)
  (have l1 := (gd-le-of _ _ (And.left dl)))
  (have ne (Not (= (:done-epoch c) (:epoch c))))
  (intro eq) (rw [eq] at hd) (rw [Nat.beq_refl] at hd) (cases hd)
  (have qc (= (hsw-one (:id c) (gdkey c)) true))
  (simp only [hsw-one gdkey]) (apply (Eq.trans (congrArg (fn [b :- Bool] (Bool.or (Bool.not (Nat.beq (:id c) (:id c))) b)) (gd-blt-of _ _ (Nat.lt_of_le_of_ne l1 ne)))))
  (simp only [Bool.or_true])
  (have u := (gd-same-id w c (fn [x :- CompRow] (hsw-one (:id c) (gdkey x))) hs hm qc))
  (have r (= (hsw-rest (:id c) w) true))
  (simp only [hsw-rest])
  (rw [all-gdkeys])
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) u))
  (intros x hx)
  (cases hi (Nat.beq (comp-id x) (:id c)))
  (have hi2 (= (Nat.beq (:id x) (:id c)) false)) (exact hi) (simp only [hsw-one gdkey hi2 Bool.not_false Bool.true_or])
  (simp only [same-id-then hi Bool.not_true Bool.false_or] at hx) (exact hx)
  (exact (hsw-intro _ w hs r)))

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
(override! HMK 'inv-cut-suffix '[inv-drop-edges]
  '(a/theorem hmk-cut-suffix [hxm :- (List Nat), w :- World, c :- Nat, has :- Bool, cut :- Nat, cid :- Nat]
     (=> (= (tbl-all (hk-sif c) (:comps w)) true) (= (hmk hxm w) true) (= (hmk hxm (cut-suffix w c has cut cid)) true))
     (intros hs h)
     (have p := (all-of-mem EdgeRow (hk-dok hxm (:comps w) (keep-prefix c has cid)) (:edges w)
                  (fn [r :- EdgeRow, m :- (List.Mem r (:edges w))] (hk-dok-cut hxm (:comps w) c has cid r hs))))
     (have h1 := (hmk-drop-edges hxm w (keep-prefix c has cid) p h))
     (simp only [cut-suffix])
     (exact (hmk-comp-upd-m hxm (drop-edges w (keep-prefix c has cid)) c
              (comp-cut-row has cut (bases-of (tbl-filter (suffix-edge c has cid) (:edges w))))
              (comp-cut-row-id has cut _) (comp-cut-row-pending has cut _)
              (fn [q :- CompRow, hq :- (= (hk-wt q) true)] hq) h1))))
(a/theorem hk-kx-found [kxy :- Nat, kxd :- Nat, w :- World, e2 :- EdgeRow]
  (=> (= (kx-rest kxy kxd w) true) (= (edge-find w kxy) (Option.some EdgeRow e2)) (= (:debtor e2) kxd))
  (intros h hf)
  (simp only [kx-rest Bool.and_eq_true] at h)
  (have m := (tbl-find-mem EdgeRow edge-id kxy e2 (:edges w) hf))
  (have i := (tbl-find-id EdgeRow edge-id kxy e2 (:edges w) hf))
  (have z := (tbl-all-mem EdgeRow (deb-at kxy kxd) e2 (:edges w) (And.right h) m))
  (have i2 (= (Nat.beq (:id e2) kxy) true)) (simp only [Nat.beq_eq]) (exact i)
  (simp only [deb-at i2 Bool.not_true Bool.false_or] at z)
  (exact (Nat.eq_of_beq_eq_true z)))
(a/theorem hk-u-kx [hxm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (hmk hxm w) true) (= (kx-rest (:id e) (:debtor e) w) true) (= (deb-final w (:debtor e)) true)
      (forall [e2 :- EdgeRow] (=> (= (edge-find w (:id e)) (Option.some EdgeRow e2)) (= (:marked e2) true) (= (hk-safe hxm (:comps w) (:creditor e2)) true))))
  (intros h k hf)
  (have nc := (hk-final-not-comp w (:debtor e) (hmk-sample hxm w h) hf))
  (apply (hk-u-of-unm hxm w (:id e)))
  (intros e2 hf2)
  (have dd := (hk-kx-found (:id e) (:debtor e) w e2 k hf2))
  (have nc2 (= (tbl-has comp-id (:debtor e2) (:comps w)) false)) (rw [dd]) (exact nc)
  (exact (hk-found-noncomp hxm w (:id e) e2 (hmk-rest-of hxm w h) hf2 nc2)))
(override! HMK 'inv-consume-entry '[inv-edge-upd inv-edge-set-phase]
  '(a/theorem hmk-consume-entry [hxm :- (List Nat), w :- World, e :- EdgeRow]
     (=> (= (kx-rest (:id e) (:debtor e) w) true) (= (hmk hxm w) true) (= (hmk hxm (consume-entry w e)) true))
     (intros k h)
     (cases hf (deb-final w (:debtor e)))
     (cases hr (Nat.beq (:cont e) cont-restart))
     (simp only [consume-entry hr hf])
     (exact (hmk-edge-upd hxm w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
              (edge-rearm-edge-id _ _) (edge-rearm-kind _ _) (edge-rearm-creditor _ _) (edge-rearm-debtor _ _) (edge-rearm-marked _ _) h))
     (simp only [consume-entry hr hf])
     (exact (hmk-edge-set-phase hxm w (:id e) ph-armed h))
     (simp only [consume-entry hf])
     (exact (hmk-remove-edge hxm w (:id e) (hk-u-kx hxm w e h k hf) h))))
(override! HMK 'inv-dispatch-raw '[inv-cancel-pred inv-cut-suffix inv-consume-entry inv-new-run-of]
  '(a/theorem hmk-dispatch-raw [hxm :- (List Nat), w :- World, c :- CompRow]
     (=> (List.Mem c (:comps w)) (= (Nat.beq (:done-epoch c) (:epoch c)) false) (= (gd w) true) (= (hmk hxm w) true)
         (= (hmk hxm (dispatch-raw w c)) true))
     (intros hm hd hg h)
     (have s0 := (hsw-start w c hg hm hd))
     (have s1 := (hsw-sif (:id c) (cancel-pred w c) (hsw-rest-of _ _ (hsw-cancel-pred (:id c) w c s0))))
     (have h1 := (hmk-cancel-pred hxm w c h))
     (cases he (entry-edge w (:id c)))
     (simp only [dispatch-raw he])
     (exact (hmk-new-run-of hxm (cut-suffix (cancel-pred w c) (:id c) false 0 0) c 0
              (hmk-cut-suffix hxm (cancel-pred w c) (:id c) false 0 0 s1 h1)))
     (rename_i e)
     (have k0 := (kx-of-mem w e (gd-sample w hg) (entry-mem w (:id c) e he)))
     (have k1 := (kx-cut-suffix (:id e) (:debtor e) (cancel-pred w c) (:id c) true (:at e) (:id e)
                   (kx-cancel-pred (:id e) (:debtor e) w c k0)))
     (simp only [dispatch-raw he])
     (exact (hmk-new-run-of hxm (consume-entry (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e) c (entry-ei e)
              (hmk-consume-entry hxm (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e
                (kx-rest-of _ _ _ k1)
                (hmk-cut-suffix hxm (cancel-pred w c) (:id c) true (:at e) (:id e) s1 h1))))))
(override! HMK 't11-inv '[inv-dispatch-raw]
  '(a/theorem t11-hmk [hxm :- (List Nat), w :- World, cid :- Nat, fresh :- Nat]
     (=> (= (gd w) true) (= (hmk hxm w) true) (= (hmk hxm (:world (t11-dispatch w cid fresh))) true))
     (intros hg h)
     (cases hc (comp-find w cid))
     (simp only [t11-dispatch hc refuse]) (exact h)
     (rename_i c)
     (cases hgg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))))
     (simp only [t11-dispatch hc hgg refuse]) (exact h)
     (have hg2 := hgg) (simp only [Bool.and_eq_true needs-run] at hg2)
     (have hd := (bnot-true _ (And.left (And.left (And.right (And.right hg2))))))
     (simp only [t11-dispatch hc hgg accept])
     (exact (hmk-dispatch-raw hxm w c (tbl-find-mem CompRow comp-id cid c (:comps w) hc) hd hg h))))

;; ===========================================================================
;; Part F. The bundle gives h-mark
;; ===========================================================================

(a/theorem hk-wt-waiting [c :- CompRow] (=> (= (hk-wt c) true) (= (comp-waiting c) true))
  (intro h)
  (simp only [hk-wt Bool.and_eq_true Bool.or_eq_true] at h)
  (have i := (bnot-true _ (And.left h)))
  (have l (= (comp-live c) false))
  (have q := (And.right h))
  (cases q)
  (rename_i z)
  (have ne (= (Nat.beq (:done-epoch c) (:epoch c)) false))
  (cases hb (Nat.beq (:done-epoch c) (:epoch c))) (rfl)
  (have e := (Nat.eq_of_beq_eq_true hb)) (have z2 := (gd-lt-of _ _ z)) (omega)
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
  (simp only [mark-ok hm waiting-at hf (And.left p) (hk-wt-waiting c z) Bool.not_true Bool.false_or Bool.and_self]))
(a/theorem hk-h-mark [w :- World] (=> (= (hmk (List.nil Nat) w) true) (= (h-mark w) true))
  (intro h)
  (have r := (hmk-rest-of _ w h)) (simp only [hmk-rest] at r)
  (simp only [h-mark])
  (exact (tbl-all-mono EdgeRow (hk-e (List.nil Nat) (:comps w)) (mark-ok w)
           (fn [e :- EdgeRow, he :- (= (hk-e (List.nil Nat) (:comps w) e) true)] (hk-mark-ok w e he)) (:edges w) r)))
(a/theorem hmk-empty [] (= (hmk (List.nil Nat) empty-world) true) (rfl))

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
  (=> (= (inv-sample w) true) (= (tbl-all (hk-jm P) (:edges w)) true) (= (tbl-all (hk-jm (hk-or-id y P)) (:edges (mark-edge w y))) true))
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
    (=> (= (inv-sample w) true) (= (tbl-all (hk-jm P) (:edges w)) true)
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
  (have r1 := (ih (mark-edge w y) (hk-or-id y P) (mark-edge-inv-sample w y hs) (hk-mark-J w y P hs h)))
  (apply (tbl-all-mono EdgeRow (hk-jm (hk-in t (hk-or-id y P))) (hk-jm (hk-in (List.cons Nat y t) P)) _ _ r1))
  (intros r hr)
  (apply (hk-jm-mono (hk-in t (hk-or-id y P)) (hk-in (List.cons Nat y t) P) r _ hr))
  (intros z hz)
  (cases hzy (Nat.beq z y))
  (simp only [hk-in reach-mem hzy] at hz) (simp only [hk-in hk-or-id hzy Bool.false_or]) (exact hz)
  (simp only [hk-in hk-or-id hzy Bool.true_or Bool.or_true]))

;; a fact about the edges or the computations that every mark-edge keeps survives the fold
(a/theorem hk-fold-mark-q [Q :- (=> World Bool),
                           hq :- (forall [w :- World, y :- Nat] (=> (= (inv-sample w) true) (= (Q w) true) (= (Q (mark-edge w y)) true))),
                           ts :- (List Nat)]
  (forall [w :- World] (=> (= (inv-sample w) true) (= (Q w) true) (= (Q (nat-fold mark-edge w ts)) true)))
  (induction ts)
  (case' [cons y t ih])
  (case' [nil])
  (intros w hs h) (simp only [nat-fold]) (exact h)
  (intros w hs h) (simp only [nat-fold]) (exact (ih (mark-edge w y) (mark-edge-inv-sample w y hs) (hq w y hs h))))
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
  (simp only [hk-wif hd hk-wt h2 pz Bool.not_true Bool.false_or Bool.not_false Bool.or_true Bool.true_and]))

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
  (intros d hx hd) (exact (hk-wif-upd d (:creditor e0) comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) hk-wt-inc (:comps w) hd))
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
(a/theorem hmk-fold-mark-x [hxm :- (List Nat), T :- (List Nat), ts :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (hk-memof T) ts) true) (= (tbl-all (hk-tg hxm T (:comps w)) (:edges w)) true)
                           (= (hmk hxm w) true) (= (hmk hxm (nat-fold mark-edge w ts)) true)))
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
  (exact (ih (mark-edge w y) (And.right hm) (hk-tg-mark hxm T w y ht) (hmk-mark-edge hxm w y mok h))))
(a/theorem hmk-discharge [hxm :- (List Nat), S :- (List Nat), w :- World]
  (=> (= (hmk (List.append Nat S hxm) w) true)
      (forall [d :- Nat] (=> (= (reach-mem d S) true) (= (tbl-has comp-id d (:comps w)) true) (= (tbl-all (hk-wif d) (:comps w)) true)))
      (= (hmk hxm w) true))
  (intros h hd)
  (have r := (hmk-rest-of _ w h)) (simp only [hmk-rest] at r)
  (have r2 (= (hmk-rest hxm w) true))
  (simp only [hmk-rest])
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
  (exact (hmk-intro hxm w (hmk-sample _ w h) r2)))

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
  (=> (= (inv-sample W1) true) (= (awake (:comps W1) d) true) (= (tbl-any (hk-ck d T) (:edges W1)) true)
      (= (tbl-all (hk-wif d) (:comps (nat-fold mark-edge W1 T))) true))
  (intros hs ha hk0)
  (have s2 := (nat-fold-inv mark-edge mark-edge-inv-sample T W1 hs))
  (have a2 := (hk-fold-mark-q (fn [q :- World] (awake (:comps q) d))
                (fn [w :- World, y :- Nat, h1 :- (= (inv-sample w) true), h2 :- (= (awake (:comps w) d) true)]
                  (hk-cs-mark (not-idle-if-id d) (fn [q :- CompRow, hq :- (= (not-idle-if-id d q) true)] hq) w y h2))
                T W1 hs ha))
  (have k2 := (hk-fold-mark-q (fn [q :- World] (tbl-any (hk-ck d T) (:edges q)))
                (fn [w :- World, y :- Nat, h1 :- (= (inv-sample w) true), h2 :- (= (tbl-any (hk-ck d T) (:edges w)) true)]
                  (hk-any-mark (hk-ck d T) (fn [r :- EdgeRow, hr :- (= (hk-ck d T r) true)] hr) w y h2))
                T W1 hs hk0))
  (have j2 := (hk-fold-J T W1 hk-none hs (hk-jm-none (:edges W1))))
  (have m2 := (any-mono-mem EdgeRow (hk-ck d T) (marks d) (:edges (nat-fold mark-edge W1 T))
                (fn [r :- EdgeRow, m :- (List.Mem r (:edges (nat-fold mark-edge W1 T))), hr :- (= (hk-ck d T r) true)]
                  (hk-marks-of d T r (tbl-all-mem EdgeRow (hk-jm (hk-in T hk-none)) r _ j2 m) hr))
                k2))
  (exact (hk-wif-marks _ d (And.left (inv-parts _ s2)) a2 m2)))

;; ---- T3 replace: the replaced computation is strong, the cone's creditors have a marked in-edge
(a/defn hk-rc [c :- Nat, r :- CompRow] Bool
  (Bool.or (Bool.not (Nat.beq (:id r) c)) (Bool.and (Bool.not (:idle r)) (Nat.blt (:done-epoch r) (:epoch r)))))
(a/theorem hk-rc-replace [w :- World, c :- Nat, i :- (List Nat), b :- Nat]
  (=> (= (gd w) true) (= (tbl-all (hk-rc c) (:comps (comp-upd w c (comp-replace-row i b)))) true))
  (intro h)
  (have p := (gdk-parts _ _ _ (gd-rest-of w h)))
  (have q := (And.right p)) (rw [all-gdkeys] at q)
  (simp only [comp-upd set-comps])
  (apply (tbl-all-upd CompRow comp-id c (comp-replace-row i b) (fn [x :- CompRow] (gd-c (:runs w) (:next-id w) (gdkey x))) (hk-rc c) _ _ (:comps w) q))
  (intros r hr hx)
  (have dl := (And.left (gd-c-parts _ _ _ hr))) (simp only [gd-dle gdkey Bool.and_eq_true] at dl)
  (have l1 := (gd-le-of _ _ (And.left dl)))
  (cases hi (:idle r))
  (have z (= (Nat.blt (:done-epoch r) (+ (:epoch r) 1)) true)) (apply gd-blt-of) (omega)
  (simp only [hk-rc comp-replace-row hi z Bool.not_false Bool.and_self Bool.or_true])
  (have z (= (Nat.blt 0 (+ (:epoch r) 1)) true)) (apply gd-blt-of) (omega)
  (simp only [hk-rc comp-replace-row hi z Bool.not_false Bool.and_self Bool.or_true])
  (intros r hr hx) (have hx2 (= (Nat.beq (:id r) c) false)) (exact hx) (simp only [hk-rc hx2 Bool.not_false Bool.true_or]))
(a/theorem hk-wif-rc [c :- Nat, cs :- (List CompRow)] (=> (= (tbl-all (hk-rc c) cs) true) (= (tbl-all (hk-wif c) cs) true))
  (intro h)
  (apply (tbl-all-mono CompRow (hk-rc c) (hk-wif c) _ cs h))
  (intros r hr)
  (cases hx (Nat.beq (:id r) c))
  (simp only [hk-wif hx Bool.not_false Bool.true_or])
  (simp only [hk-rc hx Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
  (simp only [hk-wif hx hk-wt (And.left hr) (And.right hr) Bool.not_true Bool.false_or Bool.true_or Bool.and_self]))
(a/theorem hk-awake-replace [w :- World, c :- Nat, i :- (List Nat), b :- Nat, d :- Nat]
  (=> (= (awake (:comps w) d) true) (= (awake (:comps (comp-upd w c (comp-replace-row i b))) d) true))
  (intro h)
  (simp only [awake comp-upd set-comps]) (simp only [awake] at h)
  (apply (tbl-all-upd CompRow comp-id c (comp-replace-row i b) (not-idle-if-id d) (not-idle-if-id d) _ _ (:comps w) h))
  (intros r hr hx) (simp only [not-idle-if-id comp-replace-row Bool.not_false Bool.or_true])
  (intros r hr hx) (exact hr))
(a/theorem hk-dep-cred-has [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) true) (= (tbl-has comp-id (:creditor e) (:comps w)) true))
  (intros h hm hk0)
  (have hok := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                 (And.left (And.right (inv-parts w h))) hm))
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
  (=> (= (inv-sample w) true) (= (comp-find w c) (Option.some CompRow row))
      (= (reach-mem d (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c))) true)
      (= (tbl-has comp-id d (:comps (comp-upd w c (comp-replace-row i b)))) true))
  (intros hs hf hd)
  (have hs1 := (inv-comp-upd w c (comp-replace-row i b) (comp-replace-row-id i b) (comp-replace-row-pending i b) hs))
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
  (=> (= (inv-sample W1) true) (forall [d :- Nat] (=> (= (reach-mem d S) true) (= (tbl-has comp-id d (:comps W1)) true)))
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
  (=> (= (inv-sample w) true) (= (g7-rest w) true) (= (reach-mem d (cone-set (comp-upd w c (comp-replace-row i b)) c)) true)
      (= (tbl-all (hk-wif d) (:comps (nat-fold mark-edge (comp-upd w c (comp-replace-row i b))
                                         (mark-targets (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c))
                                                       (:edges (comp-upd w c (comp-replace-row i b))))))) true))
  (intros hs h7 hd)
  (have hs1 := (inv-comp-upd w c (comp-replace-row i b) (comp-replace-row-id i b) (comp-replace-row-pending i b) hs))
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

(a/theorem hmk-mfr [hxm :- (List Nat), w :- World, c :- Nat, row :- CompRow, i :- (List Nat), b :- Nat]
  (=> (= (comp-find w c) (Option.some CompRow row)) (= (gd w) true) (= (g7 w) true) (= (hmk hxm w) true)
      (= (hmk hxm (mark-from (comp-upd w c (comp-replace-row i b)) c)) true))
  (intros hf hg h7 h)
  (have hs := (hmk-sample hxm w h))
  (have h1 := (hmk-comp-upd-m hxm w c (comp-replace-row i b) (comp-replace-row-id i b) (comp-replace-row-pending i b) (comp-replace-row-hkm i b) h))
  (have hs1 := (hmk-sample hxm _ h1))
  (have hx1 := (hmk-intro (List.append Nat (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) hxm) (comp-upd w c (comp-replace-row i b)) hs1
                 (hmk-rest-xm hxm _ (comp-upd w c (comp-replace-row i b))
                   (fn [d :- Nat, hd :- (= (reach-mem d hxm) true)] (rm-app-r d (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) hxm hd))
                   (hmk-rest-of hxm _ h1))))
  (have tg1 := (hk-tg-start hxm (comp-upd w c (comp-replace-row i b)) (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) hs1
                 (fn [d :- Nat, hd :- (= (reach-mem d (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c))) true)]
                   (hk-S-has w c row i b d hs hf hd))))
  (have h2 := (hmk-fold-mark-x _ _ (mark-targets (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) (:edges (comp-upd w c (comp-replace-row i b))))
                (comp-upd w c (comp-replace-row i b)) (hk-all-self _) tg1 hx1))
  (have rc := (hk-fold-mark-q (fn [q :- World] (tbl-all (hk-rc c) (:comps q)))
                (fn [w2 :- World, y :- Nat, a1 :- (= (inv-sample w2) true), a2 :- (= (tbl-all (hk-rc c) (:comps w2)) true)]
                  (hk-cs-mark (hk-rc c) (fn [q :- CompRow, hq :- (= (hk-rc c q) true)] hq) w2 y a2))
                (mark-targets (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) (:edges (comp-upd w c (comp-replace-row i b))))
                (comp-upd w c (comp-replace-row i b)) hs1 (hk-rc-replace w c i b hg)))
  (simp only [mark-from])
  (apply (hmk-discharge hxm (List.cons Nat c (cone-set (comp-upd w c (comp-replace-row i b)) c)) _ h2))
  (intros d hd hh)
  (cases hdc (Nat.beq d c))
  (simp only [reach-mem hdc] at hd)
  (exact (hk-cone-wif w c i b d hs (g7-rest-of w h7) hd))
  (have e := (Nat.eq_of_beq_eq_true hdc))
  (rw [e])
  (exact (hk-wif-rc c _ rc)))

(override! HMK 'inv-create-comp-raw '[]
  '(a/theorem hmk-create-comp-raw [hxm :- (List Nat), w :- World, c :- Nat, owner :- Nat, inputs :- (List Nat), body :- Nat]
     (=> (= (gd w) true) (= (g7 w) true) (= (hmk hxm w) true) (= (hmk hxm (create-comp-raw w c owner inputs body)) true))
     (intros hg h7 h)
     (cases hc (comp-find w c))
     (simp only [create-comp-raw hc])
     (exact (hmk-comp-ins hxm w (new-comp-row w (:next-id w) owner inputs body) (Eq.refl true) (rfl) (rfl) h))
     (rename_i row)
     (cases hi (nat-list-eq (:inputs row) inputs))
     (simp only [create-comp-raw hc hi])
     (exact (hmk-mfr hxm w c row inputs body hc hg h7 h))
     (simp only [create-comp-raw hc hi])
     (exact (hmk-comp-upd-m hxm w c comp-adopt-row comp-adopt-row-id comp-adopt-row-pending (fn [q :- CompRow, hq :- (= (hk-wt q) true)] hq) h))))
(override! HMK 't3-inv '[inv-create-comp-raw inv-record-basis inv-run-upd]
  '(a/theorem t3-hmk [hxm :- (List Nat), w :- World, st :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat]
     (=> (= (gd w) true) (= (g7 w) true) (= (hmk hxm w) true) (= (hmk hxm (:world (t3-create w st c inputs body))) true))
     (intros hg h7 h)
     (cases ht (tok-run w st))
     (simp only [t3-create ht refuse]) (exact h)
     (rename_i r)
     (cases hg2 (create-ok w c))
     (simp only [t3-create ht hg2 refuse]) (exact h)
     (simp only [t3-create ht hg2 accept])
     (exact (hmk-run-upd hxm _ (:id r) run-tick run-tick-run-id
              (hmk-record-basis hxm _ r c (hmk-create-comp-raw hxm w c (src-owner w r) inputs body hg h7 h))))))
(override! HMK 't3-top-inv '[inv-create-comp-raw]
  '(a/theorem t3-top-hmk [hxm :- (List Nat), w :- World, scope :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat]
     (=> (= (gd w) true) (= (g7 w) true) (= (hmk hxm w) true) (= (hmk hxm (:world (t3-create-top w scope c inputs body))) true))
     (intros hg h7 h)
     (cases hg2 (Bool.and (create-ok w c) (scope-open-at w scope)))
     (simp only [t3-create-top hg2 refuse]) (exact h)
     (simp only [t3-create-top hg2 accept])
     (exact (hmk-create-comp-raw hxm w c scope inputs body hg h7 h))))

;; ===========================================================================
;; Part H. The copy: every transition of raw0 except T2 (write) and T12 (complete), whose
;; overrides are open (notes/PLAN.md, branch hm); T3 and T11 take gd and g7 / gd
;; ===========================================================================

(doseq [r '[t1-full-inv t1-top-inv t7-inv t8-full-inv t8-unobserve-inv t9-inv t15-full-inv t17-inv t18-inv t19-inv
            t20-pin-inv t20-unpin-inv t3-inv t3-top-inv t4-inv t4-top-inv t5-inv t6-inv t11-inv sched-inv t22-inv t22-un-inv
            t-handle-new-inv t-deliver-inv t-post-inv t-take-inv t-release-inv t-finalize-inv t-cancel-inv t-release-world-inv
            t-open-scope-inv t-close-scope-inv t-detach-inv t-finally-enter-inv t-finally-exit-inv t-slice-exit-inv
            inv-cancel-losers inv-detach]]
  (lcopy! HMK r))
