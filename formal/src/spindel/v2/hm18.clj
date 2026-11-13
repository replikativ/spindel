(ns spindel.v2.hm18
  "Rule R for the h-mem2 bundle h3 (P11): detach, the normalization pass (demote), the filter."
  (:require [ansatz.core :as a]
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
            [spindel.v2.hm :refer :all]
            [spindel.v2.i10 :refer :all]
            [spindel.v2.ar :refer :all]
            [spindel.v2.hmk2 :refer :all]
            [spindel.v2.hmk :refer :all]
            [spindel.v2.hm3 :refer :all]
            [spindel.v2.hm5 :refer :all]
            [spindel.v2.hm6 :refer :all]
            [spindel.v2.hm6-base :refer :all]
            [spindel.v2.hm7 :refer :all]
            [spindel.v2.hm8 :refer :all]
            [spindel.v2.i5 :refer :all]
            [spindel.v2.i8 :refer :all]
            [spindel.v2.i1r :refer :all]
            [spindel.v2.hm4 :refer :all]
            [spindel.v2.hm9 :refer :all]
            [spindel.v2.l5 :refer :all]
            [spindel.v2.hm10 :refer :all]
            [spindel.v2.hm11 :refer :all]
            [spindel.v2.hm12 :refer :all]
            [spindel.v2.hm13 :refer :all]
            [spindel.v2.hm14 :refer :all]
            [spindel.v2.hm15 :refer :all]
            [spindel.v2.hm16 :refer :all]
            [spindel.v2.hm17 :refer :all]))


;; ---- detach: an orphan source is no computation (its finalize needs that); tasks and computations lose the owner
(a/theorem h18-detach-source [xm :- (List Nat), hx :- (List Nat), w :- World, x :- Nat]
  (=> (= (tbl-has comp-id x (:comps w)) false) (= (hmk hx w) true) (= (h3 xm w) true)
      (= (h3 xm (detach-source w x)) true))
  (intros hc hk h)
  (have h1 := (hm3-wake-closed xm (source-upd w x source-detach-row) x (hm3-source-upd xm w x source-detach-row source-detach-row-id h)))
  (have k1 := (hmk-wake-closed hx (source-upd w x source-detach-row) x (hmk-source-upd hx w x source-detach-row source-detach-row-id hk)))
  (have hc2 (= (tbl-has comp-id x (:comps (wake-closed (source-upd w x source-detach-row) x))) false))
  (exact (Eq.trans (hk-has-wake-closed (source-upd w x source-detach-row) x x) hc))
  (exact (h3-finalize-debtor xm hx (wake-closed (source-upd w x source-detach-row) x) x hc2 k1 h1)))
(a/theorem h18-fold-noc [xm :- (List Nat), hx :- (List Nat), xs :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (hk-noc (:comps w)) xs) true) (= (hmk hx w) true) (= (h3 xm w) true)
                           (= (h3 xm (nat-fold detach-source w xs)) true)))
  (induction xs)
  (case [nil] (intros w hn hk h) (simp only [nat-fold]) (exact h))
  (case [cons a t ih]
    (intros w hn hk h)
    (simp only [tbl-all Bool.and_eq_true] at hn)
    (have na := (And.left hn)) (simp only [hk-noc] at na)
    (have na2 := (bnot-true _ na))
    (simp only [nat-fold])
    (exact (ih (detach-source w a) (hk-noc-all (:comps w) (:comps (detach-source w a)) t (hk-has-detach-source w a) (And.right hn))
             (hmk-detach-source hx w a na2 hk) (h18-detach-source xm hx w a na2 hk h)))))
(a/theorem h18-detach-task [xm :- (List Nat), w :- World, x :- Nat] (=> (= (h3 xm w) true) (= (h3 xm (detach-task w x)) true))
  (intro h) (simp only [detach-task])
  (exact (h3-task-upd-m xm w x task-detach-row (fn [t :- TaskRow] (Eq.refl (task-id t))) (fn [t :- TaskRow] (Eq.refl (:run t))) h)))
(a/theorem h18-detach-comp [xm :- (List Nat), w :- World, x :- Nat] (=> (= (h3 xm w) true) (= (h3 xm (detach-comp w x)) true))
  (intro h) (simp only [detach-comp])
  (exact (h3-comp-upd-m xm w x comp-detach-row (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (:pending c)))
           (fn [c :- CompRow] (Nat.le_refl (:epoch c))) (fn [c :- CompRow, q :- (= (hk-wt c) true)] q)
           (fn [c :- CompRow, q :- (= (Nat.blt (:done-epoch c) (:epoch c)) true)] q) h)))
(a/theorem h18-detach [xm :- (List Nat), hx :- (List Nat), w :- World]
  (=> (= (hmk hx w) true) (= (h3 xm w) true) (= (h3 xm (detach w)) true))
  (intros hk h)
  (have n0 := (hk-sources-noc w (src-orphan w) (h3-sample xm w h)))
  (have h1 := (h18-fold-noc xm hx (tbl-scan source-id (src-orphan w) (:sources w)) w n0 hk h))
  (simp only [detach])
  (exact (nat-fold-h3 xm detach-comp (h18-detach-comp xm) (tbl-scan comp-id (comp-orphan w) (:comps w)) _
           (nat-fold-h3 xm detach-task (h18-detach-task xm) (tbl-scan task-id (task-orphan w) (:tasks w)) _ h1))))
