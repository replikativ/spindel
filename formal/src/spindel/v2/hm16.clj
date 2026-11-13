(ns spindel.v2.hm16
  "T12 complete and settle for the h-mem2 bundle h3 (P11). IN PROGRESS: the undo of a computation's exemption."
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
            [spindel.v2.hm15 :refer :all]))


;; ---- undo of a computation's exemption x: no activation holds a run of x (the `of` role), x is free as a
;; member id, and every edge on x is unarmed, a host edge, or its debtor condition holds (hm6's h3-undo-d
;; with the no-holder premise for "x is no computation")
(a/theorem h16-undo-c [xm :- (List Nat), w :- World, x :- Nat]
  (=> (forall [a :- ActRow, r :- RunRow] (=> (List.Mem a (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run a)) (Not (= (:of r) x))))
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (:debtor e) x) (= (h3-dx (:comps w) (:tasks w) (:runs w) e) true)))
      (= (inv-sample w) true) (= (h3-free xm w x) true) (= (h3-rest (List.cons Nat x xm) w) true) (= (h3-rest xm w) true))
  (intros hcx hdx hsw hfr h)
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
        (have ir0 (= (:id r) (:run a))) (simp only [rk3] at hi) (exact (Nat.eq_of_beq_eq_true hi))
        (have of0 (= (:of r) x)) (exact (Nat.eq_of_beq_eq_true hb))
        (exact (False.elim (hcx a r ma mr ir0 of0)))
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
                  (case [inl q6]
                    (cases hdb (Nat.beq (:debtor e) x))
                    (case [false] (exact (Or.inl (h3-rm-cons-ne _ x xm q6 hdb))))
                    (case [true]
                      (have dx := (hdx e me (Nat.eq_of_beq_eq_true hdb)))
                      (have sk := (And.left q4))
                      (simp only [h3-s Bool.and_eq_true] at sk)
                      (simp only [h3-dx Bool.or_eq_true Bool.and_eq_true] at dx)
                      (cases dx)
                      (case [inl d1] (rw [(And.left sk)] at d1) (cases d1))
                      (case [inr d1]
                        (cases d1)
                        (case [inl d2]
                          (have c3 := (And.left (And.right (And.right sk))))
                          (simp only [(bnot-true _ (And.left d2)) Bool.false_or] at c3)
                          (have c0 := (Nat.eq_of_beq_eq_true (And.right d2)))
                          (have ca := (Nat.eq_of_beq_eq_true c3))
                          (have ap := (h3-act-id-pos w a hsw ma))
                          (rw [← ca c0] at ap) (simp only [Nat.beq_refl] at ap) (cases ap))
                        (case [inr d2] (exact (Or.inr d2))))))
                  (case [inr q6] (exact (Or.inr q6))))
                (exact (tbl-all-mem-mono EdgeRow _ _ (:edges w) ge (And.right q3)))))
            (exact (tbl-all-mem-mono Nat _ _ (act-contrib a) gx (And.right q2))))))))
  (exact (tbl-all-mem-mono RunRow _ _ (:runs w) gr (And.right ha)))
  (exact (tbl-all-mem-mono ActRow _ _ (:acts w) ga h)))
