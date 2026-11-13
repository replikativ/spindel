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

;; ---- the task half: a task's result row is final, so its on-task edges all fire and its exemption is undone
(a/theorem h16-trr-final [w :- World, k :- Nat, t :- TaskRow, res :- RunResult]
  (=> (= (inv-sample w) true) (= (task-find w k) (Option.some TaskRow t)) (= (Nat.beq (:tag res) res-none) false)
      (= (deb-final (task-upd w k (task-result-row res)) k) true))
  (intros hs ht hn)
  (have th := (tbl-find-has TaskRow task-id k t (:tasks w) ht))
  (have e1 (= (source-find (task-upd w k (task-result-row res)) k) (source-find w k))) (rfl)
  (have e2 (= (task-find (task-upd w k (task-result-row res)) k) (Option.some TaskRow (task-result-row res t))))
  (exact (tbl-find-upd-same TaskRow task-id k (task-result-row res) (task-result-row-id res) (:tasks w) t ht))
  (have tg (= (Nat.beq (:tag (:result (task-result-row res t))) res-none) false)) (exact hn)
  (cases hsf (source-find w k))
  (case [some s]
    (have sh := (tbl-find-has SourceRow source-id k s (:sources w) hsf))
    (have z := (h3-src-not-task w k hs sh)) (rw [th] at z) (cases z))
  (case [none] (simp only [deb-final e1 hsf e2 tg Bool.not_false])))
(a/theorem h16-tsq-cancel-res [w :- World, r :- RunRow] (h3-tsq w (cancel-res w r))
  (exact (And.intro (fold-tasks res-cancel (fn [w2 :- World, x2 :- Nat] (Eq.refl (:tasks w2))) (:resources r) w)
                    (fold-sources res-cancel (fn [w2 :- World, x2 :- Nat] (Eq.refl (:sources w2))) (:resources r) w))))
(a/theorem h16-complete-task-x [xm :- (List Nat), w :- World, r :- RunRow, t0 :- TaskRow, res :- RunResult]
  (=> (= (comp-find w (:of r)) (Option.none CompRow)) (= (task-find w (:of r)) (Option.some TaskRow t0))
      (= (Nat.beq (:tag res) res-none) false) (= (h3-free xm w (:of r)) true) (= (ekb w) true) (= (h3 (List.cons Nat (:of r) xm) w) true)
      (= (h3 xm (:world (complete-task w r (:of r) res))) true))
  (intros hc ht hn fr0 he h)
  (have hs := (h3-sample _ w h))
  (have hs1 := (inv-task-upd w (:of r) (task-result-row res) (task-result-row-id res) hs))
  (have hs2 := (inv-cancel-res (task-upd w (:of r) (task-result-row res)) r hs1))
  (have H7 := (nat-fold-h3 (List.cons Nat (:of r) xm) (fire-edge res) (h3-fire-edge (List.cons Nat (:of r) xm) res) (tbl-scan edge-id (on-task (:of r)) (:edges w)) (cancel-res (task-upd w (:of r) (task-result-row res)) r)
                (hm3-cancel-res (List.cons Nat (:of r) xm) (task-upd w (:of r) (task-result-row res)) r (h3-task-upd-m (List.cons Nat (:of r) xm) w (:of r) (task-result-row res) (task-result-row-id res)
                  (fn [q :- TaskRow] (Eq.refl (:run q))) h))))
  (have hcx (= (tbl-has comp-id (:of r) (:comps (nat-fold (fire-edge res) (cancel-res (task-upd w (:of r) (task-result-row res)) r) (tbl-scan edge-id (on-task (:of r)) (:edges w))))) false))
  (rw [hk-fold-fire-has]) (rw [hk-comps-cancel-res])
  (exact (tbl-find-none-has CompRow comp-id (:of r) (:comps w) hc))
  (have hfr := (fm-free xm w (nat-fold (fire-edge res) (cancel-res (task-upd w (:of r) (task-result-row res)) r) (tbl-scan edge-id (on-task (:of r)) (:edges w))) (:of r)
                 (fm-trans _ _ _ (fm-task-upd w (:of r) (task-result-row res)) (fm-trans _ _ _ (fm-cancel-res (task-upd w (:of r) (task-result-row res)) r) (fm-fire-fold res (tbl-scan edge-id (on-task (:of r)) (:edges w)) (cancel-res (task-upd w (:of r) (task-result-row res)) r)))) fr0))
  (have eE (= (:edges (cancel-res (task-upd w (:of r) (task-result-row res)) r)) (:edges w))) (exact (edges-res-fold (:resources r) (task-upd w (:of r) (task-result-row res))))
  (have hd1 := (h16-trr-final w (:of r) t0 res hs ht hn))
  (have hd2 (= (deb-final (cancel-res (task-upd w (:of r) (task-result-row res)) r) (:of r)) true)) (exact (Eq.trans (tsq-final (task-upd w (:of r) (task-result-row res)) (cancel-res (task-upd w (:of r) (task-result-row res)) r) (:of r) (h16-tsq-cancel-res (task-upd w (:of r) (task-result-row res)) r)) hd1))
  (have A6 := (qk-fold res (:of r) (tbl-scan edge-id (on-task (:of r)) (:edges w)) (cancel-res (task-upd w (:of r) (task-result-row res)) r) (List.nil Nat) hs2 hd2 (qk-nil (:of r) _)))
  (have B6 := (ek-nat-fold (fire-edge res) (ek-fire-edge res) (tbl-scan edge-id (on-task (:of r)) (:edges w)) (cancel-res (task-upd w (:of r) (task-result-row res)) r)))
  (simp only [hk-ek] at B6)
  (have C6 (= (tbl-all (h3-q1 (:of r)) (:edges (nat-fold (fire-edge res) (cancel-res (task-upd w (:of r) (task-result-row res)) r) (tbl-scan edge-id (on-task (:of r)) (:edges w))))) true))
  (apply all-of-mem) (intros e me)
  (cases hq (h3-q1 (:of r) e))
  (case [true] (rfl))
  (case [false]
    (have hq2 := hq)
    (simp only [h3-q1 Bool.or_eq_false_iff] at hq2)
    (have de := (bnot-false _ (And.left hq2)))
    (have kd := (bnot-false _ (And.left (And.right hq2))))
    (have tb := (tbl-all-mem EdgeRow _ e _ B6 me))
    (simp only [hk-back] at tb)
    (apply (any-elim EdgeRow (hk-kk e) _ _ tb))
    (intros e0 m0 k0)
    (rw [eE] at m0)
    (simp only [hk-kk Bool.and_eq_true] at k0)
    (have i0 := (Nat.eq_of_beq_eq_true (And.left k0)))
    (have j0 := (Nat.eq_of_beq_eq_true (And.left (And.right k0))))
    (have d0 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right (And.right k0))))))
    (have ot (= (on-task (:of r) e0) true))
    (simp only [on-task]) (rw [d0 j0]) (rw [(Nat.eq_of_beq_eq_true de)])
    (simp only [Nat.beq_refl Bool.true_and]) (simp only [Bool.or_eq_true] at kd) (simp only [Bool.or_eq_true]) (exact kd)
    (have ml := (scan-mem EdgeRow edge-id (on-task (:of r)) e0 _ m0 ot))
    (have ml2 (= (reach-mem (:id e) (List.append Nat (tbl-scan edge-id (on-task (:of r)) (:edges w)) (List.nil Nat))) true))
    (rw [reach-mem-append]) (rw [← i0]) (simp only [edge-id] at ml) (simp only [ml Bool.true_or])
    (have qk := (tbl-all-mem EdgeRow _ e _ A6 me))
    (simp only [h3-qk ml2 hq Bool.not_true Bool.false_or] at qk) (cases qk))
  (have E7 := (nat-fold-ekb (fire-edge res) (ekb-fire-edge res) (tbl-scan edge-id (on-task (:of r)) (:edges w)) (cancel-res (task-upd w (:of r) (task-result-row res)) r)
                (ekb-cancel-res (task-upd w (:of r) (task-result-row res)) r (ekb-task-upd w (:of r) (task-result-row res) (task-result-row-id res) he))))
  (have hdx (forall [e :- EdgeRow] (=> (List.Mem e (:edges (nat-fold (fire-edge res) (cancel-res (task-upd w (:of r) (task-result-row res)) r) (tbl-scan edge-id (on-task (:of r)) (:edges w))))) (= (:debtor e) (:of r))
                                       (= (h3-dx (:comps (nat-fold (fire-edge res) (cancel-res (task-upd w (:of r) (task-result-row res)) r) (tbl-scan edge-id (on-task (:of r)) (:edges w)))) (:tasks (nat-fold (fire-edge res) (cancel-res (task-upd w (:of r) (task-result-row res)) r) (tbl-scan edge-id (on-task (:of r)) (:edges w)))) (:runs (nat-fold (fire-edge res) (cancel-res (task-upd w (:of r) (task-result-row res)) r) (tbl-scan edge-id (on-task (:of r)) (:edges w)))) e) true))))
  (intros e me de)
  (exact (h3-dx-of _ _ _ (:of r) e de (tbl-all-mem EdgeRow _ e _ (ekb-rest-of _ E7) me) (tbl-all-mem EdgeRow _ e _ C6 me)))
  (simp only [complete-task])
  (exact (h3-intro xm _ (h3-sample _ _ H7) (h3-undo-d xm _ (:of r) hcx hdx (h3-sample _ _ H7) hfr (h3-rest-of _ _ H7)))))

;; ===========================================================================
;; The computation half: settle. A delivered dep edge is re-armed (dep-consumed), so the fact tracked for a
;; processed edge is "its id is free" (no obligated activation has it as a contributing member).
;; ===========================================================================

;; ---- after a fire, the fired dep edge's id is free
(a/theorem h16-free-inval [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) true) (= (h3-rest xm w) true)
      (= (h3-free xm (invalidate w e) (:id e)) true))
  (intros me hk hr)
  (show (= (h3-free xm (edge-upd (comp-upd w (:creditor e) comp-inc-epoch) (:id e) (edge-set-phase ph-fired)) (:id e)) true))
  (rw [h3-free-edge-upd]) (exact (h3-free-inc xm w e hr me hk)))
(a/theorem h16-free-deliver [xm :- (List Nat), w :- World, e :- EdgeRow, a :- ActRow]
  (=> (List.Mem a (:acts w)) (= (h3-freeb xm w (:id e) (:id a)) true)
      (= (h3-free xm (deliver-dep w e a) (:id e)) true))
  (intros ma fb0)
  (cases hd (deb-final w (:debtor e)))
  (case [false]
    (simp only [deliver-dep dep-consumed hd])
    (have fb1 := (h3-freeb-frame xm w (edge-upd w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))) (:id e) (:id a)
                   (Eq.refl (:acts w)) (Eq.refl (:runs w))
                   (fn [k :- RK3, q :- (= (tbl-any (h3-cur k) (:comps w)) true)] q) fb0))
    (have ma1 (List.Mem a (:acts (edge-upd w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e))))))) (exact ma)
    (exact (h3-free-fill xm (edge-upd w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))) a (:id e) (deb-result w (:debtor e)) ma1 fb1)))
  (case [true]
    (simp only [deliver-dep dep-consumed hd])
    (have hcb (forall [k :- RK3] (=> (= (tbl-any (h3-cur k) (:comps (remove-edge w (:id e)))) true) (= (tbl-any (h3-cur k) (:comps w)) true))))
    (intros k q) (exact (h3-cur-remove-edge w (:id e) k q))
    (have fb1 := (h3-freeb-frame xm w (remove-edge w (:id e)) (:id e) (:id a) (h3-acts-remove-edge w (:id e)) (runs-remove-edge w (:id e)) hcb fb0))
    (have ma1 (List.Mem a (:acts (remove-edge w (:id e))))) (rw [h3-acts-remove-edge]) (exact ma)
    (exact (h3-free-fill xm (remove-edge w (:id e)) a (:id e) (deb-result w (:debtor e)) ma1 fb1))))
(a/theorem h16-free-fire-dep [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) true) (= (h3 xm w) true)
      (= (h3-free xm (fire-dep w e) (:id e)) true))
  (intros hf hk h)
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) hf))
  (have hr := (h3-rest-of xm w h))
  (cases ha (act-with-member (:id e) (:acts w)))
  (case [none] (simp only [fire-dep ha]) (exact (h16-free-inval xm w e me hk hr)))
  (case [some a]
    (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
    (case [false] (simp only [fire-dep ha hc]) (exact (h16-free-inval xm w e me hk hr)))
    (case [true]
      (simp only [fire-dep ha hc])
      (exact (h16-free-deliver xm w e a (act-with-member-mem (:id e) (:acts w) a ha) (h3-freeb-of xm w e a hr me ha))))))

;; ---- a dep edge that is not (armed and member-current) is free: an obligated activation's member edge is
;; armed, its creditor the run's computation, the activation the first with this member, the run current
(a/theorem h16-free-nmc [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) true) (= (h3 xm w) true)
      (= (Bool.and (Nat.beq (:phase e) ph-armed) (member-current w e)) false)
      (= (h3-free xm w (:id e)) true))
  (intros hf hk h hn)
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) hf))
  (have hs := (h3-sample xm w h))
  (have hr := (h3-rest-of xm w h))
  (apply (h3-free-by xm w (:id e)))
  (intros b r mb mr ir hxo hcur hmem hxx)
  (have u := (h3-r-use xm w b r hr mb mr ir))
  (have ob := (And.right u))
  (simp only [h3-ob hxo hcur Bool.not_true Bool.false_or Bool.and_eq_true] at ob)
  (have hx := (tbl-all-mem Nat _ (:id e) (act-contrib b) (And.right ob) (Iff.mp (reach-mem-iff (:id e) (act-contrib b)) hmem)))
  (simp only [h3-x hxx Bool.false_or Bool.and_eq_true] at hx)
  (have ek := (tbl-all-mem EdgeRow _ e (:edges w) (And.right hx) me))
  (simp only [h3-eok Nat.beq_refl Bool.not_true Bool.false_or Bool.and_eq_true] at ek)
  (have sk := (And.left ek))
  (simp only [h3-s Bool.and_eq_true] at sk)
  (have arm := (And.left sk))
  (have cr := (And.left (And.right sk)))
  (simp only [hk Bool.not_true Bool.false_or] at cr)
  (have fst := (And.right (And.right (And.right sk))))
  (cases ha (act-with-member (:id e) (:acts w)))
  (case [none] (simp only [ha opt-test] at fst) (cases fst))
  (case [some a1]
    (simp only [ha opt-test h3-first] at fst)
    (have m1 := (act-with-member-mem (:id e) (:acts w) a1 ha))
    (have ua := (uniq-all ActRow act-id (fn [q :- ActRow] (Nat.beq (:run q) (:run b))) b (:acts w) (h3-acts-nodup w hs) mb (Nat.beq_refl (:run b))))
    (have u1 := (tbl-all-mem ActRow _ a1 (:acts w) ua m1))
    (have fst2 (= (Nat.beq (act-id a1) (act-id b)) true)) (exact fst)
    (simp only [same-id-then fst2 Bool.not_true Bool.false_or] at u1)
    (have ra (= (:run a1) (:id r))) (exact (Eq.trans (Nat.eq_of_beq_eq_true u1) (Eq.symm ir)))
    (have rc := (h3-cur-run-current xm w b r hs hr mb mr ir hcur))
    (have mc (= (member-current w e) true))
    (simp only [member-current ha run-current-of]) (rw [ra])
    (cases hq (run-find w (:id r)))
    (case [none]
      (have z := (tbl-find-none-has RunRow run-id (:id r) (:runs w) hq))
      (have z2 := (has-of-mem RunRow run-id r (:runs w) mr))
      (have z3 (= (tbl-has run-id (:id r) (:runs w)) true)) (exact z2)
      (rw [z] at z3) (cases z3))
    (case [some r2]
      (have p2 := (find-run-mem w (:id r) r2 hq))
      (have ur := (uniq-all RunRow run-id (fn [q :- RunRow] (Nat.beq (:of q) (:of r))) r (:runs w) (runs-nodup w hs) mr (Nat.beq_refl (:of r))))
      (have u2 := (tbl-all-mem RunRow _ r2 (:runs w) ur (And.left p2)))
      (have i2 (= (Nat.beq (run-id r2) (run-id r)) true)) (show (= (Nat.beq (:id r2) (:id r)) true)) (rw [(And.right p2)]) (exact (Nat.beq_refl _))
      (simp only [same-id-then i2 Bool.not_true Bool.false_or] at u2)
      (have o2 (= (Nat.beq (:of r2) (:creditor e)) true))
      (rw [(Nat.eq_of_beq_eq_true u2)]) (rw [beq-comm]) (exact cr)
      (simp only [o2 rc Bool.and_self]))
    (rw [arm mc] at hn) (cases hn)))

;; ---- the frame h3-fm through a settle
(a/theorem h16-fm-unmark [w :- World, x :- Nat] (h3-fm w (unmark-edge w x))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact (fm-refl w)))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact (fm-refl w)))
    (case [true]
      (simp only [unmark-edge hf hm])
      (exact (fm-trans _ _ _ (fm-edge-upd w x (edge-set-marked false))
               (fm-comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending comp-dec-pending-id
                 (fn [c :- CompRow] (Nat.le_refl (:epoch c)))))))))
(a/theorem h16-fm-settle-fire [ver :- Nat, w :- World, e :- EdgeRow] (h3-fm w (settle-fire ver w e))
  (cases hp (Nat.beq (:phase e) ph-armed))
  (case [false] (simp only [settle-fire hp]) (exact (fm-refl w)))
  (case [true]
    (cases hc (Bool.or (edge-behind ver e) (member-current w e)))
    (case [false] (simp only [settle-fire hp hc]) (exact (fm-refl w)))
    (case [true] (simp only [settle-fire hp hc]) (exact (fm-fire-dep w e)))))
(a/theorem h16-fm-settle-edge [ch :- Bool, ver :- Nat, w :- World, x :- Nat] (h3-fm w (settle-edge ch ver w x))
  (cases hf (edge-find w x))
  (case [none] (simp only [settle-edge hf]) (exact (fm-refl w)))
  (case [some e]
    (have se := (settle-edge-eq ch ver w x e hf)) (simp only [se])
    (exact (fm-trans _ _ _ (h16-fm-settle-fire ver w e) (h16-fm-unmark (settle-fire ver w e) x)))))
(a/theorem h16-fm-settle-one [w :- World, d :- Nat, ch :- Bool] (h3-fm w (settle-one w d ch))
  (simp only [settle-one settle-host])
  (exact (fm-trans _ _ _ (fm-nat-fold (settle-edge ch (deb-version w d)) (h16-fm-settle-edge ch (deb-version w d)) (tbl-scan edge-id (out-dep d) (:edges w)) w)
           (fm-fire-fold _ _ _))))

;; ---- strong is closed under the row edits of a settle
(a/theorem h16-sif-inc [d :- Nat, c :- CompRow] (=> (= (hk-sif d c) true) (= (hk-sif d (comp-inc-epoch c)) true))
  (intro h)
  (cases hi (Nat.beq (:id c) d))
  (case [false] (have i2 (= (Nat.beq (:id (comp-inc-epoch c)) d) false)) (exact hi) (simp only [hk-sif i2 Bool.not_false Bool.true_or]))
  (case [true]
    (have i2 (= (Nat.beq (:id (comp-inc-epoch c)) d) true)) (exact hi)
    (simp only [hk-sif hi Bool.not_true Bool.false_or hk-strong Bool.or_eq_true] at h)
    (simp only [hk-sif i2 Bool.not_true Bool.false_or hk-strong Bool.or_eq_true])
    (cases h)
    (case [inl z] (apply Or.inl) (exact z))
    (case [inr z]
      (apply Or.inr)
      (have l := (gd-lt-of _ _ z))
      (apply gd-blt-of) (omega))))
(a/theorem h16-sif-dec [d :- Nat, c :- CompRow] (=> (= (hk-sif d c) true) (= (hk-sif d (comp-dec-pending c)) true))
  (intro h) (exact h))
(a/theorem h16-sif-setp [d :- Nat, c :- CompRow, n :- Nat] (=> (= (hk-sif d c) true) (= (hk-sif d (comp-set-pending n c)) true))
  (intro h) (exact h))
(a/theorem h16-sif-settle-fire [d :- Nat, ver :- Nat, w :- World, e :- EdgeRow]
  (=> (= (tbl-all (hk-sif d) (:comps w)) true) (= (tbl-all (hk-sif d) (:comps (settle-fire ver w e))) true))
  (intro h)
  (cases hp (Nat.beq (:phase e) ph-armed))
  (case [false] (simp only [settle-fire hp]) (exact h))
  (case [true]
    (cases hc (Bool.or (edge-behind ver e) (member-current w e)))
    (case [false] (simp only [settle-fire hp hc]) (exact h))
    (case [true] (simp only [settle-fire hp hc]) (exact (hk-cs-fire-dep (hk-sif d) (h16-sif-inc d) (h16-sif-dec d) (h16-sif-setp d) w e h)))))

;; ---- one settle-edge keeps h3 (the unmarked creditor is safe) and leaves the edge's id free
(a/theorem h16-settle-edge-h3 [xm :- (List Nat), ch :- Bool, ver :- Nat, w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) true)))
      (forall [e :- EdgeRow, e2 :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (edge-find (settle-fire ver w e) x) (Option.some EdgeRow e2))
                                               (= (:marked e2) true) (= (hk-safe xm (:comps (settle-fire ver w e)) (:creditor e2)) true)))
      (= (h3 xm w) true) (= (h3 xm (settle-edge ch ver w x)) true))
  (intros hkind hsafe h)
  (cases hf (edge-find w x))
  (case [none] (simp only [settle-edge hf]) (exact h))
  (case [some e]
    (have se := (settle-edge-eq ch ver w x e hf)) (simp only [se])
    (have ie (= (:id e) x)) (exact (tbl-find-id EdgeRow edge-id x e (:edges w) hf))
    (have hf2 (= (edge-find w (:id e)) (Option.some EdgeRow e))) (rw [ie]) (exact hf)
    (have h1 (= (h3 xm (settle-fire ver w e)) true))
    (cases hp (Nat.beq (:phase e) ph-armed))
    (case [false] (simp only [settle-fire hp]) (exact h))
    (case [true]
      (cases hc (Bool.or (edge-behind ver e) (member-current w e)))
      (case [false] (simp only [settle-fire hp hc]) (exact h))
      (case [true] (simp only [settle-fire hp hc]) (exact (h3-fire-dep xm w e hf2 (hkind e hf) h))))
    (have hu (forall [e2 :- EdgeRow] (=> (= (edge-find (settle-fire ver w e) x) (Option.some EdgeRow e2)) (= (:marked e2) true)
                                         (= (hk-safe xm (:comps (settle-fire ver w e)) (:creditor e2)) true))))
    (intros e2 q1 q2) (exact (hsafe e e2 hf q1 q2))
    (exact (h3-unmark-edge xm (settle-fire ver w e) x hu h1))))
(a/theorem h16-settle-edge-free [xm :- (List Nat), ch :- Bool, ver :- Nat, w :- World, x :- Nat]
  (=> (forall [e :- EdgeRow] (=> (= (edge-find w x) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) true)))
      (= (h3 xm w) true) (= (h3-free xm (settle-edge ch ver w x) x) true))
  (intros hkind h)
  (cases hf (edge-find w x))
  (case [none]
    (simp only [settle-edge hf])
    (exact (h3-free-noedge xm w x (h3-rest-of xm w h) (tbl-find-none-has EdgeRow edge-id x (:edges w) hf))))
  (case [some e]
    (have se := (settle-edge-eq ch ver w x e hf)) (simp only [se])
    (have ie (= (:id e) x)) (exact (tbl-find-id EdgeRow edge-id x e (:edges w) hf))
    (have hf2 (= (edge-find w (:id e)) (Option.some EdgeRow e))) (rw [ie]) (exact hf)
    (have hk := (hkind e hf))
    (have f1 (= (h3-free xm (settle-fire ver w e) (:id e)) true))
    (cases hp (Nat.beq (:phase e) ph-armed))
    (case [false]
      (simp only [settle-fire hp])
      (have hn (= (Bool.and (Nat.beq (:phase e) ph-armed) (member-current w e)) false)) (simp only [hp Bool.false_and])
      (exact (h16-free-nmc xm w e hf2 hk h hn)))
    (case [true]
      (cases hc (Bool.or (edge-behind ver e) (member-current w e)))
      (case [false]
        (simp only [settle-fire hp hc])
        (have hc2 := hc) (simp only [Bool.or_eq_false_iff] at hc2)
        (have hn (= (Bool.and (Nat.beq (:phase e) ph-armed) (member-current w e)) false)) (simp only [(And.right hc2) Bool.and_false])
        (exact (h16-free-nmc xm w e hf2 hk h hn)))
      (case [true] (simp only [settle-fire hp hc]) (exact (h16-free-fire-dep xm w e hf2 hk h))))
    (rw [ie] at f1)
    (exact (fm-free xm (settle-fire ver w e) (unmark-edge (settle-fire ver w e) x) x (h16-fm-unmark (settle-fire ver w e) x) f1))))

;; ---- an edge found under a scanned id is a dep edge on d
(a/theorem h16-xin-kind [W :- World, Wk :- World, x :- Nat, d :- Nat, e :- EdgeRow]
  (=> (= (nat-nodup (tbl-ids edge-id (:edges W))) true) (= (hk-ek (:edges W) (:edges Wk)) true) (= (hk-xin d (:edges W) x) true)
      (= (edge-find Wk x) (Option.some EdgeRow e))
      (And (= (Nat.beq (:kind e) ek-dep) true) (= (:debtor e) d)))
  (intros hn hek hx hf)
  (have me := (tbl-find-mem EdgeRow edge-id x e (:edges Wk) hf))
  (have ie (= (:id e) x)) (exact (tbl-find-id EdgeRow edge-id x e (:edges Wk) hf))
  (simp only [hk-ek] at hek)
  (have b := (tbl-all-mem EdgeRow (hk-back (:edges W)) e (:edges Wk) hek me))
  (simp only [hk-back] at b)
  (apply (any-elim EdgeRow (hk-kk e) _ (:edges W) b))
  (intros e1 m1 k1)
  (simp only [hk-kk Bool.and_eq_true] at k1)
  (have i1 := (Nat.eq_of_beq_eq_true (And.left k1)))
  (have kd1 := (Nat.eq_of_beq_eq_true (And.left (And.right k1))))
  (have d1 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right (And.right k1))))))
  (simp only [hk-xin] at hx)
  (apply (any-elim EdgeRow (hk-sq edge-id (out-dep d) x) _ (:edges W) hx))
  (intros e2 m2 h2)
  (simp only [hk-sq Bool.and_eq_true] at h2)
  (have u := (uniq-all EdgeRow edge-id (out-dep d) e2 (:edges W) hn m2 (And.right h2)))
  (have ur := (tbl-all-mem EdgeRow _ e1 (:edges W) u m1))
  (have i2 (= (:id e2) x)) (exact (Nat.eq_of_beq_eq_true (And.left h2)))
  (have i3 (= (Nat.beq (edge-id e1) (edge-id e2)) true))
  (show (= (Nat.beq (:id e1) (:id e2)) true)) (rw [i1]) (rw [ie]) (rw [i2]) (exact (Nat.beq_refl _))
  (simp only [same-id-then i3 Bool.not_true Bool.false_or] at ur)
  (simp only [out-dep Bool.and_eq_true] at ur)
  (apply And.intro)
  (rw [← kd1]) (exact (And.left ur))
  (rw [← d1]) (exact (Nat.eq_of_beq_eq_true (And.right ur))))
