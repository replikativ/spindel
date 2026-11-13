(ns spindel.v2.hm4
  "h-mem2 through `world-step` (P11, second half), continued from spindel.v2.hm3 (the bundle `h3 xm`, its
  transfer machinery and the copier bundle `H3`), kernel-checked (Init only). IN PROGRESS (notes/PLAN.md,
  branch hm4): the fires.

  Part A. Free members after a fill: the first activation with member x is the only one that can be
  obliged to x (`h3-freeb-of`: every other holder is not obliging), a fill removes x from it
  (`h3-freeb-fill`), so x is free afterwards and a member-id exemption of x can be undone (`h3-undo-x`;
  an edge id is no computation and no debtor: `h3-edge-not`).
  Part B. The fires: deliver-dep (a final debtor: the member edge goes while x is exempt, the fill takes
  x out of its only holder, undo), fire-dep, fire-wait-act (no activation: free; not current: E1 makes the
  holder not current; current: exempt, fill, undo), fire-wait (host wait: creditor 0 is no activation),
  fire-edge."
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
            [spindel.v2.hmk2 :refer :all]
            [spindel.v2.hm3 :refer :all]
            [spindel.v2.ar :refer :all]))

;; ===========================================================================
;; Part A. Free members after a fill; undoing a member-id exemption
;; ===========================================================================

(a/theorem h3-fill-contrib [x :- Nat, ms :- (List Member)]
  (= (reach-mem x (member-edges (tbl-filter (mem-other x) ms))) false)
  (induction ms)
  (case [nil] (simp only [tbl-filter member-edges reach-mem]))
  (case [cons hd t ih]
    (cases hm (mem-other x hd))
    (case [false] (simp only [tbl-filter hm ih]))
    (case [true]
      (simp only [mem-other] at hm)
      (have ne (= (Nat.beq x (:edge hd)) false)) (rw [beq-comm]) (exact (bnot-true _ hm))
      (have hm2 (= (mem-other x hd) true)) (simp only [mem-other (bnot-true _ hm) Bool.not_false])
      (simp only [tbl-filter hm2 member-edges reach-mem-cons ne ih Bool.false_or]))))
(a/theorem h3-fill-contrib-act [x :- Nat, v :- RunResult, b :- ActRow] (= (reach-mem x (act-contrib (act-fill x v b))) false)
  (simp only [act-contrib act-fill]) (exact (h3-fill-contrib x (:members b))))

;; every activation other than aid is not obliged to member x
(a/defn h3-fb [xm :- (List Nat), w :- World, x :- Nat, aid :- Nat, b :- ActRow] Bool (Bool.or (Nat.beq (:id b) aid) (h3-fa xm w x b)))
(a/defn h3-freeb [xm :- (List Nat), w :- World, x :- Nat, aid :- Nat] Bool (tbl-all (h3-fb xm w x aid) (:acts w)))

(a/theorem h3-freeb-of [xm :- (List Nat), w :- World, e :- EdgeRow, a :- ActRow]
  (=> (= (h3-rest xm w) true) (List.Mem e (:edges w)) (= (act-with-member (:id e) (:acts w)) (Option.some ActRow a))
      (= (h3-freeb xm w (:id e) (:id a)) true))
  (intros h me ha)
  (simp only [h3-freeb])
  (apply all-of-mem) (intros b mb)
  (cases hb (Nat.beq (:id b) (:id a)))
  (case [true] (simp only [h3-fb hb Bool.true_or]))
  (case [false]
    (simp only [h3-fb hb Bool.false_or h3-fa])
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
              (have f1 := (And.right (And.right (And.right sk))))
              (rw [ha] at f1)
              (simp only [opt-test h3-first] at f1)
              (rw [beq-comm] at f1) (rw [hb] at f1) (cases f1))))))))

;; transfer of a free-ness fact: comps keep currency backward, runs keyed alike
(a/theorem h3-fr-back [xm :- (List Nat), w :- World, w2 :- World, x :- Nat, b :- ActRow, r :- RunRow]
  (=> (forall [k :- RK3] (=> (= (tbl-any (h3-cur k) (:comps w2)) true) (= (tbl-any (h3-cur k) (:comps w)) true)))
      (= (h3-fr xm w x b r) true) (= (h3-fr xm w2 x b r) true))
  (intros hc h)
  (simp only [h3-fr Bool.or_eq_true] at h) (simp only [h3-fr Bool.or_eq_true])
  (cases h)
  (case [inl z] (exact (Or.inl z)))
  (case [inr z]
    (apply Or.inr)
    (cases z)
    (case [inl z2] (exact (Or.inl z2)))
    (case [inr z2]
      (apply Or.inr)
      (cases z2)
      (case [inl z3]
        (apply Or.inl)
        (cases c2 (tbl-any (h3-cur (rk3 r)) (:comps w2)))
        (case [false] (rfl))
        (case [true] (have q := (hc (rk3 r) c2)) (rw [q] at z3) (cases z3)))
      (case [inr z3] (exact (Or.inr z3))))))
(a/theorem h3-fr-rk [xm :- (List Nat), w :- World, x :- Nat, b :- ActRow, q :- RunRow, r :- RunRow]
  (=> (= (rk3 q) (rk3 r)) (= (h3-fr xm w x b q) (h3-fr xm w x b r)))
  (intro e)
  (have e1 (= (:id q) (:id r))) (exact (congrArg (fn [k :- RK3] (:id k)) e))
  (have e2 (= (:of q) (:of r))) (exact (congrArg (fn [k :- RK3] (:of k)) e))
  (simp only [h3-fr e1 e2]) (rw [e]))
(a/theorem h3-fa-back [xm :- (List Nat), w :- World, w2 :- World, x :- Nat, b :- ActRow]
  (=> (= (:runs w2) (:runs w))
      (forall [k :- RK3] (=> (= (tbl-any (h3-cur k) (:comps w2)) true) (= (tbl-any (h3-cur k) (:comps w)) true)))
      (= (h3-fa xm w x b) true) (= (h3-fa xm w2 x b) true))
  (intros er hc h)
  (simp only [h3-fa] at h) (simp only [h3-fa]) (rw [er])
  (have g (forall [r :- RunRow] (=> (= (h3-fr xm w x b r) true) (= (h3-fr xm w2 x b r) true))))
  (intros r hr) (exact (h3-fr-back xm w w2 x b r hc hr))
  (exact (tbl-all-mono RunRow _ _ g (:runs w) h)))
(a/theorem h3-freeb-frame [xm :- (List Nat), w :- World, w2 :- World, x :- Nat, aid :- Nat]
  (=> (= (:acts w2) (:acts w)) (= (:runs w2) (:runs w))
      (forall [k :- RK3] (=> (= (tbl-any (h3-cur k) (:comps w2)) true) (= (tbl-any (h3-cur k) (:comps w)) true)))
      (= (h3-freeb xm w x aid) true) (= (h3-freeb xm w2 x aid) true))
  (intros ea er hc h)
  (simp only [h3-freeb] at h) (simp only [h3-freeb]) (rw [ea])
  (have g (forall [b :- ActRow] (=> (= (h3-fb xm w x aid b) true) (= (h3-fb xm w2 x aid b) true))))
  (intros b hb)
  (simp only [h3-fb Bool.or_eq_true] at hb) (simp only [h3-fb Bool.or_eq_true])
  (cases hb)
  (case [inl z] (exact (Or.inl z)))
  (case [inr z] (exact (Or.inr (h3-fa-back xm w w2 x b er hc z))))
  (exact (tbl-all-mono ActRow _ _ g (:acts w) h)))

;; currency only reads the computations' (id, epoch): an edit of other fields keeps it backward
(a/theorem h3-cur-upd-back [k :- RK3, y :- Nat, f :- (=> CompRow CompRow),
                            hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                            hep :- (forall [c :- CompRow] (= (:epoch (f c)) (:epoch c))), cs :- (List CompRow)]
  (=> (= (tbl-any (h3-cur k) (tbl-upd comp-id y f cs)) true) (= (tbl-any (h3-cur k) cs) true))
  (intro h)
  (have g (forall [q :- CompRow] (=> (= (h3-cur k (f q)) true) (= (h3-cur k q) true))))
  (intros q z)
  (have e1 (= (:id (f q)) (:id q))) (exact (hid q))
  (simp only [h3-cur e1 (hep q)] at z) (simp only [h3-cur]) (exact z)
  (exact (h3-any-upd-back CompRow comp-id y f (h3-cur k) g cs h)))

(a/theorem h3-free-fill [xm :- (List Nat), w :- World, a :- ActRow, x :- Nat, v :- RunResult]
  (=> (List.Mem a (:acts w)) (= (h3-freeb xm w x (:id a)) true) (= (h3-free xm (fill-slot w a x v) x) true))
  (intros ma h)
  (simp only [h3-freeb] at h)
  (cases hr (act-ready (act-fill x v a)))
  (case [false]
    (simp only [fill-slot hr h3-free act-upd set-acts])
    (have hin (forall [b :- ActRow] (=> (= (h3-fb xm w x (:id a) b) true) (= (Nat.beq (act-id b) (:id a)) true)
                                       (= (h3-fa xm (set-acts w (tbl-upd act-id (:id a) (act-fill x v) (:acts w))) x (act-fill x v b)) true))))
    (intros b hb hx)
    (simp only [h3-fa])
    (apply all-of-mem) (intros r mr)
    (simp only [h3-fr h3-fill-contrib-act Bool.not_false Bool.true_or Bool.or_true])
    (have hout (forall [b :- ActRow] (=> (= (h3-fb xm w x (:id a) b) true) (= (Nat.beq (act-id b) (:id a)) false)
                                        (= (h3-fa xm (set-acts w (tbl-upd act-id (:id a) (act-fill x v) (:acts w))) x b) true))))
    (intros b hb hx)
    (have hx2 (= (Nat.beq (:id b) (:id a)) false)) (exact hx)
    (simp only [h3-fb hx2 Bool.false_or] at hb)
    (exact (h3-fa-back xm w _ x b (rfl) (fn [k :- RK3, q :- (= (tbl-any (h3-cur k) (:comps w)) true)] q) hb))
    (exact (tbl-all-upd ActRow act-id (:id a) (act-fill x v) _ _ hin hout (:acts w) h)))
  (case [true]
    (simp only [fill-slot hr resume])
    (have hc (forall [k :- RK3] (=> (= (tbl-any (h3-cur k) (:comps (run-upd (drop-act w (:id a)) (:run a) run-wake))) true)
                                    (= (tbl-any (h3-cur k) (:comps w)) true))))
    (intros k q)
    (simp only [run-upd drop-act act-del drop-cred-edges comp-upd set-runs set-acts set-comps set-edges] at q)
    (exact (h3-cur-upd-back k (:id a) (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (:epoch c))) (:comps w) q))
    (have hout (forall [b :- ActRow] (=> (= (h3-fb xm w x (:id a) b) true) (= (Nat.beq (act-id b) (:id a)) false)
                                        (= (h3-fa xm (run-upd (drop-act w (:id a)) (:run a) run-wake) x b) true))))
    (intros b hb hx)
    (have hx2 (= (Nat.beq (:id b) (:id a)) false)) (exact hx)
    (simp only [h3-fb hx2 Bool.false_or h3-fa] at hb)
    (simp only [h3-fa run-upd drop-act act-del drop-cred-edges comp-upd set-runs set-acts set-comps set-edges])
    (have hin2 (forall [r :- RunRow] (=> (= (h3-fr xm w x b r) true) (= (Nat.beq (run-id r) (:run a)) true)
                                        (= (h3-fr xm (run-upd (drop-act w (:id a)) (:run a) run-wake) x b (run-wake r)) true))))
    (intros r q hq)
    (rw [(h3-fr-rk xm (run-upd (drop-act w (:id a)) (:run a) run-wake) x b (run-wake r) r (rfl))])
    (exact (h3-fr-back xm w _ x b r hc q))
    (have hout2 (forall [r :- RunRow] (=> (= (h3-fr xm w x b r) true) (= (Nat.beq (run-id r) (:run a)) false)
                                         (= (h3-fr xm (run-upd (drop-act w (:id a)) (:run a) run-wake) x b r) true))))
    (intros r q hq) (exact (h3-fr-back xm w _ x b r hc q))
    (exact (tbl-all-upd RunRow run-id (:run a) run-wake _ _ hin2 hout2 (:runs w) hb))
    (simp only [h3-free run-upd drop-act act-del drop-cred-edges comp-upd set-runs set-acts set-comps set-edges])
    (exact (tbl-all-del ActRow act-id (:id a) _ _ hout (:acts w) h))))

;; an edge id is no computation, task, source or resource id; hence no edge's debtor
(a/theorem h3-edge-not-comp [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (tbl-has edge-id x (:edges w)) true) (= (tbl-has comp-id x (:comps w)) false))
  (intros h he)
  (cases hc (tbl-has comp-id x (:comps w)))
  (case [false] (rfl))
  (case [true]
    (have u := (ids-unique-of w h))
    (simp only [all-ids] at u)
    (have u2 := (nat-nodup-app-right _ _ u))
    (have hm (= (nat-mem x (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hc)
    (have hm2 (= (nat-mem x (tbl-ids edge-id (:edges w))) true)) (rw [nat-mem-ids]) (exact he)
    (have d := (nodup-app-disj x _ _ u2 hm))
    (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
    (have d2 := (And.left (And.right (And.right (And.right d)))))
    (rw [hm2] at d2) (cases d2)))
(a/theorem h3-edge-not-task [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (tbl-has edge-id x (:edges w)) true) (= (tbl-has task-id x (:tasks w)) false))
  (intros h he)
  (cases hc (tbl-has task-id x (:tasks w)))
  (case [false] (rfl))
  (case [true]
    (have u := (ids-unique-of w h))
    (simp only [all-ids] at u)
    (have u2 := (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ u)))
    (have hm (= (nat-mem x (tbl-ids task-id (:tasks w))) true)) (rw [nat-mem-ids]) (exact hc)
    (have hm2 (= (nat-mem x (tbl-ids edge-id (:edges w))) true)) (rw [nat-mem-ids]) (exact he)
    (have d := (nodup-app-disj x _ _ u2 hm))
    (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
    (have d2 := (And.left (And.right (And.right d))))
    (rw [hm2] at d2) (cases d2)))
(a/theorem h3-edge-not-source [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (tbl-has edge-id x (:edges w)) true) (= (tbl-has source-id x (:sources w)) false))
  (intros h he)
  (cases hc (tbl-has source-id x (:sources w)))
  (case [false] (rfl))
  (case [true]
    (have u := (ids-unique-of w h))
    (simp only [all-ids] at u)
    (have u2 := (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ u)))))
    (have hm (= (nat-mem x (tbl-ids source-id (:sources w))) true)) (rw [nat-mem-ids]) (exact hc)
    (have hm2 (= (nat-mem x (tbl-ids edge-id (:edges w))) true)) (rw [nat-mem-ids]) (exact he)
    (have d := (nodup-app-disj x _ _ u2 hm))
    (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
    (have d2 := (And.left d))
    (rw [hm2] at d2) (cases d2)))
(a/theorem h3-edge-not-res [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (tbl-has edge-id x (:edges w)) true) (= (tbl-has resource-id x (:res w)) false))
  (intros h he)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have u2 := (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ u))))))
  (have hm2 (= (nat-mem x (tbl-ids edge-id (:edges w))) true)) (rw [nat-mem-ids]) (exact he)
  (have d := (nodup-app-disj x _ _ u2 hm2))
  (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
  (have d2 := (And.left (And.right d)))
  (rw [nat-mem-ids] at d2) (exact d2))
(a/defn h3-ndx [x :- Nat, e :- EdgeRow] Bool (Bool.not (Nat.beq (:debtor e) x)))
(a/theorem h3-edge-not-debtor [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (tbl-has edge-id x (:edges w)) true) (= (tbl-all (h3-ndx x) (:edges w)) true))
  (intros h he)
  (have ok := (And.left (And.right (inv-parts w h))))
  (simp only [edges-ref-ok edges-ref-ok-in] at ok)
  (apply all-of-mem) (intros e me)
  (have k := (tbl-all-mem EdgeRow _ e (:edges w) ok me))
  (simp only [edge-ok deb-ok Bool.and_eq_true Bool.or_eq_true] at k)
  (have k2 := (And.right k))
  (cases hd (Nat.beq (:debtor e) x))
  (case [false] (simp only [h3-ndx hd Bool.not_false]))
  (case [true]
    (have ed := (Nat.eq_of_beq_eq_true hd))
    (rw [ed] at k2)
    (cases k2)
    (case [inl z] (rw [(h3-edge-not-comp w x h he)] at z) (cases z))
    (case [inr z]
      (cases z)
      (case [inl z2] (rw [(h3-edge-not-task w x h he)] at z2) (cases z2))
      (case [inr z2]
        (cases z2)
        (case [inl z3] (rw [(h3-edge-not-source w x h he)] at z3) (cases z3))
        (case [inr z3] (have z4 := (And.right z3)) (rw [(h3-edge-not-res w x h he)] at z4) (cases z4))))))

;; ===========================================================================
;; Part B. The fires
;; ===========================================================================

(a/theorem h3-free-self [xm :- (List Nat), w :- World, x :- Nat] (= (h3-free (List.cons Nat x xm) w x) true)
  (simp only [h3-free])
  (apply all-of-mem) (intros b mb)
  (simp only [h3-fa])
  (apply all-of-mem) (intros r mr)
  (simp only [h3-fr reach-mem-cons Nat.beq_refl Bool.true_or Bool.or_true]))
(a/theorem h3-xm-cons [xm :- (List Nat), x :- Nat, w :- World] (=> (= (h3 xm w) true) (= (h3 (List.cons Nat x xm) w) true))
  (intro h)
  (have g (forall [d :- Nat] (=> (= (reach-mem d xm) true) (= (reach-mem d (List.cons Nat x xm)) true))))
  (intros d q) (simp only [reach-mem-cons q Bool.or_true])
  (exact (h3-intro _ w (h3-sample xm w h) (h3-rest-xm xm _ w g (h3-rest-of xm w h)))))
(a/theorem hk-safe-nocomp [xm :- (List Nat), cs :- (List CompRow), d :- Nat]
  (=> (= (tbl-has comp-id d cs) false) (= (hk-safe xm cs d) true))
  (intro hc)
  (have ne := (has-false-ne CompRow comp-id d cs hc))
  (have g (forall [c :- CompRow] (=> (= (Bool.not (Nat.beq (comp-id c) d)) true) (= (hk-sif d c) true))))
  (intros c q) (simp only [comp-id] at q) (simp only [hk-sif q Bool.true_or])
  (have t (= (tbl-all (hk-sif d) cs) true)) (exact (tbl-all-mono CompRow _ _ g cs ne))
  (simp only [hk-safe t Bool.or_true]))

;; the h3-r facts of an activation's run, unfolded
(a/theorem h3-r-use [xm :- (List Nat), w :- World, b :- ActRow, r :- RunRow]
  (=> (= (h3-rest xm w) true) (List.Mem b (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run b))
      (And (= (tbl-all (h3-e1 (rk3 r)) (:comps w)) true) (= (h3-ob xm w b (rk3 r)) true)))
  (intros h mb mr ir)
  (have ha := (tbl-all-mem ActRow _ b (:acts w) h mb))
  (simp only [h3-a Bool.and_eq_true] at ha)
  (have hr := (tbl-all-mem RunRow _ r (:runs w) (And.right ha) mr))
  (simp only [h3-rr] at hr)
  (have i2 (= (Nat.beq (:id (rk3 r)) (:run b)) true)) (simp only [rk3 ir Nat.beq_refl])
  (simp only [h3-r i2 Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
  (exact (And.right hr)))
;; a current, non-exempt run's computation has done-epoch < epoch on every row
(a/theorem h3-cs-use [xm :- (List Nat), w :- World, b :- ActRow, r :- RunRow]
  (=> (= (h3-rest xm w) true) (List.Mem b (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run b))
      (= (reach-mem (:of r) xm) false) (= (tbl-any (h3-cur (rk3 r)) (:comps w)) true)
      (= (tbl-all (h3-cs (rk3 r)) (:comps w)) true))
  (intros h mb mr ir hx hc)
  (have ob := (And.right (h3-r-use xm w b r h mb mr ir)))
  (have hx2 (= (reach-mem (:of (rk3 r)) xm) false)) (exact hx)
  (simp only [h3-ob hx2 hc Bool.not_true Bool.false_or Bool.and_eq_true] at ob)
  (exact (And.left ob)))
;; a current run (h3's sense) is current for the engine's run-current
(a/theorem h3-cur-run-current [xm :- (List Nat), w :- World, b :- ActRow, r :- RunRow]
  (=> (= (inv-sample w) true) (= (h3-rest xm w) true) (List.Mem b (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run b))
      (= (tbl-any (h3-cur (rk3 r)) (:comps w)) true) (= (run-current w (:id r)) true))
  (intros hs h mb mr ir hc)
  (have e1 := (And.left (h3-r-use xm w b r h mb mr ir)))
  (cases hf (run-find w (:id r)))
  (case [none]
    (have z := (tbl-find-none-has RunRow run-id (:id r) (:runs w) hf))
    (rw [(tbl-find-has-mem w r mr)] at z) (cases z))
  (case [some r2]
    (have p := (find-run-mem w (:id r) r2 hf))
    (have sq := (run-same-ep w r r2 hs mr (And.left p) (And.right p)))
    (cases hg (comp-find w (:of r2)))
    (case [none] (simp only [run-current hf hg]))
    (case [some c2]
      (have mc2 := (tbl-find-mem CompRow comp-id (:of r2) c2 (:comps w) hg))
      (have ic2 (= (:id c2) (:of r2))) (exact (tbl-find-id CompRow comp-id (:of r2) c2 (:comps w) hg))
      (have q1 := (tbl-all-mem CompRow _ c2 (:comps w) e1 mc2))
      (have i3 (= (Nat.beq (:id c2) (:of (rk3 r))) true)) (try (simp only [rk3])) (rw [ic2 (And.right sq)]) (exact (Nat.beq_refl _))
      (simp only [h3-e1 i3 Bool.not_true Bool.false_or] at q1)
      (have l1 := (gd-le-of _ _ q1))
      (apply (any-elim CompRow (h3-cur (rk3 r)) _ (:comps w) hc))
      (intros c mc qc)
      (simp only [h3-cur Bool.and_eq_true] at qc)
      (have l2 := (gd-le-of _ _ (And.right qc)))
      (have ic (= (:id c) (:id c2))) (rw [ic2 (And.right sq)]) (exact (Nat.eq_of_beq_eq_true (And.left qc)))
      (have sm := (comp-same w c2 c hs mc2 mc ic))
      (have ee (= (:epoch r2) (:epoch c2))) (try (simp only [rk3] at l1)) (try (simp only [rk3] at l2)) (rw [(And.left sq)]) (omega)
      (simp only [run-current hf hg ee Nat.beq_refl]))))

;; a non-dep edge: only an activation with the creditor's id can be obliged to it
(a/theorem h3-freeb-cred [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (h3-rest xm w) true) (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) false)
      (= (h3-freeb xm w (:id e) (:creditor e)) true))
  (intros h me hk)
  (simp only [h3-freeb])
  (apply all-of-mem) (intros b mb)
  (cases hb (Nat.beq (:id b) (:creditor e)))
  (case [true] (simp only [h3-fb hb Bool.true_or]))
  (case [false]
    (simp only [h3-fb hb Bool.false_or h3-fa])
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
              (have c1 := (And.left (And.right (And.right sk))))
              (simp only [hk Bool.false_or] at c1)
              (rw [beq-comm] at c1) (rw [hb] at c1) (cases c1))))))))
(a/theorem h3-free-of-freeb [xm :- (List Nat), w :- World, x :- Nat, aid :- Nat]
  (=> (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (Nat.beq (:id b) aid) true) (= (h3-fa xm w x b) true)))
      (= (h3-freeb xm w x aid) true) (= (h3-free xm w x) true))
  (intros g h)
  (simp only [h3-freeb] at h) (simp only [h3-free])
  (have g2 (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (h3-fb xm w x aid b) true) (= (h3-fa xm w x b) true))))
  (intros b mb hb)
  (cases hi (Nat.beq (:id b) aid))
  (case [true] (exact (g b mb hi)))
  (case [false] (simp only [h3-fb hi Bool.false_or] at hb) (exact hb))
  (exact (tbl-all-mem-mono ActRow _ _ (:acts w) g2 h)))
;; the activation aid's runs are not current: it is obliged to nothing
(a/theorem h3-fa-ncur [xm :- (List Nat), w :- World, x :- Nat, b :- ActRow]
  (=> (= (inv-sample w) true) (= (h3-rest xm w) true) (List.Mem b (:acts w)) (= (run-current w (:run b)) false) (= (h3-fa xm w x b) true))
  (intros hs h mb hn)
  (simp only [h3-fa])
  (apply all-of-mem) (intros r mr)
  (simp only [h3-fr Bool.or_eq_true])
  (cases ir (Nat.beq (:id r) (:run b)))
  (case [false] (exact (Or.inl (rfl))))
  (case [true]
    (apply Or.inr) (apply Or.inr)
    (cases hc (tbl-any (h3-cur (rk3 r)) (:comps w)))
    (case [false] (exact (Or.inl (rfl))))
    (case [true]
      (have ir2 := (Nat.eq_of_beq_eq_true ir))
      (have q := (h3-cur-run-current xm w b r hs h mb mr ir2 hc))
      (rw [ir2 hn] at q) (cases q))))

;; ---- edges and computation ids through the edits of a fire
(a/theorem h3-acts-remove-edge [w :- World, x :- Nat] (= (:acts (remove-edge w x)) (:acts w))
  (cases hf (edge-find w x)) (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm comp-upd edge-del set-edges set-comps]))))
(a/theorem h3-cur-remove-edge [w :- World, x :- Nat, k :- RK3]
  (=> (= (tbl-any (h3-cur k) (:comps (remove-edge w x))) true) (= (tbl-any (h3-cur k) (:comps w)) true))
  (intro q)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf] at q) (exact q))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm edge-del set-edges] at q) (exact q))
    (case [true]
      (simp only [remove-edge hf hm comp-upd edge-del set-edges set-comps] at q)
      (exact (h3-cur-upd-back k (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (:epoch c))) (:comps w) q)))))
(a/theorem h3-ndx-remove-edge [w :- World, x :- Nat, y :- Nat]
  (=> (= (tbl-all (h3-ndx y) (:edges w)) true) (= (tbl-all (h3-ndx y) (:edges (remove-edge w x))) true))
  (intro h)
  (have g (forall [e :- EdgeRow] (=> (= (h3-ndx y e) true) (= (Nat.beq (edge-id e) x) false) (= (h3-ndx y e) true))))
  (intros e q hx) (exact q)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (all_goals (simp only [remove-edge hf hm comp-upd edge-del set-edges set-comps]))
    (all_goals (exact (tbl-all-del EdgeRow edge-id x _ _ g (:edges w) h)))))
(a/theorem h3-fill-edges [P :- (=> EdgeRow Bool), w :- World, a :- ActRow, x :- Nat, v :- RunResult]
  (=> (= (tbl-all P (:edges w)) true) (= (tbl-all P (:edges (fill-slot w a x v))) true))
  (intro h)
  (cases hr (act-ready (act-fill x v a)))
  (case [false] (simp only [fill-slot hr act-upd set-acts]) (exact h))
  (case [true]
    (simp only [fill-slot hr resume run-upd drop-act act-del drop-cred-edges comp-upd set-runs set-acts set-comps set-edges])
    (exact (tbl-all-filter EdgeRow P _ (:edges w) h))))
(a/theorem h3-fill-has [w :- World, a :- ActRow, x :- Nat, v :- RunResult, y :- Nat]
  (= (tbl-has comp-id y (:comps (fill-slot w a x v))) (tbl-has comp-id y (:comps w)))
  (cases hr (act-ready (act-fill x v a)))
  (case [false] (simp only [fill-slot hr act-upd set-acts]))
  (case [true]
    (simp only [fill-slot hr resume run-upd set-runs])
    (exact (hk-has-drop-act w (:id a) y))))

;; ---- exempt x, edit its edge, fill a, undo
(a/theorem h3-undo-fill [xm :- (List Nat), w :- World, w1 :- World, a :- ActRow, x :- Nat, v :- RunResult]
  (=> (= (inv-sample w) true) (= (tbl-has edge-id x (:edges w)) true)
      (= (h3 (List.cons Nat x xm) w1) true) (List.Mem a (:acts w1)) (= (h3-freeb xm w1 x (:id a)) true)
      (= (tbl-has comp-id x (:comps w1)) (tbl-has comp-id x (:comps w)))
      (= (tbl-all (h3-ndx x) (:edges w1)) true)
      (= (h3 xm (fill-slot w1 a x v)) true))
  (intros hs he h1 ma fb hc hd)
  (have h2 := (h3-fill-slot _ w1 a x v ma h1))
  (have fr := (h3-free-fill xm w1 a x v ma fb))
  (have hc2 (= (tbl-has comp-id x (:comps (fill-slot w1 a x v))) false))
  (rw [h3-fill-has hc]) (exact (h3-edge-not-comp w x hs he))
  (have hd2 := (h3-fill-edges (h3-ndx x) w1 a x v hd))
  (have hd3 (forall [e :- EdgeRow] (=> (List.Mem e (:edges (fill-slot w1 a x v))) (= (Nat.beq (:debtor e) x) false))))
  (intros e me) (have q := (tbl-all-mem EdgeRow _ e _ hd2 me)) (simp only [h3-ndx] at q) (exact (bnot-true _ q))
  (exact (h3-intro xm _ (h3-sample _ _ h2) (h3-undo-x xm _ x hc2 hd3 fr (h3-rest-of _ _ h2)))))

(a/theorem h3-deliver-safe [xm :- (List Nat), w :- World, e :- EdgeRow, a :- ActRow]
  (=> (= (act-with-member (:id e) (:acts w)) (Option.some ActRow a))
      (= (run-current-of w (:run a) (:creditor e)) true) (= (h3 xm w) true)
      (= (hk-safe (List.cons Nat (:id e) xm) (:comps w) (:creditor e)) true))
  (intros ha hcur h)
  (have ma := (act-with-member-mem (:id e) (:acts w) a ha))
    (simp only [run-current-of] at hcur)
    (cases hr (run-find w (:run a)))
    (simp only [hr] at hcur) (cases hcur)
      (rename_i r) (simp only [hr Bool.and_eq_true] at hcur)
      (have p := (find-run-mem w (:run a) r hr))
      (have eo := (Nat.eq_of_beq_eq_true (And.left hcur)))
      (cases hx (reach-mem (:of r) xm))
        (cases hg (comp-find w (:of r)))
          (have z := (tbl-find-none-has CompRow comp-id (:of r) (:comps w) hg))
          (rw [← eo]) (exact (hk-safe-nocomp _ _ _ z))
          (rename_i c)
          (have hcc := (And.right hcur)) (simp only [run-current hr hg] at hcc)
          (have mc := (tbl-find-mem CompRow comp-id (:of r) c (:comps w) hg))
          (have ic (= (:id c) (:of r))) (exact (tbl-find-id CompRow comp-id (:of r) c (:comps w) hg))
          (have cur (= (tbl-any (h3-cur (rk3 r)) (:comps w)) true))
          (apply (any-elim-of CompRow (h3-cur (rk3 r)) c (:comps w) mc))
          (have ee := (Nat.eq_of_beq_eq_true hcc))
          (simp only [h3-cur rk3 ic ee Nat.beq_refl gd-ble-refl Bool.and_self])
          (have cs := (h3-cs-use xm w a r (h3-rest-of xm w h) ma (And.left p) (And.right p) hx cur))
          (have g (forall [q :- CompRow] (=> (= (h3-cs (rk3 r) q) true) (= (hk-sif (:of r) q) true))))
          (intros q z)
          (simp only [h3-cs rk3 Bool.or_eq_true] at z) (simp only [hk-sif hk-strong Bool.or_eq_true])
          (cases z) (rename_i z1) (exact (Or.inl z1)) (rename_i z1) (exact (Or.inr (Or.inr z1)))
          (have t (= (tbl-all (hk-sif (:of r)) (:comps w)) true)) (exact (tbl-all-mono CompRow _ _ g (:comps w) cs))
          (rw [← eo]) (simp only [hk-safe t Bool.or_true])
          (rw [← eo]) (simp only [hk-safe reach-mem-cons hx Bool.true_or Bool.or_true]))

(a/theorem h3-deliver-dep [xm :- (List Nat), w :- World, e :- EdgeRow, a :- ActRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (act-with-member (:id e) (:acts w)) (Option.some ActRow a))
      (= (run-current-of w (:run a) (:creditor e)) true) (= (h3 xm w) true) (= (h3 xm (deliver-dep w e a)) true))
  (intros hf ha hcur h)
  (have hs := (h3-sample xm w h))
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) hf))
  (have ma := (act-with-member-mem (:id e) (:acts w) a ha))
  (cases hd (deb-final w (:debtor e)))
  (case [false]
    (simp only [deliver-dep dep-consumed hd])
    (have harm (forall [q :- EdgeRow] (=> (= (Nat.beq (:phase q) ph-armed) true)
                                          (= (Nat.beq (:phase (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)) q)) ph-armed) true))))
    (intros q z) (exact (Nat.beq_refl ph-armed))
    (have h1 := (h3-edge-upd-m xm w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
                  (edge-rearm-edge-id (deb-value w (:debtor e)) (deb-version w (:debtor e))) (edge-rearm-kind (deb-value w (:debtor e)) (deb-version w (:debtor e)))
                  (edge-rearm-creditor (deb-value w (:debtor e)) (deb-version w (:debtor e))) (edge-rearm-debtor (deb-value w (:debtor e)) (deb-version w (:debtor e)))
                  (edge-rearm-marked (deb-value w (:debtor e)) (deb-version w (:debtor e))) harm h))
    (exact (h3-fill-slot xm (edge-upd w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))) a (:id e) (deb-result w (:debtor e)) ma h1)))
  (case [true]
    (simp only [deliver-dep dep-consumed hd])
    (have h0 := (h3-xm-cons xm (:id e) w h))
    (have hu (forall [e2 :- EdgeRow] (=> (= (edge-find w (:id e)) (Option.some EdgeRow e2)) (= (:marked e2) true)
                                         (= (hk-safe (List.cons Nat (:id e) xm) (:comps w) (:creditor e2)) true))))
    (intros e2 hf2 hm2)
    (rw [hf] at hf2)
    (have ee (= e2 e)) (exact (Option.some.inj (Eq.symm hf2)))
    (rw [ee]) (exact (h3-deliver-safe xm w e a ha hcur h))
    (have h1 := (h3-remove-edge _ w (:id e) hu (h3-free-self xm w (:id e)) h0))
    (have fb0 := (h3-freeb-of xm w e a (h3-rest-of xm w h) me ha))
    (have hcb (forall [k :- RK3] (=> (= (tbl-any (h3-cur k) (:comps (remove-edge w (:id e)))) true) (= (tbl-any (h3-cur k) (:comps w)) true))))
    (intros k q) (exact (h3-cur-remove-edge w (:id e) k q))
    (have fb1 := (h3-freeb-frame xm w (remove-edge w (:id e)) (:id e) (:id a) (h3-acts-remove-edge w (:id e)) (runs-remove-edge w (:id e)) hcb fb0))
    (have ma1 (List.Mem a (:acts (remove-edge w (:id e))))) (rw [h3-acts-remove-edge]) (exact ma)
    (exact (h3-undo-fill xm w (remove-edge w (:id e)) a (:id e) (deb-result w (:debtor e)) hs (tbl-find-has-edge w e me) h1 ma1 fb1
             (hk-has-remove-edge w (:id e) (:id e)) (h3-ndx-remove-edge w (:id e) (:id e) (h3-edge-not-debtor w (:id e) hs (tbl-find-has-edge w e me)))))))

(a/theorem h3-fire-dep [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) true) (= (h3 xm w) true) (= (h3 xm (fire-dep w e)) true))
  (intros hf hk h)
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) hf))
  (cases ha (act-with-member (:id e) (:acts w)))
  (case [none] (simp only [fire-dep ha]) (exact (h3-invalidate xm w e me hk h)))
  (case [some a]
    (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
    (case [false] (simp only [fire-dep ha hc]) (exact (h3-invalidate xm w e me hk h)))
    (case [true]
      (simp only [fire-dep ha hc])
      (have hc1 (= (run-current-of w (:run a) (:creditor e)) true)) (simp only [Bool.and_eq_true] at hc) (exact (And.left hc))
      (exact (h3-deliver-dep xm w e a hf ha hc1 h)))))

(a/theorem h3-ndx-phase [x :- Nat, y :- Nat, p :- Nat, es :- (List EdgeRow)]
  (=> (= (tbl-all (h3-ndx y) es) true) (= (tbl-all (h3-ndx y) (tbl-upd edge-id x (edge-set-phase p) es)) true))
  (intro h)
  (have hin (forall [q :- EdgeRow] (=> (= (h3-ndx y q) true) (= (Nat.beq (edge-id q) x) true) (= (h3-ndx y (edge-set-phase p q)) true))))
  (intros q z hx) (exact z)
  (have hout (forall [q :- EdgeRow] (=> (= (h3-ndx y q) true) (= (Nat.beq (edge-id q) x) false) (= (h3-ndx y q) true))))
  (intros q z hx) (exact z)
  (exact (tbl-all-upd EdgeRow edge-id x (edge-set-phase p) _ _ hin hout es h)))
;; the phase change of a free edge
(a/theorem h3-phase-free [xm :- (List Nat), w :- World, x :- Nat, p :- Nat]
  (=> (= (h3-free xm w x) true) (= (h3 xm w) true) (= (h3 xm (edge-upd w x (edge-set-phase p))) true))
  (intros hfr h)
  (have hs := (h3-sample xm w h))
  (exact (h3-intro xm _ (inv-edge-set-phase w x p hs)
           (h3r-edge-upd-free xm w x (edge-set-phase p) (edge-set-phase-edge-id p) (h3-db-of w hs) hfr (h3-rest-of xm w h)))))

(a/theorem h3-fire-wait-act [xm :- (List Nat), res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) false) (= (h3 xm w) true)
      (= (h3 xm (fire-wait-act res w e)) true))
  (intros hf hk h)
  (have hs := (h3-sample xm w h))
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) hf))
  (have fbc := (h3-freeb-cred xm w e (h3-rest-of xm w h) me hk))
  (cases ha (act-find w (:creditor e)))
  (case [none]
    (have g (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (Nat.beq (:id b) (:creditor e)) true) (= (h3-fa xm w (:id e) b) true))))
    (intros b mb hb)
    (have z := (tbl-find-none-has ActRow act-id (:creditor e) (:acts w) ha))
    (have z2 := (has-of-mem ActRow act-id b (:acts w) mb))
    (have eb (= (act-id b) (:creditor e))) (exact (Nat.eq_of_beq_eq_true hb))
    (rw [eb z] at z2) (cases z2)
    (simp only [fire-wait-act ha])
    (exact (h3-phase-free xm w (:id e) ph-fired (h3-free-of-freeb xm w (:id e) (:creditor e) g fbc) h)))
  (case [some a]
    (have ma := (tbl-find-mem ActRow act-id (:creditor e) a (:acts w) ha))
    (have ia (= (:id a) (:creditor e))) (exact (tbl-find-id ActRow act-id (:creditor e) a (:acts w) ha))
    (cases hc (run-current w (:run a)))
    (case [false]
      (have g (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (Nat.beq (:id b) (:creditor e)) true) (= (h3-fa xm w (:id e) b) true))))
      (intros b mb hb)
      (have nr (= (Nat.beq (:run a) (:run a)) true)) (exact (Nat.beq_refl _))
      (have u := (uniq-all ActRow act-id (fn [q :- ActRow] (Nat.beq (:run q) (:run a))) a (:acts w) (h3-acts-nodup w hs) ma nr))
      (have ub := (tbl-all-mem ActRow _ b (:acts w) u mb))
      (have ib (= (Nat.beq (act-id b) (act-id a)) true)) (simp only [act-id]) (rw [ia]) (exact hb)
      (simp only [same-id-then ib Bool.not_true Bool.false_or] at ub)
      (have rb := (Nat.eq_of_beq_eq_true ub))
      (have hc2 (= (run-current w (:run b)) false)) (rw [rb]) (exact hc)
      (exact (h3-fa-ncur xm w (:id e) b hs (h3-rest-of xm w h) mb hc2))
      (simp only [fire-wait-act ha hc])
      (exact (h3-phase-free xm w (:id e) ph-fired (h3-free-of-freeb xm w (:id e) (:creditor e) g fbc) h)))
    (case [true]
      (simp only [fire-wait-act ha hc])
      (have h0 := (h3-xm-cons xm (:id e) w h))
      (have h1 := (h3-phase-free _ w (:id e) ph-fired (h3-free-self xm w (:id e)) h0))
      (have fb0 (= (h3-freeb xm w (:id e) (:id a)) true)) (rw [ia]) (exact fbc)
      (have hcb (forall [k :- RK3] (=> (= (tbl-any (h3-cur k) (:comps (edge-upd w (:id e) (edge-set-phase ph-fired)))) true) (= (tbl-any (h3-cur k) (:comps w)) true))))
      (intros k q) (exact q)
      (have fb1 := (h3-freeb-frame xm w (edge-upd w (:id e) (edge-set-phase ph-fired)) (:id e) (:id a) (rfl) (rfl) hcb fb0))
      (have hd := (h3-ndx-phase (:id e) (:id e) ph-fired (:edges w) (h3-edge-not-debtor w (:id e) hs (tbl-find-has-edge w e me))))
      (exact (h3-undo-fill xm w (edge-upd w (:id e) (edge-set-phase ph-fired)) a (:id e) res hs (tbl-find-has-edge w e me) h1 ma fb1 (rfl) hd)))))

(a/theorem h3-act-id-pos [w :- World, b :- ActRow] (=> (= (inv-sample w) true) (List.Mem b (:acts w)) (= (Nat.beq (:id b) 0) false))
  (intros h mb)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (exact (has-pos ActRow act-id (:id b) (:next-id w) (:acts w) (And.left (And.right (And.right (And.right (And.right (And.right (And.right hb)))))))
           (has-of-mem ActRow act-id b (:acts w) mb))))

(a/theorem h3-fire-wait [xm :- (List Nat), res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-wait) true) (= (h3 xm w) true)
      (= (h3 xm (fire-wait res w e)) true))
  (intros hf hk0 h)
  (have hs := (h3-sample xm w h))
  (have k1 := (Nat.eq_of_beq_eq_true hk0))
  (have nd (= (Nat.beq (:kind e) ek-dep) false)) (rw [k1])
  (cases hc (Nat.beq (:creditor e) 0))
  (case [false] (simp only [fire-wait hc]) (exact (h3-fire-wait-act xm res w e hf nd h)))
  (case [true]
    (simp only [fire-wait hc])
    (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) hf))
    (have ec := (Nat.eq_of_beq_eq_true hc))
    (have fbc := (h3-freeb-cred xm w e (h3-rest-of xm w h) me nd))
    (have g (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (Nat.beq (:id b) (:creditor e)) true) (= (h3-fa xm w (:id e) b) true))))
    (intros b mb hb)
    (rw [ec] at hb) (rw [(h3-act-id-pos w b hs mb)] at hb) (cases hb)
    (have fr := (h3-free-of-freeb xm w (:id e) (:creditor e) g fbc))
    (have hu (forall [e2 :- EdgeRow] (=> (= (edge-find w (:id e)) (Option.some EdgeRow e2)) (= (:marked e2) true)
                                         (= (hk-safe xm (:comps w) (:creditor e2)) true))))
    (intros e2 hf2 hm2)
    (rw [hf] at hf2)
    (have ee (= e2 e)) (exact (Option.some.inj (Eq.symm hf2)))
    (rw [ee ec]) (exact (hk-safe-nocomp xm (:comps w) 0 (comp-has-zero w hs)))
    (exact (h3-remove-edge xm w (:id e) hu fr h))))

(lcopy! H3 'inv-fire-observe)
(a/theorem h3-fire-edge [xm :- (List Nat), res :- RunResult, w :- World, x :- Nat]
  (=> (= (h3 xm w) true) (= (h3 xm (fire-edge res w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [fire-edge hf]) (exact h))
  (case [some e]
    (have hi (= (:id e) x)) (exact (tbl-find-id EdgeRow edge-id x e (:edges w) hf))
    (have hf2 (= (edge-find w (:id e)) (Option.some EdgeRow e))) (rw [hi]) (exact hf)
    (cases hp (Nat.beq (:phase e) ph-armed))
    (case [false] (simp only [fire-edge hf hp]) (exact h))
    (case [true]
      (cases hk1 (Nat.beq (:kind e) ek-dep))
      (case [true] (simp only [fire-edge hf hp hk1]) (exact (h3-fire-dep xm w e hf2 hk1 h)))
      (case [false]
        (cases hk2 (Nat.beq (:kind e) ek-wait))
        (case [true] (simp only [fire-edge hf hp hk1 hk2]) (exact (h3-fire-wait xm res w e hf2 hk2 h)))
        (case [false]
          (cases hk3 (Nat.beq (:kind e) ek-observe))
          (case [true] (simp only [fire-edge hf hp hk1 hk2 hk3]) (exact (hm3-fire-observe xm w e h)))
          (case [false] (simp only [fire-edge hf hp hk1 hk2 hk3 fire-savepoint-todo]) (exact h)))))))
(swap! (:renames H3) assoc 'inv-fire-edge 'h3-fire-edge 'inv-invalidate 'h3-invalidate 'inv-resume 'h3-resume 'inv-fill-slot 'h3-fill-slot)

;; ---- host edges (creditor 0) are held by no activation: T8 unobserve (g7's obs-one), T22 unawait
(a/theorem h3-remove-host [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) false) (= (:creditor e) 0) (= (h3 xm w) true)
      (= (h3 xm (remove-edge w (:id e))) true))
  (intros hf nd ec h)
  (have hs := (h3-sample xm w h))
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) hf))
  (have fbc := (h3-freeb-cred xm w e (h3-rest-of xm w h) me nd))
  (have g (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (Nat.beq (:id b) (:creditor e)) true) (= (h3-fa xm w (:id e) b) true))))
  (intros b mb hb)
  (rw [ec] at hb) (rw [(h3-act-id-pos w b hs mb)] at hb) (cases hb)
  (have fr := (h3-free-of-freeb xm w (:id e) (:creditor e) g fbc))
  (have hu (forall [e2 :- EdgeRow] (=> (= (edge-find w (:id e)) (Option.some EdgeRow e2)) (= (:marked e2) true)
                                       (= (hk-safe xm (:comps w) (:creditor e2)) true))))
  (intros e2 hf2 hm2)
  (rw [hf] at hf2)
  (have ee (= e2 e)) (exact (Option.some.inj (Eq.symm hf2)))
  (rw [ee ec]) (exact (hk-safe-nocomp xm (:comps w) 0 (comp-has-zero w hs)))
  (exact (h3-remove-edge xm w (:id e) hu fr h)))
(a/theorem h3-find-id [w :- World, x :- Nat, e :- EdgeRow]
  (=> (= (edge-find w x) (Option.some EdgeRow e)) (And (= (:id e) x) (= (edge-find w (:id e)) (Option.some EdgeRow e))))
  (intro hf)
  (have hi (= (:id e) x)) (exact (tbl-find-id EdgeRow edge-id x e (:edges w) hf))
  (apply (And.intro hi)) (rw [hi]) (exact hf))

(override! H3 't22-un-inv '[]
  '(a/theorem t22-un-hm3 [xm :- (List Nat), w :- World, x :- Nat]
     (=> (= (h3 xm w) true) (= (h3 xm (:world (t22-host-unawait w x))) true))
     (intro h)
     (cases hf (edge-find w x)) (case' [some e]) (case' [none])
     (simp only [t22-host-unawait hf refuse]) (exact h)
     (cases hk (Bool.and (Nat.beq (:kind e) ek-wait) (Nat.beq (:creditor e) 0)))
     (simp only [t22-host-unawait hf hk refuse]) (exact h)
     (simp only [t22-host-unawait hf hk accept])
     (simp only [Bool.and_eq_true] at hk)
     (have nd (= (Nat.beq (:kind e) ek-dep) false)) (rw [(Nat.eq_of_beq_eq_true (And.left hk))])
     (have p := (h3-find-id w x e hf))
     (rw [← (And.left p)])
     (exact (h3-remove-host xm w e (And.right p) nd (Nat.eq_of_beq_eq_true (And.right hk)) h))))
(override! H3 't8-unobserve-inv '[]
  '(a/theorem t8-unobserve-hm3 [xm :- (List Nat), w :- World, x :- Nat]
     (=> (= (g7 w) true) (= (h3 xm w) true) (= (h3 xm (:world (t8-unobserve w x))) true))
     (intros hg h)
     (cases hf (edge-find w x)) (case' [some e]) (case' [none])
     (simp only [t8-unobserve hf refuse]) (exact h)
     (cases hk (Nat.beq (:kind e) ek-observe))
     (simp only [t8-unobserve hf hk refuse]) (exact h)
     (simp only [t8-unobserve hf hk accept])
     (have p := (h3-find-id w x e hf))
     (have me := (tbl-find-mem EdgeRow edge-id x e (:edges w) hf))
     (have ob := (tbl-all-mem EdgeRow _ e (:edges w) (And.right (And.right (And.right (And.right (g7k-parts _ _ _ (g7-rest-of w hg)))))) me))
     (simp only [obs-one hk Bool.not_true Bool.false_or] at ob)
     (have nd (= (Nat.beq (:kind e) ek-dep) false)) (rw [(Nat.eq_of_beq_eq_true hk)])
     (rw [← (And.left p)])
     (exact (h3-remove-host xm w e (And.right p) nd (Nat.eq_of_beq_eq_true ob) h))))

;; ---- invalidate-dependents: the scanned ids name dep edges, and every edit keeps the edges' kinds
(a/defn h3-kd [x :- Nat, e :- EdgeRow] Bool (Bool.or (Bool.not (Nat.beq (:id e) x)) (Nat.beq (:kind e) ek-dep)))
(a/defn h3-kds [es :- (List EdgeRow), x :- Nat] Bool (tbl-all (h3-kd x) es))
(a/theorem h3-kds-inval [w :- World, e :- EdgeRow, xs :- (List Nat)]
  (=> (= (tbl-all (h3-kds (:edges w)) xs) true) (= (tbl-all (h3-kds (:edges (invalidate w e))) xs) true))
  (intro h)
  (have g (forall [y :- Nat] (=> (= (h3-kds (:edges w) y) true) (= (h3-kds (:edges (invalidate w e)) y) true))))
  (intros y q)
  (simp only [h3-kds invalidate comp-upd edge-upd set-comps set-edges] at q) (simp only [h3-kds invalidate comp-upd edge-upd set-comps set-edges])
  (have hin (forall [r :- EdgeRow] (=> (= (h3-kd y r) true) (= (Nat.beq (edge-id r) (:id e)) true) (= (h3-kd y (edge-set-phase ph-fired r)) true))))
  (intros r z hx) (exact z)
  (have hout (forall [r :- EdgeRow] (=> (= (h3-kd y r) true) (= (Nat.beq (edge-id r) (:id e)) false) (= (h3-kd y r) true))))
  (intros r z hx) (exact z)
  (exact (tbl-all-upd EdgeRow edge-id (:id e) (edge-set-phase ph-fired) _ _ hin hout (:edges w) q))
  (exact (tbl-all-mono Nat _ _ g xs h)))
(a/theorem h3-inval-id [xm :- (List Nat), w :- World, x :- Nat]
  (=> (= (h3-kds (:edges w) x) true) (= (h3 xm w) true) (= (h3 xm (invalidate-id w x)) true))
  (intros hk h)
  (cases hf (edge-find w x))
  (case [none] (simp only [invalidate-id hf]) (exact h))
  (case [some e]
    (cases hp (Nat.beq (:phase e) ph-armed))
    (case [false] (simp only [invalidate-id hf hp]) (exact h))
    (case [true]
      (simp only [invalidate-id hf hp])
      (have me := (tbl-find-mem EdgeRow edge-id x e (:edges w) hf))
      (have ie (= (:id e) x)) (exact (tbl-find-id EdgeRow edge-id x e (:edges w) hf))
      (have q := (tbl-all-mem EdgeRow _ e (:edges w) hk me))
      (have ie2 (= (Nat.beq (:id e) x) true)) (rw [ie]) (exact (Nat.beq_refl _))
      (simp only [h3-kd ie2 Bool.not_true Bool.false_or] at q)
      (exact (h3-invalidate xm w e me q h)))))
(a/theorem h3-inval-fold [xm :- (List Nat), xs :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (h3-kds (:edges w)) xs) true) (= (h3 xm w) true) (= (h3 xm (nat-fold invalidate-id w xs)) true)))
  (induction xs)
  (case [nil] (intros w hk h) (simp only [nat-fold]) (exact h))
  (case [cons y t ih]
    (intros w hk h)
    (simp only [tbl-all Bool.and_eq_true] at hk)
    (have h1 := (h3-inval-id xm w y (And.left hk) h))
    (have k1 (= (tbl-all (h3-kds (:edges (invalidate-id w y))) t) true))
    (cases hf (edge-find w y))
    (case [none] (simp only [invalidate-id hf]) (exact (And.right hk)))
    (case [some e]
      (cases hp (Nat.beq (:phase e) ph-armed))
      (case [false] (simp only [invalidate-id hf hp]) (exact (And.right hk)))
      (case [true] (simp only [invalidate-id hf hp]) (exact (h3-kds-inval w e t (And.right hk)))))
    (simp only [nat-fold]) (exact (ih (invalidate-id w y) k1 h1))))
(a/theorem h3-scan-all [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), Q :- (=> Nat Bool), xs :- (List A)]
  (=> (forall [r :- A] (=> (List.Mem r xs) (= (p r) true) (= (Q (idf r)) true))) (= (tbl-all Q (tbl-scan idf p xs)) true))
  (induction xs)
  (case [nil] (intro hq) (simp only [tbl-scan tbl-all]))
  (case [cons h t ih]
    (intro hq)
    (have g (forall [q :- A] (=> (List.Mem q t) (= (p q) true) (= (Q (idf q)) true))))
    (intros q m pq) (exact (hq q (List.Mem.tail h m) pq))
    (have r := (ih g))
    (cases hp (p h))
    (case [false] (simp only [tbl-scan hp r]))
    (case [true] (simp only [tbl-scan hp tbl-all r (hq h (List.Mem.head t) hp) Bool.and_self]))))
(a/theorem h3-kds-scan [w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (tbl-all (h3-kds (:edges w)) (tbl-scan edge-id (armed-dep-on d) (:edges w))) true))
  (intro hs)
  (have hi := (And.right (And.right (inv-parts w hs))))
  (simp only [ids-ok ids-unique all-ids Bool.and_eq_true] at hi)
  (have nd := (nat-nodup-app-left _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _
                (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (And.left hi))))))))
  (apply (h3-scan-all EdgeRow edge-id (armed-dep-on d) (h3-kds (:edges w)) (:edges w)))
  (intros r mr pr)
  (simp only [armed-dep-on Bool.and_eq_true] at pr)
  (have u := (uniq-all EdgeRow edge-id (fn [q :- EdgeRow] (Nat.beq (:kind q) ek-dep)) r (:edges w) nd mr (And.left pr)))
  (simp only [h3-kds])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) u))
  (intros q z) (simp only [same-id-then] at z) (simp only [h3-kd]) (exact z))
(override! H3 'inv-invalidate-dependents '[]
  '(a/theorem hm3-invalidate-dependents [xm :- (List Nat), w :- World, d :- Nat]
     (=> (= (h3 xm w) true) (= (h3 xm (invalidate-dependents w d)) true))
     (intro h) (simp only [invalidate-dependents])
     (exact (h3-inval-fold xm _ w (h3-kds-scan w d (h3-sample xm w h)) h))))

;; ===========================================================================
;; Part C. The copies so far (each checks the bundle version of its whole inv-sample closure)
;; ===========================================================================

(lcopy! H3 't22-un-inv)
(lcopy! H3 't8-unobserve-inv)
(lcopy! H3 'inv-invalidate-dependents)
(lcopy! H3 't2-inv)
(lcopy! H3 't9-inv)
(lcopy! H3 't18-inv)
(lcopy! H3 'inv-wake-closed)
(lcopy! H3 'inv-settle-host)
(lcopy! H3 'inv-fast-fill)
(lcopy! H3 'inv-deliver-fire)
