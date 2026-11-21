(ns spindel.v2.inv.members.fires
  "h-mem2 through `world-step` (P11, second half), continued from spindel.v2.inv.members.bundle (the bundle `current-members xm`, its
  transfer machinery and the bundle `H3`), kernel-checked (Init only): the fires.

  Part A. Free members after a fill: the first activation with member x is the only one that can be
  obliged to x (`current-members-freeb-of`: every other holder is not obliging), a fill removes x from it
  (`h3-freeb-fill`), so x is free afterwards and a member-id exemption of x can be undone (`current-members-undo-x`;
  an edge id is no computation and no debtor: `h3-edge-not`).
  Part B. The fires: deliver-dep (a final debtor: the member edge goes while x is exempt, the fill takes
  x out of its only holder, undo), fire-dep, fire-wait-act (no activation: free; not current: E1 makes the
  holder not current; current: exempt, fill, undo), fire-wait (host wait: creditor 0 is no activation),
  fire-edge."
  (:require [ansatz.core :as a]
            [spindel.v2.pres.tree :as tree]
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
            [spindel.v2.progress.l5 :refer :all]
            [spindel.v2.inv.marks :refer :all]
            [spindel.v2.inv.i14 :refer :all]
            [spindel.v2.inv.marks-step :refer :all]
            [spindel.v2.inv.members.bundle :refer :all]
            [spindel.v2.inv.alive-runs :refer :all]))

;; ===========================================================================
;; Part A. Free members after a fill; undoing a member-id exemption
;; ===========================================================================

(a/theorem current-members-fill-contrib [x :- Nat, ms :- (List Member)]
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
(a/theorem current-members-fill-contrib-act [x :- Nat, v :- RunResult, b :- ActRow] (= (reach-mem x (act-contrib (act-fill x v b))) false)
  (simp only [act-contrib act-fill]) (exact (current-members-fill-contrib x (:members b))))

;; every activation other than aid is not obliged to member x
(a/defn current-members-fb [xm :- (List Nat), w :- World, x :- Nat, aid :- Nat, b :- ActRow] Bool (Bool.or (Nat.beq (:id b) aid) (current-members-fa xm w x b)))
(a/defn current-members-freeb [xm :- (List Nat), w :- World, x :- Nat, aid :- Nat] Bool (tbl-all (current-members-fb xm w x aid) (:acts w)))

(a/theorem current-members-freeb-of [xm :- (List Nat), w :- World, e :- EdgeRow, a :- ActRow]
  (=> (= (current-members-rest xm w) true) (List.Mem e (:edges w)) (= (act-with-member (:id e) (:acts w)) (Option.some ActRow a))
      (= (current-members-freeb xm w (:id e) (:id a)) true))
  (intros h me ha)
  (simp only [current-members-freeb])
  (apply all-of-mem) (intros b mb)
  (cases hb (Nat.beq (:id b) (:id a)))
  (case [true] (simp only [current-members-fb hb Bool.true_or]))
  (case [false]
    (simp only [current-members-fb hb Bool.false_or current-members-fa])
    (apply all-of-mem) (intros r mr)
    (simp only [current-members-fr Bool.or_eq_true])
    (cases ir (Nat.beq (:id r) (:run b)))
    (case [false] (exact (Or.inl (rfl))))
    (case [true]
      (apply Or.inr)
      (cases hx (reach-mem (:of r) xm))
      (case [true] (exact (Or.inl (rfl))))
      (case [false]
        (apply Or.inr)
        (cases hc (tbl-any (current-members-cur (current-members-run-key r)) (:comps w)))
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
              (have u := (current-members-ob-use xm w b r (:id e) e h mb mr (Nat.eq_of_beq_eq_true ir) hx hc hm hxx me (rfl)))
              (have sk := (And.left u))
              (simp only [current-members-s Bool.and_eq_true] at sk)
              (have f1 := (And.right (And.right (And.right sk))))
              (rw [ha] at f1)
              (simp only [opt-test current-members-first] at f1)
              (rw [beq-comm] at f1) (rw [hb] at f1) (cases f1))))))))

;; transfer of a free-ness fact: comps keep currency backward, runs keyed alike
(a/theorem current-members-fr-back [xm :- (List Nat), w :- World, w2 :- World, x :- Nat, b :- ActRow, r :- RunRow]
  (=> (forall [k :- CurrentMembersRunKey] (=> (= (tbl-any (current-members-cur k) (:comps w2)) true) (= (tbl-any (current-members-cur k) (:comps w)) true)))
      (= (current-members-fr xm w x b r) true) (= (current-members-fr xm w2 x b r) true))
  (intros hc h)
  (simp only [current-members-fr Bool.or_eq_true] at h) (simp only [current-members-fr Bool.or_eq_true])
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
        (cases c2 (tbl-any (current-members-cur (current-members-run-key r)) (:comps w2)))
        (case [false] (rfl))
        (case [true] (have q := (hc (current-members-run-key r) c2)) (rw [q] at z3) (cases z3)))
      (case [inr z3] (exact (Or.inr z3))))))
(a/theorem current-members-fr-rk [xm :- (List Nat), w :- World, x :- Nat, b :- ActRow, q :- RunRow, r :- RunRow]
  (=> (= (current-members-run-key q) (current-members-run-key r)) (= (current-members-fr xm w x b q) (current-members-fr xm w x b r)))
  (intro e)
  (have e1 (= (:id q) (:id r))) (exact (congrArg (fn [k :- CurrentMembersRunKey] (:id k)) e))
  (have e2 (= (:of q) (:of r))) (exact (congrArg (fn [k :- CurrentMembersRunKey] (:of k)) e))
  (simp only [current-members-fr e1 e2]) (rw [e]))
(a/theorem current-members-fa-back [xm :- (List Nat), w :- World, w2 :- World, x :- Nat, b :- ActRow]
  (=> (= (:runs w2) (:runs w))
      (forall [k :- CurrentMembersRunKey] (=> (= (tbl-any (current-members-cur k) (:comps w2)) true) (= (tbl-any (current-members-cur k) (:comps w)) true)))
      (= (current-members-fa xm w x b) true) (= (current-members-fa xm w2 x b) true))
  (intros er hc h)
  (simp only [current-members-fa] at h) (simp only [current-members-fa]) (rw [er])
  (have g (forall [r :- RunRow] (=> (= (current-members-fr xm w x b r) true) (= (current-members-fr xm w2 x b r) true))))
  (intros r hr) (exact (current-members-fr-back xm w w2 x b r hc hr))
  (exact (tbl-all-mono RunRow _ _ g (:runs w) h)))
(a/theorem current-members-freeb-frame [xm :- (List Nat), w :- World, w2 :- World, x :- Nat, aid :- Nat]
  (=> (= (:acts w2) (:acts w)) (= (:runs w2) (:runs w))
      (forall [k :- CurrentMembersRunKey] (=> (= (tbl-any (current-members-cur k) (:comps w2)) true) (= (tbl-any (current-members-cur k) (:comps w)) true)))
      (= (current-members-freeb xm w x aid) true) (= (current-members-freeb xm w2 x aid) true))
  (intros ea er hc h)
  (simp only [current-members-freeb] at h) (simp only [current-members-freeb]) (rw [ea])
  (have g (forall [b :- ActRow] (=> (= (current-members-fb xm w x aid b) true) (= (current-members-fb xm w2 x aid b) true))))
  (intros b hb)
  (simp only [current-members-fb Bool.or_eq_true] at hb) (simp only [current-members-fb Bool.or_eq_true])
  (cases hb)
  (case [inl z] (exact (Or.inl z)))
  (case [inr z] (exact (Or.inr (current-members-fa-back xm w w2 x b er hc z))))
  (exact (tbl-all-mono ActRow _ _ g (:acts w) h)))

;; currency only reads the computations' (id, epoch): an edit of other fields keeps it backward
(a/theorem current-members-cur-upd-back [k :- CurrentMembersRunKey, y :- Nat, f :- (=> CompRow CompRow),
                            hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                            hep :- (forall [c :- CompRow] (= (:epoch (f c)) (:epoch c))), cs :- (List CompRow)]
  (=> (= (tbl-any (current-members-cur k) (tbl-upd comp-id y f cs)) true) (= (tbl-any (current-members-cur k) cs) true))
  (intro h)
  (have g (forall [q :- CompRow] (=> (= (current-members-cur k (f q)) true) (= (current-members-cur k q) true))))
  (intros q z)
  (have e1 (= (:id (f q)) (:id q))) (exact (hid q))
  (simp only [current-members-cur e1 (hep q)] at z) (simp only [current-members-cur]) (exact z)
  (exact (current-members-any-upd-back CompRow comp-id y f (current-members-cur k) g cs h)))

(a/theorem current-members-free-fill [xm :- (List Nat), w :- World, a :- ActRow, x :- Nat, v :- RunResult]
  (=> (List.Mem a (:acts w)) (= (current-members-freeb xm w x (:id a)) true) (= (current-members-free xm (fill-slot w a x v) x) true))
  (intros ma h)
  (simp only [current-members-freeb] at h)
  (cases hr (act-ready (act-fill x v a)))
  (case [false]
    (simp only [fill-slot hr current-members-free act-upd set-acts])
    (have hin (forall [b :- ActRow] (=> (= (current-members-fb xm w x (:id a) b) true) (= (Nat.beq (act-id b) (:id a)) true)
                                       (= (current-members-fa xm (set-acts w (tbl-upd act-id (:id a) (act-fill x v) (:acts w))) x (act-fill x v b)) true))))
    (intros b hb hx)
    (simp only [current-members-fa])
    (apply all-of-mem) (intros r mr)
    (simp only [current-members-fr current-members-fill-contrib-act Bool.not_false Bool.true_or Bool.or_true])
    (have hout (forall [b :- ActRow] (=> (= (current-members-fb xm w x (:id a) b) true) (= (Nat.beq (act-id b) (:id a)) false)
                                        (= (current-members-fa xm (set-acts w (tbl-upd act-id (:id a) (act-fill x v) (:acts w))) x b) true))))
    (intros b hb hx)
    (have hx2 (= (Nat.beq (:id b) (:id a)) false)) (exact hx)
    (simp only [current-members-fb hx2 Bool.false_or] at hb)
    (exact (current-members-fa-back xm w _ x b (rfl) (fn [k :- CurrentMembersRunKey, q :- (= (tbl-any (current-members-cur k) (:comps w)) true)] q) hb))
    (exact (tbl-all-upd ActRow act-id (:id a) (act-fill x v) _ _ hin hout (:acts w) h)))
  (case [true]
    (simp only [fill-slot hr resume])
    (have hc (forall [k :- CurrentMembersRunKey] (=> (= (tbl-any (current-members-cur k) (:comps (run-upd (drop-act w (:id a)) (:run a) run-wake))) true)
                                    (= (tbl-any (current-members-cur k) (:comps w)) true))))
    (intros k q)
    (simp only [run-upd drop-act act-del drop-cred-edges comp-upd set-runs set-acts set-comps set-edges] at q)
    (exact (current-members-cur-upd-back k (:id a) (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (:epoch c))) (:comps w) q))
    (have hout (forall [b :- ActRow] (=> (= (current-members-fb xm w x (:id a) b) true) (= (Nat.beq (act-id b) (:id a)) false)
                                        (= (current-members-fa xm (run-upd (drop-act w (:id a)) (:run a) run-wake) x b) true))))
    (intros b hb hx)
    (have hx2 (= (Nat.beq (:id b) (:id a)) false)) (exact hx)
    (simp only [current-members-fb hx2 Bool.false_or current-members-fa] at hb)
    (simp only [current-members-fa run-upd drop-act act-del drop-cred-edges comp-upd set-runs set-acts set-comps set-edges])
    (have hin2 (forall [r :- RunRow] (=> (= (current-members-fr xm w x b r) true) (= (Nat.beq (run-id r) (:run a)) true)
                                        (= (current-members-fr xm (run-upd (drop-act w (:id a)) (:run a) run-wake) x b (run-wake r)) true))))
    (intros r q hq)
    (rw [(current-members-fr-rk xm (run-upd (drop-act w (:id a)) (:run a) run-wake) x b (run-wake r) r (rfl))])
    (exact (current-members-fr-back xm w _ x b r hc q))
    (have hout2 (forall [r :- RunRow] (=> (= (current-members-fr xm w x b r) true) (= (Nat.beq (run-id r) (:run a)) false)
                                         (= (current-members-fr xm (run-upd (drop-act w (:id a)) (:run a) run-wake) x b r) true))))
    (intros r q hq) (exact (current-members-fr-back xm w _ x b r hc q))
    (exact (tbl-all-upd RunRow run-id (:run a) run-wake _ _ hin2 hout2 (:runs w) hb))
    (simp only [current-members-free run-upd drop-act act-del drop-cred-edges comp-upd set-runs set-acts set-comps set-edges])
    (exact (tbl-all-del ActRow act-id (:id a) _ _ hout (:acts w) h))))

;; an edge id is no computation, task, source or resource id; hence no edge's debtor
(a/theorem current-members-edge-not-comp [w :- World, x :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has edge-id x (:edges w)) true) (= (tbl-has comp-id x (:comps w)) false))
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
(a/theorem current-members-edge-not-task [w :- World, x :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has edge-id x (:edges w)) true) (= (tbl-has task-id x (:tasks w)) false))
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
(a/theorem current-members-edge-not-source [w :- World, x :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has edge-id x (:edges w)) true) (= (tbl-has source-id x (:sources w)) false))
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
(a/theorem current-members-edge-not-res [w :- World, x :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has edge-id x (:edges w)) true) (= (tbl-has resource-id x (:res w)) false))
  (intros h he)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have u2 := (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ u))))))
  (have hm2 (= (nat-mem x (tbl-ids edge-id (:edges w))) true)) (rw [nat-mem-ids]) (exact he)
  (have d := (nodup-app-disj x _ _ u2 hm2))
  (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
  (have d2 := (And.left (And.right d)))
  (rw [nat-mem-ids] at d2) (exact d2))
(a/defn current-members-ndx [x :- Nat, e :- EdgeRow] Bool (Bool.not (Nat.beq (:debtor e) x)))
(a/theorem current-members-edge-not-debtor [w :- World, x :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has edge-id x (:edges w)) true) (= (tbl-all (current-members-ndx x) (:edges w)) true))
  (intros h he)
  (have ok := (And.left (And.right (well-formed-parts w h))))
  (simp only [edges-ref-ok edges-ref-ok-in] at ok)
  (apply all-of-mem) (intros e me)
  (have k := (tbl-all-mem EdgeRow _ e (:edges w) ok me))
  (simp only [edge-ok deb-ok Bool.and_eq_true Bool.or_eq_true] at k)
  (have k2 := (And.right k))
  (cases hd (Nat.beq (:debtor e) x))
  (case [false] (simp only [current-members-ndx hd Bool.not_false]))
  (case [true]
    (have ed := (Nat.eq_of_beq_eq_true hd))
    (rw [ed] at k2)
    (cases k2)
    (case [inl z] (rw [(current-members-edge-not-comp w x h he)] at z) (cases z))
    (case [inr z]
      (cases z)
      (case [inl z2] (rw [(current-members-edge-not-task w x h he)] at z2) (cases z2))
      (case [inr z2]
        (cases z2)
        (case [inl z3] (rw [(current-members-edge-not-source w x h he)] at z3) (cases z3))
        (case [inr z3] (have z4 := (And.right z3)) (rw [(current-members-edge-not-res w x h he)] at z4) (cases z4))))))

;; ===========================================================================
;; Part B. The fires
;; ===========================================================================

(a/theorem current-members-free-self [xm :- (List Nat), w :- World, x :- Nat] (= (current-members-free (List.cons Nat x xm) w x) true)
  (simp only [current-members-free])
  (apply all-of-mem) (intros b mb)
  (simp only [current-members-fa])
  (apply all-of-mem) (intros r mr)
  (simp only [current-members-fr reach-mem-cons Nat.beq_refl Bool.true_or Bool.or_true]))
(a/theorem current-members-xm-cons [xm :- (List Nat), x :- Nat, w :- World] (=> (= (current-members xm w) true) (= (current-members (List.cons Nat x xm) w) true))
  (intro h)
  (have g (forall [d :- Nat] (=> (= (reach-mem d xm) true) (= (reach-mem d (List.cons Nat x xm)) true))))
  (intros d q) (simp only [reach-mem-cons q Bool.or_true])
  (exact (current-members-intro _ w (current-members-well-formed xm w h) (current-members-rest-xm xm _ w g (current-members-rest-of xm w h)))))
(a/theorem hk-safe-nocomp [xm :- (List Nat), cs :- (List CompRow), d :- Nat]
  (=> (= (tbl-has comp-id d cs) false) (= (hk-safe xm cs d) true))
  (intro hc)
  (have ne := (has-false-ne CompRow comp-id d cs hc))
  (have g (forall [c :- CompRow] (=> (= (Bool.not (Nat.beq (comp-id c) d)) true) (= (hk-sif d c) true))))
  (intros c q) (simp only [comp-id] at q) (simp only [hk-sif q Bool.true_or])
  (have t (= (tbl-all (hk-sif d) cs) true)) (exact (tbl-all-mono CompRow _ _ g cs ne))
  (simp only [hk-safe t Bool.or_true]))

;; the current-members-r facts of an activation's run, unfolded
(a/theorem current-members-r-use [xm :- (List Nat), w :- World, b :- ActRow, r :- RunRow]
  (=> (= (current-members-rest xm w) true) (List.Mem b (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run b))
      (And (= (tbl-all (current-members-e1 (current-members-run-key r)) (:comps w)) true) (= (current-members-ob xm w b (current-members-run-key r)) true)))
  (intros h mb mr ir)
  (have ha := (tbl-all-mem ActRow _ b (:acts w) h mb))
  (simp only [current-members-a Bool.and_eq_true] at ha)
  (have hr := (tbl-all-mem RunRow _ r (:runs w) (And.right ha) mr))
  (simp only [current-members-rr] at hr)
  (have i2 (= (Nat.beq (:id (current-members-run-key r)) (:run b)) true)) (simp only [current-members-run-key ir Nat.beq_refl])
  (simp only [current-members-r i2 Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
  (exact (And.right hr)))
;; a current, non-exempt run's computation has done-epoch < epoch on every row
(a/theorem current-members-cs-use [xm :- (List Nat), w :- World, b :- ActRow, r :- RunRow]
  (=> (= (current-members-rest xm w) true) (List.Mem b (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run b))
      (= (reach-mem (:of r) xm) false) (= (tbl-any (current-members-cur (current-members-run-key r)) (:comps w)) true)
      (= (tbl-all (current-members-cs (current-members-run-key r)) (:comps w)) true))
  (intros h mb mr ir hx hc)
  (have ob := (And.right (current-members-r-use xm w b r h mb mr ir)))
  (have hx2 (= (reach-mem (:of (current-members-run-key r)) xm) false)) (exact hx)
  (simp only [current-members-ob hx2 hc Bool.not_true Bool.false_or Bool.and_eq_true] at ob)
  (exact (And.left ob)))
;; a current run (h3's sense) is current for the engine's run-current
(a/theorem current-members-cur-run-current [xm :- (List Nat), w :- World, b :- ActRow, r :- RunRow]
  (=> (= (well-formed w) true) (= (current-members-rest xm w) true) (List.Mem b (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run b))
      (= (tbl-any (current-members-cur (current-members-run-key r)) (:comps w)) true) (= (run-current w (:id r)) true))
  (intros hs h mb mr ir hc)
  (have e1 := (And.left (current-members-r-use xm w b r h mb mr ir)))
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
      (have i3 (= (Nat.beq (:id c2) (:of (current-members-run-key r))) true)) (try (simp only [current-members-run-key])) (rw [ic2 (And.right sq)]) (exact (Nat.beq_refl _))
      (simp only [current-members-e1 i3 Bool.not_true Bool.false_or] at q1)
      (have l1 := (comp-facts-le-of _ _ q1))
      (apply (any-elim CompRow (current-members-cur (current-members-run-key r)) _ (:comps w) hc))
      (intros c mc qc)
      (simp only [current-members-cur Bool.and_eq_true] at qc)
      (have l2 := (comp-facts-le-of _ _ (And.right qc)))
      (have ic (= (:id c) (:id c2))) (rw [ic2 (And.right sq)]) (exact (Nat.eq_of_beq_eq_true (And.left qc)))
      (have sm := (comp-same w c2 c hs mc2 mc ic))
      (have ee (= (:epoch r2) (:epoch c2))) (try (simp only [current-members-run-key] at l1)) (try (simp only [current-members-run-key] at l2)) (rw [(And.left sq)]) (omega)
      (simp only [run-current hf hg ee Nat.beq_refl]))))

;; a non-dep edge: only an activation with the creditor's id can be obliged to it
(a/theorem current-members-freeb-cred [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (current-members-rest xm w) true) (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) false)
      (= (current-members-freeb xm w (:id e) (:creditor e)) true))
  (intros h me hk)
  (simp only [current-members-freeb])
  (apply all-of-mem) (intros b mb)
  (cases hb (Nat.beq (:id b) (:creditor e)))
  (case [true] (simp only [current-members-fb hb Bool.true_or]))
  (case [false]
    (simp only [current-members-fb hb Bool.false_or current-members-fa])
    (apply all-of-mem) (intros r mr)
    (simp only [current-members-fr Bool.or_eq_true])
    (cases ir (Nat.beq (:id r) (:run b)))
    (case [false] (exact (Or.inl (rfl))))
    (case [true]
      (apply Or.inr)
      (cases hx (reach-mem (:of r) xm))
      (case [true] (exact (Or.inl (rfl))))
      (case [false]
        (apply Or.inr)
        (cases hc (tbl-any (current-members-cur (current-members-run-key r)) (:comps w)))
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
              (have u := (current-members-ob-use xm w b r (:id e) e h mb mr (Nat.eq_of_beq_eq_true ir) hx hc hm hxx me (rfl)))
              (have sk := (And.left u))
              (simp only [current-members-s Bool.and_eq_true] at sk)
              (have c1 := (And.left (And.right (And.right sk))))
              (simp only [hk Bool.false_or] at c1)
              (rw [beq-comm] at c1) (rw [hb] at c1) (cases c1))))))))
(a/theorem current-members-free-of-freeb [xm :- (List Nat), w :- World, x :- Nat, aid :- Nat]
  (=> (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (Nat.beq (:id b) aid) true) (= (current-members-fa xm w x b) true)))
      (= (current-members-freeb xm w x aid) true) (= (current-members-free xm w x) true))
  (intros g h)
  (simp only [current-members-freeb] at h) (simp only [current-members-free])
  (have g2 (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (current-members-fb xm w x aid b) true) (= (current-members-fa xm w x b) true))))
  (intros b mb hb)
  (cases hi (Nat.beq (:id b) aid))
  (case [true] (exact (g b mb hi)))
  (case [false] (simp only [current-members-fb hi Bool.false_or] at hb) (exact hb))
  (exact (tbl-all-mem-mono ActRow _ _ (:acts w) g2 h)))
;; the activation aid's runs are not current: it is obliged to nothing
(a/theorem current-members-fa-ncur [xm :- (List Nat), w :- World, x :- Nat, b :- ActRow]
  (=> (= (well-formed w) true) (= (current-members-rest xm w) true) (List.Mem b (:acts w)) (= (run-current w (:run b)) false) (= (current-members-fa xm w x b) true))
  (intros hs h mb hn)
  (simp only [current-members-fa])
  (apply all-of-mem) (intros r mr)
  (simp only [current-members-fr Bool.or_eq_true])
  (cases ir (Nat.beq (:id r) (:run b)))
  (case [false] (exact (Or.inl (rfl))))
  (case [true]
    (apply Or.inr) (apply Or.inr)
    (cases hc (tbl-any (current-members-cur (current-members-run-key r)) (:comps w)))
    (case [false] (exact (Or.inl (rfl))))
    (case [true]
      (have ir2 := (Nat.eq_of_beq_eq_true ir))
      (have q := (current-members-cur-run-current xm w b r hs h mb mr ir2 hc))
      (rw [ir2 hn] at q) (cases q))))

;; ---- edges and computation ids through the edits of a fire
(a/theorem current-members-acts-remove-edge [w :- World, x :- Nat] (= (:acts (remove-edge w x)) (:acts w))
  (cases hf (edge-find w x)) (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm comp-upd edge-del set-edges set-comps]))))
(a/theorem current-members-cur-remove-edge [w :- World, x :- Nat, k :- CurrentMembersRunKey]
  (=> (= (tbl-any (current-members-cur k) (:comps (remove-edge w x))) true) (= (tbl-any (current-members-cur k) (:comps w)) true))
  (intro q)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf] at q) (exact q))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm edge-del set-edges] at q) (exact q))
    (case [true]
      (simp only [remove-edge hf hm comp-upd edge-del set-edges set-comps] at q)
      (exact (current-members-cur-upd-back k (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (:epoch c))) (:comps w) q)))))
(a/theorem current-members-ndx-remove-edge [w :- World, x :- Nat, y :- Nat]
  (=> (= (tbl-all (current-members-ndx y) (:edges w)) true) (= (tbl-all (current-members-ndx y) (:edges (remove-edge w x))) true))
  (intro h)
  (have g (forall [e :- EdgeRow] (=> (= (current-members-ndx y e) true) (= (Nat.beq (edge-id e) x) false) (= (current-members-ndx y e) true))))
  (intros e q hx) (exact q)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (all_goals (simp only [remove-edge hf hm comp-upd edge-del set-edges set-comps]))
    (all_goals (exact (tbl-all-del EdgeRow edge-id x _ _ g (:edges w) h)))))
(a/theorem current-members-fill-edges [P :- (=> EdgeRow Bool), w :- World, a :- ActRow, x :- Nat, v :- RunResult]
  (=> (= (tbl-all P (:edges w)) true) (= (tbl-all P (:edges (fill-slot w a x v))) true))
  (intro h)
  (cases hr (act-ready (act-fill x v a)))
  (case [false] (simp only [fill-slot hr act-upd set-acts]) (exact h))
  (case [true]
    (simp only [fill-slot hr resume run-upd drop-act act-del drop-cred-edges comp-upd set-runs set-acts set-comps set-edges])
    (exact (tbl-all-filter EdgeRow P _ (:edges w) h))))
(a/theorem current-members-fill-has [w :- World, a :- ActRow, x :- Nat, v :- RunResult, y :- Nat]
  (= (tbl-has comp-id y (:comps (fill-slot w a x v))) (tbl-has comp-id y (:comps w)))
  (cases hr (act-ready (act-fill x v a)))
  (case [false] (simp only [fill-slot hr act-upd set-acts]))
  (case [true]
    (simp only [fill-slot hr resume run-upd set-runs])
    (exact (hk-has-drop-act w (:id a) y))))

;; ---- exempt x, edit its edge, fill a, undo
(a/theorem current-members-undo-fill [xm :- (List Nat), w :- World, w1 :- World, a :- ActRow, x :- Nat, v :- RunResult]
  (=> (= (well-formed w) true) (= (tbl-has edge-id x (:edges w)) true)
      (= (current-members (List.cons Nat x xm) w1) true) (List.Mem a (:acts w1)) (= (current-members-freeb xm w1 x (:id a)) true)
      (= (tbl-has comp-id x (:comps w1)) (tbl-has comp-id x (:comps w)))
      (= (tbl-all (current-members-ndx x) (:edges w1)) true)
      (= (current-members xm (fill-slot w1 a x v)) true))
  (intros hs he h1 ma fb hc hd)
  (have h2 := (current-members-fill-slot _ w1 a x v ma h1))
  (have fr := (current-members-free-fill xm w1 a x v ma fb))
  (have hc2 (= (tbl-has comp-id x (:comps (fill-slot w1 a x v))) false))
  (rw [current-members-fill-has hc]) (exact (current-members-edge-not-comp w x hs he))
  (have hd2 := (current-members-fill-edges (current-members-ndx x) w1 a x v hd))
  (have hd3 (forall [e :- EdgeRow] (=> (List.Mem e (:edges (fill-slot w1 a x v))) (= (Nat.beq (:debtor e) x) false))))
  (intros e me) (have q := (tbl-all-mem EdgeRow _ e _ hd2 me)) (simp only [current-members-ndx] at q) (exact (bnot-true _ q))
  (exact (current-members-intro xm _ (current-members-well-formed _ _ h2) (current-members-undo-x xm _ x hc2 hd3 fr (current-members-rest-of _ _ h2)))))

(a/theorem current-members-deliver-safe [xm :- (List Nat), w :- World, e :- EdgeRow, a :- ActRow]
  (=> (= (act-with-member (:id e) (:acts w)) (Option.some ActRow a))
      (= (run-current-of w (:run a) (:creditor e)) true) (= (current-members xm w) true)
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
          (have cur (= (tbl-any (current-members-cur (current-members-run-key r)) (:comps w)) true))
          (apply (any-elim-of CompRow (current-members-cur (current-members-run-key r)) c (:comps w) mc))
          (have ee := (Nat.eq_of_beq_eq_true hcc))
          (simp only [current-members-cur current-members-run-key ic ee Nat.beq_refl comp-facts-ble-refl Bool.and_self])
          (have cs := (current-members-cs-use xm w a r (current-members-rest-of xm w h) ma (And.left p) (And.right p) hx cur))
          (have g (forall [q :- CompRow] (=> (= (current-members-cs (current-members-run-key r) q) true) (= (hk-sif (:of r) q) true))))
          (intros q z)
          (simp only [current-members-cs current-members-run-key Bool.or_eq_true] at z) (simp only [hk-sif hk-strong Bool.or_eq_true])
          (cases z) (rename_i z1) (exact (Or.inl z1)) (rename_i z1) (exact (Or.inr (Or.inr z1)))
          (have t (= (tbl-all (hk-sif (:of r)) (:comps w)) true)) (exact (tbl-all-mono CompRow _ _ g (:comps w) cs))
          (rw [← eo]) (simp only [hk-safe t Bool.or_true])
          (rw [← eo]) (simp only [hk-safe reach-mem-cons hx Bool.true_or Bool.or_true]))

(a/theorem current-members-deliver-dep [xm :- (List Nat), w :- World, e :- EdgeRow, a :- ActRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (act-with-member (:id e) (:acts w)) (Option.some ActRow a))
      (= (run-current-of w (:run a) (:creditor e)) true) (= (current-members xm w) true) (= (current-members xm (deliver-dep w e a)) true))
  (intros hf ha hcur h)
  (have hs := (current-members-well-formed xm w h))
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) hf))
  (have ma := (act-with-member-mem (:id e) (:acts w) a ha))
  (cases hd (deb-final w (:debtor e)))
  (case [false]
    (simp only [deliver-dep dep-consumed hd])
    (have harm (forall [q :- EdgeRow] (=> (= (Nat.beq (:phase q) ph-armed) true)
                                          (= (Nat.beq (:phase (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)) q)) ph-armed) true))))
    (intros q z) (exact (Nat.beq_refl ph-armed))
    (have h1 := (current-members-edge-upd-m xm w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
                  (edge-rearm-edge-id (deb-value w (:debtor e)) (deb-version w (:debtor e))) (edge-rearm-kind (deb-value w (:debtor e)) (deb-version w (:debtor e)))
                  (edge-rearm-creditor (deb-value w (:debtor e)) (deb-version w (:debtor e))) (edge-rearm-debtor (deb-value w (:debtor e)) (deb-version w (:debtor e)))
                  (edge-rearm-marked (deb-value w (:debtor e)) (deb-version w (:debtor e))) harm h))
    (exact (current-members-fill-slot xm (edge-upd w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))) a (:id e) (deb-result w (:debtor e)) ma h1)))
  (case [true]
    (simp only [deliver-dep dep-consumed hd])
    (have h0 := (current-members-xm-cons xm (:id e) w h))
    (have hu (forall [e2 :- EdgeRow] (=> (= (edge-find w (:id e)) (Option.some EdgeRow e2)) (= (:marked e2) true)
                                         (= (hk-safe (List.cons Nat (:id e) xm) (:comps w) (:creditor e2)) true))))
    (intros e2 hf2 hm2)
    (rw [hf] at hf2)
    (have ee (= e2 e)) (exact (Option.some.inj (Eq.symm hf2)))
    (rw [ee]) (exact (current-members-deliver-safe xm w e a ha hcur h))
    (have h1 := (current-members-remove-edge _ w (:id e) hu (current-members-free-self xm w (:id e)) h0))
    (have fb0 := (current-members-freeb-of xm w e a (current-members-rest-of xm w h) me ha))
    (have hcb (forall [k :- CurrentMembersRunKey] (=> (= (tbl-any (current-members-cur k) (:comps (remove-edge w (:id e)))) true) (= (tbl-any (current-members-cur k) (:comps w)) true))))
    (intros k q) (exact (current-members-cur-remove-edge w (:id e) k q))
    (have fb1 := (current-members-freeb-frame xm w (remove-edge w (:id e)) (:id e) (:id a) (current-members-acts-remove-edge w (:id e)) (runs-remove-edge w (:id e)) hcb fb0))
    (have ma1 (List.Mem a (:acts (remove-edge w (:id e))))) (rw [current-members-acts-remove-edge]) (exact ma)
    (exact (current-members-undo-fill xm w (remove-edge w (:id e)) a (:id e) (deb-result w (:debtor e)) hs (tbl-find-has-edge w e me) h1 ma1 fb1
             (hk-has-remove-edge w (:id e) (:id e)) (current-members-ndx-remove-edge w (:id e) (:id e) (current-members-edge-not-debtor w (:id e) hs (tbl-find-has-edge w e me)))))))

(a/theorem current-members-fire-dep [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) true) (= (current-members xm w) true) (= (current-members xm (fire-dep w e)) true))
  (intros hf hk h)
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) hf))
  (cases ha (act-with-member (:id e) (:acts w)))
  (case [none] (simp only [fire-dep ha]) (exact (current-members-invalidate xm w e me hk h)))
  (case [some a]
    (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
    (case [false] (simp only [fire-dep ha hc]) (exact (current-members-invalidate xm w e me hk h)))
    (case [true]
      (simp only [fire-dep ha hc])
      (have hc1 (= (run-current-of w (:run a) (:creditor e)) true)) (simp only [Bool.and_eq_true] at hc) (exact (And.left hc))
      (exact (current-members-deliver-dep xm w e a hf ha hc1 h)))))

(a/theorem current-members-ndx-phase [x :- Nat, y :- Nat, p :- Nat, es :- (List EdgeRow)]
  (=> (= (tbl-all (current-members-ndx y) es) true) (= (tbl-all (current-members-ndx y) (tbl-upd edge-id x (edge-set-phase p) es)) true))
  (intro h)
  (have hin (forall [q :- EdgeRow] (=> (= (current-members-ndx y q) true) (= (Nat.beq (edge-id q) x) true) (= (current-members-ndx y (edge-set-phase p q)) true))))
  (intros q z hx) (exact z)
  (have hout (forall [q :- EdgeRow] (=> (= (current-members-ndx y q) true) (= (Nat.beq (edge-id q) x) false) (= (current-members-ndx y q) true))))
  (intros q z hx) (exact z)
  (exact (tbl-all-upd EdgeRow edge-id x (edge-set-phase p) _ _ hin hout es h)))
;; the phase change of a free edge
(a/theorem current-members-phase-free [xm :- (List Nat), w :- World, x :- Nat, p :- Nat]
  (=> (= (current-members-free xm w x) true) (= (current-members xm w) true) (= (current-members xm (edge-upd w x (edge-set-phase p))) true))
  (intros hfr h)
  (have hs := (current-members-well-formed xm w h))
  (exact (current-members-intro xm _ (well-formed-edge-set-phase w x p hs)
           (current-members-rest-edge-upd-free xm w x (edge-set-phase p) (edge-set-phase-edge-id p) (current-members-db-of w hs) hfr (current-members-rest-of xm w h)))))

(a/theorem current-members-fire-wait-act [xm :- (List Nat), res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) false) (= (current-members xm w) true)
      (= (current-members xm (fire-wait-act res w e)) true))
  (intros hf hk h)
  (have hs := (current-members-well-formed xm w h))
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) hf))
  (have fbc := (current-members-freeb-cred xm w e (current-members-rest-of xm w h) me hk))
  (cases ha (act-find w (:creditor e)))
  (case [none]
    (have g (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (Nat.beq (:id b) (:creditor e)) true) (= (current-members-fa xm w (:id e) b) true))))
    (intros b mb hb)
    (have z := (tbl-find-none-has ActRow act-id (:creditor e) (:acts w) ha))
    (have z2 := (has-of-mem ActRow act-id b (:acts w) mb))
    (have eb (= (act-id b) (:creditor e))) (exact (Nat.eq_of_beq_eq_true hb))
    (rw [eb z] at z2) (cases z2)
    (simp only [fire-wait-act ha])
    (exact (current-members-phase-free xm w (:id e) ph-fired (current-members-free-of-freeb xm w (:id e) (:creditor e) g fbc) h)))
  (case [some a]
    (have ma := (tbl-find-mem ActRow act-id (:creditor e) a (:acts w) ha))
    (have ia (= (:id a) (:creditor e))) (exact (tbl-find-id ActRow act-id (:creditor e) a (:acts w) ha))
    (cases hc (run-current w (:run a)))
    (case [false]
      (have g (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (Nat.beq (:id b) (:creditor e)) true) (= (current-members-fa xm w (:id e) b) true))))
      (intros b mb hb)
      (have nr (= (Nat.beq (:run a) (:run a)) true)) (exact (Nat.beq_refl _))
      (have u := (uniq-all ActRow act-id (fn [q :- ActRow] (Nat.beq (:run q) (:run a))) a (:acts w) (current-members-acts-nodup w hs) ma nr))
      (have ub := (tbl-all-mem ActRow _ b (:acts w) u mb))
      (have ib (= (Nat.beq (act-id b) (act-id a)) true)) (simp only [act-id]) (rw [ia]) (exact hb)
      (simp only [same-id-then ib Bool.not_true Bool.false_or] at ub)
      (have rb := (Nat.eq_of_beq_eq_true ub))
      (have hc2 (= (run-current w (:run b)) false)) (rw [rb]) (exact hc)
      (exact (current-members-fa-ncur xm w (:id e) b hs (current-members-rest-of xm w h) mb hc2))
      (simp only [fire-wait-act ha hc])
      (exact (current-members-phase-free xm w (:id e) ph-fired (current-members-free-of-freeb xm w (:id e) (:creditor e) g fbc) h)))
    (case [true]
      (simp only [fire-wait-act ha hc])
      (have h0 := (current-members-xm-cons xm (:id e) w h))
      (have h1 := (current-members-phase-free _ w (:id e) ph-fired (current-members-free-self xm w (:id e)) h0))
      (have fb0 (= (current-members-freeb xm w (:id e) (:id a)) true)) (rw [ia]) (exact fbc)
      (have hcb (forall [k :- CurrentMembersRunKey] (=> (= (tbl-any (current-members-cur k) (:comps (edge-upd w (:id e) (edge-set-phase ph-fired)))) true) (= (tbl-any (current-members-cur k) (:comps w)) true))))
      (intros k q) (exact q)
      (have fb1 := (current-members-freeb-frame xm w (edge-upd w (:id e) (edge-set-phase ph-fired)) (:id e) (:id a) (rfl) (rfl) hcb fb0))
      (have hd := (current-members-ndx-phase (:id e) (:id e) ph-fired (:edges w) (current-members-edge-not-debtor w (:id e) hs (tbl-find-has-edge w e me))))
      (exact (current-members-undo-fill xm w (edge-upd w (:id e) (edge-set-phase ph-fired)) a (:id e) res hs (tbl-find-has-edge w e me) h1 ma fb1 (rfl) hd)))))

(a/theorem current-members-act-id-pos [w :- World, b :- ActRow] (=> (= (well-formed w) true) (List.Mem b (:acts w)) (= (Nat.beq (:id b) 0) false))
  (intros h mb)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (exact (has-pos ActRow act-id (:id b) (:next-id w) (:acts w) (And.left (And.right (And.right (And.right (And.right (And.right (And.right hb)))))))
           (has-of-mem ActRow act-id b (:acts w) mb))))

(a/theorem current-members-fire-wait [xm :- (List Nat), res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-wait) true) (= (current-members xm w) true)
      (= (current-members xm (fire-wait res w e)) true))
  (intros hf hk0 h)
  (have hs := (current-members-well-formed xm w h))
  (have k1 := (Nat.eq_of_beq_eq_true hk0))
  (have nd (= (Nat.beq (:kind e) ek-dep) false)) (rw [k1])
  (cases hc (Nat.beq (:creditor e) 0))
  (case [false] (simp only [fire-wait hc]) (exact (current-members-fire-wait-act xm res w e hf nd h)))
  (case [true]
    (simp only [fire-wait hc])
    (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) hf))
    (have ec := (Nat.eq_of_beq_eq_true hc))
    (have fbc := (current-members-freeb-cred xm w e (current-members-rest-of xm w h) me nd))
    (have g (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (Nat.beq (:id b) (:creditor e)) true) (= (current-members-fa xm w (:id e) b) true))))
    (intros b mb hb)
    (rw [ec] at hb) (rw [(current-members-act-id-pos w b hs mb)] at hb) (cases hb)
    (have fr := (current-members-free-of-freeb xm w (:id e) (:creditor e) g fbc))
    (have hu (forall [e2 :- EdgeRow] (=> (= (edge-find w (:id e)) (Option.some EdgeRow e2)) (= (:marked e2) true)
                                         (= (hk-safe xm (:comps w) (:creditor e2)) true))))
    (intros e2 hf2 hm2)
    (rw [hf] at hf2)
    (have ee (= e2 e)) (exact (Option.some.inj (Eq.symm hf2)))
    (rw [ee ec]) (exact (hk-safe-nocomp xm (:comps w) 0 (comp-has-zero w hs)))
    (exact (current-members-remove-edge xm w (:id e) hu fr h))))

(tree/restate! H3 '[well-formed-fire-observe])
(a/theorem current-members-fire-edge [xm :- (List Nat), res :- RunResult, w :- World, x :- Nat]
  (=> (= (current-members xm w) true) (= (current-members xm (fire-edge res w x)) true))
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
      (case [true] (simp only [fire-edge hf hp hk1]) (exact (current-members-fire-dep xm w e hf2 hk1 h)))
      (case [false]
        (cases hk2 (Nat.beq (:kind e) ek-wait))
        (case [true] (simp only [fire-edge hf hp hk1 hk2]) (exact (current-members-fire-wait xm res w e hf2 hk2 h)))
        (case [false]
          (cases hk3 (Nat.beq (:kind e) ek-observe))
          (case [true] (simp only [fire-edge hf hp hk1 hk2 hk3]) (exact (current-members-fire-observe xm w e h)))
          (case [false] (simp only [fire-edge hf hp hk1 hk2 hk3 fire-savepoint-todo]) (exact h)))))))
(swap! (:renames H3) assoc 'well-formed-fire-edge 'current-members-fire-edge 'well-formed-invalidate 'current-members-invalidate 'well-formed-resume 'current-members-resume 'well-formed-fill-slot 'current-members-fill-slot)

;; ---- host edges (creditor 0) are held by no activation: T8 unobserve (g7's obs-one), T22 unawait
(a/theorem current-members-remove-host [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (Nat.beq (:kind e) ek-dep) false) (= (:creditor e) 0) (= (current-members xm w) true)
      (= (current-members xm (remove-edge w (:id e))) true))
  (intros hf nd ec h)
  (have hs := (current-members-well-formed xm w h))
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) hf))
  (have fbc := (current-members-freeb-cred xm w e (current-members-rest-of xm w h) me nd))
  (have g (forall [b :- ActRow] (=> (List.Mem b (:acts w)) (= (Nat.beq (:id b) (:creditor e)) true) (= (current-members-fa xm w (:id e) b) true))))
  (intros b mb hb)
  (rw [ec] at hb) (rw [(current-members-act-id-pos w b hs mb)] at hb) (cases hb)
  (have fr := (current-members-free-of-freeb xm w (:id e) (:creditor e) g fbc))
  (have hu (forall [e2 :- EdgeRow] (=> (= (edge-find w (:id e)) (Option.some EdgeRow e2)) (= (:marked e2) true)
                                       (= (hk-safe xm (:comps w) (:creditor e2)) true))))
  (intros e2 hf2 hm2)
  (rw [hf] at hf2)
  (have ee (= e2 e)) (exact (Option.some.inj (Eq.symm hf2)))
  (rw [ee ec]) (exact (hk-safe-nocomp xm (:comps w) 0 (comp-has-zero w hs)))
  (exact (current-members-remove-edge xm w (:id e) hu fr h)))
(a/theorem current-members-find-id [w :- World, x :- Nat, e :- EdgeRow]
  (=> (= (edge-find w x) (Option.some EdgeRow e)) (And (= (:id e) x) (= (edge-find w (:id e)) (Option.some EdgeRow e))))
  (intro hf)
  (have hi (= (:id e) x)) (exact (tbl-find-id EdgeRow edge-id x e (:edges w) hf))
  (apply (And.intro hi)) (rw [hi]) (exact hf))

(a/theorem current-members-t22-host-unawait [xm :- (List Nat), w :- World, x :- Nat]
  (=> (= (current-members xm w) true) (= (current-members xm (:world (t22-host-unawait w x))) true))
  (intro h)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [t22-host-unawait hf refuse]) (exact h)
  (cases hk (Bool.and (Nat.beq (:kind e) ek-wait) (Nat.beq (:creditor e) 0)))
  (simp only [t22-host-unawait hf hk refuse]) (exact h)
  (simp only [t22-host-unawait hf hk accept])
  (simp only [Bool.and_eq_true] at hk)
  (have nd (= (Nat.beq (:kind e) ek-dep) false)) (rw [(Nat.eq_of_beq_eq_true (And.left hk))])
  (have p := (current-members-find-id w x e hf))
  (rw [← (And.left p)])
  (exact (current-members-remove-host xm w e (And.right p) nd (Nat.eq_of_beq_eq_true (And.right hk)) h)))
(swap! (:renames H3) assoc 'well-formed-t22-host-unawait 'current-members-t22-host-unawait)
(a/theorem current-members-t8-unobserve [xm :- (List Nat), w :- World, x :- Nat]
  (=> (= (i7-idle w) true) (= (current-members xm w) true) (= (current-members xm (:world (t8-unobserve w x))) true))
  (intros hg h)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [t8-unobserve hf refuse]) (exact h)
  (cases hk (Nat.beq (:kind e) ek-observe))
  (simp only [t8-unobserve hf hk refuse]) (exact h)
  (simp only [t8-unobserve hf hk accept])
  (have p := (current-members-find-id w x e hf))
  (have me := (tbl-find-mem EdgeRow edge-id x e (:edges w) hf))
  (have ob := (tbl-all-mem EdgeRow _ e (:edges w) (And.right (And.right (And.right (And.right (i7-idle-keys-ok-parts _ _ _ (i7-idle-rest-of w hg)))))) me))
  (simp only [obs-one hk Bool.not_true Bool.false_or] at ob)
  (have nd (= (Nat.beq (:kind e) ek-dep) false)) (rw [(Nat.eq_of_beq_eq_true hk)])
  (rw [← (And.left p)])
  (exact (current-members-remove-host xm w e (And.right p) nd (Nat.eq_of_beq_eq_true ob) h)))
(swap! (:renames H3) assoc 'well-formed-t8-unobserve 'current-members-t8-unobserve)

;; ---- invalidate-dependents: the scanned ids name dep edges, and every edit keeps the edges' kinds
(a/defn current-members-kd [x :- Nat, e :- EdgeRow] Bool (Bool.or (Bool.not (Nat.beq (:id e) x)) (Nat.beq (:kind e) ek-dep)))
(a/defn current-members-kds [es :- (List EdgeRow), x :- Nat] Bool (tbl-all (current-members-kd x) es))
(a/theorem current-members-kds-inval [w :- World, e :- EdgeRow, xs :- (List Nat)]
  (=> (= (tbl-all (current-members-kds (:edges w)) xs) true) (= (tbl-all (current-members-kds (:edges (invalidate w e))) xs) true))
  (intro h)
  (have g (forall [y :- Nat] (=> (= (current-members-kds (:edges w) y) true) (= (current-members-kds (:edges (invalidate w e)) y) true))))
  (intros y q)
  (simp only [current-members-kds invalidate comp-upd edge-upd set-comps set-edges] at q) (simp only [current-members-kds invalidate comp-upd edge-upd set-comps set-edges])
  (have hin (forall [r :- EdgeRow] (=> (= (current-members-kd y r) true) (= (Nat.beq (edge-id r) (:id e)) true) (= (current-members-kd y (edge-set-phase ph-fired r)) true))))
  (intros r z hx) (exact z)
  (have hout (forall [r :- EdgeRow] (=> (= (current-members-kd y r) true) (= (Nat.beq (edge-id r) (:id e)) false) (= (current-members-kd y r) true))))
  (intros r z hx) (exact z)
  (exact (tbl-all-upd EdgeRow edge-id (:id e) (edge-set-phase ph-fired) _ _ hin hout (:edges w) q))
  (exact (tbl-all-mono Nat _ _ g xs h)))
(a/theorem current-members-inval-id [xm :- (List Nat), w :- World, x :- Nat]
  (=> (= (current-members-kds (:edges w) x) true) (= (current-members xm w) true) (= (current-members xm (invalidate-id w x)) true))
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
      (simp only [current-members-kd ie2 Bool.not_true Bool.false_or] at q)
      (exact (current-members-invalidate xm w e me q h)))))
(a/theorem current-members-inval-fold [xm :- (List Nat), xs :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (current-members-kds (:edges w)) xs) true) (= (current-members xm w) true) (= (current-members xm (nat-fold invalidate-id w xs)) true)))
  (induction xs)
  (case [nil] (intros w hk h) (simp only [nat-fold]) (exact h))
  (case [cons y t ih]
    (intros w hk h)
    (simp only [tbl-all Bool.and_eq_true] at hk)
    (have h1 := (current-members-inval-id xm w y (And.left hk) h))
    (have k1 (= (tbl-all (current-members-kds (:edges (invalidate-id w y))) t) true))
    (cases hf (edge-find w y))
    (case [none] (simp only [invalidate-id hf]) (exact (And.right hk)))
    (case [some e]
      (cases hp (Nat.beq (:phase e) ph-armed))
      (case [false] (simp only [invalidate-id hf hp]) (exact (And.right hk)))
      (case [true] (simp only [invalidate-id hf hp]) (exact (current-members-kds-inval w e t (And.right hk)))))
    (simp only [nat-fold]) (exact (ih (invalidate-id w y) k1 h1))))
(a/theorem current-members-scan-all [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), Q :- (=> Nat Bool), xs :- (List A)]
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
(a/theorem current-members-kds-scan [w :- World, d :- Nat]
  (=> (= (well-formed w) true) (= (tbl-all (current-members-kds (:edges w)) (tbl-scan edge-id (armed-dep-on d) (:edges w))) true))
  (intro hs)
  (have hi := (And.right (And.right (well-formed-parts w hs))))
  (simp only [ids-ok ids-unique all-ids Bool.and_eq_true] at hi)
  (have nd := (nat-nodup-app-left _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _
                (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (And.left hi))))))))
  (apply (current-members-scan-all EdgeRow edge-id (armed-dep-on d) (current-members-kds (:edges w)) (:edges w)))
  (intros r mr pr)
  (simp only [armed-dep-on Bool.and_eq_true] at pr)
  (have u := (uniq-all EdgeRow edge-id (fn [q :- EdgeRow] (Nat.beq (:kind q) ek-dep)) r (:edges w) nd mr (And.left pr)))
  (simp only [current-members-kds])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) u))
  (intros q z) (simp only [same-id-then] at z) (simp only [current-members-kd]) (exact z))
(a/theorem current-members-invalidate-dependents [xm :- (List Nat), w :- World, d :- Nat]
  (=> (= (current-members xm w) true) (= (current-members xm (invalidate-dependents w d)) true))
  (intro h) (simp only [invalidate-dependents])
  (exact (current-members-inval-fold xm _ w (current-members-kds-scan w d (current-members-well-formed xm w h)) h)))
(swap! (:renames H3) assoc 'well-formed-invalidate-dependents 'current-members-invalidate-dependents)

;; ===========================================================================
;; Part C. h3's lemmas so far, restated from the generic tree
;; ===========================================================================

(tree/restate! H3 '[well-formed-t2-write well-formed-t9-fire well-formed-t18-resource-fire well-formed-wake-closed well-formed-settle-host well-formed-fast-fill well-formed-deliver-fire])
