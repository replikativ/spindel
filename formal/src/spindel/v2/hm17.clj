(ns spindel.v2.hm17
  "release-world for the h-mem2 bundle h3 (P11): the dropped host edges are no member edges."
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
            [spindel.v2.hm16 :refer :all]))


;; ---- a host edge (observe, or a wait of creditor 0) is no member edge: its id is free
(a/theorem h17-host-free [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (ekb w) true) (= (h3 xm w) true) (List.Mem e (:edges w)) (= (not-host e) false) (= (h3-free xm w (:id e)) true))
  (intros he h me hnh)
  (have hs := (h3-sample xm w h))
  (have hr := (h3-rest-of xm w h))
  (simp only [not-host] at hnh)
  (have hh := (bnot-false _ hnh))
  (have eb := (tbl-all-mem EdgeRow _ e (:edges w) (ekb-rest-of w he) me))
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
  (have c3 := (And.left (And.right (And.right sk))))
  (have ap := (h3-act-id-pos w b hs mb))
  (cases kd (Nat.beq (:kind e) ek-dep))
  (case [true]
    (have k1 := (Nat.eq_of_beq_eq_true kd))
    (simp only [host-cred] at hh) (rw [k1] at hh) (cases hh))
  (case [false]
    (simp only [kd Bool.false_or] at c3)
    (have ca := (Nat.eq_of_beq_eq_true c3))
    (have c0 (= (:creditor e) 0))
    (simp only [host-cred Bool.or_eq_true Bool.and_eq_true] at hh)
    (cases hh)
    (case [inl ob1]
      (have nw (= (Nat.beq (:kind e) ek-wait) false)) (rw [(Nat.eq_of_beq_eq_true ob1)])
      (simp only [ekb-one nw kd Bool.false_or Bool.and_eq_true] at eb)
      (exact (Nat.eq_of_beq_eq_true (And.right eb))))
    (case [inr wt] (exact (Nat.eq_of_beq_eq_true (And.right wt))))
    (rw [← ca c0] at ap) (simp only [Nat.beq_refl] at ap) (cases ap)))

;; ---- release-world: every marked edge is a dep edge, so it stays; the dropped edges are host edges
(a/theorem h17-dok-host [xm :- (List Nat), hx :- (List Nat), cs :- (List CompRow), e :- EdgeRow]
  (=> (= (hk-e hx cs e) true) (= (hk-dok xm cs not-host e) true))
  (intro he)
  (cases hm (:marked e))
  (simp only [hk-dok hm Bool.not_false Bool.true_or Bool.or_true])
  (have p := (hk-e-marked hx cs e he hm))
  (have k1 := (Nat.eq_of_beq_eq_true (And.left p)))
  (simp only [hk-dok not-host host-cred])
  (rw [k1]))
(a/theorem h17-revoke-roots [xm :- (List Nat), hx :- (List Nat), w :- World]
  (=> (= (hmk hx w) true) (= (ekb w) true) (= (h3 xm w) true) (= (h3 xm (revoke-roots w)) true))
  (intros hk he h)
  (have h1 := (hm3-set-released xm w true h))
  (have k1 := (hmk-set-released hx w true hk))
  (have e1 := (ekb-set-released w true he))
  (have r := (hmk-rest-of hx _ k1)) (simp only [hmk-rest] at r)
  (have p := (tbl-all-mono EdgeRow (hk-e hx (:comps (set-released w true))) (hk-dok xm (:comps (set-released w true)) not-host)
               (fn [e :- EdgeRow, q :- (= (hk-e hx (:comps (set-released w true)) e) true)] (h17-dok-host xm hx (:comps (set-released w true)) e q))
               (:edges (set-released w true)) r))
  (have fr (forall [e :- EdgeRow] (=> (List.Mem e (:edges (set-released w true))) (= (not-host e) false)
                                      (= (h3-free xm (set-released w true) (:id e)) true))))
  (intros e me hp) (exact (h17-host-free xm (set-released w true) e e1 h1 me hp))
  (simp only [revoke-roots])
  (exact (hm3-set-pending-act xm _ 0 (hm3-set-pins xm _ _ (h3-drop-edges xm (set-released w true) not-host p fr h1)))))
(lcopy! H3 'inv-zero-handles)
(lcopy! EKB 'inv-zero-handles)
(lcopy! EKB 'inv-revoke-roots)
(a/theorem h17-t-release-world [xm :- (List Nat), hx :- (List Nat), gx :- (List Nat), gk :- (List Nat), w :- World]
  (=> (= (g10 gx gk w) true) (= (hmk hx w) true) (= (ekb w) true) (= (h3 xm w) true)
      (= (h3 xm (:world (t-release-world w))) true))
  (intros hg hk he h)
  (cases hr (:released w))
  (case [true] (simp only [t-release-world hr refuse]) (exact h))
  (case [false]
    (simp only [t-release-world hr accept release-world-raw])
    (exact (h3-run-cascade-g xm hx gx gk _ _ (g10-zero-handles gx gk _ (g10-revoke-roots gx gk w hg))
             (hmk-zero-handles hx _ (hmk-revoke-roots hx w hk)) (ekb-zero-handles _ (ekb-revoke-roots w he))
             (hm3-zero-handles xm _ (h17-revoke-roots xm hx w hk he h))))))
