(ns spindel.v2.hm17
  "release-world for the h-mem2 bundle h3 (P11): the dropped host edges are no member edges; and the
  assembly over the 38 items: raw0, raw0g and raw keep h3 on a world that satisfies p3la (h17-raw-h3)."
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

;; ===========================================================================
;; The assembly: every item keeps h3 (raw0), through the host guard (raw0g) and post (raw)
;; ===========================================================================
(doseq [t '[t1-full-inv t1-top-inv t19-inv t20-pin-inv t20-unpin-inv t3-inv t3-top-inv t4-inv t4-top-inv t5-inv sched-inv
            t-handle-new-inv t-post-inv t-release-inv t-finalize-inv t-open-scope-inv t-detach-inv t-finally-enter-inv
            t-finally-exit-inv]]
  (lcopy! H3 t))

(a/theorem h17-raw0-h3 [xm :- (List Nat), w :- World, it :- Item]
  (=> (= (p3la w) true) (= (h3 xm w) true) (= (h3 xm (:world (raw0 w it))) true))
  (intros hp h)
  (have hgd := (p3la-gd w hp))
  (have hg7 := (p3la-g7 w hp))
  (have hga := (p3la-ga w hp))
  (have har := (p3la-ar w hp))
  (have hke := (p3la-ekb w hp))
  (have hk := (p3la-hmk w hp))
  (have hgr := (p3la-g10r w hp))
  (have hg10 := (p3la-g10r w hp)) (simp only [g10r] at hg10)
  (cases it)
  (case [create-source st kind v fresh] (simp only [raw0]) (cases hc (body-shut w st))
    (case [false] (simp only [hc]) (exact (t1-full-h3 xm w _ _ _ _ h)))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [create-source-top scope kind v fresh] (simp only [raw0]) (exact (t1-top-h3 xm w _ _ _ _ h)))
  (case [write x v] (simp only [raw0]) (exact (t2-h3 xm w _ _ h)))
  (case [track st x k fresh] (simp only [raw0]) (cases hc (in-cleanup w st))
    (case [false] (simp only [hc]) (exact (t7-h3 xm w _ _ _ _ hc hg7 hga har hk h)))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [observe d cb fresh] (simp only [raw0]) (exact (h15-t8-full-h3 xm w _ _ _ hp h)))
  (case [unobserve e] (simp only [raw0]) (exact (t8-unobserve-hm3 xm w _ hg7 h)))
  (case [fire e tag val] (simp only [raw0]) (exact (t9-h3 xm w _ _ _ h)))
  (case [resource-ack z] (simp only [raw0]) (exact (t15-full-h3 xm (List.nil Nat) (List.nil Nat) (List.nil Nat) w _ hk hg10 hke h)))
  (case [arm st kind k fresh] (simp only [raw0]) (cases hc (in-cleanup w st))
    (case [false] (simp only [hc]) (exact (t17-h3 xm w _ _ _ _ hgr hgd h)))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [resource-fire z tag val] (simp only [raw0]) (exact (t18-h3 xm w _ _ _ h)))
  (case [handle-drop x] (simp only [raw0]) (exact (t19-h3 xm w _ h)))
  (case [pin x] (simp only [raw0]) (exact (t20-pin-h3 xm w _ h)))
  (case [unpin x] (simp only [raw0]) (exact (t20-unpin-h3 xm w _ h)))
  (case [create-comp st c i b] (simp only [raw0]) (cases hc (in-cleanup w st))
    (case [false] (simp only [hc]) (exact (t3-h3 xm w _ _ _ _ h)))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [create-comp-top sc c i b] (simp only [raw0]) (exact (t3-top-h3 xm w _ _ _ _ h)))
  (case [spawn st b fresh ins] (simp only [raw0]) (cases hc (body-shut w st))
    (case [false] (simp only [hc]) (exact (t4-h3 xm w _ _ _ _ h)))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [spawn-top sc b fresh ins] (simp only [raw0]) (exact (t4-top-h3 xm w _ _ _ _ h)))
  (case [start c fresh] (simp only [raw0]) (exact (t5-h3 xm w _ _ h)))
  (case [await st ds m k fresh mine] (exact (And.left (h12-raw0-await-outcome xm w st ds m k fresh mine hp h))))
  (case [dispatch-comp c fresh] (simp only [raw0]) (exact (And.left (h14-t11-outcome xm w c fresh hp h))))
  (case [complete st tag val] (simp only [raw0]) (cases hc (complete-refused w st tag))
    (case [false] (simp only [hc])
      (exact (h16-t12-h3 xm (List.nil Nat) (List.nil Nat) (List.nil Nat) w st tag val (refused-tag-ok w st tag hc) hgr hg10 hga hgd hg7 hk hke h)))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [schedule r] (simp only [raw0]) (exact (sched-h3 xm w _ h)))
  (case [host-await d fresh] (exact (h15-raw0-host-await-h3 xm w d fresh hp h)))
  (case [host-unawait e] (simp only [raw0]) (exact (t22-un-hm3 xm w _ h)))
  (case [handle-new x] (simp only [raw0]) (exact (t-handle-new-h3 xm w _ h)))
  (case [deliver x v] (simp only [raw0]) (exact (t-deliver-h3 xm (List.nil Nat) w _ _ hk h)))
  (case [post x v] (simp only [raw0]) (exact (t-post-h3 xm w _ _ h)))
  (case [take st x k fresh] (simp only [raw0]) (exact (t-take-h3 xm w _ _ _ _ hgr hgd h)))
  (case [release x] (simp only [raw0]) (exact (t-release-h3 xm w _ h)))
  (case [finalize r] (simp only [raw0]) (exact (t-finalize-h3 xm w _ h)))
  (case [cancel r] (simp only [raw0]) (exact (t-cancel-h3 xm (List.nil Nat) (List.nil Nat) (List.nil Nat) w _ hk hg10 hke h)))
  (case [release-world] (simp only [raw0]) (exact (h17-t-release-world xm (List.nil Nat) (List.nil Nat) (List.nil Nat) w hg10 hk hke h)))
  (case [open-scope st s] (simp only [raw0]) (exact (t-open-scope-h3 xm w _ _ h)))
  (case [close-scope s] (simp only [raw0]) (exact (t-close-scope-h3 xm (List.nil Nat) (List.nil Nat) (List.nil Nat) w _ hk hg10 hke h)))
  (case [detach k s] (simp only [raw0]) (exact (t-detach-h3 xm w _ _ h)))
  (case [finally-enter st] (simp only [raw0]) (exact (t-finally-enter-h3 xm w _ h)))
  (case [finally-exit st] (simp only [raw0]) (exact (t-finally-exit-h3 xm w _ h)))
  (case [slice-exit r] (simp only [raw0]) (exact (t-slice-exit-h3 xm (List.nil Nat) (List.nil Nat) (List.nil Nat) w _ hk hg10 hke h))))

(a/theorem h17-raw-h3 [xm :- (List Nat), w :- World, it :- Item]
  (=> (= (p3la w) true) (= (h3 xm w) true) (= (h3 xm (:world (raw w it))) true))
  (intros hp h)
  (exact (h15-raw-lift xm w it hp (h15-raw0g-lift xm w it h (h17-raw0-h3 xm w it hp h)))))
