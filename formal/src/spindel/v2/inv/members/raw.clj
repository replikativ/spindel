(ns ^:ansatz/lean spindel.v2.inv.members.raw
  "release-world for the h-mem2 bundle current-members (P11): the dropped host edges are no member edges; and the
  assembly over the 38 items: transition, host-guarded-transition and raw keep current-members on a world that satisfies chain-to-edge-kinds (current-members-raw)."
  (:require [ansatz.core :as a]
            [spindel.v2.pres.tree :as tree]
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
            [spindel.v2.inv.comp-facts :refer :all]
            [spindel.v2.inv.i10 :refer :all]
            [spindel.v2.inv.alive-runs :refer :all]
            [spindel.v2.inv.marks-step :refer :all]
            [spindel.v2.inv.marks :refer :all]
            [spindel.v2.inv.members.bundle :refer :all]
            [spindel.v2.inv.members.track-take :refer :all]
            [spindel.v2.inv.members.cascade :refer :all]
            [spindel.v2.inv.members.base :refer :all]
            [spindel.v2.inv.members.react :refer :all]
            [spindel.v2.inv.members.await-prep :refer :all]
            [spindel.v2.inv.i5 :refer :all]
            [spindel.v2.inv.i8 :refer :all]
            [spindel.v2.inv.i1-runs :refer :all]
            [spindel.v2.inv.members.fires :refer :all]
            [spindel.v2.inv.members.await-wire :refer :all]
            [spindel.v2.progress.l5 :refer :all]
            [spindel.v2.inv.members.await-fill :refer :all]
            [spindel.v2.inv.members.await-post :refer :all]
            [spindel.v2.inv.members.await-guard :refer :all]
            [spindel.v2.inv.members.await-raw :refer :all]
            [spindel.v2.inv.members.dispatch :refer :all]
            [spindel.v2.inv.members.raw-lifts :refer :all]
            [spindel.v2.inv.members.complete :refer :all]))


;; ---- a host edge (observe, or a wait of creditor 0) is no member edge: its id is free
(a/theorem current-members-host-free [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (edge-kinds w) true) (= (current-members xm w) true) (List.Mem e (:edges w)) (= (not-host e) false) (= (current-members-free xm w (:id e)) true))
  (intros he h me hnh)
  (have hs := (current-members-well-formed xm w h))
  (have hr := (current-members-rest-of xm w h))
  (simp only [not-host] at hnh)
  (have hh := (bnot-false _ hnh))
  (have eb := (tbl-all-mem EdgeRow _ e (:edges w) (edge-kinds-rest-of w he) me))
  (apply (current-members-free-by xm w (:id e)))
  (intros b r mb mr ir hxo hcur hmem hxx)
  (have u := (current-members-r-use xm w b r hr mb mr ir))
  (have ob := (And.right u))
  (simp only [current-members-ob hxo hcur Bool.not_true Bool.false_or Bool.and_eq_true] at ob)
  (have hx := (tbl-all-mem Nat _ (:id e) (act-contrib b) (And.right ob) (Iff.mp (reach-mem-iff (:id e) (act-contrib b)) hmem)))
  (simp only [current-members-x hxx Bool.false_or Bool.and_eq_true] at hx)
  (have ek := (tbl-all-mem EdgeRow _ e (:edges w) (And.right hx) me))
  (simp only [current-members-eok Nat.beq_refl Bool.not_true Bool.false_or Bool.and_eq_true] at ek)
  (have sk := (And.left ek))
  (simp only [current-members-s Bool.and_eq_true] at sk)
  (have c3 := (And.left (And.right (And.right sk))))
  (have ap := (current-members-act-id-pos w b hs mb))
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
      (simp only [edge-kinds-one nw kd Bool.false_or Bool.and_eq_true] at eb)
      (exact (Nat.eq_of_beq_eq_true (And.right eb))))
    (case [inr wt] (exact (Nat.eq_of_beq_eq_true (And.right wt))))
    (rw [← ca c0] at ap) (simp only [Nat.beq_refl] at ap) (cases ap)))

;; ---- release-world: every marked edge is a dep edge, so it stays; the dropped edges are host edges
(a/theorem current-members-dok-host [xm :- (List Nat), hx :- (List Nat), cs :- (List CompRow), e :- EdgeRow]
  (=> (= (hk-e hx cs e) true) (= (hk-dok xm cs not-host e) true))
  (intro he)
  (cases hm (:marked e))
  (simp only [hk-dok hm Bool.not_false Bool.true_or Bool.or_true])
  (have p := (hk-e-marked hx cs e he hm))
  (have k1 := (Nat.eq_of_beq_eq_true (And.left p)))
  (simp only [hk-dok not-host host-cred])
  (rw [k1]))
(a/theorem current-members-revoke-roots [xm :- (List Nat), hx :- (List Nat), w :- World]
  (=> (= (marks-waiting hx w) true) (= (edge-kinds w) true) (= (current-members xm w) true) (= (current-members xm (revoke-roots w)) true))
  (intros hk he h)
  (have h1 := (current-members-set-released xm w true h))
  (have k1 := (marks-waiting-set-released hx w true hk))
  (have e1 := (edge-kinds-set-released w true he))
  (have r := (marks-waiting-rest-of hx _ k1)) (simp only [marks-waiting-rest] at r)
  (have p := (tbl-all-mono EdgeRow (hk-e hx (:comps (set-released w true))) (hk-dok xm (:comps (set-released w true)) not-host)
               (fn [e :- EdgeRow, q :- (= (hk-e hx (:comps (set-released w true)) e) true)] (current-members-dok-host xm hx (:comps (set-released w true)) e q))
               (:edges (set-released w true)) r))
  (have fr (forall [e :- EdgeRow] (=> (List.Mem e (:edges (set-released w true))) (= (not-host e) false)
                                      (= (current-members-free xm (set-released w true) (:id e)) true))))
  (intros e me hp) (exact (current-members-host-free xm (set-released w true) e e1 h1 me hp))
  (simp only [revoke-roots])
  (exact (current-members-set-pending-act xm _ 0 (current-members-set-pins xm _ _ (current-members-drop-edges xm (set-released w true) not-host p fr h1)))))
(tree/restate! H3 '[well-formed-zero-handles])
(a/theorem current-members-t21-release-world [xm :- (List Nat), hx :- (List Nat), gx :- (List Nat), gk :- (List Nat), w :- World]
  (=> (= (i10-current-exempt gx gk w) true) (= (marks-waiting hx w) true) (= (edge-kinds w) true) (= (current-members xm w) true)
      (= (current-members xm (:world (t21-release-world w))) true))
  (intros hg hk he h)
  (cases hr (:released w))
  (case [true] (simp only [t21-release-world hr refuse]) (exact h))
  (case [false]
    (simp only [t21-release-world hr accept release-world-raw])
    (exact (current-members-run-cascade-g xm hx gx gk _ _ (i10-current-exempt-zero-handles gx gk _ (i10-current-exempt-revoke-roots gx gk w hg))
             (marks-waiting-zero-handles hx _ (marks-waiting-revoke-roots hx w hk)) (edge-kinds-zero-handles _ (edge-kinds-revoke-roots w he))
             (current-members-zero-handles xm _ (current-members-revoke-roots xm hx w hk he h))))))

;; ===========================================================================
;; The assembly: every item keeps current-members (transition), through the host guard (host-guarded-transition) and post (raw)
;; ===========================================================================
(tree/restate! H3 '[well-formed-t1-create-nonstream well-formed-t1-create-nonstream-top well-formed-t19 well-formed-t20-pin well-formed-t20-unpin well-formed-t3-create well-formed-t3-create-top well-formed-t4-spawn well-formed-t4-spawn-top well-formed-t5-start well-formed-t-schedule
            well-formed-t-handle-new well-formed-t-post well-formed-t-release well-formed-t-finalize well-formed-t-open-scope well-formed-t-detach well-formed-t-finally-enter
            well-formed-t-finally-exit well-formed-t-finally-leave
            well-formed-t1-create-source well-formed-t1-create-source-top well-formed-t-create-link well-formed-t-create-link-top well-formed-t-link-demand well-formed-require-root-open
            well-formed-t-own well-formed-t-owned-done well-formed-t-drain])

;; ---- C0: a link's realization, an append, a stream close (marks-waiting: the realized link / closed stream is a source)
(a/theorem current-members-link-realize-raw [xm :- (List Nat), hx :- (List Nat), w :- World, l :- Nat, tag :- Nat, v :- Nat, n :- Nat]
  (=> (= (tbl-has comp-id l (:comps w)) false) (= (marks-waiting hx w) true) (= (current-members xm w) true) (= (current-members xm (:world (link-realize-raw w l tag v n))) true))
  (intros hc hk h)
  (cases h1 (Nat.beq tag res-ok))
  (case [true]
    (cases h2 (Nat.beq n (:next-id w)))
    (case [false] (simp only [link-realize-raw h1 h2 refuse]) (exact h))
    (case [true]
      (simp only [link-realize-raw h1 h2 accept link-next-raw])
      (exact (current-members-realize-link xm hx (bump (source-ins w (new-link (:next-id w) root-scope-id 0))) l v false _ hc
               (marks-waiting-source-ins-fresh hx w (new-link (:next-id w) root-scope-id 0) (rfl) hk)
               (current-members-source-ins-fresh xm w (new-link (:next-id w) root-scope-id 0) (rfl) h)))))
  (case [false]
    (cases h2 (Nat.beq n 0))
    (case [false] (simp only [link-realize-raw h1 h2 refuse]) (exact h))
    (case [true]
      (cases h3 (Nat.beq tag res-none))
      (case [true] (simp only [link-realize-raw h1 h2 h3 accept]) (exact (current-members-realize-link xm hx w l 0 false 0 hc hk h)))
      (case [false]
        (cases h4 (Nat.beq tag res-err))
        (case [false] (simp only [link-realize-raw h1 h2 h3 h4 refuse]) (exact h))
        (case [true] (simp only [link-realize-raw h1 h2 h3 h4 accept]) (exact (current-members-realize-link xm hx w l v true 0 hc hk h)))))))
(a/theorem current-members-t-link-realize [xm :- (List Nat), hx :- (List Nat), w :- World, l :- Nat, tag :- Nat, v :- Nat, n :- Nat]
  (=> (= (marks-waiting hx w) true) (= (current-members xm w) true) (= (current-members xm (:world (t-link-realize w l tag v n))) true))
  (intros hk h)
  (cases hf (source-find w l)) (case' [some s]) (case' [none])
  (simp only [t-link-realize hf refuse]) (exact h)
  (have hc := (hk-source-not-comp w l (current-members-well-formed xm w h) (tbl-find-has SourceRow source-id l s (:sources w) hf)))
  (cases hg (link-idle w s))
  (simp only [t-link-realize hf hg refuse]) (exact h)
  (simp only [t-link-realize hf hg]) (exact (current-members-link-realize-raw xm hx w l tag v n hc hk h)))
(a/theorem current-members-t-append [xm :- (List Nat), hx :- (List Nat), w :- World, x :- Nat, v :- Nat, t :- Nat]
  (=> (= (marks-waiting hx w) true) (= (current-members xm w) true) (= (current-members xm (:world (t-append w x v t))) true))
  (intros hk h)
  (cases hf (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-append hf refuse]) (exact h)
  (cases hg (Bool.and (open-kind sk-stream s) (Bool.and (Nat.beq t (:next-id w)) (link-pending w (:tail s)))))
  (simp only [t-append hf hg refuse]) (exact h)
  (have hp (= (link-pending w (:tail s)) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.right (And.right hg)))
  (have hc := (hk-source-not-comp w (:tail s) (current-members-well-formed xm w h) (link-pending-has w (:tail s) hp)))
  (simp only [t-append hf hg accept append-raw])
  (exact (current-members-realize-link xm hx (bump (source-ins (source-upd w x (stream-set-tail (:next-id w))) (new-link (:next-id w) root-scope-id x))) (:tail s) v false _ hc
           (marks-waiting-source-ins-fresh hx (source-upd w x (stream-set-tail (:next-id w))) (new-link (:next-id w) root-scope-id x) (rfl)
             (marks-waiting-source-upd hx w x (stream-set-tail (:next-id w)) (stream-set-tail-id _) hk))
           (current-members-source-ins-fresh xm (source-upd w x (stream-set-tail (:next-id w))) (new-link (:next-id w) root-scope-id x) (rfl)
             (current-members-source-upd xm w x (stream-set-tail (:next-id w)) (stream-set-tail-id _) h)))))
(a/theorem current-members-t-close [xm :- (List Nat), hx :- (List Nat), w :- World, x :- Nat, tag :- Nat, v :- Nat]
  (=> (= (marks-waiting hx w) true) (= (current-members xm w) true) (= (current-members xm (:world (t-close w x tag v))) true))
  (intros hk h)
  (cases hf (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-close hf refuse]) (exact h)
  (have hc := (hk-source-not-comp w x (current-members-well-formed xm w h) (tbl-find-has SourceRow source-id x s (:sources w) hf)))
  (cases hg (Bool.and (open-kind sk-stream s) (close-tag-ok tag)))
  (simp only [t-close hf hg refuse]) (exact h)
  (simp only [t-close hf hg accept close-raw])
  (exact (current-members-close-source xm hx (end-link w (:tail s) (Nat.beq tag res-err) v) x (Eq.trans (hk-has-end-link w (:tail s) _ v x) hc)
           (marks-waiting-end-link hx w (:tail s) _ v hk) (current-members-end-link xm hx w (:tail s) _ v hk h))))

;; ---- Z#77 T28 retire-run: each retired run completes (T12 on a task run without activation, h16) or retires
;; (T13); the bundles h16 reads are carried through the runs as h3ctx
(tree/restate! H3 '[well-formed-retire-pre])
(a/defn h3ctx [w :- World] Bool
  (Bool.and (acts-parked w) (Bool.and (comp-facts w) (Bool.and (i7-idle w) (Bool.and (i10-current-exempt (List.nil Nat) (List.nil Nat) w) (Bool.and (marks-waiting (List.nil Nat) w) (edge-kinds w)))))))
(a/theorem h3ctx-parts [w :- World]
  (=> (= (h3ctx w) true)
      (And (= (acts-parked w) true) (And (= (comp-facts w) true) (And (= (i7-idle w) true) (And (= (i10-current-exempt (List.nil Nat) (List.nil Nat) w) true) (And (= (marks-waiting (List.nil Nat) w) true) (= (edge-kinds w) true)))))))
  (intro h) (simp only [h3ctx Bool.and_eq_true] at h) (exact h))
(a/theorem h3ctx-intro [w :- World]
  (=> (= (acts-parked w) true) (= (comp-facts w) true) (= (i7-idle w) true) (= (i10-current-exempt (List.nil Nat) (List.nil Nat) w) true) (= (marks-waiting (List.nil Nat) w) true) (= (edge-kinds w) true) (= (h3ctx w) true))
  (intros a b c d e f) (simp only [h3ctx a b c d e f Bool.and_self]))
(a/theorem h3ctx-retire-pre [w :- World, r :- RunRow] (=> (= (h3ctx w) true) (= (h3ctx (retire-pre w r)) true))
  (intro h) (have p := (h3ctx-parts w h))
  (exact (h3ctx-intro _ (acts-parked-retire-pre w r (And.left p)) (comp-facts-retire-pre w r (And.left (And.right p)))
           (i7-idle-retire-pre w r (And.left (And.right (And.right p)))) (i10-current-exempt-retire-pre (List.nil Nat) (List.nil Nat) w r (And.left (And.right (And.right (And.right p)))))
           (marks-waiting-retire-pre (List.nil Nat) w r (And.left (And.right (And.right (And.right (And.right p))))))
           (edge-kinds-retire-pre w r (And.right (And.right (And.right (And.right (And.right p)))))))))
(a/theorem h3ctx-retire-one [v :- Nat, w :- World, rid :- Nat] (=> (= (h3ctx w) true) (= (h3ctx (retire-one v w rid)) true))
  (intro h) (have p := (h3ctx-parts w h))
  (exact (h3ctx-intro _ (acts-parked-retire-one v w rid (And.left p)) (comp-facts-retire-one v w rid (And.left (And.right p)))
           (i7-idle-retire-one v w rid (And.left (And.right (And.right p)))) (i10-current-exempt-retire-one (List.nil Nat) (List.nil Nat) v w rid (And.left (And.right (And.right (And.right p)))))
           (marks-waiting-retire-one (List.nil Nat) v w rid (And.left (And.right p)) (And.left (And.right (And.right p))) (And.left (And.right (And.right (And.right (And.right p))))))
           (edge-kinds-retire-one v w rid (And.right (And.right (And.right (And.right (And.right p)))))))))
(a/theorem current-members-retire-one [xm :- (List Nat), v :- Nat, w :- World, rid :- Nat]
  (=> (= (h3ctx w) true) (= (current-members xm w) true) (= (current-members xm (retire-one v w rid)) true))
  (intros hc h)
  (cases hf (run-find w rid))
  (case [none] (simp only [retire-one hf]) (exact h))
  (case [some r]
    (have hp := (current-members-retire-pre xm w r h))
    (have p := (h3ctx-parts _ (h3ctx-retire-pre w r hc)))
    (cases hf1 (run-find (retire-pre w r) rid))
    (case [none] (simp only [retire-one hf hf1]) (exact hp))
    (case [some r1]
      (cases ha (Bool.and (run-alive r1) (run-of-local (retire-pre w r) r1)))
      (case [true] (simp only [retire-one hf hf1 ha])
        (have hnc := (local-run-nocomp _ r1 (comp-facts-well-formed _ (And.left (And.right p))) (bool-and-right _ _ ha)))
        (have pre (= (Bool.or (Bool.not (comp-facts-cce (retire-pre w r) r1)) (tbl-all (comp-facts-u1 r1) (:runs (retire-pre w r)))) true))
        (simp only [comp-facts-cce hnc Bool.not_false Bool.true_or])
        (exact (current-members-complete-raw-x xm (List.nil Nat) (List.nil Nat) (List.nil Nat) _ r1 _ (retire-r1-mem w r r1 rid hf1) (bool-and-left _ _ ha)
                 (retire-r1-noact w r r1 rid hf hf1) pre (task-final-res-tag _ _ v)
                 (And.left (And.right (And.right (And.right p)))) (And.left p) (And.left (And.right p)) (And.left (And.right (And.right p)))
                 (And.left (And.right (And.right (And.right (And.right p))))) (And.right (And.right (And.right (And.right (And.right p))))) hp)))
      (case [false] (simp only [retire-one hf hf1 ha t13-retire])
        (exact (current-members-run-cascade-g xm (List.nil Nat) (List.nil Nat) (List.nil Nat) _ _ (And.left (And.right (And.right (And.right p))))
                 (And.left (And.right (And.right (And.right (And.right p))))) (And.right (And.right (And.right (And.right (And.right p))))) hp))))))
(a/theorem current-members-t28-retire-local [xm :- (List Nat), w :- World, v :- Nat]
  (=> (= (h3ctx w) true) (= (current-members xm w) true) (= (current-members xm (:world (t28-retire-local w v))) true))
  (intros hc h)
  (cases hm (tbl-any (run-of-local w) (:runs w)))
  (case [false] (simp only [t28-retire-local hm refuse]) (exact h))
  (case [true] (simp only [t28-retire-local hm accept])
    (exact (nat-fold-pres2 h3ctx (current-members xm) (retire-one v) (h3ctx-retire-one v) (current-members-retire-one xm v) (local-order w) w hc h))))

(a/theorem current-members-transition [xm :- (List Nat), w :- World, it :- Item]
  (=> (= (chain-to-edge-kinds w) true) (= (current-members xm w) true) (= (current-members xm (:world (transition w it))) true))
  (intros hp h)
  (have hgd := (chain-to-edge-kinds-comp-facts w hp))
  (have hg7 := (chain-to-edge-kinds-i7-idle w hp))
  (have hga := (chain-to-edge-kinds-acts-parked w hp))
  (have har := (chain-to-edge-kinds-alive-run-latest w hp))
  (have hke := (chain-to-edge-kinds-edge-kinds w hp))
  (have hk := (chain-to-edge-kinds-marks-waiting w hp))
  (have hgr := (chain-to-edge-kinds-i10-current w hp))
  (have hg10 := (chain-to-edge-kinds-i10-current w hp)) (simp only [i10-current] at hg10)
  (cases it)
  (case [create-source st kind v fresh] (simp only [transition]) (cases hc (create-in-scope-refused w st))
    (case [false] (simp only [hc]) (exact (current-members-require-root-open xm w _ _ h (current-members-t1-create-source xm w st kind v fresh h))))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [create-source-top scope kind v fresh] (simp only [transition]) (cases hr (world-released w))
    (case [true] (simp only [hr refuse]) (exact h))
    (case [false] (simp only [hr]) (exact (current-members-require-root-open xm w _ _ h (current-members-t1-create-source-top xm w scope kind v fresh h)))))
  (case [write x v] (simp only [transition]) (exact (current-members-t2-write xm w _ _ h)))
  (case [track st x k fresh] (simp only [transition]) (cases hc (in-cleanup w st))
    (case [false] (simp only [hc]) (exact (current-members-t7-track xm w _ _ _ _ hc hg7 hga har hk h)))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [observe d cb fresh] (simp only [transition]) (cases hr (world-released w))
    (case [true] (simp only [hr refuse]) (exact h))
    (case [false] (simp only [hr t8-observe]) (cases hs (source-kind-at w sk-stream d))
      (case [false] (simp only [hs]) (exact (current-members-t8-observe-any-kind xm w _ _ _ hp h)))
      (case [true] (simp only [hs refuse]) (exact h))))
  (case [unobserve e] (simp only [transition]) (exact (current-members-t8-unobserve xm w _ hg7 h)))
  (case [fire e tag val] (simp only [transition]) (exact (current-members-t9-fire xm w _ _ _ h)))
  (case [resource-ack z] (simp only [transition]) (exact (current-members-t15-resource-ack xm (List.nil Nat) (List.nil Nat) (List.nil Nat) w _ hk hg10 hke h)))
  (case [arm st kind k fresh] (simp only [transition]) (cases hc (arm-refused w st))
    (case [false] (simp only [hc]) (exact (current-members-t17-arm xm w _ _ _ _ hgr hgd h)))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [resource-fire z tag val] (simp only [transition]) (exact (current-members-t18-resource-fire xm w _ _ _ h)))
  (case [handle-drop x] (simp only [transition]) (exact (current-members-t19 xm w _ h)))
  (case [pin x] (simp only [transition]) (cases hr (world-released w))
    (case [true] (simp only [hr refuse]) (exact h))
    (case [false] (simp only [hr]) (exact (current-members-t20-pin xm w _ h))))
  (case [unpin x] (simp only [transition]) (exact (current-members-t20-unpin xm w _ h)))
  (case [create-comp st c i b] (simp only [transition]) (cases hc (create-refused w st))
    (case [false] (simp only [hc]) (exact (current-members-t3-create xm w _ _ _ _ h)))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [create-comp-top sc c i b] (simp only [transition]) (cases hr (world-released w))
    (case [true] (simp only [hr refuse]) (exact h))
    (case [false] (simp only [hr]) (exact (current-members-t3-create-top xm w _ _ _ _ h))))
  (case [spawn st b fresh ins loc] (simp only [transition]) (cases hc (create-in-scope-refused w st))
    (case [false] (simp only [hc]) (cases hl (spawn-local-refused w st loc))
      (case [false] (simp only [hl]) (exact (current-members-t4-spawn xm w _ _ _ _ _ h)))
      (case [true] (simp only [hl refuse]) (exact h)))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [spawn-top sc b fresh ins loc] (simp only [transition]) (cases hr (world-released w))
    (case [true] (simp only [hr refuse]) (exact h))
    (case [false] (simp only [hr]) (exact (current-members-t4-spawn-top xm w _ _ _ _ _ h))))
  (case [start c fresh] (simp only [transition]) (exact (current-members-t5-start xm w _ _ h)))
  (case [await st ds m k fresh mine] (exact (And.left (current-members-transition-await-outcome xm w st ds m k fresh mine hp h))))
  (case [dispatch-comp c fresh] (simp only [transition]) (exact (And.left (current-members-t11-dispatch-outcome xm w c fresh hp h))))
  (case [complete st tag val] (simp only [transition]) (cases hc (complete-refused w st tag))
    (case [false] (simp only [hc])
      (exact (current-members-t12-complete xm (List.nil Nat) (List.nil Nat) (List.nil Nat) w st tag val (refused-tag-ok w st tag hc) hgr hg10 hga hgd hg7 hk hke h)))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [schedule r] (simp only [transition]) (exact (current-members-t-schedule xm w _ h)))
  (case [host-await d fresh] (exact (current-members-transition-host-await xm w d fresh hp h)))
  (case [host-unawait e] (simp only [transition]) (exact (current-members-t22-host-unawait xm w _ h)))
  (case [handle-new x] (simp only [transition]) (cases hr (world-released w))
    (case [true] (simp only [hr refuse]) (exact h))
    (case [false] (simp only [hr]) (exact (current-members-t-handle-new xm w _ h))))
  (case [deliver x v] (simp only [transition]) (exact (current-members-t-deliver xm (List.nil Nat) w _ _ hk h)))
  (case [post x v] (simp only [transition]) (exact (current-members-t-post xm w _ _ h)))
  (case [take st x k fresh] (simp only [transition]) (cases hc (take-refused w st x))
    (case [false] (simp only [hc]) (exact (current-members-t-take xm w _ _ _ _ hgr hgd h)))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [release x] (simp only [transition]) (exact (current-members-t-release xm w _ h)))
  (case [finalize r] (simp only [transition]) (exact (current-members-t-finalize xm w _ h)))
  (case [cancel r] (simp only [transition]) (exact (current-members-t14-host-cancel xm (List.nil Nat) (List.nil Nat) (List.nil Nat) w _ hk hg10 hke h)))
  (case [release-world] (simp only [transition]) (exact (current-members-t21-release-world xm (List.nil Nat) (List.nil Nat) (List.nil Nat) w hg10 hk hke h)))
  (case [open-scope st s] (simp only [transition]) (exact (current-members-t-open-scope xm w _ _ h)))
  (case [close-scope s] (simp only [transition]) (exact (current-members-t-close-scope xm (List.nil Nat) (List.nil Nat) (List.nil Nat) w _ hk hg10 hke h)))
  (case [detach k s] (simp only [transition]) (cases hc (detach-local-refused w k s))
    (case [false] (simp only [hc]) (exact (current-members-t-detach xm w _ _ h)))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [finally-enter st] (simp only [transition]) (exact (current-members-t-finally-enter xm w _ h)))
  (case [finally-exit st] (simp only [transition]) (exact (current-members-t-finally-exit xm w _ h)))
  (case [slice-exit r] (simp only [transition]) (exact (current-members-t-slice-exit xm (List.nil Nat) (List.nil Nat) (List.nil Nat) w _ hk hg10 hke h)))
  (case [create-link st l] (simp only [transition]) (cases hc (create-refused w st))
    (case [false] (simp only [hc]) (exact (current-members-require-root-open xm w _ _ h (current-members-t-create-link xm w st l h))))
    (case [true] (simp only [hc refuse]) (exact h)))
  (case [create-link-top sc l] (simp only [transition]) (cases hr (world-released w))
    (case [true] (simp only [hr refuse]) (exact h))
    (case [false] (simp only [hr]) (exact (current-members-require-root-open xm w _ _ h (current-members-t-create-link-top xm w sc l h)))))
  (case [link-demand l k] (simp only [transition]) (cases hr (world-released w))
    (case [true] (simp only [hr refuse]) (exact h))
    (case [false] (simp only [hr]) (exact (current-members-t-link-demand xm w _ _ h))))
  (case [link-realize l tag v n] (simp only [transition]) (cases hr (world-released w))
    (case [true] (simp only [hr refuse]) (exact h))
    (case [false] (simp only [hr]) (exact (current-members-require-root-open xm w _ _ h (current-members-t-link-realize xm (List.nil Nat) w l tag v n hk h)))))
  (case [append x v t] (simp only [transition]) (cases hr (world-released w))
    (case [true] (simp only [hr refuse]) (exact h))
    (case [false] (simp only [hr]) (exact (current-members-require-root-open xm w _ _ h (current-members-t-append xm (List.nil Nat) w x v t hk h)))))
  (case [close x tag v] (simp only [transition]) (exact (current-members-t-close xm (List.nil Nat) w _ _ _ hk h)))
  (case [finally-leave st] (simp only [transition]) (exact (current-members-t-finally-leave xm w _ h)))
  (case [own s m] (simp only [transition]) (exact (current-members-t-own xm w _ _ h)))
  (case [owned-done s c] (simp only [transition]) (exact (current-members-t-owned-done xm w _ _ h)))
  (case [drain ids] (simp only [transition]) (exact (current-members-t-drain xm w _ h)))
  (case [retire-local v] (simp only [transition]) (exact (current-members-t28-retire-local xm w _ (h3ctx-intro w hga hgd hg7 hg10 hk hke) h))))

(a/theorem current-members-raw [xm :- (List Nat), w :- World, it :- Item]
  (=> (= (chain-to-edge-kinds w) true) (= (current-members xm w) true) (= (current-members xm (:world (raw w it))) true))
  (intros hp h)
  (exact (current-members-raw-lift xm w it hp (current-members-host-guarded-transition-lift xm w it h (current-members-transition xm w it hp h)))))
