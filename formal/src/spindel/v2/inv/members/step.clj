(ns ^:ansatz/lean spindel.v2.inv.members.step
  "Rule R for the h-mem2 bundle current-members (P11): detach, the normalization pass (demote), the filter."
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
            [spindel.v2.inv.members.complete :refer :all]
            [spindel.v2.inv.members.raw :refer :all]
            [spindel.v2.inv.tomb :refer :all]))


;; ---- detach: an orphan source is no computation (its finalize needs that); tasks and computations lose the owner
(a/theorem current-members-detach-source [xm :- (List Nat), hx :- (List Nat), w :- World, x :- Nat]
  (=> (= (tbl-has comp-id x (:comps w)) false) (= (marks-waiting hx w) true) (= (current-members xm w) true)
      (= (current-members xm (detach-source w x)) true))
  (intros hc hk h)
  (have h1 := (current-members-wake-closed xm (source-upd w x source-detach-row) x (current-members-source-upd xm w x source-detach-row source-detach-row-id h)))
  (have k1 := (marks-waiting-wake-closed hx (source-upd w x source-detach-row) x (marks-waiting-source-upd hx w x source-detach-row source-detach-row-id hk)))
  (have hc2 (= (tbl-has comp-id x (:comps (wake-closed (source-upd w x source-detach-row) x))) false))
  (exact (Eq.trans (hk-has-wake-closed (source-upd w x source-detach-row) x x) hc))
  (exact (current-members-t10-finalize-debtor xm hx (wake-closed (source-upd w x source-detach-row) x) x hc2 k1 h1)))
(a/theorem current-members-step-fold-noc [xm :- (List Nat), hx :- (List Nat), xs :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (hk-noc (:comps w)) xs) true) (= (marks-waiting hx w) true) (= (current-members xm w) true)
                           (= (current-members xm (nat-fold detach-source w xs)) true)))
  (induction xs)
  (case [nil] (intros w hn hk h) (simp only [nat-fold]) (exact h))
  (case [cons a t ih]
    (intros w hn hk h)
    (simp only [tbl-all Bool.and_eq_true] at hn)
    (have na := (And.left hn)) (simp only [hk-noc] at na)
    (have na2 := (bnot-true _ na))
    (simp only [nat-fold])
    (exact (ih (detach-source w a) (hk-noc-all (:comps w) (:comps (detach-source w a)) t (hk-has-detach-source w a) (And.right hn))
             (marks-waiting-detach-source hx w a na2 hk) (current-members-detach-source xm hx w a na2 hk h)))))
(a/theorem current-members-detach-task [xm :- (List Nat), w :- World, x :- Nat] (=> (= (current-members xm w) true) (= (current-members xm (detach-task w x)) true))
  (intro h) (simp only [detach-task])
  (exact (current-members-task-upd-m xm w x task-detach-row (fn [t :- TaskRow] (Eq.refl (task-id t))) (fn [t :- TaskRow] (Eq.refl (:run t))) h)))
(a/theorem current-members-detach-comp [xm :- (List Nat), w :- World, x :- Nat] (=> (= (current-members xm w) true) (= (current-members xm (detach-comp w x)) true))
  (intro h) (simp only [detach-comp])
  (exact (current-members-comp-upd-m xm w x comp-detach-row (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (:pending c)))
           (fn [c :- CompRow] (Nat.le_refl (:epoch c))) (fn [c :- CompRow, q :- (= (waiting-strongly c) true)] q)
           (fn [c :- CompRow, q :- (= (Nat.blt (:done-epoch c) (:epoch c)) true)] q) h)))
(a/theorem current-members-detach [xm :- (List Nat), hx :- (List Nat), w :- World]
  (=> (= (marks-waiting hx w) true) (= (current-members xm w) true) (= (current-members xm (detach w)) true))
  (intros hk h)
  (have n0 := (hk-sources-noc w (source-orphan w) (current-members-well-formed xm w h)))
  (have h1 := (current-members-step-fold-noc xm hx (tbl-scan source-id (source-orphan w) (:sources w)) w n0 hk h))
  (simp only [detach])
  (exact (current-members-nat-fold xm detach-comp (current-members-detach-comp xm) (tbl-scan comp-id (comp-orphan w) (:comps w)) _
           (current-members-nat-fold xm detach-task (current-members-detach-task xm) (tbl-scan task-id (task-orphan w) (:tasks w)) _ h1))))

;; ===========================================================================
;; The frame bundle members-round-frame zl zf zd zs: facts that the frame current-members-fm transports, carried through the cascades
;; of the normalization pass (a part of the generic tree: its sites below).
;;   - every id of zf is free (current-members-free zl): the non-dep edges on the round's strays, free at the pass start
;;   - no activation holds a current run of a computation of zd (the strays demoted so far)
;;   - every edge is a dep edge, or its debtor is outside zs, or its id is in zf
;; ===========================================================================
(a/defn members-round-frame-nr [cs :- (List CompRow), d :- Nat, b :- ActRow, r :- RunRow] Bool
  (Bool.not (Bool.and (Nat.beq (:id r) (:run b)) (Bool.and (Nat.beq (:of r) d) (tbl-any (current-members-cur (current-members-run-key r)) cs)))))
(a/defn members-round-frame-nb [cs :- (List CompRow), rs :- (List RunRow), d :- Nat, b :- ActRow] Bool (tbl-all (members-round-frame-nr cs d b) rs))
(a/defn members-round-frame-nh [w :- World, d :- Nat] Bool (tbl-all (members-round-frame-nb (:comps w) (:runs w) d) (:acts w)))
(a/defn members-round-frame-e [S :- (List Nat), F :- (List Nat), e :- EdgeRow] Bool
  (Bool.or (Nat.beq (:kind e) ek-dep) (Bool.or (Bool.not (reach-mem (:debtor e) S)) (reach-mem (:id e) F))))
(a/defn members-round-frame-rest [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] Bool
  (Bool.and (tbl-all (current-members-free zl w) zf) (Bool.and (tbl-all (members-round-frame-nh w) zd) (tbl-all (members-round-frame-e zs zf) (:edges w)))))
(a/defn members-round-frame [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] Bool (Bool.and (well-formed w) (members-round-frame-rest zl zf zd zs w)))
(a/theorem members-round-frame-well-formed [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] (=> (= (members-round-frame zl zf zd zs w) true) (= (well-formed w) true))
  (intro h) (simp only [members-round-frame Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem members-round-frame-rest-of [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] (=> (= (members-round-frame zl zf zd zs w) true) (= (members-round-frame-rest zl zf zd zs w) true))
  (intro h) (simp only [members-round-frame Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem members-round-frame-intro [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] (=> (= (well-formed w) true) (= (members-round-frame-rest zl zf zd zs w) true) (= (members-round-frame zl zf zd zs w) true))
  (intros h1 h2) (simp only [members-round-frame h1 h2 Bool.and_self]))
(a/theorem members-round-frame-parts [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World]
  (=> (= (members-round-frame zl zf zd zs w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (members-round-frame-well-formed zl zf zd zs w h))))
(a/theorem members-round-frame-fr [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] (=> (= (members-round-frame-rest zl zf zd zs w) true) (= (tbl-all (current-members-free zl w) zf) true))
  (intro h) (simp only [members-round-frame-rest Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem members-round-frame-nhs [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] (=> (= (members-round-frame-rest zl zf zd zs w) true) (= (tbl-all (members-round-frame-nh w) zd) true))
  (intro h) (simp only [members-round-frame-rest Bool.and_eq_true] at h) (exact (And.left (And.right h))))
(a/theorem members-round-frame-er [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] (=> (= (members-round-frame-rest zl zf zd zs w) true) (= (tbl-all (members-round-frame-e zs zf) (:edges w)) true))
  (intro h) (simp only [members-round-frame-rest Bool.and_eq_true] at h) (exact (And.right (And.right h))))
(a/theorem members-round-frame-rest-mk [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World]
  (=> (= (tbl-all (current-members-free zl w) zf) true) (= (tbl-all (members-round-frame-nh w) zd) true) (= (tbl-all (members-round-frame-e zs zf) (:edges w)) true)
      (= (members-round-frame-rest zl zf zd zs w) true))
  (intros h1 h2 h3) (simp only [members-round-frame-rest h1 h2 h3 Bool.and_self]))

(a/theorem members-round-frame-nh-of [w :- World, d :- Nat] (=> (= (members-round-frame-nh w d) true) (current-members-nh w d))
  (intro h)
  (apply current-members-nh-mk)
  (intros a r ma mr ir ho hc)
  (simp only [members-round-frame-nh] at h)
  (have q := (tbl-all-mem RunRow _ r (:runs w) (tbl-all-mem ActRow _ a (:acts w) h ma) mr))
  (have i1 (= (Nat.beq (:id r) (:run a)) true)) (rw [ir]) (exact (Nat.beq_refl _))
  (have i2 (= (Nat.beq (:of r) d) true)) (rw [ho]) (exact (Nat.beq_refl _))
  (simp only [members-round-frame-nr i1 i2 hc Bool.and_self Bool.not_true] at q)
  (cases q))
(a/theorem members-round-frame-nh-mk [w :- World, d :- Nat] (=> (current-members-nh w d) (= (members-round-frame-nh w d) true))
  (intro h)
  (simp only [members-round-frame-nh])
  (apply (all-of-mem ActRow _ (:acts w)))
  (intros a ma)
  (apply (all-of-mem RunRow _ (:runs w)))
  (intros r mr)
  (cases i1 (Nat.beq (:id r) (:run a)))
  (case [false] (simp only [members-round-frame-nr i1 Bool.false_and Bool.not_false]))
  (case [true]
    (cases i2 (Nat.beq (:of r) d))
    (case [false] (simp only [members-round-frame-nr i2 Bool.false_and Bool.and_false Bool.not_false]))
    (case [true]
      (cases hc (tbl-any (current-members-cur (current-members-run-key r)) (:comps w)))
      (case [false] (simp only [members-round-frame-nr hc Bool.and_false Bool.not_false]))
      (case [true]
        (exact (False.elim (current-members-nh-use w d h a r ma mr (Nat.eq_of_beq_eq_true i1) (Nat.eq_of_beq_eq_true i2) hc)))))))
;; the transport: the frame moves the first two parts; the edge part is the operation's own
(a/theorem members-round-frame-move [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, w2 :- World]
  (=> (current-members-fm w w2) (= (tbl-all (members-round-frame-e zs zf) (:edges w2)) true) (= (members-round-frame-rest zl zf zd zs w) true) (= (members-round-frame-rest zl zf zd zs w2) true))
  (intros hf he h)
  (exact (members-round-frame-rest-mk zl zf zd zs w2
           (tbl-all-mono Nat (current-members-free zl w) (current-members-free zl w2)
             (fn [y :- Nat, q :- (= (current-members-free zl w y) true)] (fm-free zl w w2 y hf q)) zf (members-round-frame-fr zl zf zd zs w h))
           (tbl-all-mono Nat (members-round-frame-nh w) (members-round-frame-nh w2)
             (fn [d :- Nat, q :- (= (members-round-frame-nh w d) true)] (members-round-frame-nh-mk w2 d (current-members-nh-fm w w2 d hf (members-round-frame-nh-of w d q)))) zd (members-round-frame-nhs zl zf zd zs w h))
           he)))
(a/theorem members-round-frame-e-keep [S :- (List Nat), F :- (List Nat), f :- (=> EdgeRow EdgeRow),
                      hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                      hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                      hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))), e :- EdgeRow]
  (=> (= (members-round-frame-e S F e) true) (= (members-round-frame-e S F (f e)) true))
  (intro h)
  (have i1 (= (:id (f e)) (:id e))) (exact (hid e))
  (simp only [members-round-frame-e (hk e) (hd e) i1]) (simp only [members-round-frame-e] at h) (exact h))

;; ---- frames of the two row deletions
(a/theorem members-round-frame-fm-run-del [w :- World, x :- Nat] (current-members-fm w (run-del w x))
  (apply fm-mk)
  (exact (fm-acts-of w w (fm-refl w)))
  (simp only [run-del set-runs])
  (exact (tbl-all-del RunRow run-id x (fm-rr (:runs w)) (fm-rr (:runs w))
           (fn [q :- RunRow, hq :- (= (fm-rr (:runs w) q) true), hx :- (= (Nat.beq (run-id q) x) false)] hq) (:runs w) (fm-runs-of w w (fm-refl w))))
  (intros k hc) (exact hc))
(a/theorem members-round-frame-fm-comp-del [w :- World, x :- Nat] (current-members-fm w (comp-del w x))
  (apply fm-mk)
  (exact (fm-acts-of w w (fm-refl w)))
  (exact (fm-runs-of w w (fm-refl w)))
  (intros k hc) (simp only [comp-del set-comps] at hc) (exact (current-members-any-del-back CompRow comp-id x (current-members-cur k) (:comps w) hc)))

;; ---- the row-function edits (the cells of members-round-frame's sites)
(a/theorem members-round-frame-comp-upd-m [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                          hep :- (forall [c :- CompRow] (<= (:epoch c) (:epoch (f c))))]
  (=> (= (members-round-frame zl zf zd zs w) true) (= (members-round-frame zl zf zd zs (comp-upd w x f)) true))
  (intro h)
  (exact (members-round-frame-intro zl zf zd zs _ (well-formed-comp-upd w x f hid hp (members-round-frame-well-formed zl zf zd zs w h))
           (members-round-frame-move zl zf zd zs w (comp-upd w x f) (fm-comp-upd w x f hid hep) (members-round-frame-er zl zf zd zs w (members-round-frame-rest-of zl zf zd zs w h)) (members-round-frame-rest-of zl zf zd zs w h)))))
(a/theorem members-round-frame-run-upd-m [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                         hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         hk :- (forall [q :- RunRow] (= (current-members-run-key (f q)) (current-members-run-key q)))]
  (=> (= (members-round-frame zl zf zd zs w) true) (= (members-round-frame zl zf zd zs (run-upd w x f)) true))
  (intro h)
  (exact (members-round-frame-intro zl zf zd zs _ (well-formed-run-upd w x f hid (members-round-frame-well-formed zl zf zd zs w h))
           (members-round-frame-move zl zf zd zs w (run-upd w x f) (fm-run-upd w x f hk) (members-round-frame-er zl zf zd zs w (members-round-frame-rest-of zl zf zd zs w h)) (members-round-frame-rest-of zl zf zd zs w h)))))
(a/theorem members-round-frame-task-upd [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                        hid :- (forall [r :- TaskRow] (= (task-id (f r)) (task-id r)))]
  (=> (= (members-round-frame zl zf zd zs w) true) (= (members-round-frame zl zf zd zs (task-upd w x f)) true))
  (intro h)
  (exact (members-round-frame-intro zl zf zd zs _ (well-formed-task-upd w x f hid (members-round-frame-well-formed zl zf zd zs w h))
           (members-round-frame-move zl zf zd zs w (task-upd w x f) (fm-task-upd w x f) (members-round-frame-er zl zf zd zs w (members-round-frame-rest-of zl zf zd zs w h)) (members-round-frame-rest-of zl zf zd zs w h)))))
(a/theorem members-round-frame-edge-upd [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                        hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                        hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                        hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                        hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                        hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e)))]
  (=> (= (members-round-frame zl zf zd zs w) true) (= (members-round-frame zl zf zd zs (edge-upd w x f)) true))
  (intro h)
  (exact (members-round-frame-intro zl zf zd zs _ (well-formed-edge-upd w x f hid hk hc hd hm (members-round-frame-well-formed zl zf zd zs w h))
           (members-round-frame-move zl zf zd zs w (edge-upd w x f) (fm-edge-upd w x f)
             (ep-edge-upd (members-round-frame-e zs zf) w x f (members-round-frame-e-keep zs zf f hid hk hd) (members-round-frame-er zl zf zd zs w (members-round-frame-rest-of zl zf zd zs w h)))
             (members-round-frame-rest-of zl zf zd zs w h)))))
(a/theorem members-round-frame-act-upd-m [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, x :- Nat, f :- (=> ActRow ActRow),
                         hid :- (forall [r :- ActRow] (= (act-id (f r)) (act-id r))), hfm :- (current-members-fm w (act-upd w x f))]
  (=> (= (members-round-frame zl zf zd zs w) true) (= (members-round-frame zl zf zd zs (act-upd w x f)) true))
  (intro h)
  (exact (members-round-frame-intro zl zf zd zs _ (well-formed-act-upd w x f hid (members-round-frame-well-formed zl zf zd zs w h))
           (members-round-frame-move zl zf zd zs w (act-upd w x f) hfm (members-round-frame-er zl zf zd zs w (members-round-frame-rest-of zl zf zd zs w h)) (members-round-frame-rest-of zl zf zd zs w h)))))

(def FB (mk-bundle 'members-round-frame '[zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat)] "members-round-frame-" {}))
(swap! (:renames FB) assoc 'well-formed-parts 'members-round-frame-parts 'well-formed-task-upd 'members-round-frame-task-upd 'well-formed-edge-upd 'members-round-frame-edge-upd
       'well-formed-comp-upd 'fb-comp-upd-NONE 'well-formed-run-upd 'fb-run-upd-NONE 'well-formed-act-upd 'fb-act-upd-NONE
       'well-formed-filter-world 'fb-filter-world-NONE 'well-formed-act-ins-fresh 'fb-act-ins-NONE)
(doseq [o '[well-formed-scope-upd well-formed-pub-upd well-formed-source-upd well-formed-resource-upd well-formed-cleanup-upd well-formed-cleanup-del well-formed-set-pins
            well-formed-resource-del well-formed-scope-del well-formed-cleanup-ins well-formed-set-released well-formed-set-pending-act well-formed-fork-del]]
  (prim! FB o nil))
(prim! FB 'well-formed-run-del '(members-round-frame-move zl zf zd zs w (run-del w x) (members-round-frame-fm-run-del w x) (members-round-frame-er zl zf zd zs w R) R))
(prim! FB 'well-formed-comp-del-unref '(members-round-frame-move zl zf zd zs w (comp-del w x) (members-round-frame-fm-comp-del w x) (members-round-frame-er zl zf zd zs w R) R))
(prim! FB 'well-formed-drop-act '(members-round-frame-move zl zf zd zs w (drop-act w a) (fm-drop-act w a) (ep-filter (members-round-frame-e zs zf) (cred-ne a) (:edges w) (members-round-frame-er zl zf zd zs w R)) R))
(prim! FB 'well-formed-drop-edges '(members-round-frame-move zl zf zd zs w (drop-edges w p) (fm-drop-edges w p) (ep-filter (members-round-frame-e zs zf) p (:edges w) (members-round-frame-er zl zf zd zs w R)) R))
(prim! FB 'well-formed-remove-edge '(members-round-frame-move zl zf zd zs w (remove-edge w x) (fm-remove-edge w x) (ep-remove-edge (members-round-frame-e zs zf) w x (members-round-frame-er zl zf zd zs w R)) R))
(prim! FB 'well-formed-unmark-edge
       '(members-round-frame-move zl zf zd zs w (unmark-edge w x) (current-members-fm-unmark w x)
          (ep-unmark-edge (members-round-frame-e zs zf) (fn [e :- EdgeRow, q :- (= (members-round-frame-e zs zf e) true)] q) w x (members-round-frame-er zl zf zd zs w R)) R))
;; members-round-frame on the generic tree: a computation edit keeps members-round-frame when the epoch does not go down (by lemma where
;; the row function changes it), a run edit keeps the run keys, a fill moves the member (fm-act-fill)
(defn- fb-lapp [F lem] (if (seq? F) (apply list lem (rest F)) lem))
(tree/part! FB
  :sites (merge
          (tree/row-sites 'well-formed-comp-upd (constantly true)
                          (fn [F] (list 'members-round-frame-comp-upd-m 'zl 'zf 'zd 'zs 'w 'x F 'hid 'hp
                                        (if (contains? '#{comp-inc-epoch comp-demand-row comp-replace-row comp-start-row} (if (seq? F) (first F) F))
                                          (fb-lapp F (symbol (str (if (seq? F) (first F) F) "-h3ep")))
                                          '(fn [c :- CompRow] (Nat.le_refl (:epoch c))))
                                        'h0)))
          (tree/row-sites 'well-formed-run-upd (constantly true)
                          (fn [F] (list 'members-round-frame-run-upd-m 'zl 'zf 'zd 'zs 'w 'x F 'hf '(fn [q :- RunRow] (Eq.refl (current-members-run-key q))) 'h0)))
          (tree/row-sites 'well-formed-act-upd '#{act-fill}
                          (fn [F] (list 'members-round-frame-act-upd-m 'zl 'zf 'zd 'zs 'w 'x F 'hf (apply list 'fm-act-fill 'w 'x (map (constantly '_) (rest F))) 'h0)))))
(tree/restate! FB '[well-formed-demote])

;; ===========================================================================
;; demote of a stray x (x is in the list)
;; ===========================================================================
(a/theorem current-members-single [d :- Nat, x :- Nat, L :- (List Nat)]
  (=> (= (reach-mem d (List.cons Nat x (List.nil Nat))) true) (= (reach-mem x L) true) (= (reach-mem d L) true))
  (intros hd hx)
  (simp only [reach-mem-cons reach-mem Bool.or_false] at hd)
  (rw [(Nat.eq_of_beq_eq_true hd)]) (exact hx))
(a/theorem current-members-list-in [L :- (List Nat), w :- World, x :- Nat]
  (=> (= (reach-mem x L) true) (= (current-members (List.cons Nat x L) w) true) (= (current-members L w) true))
  (intros hx h)
  (have hs := (current-members-well-formed _ w h))
  (have hr (= (current-members-rest (List.append Nat (List.cons Nat x (List.nil Nat)) L) w) true)) (exact (current-members-rest-of _ w h))
  (apply (current-members-intro L w hs))
  (apply (current-members-dis L w (List.cons Nat x (List.nil Nat)) hs))
  (intros d hd) (apply Or.inl) (exact (current-members-single d x L hd hx))
  (exact hr))
(a/theorem current-members-comp-upd-in [L :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                            hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                            hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                            hep :- (forall [c :- CompRow] (<= (:epoch c) (:epoch (f c))))]
  (=> (= (reach-mem x L) true) (= (current-members L w) true) (= (current-members L (comp-upd w x f)) true))
  (intros hx h) (exact (current-members-list-in L _ x hx (current-members-comp-upd-x L w x f hid hp hep h))))
;; a dep edge of an exempt creditor is free; a non-dep edge whose creditor is a computation is free
(a/theorem current-members-free-cred-in [L :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (current-members-rest L w) true) (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) true) (= (reach-mem (:creditor e) L) true)
      (= (current-members-free L w (:id e)) true))
  (intros hr me kd hc)
  (apply (current-members-free-by L w (:id e)))
  (intros b r mb mr ir hxo hcur hmem hxx)
  (have u := (current-members-ob-use L w b r (:id e) e hr mb mr ir hxo hcur hmem hxx me (Eq.refl (:id e))))
  (have sk := (And.left u))
  (simp only [current-members-s Bool.and_eq_true] at sk)
  (have c2 := (And.left (And.right sk)))
  (simp only [kd Bool.not_true Bool.false_or current-members-run-key] at c2)
  (rw [(Nat.eq_of_beq_eq_true c2)] at hc) (rw [hxo] at hc) (cases hc))
(a/theorem current-members-free-wait-comp [L :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (well-formed w) true) (= (current-members-rest L w) true) (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) false)
      (= (tbl-has comp-id (:creditor e) (:comps w)) true) (= (current-members-free L w (:id e)) true))
  (intros hs hr me kd hc)
  (apply (current-members-free-by L w (:id e)))
  (intros b r mb mr ir hxo hcur hmem hxx)
  (have u := (current-members-ob-use L w b r (:id e) e hr mb mr ir hxo hcur hmem hxx me (Eq.refl (:id e))))
  (have sk := (And.left u))
  (simp only [current-members-s Bool.and_eq_true] at sk)
  (have c3 := (And.left (And.right (And.right sk))))
  (simp only [kd Bool.false_or] at c3)
  (have z := (act-not-comp w (:id b) hs (has-of-mem ActRow act-id b (:acts w) mb)))
  (rw [(Nat.eq_of_beq_eq_true c3)] at hc) (rw [z] at hc) (cases hc))

(a/theorem current-members-free-nil [L :- (List Nat), w :- World, x :- Nat] (=> (= (current-members-free (List.nil Nat) w x) true) (= (current-members-free L w x) true))
  (intro h)
  (apply (current-members-free-mono (List.nil Nat) L w x))
  (intros d hd) (simp only [reach-mem] at hd) (cases hd)
  (exact h))
(a/theorem current-members-fr-dep [L :- (List Nat), w :- World, x :- Nat]
  (=> (= (current-members-rest L w) true) (= (reach-mem x L) true)
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (not-dep-of x e) false) (= (current-members-free L w (:id e)) true))))
  (intros hr hx e me hn)
  (simp only [not-dep-of dep-of] at hn)
  (have hn2 := (bnot-false _ hn))
  (simp only [Bool.and_eq_true] at hn2)
  (have hc (= (reach-mem (:creditor e) L) true)) (rw [(Nat.eq_of_beq_eq_true (And.right hn2))]) (exact hx)
  (exact (current-members-free-cred-in L w e hr me (And.left hn2) hc)))
(a/theorem current-members-fr-avoid [S :- (List Nat), R :- (List Nat), F :- (List Nat), D :- (List Nat), W :- World, x :- Nat]
  (=> (= (reach-mem x S) true) (= (tbl-all (rm-in S) R) true) (= (i14-validity-rule-r S R W) true) (= (current-members (List.append Nat S (List.nil Nat)) W) true)
      (= (members-round-frame (List.nil Nat) F D S W) true) (= (tbl-has comp-id x (:comps W)) true)
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges W)) (= (edge-avoids x e) false) (= (current-members-free (List.append Nat S (List.nil Nat)) W (:id e)) true))))
  (intros hx hR hv h hfb hcx e me ha)
  (have hs := (current-members-well-formed _ W h))
  (have hr := (current-members-rest-of _ W h))
  (have p := (i14-validity-rule-r-keys-ok-parts _ _ _ _ _ (i14-validity-rule-r-rest-of _ _ W hv)))
  (cases kd (Nat.beq (:kind e) ek-dep))
  (case [true]
    (have hc (= (reach-mem (:creditor e) (List.append Nat S (List.nil Nat))) true))
    (cases hcx2 (Nat.beq (:creditor e) x))
    (case [true] (rw [(Nat.eq_of_beq_eq_true hcx2)]) (exact (rm-app-l x S (List.nil Nat) hx)))
    (case [false]
      (simp only [edge-avoids hcx2 Bool.not_false Bool.true_and] at ha)
      (have hd := (bnot-false _ ha))
      (have dS (= (reach-mem (:debtor e) S) true)) (rw [(Nat.eq_of_beq_eq_true hd)]) (exact hx)
      (have db := (tbl-all-mem EdgeRow _ e (:edges W) (And.left (And.right p)) me))
      (simp only [dnb14 kd dS Bool.not_true Bool.false_or Bool.true_or Bool.true_and] at db)
      (have cS := (all-reach-mem (rm-in S) (:creditor e) R hR db))
      (simp only [rm-in] at cS)
      (exact (rm-app-l (:creditor e) S (List.nil Nat) cS)))
    (exact (current-members-free-cred-in (List.append Nat S (List.nil Nat)) W e hr me kd hc)))
  (case [false]
    (cases hd (Nat.beq (:debtor e) x))
    (case [true]
      (have dS (= (reach-mem (:debtor e) S) true)) (rw [(Nat.eq_of_beq_eq_true hd)]) (exact hx)
      (have fe := (tbl-all-mem EdgeRow _ e (:edges W) (members-round-frame-er (List.nil Nat) F D S W (members-round-frame-rest-of (List.nil Nat) F D S W hfb)) me))
      (simp only [members-round-frame-e kd dS Bool.not_true Bool.false_or] at fe)
      (exact (current-members-free-nil (List.append Nat S (List.nil Nat)) W (:id e) (all-reach-mem (current-members-free (List.nil Nat) W) (:id e) F (members-round-frame-fr (List.nil Nat) F D S W (members-round-frame-rest-of (List.nil Nat) F D S W hfb)) fe))))
    (case [false]
      (simp only [edge-avoids hd Bool.not_false Bool.and_true] at ha)
      (have hc := (bnot-false _ ha))
      (have hcc (= (tbl-has comp-id (:creditor e) (:comps W)) true)) (rw [(Nat.eq_of_beq_eq_true hc)]) (exact hcx)
      (exact (current-members-free-wait-comp (List.append Nat S (List.nil Nat)) W e hs hr me kd hcc)))))

;; C0: demote closes C's basis streams (end-basis); each is a source, not a computation
(a/theorem current-members-end-basis [xm :- (List Nat), hx :- (List Nat), w :- World, cid :- Nat]
  (=> (= (marks-waiting hx w) true) (= (current-members xm w) true) (= (current-members xm (end-basis w cid)) true))
  (intros hk h)
  (cases hf (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [end-basis hf]) (exact h)
  (have n0 (= (tbl-all (hk-noc (:comps w)) (basis-streams w c)) true))
  (simp only [basis-streams])
  (exact (tbl-all-mono Nat (source-kind-at w sk-stream) (hk-noc (:comps w))
           (fn [y :- Nat, hy :- (= (source-kind-at w sk-stream y) true)] (hk-noc-source w sk-stream y (current-members-well-formed xm w h) hy))
           _ (tbl-all-filter-self Nat _ _)))
  (simp only [end-basis hf])
  (exact (current-members-fold-noc2 xm hx close-source (current-members-close-source xm hx) (marks-waiting-close-source hx) hk-has-close-source (basis-streams w c) w n0 hk h)))

(a/theorem current-members-demote-x [S :- (List Nat), R :- (List Nat), gx :- (List Nat), gk :- (List Nat), F :- (List Nat), D :- (List Nat), W :- World, x :- Nat]
  (=> (= (reach-mem x S) true) (= (tbl-all (rm-in S) R) true) (= (i12-ranks W) true) (= (i14-validity-rule-r S (List.cons Nat x R) W) true)
      (= (marks-waiting (List.append Nat S (List.nil Nat)) W) true) (= (i10-current-exempt gx gk W) true) (= (edge-kinds W) true) (= (members-round-frame (List.nil Nat) F D S W) true)
      (= (current-members (List.append Nat S (List.nil Nat)) W) true) (= (current-members (List.append Nat S (List.nil Nat)) (demote W x)) true))
  (intros hx hR hk hv hm hg he hfb h)
  (have hX := (rm-app-l x S (List.nil Nat) hx))
  (cases hf (comp-find W x))
  (case [none] (simp only [demote hf]) (exact h))
  (case [some c]
    (cases hi (:idle c))
    (case [true] (simp only [demote hf hi]) (exact h))
    (case [false]
      (simp only [demote hf hi demote-edges])
      (have h1 := (current-members-run-cascade-g (List.append Nat S (List.nil Nat)) (List.append Nat S (List.nil Nat)) gx gk W (cancel-jobs (demote-cancels W c)) hg hm he h))
      (have m1 := (marks-waiting-run-cascade (List.append Nat S (List.nil Nat)) W (cancel-jobs (demote-cancels W c)) hm))
      (have v1 := (i14-validity-rule-r-run-cascade S (List.cons Nat x R) W (cancel-jobs (demote-cancels W c)) hv))
      (have f1 := (members-round-frame-run-cascade (List.nil Nat) F D S W (cancel-jobs (demote-cancels W c)) hfb))
      (have h2 (= (current-members (List.append Nat S (List.nil Nat)) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c))) true))
      (cases hb (demote-cur W c))
      (case [false] (simp only [demote-epoch]) (exact h1))
      (case [true] (simp only [demote-epoch])
        (exact (current-members-comp-upd-in (List.append Nat S (List.nil Nat)) (run-cascade W (cancel-jobs (demote-cancels W c))) x comp-inc-epoch (fn [q :- CompRow] (Eq.refl (comp-id q))) (fn [q :- CompRow] (Eq.refl (:pending q)))
                 comp-inc-epoch-h3ep hX h1)))
      (have m2 := (marks-waiting-demote-epoch (List.append Nat S (List.nil Nat)) (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c) m1))
      (have v2 := (i14-validity-rule-r-demote-epoch S (List.cons Nat x R) (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c) v1))
      (have f2 := (members-round-frame-demote-epoch (List.nil Nat) F D S (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c) f1))
      (have dk (= (tbl-all (hk-dok (List.append Nat S (List.nil Nat)) (:comps (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c))) (not-dep-of x)) (:edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)))) true))
      (apply (all-of-mem EdgeRow _ (:edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c))))) (intros e me) (exact (hk-dok-own _ _ x e hX))
      (have h3x := (current-members-drop-edges (List.append Nat S (List.nil Nat)) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) dk (current-members-fr-dep (List.append Nat S (List.nil Nat)) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) x (current-members-rest-of _ _ h2) hX) h2))
      (have m3 := (marks-waiting-drop-edges (List.append Nat S (List.nil Nat)) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) dk m2))
      (have v3 := (i14-validity-rule-r-drop-r S R (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x (ncd-drop (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) x) (i14-validity-rule-r-drop-edges S (List.cons Nat x R) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) v2)))
      (have f3 := (members-round-frame-drop-edges (List.nil Nat) F D S (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) f2))
      (have nc0 := (ncd-drop (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) x))
      (have wd := (wdom-end-basis (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x))
      (have nc := ((And.left (And.right wd)) (ncd14 x) (ecl-ncd14 x) nc0))
      (have h3y := (current-members-end-basis (List.append Nat S (List.nil Nat)) (List.append Nat S (List.nil Nat)) (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x m3 h3x))
      (have m3y := (marks-waiting-end-basis (List.append Nat S (List.nil Nat)) (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x m3))
      (have v3y := (i14-validity-rule-r-end-basis S R (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x v3))
      (have f3y := (members-round-frame-end-basis (List.nil Nat) F D S (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x f3))
      (cases hf3 (comp-find (end-basis (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x) x))
      (case [none] (simp only [demote-finish hf3]) (exact h3y))
      (case [some c3]
        (cases hkp (demote-keep (end-basis (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x) c3))
        (case [true]
          (simp only [demote-finish hf3 hkp])
          (exact (current-members-comp-upd-in (List.append Nat S (List.nil Nat)) (end-basis (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x) x (comp-demote-row (validity-of (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) x)) (comp-demote-row-id _) (comp-demote-row-pending _) (fn [q :- CompRow] (Nat.le_refl (:epoch q))) hX h3y)))
        (case [false]
          (simp only [demote-finish hf3 hkp])
          (have hcx := (tbl-find-has CompRow comp-id x c3 (:comps (end-basis (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x)) hf3))
          (have h4 := (current-members-drop-edges (List.append Nat S (List.nil Nat)) (end-basis (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x) (edge-avoids x) (hk-dok-avoid S R (List.nil Nat) (end-basis (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x) x hx hR v3y nc m3y)
                        (current-members-fr-avoid S R F D (end-basis (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x) x hx hR v3y h3y f3y hcx) h3y))
          (have s4 := (current-members-well-formed _ _ h4))
          (exact (current-members-intro (List.append Nat S (List.nil Nat)) _ (well-formed-comp-del-unref (drop-edges (end-basis (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x) (edge-avoids x)) x (drop-edges-avoids (end-basis (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x) x) s4)
                   (current-members-rest-comp-del (List.append Nat S (List.nil Nat)) (drop-edges (end-basis (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x) (edge-avoids x)) x (current-members-db-of (drop-edges (end-basis (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x) (edge-avoids x)) s4) (current-members-rest-of _ _ h4)))))))))

;; ---- after its demote, no activation holds a current run of x
(a/theorem current-members-nh-dead [w :- World, d :- Nat]
  (=> (= (acts-alive w) true) (= (tbl-all (not-alive-of d) (:runs w)) true) (current-members-nh w d))
  (intros haa hn)
  (apply current-members-nh-mk)
  (intros a r ma mr ir ho hc)
  (simp only [acts-alive] at haa)
  (have al0 := (tbl-all-mem RunRow _ r (:runs w) (tbl-all-mem ActRow _ a (:acts w) haa ma) mr))
  (have ib (= (Nat.beq (:id r) (:run a)) true)) (rw [ir]) (exact (Nat.beq_refl _))
  (simp only [run-ok-for ib Bool.not_true Bool.false_or] at al0)
  (have na := (tbl-all-mem RunRow _ r (:runs w) hn mr))
  (have ob (= (Nat.beq (:of r) d) true)) (rw [ho]) (exact (Nat.beq_refl _))
  (simp only [not-alive-of al0 ob Bool.not_true Bool.or_self] at na)
  (cases na))
(a/theorem current-members-runs-then-rule-r [w :- World, x :- Nat, vs :- (List Valid)] (= (:runs (demote-finish w x vs)) (:runs w))
  (cases hf (comp-find w x))
  (case [none] (simp only [demote-finish hf]))
  (case [some c]
    (cases hk (demote-keep w c))
    (case [true] (simp only [demote-finish hf hk comp-upd set-comps]))
    (case [false] (simp only [demote-finish hf hk comp-del set-comps drop-edges set-edges]))))
(a/theorem current-members-round-bound-aa [a :- Nat, k :- Nat, w :- World] (=> (= (round-bound a k w) true) (And (= (well-formed w) true) (= (acts-alive w) true)))
  (intro h) (simp only [round-bound Bool.and_eq_true] at h) (exact (And.intro (And.left h) (And.left (And.right h)))))
(a/theorem current-members-nh-demote [a :- Nat, k :- Nat, W :- World, x :- Nat]
  (=> (= (round-bound a k W) true) (= (i7-idle W) true) (current-members-nh (demote W x) x))
  (intros hb h7)
  (have hs := (And.left (current-members-round-bound-aa a k W hb)))
  (have haa := (And.right (current-members-round-bound-aa a k W hb)))
  (have aa2 := (And.right (current-members-round-bound-aa a k (demote W x) (round-bound-demote a k W x hb))))
  (cases hf (comp-find W x))
  (case [none]
    (simp only [demote hf])
    (apply current-members-nh-mk)
    (intros b r mb mr ir ho hc)
    (apply (any-elim CompRow (current-members-cur (current-members-run-key r)) _ (:comps W) hc))
    (intros c2 mc2 hq)
    (simp only [current-members-cur current-members-run-key Bool.and_eq_true] at hq)
    (have z := (has-of-mem CompRow comp-id c2 (:comps W) mc2))
    (have ic (= (comp-id c2) x)) (exact (Eq.trans (Nat.eq_of_beq_eq_true (And.left hq)) ho))
    (rw [ic (tbl-find-none-has CompRow comp-id x (:comps W) hf)] at z) (cases z))
  (case [some c]
    (have mc := (tbl-find-mem CompRow comp-id x c (:comps W) hf))
    (have ic (= (:id c) x)) (exact (tbl-find-id CompRow comp-id x c (:comps W) hf))
    (cases hi (:idle c))
    (case [true]
      (simp only [demote hf hi])
      (apply current-members-nh-mk)
      (intros b r mb mr ir ho hc)
      (simp only [acts-alive] at haa)
      (have al0 := (tbl-all-mem RunRow _ r (:runs W) (tbl-all-mem ActRow _ b (:acts W) haa mb) mr))
      (have ib (= (Nat.beq (:id r) (:run b)) true)) (rw [ir]) (exact (Nat.beq_refl _))
      (simp only [run-ok-for ib Bool.not_true Bool.false_or] at al0)
      (have p := (i7-idle-keys-ok-parts _ _ _ (i7-idle-rest-of W h7)))
      (have aw := (tbl-all-mem RunRow _ r (:runs W) (And.left p) mr))
      (simp only [a7-one al0 Bool.not_true Bool.false_or awake] at aw)
      (have q := (tbl-all-mem CompRow _ c (:comps W) aw mc))
      (have ob (= (Nat.beq (:id c) (:of r)) true)) (rw [ic ho]) (exact (Nat.beq_refl _))
      (simp only [not-idle-if-id ob hi Bool.not_true Bool.or_self] at q)
      (cases q))
    (case [false]
      (simp only [demote hf hi demote-edges] at aa2)
      (simp only [demote hf hi demote-edges])
      (apply (current-members-nh-dead _ x aa2))
      (rw [(current-members-runs-then-rule-r (end-basis (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x) x (validity-of (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) x))])
      (apply (end-basis-dead (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x x (well-formed-drop-edges _ (not-dep-of x) (well-formed-demote-epoch _ x (demote-cur W c) (well-formed-run-cascade W _ hs)))))
      (show (= (tbl-all (not-alive-of x) (:runs (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)))) true))
      (rw [(runs-demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c))])
      (have nd := (demote-dead W c hs haa))
      (rw [ic] at nd) (exact nd))))

;; ---- the fold over the strays: the demoted ones are collected in the bundle's zd
(a/defn current-members-acc [R :- (List Nat), D :- (List Nat)] (List Nat) (match R nil D (cons x t) (current-members-acc t (List.cons Nat x D))))
(a/theorem current-members-acc-d [d :- Nat, R :- (List Nat)]
  (forall [D :- (List Nat)] (=> (= (reach-mem d D) true) (= (reach-mem d (current-members-acc R D)) true)))
  (induction R)
  (case [nil] (intros D h) (simp only [current-members-acc]) (exact h))
  (case [cons x t ih] (intros D h) (simp only [current-members-acc]) (apply ih) (simp only [reach-mem-cons h Bool.or_true])))
(a/theorem current-members-acc-r [d :- Nat, R :- (List Nat)]
  (forall [D :- (List Nat)] (=> (= (reach-mem d R) true) (= (reach-mem d (current-members-acc R D)) true)))
  (induction R)
  (case [nil] (intros D h) (simp only [reach-mem] at h) (cases h))
  (case [cons x t ih]
    (intros D h)
    (simp only [reach-mem-cons Bool.or_eq_true] at h)
    (simp only [current-members-acc])
    (cases h)
    (case [inl h1] (apply (current-members-acc-d d t)) (simp only [reach-mem-cons h1 Bool.true_or]))
    (case [inr h1] (exact (ih (List.cons Nat x D) h1)))))
(a/theorem members-round-frame-add-d [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, x :- Nat]
  (=> (current-members-nh w x) (= (members-round-frame zl zf zd zs w) true) (= (members-round-frame zl zf (List.cons Nat x zd) zs w) true))
  (intros hn h)
  (have r := (members-round-frame-rest-of zl zf zd zs w h))
  (have n2 (= (tbl-all (members-round-frame-nh w) (List.cons Nat x zd)) true))
  (simp only [tbl-all (members-round-frame-nh-mk w x hn) (members-round-frame-nhs zl zf zd zs w r) Bool.and_self])
  (exact (members-round-frame-intro zl zf (List.cons Nat x zd) zs w (members-round-frame-well-formed zl zf zd zs w h)
           (members-round-frame-rest-mk zl zf (List.cons Nat x zd) zs w (members-round-frame-fr zl zf zd zs w r) n2 (members-round-frame-er zl zf zd zs w r)))))
(a/theorem current-members-demote-fold [S :- (List Nat), gk :- (List Nat), F :- (List Nat), a :- Nat, k :- Nat, R :- (List Nat)]
  (forall [gx :- (List Nat), D :- (List Nat), W :- World]
    (=> (= (tbl-all (rm-in S) R) true) (= (i12-ranks W) true) (= (i14-validity-rule-r S R W) true) (= (marks-waiting (List.append Nat S (List.nil Nat)) W) true)
        (= (i10-current-exempt (List.append Nat R gx) gk W) true) (= (edge-kinds W) true) (= (round-bound a k W) true) (= (i7-idle W) true)
        (= (members-round-frame (List.nil Nat) F D S W) true) (= (current-members (List.append Nat S (List.nil Nat)) W) true)
        (And (= (current-members (List.append Nat S (List.nil Nat)) (nat-fold demote W R)) true) (= (members-round-frame (List.nil Nat) F (current-members-acc R D) S (nat-fold demote W R)) true))))
  (induction R)
  (case [nil] (intros gx D W hR hk hv hm hg he hb h7 hfb h) (simp only [nat-fold current-members-acc]) (exact (And.intro h hfb)))
  (case [cons x t ih]
    (intros gx D W hR hk hv hm hg he hb h7 hfb h)
    (simp only [tbl-all Bool.and_eq_true] at hR)
    (have hx (= (reach-mem x S) true)) (exact (And.left hR))
    (have hg1 (= (i10-current-exempt (List.cons Nat x (List.append Nat t gx)) gk W) true)) (exact hg)
    (simp only [nat-fold current-members-acc])
    (exact (ih gx (List.cons Nat x D) (demote W x) (And.right hR) (i12-ranks-demote W x hk) (i14-validity-rule-r-demote S t W x hx hk hv)
             (marks-waiting-demote-x S t (List.nil Nat) W x hx (And.right hR) hk hv hm)
             (i10-current-exempt-demote (List.append Nat t gx) gk W x hg1) (edge-kinds-demote W x he) (round-bound-demote a k W x hb)
             (i7-idle-demote W x (And.right (current-members-round-bound-aa a k W hb)) h7)
             (members-round-frame-add-d (List.nil Nat) F D S (demote W x) x (current-members-nh-demote a k W x hb h7) (members-round-frame-demote (List.nil Nat) F D S W x hfb))
             (current-members-demote-x S t (List.cons Nat x (List.append Nat t gx)) gk F D W x hx (And.right hR) hk hv hm hg1 he hfb h)))))

;; ===========================================================================
;; The pass: start (the bundle at the round's world), end (the strays' exemption is undone), normalize-round
;; ===========================================================================
(a/defn members-round-frame-pick [S :- (List Nat), e :- EdgeRow] Bool (Bool.and (Bool.not (Nat.beq (:kind e) ek-dep)) (reach-mem (:debtor e) S)))
(a/theorem current-members-xm-app [w :- World, S :- (List Nat)] (=> (= (current-members (List.nil Nat) w) true) (= (current-members (List.append Nat S (List.nil Nat)) w) true))
  (induction S)
  (case [nil] (intro h) (exact h))
  (case [cons x t ih] (intro h) (exact (current-members-xm-cons (List.append Nat t (List.nil Nat)) x w (ih h)))))
;; at a world with current-members []: a computation id is free, and so is a non-dep edge on a computation
;; (a current member edge on a computation is a dep edge: current-members-m)
(a/theorem current-members-members-round-frame-init [S :- (List Nat), w :- World]
  (=> (forall [d :- Nat] (=> (= (reach-mem d S) true) (= (tbl-has comp-id d (:comps w)) true)))
      (= (current-members (List.nil Nat) w) true) (= (members-round-frame (List.nil Nat) (List.append Nat S (tbl-scan edge-id (members-round-frame-pick S) (:edges w))) (List.nil Nat) S w) true))
  (intros hS h)
  (have hs := (current-members-well-formed _ w h))
  (have hr := (current-members-rest-of _ w h))
  (have hp (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (members-round-frame-pick S e) true) (= (current-members-free (List.nil Nat) w (edge-id e)) true))))
  (intros e me hp)
  (simp only [members-round-frame-pick Bool.and_eq_true] at hp)
  (have kd := (bnot-true _ (And.left hp)))
  (show (= (current-members-free (List.nil Nat) w (:id e)) true))
  (apply (current-members-free-by (List.nil Nat) w (:id e)))
  (intros b r mb mr ir hxo hcur hmem hxx)
  (have u := (current-members-ob-use (List.nil Nat) w b r (:id e) e hr mb mr ir hxo hcur hmem hxx me (Eq.refl (:id e))))
  (have ur := (And.right u))
  (cases ur)
  (case [inl z] (simp only [reach-mem] at z) (cases z))
  (case [inr z]
    (simp only [current-members-m Bool.and_eq_true] at z)
    (have z2 := (And.right z))
    (simp only [(hS (:debtor e) (And.right hp)) kd Bool.not_true Bool.false_or Bool.false_and] at z2)
    (cases z2))
  (have fr (= (tbl-all (current-members-free (List.nil Nat) w) (List.append Nat S (tbl-scan edge-id (members-round-frame-pick S) (:edges w)))) true))
  (apply (all-of-mem Nat _ (List.append Nat S (tbl-scan edge-id (members-round-frame-pick S) (:edges w)))))
  (intros y my)
  (have ry := (Iff.mpr (reach-mem-iff y (List.append Nat S (tbl-scan edge-id (members-round-frame-pick S) (:edges w)))) my))
  (simp only [reach-mem-append Bool.or_eq_true] at ry)
  (cases ry)
  (case [inl y1]
    (apply (current-members-free-noedge (List.nil Nat) w y hr))
    (cases q (tbl-has edge-id y (:edges w)))
    (case [false] (rfl))
    (case [true] (have z := (current-members-edge-not-comp w y hs q)) (rw [(hS y y1)] at z) (cases z)))
  (case [inr y2]
    (exact (scan-prop EdgeRow edge-id (members-round-frame-pick S) (fn [v :- Nat] (= (current-members-free (List.nil Nat) w v) true)) (:edges w) hp y y2)))
  (have ep (= (tbl-all (members-round-frame-e S (List.append Nat S (tbl-scan edge-id (members-round-frame-pick S) (:edges w)))) (:edges w)) true))
  (apply (all-of-mem EdgeRow _ (:edges w)))
  (intros e me)
  (cases kd (Nat.beq (:kind e) ek-dep))
  (case [true] (simp only [members-round-frame-e kd Bool.true_or]))
  (case [false]
    (cases dS (reach-mem (:debtor e) S))
    (case [false] (simp only [members-round-frame-e dS Bool.not_false Bool.true_or Bool.or_true]))
    (case [true]
      (have pk (= (members-round-frame-pick S e) true)) (simp only [members-round-frame-pick kd dS Bool.not_false Bool.and_self])
      (have im := (scan-mem EdgeRow edge-id (members-round-frame-pick S) e (:edges w) me pk))
      (have im2 (= (reach-mem (:id e) (tbl-scan edge-id (members-round-frame-pick S) (:edges w))) true)) (exact im)
      (simp only [members-round-frame-e reach-mem-append im2 Bool.or_true])))
  (have nh (= (tbl-all (members-round-frame-nh w) (List.nil Nat)) true)) (simp only [tbl-all])
  (exact (members-round-frame-intro (List.nil Nat) (List.append Nat S (tbl-scan edge-id (members-round-frame-pick S) (:edges w))) (List.nil Nat) S w hs (members-round-frame-rest-mk (List.nil Nat) (List.append Nat S (tbl-scan edge-id (members-round-frame-pick S) (:edges w))) (List.nil Nat) S w fr nh ep))))
;; the pass end: every stray has no current holder, its id is free, and the edges on it are no dep edges
;; (i14-validity-rule-r: a dep edge on a stray has a stray creditor not yet demoted) with free ids
(a/theorem current-members-pass-end [S :- (List Nat), F :- (List Nat), D :- (List Nat), W :- World]
  (=> (= (i14-validity-rule-r S (List.nil Nat) W) true) (= (members-round-frame (List.nil Nat) F D S W) true)
      (forall [d :- Nat] (=> (= (reach-mem d S) true) (= (reach-mem d D) true)))
      (forall [d :- Nat] (=> (= (reach-mem d S) true) (= (reach-mem d F) true)))
      (= (current-members (List.append Nat S (List.nil Nat)) W) true) (= (current-members (List.nil Nat) W) true))
  (intros hv hfb hD hF h)
  (have hs := (current-members-well-formed _ W h))
  (have r := (members-round-frame-rest-of (List.nil Nat) F D S W hfb))
  (have p := (i14-validity-rule-r-keys-ok-parts _ _ _ _ _ (i14-validity-rule-r-rest-of _ _ W hv)))
  (apply (current-members-intro (List.nil Nat) W hs))
  (apply (current-members-dis (List.nil Nat) W S hs))
  (intros d hd)
  (apply Or.inr)
  (apply And.intro)
  (exact (members-round-frame-nh-of W d (all-reach-mem (members-round-frame-nh W) d D (members-round-frame-nhs (List.nil Nat) F D S W r) (hD d hd))))
  (apply And.intro)
  (exact (all-reach-mem (current-members-free (List.nil Nat) W) d F (members-round-frame-fr (List.nil Nat) F D S W r) (hF d hd)))
  (intros e me ed)
  (have dS (= (reach-mem (:debtor e) S) true)) (rw [ed]) (exact hd)
  (cases kd (Nat.beq (:kind e) ek-dep))
  (case [true]
    (have db := (tbl-all-mem EdgeRow _ e (:edges W) (And.left (And.right p)) me))
    (simp only [dnb14 kd dS reach-mem Bool.not_true Bool.false_or Bool.true_or Bool.true_and] at db)
    (cases db))
  (case [false]
    (have fe := (tbl-all-mem EdgeRow _ e (:edges W) (members-round-frame-er (List.nil Nat) F D S W r) me))
    (simp only [members-round-frame-e kd dS Bool.not_true Bool.false_or] at fe)
    (apply Or.inr)
    (exact (all-reach-mem (current-members-free (List.nil Nat) W) (:id e) F (members-round-frame-fr (List.nil Nat) F D S W r) fe)))
  (exact (current-members-rest-of _ W h)))

(a/theorem current-members-normalize-round [w :- World]
  (=> (= (trc w) true) (= (i12-ranks w) true) (= (i14-validity-rule-r (List.nil Nat) (List.nil Nat) w) true) (= (marks-waiting (List.nil Nat) w) true) (= (i10-current-exempt (List.nil Nat) (List.nil Nat) w) true) (= (edge-kinds w) true)
      (= (acts-alive w) true) (= (i7-idle w) true) (= (current-members (List.nil Nat) w) true) (= (current-members (List.nil Nat) (normalize-round w)) true))
  (intros htc hk hv hm hg he haa h7 h)
  (have hs := (current-members-well-formed _ w h))
  (have hS (forall [d :- Nat] (=> (= (reach-mem d (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) true) (= (tbl-has comp-id d (:comps w)) true))))
  (intros d hd)
  (exact (scan-prop CompRow comp-id (comp-stray (live-list w)) (fn [v :- Nat] (= (tbl-has comp-id v (:comps w)) true)) (:comps w)
           (fn [c :- CompRow, m :- (List.Mem c (:comps w)), q :- (= (comp-stray (live-list w) c) true)] (has-of-mem CompRow comp-id c (:comps w) m)) d hd))
  (have f0 := (current-members-members-round-frame-init (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) w hS h))
  (have hL := (current-members-xm-app w (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) h))
  (have g1 := (i10-current-exempt-gx-app (List.nil Nat) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) w hg))
  (have hj (= (tbl-all (job-ok (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (List.nil Nat) w) (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) true))
  (rw [jl-cancel-jobs])
  (exact (scan-all RunRow run-id (run-stray (live-list w)) (fn [x :- Nat] (ncw (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (List.nil Nat) x w))
           (:runs w) (fn [r :- RunRow, m :- (List.Mem r (:runs w)), q :- (= (run-stray (live-list w) r) true)] (stray-ncw (List.nil Nat) (List.nil Nat) w r (trc-ta w htc) hg m q))))
  (have g2 := (i10-current-exempt-run-cascade (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (List.nil Nat) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) hj g1))
  (have mL := (marks-waiting-intro (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) w (marks-waiting-well-formed (List.nil Nat) w hm)
                (marks-waiting-rest-xm (List.nil Nat) (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) w (fn [d :- Nat, hd :- (= (reach-mem d (List.nil Nat)) true)] (rm-app-r d (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) hd)) (marks-waiting-rest-of (List.nil Nat) w hm))))
  (have h1 := (current-members-run-cascade-g (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (List.nil Nat) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) g1 mL he hL))
  (have m1 := (marks-waiting-run-cascade (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) mL))
  (have v1 := (i14-validity-rule-r-run-cascade (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) (i14-validity-rule-r-pass-start w htc hv)))
  (have k1 := (i12-ranks-run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) hk))
  (have e1 := (edge-kinds-run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) he))
  (have b1 := (round-bound-run-cascade (alive-cnt w) (act-cnt w) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) (round-bound-intro (alive-cnt w) (act-cnt w) w hs haa (Nat.le_refl _) (Nat.le_refl _))))
  (have g71 := (i7-idle-run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) h7))
  (have f1 := (members-round-frame-run-cascade (List.nil Nat) (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan edge-id (members-round-frame-pick (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) (:edges w))) (List.nil Nat) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) f0))
  (have rm := (rm-in-scan CompRow comp-id (comp-stray (live-list w)) (:comps w)))
  (have fold := (current-members-demote-fold (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan edge-id (members-round-frame-pick (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) (:edges w))) (alive-cnt w) (act-cnt w) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) (List.nil Nat) (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) rm k1 v1 m1 g2 e1 b1 g71 f1 h1))
  (have vf := (i14-validity-rule-r-fold (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) rm k1 v1))
  (have mf := (marks-waiting-demote-fold (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) rm k1 v1 m1))
  (have m0 (= (marks-waiting (List.nil Nat) (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)))) true))
  (apply (marks-waiting-dis (List.nil Nat) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) mf))
  (intros d hd) (exact (Or.inr (Or.inr (hk-nmd-pass (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) d (And.left vf) mf hd))))
  (intros d hd) (exact hd)
  (have hend := (current-members-pass-end (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan edge-id (members-round-frame-pick (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) (:edges w))) (current-members-acc (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) (And.left vf) (And.right fold)
                  (fn [d :- Nat, hd :- (= (reach-mem d (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) true)] (current-members-acc-r d (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) hd))
                  (fn [d :- Nat, hd :- (= (reach-mem d (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) true)] (rm-app-l d (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan edge-id (members-round-frame-pick (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) (:edges w)) hd))
                  (And.left fold)))
  (simp only [normalize-round normalize-round-with-live])
  (exact (current-members-detach (List.nil Nat) (List.nil Nat) (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) m0 hend)))

(a/theorem current-members-normalize-loop [fuel :- (List Nat)]
  (forall [w :- World]
    (=> (= (trc w) true) (= (i12-ranks w) true) (= (i14-validity-rule-r (List.nil Nat) (List.nil Nat) w) true) (= (marks-waiting (List.nil Nat) w) true) (= (i10-current-exempt (List.nil Nat) (List.nil Nat) w) true) (= (edge-kinds w) true)
      (= (acts-alive w) true) (= (i7-idle w) true) (= (current-members (List.nil Nat) w) true) (= (current-members (List.nil Nat) (normalize-loop fuel w)) true)))
  (induction fuel)
  (case [nil] (intros w htc hk hv hm hg he haa h7 h) (simp only [normalize-loop]) (exact h))
  (case [cons u f ih]
    (intros w htc hk hv hm hg he haa h7 h)
    (cases hn (normalized w))
    (case [true] (simp only [normalize-loop hn]) (exact h))
    (case [false]
      (simp only [normalize-loop hn])
      (exact (ih (normalize-round w) (trc-normalize-round w htc) (i12-ranks-normalize-round w hk) (i14-validity-rule-r-normalize-round w htc hk hv) (marks-waiting-normalize-round (List.nil Nat) w htc hk hv hm) (i10-current-exempt-normalize-round (List.nil Nat) (List.nil Nat) w (trc-ta w htc) hg)
               (edge-kinds-normalize-round w he) (And.right (round-bound-round w (current-members-well-formed _ w h) haa)) (i7-idle-normalize-round w haa h7)
               (current-members-normalize-round w htc hk hv hm hg he haa h7 h))))))
(a/theorem current-members-normalize [w :- World]
  (=> (= (trc w) true) (= (i12-ranks w) true) (= (i14-validity-rule-r (List.nil Nat) (List.nil Nat) w) true) (= (marks-waiting (List.nil Nat) w) true) (= (i10-current-exempt (List.nil Nat) (List.nil Nat) w) true) (= (edge-kinds w) true)
      (= (acts-alive w) true) (= (i7-idle w) true) (= (current-members (List.nil Nat) w) true) (= (current-members (List.nil Nat) (normalize w)) true))
  (intros htc hk hv hm hg he haa h7 h)
  (have p := (round-bound-parts _ _ _ (round-bound-detach (alive-cnt w) (act-cnt w) w (round-bound-intro _ _ w (current-members-well-formed _ w h) haa (Nat.le_refl _) (Nat.le_refl _)))))
  (simp only [normalize])
  (exact (current-members-normalize-loop (normalize-fuel (detach w)) (detach w) (trc-detach w htc) (i12-ranks-detach w hk) (i14-validity-rule-r-detach (List.nil Nat) (List.nil Nat) w hv) (marks-waiting-detach (List.nil Nat) w hm)
           (i10-current-exempt-detach (List.nil Nat) (List.nil Nat) w hg) (edge-kinds-detach w he) (And.left (And.right p)) (i7-idle-detach w h7) (current-members-detach (List.nil Nat) (List.nil Nat) w hm h))))

;; ===========================================================================
;; The filter: at a normalized world every run is kept, and a held activation's member edges are live
;; ===========================================================================
(a/theorem current-members-awm-keep [K :- (=> Nat Bool), x :- Nat, i :- Nat, as :- (List ActRow)]
  (=> (= (K i) true) (= (opt-test (current-members-first i) (act-with-member x as)) true)
      (= (opt-test (current-members-first i) (act-with-member x (tbl-keep K act-id as))) true))
  (induction as)
  (case [nil] (intros hk h) (simp only [tbl-keep]) (exact h))
  (case [cons hd t ih]
    (intros hk h)
    (cases hm (mem-has x (:members hd)))
    (case [true]
      (simp only [act-with-member hm opt-test current-members-first] at h)
      (have kh (= (K (act-id hd)) true)) (show (= (K (:id hd)) true)) (rw [(Nat.eq_of_beq_eq_true h)]) (exact hk)
      (simp only [tbl-keep kh act-with-member hm opt-test current-members-first])
      (exact h))
    (case [false]
      (simp only [act-with-member hm] at h)
      (cases hkk (K (act-id hd)))
      (case [true] (simp only [tbl-keep hkk act-with-member hm]) (exact (ih hk h)))
      (case [false] (simp only [tbl-keep hkk]) (exact (ih hk h))))))
(a/theorem current-members-filter-k [xm :- (List Nat), w :- World, K :- (=> Nat Bool)]
  (=> (= (tbl-keep K run-id (:runs w)) (:runs w))
      (forall [a :- ActRow, r :- RunRow, x :- Nat]
        (=> (List.Mem a (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run a)) (= (reach-mem x (act-contrib a)) true) (= (K x) true)))
      (= (current-members-rest xm w) true) (= (current-members-rest xm (filter-world K w)) true))
  (intros hr hx h)
  (simp only [current-members-rest] at h)
  (have er (= (:runs (filter-world K w)) (:runs w))) (simp only [filter-world hr])
  (have nx (= (:next-id (filter-world K w)) (:next-id w))) (rfl)
  (have hp (forall [a :- ActRow] (=> (List.Mem a (:acts w)) (= (current-members-a xm w a) true) (= (K (act-id a)) true) (= (current-members-a xm (filter-world K w) a) true))))
  (intros a ma ha ka)
  (have ka2 (= (K (:id a)) true)) (exact ka)
  (simp only [current-members-a Bool.and_eq_true] at ha)
  (have hq (forall [r :- RunRow] (=> (List.Mem r (:runs w)) (= (current-members-rr xm w a r) true) (= (current-members-rr xm (filter-world K w) a r) true))))
  (intros r mr hrr)
  (cases ib (Nat.beq (:id r) (:run a)))
  (case [false]
    (have ib2 (= (Nat.beq (:id (current-members-run-key r)) (:run a)) false)) (exact ib)
    (simp only [current-members-rr current-members-r ib2 Bool.not_false Bool.true_or]))
  (case [true]
    (have ib2 (= (Nat.beq (:id (current-members-run-key r)) (:run a)) true)) (exact ib)
    (simp only [current-members-rr current-members-r ib2 Bool.not_true Bool.false_or Bool.and_eq_true] at hrr)
    (have e1 (= (tbl-all (current-members-e1 (current-members-run-key r)) (:comps (filter-world K w))) true))
    (exact (tbl-all-keep-same CompRow K comp-id (current-members-e1 (current-members-run-key r)) (:comps w) (And.left (And.right hrr))))
    (have ob (= (current-members-ob xm (filter-world K w) a (current-members-run-key r)) true))
    (cases ho (reach-mem (:of (current-members-run-key r)) xm))
    (case [true] (simp only [current-members-ob ho Bool.true_or]))
    (case [false]
      (cases hc (tbl-any (current-members-cur (current-members-run-key r)) (tbl-keep K comp-id (:comps w))))
      (case [false]
        (have hc2 (= (tbl-any (current-members-cur (current-members-run-key r)) (:comps (filter-world K w))) false)) (exact hc)
        (simp only [current-members-ob hc2 Bool.not_false Bool.true_or Bool.or_true]))
      (case [true]
        (have hc0 := (tbl-any-keep CompRow (current-members-cur (current-members-run-key r)) K comp-id (:comps w) hc))
        (have o := (And.right (And.right hrr)))
        (simp only [current-members-ob ho hc0 Bool.not_true Bool.false_or Bool.and_eq_true] at o)
        (have cs2 (= (tbl-all (current-members-cs (current-members-run-key r)) (:comps (filter-world K w))) true))
        (exact (tbl-all-keep-same CompRow K comp-id (current-members-cs (current-members-run-key r)) (:comps w) (And.left o)))
        (have xs (= (tbl-all (current-members-x xm (filter-world K w) a (current-members-run-key r)) (act-contrib a)) true))
        (apply (all-of-mem Nat _ (act-contrib a)))
        (intros x mx)
        (have rx := (Iff.mpr (reach-mem-iff x (act-contrib a)) mx))
        (have hx0 := (all-reach-mem (current-members-x xm w a (current-members-run-key r)) x (act-contrib a) (And.right o) rx))
        (cases hxm (reach-mem x xm))
        (case [true] (simp only [current-members-x hxm Bool.true_or]))
        (case [false]
          (simp only [current-members-x hxm Bool.false_or Bool.and_eq_true] at hx0)
          (have kx := (hx a r x ma mr (Nat.eq_of_beq_eq_true ib) rx))
          (have he2 (= (tbl-has edge-id x (:edges (filter-world K w))) true))
          (show (= (tbl-has edge-id x (tbl-keep K edge-id (:edges w))) true))
          (rw [tbl-has-keep]) (simp only [kx (And.left hx0) Bool.and_self])
          (have pe (forall [e :- EdgeRow] (=> (= (current-members-eok xm w a (current-members-run-key r) x e) true) (= (K (edge-id e)) true) (= (current-members-eok xm (filter-world K w) a (current-members-run-key r) x e) true))))
          (intros e he0 ke)
          (cases ie (Nat.beq (:id e) x))
          (case [false] (simp only [current-members-eok ie Bool.not_false Bool.true_or]))
          (case [true]
            (simp only [current-members-eok ie Bool.not_true Bool.false_or Bool.and_eq_true] at he0)
            (have s0 := (And.left he0))
            (simp only [current-members-s Bool.and_eq_true] at s0)
            (have aw2 (= (opt-test (current-members-first (:id a)) (act-with-member (:id e) (:acts (filter-world K w)))) true))
            (exact (current-members-awm-keep K (:id e) (:id a) (:acts w) ka2 (And.right (And.right (And.right s0)))))
            (have s1 (= (current-members-s (:acts (filter-world K w)) a (current-members-run-key r) e) true))
            (simp only [current-members-s (And.left s0) (And.left (And.right s0)) (And.left (And.right (And.right s0))) aw2 Bool.and_self])
            (have m1 (= (Bool.or (reach-mem (:debtor e) xm) (current-members-m (:comps (filter-world K w)) (:tasks (filter-world K w)) (:runs (filter-world K w)) e)) true))
            (cases hd (reach-mem (:debtor e) xm))
            (case [true] (simp only [hd Bool.true_or]))
            (case [false]
              (have m0 := (And.right he0))
              (simp only [hd Bool.false_or current-members-m Bool.and_eq_true] at m0)
              (have t1 (= (tbl-all (current-members-tk (:runs (filter-world K w)) (:debtor e)) (:tasks (filter-world K w))) true))
              (rw [er]) (exact (tbl-all-keep-same TaskRow K task-id (current-members-tk (:runs w) (:debtor e)) (:tasks w) (And.left m0)))
              (have c1 (= (Bool.or (Bool.not (tbl-has comp-id (:debtor e) (:comps (filter-world K w)))) (Bool.and (Nat.beq (:kind e) ek-dep) (tbl-all (hk-wif (:debtor e)) (:comps (filter-world K w))))) true))
              (cases hh (tbl-has comp-id (:debtor e) (tbl-keep K comp-id (:comps w))))
              (case [false]
                (have hh2 (= (tbl-has comp-id (:debtor e) (:comps (filter-world K w))) false)) (exact hh)
                (simp only [hh2 Bool.not_false Bool.true_or]))
              (case [true]
                (have hh2 (= (tbl-has comp-id (:debtor e) (:comps (filter-world K w))) true)) (exact hh)
                (rw [tbl-has-keep] at hh) (simp only [Bool.and_eq_true] at hh)
                (have m2 := (And.right m0))
                (simp only [(And.right hh) Bool.not_true Bool.false_or Bool.and_eq_true] at m2)
                (have w3 (= (tbl-all (hk-wif (:debtor e)) (:comps (filter-world K w))) true))
                (exact (tbl-all-keep-same CompRow K comp-id (hk-wif (:debtor e)) (:comps w) (And.right m2)))
                (simp only [hh2 (And.left m2) w3 Bool.not_true Bool.false_or Bool.and_self]))
              (simp only [hd Bool.false_or current-members-m t1 c1 Bool.and_self]))
            (simp only [current-members-eok ie Bool.not_true Bool.false_or s1 m1 Bool.and_self]))
          (have ee2 (= (tbl-all (current-members-eok xm (filter-world K w) a (current-members-run-key r) x) (:edges (filter-world K w))) true))
          (exact (tbl-all-keep EdgeRow K edge-id (current-members-eok xm w a (current-members-run-key r) x) (current-members-eok xm (filter-world K w) a (current-members-run-key r) x) pe (:edges w) (And.right hx0)))
          (simp only [current-members-x hxm Bool.false_or he2 ee2 Bool.and_self]))
        (simp only [current-members-ob ho Bool.false_or cs2 xs Bool.and_self Bool.or_true])))
    (simp only [current-members-rr current-members-r ib2 Bool.not_true Bool.false_or nx (And.left hrr) e1 ob Bool.and_self]))
  (have rr (= (tbl-all (current-members-rr xm (filter-world K w) a) (:runs (filter-world K w))) true))
  (rw [er]) (exact (tbl-all-mem-mono RunRow (current-members-rr xm w a) (current-members-rr xm (filter-world K w) a) (:runs w) hq (And.right ha)))
  (simp only [current-members-a nx (And.left ha) rr Bool.and_self])
  (simp only [current-members-rest])
  (exact (tbl-all-keep-mem ActRow K act-id (current-members-a xm w) (current-members-a xm (filter-world K w)) (:acts w) hp h)))
(a/theorem current-members-filter [xm :- (List Nat), W :- World]
  (=> (= (normalized W) true) (= (i1-runs W) true) (= (acts-alive W) true) (= (filter-safe W) true) (= (current-members xm W) true)
      (= (current-members xm (rule-r-filter W)) true))
  (intros hn hg haa hf h)
  (have hs := (current-members-well-formed xm W h))
  (rw [rule-r-filter-eq])
  (have kr (= (tbl-keep (keep-fn W) run-id (:runs W)) (:runs W)))
  (exact (keep-all-of RunRow (keep-fn W) run-id (:runs W) (fn [q :- RunRow, m :- (List.Mem q (:runs W))] (And.left (run-kept W q hn hg m)))))
  (have hx (forall [a :- ActRow, r :- RunRow, x :- Nat]
             (=> (List.Mem a (:acts W)) (List.Mem r (:runs W)) (= (:id r) (:run a)) (= (reach-mem x (act-contrib a)) true) (= (keep-fn W x) true))))
  (intros a r x ma mr ir rx)
  (simp only [acts-alive] at haa)
  (have al0 := (tbl-all-mem RunRow _ r (:runs W) (tbl-all-mem ActRow _ a (:acts W) haa ma) mr))
  (have ib (= (Nat.beq (:id r) (:run a)) true)) (rw [ir]) (exact (Nat.beq_refl _))
  (simp only [run-ok-for ib Bool.not_true Bool.false_or] at al0)
  (have l := (normalized-runs W r hn mr al0))
  (have pa (= (act-of-run (:id r) a) true)) (simp only [act-of-run]) (rw [ir]) (exact (Nat.beq_refl _))
  (have sm (= (reach-mem (:id a) (tbl-scan act-id (act-of-run (:id r)) (:acts W))) true))
  (exact (scan-mem ActRow act-id (act-of-run (:id r)) a (:acts W) ma pa))
  (have sa (= (reach-mem (:id a) (run-contrib W r)) true))
  (simp only [run-contrib al0 reach-mem-append sm Bool.true_or Bool.or_true])
  (have la := (live-close W (:id r) (:id a) l (retain-run W r (:id a) mr sa)))
  (have g := (gather-mem ActRow (id-is act-id (:id a)) act-contrib a x (:acts W) ma (Nat.beq_refl (:id a)) rx))
  (have gs (= (reach-mem x (retain-succ W (:id a))) true))
  (simp only [retain-succ reach-mem-append g Bool.true_or Bool.or_true])
  (exact (keep-of-live W x (live-close W (:id a) x la gs)))
  (exact (current-members-intro xm _ (well-formed-filter-world W (keep-fn W) hs hf) (current-members-filter-k xm W (keep-fn W) kr hx (current-members-rest-of xm W h)))))

;; ===========================================================================
;; Rule R
;; ===========================================================================
(a/theorem current-members-rule-r-round [w :- World]
  (=> (= (trc w) true) (= (i12-ranks w) true) (= (i14-validity-rule-r (List.nil Nat) (List.nil Nat) w) true) (= (marks-waiting (List.nil Nat) w) true) (= (i10-current-exempt (List.nil Nat) (List.nil Nat) w) true) (= (edge-kinds w) true)
      (= (acts-alive w) true) (= (i7-idle w) true) (= (i1-runs w) true) (= (current-members (List.nil Nat) w) true) (= (filter-safe (normalize w)) true) (= (current-members (List.nil Nat) (rule-r-round w)) true))
  (intros htc hk hv hm hg he haa h7 h0 h hf)
  (have hs := (current-members-well-formed _ w h))
  (simp only [rule-r-round])
  (exact (current-members-filter (List.nil Nat) (normalize w) (normalized-ok w hs haa) (i1-runs-normalize-aa w haa h0) (acts-alive-normalize w hs haa) hf
           (current-members-normalize w htc hk hv hm hg he haa h7 h))))
(a/theorem current-members-rule-r-loop [fuel :- (List Nat)]
  (forall [w :- World]
    (=> (= (trc w) true) (= (i12-ranks w) true) (= (i14-validity-rule-r (List.nil Nat) (List.nil Nat) w) true) (= (marks-waiting (List.nil Nat) w) true) (= (i10-current-exempt (List.nil Nat) (List.nil Nat) w) true) (= (edge-kinds w) true)
      (= (acts-alive w) true) (= (i7-idle w) true) (= (i1-runs w) true) (= (current-members (List.nil Nat) w) true) (= (rounds-safe-loop fuel w) true) (= (current-members (List.nil Nat) (rule-r-loop fuel (rule-r-round w))) true)))
  (induction fuel)
  (case [nil] (intros w htc hk hv hm hg he haa h7 h0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop])
    (exact (current-members-rule-r-round w htc hk hv hm hg he haa h7 h0 h hs)))
  (case [cons x f ih]
    (intros w htc hk hv hm hg he haa h7 h0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (current-members-rule-r-round w htc hk hv hm hg he haa h7 h0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho])
      (exact (ih (rule-r-round w) (trc-rule-r-round w htc (And.left hs)) (i12-ranks-rule-r-round w hk (And.left hs)) (i14-validity-rule-r-rule-r-round w htc hk hv (And.left hs))
               (marks-waiting-rule-r-round (List.nil Nat) w htc hk hv hm (And.left hs)) (i10-current-exempt-rule-r-round (List.nil Nat) (List.nil Nat) w haa (And.right (trc-parts w htc)) hg (And.left hs))
               (edge-kinds-rule-r-round w he (And.left hs)) (acts-alive-round w (current-members-well-formed _ w h) haa) (i7-idle-rule-r-round w haa h7 (And.left hs))
               (i1-runs-rule-r-round w haa h0 (And.left hs)) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))
(a/theorem current-members-rule-r [w :- World]
  (=> (= (trc w) true) (= (i12-ranks w) true) (= (i14-validity-rule-r (List.nil Nat) (List.nil Nat) w) true) (= (marks-waiting (List.nil Nat) w) true) (= (i10-current-exempt (List.nil Nat) (List.nil Nat) w) true) (= (edge-kinds w) true)
      (= (acts-alive w) true) (= (i7-idle w) true) (= (i1-runs w) true) (= (current-members (List.nil Nat) w) true) (= (rule-r-safe w) true) (= (current-members (List.nil Nat) (rule-r w)) true))
  (intros htc hk hv hm hg he haa h7 h0 h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r])
  (exact (current-members-rule-r-loop (rule-r-fuel w) w htc hk hv hm hg he haa h7 h0 h hs)))

;; ===========================================================================
;; The step: chain = chain-to-edge-kinds && current-members [] is a step invariant; L5 safety with no honest hypothesis
;; ===========================================================================
(a/theorem step-current-members [w :- World, it :- Item]
  (=> (= (chain-to-edge-kinds w) true) (= (current-members (List.nil Nat) w) true) (= (current-members (List.nil Nat) (:world (world-step w it))) true))
  (intros hp h)
  (have pl := (chain-to-marks-waiting-parts w (chain-to-edge-kinds-prev w hp)))
  (have pk := (chain-to-i14-ordered-parts w (And.left pl)))
  (have pj := (chain-to-comp-facts-parts w (And.left pk)))
  (have pc := (chain-to-i8-closed-ctx w (And.left pj)))
  (have pb := (chain-start-parts w (And.left pc)))
  (have h0 := (And.right (chain-to-i1-runs-parts w (And.left (chain-to-i8-closed-parts w (And.left pj))))))
  (have h7 := (chain-to-i8-closed-i7-idle w (And.left pj)))
  (have hga := (And.left pb))
  (have hk := (And.left (And.right pb)))
  (have hv := (And.right pk))
  (simp only [i14-ordered] at hv)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true]
    (have e2 := (step-accepted w it ha)) (rw [e2])
    (have r0 := (i14-validity-raw-raw (List.nil Nat) (List.nil Nat) false w it hv))
    (have rq := (round-facts-parts w (And.right (And.right (And.right (And.right pb))))))
    (exact (current-members-rule-r (:world (raw w it)) (trc-raw w it hga h7 (And.right (And.right (And.right (And.right rq))))) (i12-ranks-raw w it hk)
             (i14-validity-rule-r-of-i14-validity-raw (List.nil Nat) false _ r0 (dep-active-of-i7-idle _ (i7-idle-raw w it h7)))
             (marks-waiting-raw _ w it (And.right pj) h7 hga (And.right pc) (And.right pl))
             (i10-current-raw w it (And.right pc)) (edge-kinds-raw w it (chain-to-edge-kinds-edge-kinds w hp)) (raw-acts-alive w it hga) (i7-idle-raw w it h7)
             (i1-runs-raw w it hga h0) (current-members-raw (List.nil Nat) w it hp h) (step-rule-r-safe w it (And.left pc))))))
(a/defn chain [w :- World] Bool (Bool.and (chain-to-edge-kinds w) (current-members (List.nil Nat) w)))
(a/theorem chain-parts [w :- World] (=> (= (chain w) true) (And (= (chain-to-edge-kinds w) true) (= (current-members (List.nil Nat) w) true)))
  (intro h) (simp only [chain Bool.and_eq_true] at h) (exact h))
(a/theorem chain-empty [] (= (chain empty-world) true) (rfl))
(a/theorem step-chain [w :- World, it :- Item] (=> (= (chain w) true) (= (chain (:world (world-step w it))) true))
  (intro h)
  (have p := (chain-parts w h))
  (have a1 := (step-chain-to-edge-kinds w it (And.left p)))
  (have a2 := (step-current-members w it (And.left p) (And.right p)))
  (simp only [chain a1 a2 Bool.and_self]))
;; Theorem (h-mem2, P11 second half): the memory bundle holds after every step
(a/theorem step-current-members-total [w :- World, it :- Item] (=> (= (chain w) true) (= (current-members (List.nil Nat) (:world (world-step w it))) true))
  (intro h) (exact (And.right (chain-parts _ (step-chain w it h)))))
;; Theorem (L5 safety, unconditional): in a chain world a quiescent waiting computation has a blocked dependency,
;; an eligible one or an unblocked task -- no honest hypothesis (h-mark and h-mem2 are invariants)
(a/theorem l5-safety-total [w :- World, c0 :- Nat, c :- CompRow]
  (=> (= (chain w) true) (= (quiescent w) true) (= (comp-find w c0) (Option.some CompRow c)) (= (comp-waiting c) true)
      (none-blocked w c0) (none-eligible w c0) (tasks-blocked w c0) False)
  (intros h hq hf hw nb ne tb)
  (have p := (chain-parts w h))
  (have hl := (chain-to-edge-kinds-prev w (And.left p)))
  (have pj := (chain-to-comp-facts-parts w (And.left (chain-to-i14-ordered-parts w (And.left (chain-to-marks-waiting-parts w hl))))))
  (have pc := (chain-to-i8-closed-ctx w (And.left pj)))
  (have h3c (= (chain-to-i10-current w) true)) (simp only [chain-to-i10-current (And.left pc) (And.right pc) Bool.and_self])
  (exact (current-members-l5-safety w c0 c h3c (And.right pj) (And.right p) hq (chain-to-marks-waiting-h-mark w hl) hf hw nb ne tb)))
;; the literal h-mem2 of progress/l5.clj, after every step
(a/theorem step-h-mem2-total [w :- World, it :- Item] (=> (= (chain w) true) (= (h-mem2 (:world (world-step w it))) true))
  (intro h)
  (have p := (chain-parts _ (step-chain w it h)))
  (have pj := (chain-to-comp-facts-parts _ (And.left (chain-to-i14-ordered-parts _ (And.left (chain-to-marks-waiting-parts _ (chain-to-edge-kinds-prev _ (And.left p))))))))
  (exact (current-members-h-mem2 _ (And.right p) (And.right pj))))
