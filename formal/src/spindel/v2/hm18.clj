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

;; ===========================================================================
;; The frame bundle fb zl zf zd zs: facts that the frame h3-fm transports, carried through the cascades
;; of the normalization pass by the copier.
;;   - every id of zf is free (h3-free zl): the non-dep edges on the round's strays, free at the pass start
;;   - no activation holds a current run of a computation of zd (the strays demoted so far)
;;   - every edge is a dep edge, or its debtor is outside zs, or its id is in zf
;; ===========================================================================
(a/defn fb-nr [cs :- (List CompRow), d :- Nat, b :- ActRow, r :- RunRow] Bool
  (Bool.not (Bool.and (Nat.beq (:id r) (:run b)) (Bool.and (Nat.beq (:of r) d) (tbl-any (h3-cur (rk3 r)) cs)))))
(a/defn fb-nb [cs :- (List CompRow), rs :- (List RunRow), d :- Nat, b :- ActRow] Bool (tbl-all (fb-nr cs d b) rs))
(a/defn fb-nh [w :- World, d :- Nat] Bool (tbl-all (fb-nb (:comps w) (:runs w) d) (:acts w)))
(a/defn fb-e [S :- (List Nat), F :- (List Nat), e :- EdgeRow] Bool
  (Bool.or (Nat.beq (:kind e) ek-dep) (Bool.or (Bool.not (reach-mem (:debtor e) S)) (reach-mem (:id e) F))))
(a/defn fb-rest [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] Bool
  (Bool.and (tbl-all (h3-free zl w) zf) (Bool.and (tbl-all (fb-nh w) zd) (tbl-all (fb-e zs zf) (:edges w)))))
(a/defn fb [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] Bool (Bool.and (inv-sample w) (fb-rest zl zf zd zs w)))
(a/theorem fb-sample [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] (=> (= (fb zl zf zd zs w) true) (= (inv-sample w) true))
  (intro h) (simp only [fb Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem fb-rest-of [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] (=> (= (fb zl zf zd zs w) true) (= (fb-rest zl zf zd zs w) true))
  (intro h) (simp only [fb Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem fb-intro [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] (=> (= (inv-sample w) true) (= (fb-rest zl zf zd zs w) true) (= (fb zl zf zd zs w) true))
  (intros h1 h2) (simp only [fb h1 h2 Bool.and_self]))
(a/theorem fb-parts [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World]
  (=> (= (fb zl zf zd zs w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (fb-sample zl zf zd zs w h))))
(a/theorem fb-fr [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] (=> (= (fb-rest zl zf zd zs w) true) (= (tbl-all (h3-free zl w) zf) true))
  (intro h) (simp only [fb-rest Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem fb-nhs [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] (=> (= (fb-rest zl zf zd zs w) true) (= (tbl-all (fb-nh w) zd) true))
  (intro h) (simp only [fb-rest Bool.and_eq_true] at h) (exact (And.left (And.right h))))
(a/theorem fb-er [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World] (=> (= (fb-rest zl zf zd zs w) true) (= (tbl-all (fb-e zs zf) (:edges w)) true))
  (intro h) (simp only [fb-rest Bool.and_eq_true] at h) (exact (And.right (And.right h))))
(a/theorem fb-rest-mk [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World]
  (=> (= (tbl-all (h3-free zl w) zf) true) (= (tbl-all (fb-nh w) zd) true) (= (tbl-all (fb-e zs zf) (:edges w)) true)
      (= (fb-rest zl zf zd zs w) true))
  (intros h1 h2 h3) (simp only [fb-rest h1 h2 h3 Bool.and_self]))

(a/theorem fb-nh-of [w :- World, d :- Nat] (=> (= (fb-nh w d) true) (h16-nh w d))
  (intro h)
  (apply h16-nh-mk)
  (intros a r ma mr ir ho hc)
  (simp only [fb-nh] at h)
  (have q := (tbl-all-mem RunRow _ r (:runs w) (tbl-all-mem ActRow _ a (:acts w) h ma) mr))
  (have i1 (= (Nat.beq (:id r) (:run a)) true)) (rw [ir]) (exact (Nat.beq_refl _))
  (have i2 (= (Nat.beq (:of r) d) true)) (rw [ho]) (exact (Nat.beq_refl _))
  (simp only [fb-nr i1 i2 hc Bool.and_self Bool.not_true] at q)
  (cases q))
(a/theorem fb-nh-mk [w :- World, d :- Nat] (=> (h16-nh w d) (= (fb-nh w d) true))
  (intro h)
  (simp only [fb-nh])
  (apply (all-of-mem ActRow _ (:acts w)))
  (intros a ma)
  (apply (all-of-mem RunRow _ (:runs w)))
  (intros r mr)
  (cases i1 (Nat.beq (:id r) (:run a)))
  (case [false] (simp only [fb-nr i1 Bool.false_and Bool.not_false]))
  (case [true]
    (cases i2 (Nat.beq (:of r) d))
    (case [false] (simp only [fb-nr i2 Bool.false_and Bool.and_false Bool.not_false]))
    (case [true]
      (cases hc (tbl-any (h3-cur (rk3 r)) (:comps w)))
      (case [false] (simp only [fb-nr hc Bool.and_false Bool.not_false]))
      (case [true]
        (exact (False.elim (h16-nh-use w d h a r ma mr (Nat.eq_of_beq_eq_true i1) (Nat.eq_of_beq_eq_true i2) hc)))))))
;; the transport: the frame moves the first two parts; the edge part is the operation's own
(a/theorem fb-move [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, w2 :- World]
  (=> (h3-fm w w2) (= (tbl-all (fb-e zs zf) (:edges w2)) true) (= (fb-rest zl zf zd zs w) true) (= (fb-rest zl zf zd zs w2) true))
  (intros hf he h)
  (exact (fb-rest-mk zl zf zd zs w2
           (tbl-all-mono Nat (h3-free zl w) (h3-free zl w2)
             (fn [y :- Nat, q :- (= (h3-free zl w y) true)] (fm-free zl w w2 y hf q)) zf (fb-fr zl zf zd zs w h))
           (tbl-all-mono Nat (fb-nh w) (fb-nh w2)
             (fn [d :- Nat, q :- (= (fb-nh w d) true)] (fb-nh-mk w2 d (h16-nh-fm w w2 d hf (fb-nh-of w d q)))) zd (fb-nhs zl zf zd zs w h))
           he)))
(a/theorem fb-e-keep [S :- (List Nat), F :- (List Nat), f :- (=> EdgeRow EdgeRow),
                      hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                      hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                      hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))), e :- EdgeRow]
  (=> (= (fb-e S F e) true) (= (fb-e S F (f e)) true))
  (intro h)
  (have i1 (= (:id (f e)) (:id e))) (exact (hid e))
  (simp only [fb-e (hk e) (hd e) i1]) (simp only [fb-e] at h) (exact h))

;; ---- frames of the two row deletions
(a/theorem fb-fm-run-del [w :- World, x :- Nat] (h3-fm w (run-del w x))
  (apply fm-mk)
  (exact (fm-acts-of w w (fm-refl w)))
  (simp only [run-del set-runs])
  (exact (tbl-all-del RunRow run-id x (fm-rr (:runs w)) (fm-rr (:runs w))
           (fn [q :- RunRow, hq :- (= (fm-rr (:runs w) q) true), hx :- (= (Nat.beq (run-id q) x) false)] hq) (:runs w) (fm-runs-of w w (fm-refl w))))
  (intros k hc) (exact hc))
(a/theorem fb-fm-comp-del [w :- World, x :- Nat] (h3-fm w (comp-del w x))
  (apply fm-mk)
  (exact (fm-acts-of w w (fm-refl w)))
  (exact (fm-runs-of w w (fm-refl w)))
  (intros k hc) (simp only [comp-del set-comps] at hc) (exact (h3-any-del-back CompRow comp-id x (h3-cur k) (:comps w) hc)))

;; ---- the row-function edits (their callers are patched to these forms)
(a/theorem fb-comp-upd-m [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                          hep :- (forall [c :- CompRow] (<= (:epoch c) (:epoch (f c))))]
  (=> (= (fb zl zf zd zs w) true) (= (fb zl zf zd zs (comp-upd w x f)) true))
  (intro h)
  (exact (fb-intro zl zf zd zs _ (inv-comp-upd w x f hid hp (fb-sample zl zf zd zs w h))
           (fb-move zl zf zd zs w (comp-upd w x f) (fm-comp-upd w x f hid hep) (fb-er zl zf zd zs w (fb-rest-of zl zf zd zs w h)) (fb-rest-of zl zf zd zs w h)))))
(a/theorem fb-run-upd-m [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                         hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         hk :- (forall [q :- RunRow] (= (rk3 (f q)) (rk3 q)))]
  (=> (= (fb zl zf zd zs w) true) (= (fb zl zf zd zs (run-upd w x f)) true))
  (intro h)
  (exact (fb-intro zl zf zd zs _ (inv-run-upd w x f hid (fb-sample zl zf zd zs w h))
           (fb-move zl zf zd zs w (run-upd w x f) (fm-run-upd w x f hk) (fb-er zl zf zd zs w (fb-rest-of zl zf zd zs w h)) (fb-rest-of zl zf zd zs w h)))))
(a/theorem fb-task-upd [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                        hid :- (forall [r :- TaskRow] (= (task-id (f r)) (task-id r)))]
  (=> (= (fb zl zf zd zs w) true) (= (fb zl zf zd zs (task-upd w x f)) true))
  (intro h)
  (exact (fb-intro zl zf zd zs _ (inv-task-upd w x f hid (fb-sample zl zf zd zs w h))
           (fb-move zl zf zd zs w (task-upd w x f) (fm-task-upd w x f) (fb-er zl zf zd zs w (fb-rest-of zl zf zd zs w h)) (fb-rest-of zl zf zd zs w h)))))
(a/theorem fb-edge-upd [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                        hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                        hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                        hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                        hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                        hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e)))]
  (=> (= (fb zl zf zd zs w) true) (= (fb zl zf zd zs (edge-upd w x f)) true))
  (intro h)
  (exact (fb-intro zl zf zd zs _ (inv-edge-upd w x f hid hk hc hd hm (fb-sample zl zf zd zs w h))
           (fb-move zl zf zd zs w (edge-upd w x f) (fm-edge-upd w x f)
             (ep-edge-upd (fb-e zs zf) w x f (fb-e-keep zs zf f hid hk hd) (fb-er zl zf zd zs w (fb-rest-of zl zf zd zs w h)))
             (fb-rest-of zl zf zd zs w h)))))
(a/theorem fb-act-upd-m [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, x :- Nat, f :- (=> ActRow ActRow),
                         hid :- (forall [r :- ActRow] (= (act-id (f r)) (act-id r))), hfm :- (h3-fm w (act-upd w x f))]
  (=> (= (fb zl zf zd zs w) true) (= (fb zl zf zd zs (act-upd w x f)) true))
  (intro h)
  (exact (fb-intro zl zf zd zs _ (inv-act-upd w x f hid (fb-sample zl zf zd zs w h))
           (fb-move zl zf zd zs w (act-upd w x f) hfm (fb-er zl zf zd zs w (fb-rest-of zl zf zd zs w h)) (fb-rest-of zl zf zd zs w h)))))

(def FB (mk-bundle 'fb '[zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat)] "fb-" {}))
(swap! (:renames FB) assoc 'inv-parts 'fb-parts 'inv-task-upd 'fb-task-upd 'inv-edge-upd 'fb-edge-upd
       'inv-comp-upd 'fb-comp-upd-NONE 'inv-run-upd 'fb-run-upd-NONE 'inv-act-upd 'fb-act-upd-NONE
       'inv-filter-world 'fb-filter-world-NONE 'inv-act-ins-fresh 'fb-act-ins-NONE)
(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-set-pins
            inv-resource-del inv-scope-del inv-cleanup-ins inv-set-released inv-set-pending-act]]
  (prim! FB o nil))
(prim! FB 'inv-run-del '(fb-move zl zf zd zs w (run-del w x) (fb-fm-run-del w x) (fb-er zl zf zd zs w R) R))
(prim! FB 'inv-comp-del-unref '(fb-move zl zf zd zs w (comp-del w x) (fb-fm-comp-del w x) (fb-er zl zf zd zs w R) R))
(prim! FB 'inv-drop-act '(fb-move zl zf zd zs w (drop-act w a) (fm-drop-act w a) (ep-filter (fb-e zs zf) (cred-ne a) (:edges w) (fb-er zl zf zd zs w R)) R))
(prim! FB 'inv-drop-edges '(fb-move zl zf zd zs w (drop-edges w p) (fm-drop-edges w p) (ep-filter (fb-e zs zf) p (:edges w) (fb-er zl zf zd zs w R)) R))
(prim! FB 'inv-remove-edge '(fb-move zl zf zd zs w (remove-edge w x) (fm-remove-edge w x) (ep-remove-edge (fb-e zs zf) w x (fb-er zl zf zd zs w R)) R))
(prim! FB 'unmark-edge-inv-sample
       '(fb-move zl zf zd zs w (unmark-edge w x) (h16-fm-unmark w x)
          (ep-unmark-edge (fb-e zs zf) (fn [e :- EdgeRow, q :- (= (fb-e zs zf e) true)] q) w x (fb-er zl zf zd zs w R)) R))
(defn fb-patch [form]
  (->> (@#'spindel.v2.idle/fix-f form)
       (subst-forms (fn [y] (and (seq? y) (= 'inv-comp-upd (first y)) (>= (count y) 6)))
                    (fn [[_ w x f hid hp & more]]
                      (let [h (if (seq? f) (first f) f)
                            lem (fn [l] (if (seq? f) (apply list l (rest f)) l))]
                        (apply list 'fb-comp-upd-m 'zl 'zf 'zd 'zs w x f hid hp
                               (if (contains? '#{comp-inc-epoch comp-demand-row comp-replace-row comp-start-row} h)
                                 (lem (symbol (str h "-h3ep")))
                                 '(fn [c :- CompRow] (Nat.le_refl (:epoch c))))
                               more))))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (>= (count y) 5)))
                    (fn [[_ w x f hid & more]]
                      (apply list 'fb-run-upd-m 'zl 'zf 'zd 'zs w x f hid '(fn [q :- RunRow] (Eq.refl (rk3 q))) more)))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-act-upd (first y)) (>= (count y) 5) (seq? (nth y 3)) (= 'act-fill (first (nth y 3)))))
                    (fn [[_ w x f hid & more]]
                      (apply list 'fb-act-upd-m 'zl 'zf 'zd 'zs w x f hid (apply list 'fm-act-fill w x (rest f)) more)))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! FB n fb-patch))
(lcopy! FB 'inv-demote)

;; ===========================================================================
;; demote of a stray x (x is in the list)
;; ===========================================================================
(a/theorem h18-single [d :- Nat, x :- Nat, L :- (List Nat)]
  (=> (= (reach-mem d (List.cons Nat x (List.nil Nat))) true) (= (reach-mem x L) true) (= (reach-mem d L) true))
  (intros hd hx)
  (simp only [reach-mem-cons reach-mem Bool.or_false] at hd)
  (rw [(Nat.eq_of_beq_eq_true hd)]) (exact hx))
(a/theorem h18-list-in [L :- (List Nat), w :- World, x :- Nat]
  (=> (= (reach-mem x L) true) (= (h3 (List.cons Nat x L) w) true) (= (h3 L w) true))
  (intros hx h)
  (have hs := (h3-sample _ w h))
  (have hr (= (h3-rest (List.append Nat (List.cons Nat x (List.nil Nat)) L) w) true)) (exact (h3-rest-of _ w h))
  (apply (h3-intro L w hs))
  (apply (h16-dis L w (List.cons Nat x (List.nil Nat)) hs))
  (intros d hd) (apply Or.inl) (exact (h18-single d x L hd hx))
  (exact hr))
(a/theorem h18-comp-upd-in [L :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                            hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                            hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                            hep :- (forall [c :- CompRow] (<= (:epoch c) (:epoch (f c))))]
  (=> (= (reach-mem x L) true) (= (h3 L w) true) (= (h3 L (comp-upd w x f)) true))
  (intros hx h) (exact (h18-list-in L _ x hx (h16-comp-upd-x L w x f hid hp hep h))))
;; a dep edge of an exempt creditor is free; a non-dep edge whose creditor is a computation is free
(a/theorem h18-free-cred-in [L :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (h3-rest L w) true) (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) true) (= (reach-mem (:creditor e) L) true)
      (= (h3-free L w (:id e)) true))
  (intros hr me kd hc)
  (apply (h3-free-by L w (:id e)))
  (intros b r mb mr ir hxo hcur hmem hxx)
  (have u := (h3-ob-use L w b r (:id e) e hr mb mr ir hxo hcur hmem hxx me (Eq.refl (:id e))))
  (have sk := (And.left u))
  (simp only [h3-s Bool.and_eq_true] at sk)
  (have c2 := (And.left (And.right sk)))
  (simp only [kd Bool.not_true Bool.false_or rk3] at c2)
  (rw [(Nat.eq_of_beq_eq_true c2)] at hc) (rw [hxo] at hc) (cases hc))
(a/theorem h18-free-wait-comp [L :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (h3-rest L w) true) (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) false)
      (= (tbl-has comp-id (:creditor e) (:comps w)) true) (= (h3-free L w (:id e)) true))
  (intros hs hr me kd hc)
  (apply (h3-free-by L w (:id e)))
  (intros b r mb mr ir hxo hcur hmem hxx)
  (have u := (h3-ob-use L w b r (:id e) e hr mb mr ir hxo hcur hmem hxx me (Eq.refl (:id e))))
  (have sk := (And.left u))
  (simp only [h3-s Bool.and_eq_true] at sk)
  (have c3 := (And.left (And.right (And.right sk))))
  (simp only [kd Bool.false_or] at c3)
  (have z := (act-not-comp w (:id b) hs (has-of-mem ActRow act-id b (:acts w) mb)))
  (rw [(Nat.eq_of_beq_eq_true c3)] at hc) (rw [z] at hc) (cases hc))

(a/theorem h18-free-nil [L :- (List Nat), w :- World, x :- Nat] (=> (= (h3-free (List.nil Nat) w x) true) (= (h3-free L w x) true))
  (intro h)
  (apply (h16-free-mono (List.nil Nat) L w x))
  (intros d hd) (simp only [reach-mem] at hd) (cases hd)
  (exact h))
(a/theorem h18-fr-dep [L :- (List Nat), w :- World, x :- Nat]
  (=> (= (h3-rest L w) true) (= (reach-mem x L) true)
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (not-dep-of x e) false) (= (h3-free L w (:id e)) true))))
  (intros hr hx e me hn)
  (simp only [not-dep-of dep-of] at hn)
  (have hn2 := (bnot-false _ hn))
  (simp only [Bool.and_eq_true] at hn2)
  (have hc (= (reach-mem (:creditor e) L) true)) (rw [(Nat.eq_of_beq_eq_true (And.right hn2))]) (exact hx)
  (exact (h18-free-cred-in L w e hr me (And.left hn2) hc)))
(a/theorem h18-fr-avoid [S :- (List Nat), R :- (List Nat), F :- (List Nat), D :- (List Nat), W :- World, x :- Nat]
  (=> (= (reach-mem x S) true) (= (tbl-all (rm-in S) R) true) (= (vr S R W) true) (= (h3 (List.append Nat S (List.nil Nat)) W) true)
      (= (fb (List.nil Nat) F D S W) true) (= (tbl-has comp-id x (:comps W)) true)
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges W)) (= (edge-avoids x e) false) (= (h3-free (List.append Nat S (List.nil Nat)) W (:id e)) true))))
  (intros hx hR hv h hfb hcx e me ha)
  (have hs := (h3-sample _ W h))
  (have hr := (h3-rest-of _ W h))
  (have p := (vrk-parts _ _ _ _ _ (vr-rest-of _ _ W hv)))
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
    (exact (h18-free-cred-in (List.append Nat S (List.nil Nat)) W e hr me kd hc)))
  (case [false]
    (cases hd (Nat.beq (:debtor e) x))
    (case [true]
      (have dS (= (reach-mem (:debtor e) S) true)) (rw [(Nat.eq_of_beq_eq_true hd)]) (exact hx)
      (have fe := (tbl-all-mem EdgeRow _ e (:edges W) (fb-er (List.nil Nat) F D S W (fb-rest-of (List.nil Nat) F D S W hfb)) me))
      (simp only [fb-e kd dS Bool.not_true Bool.false_or] at fe)
      (exact (h18-free-nil (List.append Nat S (List.nil Nat)) W (:id e) (all-reach-mem (h3-free (List.nil Nat) W) (:id e) F (fb-fr (List.nil Nat) F D S W (fb-rest-of (List.nil Nat) F D S W hfb)) fe))))
    (case [false]
      (simp only [edge-avoids hd Bool.not_false Bool.and_true] at ha)
      (have hc := (bnot-false _ ha))
      (have hcc (= (tbl-has comp-id (:creditor e) (:comps W)) true)) (rw [(Nat.eq_of_beq_eq_true hc)]) (exact hcx)
      (exact (h18-free-wait-comp (List.append Nat S (List.nil Nat)) W e hs hr me kd hcc)))))

(a/theorem h18-demote-x [S :- (List Nat), R :- (List Nat), gx :- (List Nat), gk :- (List Nat), F :- (List Nat), D :- (List Nat), W :- World, x :- Nat]
  (=> (= (reach-mem x S) true) (= (tbl-all (rm-in S) R) true) (= (inv-rank W) true) (= (vr S (List.cons Nat x R) W) true)
      (= (hmk (List.append Nat S (List.nil Nat)) W) true) (= (g10 gx gk W) true) (= (ekb W) true) (= (fb (List.nil Nat) F D S W) true)
      (= (h3 (List.append Nat S (List.nil Nat)) W) true) (= (h3 (List.append Nat S (List.nil Nat)) (demote W x)) true))
  (intros hx hR hk hv hm hg he hfb h)
  (have hX := (rm-app-l x S (List.nil Nat) hx))
  (cases hf (comp-find W x))
  (case [none] (simp only [demote hf]) (exact h))
  (case [some c]
    (cases hi (:idle c))
    (case [true] (simp only [demote hf hi]) (exact h))
    (case [false]
      (simp only [demote hf hi demote-edges])
      (have h1 := (h3-run-cascade-g (List.append Nat S (List.nil Nat)) (List.append Nat S (List.nil Nat)) gx gk W (cancel-jobs (demote-cancels W c)) hg hm he h))
      (have m1 := (hmk-run-cascade (List.append Nat S (List.nil Nat)) W (cancel-jobs (demote-cancels W c)) hm))
      (have v1 := (vr-run-cascade S (List.cons Nat x R) W (cancel-jobs (demote-cancels W c)) hv))
      (have f1 := (fb-run-cascade (List.nil Nat) F D S W (cancel-jobs (demote-cancels W c)) hfb))
      (have h2 (= (h3 (List.append Nat S (List.nil Nat)) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c))) true))
      (cases hb (demote-cur W c))
      (case [false] (simp only [demote-epoch]) (exact h1))
      (case [true] (simp only [demote-epoch])
        (exact (h18-comp-upd-in (List.append Nat S (List.nil Nat)) (run-cascade W (cancel-jobs (demote-cancels W c))) x comp-inc-epoch (fn [q :- CompRow] (Eq.refl (comp-id q))) (fn [q :- CompRow] (Eq.refl (:pending q)))
                 comp-inc-epoch-h3ep hX h1)))
      (have m2 := (hmk-demote-epoch (List.append Nat S (List.nil Nat)) (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c) m1))
      (have v2 := (vr-demote-epoch S (List.cons Nat x R) (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c) v1))
      (have f2 := (fb-demote-epoch (List.nil Nat) F D S (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c) f1))
      (have dk (= (tbl-all (hk-dok (List.append Nat S (List.nil Nat)) (:comps (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c))) (not-dep-of x)) (:edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)))) true))
      (apply (all-of-mem EdgeRow _ (:edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c))))) (intros e me) (exact (hk-dok-own _ _ x e hX))
      (have h3x := (h3-drop-edges (List.append Nat S (List.nil Nat)) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) dk (h18-fr-dep (List.append Nat S (List.nil Nat)) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) x (h3-rest-of _ _ h2) hX) h2))
      (have m3 := (hmk-drop-edges (List.append Nat S (List.nil Nat)) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) dk m2))
      (have v3 := (vr-drop-r S R (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x (ncd-drop (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) x) (vr-drop-edges S (List.cons Nat x R) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) v2)))
      (have f3 := (fb-drop-edges (List.nil Nat) F D S (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) f2))
      (have nc := (ncd-drop (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) x))
      (cases hf3 (comp-find (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x))
      (case [none] (simp only [demote-finish hf3]) (exact h3x))
      (case [some c3]
        (cases hkp (demote-keep (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) c3))
        (case [true]
          (simp only [demote-finish hf3 hkp])
          (exact (h18-comp-upd-in (List.append Nat S (List.nil Nat)) (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x _ (comp-make-idle-id _) (comp-make-idle-pending _) (fn [q :- CompRow] (Nat.le_refl (:epoch q))) hX h3x)))
        (case [false]
          (simp only [demote-finish hf3 hkp])
          (have hcx := (tbl-find-has CompRow comp-id x c3 (:comps (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x))) hf3))
          (have h4 := (h3-drop-edges (List.append Nat S (List.nil Nat)) (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) (edge-avoids x) (hk-dok-avoid S R (List.nil Nat) (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x hx hR v3 nc m3)
                        (h18-fr-avoid S R F D (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x hx hR v3 h3x f3 hcx) h3x))
          (have s4 := (h3-sample _ _ h4))
          (exact (h3-intro (List.append Nat S (List.nil Nat)) _ (inv-comp-del-unref (drop-edges (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) (edge-avoids x)) x (drop-edges-avoids (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x) s4)
                   (h3r-comp-del (List.append Nat S (List.nil Nat)) (drop-edges (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) (edge-avoids x)) x (h3-db-of (drop-edges (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) (edge-avoids x)) s4) (h3-rest-of _ _ h4)))))))))

;; ---- after its demote, no activation holds a current run of x
(a/theorem h18-nh-dead [w :- World, d :- Nat]
  (=> (= (acts-alive w) true) (= (tbl-all (not-alive-of d) (:runs w)) true) (h16-nh w d))
  (intros haa hn)
  (apply h16-nh-mk)
  (intros a r ma mr ir ho hc)
  (simp only [acts-alive] at haa)
  (have al0 := (tbl-all-mem RunRow _ r (:runs w) (tbl-all-mem ActRow _ a (:acts w) haa ma) mr))
  (have ib (= (Nat.beq (:id r) (:run a)) true)) (rw [ir]) (exact (Nat.beq_refl _))
  (simp only [run-ok-for ib Bool.not_true Bool.false_or] at al0)
  (have na := (tbl-all-mem RunRow _ r (:runs w) hn mr))
  (have ob (= (Nat.beq (:of r) d) true)) (rw [ho]) (exact (Nat.beq_refl _))
  (simp only [not-alive-of al0 ob Bool.not_true Bool.or_self] at na)
  (cases na))
(a/theorem h18-runs-finish [w :- World, x :- Nat, vs :- (List Valid)] (= (:runs (demote-finish w x vs)) (:runs w))
  (cases hf (comp-find w x))
  (case [none] (simp only [demote-finish hf]))
  (case [some c]
    (cases hk (demote-keep w c))
    (case [true] (simp only [demote-finish hf hk comp-upd set-comps]))
    (case [false] (simp only [demote-finish hf hk comp-del set-comps drop-edges set-edges]))))
(a/theorem h18-bn-aa [a :- Nat, k :- Nat, w :- World] (=> (= (bn a k w) true) (And (= (inv-sample w) true) (= (acts-alive w) true)))
  (intro h) (simp only [bn Bool.and_eq_true] at h) (exact (And.intro (And.left h) (And.left (And.right h)))))
(a/theorem h18-nh-demote [a :- Nat, k :- Nat, W :- World, x :- Nat]
  (=> (= (bn a k W) true) (= (g7 W) true) (h16-nh (demote W x) x))
  (intros hb h7)
  (have hs := (And.left (h18-bn-aa a k W hb)))
  (have haa := (And.right (h18-bn-aa a k W hb)))
  (have aa2 := (And.right (h18-bn-aa a k (demote W x) (bn-demote a k W x hb))))
  (cases hf (comp-find W x))
  (case [none]
    (simp only [demote hf])
    (apply h16-nh-mk)
    (intros b r mb mr ir ho hc)
    (apply (any-elim CompRow (h3-cur (rk3 r)) _ (:comps W) hc))
    (intros c2 mc2 hq)
    (simp only [h3-cur rk3 Bool.and_eq_true] at hq)
    (have z := (has-of-mem CompRow comp-id c2 (:comps W) mc2))
    (have ic (= (comp-id c2) x)) (exact (Eq.trans (Nat.eq_of_beq_eq_true (And.left hq)) ho))
    (rw [ic (tbl-find-none-has CompRow comp-id x (:comps W) hf)] at z) (cases z))
  (case [some c]
    (have mc := (tbl-find-mem CompRow comp-id x c (:comps W) hf))
    (have ic (= (:id c) x)) (exact (tbl-find-id CompRow comp-id x c (:comps W) hf))
    (cases hi (:idle c))
    (case [true]
      (simp only [demote hf hi])
      (apply h16-nh-mk)
      (intros b r mb mr ir ho hc)
      (simp only [acts-alive] at haa)
      (have al0 := (tbl-all-mem RunRow _ r (:runs W) (tbl-all-mem ActRow _ b (:acts W) haa mb) mr))
      (have ib (= (Nat.beq (:id r) (:run b)) true)) (rw [ir]) (exact (Nat.beq_refl _))
      (simp only [run-ok-for ib Bool.not_true Bool.false_or] at al0)
      (have p := (g7k-parts _ _ _ (g7-rest-of W h7)))
      (have aw := (tbl-all-mem RunRow _ r (:runs W) (And.left p) mr))
      (simp only [a7-one al0 Bool.not_true Bool.false_or awake] at aw)
      (have q := (tbl-all-mem CompRow _ c (:comps W) aw mc))
      (have ob (= (Nat.beq (:id c) (:of r)) true)) (rw [ic ho]) (exact (Nat.beq_refl _))
      (simp only [not-idle-if-id ob hi Bool.not_true Bool.or_self] at q)
      (cases q))
    (case [false]
      (simp only [demote hf hi demote-edges] at aa2)
      (simp only [demote hf hi demote-edges])
      (apply (h18-nh-dead _ x aa2))
      (rw [(h18-runs-finish (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x (validity-of (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) x))])
      (show (= (tbl-all (not-alive-of x) (:runs (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)))) true))
      (rw [(runs-demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c))])
      (have nd := (demote-dead W c hs haa))
      (rw [ic] at nd) (exact nd))))

;; ---- the fold over the strays: the demoted ones are collected in the bundle's zd
(a/defn h18-acc [R :- (List Nat), D :- (List Nat)] (List Nat) (match R [nil D] [(cons x t) (h18-acc t (List.cons Nat x D))]))
(a/theorem h18-acc-d [d :- Nat, R :- (List Nat)]
  (forall [D :- (List Nat)] (=> (= (reach-mem d D) true) (= (reach-mem d (h18-acc R D)) true)))
  (induction R)
  (case [nil] (intros D h) (simp only [h18-acc]) (exact h))
  (case [cons x t ih] (intros D h) (simp only [h18-acc]) (apply ih) (simp only [reach-mem-cons h Bool.or_true])))
(a/theorem h18-acc-r [d :- Nat, R :- (List Nat)]
  (forall [D :- (List Nat)] (=> (= (reach-mem d R) true) (= (reach-mem d (h18-acc R D)) true)))
  (induction R)
  (case [nil] (intros D h) (simp only [reach-mem] at h) (cases h))
  (case [cons x t ih]
    (intros D h)
    (simp only [reach-mem-cons Bool.or_eq_true] at h)
    (simp only [h18-acc])
    (cases h)
    (case [inl h1] (apply (h18-acc-d d t)) (simp only [reach-mem-cons h1 Bool.true_or]))
    (case [inr h1] (exact (ih (List.cons Nat x D) h1)))))
(a/theorem fb-add-d [zl :- (List Nat), zf :- (List Nat), zd :- (List Nat), zs :- (List Nat), w :- World, x :- Nat]
  (=> (h16-nh w x) (= (fb zl zf zd zs w) true) (= (fb zl zf (List.cons Nat x zd) zs w) true))
  (intros hn h)
  (have r := (fb-rest-of zl zf zd zs w h))
  (have n2 (= (tbl-all (fb-nh w) (List.cons Nat x zd)) true))
  (simp only [tbl-all (fb-nh-mk w x hn) (fb-nhs zl zf zd zs w r) Bool.and_self])
  (exact (fb-intro zl zf (List.cons Nat x zd) zs w (fb-sample zl zf zd zs w h)
           (fb-rest-mk zl zf (List.cons Nat x zd) zs w (fb-fr zl zf zd zs w r) n2 (fb-er zl zf zd zs w r)))))
(a/theorem h18-demote-fold [S :- (List Nat), gk :- (List Nat), F :- (List Nat), a :- Nat, k :- Nat, R :- (List Nat)]
  (forall [gx :- (List Nat), D :- (List Nat), W :- World]
    (=> (= (tbl-all (rm-in S) R) true) (= (inv-rank W) true) (= (vr S R W) true) (= (hmk (List.append Nat S (List.nil Nat)) W) true)
        (= (g10 (List.append Nat R gx) gk W) true) (= (ekb W) true) (= (bn a k W) true) (= (g7 W) true)
        (= (fb (List.nil Nat) F D S W) true) (= (h3 (List.append Nat S (List.nil Nat)) W) true)
        (And (= (h3 (List.append Nat S (List.nil Nat)) (nat-fold demote W R)) true) (= (fb (List.nil Nat) F (h18-acc R D) S (nat-fold demote W R)) true))))
  (induction R)
  (case [nil] (intros gx D W hR hk hv hm hg he hb h7 hfb h) (simp only [nat-fold h18-acc]) (exact (And.intro h hfb)))
  (case [cons x t ih]
    (intros gx D W hR hk hv hm hg he hb h7 hfb h)
    (simp only [tbl-all Bool.and_eq_true] at hR)
    (have hx (= (reach-mem x S) true)) (exact (And.left hR))
    (have hg1 (= (g10 (List.cons Nat x (List.append Nat t gx)) gk W) true)) (exact hg)
    (simp only [nat-fold h18-acc])
    (exact (ih gx (List.cons Nat x D) (demote W x) (And.right hR) (rk-demote W x hk) (vr-demote S t W x hx hk hv)
             (hmk-demote-x S t (List.nil Nat) W x hx (And.right hR) hk hv hm)
             (g10-demote (List.append Nat t gx) gk W x hg1) (ekb-demote W x he) (bn-demote a k W x hb)
             (g7-demote W x (And.right (h18-bn-aa a k W hb)) h7)
             (fb-add-d (List.nil Nat) F D S (demote W x) x (h18-nh-demote a k W x hb h7) (fb-demote (List.nil Nat) F D S W x hfb))
             (h18-demote-x S t (List.cons Nat x (List.append Nat t gx)) gk F D W x hx (And.right hR) hk hv hm hg1 he hfb h)))))

;; ===========================================================================
;; The pass: start (the bundle at the round's world), end (the strays' exemption is undone), norm-round
;; ===========================================================================
(a/defn fb-pick [S :- (List Nat), e :- EdgeRow] Bool (Bool.and (Bool.not (Nat.beq (:kind e) ek-dep)) (reach-mem (:debtor e) S)))
(a/theorem h18-xm-app [w :- World, S :- (List Nat)] (=> (= (h3 (List.nil Nat) w) true) (= (h3 (List.append Nat S (List.nil Nat)) w) true))
  (induction S)
  (case [nil] (intro h) (exact h))
  (case [cons x t ih] (intro h) (exact (h3-xm-cons (List.append Nat t (List.nil Nat)) x w (ih h)))))
;; at a world with h3 []: a computation id is free, and so is a non-dep edge on a computation
;; (a current member edge on a computation is a dep edge: h3-m)
(a/theorem h18-fb-init [S :- (List Nat), w :- World]
  (=> (forall [d :- Nat] (=> (= (reach-mem d S) true) (= (tbl-has comp-id d (:comps w)) true)))
      (= (h3 (List.nil Nat) w) true) (= (fb (List.nil Nat) (List.append Nat S (tbl-scan edge-id (fb-pick S) (:edges w))) (List.nil Nat) S w) true))
  (intros hS h)
  (have hs := (h3-sample _ w h))
  (have hr := (h3-rest-of _ w h))
  (have hp (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (fb-pick S e) true) (= (h3-free (List.nil Nat) w (edge-id e)) true))))
  (intros e me hp)
  (simp only [fb-pick Bool.and_eq_true] at hp)
  (have kd := (bnot-true _ (And.left hp)))
  (show (= (h3-free (List.nil Nat) w (:id e)) true))
  (apply (h3-free-by (List.nil Nat) w (:id e)))
  (intros b r mb mr ir hxo hcur hmem hxx)
  (have u := (h3-ob-use (List.nil Nat) w b r (:id e) e hr mb mr ir hxo hcur hmem hxx me (Eq.refl (:id e))))
  (have ur := (And.right u))
  (cases ur)
  (case [inl z] (simp only [reach-mem] at z) (cases z))
  (case [inr z]
    (simp only [h3-m Bool.and_eq_true] at z)
    (have z2 := (And.right z))
    (simp only [(hS (:debtor e) (And.right hp)) kd Bool.not_true Bool.false_or Bool.false_and] at z2)
    (cases z2))
  (have fr (= (tbl-all (h3-free (List.nil Nat) w) (List.append Nat S (tbl-scan edge-id (fb-pick S) (:edges w)))) true))
  (apply (all-of-mem Nat _ (List.append Nat S (tbl-scan edge-id (fb-pick S) (:edges w)))))
  (intros y my)
  (have ry := (Iff.mpr (reach-mem-iff y (List.append Nat S (tbl-scan edge-id (fb-pick S) (:edges w)))) my))
  (simp only [reach-mem-append Bool.or_eq_true] at ry)
  (cases ry)
  (case [inl y1]
    (apply (h3-free-noedge (List.nil Nat) w y hr))
    (cases q (tbl-has edge-id y (:edges w)))
    (case [false] (rfl))
    (case [true] (have z := (h3-edge-not-comp w y hs q)) (rw [(hS y y1)] at z) (cases z)))
  (case [inr y2]
    (exact (scan-prop EdgeRow edge-id (fb-pick S) (fn [v :- Nat] (= (h3-free (List.nil Nat) w v) true)) (:edges w) hp y y2)))
  (have ep (= (tbl-all (fb-e S (List.append Nat S (tbl-scan edge-id (fb-pick S) (:edges w)))) (:edges w)) true))
  (apply (all-of-mem EdgeRow _ (:edges w)))
  (intros e me)
  (cases kd (Nat.beq (:kind e) ek-dep))
  (case [true] (simp only [fb-e kd Bool.true_or]))
  (case [false]
    (cases dS (reach-mem (:debtor e) S))
    (case [false] (simp only [fb-e dS Bool.not_false Bool.true_or Bool.or_true]))
    (case [true]
      (have pk (= (fb-pick S e) true)) (simp only [fb-pick kd dS Bool.not_false Bool.and_self])
      (have im := (scan-mem EdgeRow edge-id (fb-pick S) e (:edges w) me pk))
      (have im2 (= (reach-mem (:id e) (tbl-scan edge-id (fb-pick S) (:edges w))) true)) (exact im)
      (simp only [fb-e reach-mem-append im2 Bool.or_true])))
  (have nh (= (tbl-all (fb-nh w) (List.nil Nat)) true)) (simp only [tbl-all])
  (exact (fb-intro (List.nil Nat) (List.append Nat S (tbl-scan edge-id (fb-pick S) (:edges w))) (List.nil Nat) S w hs (fb-rest-mk (List.nil Nat) (List.append Nat S (tbl-scan edge-id (fb-pick S) (:edges w))) (List.nil Nat) S w fr nh ep))))
;; the pass end: every stray has no current holder, its id is free, and the edges on it are no dep edges
;; (vr: a dep edge on a stray has a stray creditor not yet demoted) with free ids
(a/theorem h18-pass-end [S :- (List Nat), F :- (List Nat), D :- (List Nat), W :- World]
  (=> (= (vr S (List.nil Nat) W) true) (= (fb (List.nil Nat) F D S W) true)
      (forall [d :- Nat] (=> (= (reach-mem d S) true) (= (reach-mem d D) true)))
      (forall [d :- Nat] (=> (= (reach-mem d S) true) (= (reach-mem d F) true)))
      (= (h3 (List.append Nat S (List.nil Nat)) W) true) (= (h3 (List.nil Nat) W) true))
  (intros hv hfb hD hF h)
  (have hs := (h3-sample _ W h))
  (have r := (fb-rest-of (List.nil Nat) F D S W hfb))
  (have p := (vrk-parts _ _ _ _ _ (vr-rest-of _ _ W hv)))
  (apply (h3-intro (List.nil Nat) W hs))
  (apply (h16-dis (List.nil Nat) W S hs))
  (intros d hd)
  (apply Or.inr)
  (apply And.intro)
  (exact (fb-nh-of W d (all-reach-mem (fb-nh W) d D (fb-nhs (List.nil Nat) F D S W r) (hD d hd))))
  (apply And.intro)
  (exact (all-reach-mem (h3-free (List.nil Nat) W) d F (fb-fr (List.nil Nat) F D S W r) (hF d hd)))
  (intros e me ed)
  (have dS (= (reach-mem (:debtor e) S) true)) (rw [ed]) (exact hd)
  (cases kd (Nat.beq (:kind e) ek-dep))
  (case [true]
    (have db := (tbl-all-mem EdgeRow _ e (:edges W) (And.left (And.right p)) me))
    (simp only [dnb14 kd dS reach-mem Bool.not_true Bool.false_or Bool.true_or Bool.true_and] at db)
    (cases db))
  (case [false]
    (have fe := (tbl-all-mem EdgeRow _ e (:edges W) (fb-er (List.nil Nat) F D S W r) me))
    (simp only [fb-e kd dS Bool.not_true Bool.false_or] at fe)
    (apply Or.inr)
    (exact (all-reach-mem (h3-free (List.nil Nat) W) (:id e) F (fb-fr (List.nil Nat) F D S W r) fe)))
  (exact (h3-rest-of _ W h)))

(a/theorem h18-norm-round [w :- World]
  (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (hmk (List.nil Nat) w) true) (= (g10 (List.nil Nat) (List.nil Nat) w) true) (= (ekb w) true)
      (= (acts-alive w) true) (= (g7 w) true) (= (h3 (List.nil Nat) w) true) (= (h3 (List.nil Nat) (norm-round w)) true))
  (intros hk hv hm hg he haa h7 h)
  (have hs := (h3-sample _ w h))
  (have hS (forall [d :- Nat] (=> (= (reach-mem d (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) true) (= (tbl-has comp-id d (:comps w)) true))))
  (intros d hd)
  (exact (scan-prop CompRow comp-id (comp-stray (live-list w)) (fn [v :- Nat] (= (tbl-has comp-id v (:comps w)) true)) (:comps w)
           (fn [c :- CompRow, m :- (List.Mem c (:comps w)), q :- (= (comp-stray (live-list w) c) true)] (has-of-mem CompRow comp-id c (:comps w) m)) d hd))
  (have f0 := (h18-fb-init (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) w hS h))
  (have hL := (h18-xm-app w (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) h))
  (have g1 := (g10-gx-app (List.nil Nat) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) w hg))
  (have hj (= (tbl-all (job-ok (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (List.nil Nat) w) (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) true))
  (rw [jl-cancel-jobs])
  (exact (scan-all RunRow run-id (run-stray (live-list w)) (fn [x :- Nat] (ncw (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (List.nil Nat) x w))
           (:runs w) (fn [r :- RunRow, m :- (List.Mem r (:runs w)), q :- (= (run-stray (live-list w) r) true)] (stray-ncw (List.nil Nat) (List.nil Nat) w r hg m q))))
  (have g2 := (g10-run-cascade (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (List.nil Nat) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) hj g1))
  (have mL := (hmk-intro (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) w (hmk-sample (List.nil Nat) w hm)
                (hmk-rest-xm (List.nil Nat) (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) w (fn [d :- Nat, hd :- (= (reach-mem d (List.nil Nat)) true)] (rm-app-r d (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) hd)) (hmk-rest-of (List.nil Nat) w hm))))
  (have h1 := (h3-run-cascade-g (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (List.nil Nat) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) g1 mL he hL))
  (have m1 := (hmk-run-cascade (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) mL))
  (have v1 := (vr-run-cascade (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) (vr-pass-start w hv)))
  (have k1 := (rk-run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) hk))
  (have e1 := (ekb-run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) he))
  (have b1 := (bn-run-cascade (alive-cnt w) (act-cnt w) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) (bn-intro (alive-cnt w) (act-cnt w) w hs haa (Nat.le_refl _) (Nat.le_refl _))))
  (have g71 := (g7-run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) h7))
  (have f1 := (fb-run-cascade (List.nil Nat) (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan edge-id (fb-pick (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) (:edges w))) (List.nil Nat) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) f0))
  (have rm := (rm-in-scan CompRow comp-id (comp-stray (live-list w)) (:comps w)))
  (have fold := (h18-demote-fold (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan edge-id (fb-pick (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) (:edges w))) (alive-cnt w) (act-cnt w) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) (List.nil Nat) (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) rm k1 v1 m1 g2 e1 b1 g71 f1 h1))
  (have vf := (vr-fold (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) rm k1 v1))
  (have mf := (hmk-demote-fold (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) rm k1 v1 m1))
  (have m0 (= (hmk (List.nil Nat) (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)))) true))
  (apply (hmk-dis (List.nil Nat) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) mf))
  (intros d hd) (exact (Or.inr (Or.inr (hk-nmd-pass (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) d (And.left vf) mf hd))))
  (intros d hd) (exact hd)
  (have hend := (h18-pass-end (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan edge-id (fb-pick (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) (:edges w))) (h18-acc (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat)) (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) (And.left vf) (And.right fold)
                  (fn [d :- Nat, hd :- (= (reach-mem d (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) true)] (h18-acc-r d (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (List.nil Nat) hd))
                  (fn [d :- Nat, hd :- (= (reach-mem d (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) true)] (rm-app-l d (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan edge-id (fb-pick (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) (:edges w)) hd))
                  (And.left fold)))
  (simp only [norm-round norm-round-lv])
  (exact (h18-detach (List.nil Nat) (List.nil Nat) (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) m0 hend)))

(a/theorem h18-norm-loop [fuel :- (List Nat)]
  (forall [w :- World]
    (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (hmk (List.nil Nat) w) true) (= (g10 (List.nil Nat) (List.nil Nat) w) true) (= (ekb w) true)
      (= (acts-alive w) true) (= (g7 w) true) (= (h3 (List.nil Nat) w) true) (= (h3 (List.nil Nat) (norm-loop fuel w)) true)))
  (induction fuel)
  (case [nil] (intros w hk hv hm hg he haa h7 h) (simp only [norm-loop]) (exact h))
  (case [cons u f ih]
    (intros w hk hv hm hg he haa h7 h)
    (cases hn (normalized w))
    (case [true] (simp only [norm-loop hn]) (exact h))
    (case [false]
      (simp only [norm-loop hn])
      (exact (ih (norm-round w) (rk-norm-round w hk) (vr-norm-round w hk hv) (hmk-norm-round (List.nil Nat) w hk hv hm) (g10-norm-round (List.nil Nat) (List.nil Nat) w hg)
               (ekb-norm-round w he) (And.right (bn-round w (h3-sample _ w h) haa)) (g7-norm-round w haa h7)
               (h18-norm-round w hk hv hm hg he haa h7 h))))))
(a/theorem h18-normalize [w :- World]
  (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (hmk (List.nil Nat) w) true) (= (g10 (List.nil Nat) (List.nil Nat) w) true) (= (ekb w) true)
      (= (acts-alive w) true) (= (g7 w) true) (= (h3 (List.nil Nat) w) true) (= (h3 (List.nil Nat) (normalize w)) true))
  (intros hk hv hm hg he haa h7 h)
  (have p := (bn-parts _ _ _ (bn-detach (alive-cnt w) (act-cnt w) w (bn-intro _ _ w (h3-sample _ w h) haa (Nat.le_refl _) (Nat.le_refl _)))))
  (simp only [normalize])
  (exact (h18-norm-loop (norm-fuel (detach w)) (detach w) (rk-detach w hk) (vr-detach (List.nil Nat) (List.nil Nat) w hv) (hmk-detach (List.nil Nat) w hm)
           (g10-detach (List.nil Nat) (List.nil Nat) w hg) (ekb-detach w he) (And.left (And.right p)) (g7-detach w h7) (h18-detach (List.nil Nat) (List.nil Nat) w hm h))))

;; ===========================================================================
;; The filter: at a normalized world every run is kept, and a held activation's member edges are live
;; ===========================================================================
(a/theorem h18-awm-keep [K :- (=> Nat Bool), x :- Nat, i :- Nat, as :- (List ActRow)]
  (=> (= (K i) true) (= (opt-test (h3-first i) (act-with-member x as)) true)
      (= (opt-test (h3-first i) (act-with-member x (tbl-keep K act-id as))) true))
  (induction as)
  (case [nil] (intros hk h) (simp only [tbl-keep]) (exact h))
  (case [cons hd t ih]
    (intros hk h)
    (cases hm (mem-has x (:members hd)))
    (case [true]
      (simp only [act-with-member hm opt-test h3-first] at h)
      (have kh (= (K (act-id hd)) true)) (show (= (K (:id hd)) true)) (rw [(Nat.eq_of_beq_eq_true h)]) (exact hk)
      (simp only [tbl-keep kh act-with-member hm opt-test h3-first])
      (exact h))
    (case [false]
      (simp only [act-with-member hm] at h)
      (cases hkk (K (act-id hd)))
      (case [true] (simp only [tbl-keep hkk act-with-member hm]) (exact (ih hk h)))
      (case [false] (simp only [tbl-keep hkk]) (exact (ih hk h))))))
(a/theorem h18-filter-k [xm :- (List Nat), w :- World, K :- (=> Nat Bool)]
  (=> (= (tbl-keep K run-id (:runs w)) (:runs w))
      (forall [a :- ActRow, r :- RunRow, x :- Nat]
        (=> (List.Mem a (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run a)) (= (reach-mem x (act-contrib a)) true) (= (K x) true)))
      (= (h3-rest xm w) true) (= (h3-rest xm (filter-world K w)) true))
  (intros hr hx h)
  (simp only [h3-rest] at h)
  (have er (= (:runs (filter-world K w)) (:runs w))) (simp only [filter-world hr])
  (have nx (= (:next-id (filter-world K w)) (:next-id w))) (rfl)
  (have hp (forall [a :- ActRow] (=> (List.Mem a (:acts w)) (= (h3-a xm w a) true) (= (K (act-id a)) true) (= (h3-a xm (filter-world K w) a) true))))
  (intros a ma ha ka)
  (have ka2 (= (K (:id a)) true)) (exact ka)
  (simp only [h3-a Bool.and_eq_true] at ha)
  (have hq (forall [r :- RunRow] (=> (List.Mem r (:runs w)) (= (h3-rr xm w a r) true) (= (h3-rr xm (filter-world K w) a r) true))))
  (intros r mr hrr)
  (cases ib (Nat.beq (:id r) (:run a)))
  (case [false]
    (have ib2 (= (Nat.beq (:id (rk3 r)) (:run a)) false)) (exact ib)
    (simp only [h3-rr h3-r ib2 Bool.not_false Bool.true_or]))
  (case [true]
    (have ib2 (= (Nat.beq (:id (rk3 r)) (:run a)) true)) (exact ib)
    (simp only [h3-rr h3-r ib2 Bool.not_true Bool.false_or Bool.and_eq_true] at hrr)
    (have e1 (= (tbl-all (h3-e1 (rk3 r)) (:comps (filter-world K w))) true))
    (exact (tbl-all-keep-same CompRow K comp-id (h3-e1 (rk3 r)) (:comps w) (And.left (And.right hrr))))
    (have ob (= (h3-ob xm (filter-world K w) a (rk3 r)) true))
    (cases ho (reach-mem (:of (rk3 r)) xm))
    (case [true] (simp only [h3-ob ho Bool.true_or]))
    (case [false]
      (cases hc (tbl-any (h3-cur (rk3 r)) (tbl-keep K comp-id (:comps w))))
      (case [false]
        (have hc2 (= (tbl-any (h3-cur (rk3 r)) (:comps (filter-world K w))) false)) (exact hc)
        (simp only [h3-ob hc2 Bool.not_false Bool.true_or Bool.or_true]))
      (case [true]
        (have hc0 := (tbl-any-keep CompRow (h3-cur (rk3 r)) K comp-id (:comps w) hc))
        (have o := (And.right (And.right hrr)))
        (simp only [h3-ob ho hc0 Bool.not_true Bool.false_or Bool.and_eq_true] at o)
        (have cs2 (= (tbl-all (h3-cs (rk3 r)) (:comps (filter-world K w))) true))
        (exact (tbl-all-keep-same CompRow K comp-id (h3-cs (rk3 r)) (:comps w) (And.left o)))
        (have xs (= (tbl-all (h3-x xm (filter-world K w) a (rk3 r)) (act-contrib a)) true))
        (apply (all-of-mem Nat _ (act-contrib a)))
        (intros x mx)
        (have rx := (Iff.mpr (reach-mem-iff x (act-contrib a)) mx))
        (have hx0 := (all-reach-mem (h3-x xm w a (rk3 r)) x (act-contrib a) (And.right o) rx))
        (cases hxm (reach-mem x xm))
        (case [true] (simp only [h3-x hxm Bool.true_or]))
        (case [false]
          (simp only [h3-x hxm Bool.false_or Bool.and_eq_true] at hx0)
          (have kx := (hx a r x ma mr (Nat.eq_of_beq_eq_true ib) rx))
          (have he2 (= (tbl-has edge-id x (:edges (filter-world K w))) true))
          (show (= (tbl-has edge-id x (tbl-keep K edge-id (:edges w))) true))
          (rw [tbl-has-keep]) (simp only [kx (And.left hx0) Bool.and_self])
          (have pe (forall [e :- EdgeRow] (=> (= (h3-eok xm w a (rk3 r) x e) true) (= (K (edge-id e)) true) (= (h3-eok xm (filter-world K w) a (rk3 r) x e) true))))
          (intros e he0 ke)
          (cases ie (Nat.beq (:id e) x))
          (case [false] (simp only [h3-eok ie Bool.not_false Bool.true_or]))
          (case [true]
            (simp only [h3-eok ie Bool.not_true Bool.false_or Bool.and_eq_true] at he0)
            (have s0 := (And.left he0))
            (simp only [h3-s Bool.and_eq_true] at s0)
            (have aw2 (= (opt-test (h3-first (:id a)) (act-with-member (:id e) (:acts (filter-world K w)))) true))
            (exact (h18-awm-keep K (:id e) (:id a) (:acts w) ka2 (And.right (And.right (And.right s0)))))
            (have s1 (= (h3-s (:acts (filter-world K w)) a (rk3 r) e) true))
            (simp only [h3-s (And.left s0) (And.left (And.right s0)) (And.left (And.right (And.right s0))) aw2 Bool.and_self])
            (have m1 (= (Bool.or (reach-mem (:debtor e) xm) (h3-m (:comps (filter-world K w)) (:tasks (filter-world K w)) (:runs (filter-world K w)) e)) true))
            (cases hd (reach-mem (:debtor e) xm))
            (case [true] (simp only [hd Bool.true_or]))
            (case [false]
              (have m0 := (And.right he0))
              (simp only [hd Bool.false_or h3-m Bool.and_eq_true] at m0)
              (have t1 (= (tbl-all (h3-tk (:runs (filter-world K w)) (:debtor e)) (:tasks (filter-world K w))) true))
              (rw [er]) (exact (tbl-all-keep-same TaskRow K task-id (h3-tk (:runs w) (:debtor e)) (:tasks w) (And.left m0)))
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
              (simp only [hd Bool.false_or h3-m t1 c1 Bool.and_self]))
            (simp only [h3-eok ie Bool.not_true Bool.false_or s1 m1 Bool.and_self]))
          (have ee2 (= (tbl-all (h3-eok xm (filter-world K w) a (rk3 r) x) (:edges (filter-world K w))) true))
          (exact (tbl-all-keep EdgeRow K edge-id (h3-eok xm w a (rk3 r) x) (h3-eok xm (filter-world K w) a (rk3 r) x) pe (:edges w) (And.right hx0)))
          (simp only [h3-x hxm Bool.false_or he2 ee2 Bool.and_self]))
        (simp only [h3-ob ho Bool.false_or cs2 xs Bool.and_self Bool.or_true])))
    (simp only [h3-rr h3-r ib2 Bool.not_true Bool.false_or nx (And.left hrr) e1 ob Bool.and_self]))
  (have rr (= (tbl-all (h3-rr xm (filter-world K w) a) (:runs (filter-world K w))) true))
  (rw [er]) (exact (tbl-all-mem-mono RunRow (h3-rr xm w a) (h3-rr xm (filter-world K w) a) (:runs w) hq (And.right ha)))
  (simp only [h3-a nx (And.left ha) rr Bool.and_self])
  (simp only [h3-rest])
  (exact (tbl-all-keep-mem ActRow K act-id (h3-a xm w) (h3-a xm (filter-world K w)) (:acts w) hp h)))
(a/theorem h18-filter [xm :- (List Nat), W :- World]
  (=> (= (normalized W) true) (= (gr0 W) true) (= (acts-alive W) true) (= (filter-safe W) true) (= (h3 xm W) true)
      (= (h3 xm (rule-r-filter W)) true))
  (intros hn hg haa hf h)
  (have hs := (h3-sample xm W h))
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
  (exact (h3-intro xm _ (inv-filter-world W (keep-fn W) hs hf) (h18-filter-k xm W (keep-fn W) kr hx (h3-rest-of xm W h)))))

;; ===========================================================================
;; Rule R
;; ===========================================================================
(a/theorem h18-rule-r-round [w :- World]
  (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (hmk (List.nil Nat) w) true) (= (g10 (List.nil Nat) (List.nil Nat) w) true) (= (ekb w) true)
      (= (acts-alive w) true) (= (g7 w) true) (= (gr0 w) true) (= (h3 (List.nil Nat) w) true) (= (filter-safe (normalize w)) true) (= (h3 (List.nil Nat) (rule-r-round w)) true))
  (intros hk hv hm hg he haa h7 h0 h hf)
  (have hs := (h3-sample _ w h))
  (simp only [rule-r-round])
  (exact (h18-filter (List.nil Nat) (normalize w) (normalized-ok w hs haa) (gr0-normalize-aa w haa h0) (acts-alive-normalize w hs haa) hf
           (h18-normalize w hk hv hm hg he haa h7 h))))
(a/theorem h18-rr-loop [fuel :- (List Nat)]
  (forall [w :- World]
    (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (hmk (List.nil Nat) w) true) (= (g10 (List.nil Nat) (List.nil Nat) w) true) (= (ekb w) true)
      (= (acts-alive w) true) (= (g7 w) true) (= (gr0 w) true) (= (h3 (List.nil Nat) w) true) (= (rr-safe fuel w) true) (= (h3 (List.nil Nat) (rr-loop fuel (rule-r-round w))) true)))
  (induction fuel)
  (case [nil] (intros w hk hv hm hg he haa h7 h0 h hs) (simp only [rr-safe] at hs) (simp only [rr-loop])
    (exact (h18-rule-r-round w hk hv hm hg he haa h7 h0 h hs)))
  (case [cons x f ih]
    (intros w hk hv hm hg he haa h7 h0 h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (h18-rule-r-round w hk hv hm hg he haa h7 h0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho])
      (exact (ih (rule-r-round w) (rk-rule-r-round w hk (And.left hs)) (vr-rule-r-round w hk hv (And.left hs))
               (hmk-rule-r-round (List.nil Nat) w hk hv hm (And.left hs)) (g10-rule-r-round (List.nil Nat) (List.nil Nat) w hg (And.left hs))
               (ekb-rule-r-round w he (And.left hs)) (acts-alive-round w (h3-sample _ w h) haa) (g7-rule-r-round w haa h7 (And.left hs))
               (gr0-rule-r-round w haa h0 (And.left hs)) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))
(a/theorem h18-rule-r [w :- World]
  (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (hmk (List.nil Nat) w) true) (= (g10 (List.nil Nat) (List.nil Nat) w) true) (= (ekb w) true)
      (= (acts-alive w) true) (= (g7 w) true) (= (gr0 w) true) (= (h3 (List.nil Nat) w) true) (= (rule-r-safe w) true) (= (h3 (List.nil Nat) (rule-r w)) true))
  (intros hk hv hm hg he haa h7 h0 h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r])
  (exact (h18-rr-loop (rr-fuel w) w hk hv hm hg he haa h7 h0 h hs)))

;; ===========================================================================
;; The step: p3m = p3la && h3 [] is a step invariant; L5 safety with no honest hypothesis
;; ===========================================================================
(a/theorem step-h3 [w :- World, it :- Item]
  (=> (= (p3la w) true) (= (h3 (List.nil Nat) w) true) (= (h3 (List.nil Nat) (:world (world-step w it))) true))
  (intros hp h)
  (have pl := (p3l-parts w (p3la-p3l w hp)))
  (have pk := (p3k-parts w (And.left pl)))
  (have pj := (p3j-parts w (And.left pk)))
  (have pc := (p3i-ctx w (And.left pj)))
  (have pb := (p3b-parts w (And.left pc)))
  (have h0 := (And.right (p3h-parts w (And.left (p3i-parts w (And.left pj))))))
  (have h7 := (p3i-g7 w (And.left pj)))
  (have hga := (And.left pb))
  (have hk := (And.left (And.right pb)))
  (have hv := (And.right pk))
  (simp only [v14] at hv)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true]
    (have e2 := (step-accepted w it ha)) (rw [e2])
    (have r0 := (raw-vq (List.nil Nat) (List.nil Nat) false w it hv))
    (exact (h18-rule-r (:world (raw w it)) (raw-rk w it hk)
             (vr-of-vq (List.nil Nat) false _ r0 (dep-active-of-g7 _ (raw-g7 w it h7)))
             (raw-hmk _ w it (And.right pj) h7 hga (And.right pc) (And.right pl))
             (raw-g10r w it (And.right pc)) (raw-ekb w it (p3la-ekb w hp)) (raw-acts-alive w it hga) (raw-g7 w it h7)
             (raw-gr0 w it hga h0) (h17-raw-h3 (List.nil Nat) w it hp h) (step-rule-r-safe w it (And.left pc))))))
(a/defn p3m [w :- World] Bool (Bool.and (p3la w) (h3 (List.nil Nat) w)))
(a/theorem p3m-parts [w :- World] (=> (= (p3m w) true) (And (= (p3la w) true) (= (h3 (List.nil Nat) w) true)))
  (intro h) (simp only [p3m Bool.and_eq_true] at h) (exact h))
(a/theorem p3m-empty [] (= (p3m empty-world) true) (rfl))
(a/theorem step-p3m [w :- World, it :- Item] (=> (= (p3m w) true) (= (p3m (:world (world-step w it))) true))
  (intro h)
  (have p := (p3m-parts w h))
  (have a1 := (step-p3la w it (And.left p)))
  (have a2 := (step-h3 w it (And.left p) (And.right p)))
  (simp only [p3m a1 a2 Bool.and_self]))
;; Theorem (h-mem2, P11 second half): the memory bundle holds after every step
(a/theorem step-h3-total [w :- World, it :- Item] (=> (= (p3m w) true) (= (h3 (List.nil Nat) (:world (world-step w it))) true))
  (intro h) (exact (And.right (p3m-parts _ (step-p3m w it h)))))
;; Theorem (L5 safety, unconditional): in a p3m world a quiescent waiting computation has a blocked dependency,
;; an eligible one or an unblocked task -- no honest hypothesis (h-mark and h-mem2 are invariants)
(a/theorem l5-safety-total [w :- World, c0 :- Nat, c :- CompRow]
  (=> (= (p3m w) true) (= (quiescent w) true) (= (comp-find w c0) (Option.some CompRow c)) (= (comp-waiting c) true)
      (none-blocked w c0) (none-eligible w c0) (tasks-blocked w c0) False)
  (intros h hq hf hw nb ne tb)
  (have p := (p3m-parts w h))
  (have hl := (p3la-p3l w (And.left p)))
  (have pj := (p3j-parts w (And.left (p3k-parts w (And.left (p3l-parts w hl))))))
  (have pc := (p3i-ctx w (And.left pj)))
  (have h3c (= (p3c w) true)) (simp only [p3c (And.left pc) (And.right pc) Bool.and_self])
  (exact (h3-l5-safety w c0 c h3c (And.right pj) (And.right p) hq (p3l-h-mark w hl) hf hw nb ne tb)))
;; the literal h-mem2 of l5.clj, after every step
(a/theorem step-h-mem2-total [w :- World, it :- Item] (=> (= (p3m w) true) (= (h-mem2 (:world (world-step w it))) true))
  (intro h)
  (have p := (p3m-parts _ (step-p3m w it h)))
  (have pj := (p3j-parts _ (And.left (p3k-parts _ (And.left (p3l-parts _ (p3la-p3l _ (And.left p))))))))
  (exact (h3-h-mem2 _ (And.right p) (And.right pj))))
