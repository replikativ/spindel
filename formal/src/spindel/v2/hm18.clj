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
      (= (fb (List.append Nat S (List.nil Nat)) F D S W) true) (= (tbl-has comp-id x (:comps W)) true)
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
      (have fe := (tbl-all-mem EdgeRow _ e (:edges W) (fb-er (List.append Nat S (List.nil Nat)) F D S W (fb-rest-of (List.append Nat S (List.nil Nat)) F D S W hfb)) me))
      (simp only [fb-e kd dS Bool.not_true Bool.false_or] at fe)
      (exact (all-reach-mem (h3-free (List.append Nat S (List.nil Nat)) W) (:id e) F (fb-fr (List.append Nat S (List.nil Nat)) F D S W (fb-rest-of (List.append Nat S (List.nil Nat)) F D S W hfb)) fe)))
    (case [false]
      (simp only [edge-avoids hd Bool.not_false Bool.and_true] at ha)
      (have hc := (bnot-false _ ha))
      (have hcc (= (tbl-has comp-id (:creditor e) (:comps W)) true)) (rw [(Nat.eq_of_beq_eq_true hc)]) (exact hcx)
      (exact (h18-free-wait-comp (List.append Nat S (List.nil Nat)) W e hs hr me kd hcc)))))

(a/theorem h18-demote-x [S :- (List Nat), R :- (List Nat), gx :- (List Nat), gk :- (List Nat), F :- (List Nat), D :- (List Nat), W :- World, x :- Nat]
  (=> (= (reach-mem x S) true) (= (tbl-all (rm-in S) R) true) (= (inv-rank W) true) (= (vr S (List.cons Nat x R) W) true)
      (= (hmk (List.append Nat S (List.nil Nat)) W) true) (= (g10 gx gk W) true) (= (ekb W) true) (= (fb (List.append Nat S (List.nil Nat)) F D S W) true)
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
      (have f1 := (fb-run-cascade (List.append Nat S (List.nil Nat)) F D S W (cancel-jobs (demote-cancels W c)) hfb))
      (have h2 (= (h3 (List.append Nat S (List.nil Nat)) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c))) true))
      (cases hb (demote-cur W c))
      (case [false] (simp only [demote-epoch]) (exact h1))
      (case [true] (simp only [demote-epoch])
        (exact (h18-comp-upd-in (List.append Nat S (List.nil Nat)) (run-cascade W (cancel-jobs (demote-cancels W c))) x comp-inc-epoch (fn [q :- CompRow] (Eq.refl (comp-id q))) (fn [q :- CompRow] (Eq.refl (:pending q)))
                 comp-inc-epoch-h3ep hX h1)))
      (have m2 := (hmk-demote-epoch (List.append Nat S (List.nil Nat)) (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c) m1))
      (have v2 := (vr-demote-epoch S (List.cons Nat x R) (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c) v1))
      (have f2 := (fb-demote-epoch (List.append Nat S (List.nil Nat)) F D S (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c) f1))
      (have dk (= (tbl-all (hk-dok (List.append Nat S (List.nil Nat)) (:comps (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c))) (not-dep-of x)) (:edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)))) true))
      (apply (all-of-mem EdgeRow _ (:edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c))))) (intros e me) (exact (hk-dok-own _ _ x e hX))
      (have h3x := (h3-drop-edges (List.append Nat S (List.nil Nat)) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) dk (h18-fr-dep (List.append Nat S (List.nil Nat)) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) x (h3-rest-of _ _ h2) hX) h2))
      (have m3 := (hmk-drop-edges (List.append Nat S (List.nil Nat)) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) dk m2))
      (have v3 := (vr-drop-r S R (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x (ncd-drop (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) x) (vr-drop-edges S (List.cons Nat x R) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) v2)))
      (have f3 := (fb-drop-edges (List.append Nat S (List.nil Nat)) F D S (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) f2))
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
