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
                      (apply list 'fb-run-upd-m 'zl 'zf 'zd 'zs w x f hid '(fn [q :- RunRow] (Eq.refl (rk3 q))) more)))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! FB n fb-patch))
