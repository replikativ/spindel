(ns spindel.v2.hm14
  "T11 dispatch keeps the h-mem2 bundle `h3` (P11): through cancel-pred, the cut, the consumed entry edge,
  the new run and post; before finish/Rule R. Contracts: notes/hm14-contracts.edn."
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
            [spindel.v2.hm13 :refer :all]))


;; ---- the new run: a fresh run row, a fresh scope row, C.run set

(a/theorem h14-add-run-scope-h3 [xm :- (List Nat), w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (h3 xm w) true) (= (h3 xm (add-run-scope w of epoch parent ei)) true))
  (intro h)
  (simp only [add-run-scope])
  (have h1 (= (h3 xm (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))) true))
  (exact (hm3-run-ins-fresh xm w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) (rfl) h))
  (have he (= (scope-id (new-scope-row (+ (:next-id w) 1) parent))
              (:next-id (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei))))))
  (rfl)
  (exact (hm3-scope-ins-fresh xm (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))
           (new-scope-row (+ (:next-id w) 1) parent) he h1)))

(a/theorem h14-new-run-of-h3 [xm :- (List Nat), w :- World, c :- CompRow, ei :- Nat]
  (=> (= (h3 xm w) true) (= (h3 xm (new-run-of w c ei)) true))
  (intro h)
  (simp only [new-run-of])
  (exact (h3-comp-upd-m xm _ (:id c) (comp-set-run (:next-id w)) (comp-set-run-id (:next-id w))
           (comp-set-run-pending (:next-id w))
           (fn [q :- CompRow] (Nat.le_refl (:epoch q)))
           (fn [q :- CompRow, hq :- (= (hk-wt q) true)] hq)
           (fn [q :- CompRow, hq :- (= (Nat.blt (:done-epoch q) (:epoch q)) true)] hq)
           (h14-add-run-scope-h3 xm w (:id c) (:epoch c) 0 ei h))))

;; ---- the entry edge

(a/theorem h14-entry-edge-facts [w :- World, cid :- Nat, e :- EdgeRow]
  (=> (= (entry-edge w cid) (Option.some EdgeRow e))
      (And (List.Mem e (:edges w)) (And (= (:kind e) ek-dep) (And (= (:creditor e) cid) (= (:phase e) ph-fired)))))
  (intro he)
  (have m := (entry-mem w cid e he))
  (simp only [entry-edge] at he)
  (have r := (earliest-mem _ (Option.none EdgeRow) e he))
  (cases r)
  (case [inl h1] (cases h1))
  (case [inr h2]
    (have q := (And.right (mem-filter14 EdgeRow (fired-dep-of cid) e (:edges w) h2)))
    (simp only [fired-dep-of dep-of Bool.and_eq_true] at q)
    (exact (And.intro m (And.intro (Nat.eq_of_beq_eq_true (And.left (And.left q)))
             (And.intro (Nat.eq_of_beq_eq_true (And.right (And.left q))) (Nat.eq_of_beq_eq_true (And.right q))))))))

;; ---- cancel-pred: the predecessor's cancel cascade

(a/theorem h14-cancel-pred-h3 [xm :- (List Nat), w :- World, c :- CompRow]
  (=> (= (p3la w) true) (= (h3 xm w) true) (= (h3 xm (cancel-pred w c)) true))
  (intros hp h)
  (have g := (p3la-g10r w hp)) (simp only [g10r] at g)
  (cases hr (run-find w (:run c)))
  (case [none] (simp only [cancel-pred hr]) (exact h))
  (case [some r]
    (cases ha (run-alive r))
    (case [false] (simp only [cancel-pred hr ha]) (exact h))
    (case [true]
      (simp only [cancel-pred hr ha])
      (exact (h3-run-cascade-g xm (List.nil Nat) (List.nil Nat) (List.nil Nat) w _ g (p3la-hmk w hp) (p3la-ekb w hp) h)))))

;; ---- the consumed entry edge: removed on a final debtor (free, and its creditor is safe), re-armed otherwise

(a/theorem h14-consume-entry-h3 [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (hmk (List.nil Nat) w) true) (= (kx-rest (:id e) (:debtor e) w) true) (= (h3-free xm w (:id e)) true)
      (= (h3 xm w) true) (= (h3 xm (consume-entry w e)) true))
  (intros hk k hfr h)
  (cases hf (deb-final w (:debtor e)))
  (case [false]
    (cases hr (Nat.beq (:cont e) cont-restart))
    (case [false]
      (simp only [consume-entry hr hf])
      (have p6 (forall [q :- EdgeRow] (=> (= (Nat.beq (:phase q) ph-armed) true)
                 (= (Nat.beq (:phase (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)) q)) ph-armed) true))))
      (intros q hq) (rfl)
      (exact (h3-edge-upd-m xm w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
               (edge-rearm-edge-id _ _) (edge-rearm-kind _ _) (edge-rearm-creditor _ _) (edge-rearm-debtor _ _) (edge-rearm-marked _ _)
               p6 h)))
    (case [true]
      (simp only [consume-entry hr hf])
      (have p1 (forall [q :- EdgeRow] (= (:kind (edge-set-phase ph-armed q)) (:kind q)))) (intro q) (rfl)
      (have p2 (forall [q :- EdgeRow] (= (:creditor (edge-set-phase ph-armed q)) (:creditor q)))) (intro q) (rfl)
      (have p3 (forall [q :- EdgeRow] (= (:debtor (edge-set-phase ph-armed q)) (:debtor q)))) (intro q) (rfl)
      (have p4 (forall [q :- EdgeRow] (= (:marked (edge-set-phase ph-armed q)) (:marked q)))) (intro q) (rfl)
      (have p5 (forall [q :- EdgeRow] (=> (= (Nat.beq (:phase q) ph-armed) true)
                                          (= (Nat.beq (:phase (edge-set-phase ph-armed q)) ph-armed) true))))
      (intros q hq) (rfl)
      (exact (h3-edge-upd-m xm w (:id e) (edge-set-phase ph-armed) (edge-set-phase-edge-id ph-armed) p1 p2 p3 p4 p5 h))))
  (case [true]
    (have u0 := (hk-u-kx (List.nil Nat) w e hk k hf))
    (have u (forall [e2 :- EdgeRow] (=> (= (edge-find w (:id e)) (Option.some EdgeRow e2)) (= (:marked e2) true)
                                        (= (hk-safe xm (:comps w) (:creditor e2)) true))))
    (intros e2 hf2 hm2)
    (have s := (u0 e2 hf2 hm2))
    (simp only [hk-safe reach-mem Bool.false_or] at s)
    (simp only [hk-safe s Bool.or_true])
    (simp only [consume-entry hf])
    (exact (h3-remove-edge xm w (:id e) u hfr h))))

;; ---- no activation holds a run of C once C has no alive run

(a/theorem h14-acts-alive-no-holder [w :- World, cid :- Nat]
  (=> (= (acts-alive w) true) (= (tbl-all (not-alive-of cid) (:runs w)) true)
      (forall [a :- ActRow, r :- RunRow]
        (=> (List.Mem a (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run a)) (Not (= (:of r) cid)))))
  (intros ha hn a r ma mr hid hof)
  (simp only [acts-alive] at ha)
  (have x := (tbl-all-mem ActRow (act-run-ok (:runs w)) a (:acts w) ha ma))
  (simp only [act-run-ok] at x)
  (have y := (tbl-all-mem RunRow (run-ok-for (:run a)) r (:runs w) x mr))
  (have z := (tbl-all-mem RunRow (not-alive-of cid) r (:runs w) hn mr))
  (have i2 (= (Nat.beq (:id r) (:run a)) true)) (simp only [Nat.beq_eq]) (exact hid)
  (have j2 (= (Nat.beq (:of r) cid) true)) (simp only [Nat.beq_eq]) (exact hof)
  (simp only [run-ok-for i2 Bool.not_true Bool.false_or] at y)
  (simp only [not-alive-of y j2 Bool.not_true Bool.or_false] at z)
  (cases z))

(a/theorem h14-cancel-pred-no-holder [w :- World, c :- CompRow]
  (=> (= (p3la w) true) (List.Mem c (:comps w))
      (forall [a :- ActRow, r :- RunRow]
        (=> (List.Mem a (:acts (cancel-pred w c))) (List.Mem r (:runs (cancel-pred w c))) (= (:id r) (:run a))
            (Not (= (:of r) (:id c))))))
  (intros hp mc)
  (exact (h14-acts-alive-no-holder (cancel-pred w c) (:id c)
           (aha-acts-alive _ (aha-cancel-pred w c (p3la-aha w hp)))
           (ar-cancel-pred-none w c (aha-acts-alive w (p3la-aha w hp)) (p3la-ar w hp) mc))))

;; ---- a dep edge of C is free while no activation holds a run of C (a member dep edge's creditor is the run's `of`)

(a/theorem h14-free-dep-no-holder [xm :- (List Nat), w :- World, cid :- Nat, e :- EdgeRow]
  (=> (= (h3 xm w) true)
      (forall [a :- ActRow, r :- RunRow] (=> (List.Mem a (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run a)) (Not (= (:of r) cid))))
      (List.Mem e (:edges w)) (= (:kind e) ek-dep) (= (:creditor e) cid)
      (= (h3-free xm w (:id e)) true))
  (intros h hn m hk hc)
  (apply (h3-free-by xm w (:id e)))
  (intros b r mb mr hid hx hcur hmem hnx)
  (have o := (h3-ob-use xm w b r (:id e) e (h3-rest-of xm w h) mb mr hid hx hcur hmem hnx m (rfl)))
  (have s := (And.left o))
  (simp only [h3-s Bool.and_eq_true] at s)
  (have k2 (= (Nat.beq (:kind e) ek-dep) true)) (simp only [Nat.beq_eq]) (exact hk)
  (have s2 := (And.left (And.right s)))
  (simp only [k2 Bool.not_true Bool.false_or] at s2)
  (have q := (Nat.eq_of_beq_eq_true s2))
  (exact (hn b r mb mr hid (Eq.trans (Eq.symm q) hc))))

;; ---- the cut: every dropped edge is a dep edge of C, so free and droppable; C's row keeps epoch, pending and waiting

(a/theorem h14-cut-suffix-h3 [xm :- (List Nat), w :- World, cid :- Nat, has :- Bool, cut :- Nat, entry-id :- Nat]
  (=> (= (h3 xm w) true) (= (tbl-all (hk-sif cid) (:comps w)) true)
      (forall [a :- ActRow, r :- RunRow] (=> (List.Mem a (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run a)) (Not (= (:of r) cid))))
      (And (= (h3 xm (cut-suffix w cid has cut entry-id)) true)
           (forall [a :- ActRow, r :- RunRow]
             (=> (List.Mem a (:acts (cut-suffix w cid has cut entry-id))) (List.Mem r (:runs (cut-suffix w cid has cut entry-id)))
                 (= (:id r) (:run a)) (Not (= (:of r) cid))))))
  (intros h hs hn)
  (constructor)
  (have p := (all-of-mem EdgeRow (hk-dok xm (:comps w) (keep-prefix cid has entry-id)) (:edges w)
               (fn [r :- EdgeRow, m :- (List.Mem r (:edges w))] (hk-dok-cut xm (:comps w) cid has entry-id r hs))))
  (have f (forall [e2 :- EdgeRow] (=> (List.Mem e2 (:edges w)) (= (keep-prefix cid has entry-id e2) false)
                                      (= (h3-free xm w (:id e2)) true))))
  (intros e2 m2 hp2)
  (simp only [keep-prefix] at hp2)
  (have s1 := (bnot-false _ hp2))
  (simp only [suffix-edge dep-of Bool.and_eq_true] at s1)
  (exact (h14-free-dep-no-holder xm w cid e2 h hn m2 (Nat.eq_of_beq_eq_true (And.left (And.left s1)))
           (Nat.eq_of_beq_eq_true (And.right (And.left s1)))))
  (have h1 := (h3-drop-edges xm w (keep-prefix cid has entry-id) p f h))
  (simp only [cut-suffix])
  (exact (h3-comp-upd-m xm (drop-edges w (keep-prefix cid has entry-id)) cid
           (comp-cut-row has cut (bases-of (tbl-filter (suffix-edge cid has entry-id) (:edges w))))
           (comp-cut-row-id has cut _) (comp-cut-row-pending has cut _)
           (fn [q :- CompRow] (Nat.le_refl (:epoch q)))
           (fn [q :- CompRow, hq :- (= (hk-wt q) true)] hq)
           (fn [q :- CompRow, hq :- (= (Nat.blt (:done-epoch q) (:epoch q)) true)] hq)
           h1))
  (have ea (= (:acts (cut-suffix w cid has cut entry-id)) (:acts w))) (rfl)
  (intros a r ma mr)
  (rw [ea] at ma)
  (rw [(ar-runs-cut w cid has cut entry-id)] at mr)
  (exact (hn a r ma mr)))

;; ===========================================================================
;; The entry edge keeps kind and creditor through cancel-pred and the cut
;; ===========================================================================

(a/defn kc-at [kxy :- Nat, kck :- Nat, kcc :- Nat, e :- EdgeRow] Bool (Bool.or (Bool.not (Nat.beq (:id e) kxy)) (Bool.and (Nat.beq (:kind e) kck) (Nat.beq (:creditor e) kcc))))
(a/defn kc-rest [kxy :- Nat, kck :- Nat, kcc :- Nat, w :- World] Bool (Bool.and (Nat.blt kxy (:next-id w)) (tbl-all (kc-at kxy kck kcc) (:edges w))))
(a/defn kc [kxy :- Nat, kck :- Nat, kcc :- Nat, w :- World] Bool (Bool.and (inv-sample w) (kc-rest kxy kck kcc w)))
(a/theorem kc-sample [kxy :- Nat, kck :- Nat, kcc :- Nat, w :- World] (=> (= (kc kxy kck kcc w) true) (= (inv-sample w) true))
  (intro h) (simp only [kc Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem kc-rest-of [kxy :- Nat, kck :- Nat, kcc :- Nat, w :- World] (=> (= (kc kxy kck kcc w) true) (= (kc-rest kxy kck kcc w) true))
  (intro h) (simp only [kc Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem kc-intro [kxy :- Nat, kck :- Nat, kcc :- Nat, w :- World] (=> (= (inv-sample w) true) (= (kc-rest kxy kck kcc w) true) (= (kc kxy kck kcc w) true))
  (intros h1 h2) (simp only [kc h1 h2 Bool.and_self]))
(a/theorem kc-parts [kxy :- Nat, kck :- Nat, kcc :- Nat, w :- World]
  (=> (= (kc kxy kck kcc w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (kc-sample kxy kck kcc w h))))
(a/theorem kc-rest-mk [kxy :- Nat, kck :- Nat, kcc :- Nat, w :- World, w2 :- World]
  (=> (<= (:next-id w) (:next-id w2)) (=> (= (tbl-all (kc-at kxy kck kcc) (:edges w)) true) (= (tbl-all (kc-at kxy kck kcc) (:edges w2)) true))
      (= (kc-rest kxy kck kcc w) true) (= (kc-rest kxy kck kcc w2) true))
  (intros hn he h)
  (simp only [kc-rest Bool.and_eq_true Nat.blt_eq] at h)
  (have l (= (Nat.blt kxy (:next-id w2)) true)) (simp only [Nat.blt_eq]) (omega)
  (simp only [kc-rest l (he (And.right h)) Bool.and_self]))

(a/theorem kc-at-f [kxy :- Nat, kck :- Nat, kcc :- Nat, f :- (=> EdgeRow EdgeRow), hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                     hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                     hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))), e :- EdgeRow]
  (=> (= (kc-at kxy kck kcc e) true) (= (kc-at kxy kck kcc (f e)) true))
  (intro h) (have e1 (= (:id (f e)) (:id e))) (exact (hid e)) (simp only [kc-at e1 (hk e) (hc e)]) (simp only [kc-at] at h) (exact h))
(a/theorem kc-at-marked [kxy :- Nat, kck :- Nat, kcc :- Nat, b :- Bool, e :- EdgeRow]
  (=> (= (kc-at kxy kck kcc e) true) (= (kc-at kxy kck kcc (edge-set-marked b e)) true))
  (intro h) (simp only [kc-at edge-set-marked] at h) (simp only [kc-at edge-set-marked]) (exact h))

(a/theorem kc-at-new [kxy :- Nat, kck :- Nat, kcc :- Nat, w :- World, e :- EdgeRow]
  (=> (= (kc-rest kxy kck kcc w) true) (= (kc-at kxy kck kcc (edge-set-marked false (edge-set-id (:next-id w) e))) true))
  (intro h)
  (simp only [kc-rest Bool.and_eq_true Nat.blt_eq] at h)
  (have ne (= (Nat.beq (:next-id w) kxy) false))
  (cases hb (Nat.beq (:next-id w) kxy))
  (case [false] (rfl))
  (case [true] (have eq (= (:next-id w) kxy)) (exact (Nat.eq_of_beq_eq_true hb)) (have l := (And.left h)) (omega))
  (simp only [kc-at edge-set-marked edge-set-id ne Bool.not_false Bool.true_or]))





(def KC (mk-bundle 'kc '[kxy :- Nat, kck :- Nat, kcc :- Nat] "kc-" {}))
(swap! (:renames KC) assoc 'inv-parts 'kc-parts)
(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-set-pins
            inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-task-upd inv-run-upd inv-run-del inv-comp-upd
            inv-comp-del-unref]]
  (prim! KC o nil))
(doseq [[o w2] '[[inv-source-ins-fresh (bump (source-ins w r))] [inv-resource-ins-fresh (bump (resource-ins w r))]
                 [inv-scope-ins-fresh (bump (scope-ins w r))] [inv-act-ins-fresh (bump (act-ins w r))]
                 [inv-task-ins-fresh (bump (task-ins w r))] [inv-comp-ins-fresh (bump (comp-ins w r))]
                 [inv-run-ins-fresh (bump (run-ins w r))] [inv-bump (bump w)]]]
  (prim! KC o (list 'kc-rest-mk 'kxy 'kck 'kcc 'w w2 '(Nat.le_succ _) '(fn [h1 :- (= (tbl-all (kc-at kxy kck kcc) (:edges w)) true)] h1) 'R)))
(prim! KC 'inv-edge-upd
  '(kc-rest-mk kxy kck kcc w (edge-upd w x f) (Nat.le_refl _)
     (fn [h1 :- (= (tbl-all (kc-at kxy kck kcc) (:edges w)) true)]
       (tbl-all-upd EdgeRow edge-id x f (kc-at kxy kck kcc) (kc-at kxy kck kcc)
         (fn [e :- EdgeRow, he :- (= (kc-at kxy kck kcc e) true), hx :- (= (Nat.beq (edge-id e) x) true)] (kc-at-f kxy kck kcc f hid hk hc e he))
         (fn [e :- EdgeRow, he :- (= (kc-at kxy kck kcc e) true), hx :- (= (Nat.beq (edge-id e) x) false)] he) (:edges w) h1))
     R))
(prim! KC 'inv-remove-edge '(kc-rest-mk kxy kck kcc w (remove-edge w x) (Nat.le_of_eq (Eq.symm (next-remove-edge w x))) (fn [h1 :- (= (tbl-all (kc-at kxy kck kcc) (:edges w)) true)] (ep-remove-edge (kc-at kxy kck kcc) w x h1)) R))
(prim! KC 'mark-edge-inv-sample '(kc-rest-mk kxy kck kcc w (mark-edge w x) (Nat.le_of_eq (Eq.symm (next-mark-edge w x))) (fn [h1 :- (= (tbl-all (kc-at kxy kck kcc) (:edges w)) true)] (ep-mark-edge (kc-at kxy kck kcc) (kc-at-marked kxy kck kcc true) w x h1)) R))
(prim! KC 'unmark-edge-inv-sample '(kc-rest-mk kxy kck kcc w (unmark-edge w x) (Nat.le_of_eq (Eq.symm (next-unmark-edge w x))) (fn [h1 :- (= (tbl-all (kc-at kxy kck kcc) (:edges w)) true)] (ep-unmark-edge (kc-at kxy kck kcc) (kc-at-marked kxy kck kcc false) w x h1)) R))
(prim! KC 'inv-drop-cred '(kc-rest-mk kxy kck kcc w (drop-cred-edges w a) (Nat.le_refl _) (fn [h1 :- (= (tbl-all (kc-at kxy kck kcc) (:edges w)) true)] (ep-filter (kc-at kxy kck kcc) (cred-ne a) (:edges w) h1)) R))
(prim! KC 'inv-drop-act '(kc-rest-mk kxy kck kcc w (drop-act w a) (Nat.le_refl _) (fn [h1 :- (= (tbl-all (kc-at kxy kck kcc) (:edges w)) true)] (ep-filter (kc-at kxy kck kcc) (cred-ne a) (:edges w) h1)) R))
(prim! KC 'inv-drop-edges '(kc-rest-mk kxy kck kcc w (drop-edges w p) (Nat.le_refl _) (fn [h1 :- (= (tbl-all (kc-at kxy kck kcc) (:edges w)) true)] (ep-filter (kc-at kxy kck kcc) p (:edges w) h1)) R))
(a/theorem kc-rest-ins [kxy :- Nat, kck :- Nat, kcc :- Nat, w :- World, e :- EdgeRow]
  (=> (= (kc-rest kxy kck kcc w) true) (= (kc-rest kxy kck kcc (insert-edge-fresh w e)) true))
  (intro h)
  (have n1 := (kc-at-new kxy kck kcc w e h))
  (simp only [kc-rest Bool.and_eq_true Nat.blt_eq] at h)
  (have l (= (Nat.blt kxy (+ (:next-id w) 1)) true)) (simp only [Nat.blt_eq]) (omega)
  (simp only [kc-rest insert-edge-fresh bump insert-edge edge-ins set-next-id set-edges tbl-ins tbl-all n1 (And.right h) l Bool.and_self]))
(prim! KC 'insert-edge-fresh-inv-sample '(kc-rest-ins kxy kck kcc w e R))

(lcopy! KC 'inv-cancel-pred)
(lcopy! KC 'inv-cut-suffix)

(a/theorem kc-rest-from [kxy :- Nat, kck :- Nat, kcc :- Nat, w :- World]
  (=> (= (Nat.blt kxy (:next-id w)) true)
      (= (tbl-all (same-id-then edge-id kxy (fn [r :- EdgeRow] (Bool.and (Nat.beq (:kind r) kck) (Nat.beq (:creditor r) kcc)))) (:edges w)) true)
      (= (kc-rest kxy kck kcc w) true))
  (intros h1 h2) (simp only [kc-rest h1 Bool.true_and]) (exact h2))

(a/theorem kc-of-mem [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (List.Mem e (:edges w)) (= (kc (:id e) (:kind e) (:creditor e) w) true))
  (intros h hm)
  (have pe (= (Bool.and (Nat.beq (:kind e) (:kind e)) (Nat.beq (:creditor e) (:creditor e))) true))
  (simp only [Bool.and_eq_true Nat.beq_eq]) (exact (And.intro True.intro True.intro))
  (have u := (uniq-all EdgeRow edge-id (fn [r :- EdgeRow] (Bool.and (Nat.beq (:kind r) (:kind e)) (Nat.beq (:creditor r) (:creditor e))))
               e (:edges w) (edges-nodup w h) hm pe))
  (have l := (run-ref-ok-edge w e h hm))
  (exact (kc-intro _ _ _ w h (kc-rest-from (:id e) (:kind e) (:creditor e) w l u))))

(a/theorem h14-entry-after-cut-keys [w :- World, c :- CompRow, e :- EdgeRow, e2 :- EdgeRow]
  (=> (= (inv-sample w) true) (= (entry-edge w (:id c)) (Option.some EdgeRow e))
      (List.Mem e2 (:edges (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)))) (= (:id e2) (:id e))
      (And (= (:kind e2) ek-dep) (= (:creditor e2) (:id c))))
  (intros hi he m2 hid)
  (have f := (h14-entry-edge-facts w (:id c) e he))
  (have k0 := (kc-of-mem w e hi (And.left f)))
  (have k1 := (kc-rest-of _ _ _ _ (kc-cut-suffix (:id e) (:kind e) (:creditor e) (cancel-pred w c) (:id c) true (:at e) (:id e)
                                    (kc-cancel-pred (:id e) (:kind e) (:creditor e) w c k0))))
  (simp only [kc-rest Bool.and_eq_true] at k1)
  (have z := (tbl-all-mem EdgeRow (kc-at (:id e) (:kind e) (:creditor e)) e2 _ (And.right k1) m2))
  (have i2 (= (Nat.beq (:id e2) (:id e)) true)) (simp only [Nat.beq_eq]) (exact hid)
  (simp only [kc-at i2 Bool.not_true Bool.false_or Bool.and_eq_true] at z)
  (exact (And.intro (Eq.trans (Nat.eq_of_beq_eq_true (And.left z)) (And.left (And.right f)))
                    (Eq.trans (Nat.eq_of_beq_eq_true (And.right z)) (And.left (And.right (And.right f)))))))

;; ---- the entry edge's id is free after cancel-pred and the cut: the edge is gone, or it is still a dep edge of C

(a/theorem h14-entry-free-after-cut [xm :- (List Nat), w :- World, c :- CompRow, e :- EdgeRow]
  (=> (= (p3la w) true) (= (h3 xm w) true) (List.Mem c (:comps w)) (= (Nat.beq (:done-epoch c) (:epoch c)) false)
      (= (entry-edge w (:id c)) (Option.some EdgeRow e))
      (= (h3-free xm (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) (:id e)) true))
  (intros hp h mc hd he)
  (have hg := (p3la-gd w hp))
  (have s1 := (hsw-sif (:id c) (cancel-pred w c) (hsw-rest-of _ _ (hsw-cancel-pred (:id c) w c (hsw-start w c hg mc hd)))))
  (have cs := (h14-cut-suffix-h3 xm (cancel-pred w c) (:id c) true (:at e) (:id e)
                (h14-cancel-pred-h3 xm w c hp h) s1 (h14-cancel-pred-no-holder w c hp mc)))
  (cases hf (tbl-find edge-id (:id e) (:edges (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)))))
  (case [none]
    (exact (h3-free-noedge xm _ (:id e) (h3-rest-of xm _ (And.left cs)) (tbl-find-none-has EdgeRow edge-id (:id e) _ hf))))
  (case [some e2]
    (have m2 := (tbl-find-mem EdgeRow edge-id (:id e) e2 _ hf))
    (have i2 := (tbl-find-id EdgeRow edge-id (:id e) e2 _ hf))
    (have i3 (= (:id e2) (:id e))) (exact i2)
    (have ks := (h14-entry-after-cut-keys w c e e2 (gd-sample w hg) he m2 i3))
    (have fr := (h14-free-dep-no-holder xm _ (:id c) e2 (And.left cs) (And.right cs) m2 (And.left ks) (And.right ks)))
    (rw [i3] at fr)
    (exact fr)))

;; ===========================================================================
;; T11 dispatch keeps h3: raw, through the guard, raw0g and post
;; ===========================================================================

(a/theorem h14-dispatch-raw-h3 [xm :- (List Nat), w :- World, c :- CompRow]
  (=> (= (p3la w) true) (List.Mem c (:comps w))
      (= (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c))) true)
      (= (h3 xm w) true) (= (h3 xm (dispatch-raw w c)) true))
  (intros hp mc hgd h)
  (have hg2 := hgd) (simp only [Bool.and_eq_true needs-run] at hg2)
  (have hd := (bnot-true _ (And.left (And.left (And.right hg2)))))
  (have hg := (p3la-gd w hp))
  (have s1 := (hsw-sif (:id c) (cancel-pred w c) (hsw-rest-of _ _ (hsw-cancel-pred (:id c) w c (hsw-start w c hg mc hd)))))
  (have cp := (h14-cancel-pred-h3 xm w c hp h))
  (have nh := (h14-cancel-pred-no-holder w c hp mc))
  (cases he (entry-edge w (:id c)))
  (case [none]
    (simp only [dispatch-raw he])
    (exact (h14-new-run-of-h3 xm _ c 0 (And.left (h14-cut-suffix-h3 xm (cancel-pred w c) (:id c) false 0 0 cp s1 nh)))))
  (case [some e]
    (have k0 := (kx-of-mem w e (gd-sample w hg) (entry-mem w (:id c) e he)))
    (have k1 := (kx-cut-suffix (:id e) (:debtor e) (cancel-pred w c) (:id c) true (:at e) (:id e)
                  (kx-cancel-pred (:id e) (:debtor e) w c k0)))
    (have hk1 := (hmk-cut-suffix (List.nil Nat) (cancel-pred w c) (:id c) true (:at e) (:id e) s1
                   (hmk-cancel-pred (List.nil Nat) w c (p3la-hmk w hp))))
    (simp only [dispatch-raw he])
    (exact (h14-new-run-of-h3 xm _ c (entry-ei e)
             (h14-consume-entry-h3 xm (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e hk1 (kx-rest-of _ _ _ k1)
               (h14-entry-free-after-cut xm w c e hp h mc hd he)
               (And.left (h14-cut-suffix-h3 xm (cancel-pred w c) (:id c) true (:at e) (:id e) cp s1 nh)))))))

(a/theorem h14-t11-outcome [xm :- (List Nat), w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (p3la w) true) (= (h3 xm w) true)
      (And (= (h3 xm (:world (t11-dispatch w cid fresh))) true)
           (=> (= (:accepted (t11-dispatch w cid fresh)) false) (= (:world (t11-dispatch w cid fresh)) w))))
  (intros hp h)
  (apply And.intro)
  (cases hc (comp-find w cid))
  (case [none] (simp only [t11-dispatch hc refuse]) (exact h))
  (case [some c]
    (cases hg3 (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c))))
    (case [false] (simp only [t11-dispatch hc hg3 Bool.and_false refuse]) (exact h))
    (case [true]
      (cases hf (Nat.beq fresh (:next-id w)))
      (case [false] (simp only [t11-dispatch hc hf Bool.false_and refuse]) (exact h))
      (case [true]
        (simp only [t11-dispatch hc hf hg3 Bool.and_self accept])
        (exact (h14-dispatch-raw-h3 xm w c hp (tbl-find-mem CompRow comp-id cid c (:comps w) hc) hg3 h)))))
  (exact (t11-refuse w cid fresh)))

(a/theorem h14-raw0g-dispatch-outcome [xm :- (List Nat), w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (p3la w) true) (= (h3 xm w) true)
      (And (= (h3 xm (:world (raw0g w (Item.dispatch-comp cid fresh)))) true)
           (=> (= (:accepted (raw0g w (Item.dispatch-comp cid fresh))) false) (= (:world (raw0g w (Item.dispatch-comp cid fresh))) w))))
  (intros hp h)
  (have non-host (= (host-item (Item.dispatch-comp cid fresh)) false)) (rfl)
  (have same := (raw0g-of w (Item.dispatch-comp cid fresh) non-host))
  (have r0 (= (raw0 w (Item.dispatch-comp cid fresh)) (t11-dispatch w cid fresh))) (rfl)
  (apply And.intro)
  (rw [same r0]) (exact (And.left (h14-t11-outcome xm w cid fresh hp h)))
  (exact (raw0g-refuse w (Item.dispatch-comp cid fresh))))

(a/theorem h14-raw-dispatch-accepted [w :- World, cid :- Nat, fresh :- Nat]
  (And (= (:accepted (raw w (Item.dispatch-comp cid fresh))) (:accepted (t11-dispatch w cid fresh)))
       (=> (= (:accepted (t11-dispatch w cid fresh)) true)
           (= (raw w (Item.dispatch-comp cid fresh)) (accept (cancel-losers w (:world (t11-dispatch w cid fresh)))))))
  (have non-host (= (host-item (Item.dispatch-comp cid fresh)) false)) (rfl)
  (have same := (raw0g-of w (Item.dispatch-comp cid fresh) non-host))
  (have r0 (= (raw0 w (Item.dispatch-comp cid fresh)) (t11-dispatch w cid fresh))) (rfl)
  (apply And.intro)
  (cases ha (:accepted (t11-dispatch w cid fresh)))
  (case [false] (simp only [raw same r0 post ha]))
  (case [true] (simp only [raw same r0 post ha accept]))
  (intro accepted)
  (simp only [raw same r0 post accepted]))

(a/theorem h14-raw-dispatch-outcome [xm :- (List Nat), w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (p3la w) true) (= (h3 xm w) true)
      (And (= (h3 xm (:world (raw w (Item.dispatch-comp cid fresh)))) true)
           (=> (= (:accepted (raw w (Item.dispatch-comp cid fresh))) false) (= (:world (raw w (Item.dispatch-comp cid fresh))) w))))
  (intros hp h)
  (have support := (h13-raw0g-support w (Item.dispatch-comp cid fresh) hp))
  (have before := (And.left (h14-raw0g-dispatch-outcome xm w cid fresh hp h)))
  (apply And.intro)
  (simp only [raw])
  (exact (h13-post-h3 xm w (raw0g w (Item.dispatch-comp cid fresh)) (And.left support) (And.left (And.right support))
           (And.right (And.right support)) before))
  (exact (raw-refuse w (Item.dispatch-comp cid fresh))))
