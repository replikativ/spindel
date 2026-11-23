(ns ^:ansatz/lean spindel.v2.inv.base
  "P3 complete: the reference invariants of `filter-safe-of-refs` (spindel.v2.inv.copier) through the step,
  and with them the step theorems with no honest hypothesis. Bundles (well-formed plus a rest
  part; each goes through the generic step tree, spindel.v2.pres.tree, by its table `tree/part!`):
    marks-on-dep   a marked edge is a dep edge (P3's `marked-dep`); companion mark-targets-dep M: the edges with an id in
          M are dep edges (the mark targets, computed before the fires of a write)
    refs-not-edges   edge-sep: every reference (cleanup entries' run and rows, a run's stored refs, a scope's
          parent) is no edge id and below the allocator (references are taken from existing non-edge
          rows; edges get fresh ids)
    act-runs-alive   every activation's run exists and is alive (acts-alive plus `act-run-has`); companion
          no-act-of-run x (no activation names run x) carries a retire's precondition to its run-del
    round-facts    the round invariant i7-idle, marks-on-dep, refs-not-edges, act-runs-alive, tombs-dormant 0 (C1 Q6: tombstones are dormant, spindel.v2.inv.tomb):
          every Rule R round is filter-safe (`round-facts-round`)
    chain-start   acts-parked, i12-ranks, i10-task, i9-res and round-facts: `step-chain-start`, `step-rule-r-safe` and the step theorems with no
          honest hypothesis (`step-well-formed-total`, `step-acts-total`, `step-rank-total`, ...)
    i5-seen   I5's observe part: an observe edge's seen is at most its debtor's version (versions only
          grow, an observed debtor is kept); companion edge-debtor-kept y d (edge id y keeps debtor d) for the
          rearms of T9/T11/T7; `step-i5-total`. The spec's third I5 clause (no armed dep edge on a
          final debtor) was false before Z#51 (reactivation re-armed onto a debtor that became
          final); Z#51 consumes such an edge (inv_test literal-i5-reactivation-resolved), and the
          clause is proved in spindel.v2.inv.i5 (`step-lit-i5-dep-final-total`, bundle i5-dep-final, chain-to-i5-dep-final)"
  (:require [ansatz.core :as a]
            [spindel.v2.pres.tree :as tree]
            [clojure.string :as str]
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
            [spindel.v2.inv.i10-task]
            [spindel.v2.inv.i9-res]
            [spindel.v2.inv.idle :refer :all]
            [spindel.v2.inv.tomb :refer :all]))

;; ===========================================================================
;; Part A. Marked edges are dep edges
;; ===========================================================================

(a/defn marks-on-dep-rest [w :- World] Bool (tbl-all marked-dep (:edges w)))
(a/defn marks-on-dep [w :- World] Bool (Bool.and (well-formed w) (marks-on-dep-rest w)))
(a/defn dep-in [m :- (List Nat), e :- EdgeRow] Bool
  (Bool.or (Bool.not (reach-mem (:id e) m)) (Nat.beq (:kind e) ek-dep)))
(a/defn mark-targets-dep-rest [mkm :- (List Nat), w :- World] Bool (tbl-all (both marked-dep (dep-in mkm)) (:edges w)))
(a/defn mark-targets-dep [mkm :- (List Nat), w :- World] Bool (Bool.and (well-formed w) (mark-targets-dep-rest mkm w)))

(a/theorem marks-on-dep-well-formed [w :- World] (=> (= (marks-on-dep w) true) (= (well-formed w) true))
  (intro h) (simp only [marks-on-dep Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem marks-on-dep-rest-of [w :- World] (=> (= (marks-on-dep w) true) (= (marks-on-dep-rest w) true))
  (intro h) (simp only [marks-on-dep Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem marks-on-dep-intro [w :- World] (=> (= (well-formed w) true) (= (marks-on-dep-rest w) true) (= (marks-on-dep w) true))
  (intros h1 h2) (simp only [marks-on-dep h1 h2 Bool.and_self]))
(a/theorem marks-on-dep-parts [w :- World]
  (=> (= (marks-on-dep w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (marks-on-dep-well-formed w h))))

(a/theorem mark-targets-dep-well-formed [mkm :- (List Nat), w :- World] (=> (= (mark-targets-dep mkm w) true) (= (well-formed w) true))
  (intro h) (simp only [mark-targets-dep Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem mark-targets-dep-rest-of [mkm :- (List Nat), w :- World] (=> (= (mark-targets-dep mkm w) true) (= (mark-targets-dep-rest mkm w) true))
  (intro h) (simp only [mark-targets-dep Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem mark-targets-dep-intro [mkm :- (List Nat), w :- World] (=> (= (well-formed w) true) (= (mark-targets-dep-rest mkm w) true) (= (mark-targets-dep mkm w) true))
  (intros h1 h2) (simp only [mark-targets-dep h1 h2 Bool.and_self]))
(a/theorem mark-targets-dep-parts [mkm :- (List Nat), w :- World]
  (=> (= (mark-targets-dep mkm w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (mark-targets-dep-well-formed mkm w h))))

;; ---- the edge predicates under edge edits

(a/theorem md-upd [x :- Nat, f :- (=> EdgeRow EdgeRow),
                   hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                   hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e))), es :- (List EdgeRow)]
  (=> (= (tbl-all marked-dep es) true) (= (tbl-all marked-dep (tbl-upd edge-id x f es)) true))
  (intro h)
  (apply (tbl-all-upd EdgeRow edge-id x f marked-dep marked-dep _ _ es h))
  (intros e he hx) (simp only [marked-dep (hk e) (hm e)]) (simp only [marked-dep] at he) (exact he)
  (intros e he hx) (exact he))

(a/theorem mk-upd [m :- (List Nat), x :- Nat, f :- (=> EdgeRow EdgeRow),
                   hi :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                   hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                   hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e))), es :- (List EdgeRow)]
  (=> (= (tbl-all (both marked-dep (dep-in m)) es) true) (= (tbl-all (both marked-dep (dep-in m)) (tbl-upd edge-id x f es)) true))
  (intro h)
  (apply (tbl-all-upd EdgeRow edge-id x f (both marked-dep (dep-in m)) (both marked-dep (dep-in m)) _ _ es h))
  (intros e he hx)
  (have e1 (= (:id (f e)) (:id e))) (exact (hi e))
  (simp only [both marked-dep dep-in] at he) (simp only [both marked-dep dep-in (hk e) (hm e) e1]) (exact he)
  (intros e he hx) (exact he))

(a/theorem all-sub-del [A :- Type, P :- (=> A Bool), idf :- (=> A Nat), x :- Nat, xs :- (List A)]
  (=> (= (tbl-all P xs) true) (= (tbl-all P (tbl-del idf x xs)) true))
  (intro h) (exact (tbl-all-del A idf x P P (fn [e :- A, he :- (= (P e) true), hx :- (= (Nat.beq (idf e) x) false)] he) xs h)))

;; generic: an edge predicate P over the edge table under the world edits
(a/theorem ep-edge-upd [P :- (=> EdgeRow Bool), w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                        hP :- (forall [e :- EdgeRow] (=> (= (P e) true) (= (P (f e)) true)))]
  (=> (= (tbl-all P (:edges w)) true) (= (tbl-all P (:edges (edge-upd w x f))) true))
  (intro h) (simp only [edge-upd set-edges])
  (exact (tbl-all-upd EdgeRow edge-id x f P P (fn [e :- EdgeRow, he :- (= (P e) true), hx :- (= (Nat.beq (edge-id e) x) true)] (hP e he))
           (fn [e :- EdgeRow, he :- (= (P e) true), hx :- (= (Nat.beq (edge-id e) x) false)] he) (:edges w) h)))

(a/theorem ep-remove-edge [P :- (=> EdgeRow Bool), w :- World, x :- Nat]
  (=> (= (tbl-all P (:edges w)) true) (= (tbl-all P (:edges (remove-edge w x))) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (all_goals (simp only [remove-edge hf hm comp-upd edge-del set-edges set-comps]))
    (all_goals (exact (all-sub-del EdgeRow P edge-id x (:edges w) h)))))

(a/theorem ep-unmark-edge [P :- (=> EdgeRow Bool), hP :- (forall [e :- EdgeRow] (=> (= (P e) true) (= (P (edge-set-marked false e)) true))),
                           w :- World, x :- Nat]
  (=> (= (tbl-all P (:edges w)) true) (= (tbl-all P (:edges (unmark-edge w x))) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true] (simp only [unmark-edge hf hm comp-upd set-comps]) (exact (ep-edge-upd P w x (edge-set-marked false) hP h)))))

(a/theorem ep-filter [P :- (=> EdgeRow Bool), q :- (=> EdgeRow Bool), es :- (List EdgeRow)]
  (=> (= (tbl-all P es) true) (= (tbl-all P (tbl-filter q es)) true))
  (intro h) (exact (tbl-all-filter EdgeRow P q es h)))

(a/theorem md-pres [f :- (=> EdgeRow EdgeRow), hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                    hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e))), e :- EdgeRow]
  (=> (= (marked-dep e) true) (= (marked-dep (f e)) true))
  (intro h) (simp only [marked-dep (hk e) (hm e)]) (exact h))
(a/theorem mk-pres [m :- (List Nat), f :- (=> EdgeRow EdgeRow), hi :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                    hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                    hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e))), e :- EdgeRow]
  (=> (= (both marked-dep (dep-in m) e) true) (= (both marked-dep (dep-in m) (f e)) true))
  (intro h)
  (have e1 (= (:id (f e)) (:id e))) (exact (hi e))
  (simp only [both marked-dep dep-in] at h) (simp only [both marked-dep dep-in (hk e) (hm e) e1]) (exact h))
(a/theorem md-unmark [e :- EdgeRow] (=> (= (marked-dep e) true) (= (marked-dep (edge-set-marked false e)) true))
  (intro h) (simp only [marked-dep edge-set-marked Bool.not_false Bool.true_or]))
(a/theorem mk-unmark [m :- (List Nat), e :- EdgeRow]
  (=> (= (both marked-dep (dep-in m) e) true) (= (both marked-dep (dep-in m) (edge-set-marked false e)) true))
  (intro h) (simp only [both marked-dep dep-in Bool.and_eq_true] at h)
  (simp only [both marked-dep dep-in edge-set-marked Bool.not_false Bool.true_or (And.right h) Bool.true_and]))

(a/theorem md-unmark-new [n :- Nat, e :- EdgeRow] (= (marked-dep (edge-set-id n (edge-set-marked false e))) true)
  (simp only [marked-dep edge-set-id edge-set-marked Bool.not_false Bool.true_or]))

(def MDB (mk-bundle 'marks-on-dep [] "marks-on-dep-" {}))
(swap! (:renames MDB) assoc 'well-formed-parts 'marks-on-dep-parts)
(defpart MDB :reads '[edges])
(prim! MDB 'well-formed-edge-upd '(ep-edge-upd marked-dep w x f (md-pres f hk hm) R))
(prim! MDB 'well-formed-remove-edge '(ep-remove-edge marked-dep w x R))
(prim! MDB 'well-formed-unmark-edge '(ep-unmark-edge marked-dep md-unmark w x R))
(prim! MDB 'well-formed-drop-cred-edges '(ep-filter marked-dep (cred-ne a) (:edges w) R))
(prim! MDB 'well-formed-drop-act '(ep-filter marked-dep (cred-ne a) (:edges w) R))
(prim! MDB 'well-formed-drop-edges '(ep-filter marked-dep p (:edges w) R))
(prim! MDB 'well-formed-filter-world '(tbl-all-keep-same EdgeRow K edge-id marked-dep (:edges w) R))
(prim! MDB 'well-formed-insert-edge-fresh '(all-cons EdgeRow marked-dep _ (:edges w) (md-unmark-new (:next-id w) e) R))
;; marks-on-dep on the generic tree (spindel.v2.pres.tree): its two own proofs go through the companion mark-targets-dep
(tree/part! MDB :over '{well-formed-write-raw marks-on-dep-write-raw       ; T2: the marks of a write land on dep edges
                        well-formed-mark-from marks-on-dep-mark-from})

(def MDK (mk-bundle 'mark-targets-dep '[mkm :- (List Nat)] "mark-targets-dep-" {}))
(swap! (:renames MDK) assoc 'well-formed-parts 'mark-targets-dep-parts)
(doseq [o '[well-formed-scope-upd well-formed-pub-upd well-formed-source-upd well-formed-resource-upd well-formed-cleanup-upd well-formed-cleanup-del
            well-formed-set-pins well-formed-resource-del well-formed-scope-del well-formed-cleanup-ins well-formed-act-upd well-formed-task-upd well-formed-run-upd well-formed-run-del
            well-formed-comp-upd well-formed-comp-del-unref well-formed-comp-ins-fresh well-formed-run-ins-fresh
            well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-resource-ins-fresh well-formed-scope-ins-fresh well-formed-act-ins-fresh well-formed-task-ins-fresh well-formed-bump well-formed-fork-del]]
  (prim! MDK o nil))
(prim! MDK 'well-formed-edge-upd '(ep-edge-upd (both marked-dep (dep-in mkm)) w x f (mk-pres mkm f hid hk hm) R))
(prim! MDK 'well-formed-remove-edge '(ep-remove-edge (both marked-dep (dep-in mkm)) w x R))
(prim! MDK 'well-formed-unmark-edge '(ep-unmark-edge (both marked-dep (dep-in mkm)) (mk-unmark mkm) w x R))
(prim! MDK 'well-formed-drop-cred-edges '(ep-filter (both marked-dep (dep-in mkm)) (cred-ne a) (:edges w) R))
(prim! MDK 'well-formed-drop-act '(ep-filter (both marked-dep (dep-in mkm)) (cred-ne a) (:edges w) R))
(prim! MDK 'well-formed-drop-edges '(ep-filter (both marked-dep (dep-in mkm)) p (:edges w) R))

(tree/restate! MDK '[well-formed-fire-edge well-formed-nat-fold])   ; the generic tree (spindel.v2.pres.tree) instead of a copy

;; ---- the mark targets are dep edges (unique edge ids)

(a/theorem nat-mem-cons-or [y :- Nat, h :- Nat, t :- (List Nat)] (= (nat-mem y (List.cons Nat h t)) (Bool.or (Nat.beq h y) (nat-mem y t)))
  (cases hb (Nat.beq h y)) (all_goals (simp [nat-mem hb])))

(a/theorem mt-ids [m :- (List Nat), y :- Nat, es :- (List EdgeRow)]
  (=> (= (reach-mem y (mark-targets m es)) true) (= (nat-mem y (tbl-ids edge-id es)) true))
  (induction es)
  (case [nil] (intro h) (simp [mark-targets reach-mem] at h))
  (case [cons hd t ih]
    (intro h)
    (cases hs (Bool.and (Nat.beq (:kind hd) ek-dep) (reach-mem (:debtor hd) m)))
    (case [false] (simp only [mark-targets hs] at h) (simp only [tbl-ids nat-mem-cons-or (ih h) Bool.or_true]))
    (case [true]
      (simp only [mark-targets hs reach-mem-cons Bool.or_eq_true] at h)
      (cases h)
      (case [inl h1] (simp only [tbl-ids nat-mem-cons-or (Eq.trans (beq-comm (edge-id hd) y) h1) Bool.true_or]))
      (case [inr h2] (simp only [tbl-ids nat-mem-cons-or (ih h2) Bool.or_true])))))

(a/theorem mt-dep [m :- (List Nat), es :- (List EdgeRow)]
  (=> (= (nat-nodup (tbl-ids edge-id es)) true) (= (tbl-all (dep-in (mark-targets m es)) es) true))
  (induction es)
  (case [nil] (intro h) (simp [tbl-all]))
  (case [cons hd t ih]
    (intro hn)
    (simp only [tbl-ids nat-nodup Bool.and_eq_true] at hn)
    (have hn1 := (bnot-true _ (And.left hn)))
    (have ne := (has-false-ne EdgeRow edge-id (edge-id hd) t (Eq.trans (Eq.symm (nat-mem-ids EdgeRow edge-id (edge-id hd) t)) hn1)))
    (have i1 := (ih (And.right hn)))
    (have nm (= (reach-mem (:id hd) (mark-targets m t)) false))
    (cases hr (reach-mem (:id hd) (mark-targets m t)))
    (case [false] (rfl))
    (case [true] (have z := (mt-ids m (:id hd) t hr)) (have z2 := (Eq.trans (Eq.symm z) hn1)) (cases z2))
    (cases hs (Bool.and (Nat.beq (:kind hd) ek-dep) (reach-mem (:debtor hd) m)))
    (case [false]
      (simp only [mark-targets hs tbl-all dep-in nm Bool.not_false Bool.true_or Bool.true_and])
      (exact i1))
    (case [true]
      (simp only [Bool.and_eq_true] at hs)
      (have h1 (= (dep-in (List.cons Nat (:id hd) (mark-targets m t)) hd) true)) (simp only [dep-in (And.left hs) Bool.or_true])
      (have h2 (= (tbl-all (dep-in (List.cons Nat (:id hd) (mark-targets m t))) t) true))
      (apply (tbl-all-mono2 EdgeRow (dep-in (mark-targets m t)) (fn [q :- EdgeRow] (Bool.not (Nat.beq (edge-id q) (edge-id hd))))
               (dep-in (List.cons Nat (:id hd) (mark-targets m t))) _ t i1 ne))
      (intros e d1 d2)
      (have d3 := (bnot-true _ d2))
      (have d4 (= (Nat.beq (:id e) (:id hd)) false)) (exact d3)
      (simp only [dep-in reach-mem-cons d4 Bool.false_or]) (simp only [dep-in] at d1) (exact d1)
      (simp only [mark-targets (And.left hs) (And.right hs) Bool.and_self tbl-all h1 h2]))))

(a/theorem edges-nodup [w :- World] (=> (= (well-formed w) true) (= (nat-nodup (tbl-ids edge-id (:edges w))) true))
  (intro h)
  (have hi := (And.right (And.right (well-formed-parts w h))))
  (simp only [ids-ok Bool.and_eq_true] at hi)
  (exact (ids-unique-edges w (And.left hi))))

(a/theorem mark-targets-dep-start [m :- (List Nat), w :- World]
  (=> (= (marks-on-dep w) true) (= (mark-targets-dep (mark-targets m (:edges w)) w) true))
  (intro h)
  (have hs := (marks-on-dep-well-formed w h))
  (have d := (mt-dep m (:edges w) (edges-nodup w hs)))
  (have r := (marks-on-dep-rest-of w h)) (simp only [marks-on-dep-rest] at r)
  (exact (mark-targets-dep-intro _ w hs
           (tbl-all-mono2 EdgeRow marked-dep (dep-in (mark-targets m (:edges w))) (both marked-dep (dep-in (mark-targets m (:edges w))))
             (fn [e :- EdgeRow, h1 :- (= (marked-dep e) true), h2 :- (= (dep-in (mark-targets m (:edges w)) e) true)]
               (both-of EdgeRow marked-dep (dep-in (mark-targets m (:edges w))) e h1 h2))
             (:edges w) r d))))

(a/theorem marks-on-dep-of-mark-targets-dep [m :- (List Nat), w :- World] (=> (= (mark-targets-dep m w) true) (= (marks-on-dep w) true))
  (intro h)
  (have r := (mark-targets-dep-rest-of m w h)) (simp only [mark-targets-dep-rest] at r)
  (exact (marks-on-dep-intro w (mark-targets-dep-well-formed m w h)
           (tbl-all-mono EdgeRow (both marked-dep (dep-in m)) marked-dep (both-left EdgeRow marked-dep (dep-in m)) (:edges w) r))))

(a/theorem mark-targets-dep-mark [m :- (List Nat), w :- World, x :- Nat]
  (=> (= (reach-mem x m) true) (= (mark-targets-dep m w) true) (= (mark-targets-dep m (mark-edge w x)) true))
  (intros hx h)
  (have hs := (mark-targets-dep-well-formed m w h))
  (have r := (mark-targets-dep-rest-of m w h)) (simp only [mark-targets-dep-rest] at r)
  (have r2 (= (mark-targets-dep-rest m (mark-edge w x)) true))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact r))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact r))
    (case [false]
      (simp only [mark-targets-dep-rest mark-edge hf hm comp-upd edge-upd set-edges set-comps])
      (apply (tbl-all-upd EdgeRow edge-id x (edge-set-marked true) (both marked-dep (dep-in m)) (both marked-dep (dep-in m)) _ _ (:edges w) r))
      (intros d hd hdx)
      (have hd2 (= (Nat.beq (:id d) x) true)) (exact hdx)
      (have e2 (= (:id d) x)) (exact (Nat.eq_of_beq_eq_true hdx))
      (simp only [both dep-in Bool.and_eq_true] at hd)
      (have k := (And.right hd))
      (simp only [e2 hx Bool.not_true Bool.false_or] at k)
      (simp only [both marked-dep dep-in edge-set-marked k Bool.or_true Bool.and_self])
      (intros d hd hdx) (exact hd)))
  (exact (mark-targets-dep-intro m _ (well-formed-mark-edge w x hs) r2)))

(a/theorem mark-targets-dep-mark-fold [m :- (List Nat), xs :- (List Nat)]
  (=> (= (tbl-all (fn [y :- Nat] (reach-mem y m)) xs) true)
      (forall [w :- World] (=> (= (mark-targets-dep m w) true) (= (mark-targets-dep m (nat-fold mark-edge w xs)) true))))
  (induction xs)
  (case [nil] (intros hx w h) (simp only [nat-fold]) (exact h))
  (case [cons hd t ih]
    (intros hx w h)
    (simp only [tbl-all Bool.and_eq_true] at hx)
    (simp only [nat-fold])
    (exact (ih (And.right hx) (mark-edge w hd) (mark-targets-dep-mark m w hd (And.left hx) h)))))

(a/theorem all-self-mem [m :- (List Nat)] (= (tbl-all (fn [y :- Nat] (reach-mem y m)) m) true)
  (apply all-of-mem-r) (intros y hy) (exact hy))

(a/theorem marks-on-dep-write-raw [w :- World, x :- Nat, v :- Nat]
  (=> (= (marks-on-dep w) true) (= (marks-on-dep (write-raw w x v)) true))
  (intro h)
  (simp only [write-raw])
  (have k0 := (mark-targets-dep-start (dirty-set w x) w h))
  (have k1 := (mark-targets-dep-source-upd (mark-targets (dirty-set w x) (:edges w)) w x (source-write v) (source-write-source-id v) k0))
  (have k2 := (mark-targets-dep-nat-fold (mark-targets (dirty-set w x) (:edges w)) (fire-edge (RunResult.mk res-ok v))
                (mark-targets-dep-fire-edge (mark-targets (dirty-set w x) (:edges w)) (RunResult.mk res-ok v)) (edges-onto x (:edges w)) _ k1))
  (exact (marks-on-dep-of-mark-targets-dep _ _ (mark-targets-dep-mark-fold (mark-targets (dirty-set w x) (:edges w)) (mark-targets (dirty-set w x) (:edges w))
                           (all-self-mem _) _ k2))))

(a/theorem marks-on-dep-mark-from [w :- World, c :- Nat]
  (=> (= (marks-on-dep w) true) (= (marks-on-dep (mark-from w c)) true))
  (intro h)
  (simp only [mark-from])
  (exact (marks-on-dep-of-mark-targets-dep _ _ (mark-targets-dep-mark-fold (mark-targets (List.cons Nat c (cone-set w c)) (:edges w))
                           (mark-targets (List.cons Nat c (cone-set w c)) (:edges w))
                           (all-self-mem _) w (mark-targets-dep-start (List.cons Nat c (cone-set w c)) w h)))))

(tree/restate! MDB '[well-formed-raw])
(tree/restate! MDB '[well-formed-normalize])

(a/theorem marks-on-dep-rule-r-round [w :- World]
  (=> (= (marks-on-dep w) true) (= (filter-safe (normalize w)) true) (= (marks-on-dep (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (marks-on-dep-filter-world _ (keep-fn (normalize w)) (marks-on-dep-normalize w h) hf)))

(a/theorem marks-on-dep-rule-r-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (marks-on-dep w0) true) (= (rounds-safe-loop fuel w0) true) (= (marks-on-dep (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (marks-on-dep-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (marks-on-dep-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))

(a/theorem marks-on-dep-rule-r [w :- World]
  (=> (= (marks-on-dep w) true) (= (rule-r-safe w) true) (= (marks-on-dep (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (marks-on-dep-rule-r-loop (rule-r-fuel w) w h hs)))

(a/theorem step-marks-on-dep [w :- World, it :- Item]
  (=> (= (marks-on-dep w) true) (= (rule-r-safe (:world (raw w it))) true) (= (marks-on-dep (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (marks-on-dep-rule-r (:world (raw w it)) (marks-on-dep-raw w it h) hs))))

(a/theorem marks-on-dep-empty [] (= (marks-on-dep empty-world) true) (rfl))

;; ===========================================================================
;; Part B. No edge id is a cleanup row or a storage ref (edge-sep): every reference (cleanup
;; entries' run and rows, a run row's stored refs, a scope's parent) is below the allocator and
;; no edge id; references are only ever taken from existing non-edge rows, edges get fresh ids
;; ===========================================================================

(a/defn ref-ok-k [es :- (List EdgeRow), n :- Nat, y :- Nat] Bool
  (Bool.and (Bool.not (tbl-has edge-id y es)) (Nat.blt y n)))
(a/defn crow-ok [es :- (List EdgeRow), n :- Nat, c :- CleanupRow] Bool
  (Bool.and (ref-ok-k es n (:run c)) (tbl-all (ref-ok-k es n) (:rows c))))
(a/defn rrow-ok [es :- (List EdgeRow), n :- Nat, r :- RunRow] Bool (tbl-all (ref-ok-k es n) (run-stored r)))
(a/defn srow-ok [es :- (List EdgeRow), n :- Nat, s :- ScopeRow] Bool (ref-ok-k es n (:parent s)))
;; C1c stage B: a fork marker's id and owner are references too (they are storage, spindel.v2.retain `fork-keep`)
(a/defn frow-ok [es :- (List EdgeRow), n :- Nat, f :- ForkRow] Bool
  (Bool.and (ref-ok-k es n (:id f)) (ref-ok-k es n (:owner f))))
(a/defn esk [es :- (List EdgeRow), n :- Nat, cl :- (List CleanupRow), rs :- (List RunRow), ss :- (List ScopeRow),
             fs :- (List ForkRow)] Bool
  (Bool.and (tbl-all (crow-ok es n) cl)
            (Bool.and (tbl-all (rrow-ok es n) rs) (Bool.and (tbl-all (srow-ok es n) ss) (tbl-all (frow-ok es n) fs)))))
(a/defn refs-not-edges-rest [w :- World] Bool (esk (:edges w) (:next-id w) (:cleanup w) (:runs w) (:scopes w) (:forks w)))
(a/defn refs-not-edges [w :- World] Bool (Bool.and (well-formed w) (refs-not-edges-rest w)))

(a/theorem refs-not-edges-well-formed [w :- World] (=> (= (refs-not-edges w) true) (= (well-formed w) true))
  (intro h) (simp only [refs-not-edges Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem refs-not-edges-rest-of [w :- World] (=> (= (refs-not-edges w) true) (= (refs-not-edges-rest w) true))
  (intro h) (simp only [refs-not-edges Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem refs-not-edges-intro [w :- World] (=> (= (well-formed w) true) (= (refs-not-edges-rest w) true) (= (refs-not-edges w) true))
  (intros h1 h2) (simp only [refs-not-edges h1 h2 Bool.and_self]))
(a/theorem refs-not-edges-parts [w :- World]
  (=> (= (refs-not-edges w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (refs-not-edges-well-formed w h))))
(a/theorem esk-parts [es :- (List EdgeRow), n :- Nat, cl :- (List CleanupRow), rs :- (List RunRow), ss :- (List ScopeRow),
                      fs :- (List ForkRow)]
  (=> (= (esk es n cl rs ss fs) true)
      (And (= (tbl-all (crow-ok es n) cl) true) (And (= (tbl-all (rrow-ok es n) rs) true) (= (tbl-all (srow-ok es n) ss) true))))
  (intro h) (simp only [esk Bool.and_eq_true] at h)
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h)) (And.left (And.right (And.right h)))))))
(a/theorem esk-fparts [es :- (List EdgeRow), n :- Nat, cl :- (List CleanupRow), rs :- (List RunRow), ss :- (List ScopeRow),
                       fs :- (List ForkRow)]
  (=> (= (esk es n cl rs ss fs) true) (= (tbl-all (frow-ok es n) fs) true))
  (intro h) (simp only [esk Bool.and_eq_true] at h) (exact (And.right (And.right (And.right h)))))
(a/theorem esk-intro [es :- (List EdgeRow), n :- Nat, cl :- (List CleanupRow), rs :- (List RunRow), ss :- (List ScopeRow),
                      fs :- (List ForkRow)]
  (=> (= (tbl-all (crow-ok es n) cl) true) (= (tbl-all (rrow-ok es n) rs) true) (= (tbl-all (srow-ok es n) ss) true)
      (= (tbl-all (frow-ok es n) fs) true)
      (= (esk es n cl rs ss fs) true))
  (intros h1 h2 h3 h4) (simp only [esk h1 h2 h3 h4 Bool.and_self]))

;; ---- sublists

(a/theorem all-sub [p :- (=> Nat Bool), xs :- (List Nat), ys :- (List Nat),
                    hs :- (forall [y :- Nat] (=> (= (reach-mem y ys) true) (= (reach-mem y xs) true)))]
  (=> (= (tbl-all p xs) true) (= (tbl-all p ys) true))
  (intro h)
  (exact (all-of-mem-r p ys (fn [y :- Nat, hy :- (= (reach-mem y ys) true)] (all-reach-mem p y xs h (hs y hy))))))

;; ---- edges and the allocator: fewer edge ids below n, n grows

(a/defn edges-sub [n :- Nat, es :- (List EdgeRow), es2 :- (List EdgeRow)] Prop
  (forall [y :- Nat] (=> (= (Nat.blt y n) true) (= (tbl-has edge-id y es2) true) (= (tbl-has edge-id y es) true))))

(a/theorem ref-ok-mono [es :- (List EdgeRow), es2 :- (List EdgeRow), n :- Nat, n2 :- Nat, y :- Nat]
  (=> (edges-sub n es es2) (<= n n2) (= (ref-ok-k es n y) true) (= (ref-ok-k es2 n2 y) true))
  (intros hs hn h)
  (simp only [ref-ok-k Bool.and_eq_true] at h)
  (have hb := (And.right h))
  (have h1 (= (tbl-has edge-id y es2) false))
  (cases hy (tbl-has edge-id y es2))
  (case [false] (rfl))
  (case [true] (have z := (hs y hb hy)) (have z2 := (Eq.trans (Eq.symm z) (bnot-true _ (And.left h)))) (cases z2))
  (have h2 (= (Nat.blt y n2) true))
  (simp only [Nat.blt_eq] at hb) (simp only [Nat.blt_eq]) (omega)
  (simp only [ref-ok-k h1 h2 Bool.not_false Bool.and_self]))

(a/theorem crow-mono [es :- (List EdgeRow), es2 :- (List EdgeRow), n :- Nat, n2 :- Nat,
                      m :- (forall [y :- Nat] (=> (= (ref-ok-k es n y) true) (= (ref-ok-k es2 n2 y) true))), c :- CleanupRow]
  (=> (= (crow-ok es n c) true) (= (crow-ok es2 n2 c) true))
  (intro h) (simp only [crow-ok Bool.and_eq_true] at h)
  (simp only [crow-ok (m (:run c) (And.left h)) (tbl-all-mono Nat (ref-ok-k es n) (ref-ok-k es2 n2) m (:rows c) (And.right h)) Bool.and_self]))

(a/theorem frow-mono [es :- (List EdgeRow), es2 :- (List EdgeRow), n :- Nat, n2 :- Nat,
                      m :- (forall [y :- Nat] (=> (= (ref-ok-k es n y) true) (= (ref-ok-k es2 n2 y) true))), f :- ForkRow]
  (=> (= (frow-ok es n f) true) (= (frow-ok es2 n2 f) true))
  (intro h) (simp only [frow-ok Bool.and_eq_true] at h)
  (simp only [frow-ok (m (:id f) (And.left h)) (m (:owner f) (And.right h)) Bool.and_self]))

(a/theorem esk-mono [es :- (List EdgeRow), es2 :- (List EdgeRow), n :- Nat, n2 :- Nat,
                     cl :- (List CleanupRow), rs :- (List RunRow), ss :- (List ScopeRow), fs :- (List ForkRow)]
  (=> (edges-sub n es es2) (<= n n2) (= (esk es n cl rs ss fs) true) (= (esk es2 n2 cl rs ss fs) true))
  (intros hs hn h)
  (have p := (esk-parts es n cl rs ss fs h))
  (have m (forall [y :- Nat] (=> (= (ref-ok-k es n y) true) (= (ref-ok-k es2 n2 y) true))))
  (intros y hy) (exact (ref-ok-mono es es2 n n2 y hs hn hy))
  (exact (esk-intro es2 n2 cl rs ss fs
           (tbl-all-mono CleanupRow (crow-ok es n) (crow-ok es2 n2)
             (fn [c :- CleanupRow, hc :- (= (crow-ok es n c) true)] (crow-mono es es2 n n2 m c hc)) cl (And.left p))
           (tbl-all-mono RunRow (rrow-ok es n) (rrow-ok es2 n2)
             (fn [r :- RunRow, hr :- (= (rrow-ok es n r) true)] (tbl-all-mono Nat (ref-ok-k es n) (ref-ok-k es2 n2) m (run-stored r) hr)) rs (And.left (And.right p)))
           (tbl-all-mono ScopeRow (srow-ok es n) (srow-ok es2 n2)
             (fn [s :- ScopeRow, hs2 :- (= (srow-ok es n s) true)] (m (:parent s) hs2)) ss (And.right (And.right p)))
           (tbl-all-mono ForkRow (frow-ok es n) (frow-ok es2 n2) (frow-mono es es2 n n2 m) fs (esk-fparts es n cl rs ss fs h)))))

;; ---- references to existing non-edge rows (unique ids, below the allocator)

(a/theorem nodup-app-disj2 [x :- Nat, xs :- (List Nat), ys :- (List Nat)]
  (=> (= (nat-nodup (nat-app xs ys)) true) (= (nat-mem x ys) true) (= (nat-mem x xs) false))
  (intros hn hm)
  (cases hx (nat-mem x xs))
  (case [false] (rfl))
  (case [true] (have d := (nodup-app-disj x xs ys hn hx)) (have z := (Eq.trans (Eq.symm hm) d)) (cases z)))

(a/theorem ref-ok-of [w :- World, y :- Nat]
  (=> (= (well-formed w) true) (= (nat-mem y (all-ids w)) true) (= (nat-mem y (tbl-ids edge-id (:edges w))) false)
      (= (ref-ok-k (:edges w) (:next-id w) y) true))
  (intros h hm he)
  (have hb := (ids-below-of w h))
  (have r := (all-nat-mem (id-in-range (:next-id w)) y (all-ids w) hb hm))
  (simp only [id-in-range Bool.and_eq_true] at r)
  (have he2 (= (tbl-has edge-id y (:edges w)) false)) (rw [← (nat-mem-ids EdgeRow edge-id y (:edges w))]) (exact he)
  (simp only [ref-ok-k he2 (And.right r) Bool.not_false Bool.and_self]))

(a/theorem ref-ok-zero [w :- World] (=> (= (well-formed w) true) (= (ref-ok-k (:edges w) (:next-id w) 0) true))
  (intro h)
  (have hi := (And.right (And.right (well-formed-parts w h))))
  (simp only [ids-ok ids-below Bool.and_eq_true] at hi)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (have he (= (tbl-has edge-id 0 (:edges w)) false))
  (cases hc (tbl-has edge-id 0 (:edges w)))
  (case [false] (rfl))
  (case [true]
    (have z := (has-pos EdgeRow edge-id 0 (:next-id w) (:edges w) (And.left (And.right (And.right (And.right (And.right (And.right hb)))))) hc))
    (simp at z))
  (simp only [ref-ok-k he (And.left (And.right hi)) Bool.not_false Bool.and_self]))

(a/theorem scope-ref-ok [w :- World, y :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has scope-id y (:scopes w)) true) (= (ref-ok-k (:edges w) (:next-id w) y) true))
  (intros h hh)
  (have hm (= (nat-mem y (tbl-ids scope-id (:scopes w))) true)) (rw [nat-mem-ids]) (exact hh)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have ma (= (nat-mem y (all-ids w)) true)) (simp only [all-ids]) (exact (mem-app-l _ _ _ hm))
  (have d := (nodup-app-disj y _ _ u hm))
  (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
  (have ne := (And.left (And.right (And.right (And.right (And.right d))))))
  (exact (ref-ok-of w y h ma ne)))
(a/theorem comp-ref-ok [w :- World, y :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has comp-id y (:comps w)) true) (= (ref-ok-k (:edges w) (:next-id w) y) true))
  (intros h hh)
  (have hm (= (nat-mem y (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hh)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have ma (= (nat-mem y (all-ids w)) true)) (simp only [all-ids]) (exact (mem-app-r _ _ _ (mem-app-l _ _ _ hm)))
  (have d := (nodup-app-disj y _ _ (nat-nodup-app-right _ _ u) hm))
  (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
  (have ne := (And.left (And.right (And.right (And.right d)))))
  (exact (ref-ok-of w y h ma ne)))
(a/theorem task-ref-ok [w :- World, y :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has task-id y (:tasks w)) true) (= (ref-ok-k (:edges w) (:next-id w) y) true))
  (intros h hh)
  (have hm (= (nat-mem y (tbl-ids task-id (:tasks w))) true)) (rw [nat-mem-ids]) (exact hh)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have ma (= (nat-mem y (all-ids w)) true)) (simp only [all-ids]) (exact (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-l _ _ _ hm))))
  (have d := (nodup-app-disj y _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ u)) hm))
  (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
  (have ne := (And.left (And.right (And.right d))))
  (exact (ref-ok-of w y h ma ne)))
(a/theorem run-ref-ok [w :- World, y :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has run-id y (:runs w)) true) (= (ref-ok-k (:edges w) (:next-id w) y) true))
  (intros h hh)
  (have hm (= (nat-mem y (tbl-ids run-id (:runs w))) true)) (rw [nat-mem-ids]) (exact hh)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have ma (= (nat-mem y (all-ids w)) true)) (simp only [all-ids]) (exact (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-l _ _ _ hm)))))
  (have d := (nodup-app-disj y _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ u))) hm))
  (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
  (have ne := (And.left (And.right d)))
  (exact (ref-ok-of w y h ma ne)))
(a/theorem source-ref-ok [w :- World, y :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has source-id y (:sources w)) true) (= (ref-ok-k (:edges w) (:next-id w) y) true))
  (intros h hh)
  (have hm (= (nat-mem y (tbl-ids source-id (:sources w))) true)) (rw [nat-mem-ids]) (exact hh)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have ma (= (nat-mem y (all-ids w)) true)) (simp only [all-ids]) (exact (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-l _ _ _ hm))))))
  (have d := (nodup-app-disj y _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ u)))) hm))
  (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
  (have ne := (And.left d))
  (exact (ref-ok-of w y h ma ne)))
(a/theorem res-ref-ok [w :- World, y :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has resource-id y (:res w)) true) (= (ref-ok-k (:edges w) (:next-id w) y) true))
  (intros h hh)
  (have hm (= (nat-mem y (tbl-ids resource-id (:res w))) true)) (rw [nat-mem-ids]) (exact hh)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have ma (= (nat-mem y (all-ids w)) true)) (simp only [all-ids]) (exact (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-l _ _ _ hm)))))))))
  (have u5 := (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ u))))))
  (have ne := (nodup-app-disj2 y _ _ u5 (mem-app-r _ _ _ (mem-app-l _ _ _ hm))))
  (exact (ref-ok-of w y h ma ne)))

;; ---- edges-sub instances

(a/theorem esub-refl [n :- Nat, es :- (List EdgeRow)] (edges-sub n es es)
  (intros y hy hh) (exact hh))
(a/theorem esub-upd [n :- Nat, x :- Nat, f :- (=> EdgeRow EdgeRow), hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))), es :- (List EdgeRow)]
  (edges-sub n es (tbl-upd edge-id x f es))
  (intros y hy hh) (rw [(tbl-has-upd EdgeRow edge-id x y f hid es)] at hh) (exact hh))
(a/theorem has-del-sub [A :- Type, idf :- (=> A Nat), x :- Nat, y :- Nat, xs :- (List A)]
  (=> (= (tbl-has idf y (tbl-del idf x xs)) true) (= (tbl-has idf y xs) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-del tbl-has] at h))
  (case [cons hd t ih]
    (intro h)
    (cases hx (Nat.beq (idf hd) x))
    (case [true] (simp only [tbl-del hx] at h) (cases hy (Nat.beq (idf hd) y)) (all_goals (simp only [tbl-has hy (ih h)])))
    (case [false]
      (simp only [tbl-del hx tbl-has] at h)
      (cases hy (Nat.beq (idf hd) y))
      (case [true] (simp only [tbl-has hy]))
      (case [false] (simp only [hy] at h) (simp only [tbl-has hy (ih h)])))))
(a/theorem has-filter-sub [A :- Type, idf :- (=> A Nat), q :- (=> A Bool), y :- Nat, xs :- (List A)]
  (=> (= (tbl-has idf y (tbl-filter q xs)) true) (= (tbl-has idf y xs) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-filter tbl-has] at h))
  (case [cons hd t ih]
    (intro h)
    (cases hy (Nat.beq (idf hd) y))
    (case [true] (simp only [tbl-has hy]))
    (case [false]
      (cases hq (q hd))
      (all_goals (simp only [tbl-filter hq tbl-has hy] at h))
      (all_goals (simp only [tbl-has hy (ih h)])))))
(a/theorem esub-del [n :- Nat, x :- Nat, es :- (List EdgeRow)] (edges-sub n es (tbl-del edge-id x es))
  (intros y hy hh) (exact (has-del-sub EdgeRow edge-id x y es hh)))
(a/theorem esub-filter [n :- Nat, q :- (=> EdgeRow Bool), es :- (List EdgeRow)] (edges-sub n es (tbl-filter q es))
  (intros y hy hh) (exact (has-filter-sub EdgeRow edge-id q y es hh)))
(a/theorem esub-keep [n :- Nat, K :- (=> Nat Bool), es :- (List EdgeRow)] (edges-sub n es (tbl-keep K edge-id es))
  (intros y hy hh) (rw [tbl-has-keep] at hh) (simp only [Bool.and_eq_true] at hh) (exact (And.right hh)))
(a/theorem esub-ins [n :- Nat, r :- EdgeRow, hr :- (= (edge-id r) n), es :- (List EdgeRow)] (edges-sub n es (List.cons EdgeRow r es))
  (intros y hy hh)
  (cases he (Nat.beq (edge-id r) y))
  (case [true]
    (have e1 (= (edge-id r) y)) (exact (Nat.eq_of_beq_eq_true he))
    (have e2 (= y n)) (exact (Eq.trans (Eq.symm e1) hr))
    (simp only [Nat.blt_eq e2] at hy) (omega))
  (case [false] (simp only [tbl-has he] at hh) (exact hh)))

(a/theorem refs-not-edges-rest-mw [w :- World, w2 :- World]
  (=> (edges-sub (:next-id w) (:edges w) (:edges w2)) (<= (:next-id w) (:next-id w2))
      (= (:cleanup w2) (:cleanup w)) (= (:runs w2) (:runs w)) (= (:scopes w2) (:scopes w)) (= (:forks w2) (:forks w))
      (= (refs-not-edges-rest w) true) (= (refs-not-edges-rest w2) true))
  (intros hs hn hc hr hsc hf h)
  (simp only [refs-not-edges-rest hc hr hsc hf])
  (exact (esk-mono _ _ _ _ _ _ _ _ hs hn h)))

(a/theorem refs-not-edges-rest-sets [w :- World, cl :- (List CleanupRow), rs :- (List RunRow), ss :- (List ScopeRow), fs :- (List ForkRow)]
  (=> (= (refs-not-edges-rest w) true)
      (=> (= (tbl-all (frow-ok (:edges w) (:next-id w)) (:forks w)) true) (= (tbl-all (frow-ok (:edges w) (:next-id w)) fs) true))
      (=> (= (tbl-all (crow-ok (:edges w) (:next-id w)) (:cleanup w)) true) (= (tbl-all (crow-ok (:edges w) (:next-id w)) cl) true))
      (=> (= (tbl-all (rrow-ok (:edges w) (:next-id w)) (:runs w)) true) (= (tbl-all (rrow-ok (:edges w) (:next-id w)) rs) true))
      (=> (= (tbl-all (srow-ok (:edges w) (:next-id w)) (:scopes w)) true) (= (tbl-all (srow-ok (:edges w) (:next-id w)) ss) true))
      (= (esk (:edges w) (:next-id w) cl rs ss fs) true))
  (intros h h4 h1 h2 h3)
  (have p := (esk-parts _ _ _ _ _ _ h))
  (exact (esk-intro _ _ _ _ _ _ (h1 (And.left p)) (h2 (And.left (And.right p))) (h3 (And.right (And.right p)))
           (h4 (esk-fparts _ _ _ _ _ _ h)))))

;; ---- primitives

(a/theorem refs-not-edges-rest-remove-edge [w :- World, x :- Nat] (=> (= (refs-not-edges-rest w) true) (= (refs-not-edges-rest (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm])
      (exact (refs-not-edges-rest-mw w (edge-del w x) (esub-del (:next-id w) x (:edges w)) (Nat.le_refl _) (rfl) (rfl) (rfl) (rfl) h)))
    (case [true] (simp only [remove-edge hf hm])
      (exact (refs-not-edges-rest-mw w (comp-upd (edge-del w x) (:creditor e) comp-dec-pending) (esub-del (:next-id w) x (:edges w)) (Nat.le_refl _) (rfl) (rfl) (rfl) (rfl) h)))))

(a/theorem refs-not-edges-rest-mark-edge [w :- World, x :- Nat] (=> (= (refs-not-edges-rest w) true) (= (refs-not-edges-rest (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false] (simp only [mark-edge hf hm])
      (exact (refs-not-edges-rest-mw w (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending)
               (esub-upd (:next-id w) x (edge-set-marked true) (fn [d :- EdgeRow] (Eq.refl (edge-id d))) (:edges w)) (Nat.le_refl _) (rfl) (rfl) (rfl) (rfl) h)))))

(a/theorem refs-not-edges-rest-unmark-edge [w :- World, x :- Nat] (=> (= (refs-not-edges-rest w) true) (= (refs-not-edges-rest (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true] (simp only [unmark-edge hf hm])
      (exact (refs-not-edges-rest-mw w (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending)
               (esub-upd (:next-id w) x (edge-set-marked false) (fn [d :- EdgeRow] (Eq.refl (edge-id d))) (:edges w)) (Nat.le_refl _) (rfl) (rfl) (rfl) (rfl) h)))))

(a/theorem all-del-same [A :- Type, P :- (=> A Bool), idf :- (=> A Nat), x :- Nat, xs :- (List A)]
  (=> (= (tbl-all P xs) true) (= (tbl-all P (tbl-del idf x xs)) true))
  (intro h) (exact (tbl-all-del A idf x P P (fn [e :- A, he :- (= (P e) true), hx :- (= (Nat.beq (idf e) x) false)] he) xs h)))
(a/theorem self-imp [b :- Bool] (=> (= b true) (= b true)) (intro h) (exact h))

(a/theorem refs-not-edges-rest-run-del [w :- World, x :- Nat] (=> (= (refs-not-edges-rest w) true) (= (refs-not-edges-rest (run-del w x)) true))
  (intro h) (simp only [refs-not-edges-rest run-del set-runs])
  (exact (refs-not-edges-rest-sets w _ _ _ _ h (self-imp _) (self-imp _) (all-del-same RunRow (rrow-ok (:edges w) (:next-id w)) run-id x (:runs w)) (self-imp _))))
(a/theorem refs-not-edges-rest-scope-del [w :- World, x :- Nat] (=> (= (refs-not-edges-rest w) true) (= (refs-not-edges-rest (scope-del w x)) true))
  (intro h) (simp only [refs-not-edges-rest scope-del set-scopes])
  (exact (refs-not-edges-rest-sets w _ _ _ _ h (self-imp _) (self-imp _) (self-imp _) (all-del-same ScopeRow (srow-ok (:edges w) (:next-id w)) scope-id x (:scopes w)))))
(a/theorem refs-not-edges-rest-cleanup-del [w :- World, x :- Nat] (=> (= (refs-not-edges-rest w) true) (= (refs-not-edges-rest (cleanup-del w x)) true))
  (intro h) (simp only [refs-not-edges-rest cleanup-del set-cleanup])
  (exact (refs-not-edges-rest-sets w _ _ _ _ h (self-imp _) (all-del-same CleanupRow (crow-ok (:edges w) (:next-id w)) cleanup-id x (:cleanup w)) (self-imp _) (self-imp _))))

(a/theorem refs-not-edges-rest-fork-del [w :- World, x :- Nat] (=> (= (refs-not-edges-rest w) true) (= (refs-not-edges-rest (fork-del w x)) true))
  (intro h) (simp only [refs-not-edges-rest fork-del set-forks])
  (exact (refs-not-edges-rest-sets w _ _ _ _ h (all-del-same ForkRow (frow-ok (:edges w) (:next-id w)) fork-id x (:forks w)) (self-imp _) (self-imp _) (self-imp _))))

(a/theorem refs-not-edges-rest-filter-world [w :- World, K :- (=> Nat Bool)] (=> (= (refs-not-edges-rest w) true) (= (refs-not-edges-rest (filter-world K w)) true))
  (intro h)
  (have h1 (= (esk (:edges w) (:next-id w) (:cleanup w) (tbl-keep K run-id (:runs w)) (tbl-keep K scope-id (:scopes w))
                   (tbl-keep K fork-id (:forks w))) true))
  (exact (refs-not-edges-rest-sets w _ _ _ _ h (tbl-all-keep-same ForkRow K fork-id (frow-ok (:edges w) (:next-id w)) (:forks w))
           (self-imp _) (tbl-all-keep-same RunRow K run-id (rrow-ok (:edges w) (:next-id w)) (:runs w))
           (tbl-all-keep-same ScopeRow K scope-id (srow-ok (:edges w) (:next-id w)) (:scopes w))))
  (simp only [refs-not-edges-rest filter-world])
  (exact (esk-mono _ _ _ _ _ _ _ _ (esub-keep (:next-id w) K (:edges w)) (Nat.le_refl _) h1)))

(a/theorem refs-not-edges-run-upd-m [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                          hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                          hs :- (forall [r :- RunRow, y :- Nat] (=> (= (reach-mem y (run-stored (f r))) true) (= (reach-mem y (run-stored r)) true)))]
  (=> (= (refs-not-edges w) true) (= (refs-not-edges (run-upd w x f)) true))
  (intro h)
  (have r (= (refs-not-edges-rest (run-upd w x f)) true))
  (simp only [refs-not-edges-rest run-upd set-runs])
  (apply (refs-not-edges-rest-sets w _ _ _ _ (refs-not-edges-rest-of w h) (self-imp _) (self-imp _) _ (self-imp _)))
  (intro h2)
  (exact (tbl-all-upd RunRow run-id x f (rrow-ok (:edges w) (:next-id w)) (rrow-ok (:edges w) (:next-id w))
           (fn [q :- RunRow, hq :- (= (rrow-ok (:edges w) (:next-id w) q) true), hx :- (= (Nat.beq (run-id q) x) true)]
             (all-sub (ref-ok-k (:edges w) (:next-id w)) (run-stored q) (run-stored (f q)) (hs q) hq))
           (fn [q :- RunRow, hq :- (= (rrow-ok (:edges w) (:next-id w) q) true), hx :- (= (Nat.beq (run-id q) x) false)] hq)
           (:runs w) h2))
  (exact (refs-not-edges-intro _ (well-formed-run-upd w x f hf (refs-not-edges-well-formed w h)) r)))

(a/theorem refs-not-edges-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                        hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hk :- (forall [r :- RunRow] (= (run-stored (f r)) (run-stored r)))]
  (=> (= (refs-not-edges w) true) (= (refs-not-edges (run-upd w x f)) true))
  (exact (refs-not-edges-run-upd-m w x f hf (fn [r :- RunRow, y :- Nat, hy :- (= (reach-mem y (run-stored (f r))) true)] (Eq.trans (Eq.symm (congrArg (reach-mem y) (hk r))) hy)))))

(a/theorem refs-not-edges-scope-upd [w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow),
                          hid :- (forall [s :- ScopeRow] (= (scope-id (f s)) (scope-id s))),
                          hp :- (forall [s :- ScopeRow] (= (:parent (f s)) (:parent s)))]
  (=> (= (refs-not-edges w) true) (= (refs-not-edges (scope-upd w x f)) true))
  (intro h)
  (have r (= (refs-not-edges-rest (scope-upd w x f)) true))
  (simp only [refs-not-edges-rest scope-upd set-scopes])
  (apply (refs-not-edges-rest-sets w _ _ _ _ (refs-not-edges-rest-of w h) (self-imp _) (self-imp _) (self-imp _)))
  (intro h2)
  (exact (tbl-all-upd ScopeRow scope-id x f (srow-ok (:edges w) (:next-id w)) (srow-ok (:edges w) (:next-id w))
           (fn [s :- ScopeRow, hq :- (= (srow-ok (:edges w) (:next-id w) s) true), hx :- (= (Nat.beq (scope-id s) x) true)]
             (Eq.trans (congrArg (ref-ok-k (:edges w) (:next-id w)) (hp s)) hq))
           (fn [s :- ScopeRow, hq :- (= (srow-ok (:edges w) (:next-id w) s) true), hx :- (= (Nat.beq (scope-id s) x) false)] hq)
           (:scopes w) h2))
  (exact (refs-not-edges-intro _ (well-formed-scope-upd w x f hid (refs-not-edges-well-formed w h)) r)))

(a/theorem crow-sub [w :- World, c :- CleanupRow, c2 :- CleanupRow]
  (=> (= (:run c2) (:run c)) (forall [y :- Nat] (=> (= (reach-mem y (:rows c2)) true) (= (reach-mem y (:rows c)) true)))
      (= (crow-ok (:edges w) (:next-id w) c) true) (= (crow-ok (:edges w) (:next-id w) c2) true))
  (intros hr hs h)
  (simp only [crow-ok Bool.and_eq_true] at h)
  (simp only [crow-ok hr (And.left h) (all-sub (ref-ok-k (:edges w) (:next-id w)) (:rows c) (:rows c2) hs (And.right h)) Bool.and_self]))

(a/theorem refs-not-edges-cleanup-upd-m [w :- World, x :- Nat, f :- (=> CleanupRow CleanupRow),
                              hr :- (forall [c :- CleanupRow] (= (:run (f c)) (:run c))),
                              hs :- (forall [c :- CleanupRow, y :- Nat] (=> (= (reach-mem y (:rows (f c))) true) (= (reach-mem y (:rows c)) true)))]
  (=> (= (refs-not-edges w) true) (= (refs-not-edges (cleanup-upd w x f)) true))
  (intro h)
  (have r (= (refs-not-edges-rest (cleanup-upd w x f)) true))
  (simp only [refs-not-edges-rest cleanup-upd set-cleanup])
  (apply (refs-not-edges-rest-sets w _ _ _ _ (refs-not-edges-rest-of w h) (self-imp _) _ (self-imp _) (self-imp _)))
  (intro h2)
  (exact (tbl-all-upd CleanupRow cleanup-id x f (crow-ok (:edges w) (:next-id w)) (crow-ok (:edges w) (:next-id w))
           (fn [c :- CleanupRow, hq :- (= (crow-ok (:edges w) (:next-id w) c) true), hx :- (= (Nat.beq (cleanup-id c) x) true)]
             (crow-sub w c (f c) (hr c) (hs c) hq))
           (fn [c :- CleanupRow, hq :- (= (crow-ok (:edges w) (:next-id w) c) true), hx :- (= (Nat.beq (cleanup-id c) x) false)] hq)
           (:cleanup w) h2))
  (exact (refs-not-edges-intro _ (well-formed-cleanup-upd w x f (refs-not-edges-well-formed w h)) r)))

;; ---- the rows of a new cleanup entry are references to existing non-edge rows

(a/theorem nz-mem [p :- Nat, y :- Nat] (=> (List.Mem y (nz p)) (= y p))
  (intro hm)
  (cases hz (Nat.beq p 0))
  (case [true] (simp only [nz hz] at hm) (cases hm))
  (case [false] (simp only [nz hz] at hm) (cases hm) (rfl) (rename_i hm2) (cases hm2)))

(a/theorem su-ok [w :- World, x :- Nat, y :- Nat]
  (=> (= (tbl-all (srow-ok (:edges w) (:next-id w)) (:scopes w)) true) (List.Mem y (scope-up w x))
      (= (ref-ok-k (:edges w) (:next-id w) y) true))
  (intros hs hm)
  (cases hf (scope-find w x))
  (case [none] (simp only [scope-up hf] at hm) (cases hm))
  (case [some sc]
    (simp only [scope-up hf] at hm)
    (have e := (nz-mem _ y hm))
    (have so := (tbl-all-mem ScopeRow (srow-ok (:edges w) (:next-id w)) sc (:scopes w) hs (tbl-find-mem ScopeRow scope-id x sc (:scopes w) hf)))
    (simp only [srow-ok] at so) (rw [e]) (exact so)))

(a/theorem reach-l-sound [fuel :- (List Nat), succ :- (=> Nat (List Nat)), roots :- (List Nat), y :- Nat]
  (=> (= (reach-mem y (:visited (reach-run-l fuel succ roots))) true) (Reach succ roots y))
  (intro h)
  (have e := (reach-run-l-eq fuel succ roots))
  (exact (reach-run-sound _ succ roots y (Eq.trans (congrArg (fn [q :- ReachResult] (reach-mem y (:visited q))) (Eq.symm e)) h))))

(a/theorem anc-ok [w :- World, s :- Nat]
  (=> (= (tbl-all (srow-ok (:edges w) (:next-id w)) (:scopes w)) true)
      (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) (scope-ancestors w s)) true))
  (intro hs)
  (apply all-of-mem-r) (intros y hy)
  (simp only [scope-ancestors] at hy)
  (have rc := (reach-l-sound _ (scope-up w) (scope-up w s) y hy))
  (cases rc)
  (case [root hm] (exact (su-ok w s y hs hm)))
  (case [step x hx hm] (exact (su-ok w x y hs hm))))

(a/theorem mem-reach [y :- Nat, xs :- (List Nat)] (=> (List.Mem y xs) (= (reach-mem y xs) true))
  (intro h) (exact (Iff.mpr (reach-mem-iff y xs) h)))

(a/theorem scan-has [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), y :- Nat, xs :- (List A)]
  (=> (= (reach-mem y (tbl-scan idf p xs)) true) (= (tbl-has idf y xs) true))
  (intro h) (rw [← (nat-mem-ids A idf y xs)]) (exact (scan-ids-mem A idf p y xs h)))

(a/theorem sub-ok [w :- World, s :- Nat]
  (=> (= (well-formed w) true) (= (ref-ok-k (:edges w) (:next-id w) s) true)
      (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) (scope-subtree w s)) true))
  (intros h hs0)
  (apply all-of-mem-r) (intros y hy)
  (simp only [scope-subtree] at hy)
  (have rc := (reach-l-sound _ (child-scopes w) (nz s) y hy))
  (cases rc)
  (case [root hm] (rw [(nz-mem s y hm)]) (exact hs0))
  (case [step x hx hm]
    (exact (scope-ref-ok w y h (scan-has ScopeRow scope-id (parent-is x) y (:scopes w) (mem-reach y _ hm))))))

(a/theorem tbl-find-has-mem [w :- World, r :- RunRow] (=> (List.Mem r (:runs w)) (= (tbl-has run-id (:id r) (:runs w)) true))
  (intro hm) (rw [← (nat-mem-ids RunRow run-id (:id r) (:runs w))]) (exact (mem-ids-has RunRow run-id r (:runs w) hm)))

(a/theorem crows-ok [w :- World, r :- RunRow]
  (=> (= (refs-not-edges w) true) (List.Mem r (:runs w))
      (And (= (ref-ok-k (:edges w) (:next-id w) (:id r)) true) (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) (cleanup-rows-of w r)) true)))
  (intros h hm)
  (have hs := (refs-not-edges-well-formed w h))
  (have p := (esk-parts _ _ _ _ _ _ (refs-not-edges-rest-of w h)))
  (have rr := (tbl-all-mem RunRow (rrow-ok (:edges w) (:next-id w)) r (:runs w) (And.left (And.right p)) hm))
  (simp only [rrow-ok run-stored tbl-all Bool.and_eq_true] at rr)
  (have id1 := (run-ref-ok w (:id r) hs (tbl-find-has-mem w r hm)))
  (have a1 := (anc-ok w (:scope r) (And.right (And.right p))))
  (have s1 := (sub-ok w (:scope r) hs (And.left rr)))
  (have t1 (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) (tbl-scan task-id (task-owned-in (scope-subtree w (:scope r))) (:tasks w))) true))
  (apply all-of-mem-r) (intros y hy) (exact (task-ref-ok w y hs (scan-has TaskRow task-id _ y (:tasks w) hy)))
  (have x1 (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) (tbl-scan source-id (source-owned-in (scope-subtree w (:scope r))) (:sources w))) true))
  (apply all-of-mem-r) (intros y hy) (exact (source-ref-ok w y hs (scan-has SourceRow source-id _ y (:sources w) hy)))
  (have c1 (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) (cleanup-rows-of w r)) true))
  (simp only [cleanup-rows-of rows-of-sub tbl-all-nat-app a1 s1 t1 x1 Bool.and_self])
  (exact (And.intro id1 c1)))

;; ---- creation sites

(a/theorem edge-fresh-absent [w :- World, y :- Nat]
  (=> (= (well-formed w) true) (<= (:next-id w) y) (= (tbl-has edge-id y (:edges w)) false))
  (intros h hy)
  (cases hc (tbl-has edge-id y (:edges w)))
  (case [false] (rfl))
  (case [true]
    (have hb := (ids-below-of w h))
    (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
    (have hm (= (nat-mem y (tbl-ids edge-id (:edges w))) true)) (rw [nat-mem-ids]) (exact hc)
    (have r := (all-nat-mem (id-in-range (:next-id w)) y _ (And.left (And.right (And.right (And.right (And.right (And.right hb)))))) hm))
    (simp only [id-in-range Bool.and_eq_true Nat.blt_eq] at r)
    (have l := (And.right r)) (omega)))

(a/theorem ref-ok-up [es :- (List EdgeRow), n :- Nat, m :- Nat, y :- Nat]
  (=> (<= n m) (= (ref-ok-k es n y) true) (= (ref-ok-k es m y) true))
  (intros hn h) (exact (ref-ok-mono es es n m y (esub-refl n es) hn h)))

(a/theorem refs-not-edges-add-run-scope [w :- World, of :- Nat, ep :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (ref-ok-k (:edges w) (:next-id w) of) true) (= (ref-ok-k (:edges w) (:next-id w) parent) true)
      (= (refs-not-edges w) true) (= (refs-not-edges (add-run-scope w of ep parent ei)) true))
  (intros ho hp h)
  (have hs := (refs-not-edges-well-formed w h))
  (have p := (esk-parts _ _ _ _ _ _ (refs-not-edges-rest-of w h)))
  (have le2 (<= (:next-id w) (+ (+ (:next-id w) 1) 1))) (omega)
  (have m (forall [y :- Nat] (=> (= (ref-ok-k (:edges w) (:next-id w) y) true) (= (ref-ok-k (:edges w) (+ (+ (:next-id w) 1) 1) y) true))))
  (intros y hy) (exact (ref-ok-up _ _ _ y le2 hy))
  (have s1 (= (ref-ok-k (:edges w) (+ (+ (:next-id w) 1) 1) (+ (:next-id w) 1)) true))
  (have na := (edge-fresh-absent w (+ (:next-id w) 1) hs (Nat.le_succ _)))
  (have lt (= (Nat.blt (+ (:next-id w) 1) (+ (+ (:next-id w) 1) 1)) true)) (simp only [Nat.blt_eq]) (omega)
  (simp only [ref-ok-k na lt Bool.not_false Bool.and_self])
  (have rr (= (rrow-ok (:edges w) (+ (+ (:next-id w) 1) 1) (new-run-row (:next-id w) of ep (+ (:next-id w) 1) ei)) true))
  (simp only [rrow-ok run-stored new-run-row fin-refs tbl-all s1 (m of ho) Bool.and_self List.append])
  (have sr (= (srow-ok (:edges w) (+ (+ (:next-id w) 1) 1) (new-scope-row (+ (:next-id w) 1) parent)) true))
  (simp only [srow-ok new-scope-row]) (exact (m parent hp))
  (have r (= (refs-not-edges-rest (add-run-scope w of ep parent ei)) true))
  (simp only [refs-not-edges-rest add-run-scope bump scope-ins run-ins set-next-id set-scopes set-runs tbl-ins])
  (exact (esk-intro _ _ _ _ _ _
           (tbl-all-mono CleanupRow (crow-ok (:edges w) (:next-id w)) (crow-ok (:edges w) (+ (+ (:next-id w) 1) 1))
             (crow-mono _ _ _ _ m) (:cleanup w) (And.left p))
           (all-cons RunRow (rrow-ok (:edges w) (+ (+ (:next-id w) 1) 1)) _ _ rr
             (tbl-all-mono RunRow (rrow-ok (:edges w) (:next-id w)) (rrow-ok (:edges w) (+ (+ (:next-id w) 1) 1))
               (fn [q :- RunRow, hq :- (= (rrow-ok (:edges w) (:next-id w) q) true)] (tbl-all-mono Nat _ _ m (run-stored q) hq)) (:runs w) (And.left (And.right p))))
           (all-cons ScopeRow (srow-ok (:edges w) (+ (+ (:next-id w) 1) 1)) _ _ sr
             (tbl-all-mono ScopeRow (srow-ok (:edges w) (:next-id w)) (srow-ok (:edges w) (+ (+ (:next-id w) 1) 1))
               (fn [q :- ScopeRow, hq :- (= (srow-ok (:edges w) (:next-id w) q) true)] (m (:parent q) hq)) (:scopes w) (And.right (And.right p))))
           (tbl-all-mono ForkRow (frow-ok (:edges w) (:next-id w)) _ (frow-mono _ _ _ _ m) (:forks w)
             (esk-fparts _ _ _ _ _ _ (refs-not-edges-rest-of w h)))))
  (exact (refs-not-edges-intro _ (well-formed-add-run-scope w of ep parent ei hs) r)))

;; C1c stage B: own's marker (id = next-id, owner a scope row) is a pair of references
(a/theorem refs-not-edges-fork-ins-own [w :- World, m :- Nat, s :- Nat]
  (=> (= (ref-ok-k (:edges w) (:next-id w) s) true) (= (refs-not-edges w) true)
      (= (refs-not-edges (bump (fork-ins w (ForkRow.mk (:next-id w) m s)))) true))
  (intros hsr h)
  (have hs := (refs-not-edges-well-formed w h))
  (have p := (esk-parts _ _ _ _ _ _ (refs-not-edges-rest-of w h)))
  (have le (<= (:next-id w) (+ (:next-id w) 1))) (omega)
  (have mm (forall [y :- Nat] (=> (= (ref-ok-k (:edges w) (:next-id w) y) true) (= (ref-ok-k (:edges w) (+ (:next-id w) 1) y) true))))
  (intros y hy) (exact (ref-ok-up _ _ _ y le hy))
  (have s0 (= (ref-ok-k (:edges w) (+ (:next-id w) 1) (:next-id w)) true))
  (have na := (edge-fresh-absent w (:next-id w) hs (Nat.le_refl _)))
  (have lt (= (Nat.blt (:next-id w) (+ (:next-id w) 1)) true)) (simp only [Nat.blt_eq]) (omega)
  (simp only [ref-ok-k na lt Bool.not_false Bool.and_self])
  (have fr (= (frow-ok (:edges w) (+ (:next-id w) 1) (ForkRow.mk (:next-id w) m s)) true))
  (simp only [frow-ok s0 (mm s hsr) Bool.and_self])
  (have r (= (refs-not-edges-rest (bump (fork-ins w (ForkRow.mk (:next-id w) m s)))) true))
  (simp only [refs-not-edges-rest bump fork-ins set-next-id set-forks tbl-ins])
  (exact (esk-intro _ _ _ _ _ _
           (tbl-all-mono CleanupRow (crow-ok (:edges w) (:next-id w)) (crow-ok (:edges w) (+ (:next-id w) 1))
             (crow-mono _ _ _ _ mm) (:cleanup w) (And.left p))
           (tbl-all-mono RunRow (rrow-ok (:edges w) (:next-id w)) (rrow-ok (:edges w) (+ (:next-id w) 1))
             (fn [q :- RunRow, hq :- (= (rrow-ok (:edges w) (:next-id w) q) true)] (tbl-all-mono Nat _ _ mm (run-stored q) hq)) (:runs w) (And.left (And.right p)))
           (tbl-all-mono ScopeRow (srow-ok (:edges w) (:next-id w)) (srow-ok (:edges w) (+ (:next-id w) 1))
             (fn [q :- ScopeRow, hq :- (= (srow-ok (:edges w) (:next-id w) q) true)] (mm (:parent q) hq)) (:scopes w) (And.right (And.right p)))
           (all-cons ForkRow (frow-ok (:edges w) (+ (:next-id w) 1)) _ _ fr
             (tbl-all-mono ForkRow (frow-ok (:edges w) (:next-id w)) _ (frow-mono _ _ _ _ mm) (:forks w)
               (esk-fparts _ _ _ _ _ _ (refs-not-edges-rest-of w h))))))
  (exact (refs-not-edges-intro _ (well-formed-fork-ins-fresh w (ForkRow.mk (:next-id w) m s) (rfl) hs) r)))

(a/theorem refs-not-edges-cleanup-set [w :- World, rid :- Nat, rows :- (List Nat)]
  (=> (= (ref-ok-k (:edges w) (:next-id w) rid) true) (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) rows) true)
      (= (refs-not-edges w) true) (= (refs-not-edges (cleanup-set w rid rows)) true))
  (intros hr hrows h)
  (have p := (esk-parts _ _ _ _ _ _ (refs-not-edges-rest-of w h)))
  (have c1 (= (crow-ok (:edges w) (:next-id w) (CleanupRow.mk rid rows)) true)) (simp only [crow-ok hr hrows Bool.and_self])
  (have r (= (refs-not-edges-rest (cleanup-set w rid rows)) true))
  (simp only [refs-not-edges-rest cleanup-set cleanup-ins cleanup-del set-cleanup tbl-ins])
  (exact (esk-intro _ _ _ _ _ _ (all-cons CleanupRow _ _ _ c1 (all-del-same CleanupRow _ cleanup-id rid (:cleanup w) (And.left p)))
           (And.left (And.right p)) (And.right (And.right p)) (esk-fparts _ _ _ _ _ _ (refs-not-edges-rest-of w h))))
  (exact (refs-not-edges-intro _ (well-formed-cleanup-set w rid rows (refs-not-edges-well-formed w h)) r)))

;; ---- the bundle

(def ESB (mk-bundle 'refs-not-edges [] "refs-not-edges-"
           {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (run-stored r))) 4]
            'well-formed-scope-upd ['(fn [s :- ScopeRow] (Eq.refl (:parent s))) 4]}))
(swap! (:renames ESB) assoc 'well-formed-parts 'refs-not-edges-parts 'well-formed-run-upd 'refs-not-edges-run-upd 'well-formed-scope-upd 'refs-not-edges-scope-upd)
(defpart ESB :reads '[cleanup edges forks next-id runs scopes])
(prim! ESB 'well-formed-bump '(refs-not-edges-rest-mw w (bump w) (esub-refl (:next-id w) (:edges w)) (Nat.le_succ _) (rfl) (rfl) (rfl) (rfl) R))
(prim! ESB 'well-formed-source-ins-fresh '(refs-not-edges-rest-mw w (bump (source-ins w r)) (esub-refl (:next-id w) (:edges w)) (Nat.le_succ _) (rfl) (rfl) (rfl) (rfl) R))
(prim! ESB 'well-formed-resource-ins-fresh '(refs-not-edges-rest-mw w (bump (resource-ins w r)) (esub-refl (:next-id w) (:edges w)) (Nat.le_succ _) (rfl) (rfl) (rfl) (rfl) R))
(prim! ESB 'well-formed-act-ins-fresh '(refs-not-edges-rest-mw w (bump (act-ins w r)) (esub-refl (:next-id w) (:edges w)) (Nat.le_succ _) (rfl) (rfl) (rfl) (rfl) R))
(prim! ESB 'well-formed-task-ins-fresh '(refs-not-edges-rest-mw w (bump (task-ins w r)) (esub-refl (:next-id w) (:edges w)) (Nat.le_succ _) (rfl) (rfl) (rfl) (rfl) R))
(prim! ESB 'well-formed-comp-ins-fresh '(refs-not-edges-rest-mw w (bump (comp-ins w r)) (esub-refl (:next-id w) (:edges w)) (Nat.le_succ _) (rfl) (rfl) (rfl) (rfl) R))
(prim! ESB 'well-formed-edge-upd '(refs-not-edges-rest-mw w (edge-upd w x f) (esub-upd (:next-id w) x f hid (:edges w)) (Nat.le_refl _) (rfl) (rfl) (rfl) (rfl) R))
(prim! ESB 'well-formed-drop-cred-edges '(refs-not-edges-rest-mw w (drop-cred-edges w a) (esub-filter (:next-id w) (cred-ne a) (:edges w)) (Nat.le_refl _) (rfl) (rfl) (rfl) (rfl) R))
(prim! ESB 'well-formed-drop-act '(refs-not-edges-rest-mw w (drop-act w a) (esub-filter (:next-id w) (cred-ne a) (:edges w)) (Nat.le_refl _) (rfl) (rfl) (rfl) (rfl) R))
(prim! ESB 'well-formed-drop-edges '(refs-not-edges-rest-mw w (drop-edges w p) (esub-filter (:next-id w) p (:edges w)) (Nat.le_refl _) (rfl) (rfl) (rfl) (rfl) R))
(prim! ESB 'well-formed-insert-edge-fresh
  '(refs-not-edges-rest-mw w (insert-edge-fresh w e) (esub-ins (:next-id w) (edge-set-marked false (edge-set-id (:next-id w) e)) (rfl) (:edges w)) (Nat.le_succ _) (rfl) (rfl) (rfl) (rfl) R))
(prim! ESB 'well-formed-remove-edge '(refs-not-edges-rest-remove-edge w x R))
(prim! ESB 'well-formed-mark-edge '(refs-not-edges-rest-mark-edge w x R))
(prim! ESB 'well-formed-unmark-edge '(refs-not-edges-rest-unmark-edge w x R))
(prim! ESB 'well-formed-run-del '(refs-not-edges-rest-run-del w x R))
(prim! ESB 'well-formed-scope-del '(refs-not-edges-rest-scope-del w x R))
(prim! ESB 'well-formed-cleanup-del '(refs-not-edges-rest-cleanup-del w x R))
(prim! ESB 'well-formed-filter-world '(refs-not-edges-rest-filter-world w K R))
(prim! ESB 'well-formed-fork-del '(refs-not-edges-rest-fork-del w x R))
;; refs-not-edges on the generic tree (spindel.v2.pres.tree): its table; its own proofs follow
(def ^:private esb-run-fns   ; row functions under which a run's stored refs only shrink, with the lemma
  '{run-fin-pop run-fin-pop-sub run-fin-exit run-fin-exit-sub run-fin-pop-end run-fin-pop-end-sub
    run-unres run-unres-sub run-drop-fins run-drop-fins-sub})
(defn- row-lemma [F lem] (if (seq? F) (apply list lem (rest F)) lem))
(tree/part! ESB
  ;; ---- the part's own proofs (content: the new references are existing non-edge rows)
  :over '{well-formed-t-own            refs-not-edges-t-own              ; own: the marker's scope exists
          well-formed-cleanup-set      refs-not-edges-cleanup-set        ; a cleanup entry whose refs exist
          well-formed-cancel-run-local refs-not-edges-cancel-run-local   ; T14: the entry's rows, read before the cancel
          well-formed-retire-after     refs-not-edges-retire-after       ; T13's entry: the retired run's rows
          well-formed-spawn-rows       refs-not-edges-spawn-rows         ; T4: the task and its scope parent exist
          well-formed-start-raw        refs-not-edges-start-raw          ; T5: the computation exists
          well-formed-new-run-of       refs-not-edges-new-run-of         ; T11: same
          well-formed-dispatch-raw     refs-not-edges-dispatch-raw       ; T11: carries "the computation exists" (comp-exists)
          well-formed-t-finally-enter  refs-not-edges-t-finally-enter    ; a pushed region stores no refs
          well-formed-arm-raw          refs-not-edges-arm-raw            ; the armed run stores its new resource
          well-formed-t-detach         refs-not-edges-t-detach           ; the new parent is an open scope
          well-formed-t-open-scope     refs-not-edges-t-open-scope}      ; the parent is the current scope
  ;; ---- sites: a run or cleanup row whose stored refs only shrink, by the row function's lemma
  :sites (merge (tree/row-sites 'well-formed-run-upd esb-run-fns
                  (fn [F] (list 'refs-not-edges-run-upd-m 'w 'x F 'hf (row-lemma F (esb-run-fns (if (seq? F) (first F) F))) 'h0)))
                (tree/row-sites 'well-formed-cleanup-upd '#{cleanup-drop}
                  (fn [F] (list 'refs-not-edges-cleanup-upd-m 'w 'x F '(fn [c :- CleanupRow] (Eq.refl (:run c))) (row-lemma F 'cleanup-drop-sub) 'h0))))
  ;; ---- facts from the path: the cancelled run is a row; the started or dispatched computation
  ;; exists; a cleanup entry's refs are existing non-edge rows
  :ctx '{well-formed-cancel-run-local [(List.Mem r (:runs w))]
         well-formed-start-raw        [(= (comp-has w (:id c)) true)]
         well-formed-new-run-of       [(= (comp-has w (:id c)) true)]
         well-formed-dispatch-raw     [(= (comp-has w (:id c)) true)]
         well-formed-cleanup-set      [(= (ref-ok-k (:edges w) (:next-id w) rid) true) (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) rows) true)]}
  :pass '{well-formed-job-apply {well-formed-cancel-run-local [(tbl-find-mem RunRow run-id rid r (:runs w) hf)]}   ; run-find found it
          well-formed-t5-start        {well-formed-start-raw [(find-comp-has w cid c hc)]}                                 ; comp-find found it
          well-formed-t11-dispatch       {well-formed-dispatch-raw [(find-comp-has w cid c hc)]}})
(a/theorem refs-not-edges-t-own [w :- World, s :- Nat, m :- Nat]
  (=> (= (refs-not-edges w) true) (= (refs-not-edges (:world (t-own w s m))) true))
  (intro h)
  (cases ho (own-ok w s))
  (case [false] (simp only [t-own ho refuse]) (exact h))
  (case [true]
    (simp only [t-own ho accept])
    (exact (refs-not-edges-fork-ins-own w m s (scope-ref-ok w s (refs-not-edges-well-formed w h) (And.right (And.right (own-ok-parts w s ho)))) h))))

;; ---- T14's local part: the entry's rows are read from the world before the cancel

(a/theorem esub-trans [n :- Nat, a :- (List EdgeRow), b :- (List EdgeRow), c :- (List EdgeRow)]
  (=> (edges-sub n a b) (edges-sub n b c) (edges-sub n a c))
  (intros h1 h2) (intros y hy hc) (exact (h1 y hy (h2 y hy hc))))

(a/theorem drop-fold-sub [n :- Nat, ids :- (List Nat)]
  (forall [w :- World] (And (edges-sub n (:edges w) (:edges (nat-fold drop-act w ids))) (= (:next-id (nat-fold drop-act w ids)) (:next-id w))))
  (induction ids)
  (case [nil] (intro w) (exact (And.intro (esub-refl n (:edges w)) (rfl))))
  (case [cons hd t ih]
    (intro w)
    (have p := (ih (drop-act w hd)))
    (have s1 (edges-sub n (:edges w) (:edges (drop-act w hd)))) (exact (esub-filter n (cred-ne hd) (:edges w)))
    (have s2 := (esub-trans n (:edges w) (:edges (drop-act w hd)) _ s1 (And.left p)))
    (have e2 (= (:next-id (drop-act w hd)) (:next-id w))) (rfl)
    (exact (And.intro s2 (Eq.trans (And.right p) e2)))))

(a/theorem rc-fold-same [ids :- (List Nat)]
  (forall [w :- World] (And (= (:edges (nat-fold res-cancel w ids)) (:edges w)) (= (:next-id (nat-fold res-cancel w ids)) (:next-id w))))
  (induction ids)
  (case [nil] (intro w) (exact (And.intro (rfl) (rfl))))
  (case [cons hd t ih]
    (intro w)
    (have p := (ih (res-cancel w hd)))
    (have e1 (= (:edges (res-cancel w hd)) (:edges w))) (rfl)
    (have e2 (= (:next-id (res-cancel w hd)) (:next-id w))) (rfl)
    (exact (And.intro (Eq.trans (And.left p) e1) (Eq.trans (And.right p) e2)))))

(tree/restate! ESB '[well-formed-cancel-debtor well-formed-cancel-res well-formed-cancel-acts])
(a/theorem refs-not-edges-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
  (=> (List.Mem r (:runs w)) (= (refs-not-edges w) true) (= (refs-not-edges (cancel-run-local w r rep)) true))
  (intros hm h)
  (simp only [cancel-run-local])
  (have cr := (crows-ok w r h hm))
  (have e1 := (refs-not-edges-cancel-res _ r (refs-not-edges-cancel-acts _ (:id r) (refs-not-edges-run-upd w (:id r) run-cancel-row run-cancel-row-id (fn [q :- RunRow] (Eq.refl (run-stored q))) h))))
  (have d := (drop-fold-sub (:next-id w) (tbl-scan act-id (act-of-run (:id r)) (:acts (run-upd w (:id r) run-cancel-row))) (run-upd w (:id r) run-cancel-row)))
  (have rc := (rc-fold-same (:resources r) (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r))))
  (have sub (edges-sub (:next-id w) (:edges w) (:edges (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r))))
  (simp only [cancel-res (And.left rc)]) (exact (And.left d))
  (have nx (= (:next-id (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r)) (:next-id w)))
  (simp only [cancel-res (And.right rc)]) (exact (And.right d))
  (have m (forall [y :- Nat] (=> (= (ref-ok-k (:edges w) (:next-id w) y) true)
                                 (= (ref-ok-k (:edges (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r))
                                              (:next-id (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r)) y) true))))
  (intros y hy) (rw [nx]) (exact (ref-ok-mono _ _ _ _ y sub (Nat.le_refl _) hy))
  (exact (refs-not-edges-cancel-debtor rep _ r
           (refs-not-edges-cleanup-set _ (:id r) (cleanup-rows-of w r) (m (:id r) (And.left cr))
             (tbl-all-mono Nat _ _ m (cleanup-rows-of w r) (And.right cr)) e1))))

;; ---- run rows: stored refs only shrink (pop, unres) or gain none (push a region with no refs)

(a/theorem stored-sub [r :- RunRow, r2 :- RunRow]
  (=> (= (:scope r2) (:scope r)) (= (:of r2) (:of r))
      (forall [y :- Nat] (=> (= (reach-mem y (:resources r2)) true) (= (reach-mem y (:resources r)) true)))
      (forall [y :- Nat] (=> (= (reach-mem y (fin-refs (:finalizers r2))) true) (= (reach-mem y (fin-refs (:finalizers r))) true)))
      (forall [y :- Nat] (=> (= (reach-mem y (run-stored r2)) true) (= (reach-mem y (run-stored r)) true))))
  (intros hs ho hr hf y hy)
  (simp only [run-stored reach-mem-cons reach-mem-append hs ho Bool.or_eq_true] at hy)
  (simp only [run-stored reach-mem-cons reach-mem-append Bool.or_eq_true])
  (cases hy)
  (case [inl h1] (exact (Or.inl h1)))
  (case [inr h2]
    (cases h2)
    (case [inl h3] (exact (Or.inr (Or.inl h3))))
    (case [inr h4]
      (cases h4)
      (case [inl h5] (exact (Or.inr (Or.inr (Or.inl (hr y h5))))))
      (case [inr h6] (exact (Or.inr (Or.inr (Or.inr (hf y h6)))))))))

(a/theorem fins-tail-sub [fs :- (List Finalizer), y :- Nat]
  (=> (= (reach-mem y (fin-refs (fins-tail fs))) true) (= (reach-mem y (fin-refs fs)) true))
  (intro h)
  (cases fs)
  (case [nil] (simp only [fins-tail fin-refs] at h) (exact h))
  (case [cons hd t] (simp only [fins-tail] at h) (simp only [fin-refs reach-mem-append h Bool.or_true])))

(a/theorem nat-del-sub [z :- Nat, xs :- (List Nat), y :- Nat]
  (=> (= (reach-mem y (nat-del z xs)) true) (= (reach-mem y xs) true))
  (induction xs)
  (case [nil] (intro h) (simp only [nat-del] at h) (exact h))
  (case [cons hd t ih]
    (intro h)
    (cases hz (Nat.beq hd z))
    (case [true] (simp only [nat-del hz] at h) (simp only [reach-mem-cons (ih h) Bool.or_true]))
    (case [false]
      (simp only [nat-del hz reach-mem-cons Bool.or_eq_true] at h)
      (simp only [reach-mem-cons Bool.or_eq_true])
      (cases h)
      (case [inl h1] (exact (Or.inl h1)))
      (case [inr h2] (exact (Or.inr (ih h2)))))))

(a/theorem self-sub [xs :- (List Nat), y :- Nat] (=> (= (reach-mem y xs) true) (= (reach-mem y xs) true)) (intro h) (exact h))

(a/theorem run-fin-pop-sub [r :- RunRow, y :- Nat] (=> (= (reach-mem y (run-stored (run-fin-pop r))) true) (= (reach-mem y (run-stored r)) true))
  (exact (stored-sub r (run-fin-pop r) (rfl) (rfl) (self-sub (:resources r)) (fins-tail-sub (:finalizers r)) y)))
(a/theorem fins-exit-sub [ei :- Nat, fs :- (List Finalizer), y :- Nat]
  (=> (= (reach-mem y (fin-refs (fins-exit (Finalizer.mk 1 ei (List.nil Nat)) fs))) true) (= (reach-mem y (fin-refs fs)) true))
  (intro h)
  (cases fs)
  (case [nil] (simp only [fins-exit fin-refs] at h) (exact h))
  (case [cons hd t] (simp only [fins-exit fin-refs reach-mem-append reach-mem Bool.false_or] at h)
    (simp only [fin-refs reach-mem-append h Bool.or_true])))
(a/theorem run-fin-exit-sub [r :- RunRow, y :- Nat] (=> (= (reach-mem y (run-stored (run-fin-exit r))) true) (= (reach-mem y (run-stored r)) true))
  (have hf (forall [y2 :- Nat] (=> (= (reach-mem y2 (fin-refs (:finalizers (run-fin-exit r)))) true)
                                   (= (reach-mem y2 (fin-refs (:finalizers r))) true))))
  (intros y2 h2) (simp only [run-fin-exit fin-mark] at h2)
  (exact (fins-exit-sub (:effect-index r) (:finalizers r) y2 h2))
  (exact (stored-sub r (run-fin-exit r) (rfl) (rfl) (self-sub (:resources r)) hf y)))
(a/theorem run-fin-pop-end-sub [r :- RunRow, y :- Nat] (=> (= (reach-mem y (run-stored (run-fin-pop-end r))) true) (= (reach-mem y (run-stored r)) true))
  (exact (stored-sub r (run-fin-pop-end r) (rfl) (rfl) (self-sub (:resources r)) (fins-tail-sub (:finalizers r)) y)))
(a/theorem run-drop-fins-sub [r :- RunRow, y :- Nat] (=> (= (reach-mem y (run-stored (run-drop-fins r))) true) (= (reach-mem y (run-stored r)) true))
  (have hf (forall [y2 :- Nat] (=> (= (reach-mem y2 (fin-refs (:finalizers (run-drop-fins r)))) true)
                                   (= (reach-mem y2 (fin-refs (:finalizers r))) true))))
  (intros y2 h2) (simp only [run-drop-fins fin-refs reach-mem] at h2) (cases h2)
  (exact (stored-sub r (run-drop-fins r) (rfl) (rfl) (self-sub (:resources r)) hf y)))
(a/theorem run-unres-sub [z :- Nat, r :- RunRow, y :- Nat] (=> (= (reach-mem y (run-stored (run-unres z r))) true) (= (reach-mem y (run-stored r)) true))
  (exact (stored-sub r (run-unres z r) (rfl) (rfl) (nat-del-sub z (:resources r)) (self-sub (fin-refs (:finalizers r))) y)))
(a/theorem run-fin-push-sub [f0 :- Nat, ei :- Nat, r :- RunRow, y :- Nat]
  (=> (= (reach-mem y (run-stored (run-fin-push (Finalizer.mk f0 ei (List.nil Nat)) r))) true) (= (reach-mem y (run-stored r)) true))
  (have hf (forall [y2 :- Nat] (=> (= (reach-mem y2 (fin-refs (:finalizers (run-fin-push (Finalizer.mk f0 ei (List.nil Nat)) r)))) true)
                                   (= (reach-mem y2 (fin-refs (:finalizers r))) true))))
  (intros y2 h2) (simp only [run-fin-push fin-refs reach-mem-append reach-mem Bool.false_or] at h2) (exact h2)
  (exact (stored-sub r _ (rfl) (rfl) (self-sub (:resources r)) hf y)))
(a/theorem cleanup-drop-sub [z :- Nat, c :- CleanupRow, y :- Nat] (=> (= (reach-mem y (:rows (cleanup-drop z c))) true) (= (reach-mem y (:rows c)) true))
  (intro h) (simp only [cleanup-drop] at h) (exact (nat-del-sub z (:rows c) y h)))

;; ---- ESB overrides: the new references are existing non-edge rows

(a/theorem tsp-ok [w :- World, owner :- Nat]
  (=> (= (well-formed w) true) (= (ref-ok-k (:edges w) (:next-id w) (task-scope-parent w owner)) true))
  (intro h)
  (cases hs (scope-has w owner))
  (case [false] (simp only [task-scope-parent hs]) (exact (ref-ok-zero w h)))
  (case [true] (simp only [task-scope-parent hs]) (exact (scope-ref-ok w owner h hs))))

(a/theorem has-ins-head [A :- Type, idf :- (=> A Nat), r :- A, xs :- (List A)] (= (tbl-has idf (idf r) (tbl-ins r xs)) true)
  (simp only [tbl-ins tbl-has Nat.beq_refl]))

(a/theorem refs-not-edges-spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat), loc :- Bool]
  (=> (= (refs-not-edges w) true) (= (refs-not-edges (spawn-rows w owner inputs loc)) true))
  (intro h)
  (simp only [spawn-rows])
  (have h1 := (refs-not-edges-task-ins-fresh w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc) (rfl) h))
  (have s1 := (refs-not-edges-well-formed _ h1))
  (have o1 := (task-ref-ok _ (:next-id w) s1 (has-ins-head TaskRow task-id (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc) (:tasks w))))
  (have p0 := (tsp-ok w owner (refs-not-edges-well-formed w h)))
  (have p1 (= (ref-ok-k (:edges w) (+ (:next-id w) 1) (task-scope-parent w owner)) true)) (exact (ref-ok-up _ _ _ _ (Nat.le_succ _) p0))
  (exact (refs-not-edges-add-run-scope _ (:next-id w) 0 (task-scope-parent w owner) 0 o1 p1 h1)))

(a/theorem refs-not-edges-start-raw [w :- World, c :- CompRow]
  (=> (= (comp-has w (:id c)) true) (= (refs-not-edges w) true) (= (refs-not-edges (start-raw w c)) true))
  (intros hc h)
  (simp only [start-raw])
  (exact (refs-not-edges-comp-upd _ (:id c) (comp-start-row (:next-id w)) (comp-start-row-id (:next-id w)) (comp-start-row-pending (:next-id w))
           (refs-not-edges-add-run-scope w (:id c) (start-epoch c) 0 0 (comp-ref-ok w (:id c) (refs-not-edges-well-formed w h) hc) (ref-ok-zero w (refs-not-edges-well-formed w h)) h))))
(a/theorem refs-not-edges-new-run-of [w :- World, c :- CompRow, ei :- Nat]
  (=> (= (comp-has w (:id c)) true) (= (refs-not-edges w) true) (= (refs-not-edges (new-run-of w c ei)) true))
  (intros hc h)
  (simp only [new-run-of])
  (exact (refs-not-edges-comp-upd _ (:id c) (comp-set-run (:next-id w)) (comp-set-run-id (:next-id w)) (comp-set-run-pending (:next-id w))
           (refs-not-edges-add-run-scope w (:id c) (:epoch c) 0 ei (comp-ref-ok w (:id c) (refs-not-edges-well-formed w h) hc) (ref-ok-zero w (refs-not-edges-well-formed w h)) h))))

(tree/restate! ESB '[well-formed-cancel-pred well-formed-cut-suffix well-formed-consume-entry])
(a/theorem refs-not-edges-dispatch-raw [w :- World, c :- CompRow]
  (=> (= (comp-has w (:id c)) true) (= (refs-not-edges w) true) (= (refs-not-edges (dispatch-raw w c)) true))
  (intros hc h)
  (have h1 := (refs-not-edges-cancel-pred w c h))
  (have k1 := (comp-exists-cancel-pred (:id c) w c (comp-exists-intro (:id c) w (refs-not-edges-well-formed w h) hc)))
  (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
  (simp only [dispatch-raw he])
  (exact (refs-not-edges-new-run-of _ c 0 (comp-exists-rest-of (:id c) _ (comp-exists-cut-suffix (:id c) _ (:id c) false 0 0 k1))
           (refs-not-edges-cut-suffix _ (:id c) false 0 0 h1)))
  (simp only [dispatch-raw he])
  (exact (refs-not-edges-new-run-of _ c _
           (comp-exists-rest-of (:id c) _ (comp-exists-consume-entry (:id c) _ e (comp-exists-cut-suffix (:id c) _ (:id c) true (:at e) (:id e) k1)))
           (refs-not-edges-consume-entry _ e (refs-not-edges-cut-suffix _ (:id c) true (:at e) (:id e) h1)))))
(a/theorem refs-not-edges-retire-after [w :- World, rid :- Nat]
  (=> (= (refs-not-edges w) true) (= (refs-not-edges (retire-after w rid)) true))
  (intro h)
  (cases hr (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [retire-after hr]) (exact h)
  (cases ht (retirable r))
  (have p := (find-run-mem w rid r hr))
  (have cr := (crows-ok w r h (And.left p)))
  (rw [(And.right p)] at cr)
  (simp only [retire-after hr ht]) (exact (refs-not-edges-cleanup-set w rid _ (And.left cr) (And.right cr) h))
  (simp only [retire-after hr ht]) (exact h))

(a/theorem refs-not-edges-t-finally-enter [w :- World, st :- Nat]
  (=> (= (refs-not-edges w) true) (= (refs-not-edges (:world (t-finally-enter w st))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-enter ht refuse]) (exact h)
  (cases hg (run-normal r))
  (simp only [t-finally-enter ht hg refuse]) (exact h)
  (simp only [t-finally-enter ht hg accept])
  (exact (refs-not-edges-run-upd-m w (:id r) (run-fin-push (Finalizer.mk 0 (:effect-index r) (List.nil Nat))) (run-fin-push-id _)
           (run-fin-push-sub 0 (:effect-index r)) h)))

(a/theorem refs-not-edges-run-upd-plus [w :- World, x :- Nat, f :- (=> RunRow RunRow), z :- Nat,
                             hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                             hs :- (forall [r :- RunRow, y :- Nat] (=> (= (reach-mem y (run-stored (f r))) true)
                                                                       (= (Bool.or (Nat.beq y z) (reach-mem y (run-stored r))) true)))]
  (=> (= (ref-ok-k (:edges w) (:next-id w) z) true) (= (refs-not-edges w) true) (= (refs-not-edges (run-upd w x f)) true))
  (intros hz h)
  (have r (= (refs-not-edges-rest (run-upd w x f)) true))
  (simp only [refs-not-edges-rest run-upd set-runs])
  (apply (refs-not-edges-rest-sets w _ _ _ _ (refs-not-edges-rest-of w h) (self-imp _) (self-imp _) _ (self-imp _)))
  (intro h2)
  (apply (tbl-all-upd RunRow run-id x f (rrow-ok (:edges w) (:next-id w)) (rrow-ok (:edges w) (:next-id w)) _ _ (:runs w) h2))
  (intros q hq hx)
  (simp only [rrow-ok] at hq) (simp only [rrow-ok])
  (apply all-of-mem-r) (intros y hy)
  (have o := (hs q y hy))
  (simp only [Bool.or_eq_true] at o)
  (cases o)
  (case [inl h1] (have e (= y z)) (exact (Nat.eq_of_beq_eq_true h1)) (rw [e]) (exact hz))
  (case [inr h3] (exact (all-reach-mem _ y _ hq h3)))
  (intros q hq hx) (exact hq)
  (exact (refs-not-edges-intro _ (well-formed-run-upd w x f hf (refs-not-edges-well-formed w h)) r)))

(a/theorem run-arm-plus [z :- Nat, r :- RunRow, y :- Nat]
  (=> (= (reach-mem y (run-stored (run-arm z r))) true) (= (Bool.or (Nat.beq y z) (reach-mem y (run-stored r))) true))
  (intro hy)
  (simp only [run-stored run-arm reach-mem-cons reach-mem-append Bool.or_eq_true] at hy)
  (simp only [run-stored reach-mem-cons reach-mem-append Bool.or_eq_true])
  (cases hy)
  (case [inl h1] (exact (Or.inr (Or.inl h1))))
  (case [inr h2]
    (cases h2)
    (case [inl h3] (exact (Or.inr (Or.inr (Or.inl h3)))))
    (case [inr h4]
      (cases h4)
      (case [inl h5]
        (cases h5)
        (case [inl h6] (exact (Or.inl h6)))
        (case [inr h7] (exact (Or.inr (Or.inr (Or.inr (Or.inl h7)))))))
      (case [inr h8] (exact (Or.inr (Or.inr (Or.inr (Or.inr h8)))))))))

(a/theorem refs-not-edges-arm-raw [w :- World, r :- RunRow, kind :- Nat]
  (=> (= (refs-not-edges w) true) (= (refs-not-edges (arm-raw w r kind)) true))
  (intro h)
  (simp only [arm-raw])
  (have h1 := (refs-not-edges-resource-ins-fresh w (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed) (rfl) h))
  (have z1 := (res-ref-ok _ (:next-id w) (refs-not-edges-well-formed _ h1) (has-ins-head ResRow resource-id (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed) (:res w))))
  (exact (refs-not-edges-run-upd-plus _ (:id r) (run-arm (:next-id w)) (:next-id w) (run-arm-run-id _) (run-arm-plus (:next-id w)) z1 h1)))

(a/theorem refs-not-edges-scope-reparent [w :- World, x :- Nat, p :- Nat]
  (=> (= (ref-ok-k (:edges w) (:next-id w) p) true) (= (refs-not-edges w) true) (= (refs-not-edges (scope-upd w x (scope-set-parent p))) true))
  (intros hp h)
  (have r (= (refs-not-edges-rest (scope-upd w x (scope-set-parent p))) true))
  (simp only [refs-not-edges-rest scope-upd set-scopes])
  (apply (refs-not-edges-rest-sets w _ _ _ _ (refs-not-edges-rest-of w h) (self-imp _) (self-imp _) (self-imp _)))
  (intro h2)
  (exact (tbl-all-upd ScopeRow scope-id x (scope-set-parent p) (srow-ok (:edges w) (:next-id w)) (srow-ok (:edges w) (:next-id w))
           (fn [s :- ScopeRow, hq :- (= (srow-ok (:edges w) (:next-id w) s) true), hx :- (= (Nat.beq (scope-id s) x) true)] hp)
           (fn [s :- ScopeRow, hq :- (= (srow-ok (:edges w) (:next-id w) s) true), hx :- (= (Nat.beq (scope-id s) x) false)] hq)
           (:scopes w) h2))
  (exact (refs-not-edges-intro _ (well-formed-scope-upd w x (scope-set-parent p) (scope-set-parent-id p) (refs-not-edges-well-formed w h)) r)))

(a/theorem open-has [w :- World, s :- Nat] (=> (= (scope-open-at w s) true) (= (tbl-has scope-id s (:scopes w)) true))
  (intro h)
  (cases hf (scope-find w s))
  (case [none] (simp only [scope-open-at hf] at h) (cases h))
  (case [some sc] (exact (tbl-find-has ScopeRow scope-id s sc (:scopes w) hf))))

(tree/restate! ESB '[well-formed-remove-if-empty])
(a/theorem refs-not-edges-t-detach [w :- World, k :- Nat, s :- Nat]
  (=> (= (refs-not-edges w) true) (= (refs-not-edges (:world (t-detach w k s))) true))
  (intro h)
  (cases hf (task-find w k)) (case' [some t]) (case' [none])
  (simp only [t-detach hf refuse]) (exact h)
  (cases hg (detach-ok w t s))
  (simp only [t-detach hf hg refuse]) (exact h)
  (have hg2 := hg) (simp only [detach-ok Bool.and_eq_true] at hg2)
  (have p1 := (scope-ref-ok w s (refs-not-edges-well-formed w h) (open-has w s (And.left (And.right (And.right hg2))))))
  (simp only [t-detach hf hg accept remove-empty-at detach-move])
  (have h1 := (refs-not-edges-task-upd w k (task-set-owner s) (task-set-owner-id s) h))
  (have h2 := (refs-not-edges-scope-reparent (task-upd w k (task-set-owner s)) (task-run-scope w t) s p1 h1))
  (exact (refs-not-edges-remove-if-empty _ _ h2)))

;; ---- open-scope: the parent is the current scope

(a/theorem max-ok [p :- (=> Nat Bool), xs :- (List Nat)]
  (forall [m :- Nat] (=> (= (p m) true) (= (tbl-all p xs) true) (= (p (nat-max m xs)) true)))
  (induction xs)
  (case [nil] (intros m hm h) (simp only [nat-max]) (exact hm))
  (case [cons hd t ih]
    (intros m hm h)
    (simp only [tbl-all Bool.and_eq_true] at h)
    (simp only [nat-max])
    (cases hb (Nat.blt m hd))
    (case [false] (simp only [hb]) (exact (ih m hm (And.right h))))
    (case [true] (simp only [hb]) (exact (ih hd (And.left h) (And.right h))))))

(a/theorem cur-scope-ok [w :- World, r :- RunRow]
  (=> (= (refs-not-edges w) true) (List.Mem r (:runs w)) (= (ref-ok-k (:edges w) (:next-id w) (cur-scope w r)) true))
  (intros h hm)
  (have hs := (refs-not-edges-well-formed w h))
  (have p := (esk-parts _ _ _ _ _ _ (refs-not-edges-rest-of w h)))
  (have rr := (tbl-all-mem RunRow (rrow-ok (:edges w) (:next-id w)) r (:runs w) (And.left (And.right p)) hm))
  (simp only [rrow-ok run-stored tbl-all Bool.and_eq_true] at rr)
  (have v (= (tbl-all (ref-ok-k (:edges w) (:next-id w))
                      (:visited (reach-run-l (List.cons Nat 0 (List.cons Nat 0 (tbl-ids scope-id (:scopes w))))
                                             (open-explicit-children w) (List.cons Nat (:scope r) (List.nil Nat))))) true))
  (apply all-of-mem-r) (intros y hy)
  (have rc := (reach-l-sound _ _ _ y hy))
  (cases rc)
  (case [root hm2] (cases hm2) (exact (And.left rr)) (rename_i hm3) (cases hm3))
  (case [step x hx hm2] (exact (scope-ref-ok w y hs (scan-has ScopeRow scope-id (open-explicit-child x) y (:scopes w) (mem-reach y _ hm2)))))
  (simp only [cur-scope])
  (exact (max-ok _ _ (:scope r) (And.left rr) v)))

(a/theorem refs-not-edges-scope-ins [w :- World, sr :- ScopeRow]
  (=> (= (scope-id sr) (:next-id w)) (= (ref-ok-k (:edges w) (:next-id w) (:parent sr)) true) (= (refs-not-edges w) true)
      (= (refs-not-edges (bump (scope-ins w sr))) true))
  (intros hi hp h)
  (have p := (esk-parts _ _ _ _ _ _ (refs-not-edges-rest-of w h)))
  (have m (forall [y :- Nat] (=> (= (ref-ok-k (:edges w) (:next-id w) y) true) (= (ref-ok-k (:edges w) (+ (:next-id w) 1) y) true))))
  (intros y hy) (exact (ref-ok-up _ _ _ y (Nat.le_succ _) hy))
  (have r (= (refs-not-edges-rest (bump (scope-ins w sr))) true))
  (simp only [refs-not-edges-rest bump scope-ins set-next-id set-scopes tbl-ins])
  (exact (esk-intro _ _ _ _ _ _
           (tbl-all-mono CleanupRow (crow-ok (:edges w) (:next-id w)) (crow-ok (:edges w) (+ (:next-id w) 1)) (crow-mono _ _ _ _ m) (:cleanup w) (And.left p))
           (tbl-all-mono RunRow (rrow-ok (:edges w) (:next-id w)) (rrow-ok (:edges w) (+ (:next-id w) 1))
             (fn [q :- RunRow, hq :- (= (rrow-ok (:edges w) (:next-id w) q) true)] (tbl-all-mono Nat _ _ m (run-stored q) hq)) (:runs w) (And.left (And.right p)))
           (all-cons ScopeRow (srow-ok (:edges w) (+ (:next-id w) 1)) sr _ (m (:parent sr) hp)
             (tbl-all-mono ScopeRow (srow-ok (:edges w) (:next-id w)) (srow-ok (:edges w) (+ (:next-id w) 1))
               (fn [q :- ScopeRow, hq :- (= (srow-ok (:edges w) (:next-id w) q) true)] (m (:parent q) hq)) (:scopes w) (And.right (And.right p))))
           (tbl-all-mono ForkRow (frow-ok (:edges w) (:next-id w)) _ (frow-mono _ _ _ _ m) (:forks w)
             (esk-fparts _ _ _ _ _ _ (refs-not-edges-rest-of w h)))))
  (exact (refs-not-edges-intro _ (well-formed-scope-ins-fresh w sr hi (refs-not-edges-well-formed w h)) r)))

(a/theorem refs-not-edges-t-open-scope [w :- World, st :- Nat, s :- Nat]
  (=> (= (refs-not-edges w) true) (= (refs-not-edges (:world (t-open-scope w st s))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-open-scope ht refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq s (:next-id w)) (open-ok w r)))
  (simp only [t-open-scope ht hg refuse]) (exact h)
  (have hs (= s (:next-id w))) (simp only [Bool.and_eq_true Nat.beq_eq] at hg) (exact (And.left hg))
  (simp only [t-open-scope ht hg accept])
  (exact (refs-not-edges-scope-ins w (ScopeRow.mk s (cur-scope w r) scope-explicit true) hs
           (cur-scope-ok w r h (tok-run-mem w st r ht)) h)))

(tree/restate! ESB '[well-formed-raw])
(tree/restate! ESB '[well-formed-normalize])

(a/theorem refs-not-edges-rule-r-round [w :- World]
  (=> (= (refs-not-edges w) true) (= (filter-safe (normalize w)) true) (= (refs-not-edges (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (refs-not-edges-filter-world _ (keep-fn (normalize w)) (refs-not-edges-normalize w h) hf)))

(a/theorem refs-not-edges-rule-r-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (refs-not-edges w0) true) (= (rounds-safe-loop fuel w0) true) (= (refs-not-edges (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (refs-not-edges-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (refs-not-edges-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))

(a/theorem refs-not-edges-rule-r [w :- World]
  (=> (= (refs-not-edges w) true) (= (rule-r-safe w) true) (= (refs-not-edges (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (refs-not-edges-rule-r-loop (rule-r-fuel w) w h hs)))

(a/theorem step-refs-not-edges [w :- World, it :- Item]
  (=> (= (refs-not-edges w) true) (= (rule-r-safe (:world (raw w it))) true) (= (refs-not-edges (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (refs-not-edges-rule-r (:world (raw w it)) (refs-not-edges-raw w it h) hs))))

(a/theorem refs-not-edges-empty [] (= (refs-not-edges empty-world) true) (rfl))

;; ===========================================================================
;; Part C. Every activation's run exists and is alive (acts-alive plus P3's `act-run-has`).
;; Companion no-act-of-run x: no activation names run x (carried to a retire's run-del)
;; ===========================================================================

(a/defn ok-act [rs :- (List RunRow), a :- ActRow] Bool (Bool.and (act-run-ok rs a) (act-run-has rs a)))
(a/defn act-runs-alive-rest [w :- World] Bool (tbl-all (ok-act (:runs w)) (:acts w)))
(a/defn act-runs-alive [w :- World] Bool (Bool.and (well-formed w) (act-runs-alive-rest w)))
(a/theorem act-runs-alive-well-formed [w :- World] (=> (= (act-runs-alive w) true) (= (well-formed w) true))
  (intro h) (simp only [act-runs-alive Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem act-runs-alive-rest-of [w :- World] (=> (= (act-runs-alive w) true) (= (act-runs-alive-rest w) true))
  (intro h) (simp only [act-runs-alive Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem act-runs-alive-intro [w :- World] (=> (= (well-formed w) true) (= (act-runs-alive-rest w) true) (= (act-runs-alive w) true))
  (intros h1 h2) (simp only [act-runs-alive h1 h2 Bool.and_self]))
(a/theorem act-runs-alive-parts [w :- World]
  (=> (= (act-runs-alive w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (act-runs-alive-well-formed w h))))

(a/theorem both-left-ok [rs :- (List RunRow), a :- ActRow] (=> (= (ok-act rs a) true) (= (act-run-ok rs a) true))
  (intro h) (simp only [ok-act Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem both-right-ok [rs :- (List RunRow), a :- ActRow] (=> (= (ok-act rs a) true) (= (act-run-has rs a) true))
  (intro h) (simp only [ok-act Bool.and_eq_true] at h) (exact (And.right h)))

(a/theorem act-runs-alive-acts-alive [w :- World] (=> (= (act-runs-alive w) true) (= (acts-alive w) true))
  (intro h) (have r := (act-runs-alive-rest-of w h)) (simp only [act-runs-alive-rest] at r) (simp only [acts-alive])
  (exact (tbl-all-mono ActRow (ok-act (:runs w)) (act-run-ok (:runs w))
           (fn [a :- ActRow, ha :- (= (ok-act (:runs w) a) true)] (both-left-ok (:runs w) a ha)) (:acts w) r)))
(a/theorem act-runs-alive-has [w :- World] (=> (= (act-runs-alive w) true) (= (tbl-all (act-run-has (:runs w)) (:acts w)) true))
  (intro h) (have r := (act-runs-alive-rest-of w h)) (simp only [act-runs-alive-rest] at r)
  (exact (tbl-all-mono ActRow (ok-act (:runs w)) (act-run-has (:runs w))
           (fn [a :- ActRow, ha :- (= (ok-act (:runs w) a) true)] (both-right-ok (:runs w) a ha)) (:acts w) r)))

;; ---- ok-act under run-list changes

(a/theorem ok-act-upd [x :- Nat, f :- (=> RunRow RunRow), hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hal :- (forall [r :- RunRow] (=> (= (run-alive r) true) (= (run-alive (f r)) true))),
                       rs :- (List RunRow), a :- ActRow]
  (=> (= (ok-act rs a) true) (= (ok-act (tbl-upd run-id x f rs) a) true))
  (intro h)
  (simp only [ok-act act-run-ok act-run-has Bool.and_eq_true] at h)
  (have h1 (= (tbl-all (run-ok-for (:run a)) (tbl-upd run-id x f rs)) true))
  (apply (tbl-all-upd RunRow run-id x f (run-ok-for (:run a)) (run-ok-for (:run a)) _ _ rs (And.left h)))
  (intros r hr hx)
  (have e (= (:id (f r)) (:id r))) (exact (hf r))
  (cases hb (Nat.beq (:id r) (:run a)))
  (case [false] (simp only [run-ok-for e hb Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [run-ok-for hb Bool.not_true Bool.false_or] at hr)
    (simp only [run-ok-for e hb (hal r hr) Bool.not_true Bool.false_or]))
  (intros r hr hx) (exact hr)
  (simp only [ok-act act-run-ok act-run-has h1 (tbl-has-upd RunRow run-id x (:run a) f hf rs) (And.right h) Bool.and_self]))

(a/theorem ok-act-free [x :- Nat, f :- (=> RunRow RunRow), hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        rs :- (List RunRow), a :- ActRow]
  (=> (= (act-of-run x a) false) (= (ok-act rs a) true) (= (ok-act (tbl-upd run-id x f rs) a) true))
  (intros hx h)
  (simp only [ok-act act-run-ok act-run-has Bool.and_eq_true] at h)
  (have h1 (= (tbl-all (run-ok-for (:run a)) (tbl-upd run-id x f rs)) true))
  (apply (tbl-all-upd RunRow run-id x f (run-ok-for (:run a)) (run-ok-for (:run a)) _ _ rs (And.left h)))
  (intros r hr hrx)
  (have e (= (:id (f r)) x)) (exact (Eq.trans (hf r) (Nat.eq_of_beq_eq_true hrx)))
  (have hx2 (= (Nat.beq x (:run a)) false)) (simp only [act-of-run] at hx) (exact (Eq.trans (beq-comm x (:run a)) hx))
  (simp only [run-ok-for e hx2 Bool.not_false Bool.true_or])
  (intros r hr hrx) (exact hr)
  (simp only [ok-act act-run-ok act-run-has h1 (tbl-has-upd RunRow run-id x (:run a) f hf rs) (And.right h) Bool.and_self]))

(a/theorem ok-act-del [x :- Nat, rs :- (List RunRow), a :- ActRow]
  (=> (= (act-of-run x a) false) (= (ok-act rs a) true) (= (ok-act (tbl-del run-id x rs) a) true))
  (intros hx h)
  (simp only [ok-act act-run-ok act-run-has Bool.and_eq_true] at h)
  (have hx2 (= (Nat.beq x (:run a)) false)) (simp only [act-of-run] at hx) (exact (Eq.trans (beq-comm x (:run a)) hx))
  (simp only [ok-act act-run-ok act-run-has (tbl-has-del-ne RunRow run-id x (:run a) rs hx2) (And.right h)
              (all-del-same RunRow (run-ok-for (:run a)) run-id x rs (And.left h)) Bool.and_self]))

(a/theorem ok-act-ins [r :- RunRow, rs :- (List RunRow), a :- ActRow]
  (=> (= (Nat.beq (:id r) (:run a)) false) (= (ok-act rs a) true) (= (ok-act (tbl-ins r rs) a) true))
  (intros hne h)
  (simp only [ok-act act-run-ok act-run-has Bool.and_eq_true] at h)
  (simp only [ok-act act-run-ok act-run-has tbl-ins tbl-all tbl-has run-ok-for hne (And.left h) (And.right h) Bool.not_false Bool.true_or Bool.and_self]))

;; ---- world-level primitives

(a/theorem act-runs-alive-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                        hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hal :- (forall [r :- RunRow] (= (run-alive (f r)) (run-alive r)))]
  (=> (= (act-runs-alive w) true) (= (act-runs-alive (run-upd w x f)) true))
  (intro h)
  (have r (= (act-runs-alive-rest (run-upd w x f)) true))
  (simp only [act-runs-alive-rest run-upd set-runs])
  (exact (tbl-all-mono ActRow (ok-act (:runs w)) (ok-act (tbl-upd run-id x f (:runs w)))
           (ok-act-upd x f hf (fn [q :- RunRow, hq :- (= (run-alive q) true)] (Eq.trans (hal q) hq)) (:runs w)) (:acts w) (act-runs-alive-rest-of w h)))
  (exact (act-runs-alive-intro _ (well-formed-run-upd w x f hf (act-runs-alive-well-formed w h)) r)))

(a/theorem act-runs-alive-run-upd-up [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                           hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                           hup :- (forall [r :- RunRow] (= (run-alive (f r)) true))]
  (=> (= (act-runs-alive w) true) (= (act-runs-alive (run-upd w x f)) true))
  (intro h)
  (have r (= (act-runs-alive-rest (run-upd w x f)) true))
  (simp only [act-runs-alive-rest run-upd set-runs])
  (exact (tbl-all-mono ActRow (ok-act (:runs w)) (ok-act (tbl-upd run-id x f (:runs w)))
           (ok-act-upd x f hf (fn [q :- RunRow, hq :- (= (run-alive q) true)] (hup q)) (:runs w)) (:acts w) (act-runs-alive-rest-of w h)))
  (exact (act-runs-alive-intro _ (well-formed-run-upd w x f hf (act-runs-alive-well-formed w h)) r)))

(a/theorem act-runs-alive-run-upd-free [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                             hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r)))]
  (=> (= (tbl-any (act-of-run x) (:acts w)) false) (= (act-runs-alive w) true) (= (act-runs-alive (run-upd w x f)) true))
  (intros hn h)
  (have r (= (act-runs-alive-rest (run-upd w x f)) true))
  (simp only [act-runs-alive-rest run-upd set-runs])
  (exact (tbl-all-mono2 ActRow (bnot-of (act-of-run x)) (ok-act (:runs w)) (ok-act (tbl-upd run-id x f (:runs w)))
           (fn [a :- ActRow, h1 :- (= (bnot-of (act-of-run x) a) true), h2 :- (= (ok-act (:runs w) a) true)]
             (ok-act-free x f hf (:runs w) a (bnot-true _ h1) h2))
           (:acts w) (any-false-all ActRow (act-of-run x) (:acts w) hn) (act-runs-alive-rest-of w h)))
  (exact (act-runs-alive-intro _ (well-formed-run-upd w x f hf (act-runs-alive-well-formed w h)) r)))

(a/theorem act-runs-alive-run-del [w :- World, x :- Nat]
  (=> (= (tbl-any (act-of-run x) (:acts w)) false) (= (act-runs-alive w) true) (= (act-runs-alive (run-del w x)) true))
  (intros hn h)
  (have r (= (act-runs-alive-rest (run-del w x)) true))
  (simp only [act-runs-alive-rest run-del set-runs])
  (exact (tbl-all-mono2 ActRow (bnot-of (act-of-run x)) (ok-act (:runs w)) (ok-act (tbl-del run-id x (:runs w)))
           (fn [a :- ActRow, h1 :- (= (bnot-of (act-of-run x) a) true), h2 :- (= (ok-act (:runs w) a) true)]
             (ok-act-del x (:runs w) a (bnot-true _ h1) h2))
           (:acts w) (any-false-all ActRow (act-of-run x) (:acts w) hn) (act-runs-alive-rest-of w h)))
  (exact (act-runs-alive-intro _ (well-formed-run-del w x (act-runs-alive-well-formed w h)) r)))

(a/theorem act-run-below [w :- World, a :- ActRow]
  (=> (= (well-formed w) true) (= (act-run-has (:runs w) a) true) (= (Nat.beq (:next-id w) (:run a)) false))
  (intros h ha)
  (simp only [act-run-has] at ha)
  (have b := (run-ref-ok w (:run a) h ha))
  (simp only [ref-ok-k Bool.and_eq_true Nat.blt_eq] at b)
  (cases he (Nat.beq (:next-id w) (:run a)))
  (case [false] (rfl))
  (case [true] (have e (= (:next-id w) (:run a))) (exact (Nat.eq_of_beq_eq_true he)) (have l := (And.right b)) (omega)))

(a/theorem act-runs-alive-run-ins-fresh [w :- World, r :- RunRow]
  (=> (= (run-id r) (:next-id w)) (= (act-runs-alive w) true) (= (act-runs-alive (bump (run-ins w r))) true))
  (intros hr h)
  (have hs := (act-runs-alive-well-formed w h))
  (have rr (= (act-runs-alive-rest (bump (run-ins w r))) true))
  (simp only [act-runs-alive-rest bump run-ins set-next-id set-runs])
  (apply (tbl-all-mono ActRow (ok-act (:runs w)) (ok-act (tbl-ins r (:runs w))) _ (:acts w) (act-runs-alive-rest-of w h)))
  (intros a ha)
  (have hb := (act-run-below w a hs (both-right-ok (:runs w) a ha)))
  (have e (= (:id r) (:next-id w))) (exact hr)
  (exact (ok-act-ins r (:runs w) a (Eq.trans (congrArg (fn [n :- Nat] (Nat.beq n (:run a))) e) hb) ha))
  (exact (act-runs-alive-intro _ (well-formed-run-ins-fresh w r hr hs) rr)))

(a/theorem act-runs-alive-act-ins-fresh [w :- World, r :- ActRow]
  (=> (= (act-id r) (:next-id w)) (= (tbl-all (run-ok-for (:run r)) (:runs w)) true) (= (tbl-has run-id (:run r) (:runs w)) true)
      (= (act-runs-alive w) true) (= (act-runs-alive (bump (act-ins w r))) true))
  (intros hi ho hh h)
  (have o (= (ok-act (:runs w) r) true)) (simp only [ok-act act-run-ok act-run-has ho hh Bool.and_self])
  (have rr (= (act-runs-alive-rest (bump (act-ins w r))) true))
  (simp only [act-runs-alive-rest bump act-ins set-next-id set-acts tbl-ins])
  (exact (all-cons ActRow (ok-act (:runs w)) r (:acts w) o (act-runs-alive-rest-of w h)))
  (exact (act-runs-alive-intro _ (well-formed-act-ins-fresh w r hi (act-runs-alive-well-formed w h)) rr)))

(a/theorem act-runs-alive-act-upd [w :- World, x :- Nat, f :- (=> ActRow ActRow),
                        hf :- (forall [c :- ActRow] (= (act-id (f c)) (act-id c))),
                        hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c)))]
  (=> (= (act-runs-alive w) true) (= (act-runs-alive (act-upd w x f)) true))
  (intro h)
  (have rr (= (act-runs-alive-rest (act-upd w x f)) true))
  (simp only [act-runs-alive-rest act-upd set-acts])
  (exact (tbl-all-upd ActRow act-id x f (ok-act (:runs w)) (ok-act (:runs w))
           (fn [c :- ActRow, hc :- (= (ok-act (:runs w) c) true), hx :- (= (Nat.beq (act-id c) x) true)]
             (Eq.trans (congrArg (fn [y :- Nat] (Bool.and (tbl-all (run-ok-for y) (:runs w)) (tbl-has run-id y (:runs w)))) (hr c)) hc))
           (fn [c :- ActRow, hc :- (= (ok-act (:runs w) c) true), hx :- (= (Nat.beq (act-id c) x) false)] hc)
           (:acts w) (act-runs-alive-rest-of w h)))
  (exact (act-runs-alive-intro _ (well-formed-act-upd w x f hf (act-runs-alive-well-formed w h)) rr)))

(a/theorem act-runs-alive-rest-drop-act [w :- World, a :- Nat] (=> (= (act-runs-alive-rest w) true) (= (act-runs-alive-rest (drop-act w a)) true))
  (intro h) (simp only [act-runs-alive-rest drop-act act-del drop-cred-edges comp-upd set-acts set-comps set-edges])
  (simp only [act-runs-alive-rest] at h) (exact (all-del-same ActRow (ok-act (:runs w)) act-id a (:acts w) h)))

(a/theorem act-runs-alive-rest-same [w :- World, w2 :- World] (=> (= (:runs w2) (:runs w)) (= (:acts w2) (:acts w)) (= (act-runs-alive-rest w2) (act-runs-alive-rest w)))
  (intros h1 h2) (simp only [act-runs-alive-rest h1 h2]))
(a/theorem acts-remove-edge [w :- World, x :- Nat] (= (:acts (remove-edge w x)) (:acts w))
  (cases hf (edge-find w x)) (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm comp-upd edge-del set-edges set-comps]))))
(a/theorem acts-mark-edge [w :- World, x :- Nat] (= (:acts (mark-edge w x)) (:acts w))
  (cases hf (edge-find w x)) (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm comp-upd edge-upd set-edges set-comps]))))
(a/theorem acts-unmark-edge [w :- World, x :- Nat] (= (:acts (unmark-edge w x)) (:acts w))
  (cases hf (edge-find w x)) (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm comp-upd edge-upd set-edges set-comps]))))

(a/theorem act-runs-alive-filter-world [w :- World, K :- (=> Nat Bool),
                             hK :- (forall [r :- RunRow] (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (K (:id r)) true)))]
  (=> (= (act-runs-alive w) true) (= (filter-safe-for K w) true) (= (act-runs-alive (filter-world K w)) true))
  (intros h hf)
  (have rr (= (act-runs-alive-rest (filter-world K w)) true))
  (simp only [act-runs-alive-rest filter-world])
  (apply (tbl-all-keep-same ActRow K act-id (ok-act (tbl-keep K run-id (:runs w))) (:acts w)))
  (apply all-of-mem) (intros a hm)
  (have o := (tbl-all-mem ActRow (ok-act (:runs w)) a (:acts w) (act-runs-alive-rest-of w h) hm))
  (simp only [ok-act act-run-ok act-run-has Bool.and_eq_true] at o)
  (cases hfd (tbl-find run-id (:run a) (:runs w)))
  (case [none] (have z := (tbl-find-none-has RunRow run-id (:run a) (:runs w) hfd)) (rw [(And.right o)] at z) (cases z))
  (case [some q]
    (have qm := (tbl-find-mem RunRow run-id (:run a) q (:runs w) hfd))
    (have qi (= (:id q) (:run a))) (exact (tbl-find-id RunRow run-id (:run a) q (:runs w) hfd))
    (have qa := (tbl-all-mem RunRow (run-ok-for (:run a)) q (:runs w) (And.left o) qm))
    (have qi2 (= (Nat.beq (:id q) (:run a)) true)) (rw [qi]) (exact (Nat.beq_refl _))
    (simp only [run-ok-for qi2 Bool.not_true Bool.false_or] at qa)
    (have kq := (hK q qm qa))
    (rw [qi] at kq)
    (have hh (= (tbl-has run-id (:run a) (tbl-keep K run-id (:runs w))) true)) (rw [tbl-has-keep]) (simp only [kq (And.right o) Bool.and_self])
    (simp only [ok-act act-run-ok act-run-has hh (tbl-all-keep-same RunRow K run-id (run-ok-for (:run a)) (:runs w) (And.left o)) Bool.and_self]))
  (exact (act-runs-alive-intro _ (well-formed-filter-world w K (act-runs-alive-well-formed w h) hf) rr)))

;; ---- the companion no-act-of-run x: no activation names run x

(a/theorem bnot-of-false [b :- Bool] (=> (= b false) (= (Bool.not b) true)) (intro h) (simp only [h Bool.not_false]))

(a/defn no-act-of-run-rest [nax :- Nat, w :- World] Bool (Bool.not (tbl-any (act-of-run nax) (:acts w))))
(a/defn no-act-of-run [nax :- Nat, w :- World] Bool (Bool.and (well-formed w) (no-act-of-run-rest nax w)))
(a/theorem no-act-of-run-well-formed [nax :- Nat, w :- World] (=> (= (no-act-of-run nax w) true) (= (well-formed w) true))
  (intro h) (simp only [no-act-of-run Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem no-act-of-run-rest-of [nax :- Nat, w :- World] (=> (= (no-act-of-run nax w) true) (= (no-act-of-run-rest nax w) true))
  (intro h) (simp only [no-act-of-run Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem no-act-of-run-intro [nax :- Nat, w :- World] (=> (= (well-formed w) true) (= (no-act-of-run-rest nax w) true) (= (no-act-of-run nax w) true))
  (intros h1 h2) (simp only [no-act-of-run h1 h2 Bool.and_self]))
(a/theorem no-act-of-run-parts [nax :- Nat, w :- World]
  (=> (= (no-act-of-run nax w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (no-act-of-run-well-formed nax w h))))
(a/theorem no-act-of-run-none [nax :- Nat, w :- World] (=> (= (no-act-of-run nax w) true) (= (tbl-any (act-of-run nax) (:acts w)) false))
  (intro h) (have r := (no-act-of-run-rest-of nax w h)) (simp only [no-act-of-run-rest] at r) (exact (bnot-true _ r)))

(a/theorem any-del-false [A :- Type, p :- (=> A Bool), idf :- (=> A Nat), x :- Nat, xs :- (List A)]
  (=> (= (tbl-any p xs) false) (= (tbl-any p (tbl-del idf x xs)) false))
  (intro h)
  (exact (all-bnot-any A p _ (all-del-same A (bnot-of p) idf x xs (any-false-all A p xs h)))))

(a/theorem no-act-of-run-act-upd [nax :- Nat, w :- World, x :- Nat, f :- (=> ActRow ActRow),
                       hf :- (forall [c :- ActRow] (= (act-id (f c)) (act-id c))),
                       hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c)))]
  (=> (= (no-act-of-run nax w) true) (= (no-act-of-run nax (act-upd w x f)) true))
  (intro h)
  (have n0 := (any-false-all ActRow (act-of-run nax) (:acts w) (no-act-of-run-none nax w h)))
  (have n1 (= (tbl-all (bnot-of (act-of-run nax)) (:acts (act-upd w x f))) true))
  (simp only [act-upd set-acts])
  (exact (tbl-all-upd ActRow act-id x f (bnot-of (act-of-run nax)) (bnot-of (act-of-run nax))
           (fn [c :- ActRow, hc :- (= (bnot-of (act-of-run nax) c) true), hx :- (= (Nat.beq (act-id c) x) true)]
             (Eq.trans (congrArg (fn [y :- Nat] (Bool.not (Nat.beq y nax))) (hr c)) hc))
           (fn [c :- ActRow, hc :- (= (bnot-of (act-of-run nax) c) true), hx :- (= (Nat.beq (act-id c) x) false)] hc)
           (:acts w) n0))
  (have n2 := (all-bnot-any ActRow (act-of-run nax) _ n1))
  (exact (no-act-of-run-intro nax _ (well-formed-act-upd w x f hf (no-act-of-run-well-formed nax w h)) (bnot-of-false _ n2))))

(a/theorem no-act-of-run-rest-same [nax :- Nat, w :- World, w2 :- World] (=> (= (:acts w2) (:acts w)) (= (no-act-of-run-rest nax w2) (no-act-of-run-rest nax w)))
  (intro h) (simp only [no-act-of-run-rest h]))
(a/theorem no-act-of-run-rest-drop-act [nax :- Nat, w :- World, a :- Nat] (=> (= (no-act-of-run-rest nax w) true) (= (no-act-of-run-rest nax (drop-act w a)) true))
  (intro h) (simp only [no-act-of-run-rest] at h)
  (simp only [no-act-of-run-rest drop-act act-del drop-cred-edges comp-upd set-acts set-comps set-edges (any-del-false ActRow (act-of-run nax) act-id a (:acts w) (bnot-true _ h)) Bool.not_false]))

(def NA (mk-bundle 'no-act-of-run '[nax :- Nat] "no-act-of-run-" {'well-formed-act-upd ['(fn [c :- ActRow] (Eq.refl (:run c))) 4]}))
(swap! (:renames NA) assoc 'well-formed-parts 'no-act-of-run-parts 'well-formed-act-upd 'no-act-of-run-act-upd)
(doseq [o '[well-formed-scope-upd well-formed-pub-upd well-formed-source-upd well-formed-resource-upd well-formed-cleanup-upd well-formed-cleanup-del
            well-formed-set-pins well-formed-resource-del well-formed-scope-del well-formed-cleanup-ins well-formed-task-upd well-formed-run-upd well-formed-run-del well-formed-comp-upd
            well-formed-comp-del-unref well-formed-comp-ins-fresh well-formed-run-ins-fresh well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-resource-ins-fresh
            well-formed-scope-ins-fresh well-formed-task-ins-fresh well-formed-bump well-formed-edge-upd well-formed-drop-cred-edges well-formed-drop-edges well-formed-insert-edge-fresh well-formed-fork-del]]
  (prim! NA o nil))
(prim! NA 'well-formed-drop-act '(no-act-of-run-rest-drop-act nax w a R))
(prim! NA 'well-formed-remove-edge '(Eq.trans (no-act-of-run-rest-same nax w (remove-edge w x) (acts-remove-edge w x)) R))
(prim! NA 'well-formed-mark-edge '(Eq.trans (no-act-of-run-rest-same nax w (mark-edge w x) (acts-mark-edge w x)) R))
(prim! NA 'well-formed-unmark-edge '(Eq.trans (no-act-of-run-rest-same nax w (unmark-edge w x) (acts-unmark-edge w x)) R))
(tree/restate! NA '[well-formed-clear-comp-run])
(tree/restate! NA '[well-formed-close-local])

;; ---- the AHA bundle

(def AHA (mk-bundle 'act-runs-alive [] "act-runs-alive-"
           {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (run-alive r))) 4]
            'well-formed-act-upd ['(fn [c :- ActRow] (Eq.refl (:run c))) 4]}))
(swap! (:renames AHA) assoc 'well-formed-parts 'act-runs-alive-parts 'well-formed-run-upd 'act-runs-alive-run-upd 'well-formed-act-upd 'act-runs-alive-act-upd
       'well-formed-run-ins-fresh 'act-runs-alive-run-ins-fresh)
(defpart AHA :reads '[acts runs])
(prim! AHA 'well-formed-drop-act '(act-runs-alive-rest-drop-act w a R))

(a/theorem park-alive [r :- RunRow] (= (run-alive (run-park-row r)) true) (simp [run-alive run-park-row act-parked act-done]))
(a/theorem tick-park-alive [r :- RunRow] (= (run-alive (run-tick-park r)) true) (simp [run-alive run-tick-park act-parked act-done]))

;; act-runs-alive on the generic tree (spindel.v2.pres.tree): its table; its own proofs follow
(tree/part! AHA
  ;; ---- the part's own proofs (content: a run's activations go with it; a new activation names an
  ;; alive run)
  :over '{well-formed-cancel-run-local act-runs-alive-cancel-run-local   ; T14: the cancelled run's activations go with it
          well-formed-retire-run     act-runs-alive-retire-run       ; T13: a done run has no activation (no-act-of-run carries it)
          well-formed-complete-raw     act-runs-alive-complete-raw       ; T12: the completed run has no activation
          well-formed-await-pre        act-runs-alive-await-pre          ; T6: the new activation's run is the awaiting run
          well-formed-take-park        act-runs-alive-take-park}         ; take: same
  ;; ---- sites: resume keeps the run alive (by lemma); a park makes it alive
  :sites '{[well-formed-run-upd run-wake]      (act-runs-alive-run-upd w x run-wake hf run-wake-alive h0)
           [well-formed-run-upd run-park-row]  (act-runs-alive-run-upd-up w x run-park-row hf park-alive h0)
           [well-formed-run-upd run-tick-park] (act-runs-alive-run-upd-up w x run-tick-park hf tick-park-alive h0)}
  ;; ---- facts from the path
  :ctx '{well-formed-complete-raw [(= (tbl-any (act-of-run (:id r)) (:acts w)) false)]   ; no activation names the run
         well-formed-retire-run [(List.Mem r (:runs w)) (= (retirable r) true)]        ; the retired run is a done row
         well-formed-await-pre    [(List.Mem r (:runs w)) (= (run-alive r) true)]        ; the awaiting run is an alive row
         well-formed-take-park    [(List.Mem r (:runs w)) (= (run-alive r) true)]}       ; the parking run, same
  :own '{well-formed-raw      [hga (= (acts-parked w) true)]                                      ; the companion acts-parked, from the step's input,
         well-formed-host-guarded-transition    [hga (= (acts-parked w) true)]                                      ;   down to T12
         well-formed-transition     [hga (= (acts-parked w) true)]
         well-formed-t12-complete      [hga (= (acts-parked w) true)]
         well-formed-arm-park [hm (List.Mem r (:runs w)) hal (= (run-alive r) true)]}    ; Z#55: arm, then park the armed row
  :pass '{well-formed-job-apply  {well-formed-retire-run [(tbl-find-mem RunRow run-id rid r (:runs w) hf) ha]}   ; run-find found it; retirable
          well-formed-t12-complete        {well-formed-complete-raw [(acts-parked-free-of-tok w st r hga ht)]}                         ; acts-parked: the token's run is free
          well-formed-retire-one {well-formed-complete-raw [(retire-r1-noact w r r1 rid hf hf1)]}                    ; retire-pre dropped them
          well-formed-t6-await         {well-formed-await-raw [(And.left (tok-facts w st r ht)) (normal-alive r (await-ok-normal w r ds mode fresh _ hg))]}
          well-formed-t-take     {well-formed-take-park [(And.left (tok-facts w st r ht)) (normal-alive r (bool-and-left _ _ (bool-and-right _ _ hg)))]}
          well-formed-t17-arm        {well-formed-arm-park [(And.left (tok-facts w st r ht)) (normal-alive r (bool-and-left _ _ (bool-and-right _ _ hg)))]}
          well-formed-arm-park   {well-formed-take-park [(arm-raw-mem w r kind hm) hal]}})

;; T14's local part: the cancelled run's activations go with it
(a/theorem ok-act-of [rs :- (List RunRow), a :- ActRow] (=> (= (act-run-ok rs a) true) (= (act-run-has rs a) true) (= (ok-act rs a) true))
  (intros h1 h2) (simp only [ok-act h1 h2 Bool.and_self]))
(a/theorem acts-drop-fold [P :- (=> ActRow Bool), ids :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all P (:acts w)) true)
                           (And (= (tbl-all P (:acts (nat-fold drop-act w ids))) true) (= (:runs (nat-fold drop-act w ids)) (:runs w)))))
  (induction ids)
  (case [nil] (intros w h) (exact (And.intro h (rfl))))
  (case [cons hd t ih]
    (intros w h)
    (have h1 (= (tbl-all P (:acts (drop-act w hd))) true))
    (simp only [drop-act act-del drop-cred-edges comp-upd set-acts set-comps set-edges]) (exact (all-del-same ActRow P act-id hd (:acts w) h))
    (have p := (ih (drop-act w hd) h1))
    (have e2 (= (:runs (drop-act w hd)) (:runs w))) (rfl)
    (exact (And.intro (And.left p) (Eq.trans (And.right p) e2)))))

(a/theorem act-runs-alive-cancel-mid [w :- World, x :- Nat]
  (=> (= (act-runs-alive w) true) (= (act-runs-alive (cancel-acts (run-upd w x run-cancel-row) x)) true))
  (intro h)
  (have hs := (act-runs-alive-well-formed w h))
  (have b := (cancel-acts-cascade-bound w x hs (act-runs-alive-acts-alive w h)))
  (have al := (cascade-bound-acts-alive _ _ b))
  (have hh (= (tbl-all (act-run-has (tbl-upd run-id x run-cancel-row (:runs w))) (:acts (run-upd w x run-cancel-row))) true))
  (simp only [run-upd set-runs])
  (exact (tbl-all-mono ActRow (act-run-has (:runs w)) (act-run-has (tbl-upd run-id x run-cancel-row (:runs w)))
           (fn [a :- ActRow, ha :- (= (act-run-has (:runs w) a) true)]
             (Eq.trans (tbl-has-upd RunRow run-id x (:run a) run-cancel-row run-cancel-row-id (:runs w)) ha))
           (:acts w) (act-runs-alive-has w h)))
  (have p := (acts-drop-fold (act-run-has (tbl-upd run-id x run-cancel-row (:runs w))) (tbl-scan act-id (act-of-run x) (:acts w))
               (run-upd w x run-cancel-row) hh))
  (have hh2 (= (tbl-all (act-run-has (:runs (cancel-acts (run-upd w x run-cancel-row) x))) (:acts (cancel-acts (run-upd w x run-cancel-row) x))) true))
  (simp only [cancel-acts (And.right p)]) (exact (And.left p))
  (simp only [acts-alive] at al)
  (have rr (= (act-runs-alive-rest (cancel-acts (run-upd w x run-cancel-row) x)) true))
  (simp only [act-runs-alive-rest])
  (exact (tbl-all-mono2 ActRow (act-run-ok (:runs (cancel-acts (run-upd w x run-cancel-row) x)))
           (act-run-has (:runs (cancel-acts (run-upd w x run-cancel-row) x)))
           (ok-act (:runs (cancel-acts (run-upd w x run-cancel-row) x)))
           (ok-act-of (:runs (cancel-acts (run-upd w x run-cancel-row) x)))
           (:acts (cancel-acts (run-upd w x run-cancel-row) x)) al hh2))
  (exact (act-runs-alive-intro _ (cascade-bound-well-formed _ _ b) rr)))

(tree/restate! AHA '[well-formed-cancel-debtor well-formed-cleanup-set well-formed-cancel-res])
(a/theorem act-runs-alive-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
  (=> (= (act-runs-alive w) true) (= (act-runs-alive (cancel-run-local w r rep)) true))
  (intro h)
  (simp only [cancel-run-local])
  (exact (act-runs-alive-cancel-debtor rep _ r (act-runs-alive-cleanup-set _ (:id r) _ (act-runs-alive-cancel-res _ r (act-runs-alive-cancel-mid w (:id r) h))))))

;; T13: a retirable run is done, so no activation names it (acts-alive)
(a/theorem done-no-act-one [rs :- (List RunRow), r :- RunRow, a :- ActRow]
  (=> (List.Mem r rs) (= (run-alive r) false) (= (act-run-ok rs a) true) (= (bnot-of (act-of-run (:id r)) a) true))
  (intros hm hd ha)
  (simp only [act-run-ok] at ha)
  (have o := (tbl-all-mem RunRow (run-ok-for (:run a)) r rs ha hm))
  (simp only [run-ok-for hd Bool.or_false] at o)
  (simp only [bnot-of act-of-run])
  (rw [beq-comm]) (simp only [(bnot-true _ o) Bool.not_false]))
(a/theorem done-no-act [w :- World, r :- RunRow]
  (=> (= (act-runs-alive w) true) (List.Mem r (:runs w)) (= (run-alive r) false) (= (tbl-any (act-of-run (:id r)) (:acts w)) false))
  (intros h hm hd)
  (have al := (act-runs-alive-acts-alive w h)) (simp only [acts-alive] at al)
  (apply (all-bnot-any ActRow (act-of-run (:id r)) (:acts w)))
  (exact (tbl-all-mono ActRow (act-run-ok (:runs w)) (bnot-of (act-of-run (:id r)))
           (fn [a :- ActRow, ha :- (= (act-run-ok (:runs w) a) true)] (done-no-act-one (:runs w) r a hm hd ha)) (:acts w) al)))

(a/theorem retirable-dead2 [r :- RunRow] (=> (= (retirable r) true) (= (run-alive r) false))
  (intro h) (simp only [retirable Bool.and_eq_true] at h)
  (have e (= (:act r) act-done)) (exact (Nat.eq_of_beq_eq_true (And.left h)))
  (simp [run-alive e]))

(tree/restate! AHA '[well-formed-cleanup-del well-formed-remove-if-empty well-formed-clear-comp-run well-formed-close-local])
(a/theorem act-runs-alive-retire-run [w :- World, r :- RunRow]
  (=> (List.Mem r (:runs w)) (= (retirable r) true) (= (act-runs-alive w) true) (= (act-runs-alive (retire-run w r)) true))
  (intros hm hr h)
  (simp only [retire-run t13-retire-with-subtree])
  (have n0 := (no-act-of-run-intro (:id r) w (act-runs-alive-well-formed w h) (bnot-of-false _ (done-no-act w r h hm (retirable-dead2 r hr)))))
  (have n1 := (no-act-of-run-close-local (:id r) _ (scope-subtree w (:scope r)) (no-act-of-run-clear-comp-run (:id r) w r n0)))
  (have a1 := (act-runs-alive-close-local _ (scope-subtree w (:scope r)) (act-runs-alive-clear-comp-run w r h)))
  (have a2 := (act-runs-alive-run-del _ (:id r) (no-act-of-run-none (:id r) _ n1) a1))
  (exact (act-runs-alive-remove-if-empty _ (scope-subtree w (:scope r)) (act-runs-alive-cleanup-del _ (:id r) a2))))

(tree/restate! AHA '[well-formed-finalize-if-final well-formed-run-cascade well-formed-retire-after well-formed-complete-body])
(a/theorem act-runs-alive-complete-raw [w :- World, r :- RunRow, res :- RunResult]
  (=> (= (tbl-any (act-of-run (:id r)) (:acts w)) false) (= (act-runs-alive w) true) (= (act-runs-alive (complete-raw w r res)) true))
  (intros hn h)
  (have h0 := (act-runs-alive-run-upd-free w (:id r) run-complete-row run-complete-row-id hn h))
  (simp only [complete-raw])
  (exact (act-runs-alive-finalize-if-final _ (:of r) (act-runs-alive-run-cascade _ _ (act-runs-alive-retire-after _ (:id r) (act-runs-alive-complete-body _ r res h0))))))

;; ---- T6 and take: the new activation's run exists and is alive (the awaiting run)

(a/theorem run-ok-of-mem [w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (tbl-all (run-ok-for (:id r)) (:runs w)) true))
  (intros h hm ha)
  (exact (uniq-all RunRow run-id run-alive r (:runs w) (lit-runs-nodup w h) hm ha)))

(tree/restate! AHA '[well-formed-demand-reactive well-formed-nat-fold])
(a/theorem act-runs-alive-await-pre [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (act-runs-alive w) true) (= (act-runs-alive (await-pre w r ds mode k mine)) true))
  (intros hm hal h)
  (have h1 := (act-runs-alive-run-upd w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (run-alive q))) h))
  (have he (= (act-id (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine))
              (:next-id (run-upd w (:id r) run-tick))))
  (rfl)
  (have o0 := (run-ok-of-mem w r (act-runs-alive-well-formed w h) hm hal))
  (have o1 (= (tbl-all (run-ok-for (:id r)) (:runs (run-upd w (:id r) run-tick))) true))
  (simp only [run-upd set-runs])
  (exact (tbl-all-upd RunRow run-id (:id r) run-tick (run-ok-for (:id r)) (run-ok-for (:id r))
           (fn [q :- RunRow, hq :- (= (run-ok-for (:id r) q) true), hx :- (= (Nat.beq (run-id q) (:id r)) true)] hq)
           (fn [q :- RunRow, hq :- (= (run-ok-for (:id r) q) true), hx :- (= (Nat.beq (run-id q) (:id r)) false)] hq)
           (:runs w) o0))
  (have hh (= (tbl-has run-id (:id r) (:runs (run-upd w (:id r) run-tick))) true))
  (simp only [run-upd set-runs (tbl-has-upd RunRow run-id (:id r) (:id r) run-tick run-tick-run-id (:runs w))])
  (exact (tbl-find-has-mem w r hm))
  (simp only [await-pre])
  (exact (act-runs-alive-nat-fold demand-reactive act-runs-alive-demand-reactive _ _
           (act-runs-alive-act-ins-fresh _ (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine) he o1 hh h1))))

(tree/restate! AHA '[well-formed-insert-edge-checked])
(a/theorem act-runs-alive-take-park [w :- World, r :- RunRow, x :- Nat, k :- Nat]
  (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (act-runs-alive w) true) (= (act-runs-alive (take-park w r x k)) true))
  (intros hm hal h)
  (have o0 := (run-ok-of-mem w r (act-runs-alive-well-formed w h) hm hal))
  (have h1 := (act-runs-alive-act-ins-fresh w (take-act w r k) (rfl) o0 (tbl-find-has-mem w r hm) h))
  (have h2 := (act-runs-alive-insert-edge-checked _ (take-edge r (:next-id w) x) h1))
  (simp only [take-park])
  (exact (act-runs-alive-run-upd-up _ (:id r) run-tick-park run-tick-park-id tick-park-alive h2)))

(tree/restate! AHA '[well-formed-raw])
(tree/restate! AHA '[well-formed-normalize])

(a/theorem act-runs-alive-rule-r-filter [w :- World]
  (=> (= (normalized w) true) (= (act-runs-alive w) true) (= (filter-safe w) true) (= (act-runs-alive (rule-r-filter w)) true))
  (intros hn h hf)
  (rw [rule-r-filter-eq])
  (exact (act-runs-alive-filter-world w (keep-fn w)
           (fn [r :- RunRow, hm :- (List.Mem r (:runs w)), ha :- (= (run-alive r) true)] (keep-of-live w (:id r) (normalized-runs w r hn hm ha)))
           h hf)))

(a/theorem act-runs-alive-rule-r-round [w :- World]
  (=> (= (act-runs-alive w) true) (= (filter-safe (normalize w)) true) (= (act-runs-alive (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (exact (act-runs-alive-rule-r-filter (normalize w) (normalized-ok w (act-runs-alive-well-formed w h) (act-runs-alive-acts-alive w h)) (act-runs-alive-normalize w h) hf)))

(a/theorem act-runs-alive-rule-r-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (act-runs-alive w0) true) (= (rounds-safe-loop fuel w0) true) (= (act-runs-alive (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (act-runs-alive-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (act-runs-alive-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))

(a/theorem act-runs-alive-rule-r [w :- World]
  (=> (= (act-runs-alive w) true) (= (rule-r-safe w) true) (= (act-runs-alive (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (act-runs-alive-rule-r-loop (rule-r-fuel w) w h hs)))

(a/theorem step-act-runs-alive [w :- World, it :- Item]
  (=> (= (acts-parked w) true) (= (act-runs-alive w) true) (= (rule-r-safe (:world (raw w it))) true) (= (act-runs-alive (:world (world-step w it))) true))
  (intros hg h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (act-runs-alive-rule-r (:world (raw w it)) (act-runs-alive-raw w it hg h) hs))))

(a/theorem act-runs-alive-empty [] (= (act-runs-alive empty-world) true) (rfl))

;; ===========================================================================
;; Part D. The reference invariants follow from the bundles; P3 with no hypothesis
;; ===========================================================================

;; ---- edge-sep from refs-not-edges

(a/theorem tbl-all-append [P :- (=> Nat Bool), xs :- (List Nat), ys :- (List Nat)]
  (= (tbl-all P (List.append Nat xs ys)) (Bool.and (tbl-all P xs) (tbl-all P ys)))
  (induction xs)
  (case [nil] (simp only [List.append tbl-all Bool.true_and]))
  (case [cons hd t ih] (simp only [List.append tbl-all ih Bool.and_assoc])))

(a/theorem tbl-find-has-edge [w :- World, e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (tbl-has edge-id (:id e) (:edges w)) true))
  (intro hm) (rw [← (nat-mem-ids EdgeRow edge-id (:id e) (:edges w))]) (exact (mem-ids-has EdgeRow edge-id e (:edges w) hm)))

(a/theorem gather-all [A :- Type, p :- (=> A Bool), f :- (=> A (List Nat)), P :- (=> Nat Bool), xs :- (List A)]
  (=> (= (tbl-all (fn [a :- A] (tbl-all P (f a))) xs) true) (= (tbl-all P (tbl-gather p f xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-gather tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (simp only [tbl-all Bool.and_eq_true] at h)
    (cases hp (p hd))
    (case [false] (simp only [tbl-gather hp]) (exact (ih (And.right h))))
    (case [true] (simp only [tbl-gather hp tbl-all-append (And.left h) (ih (And.right h)) Bool.and_self]))))

(a/theorem anc-all-ok [w :- World, xs :- (List Nat)]
  (=> (= (tbl-all (srow-ok (:edges w) (:next-id w)) (:scopes w)) true)
      (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) (anc-all w xs)) true))
  (intro hs)
  (induction xs)
  (case [nil] (simp only [anc-all tbl-all]))
  (case [cons x t ih] (simp only [anc-all tbl-all-append (anc-ok w x hs) ih Bool.and_self])))

(a/theorem crows-in-ok [w :- World, cs :- (List CleanupRow)]
  (=> (= (tbl-all (rrow-ok (:edges w) (:next-id w)) (:runs w)) true) (= (tbl-all (crow-ok (:edges w) (:next-id w)) cs) true)
      (= (tbl-all (srow-ok (:edges w) (:next-id w)) (:scopes w)) true)
      (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) (cleanup-rows-in w cs)) true))
  (induction cs)
  (case [nil] (intros hr hc hsc) (simp only [cleanup-rows-in tbl-all]))
  (case [cons hd t ih]
    (intros hr hc hsc)
    (simp only [tbl-all Bool.and_eq_true] at hc)
    (have c1 := (And.left hc)) (simp only [crow-ok Bool.and_eq_true] at c1)
    (have o (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) (opt-rows (run-find w (:run hd)))) true))
    (cases hf (run-find w (:run hd)))
    (case [none] (simp only [opt-rows tbl-all]))
    (case [some r]
      (simp only [opt-rows])
      (have rr := (tbl-all-mem RunRow (rrow-ok (:edges w) (:next-id w)) r (:runs w) hr (tbl-find-mem RunRow run-id (:run hd) r (:runs w) hf)))
      (simp only [rrow-ok] at rr) (exact rr))
    (have b (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) (cleanup-base w hd)) true))
    (simp only [cleanup-base tbl-all tbl-all-append (And.left c1) (And.right c1) o Bool.and_self])
    (have aa := (anc-all-ok w (cleanup-base w hd) hsc))
    (simp only [cleanup-rows-in cleanup-contrib anc-close tbl-all-append b aa (ih hr (And.right hc) hsc) Bool.and_self])))

(a/theorem fork-keep-ok [es :- (List EdgeRow), n :- Nat, fs :- (List ForkRow)]
  (=> (= (tbl-all (frow-ok es n) fs) true) (= (tbl-all (ref-ok-k es n) (fork-keep fs)) true))
  (induction fs)
  (case [nil] (intro h) (simp only [fork-keep tbl-all]))
  (case [cons f t ih]
    (intro h) (simp only [tbl-all frow-ok Bool.and_eq_true] at h)
    (simp only [fork-keep tbl-all (And.left (And.left h)) (And.right (And.left h)) (ih (And.right h)) Bool.and_self])))

(a/theorem refs-not-edges-edge-sep [w :- World] (=> (= (refs-not-edges w) true) (= (tbl-all (edge-sep w) (:edges w)) true))
  (intro h)
  (have p := (esk-parts _ _ _ _ _ _ (refs-not-edges-rest-of w h)))
  (have c := (crows-in-ok w (:cleanup w) (And.left (And.right p)) (And.left p) (And.right (And.right p))))
  (have g0 (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) (storage-seeds w (live-list w))) true))
  (simp only [storage-seeds])
  (apply (gather-all RunRow (stored-run (live-list w)) run-refs (ref-ok-k (:edges w) (:next-id w)) (:runs w)))
  (apply (tbl-all-mono RunRow (rrow-ok (:edges w) (:next-id w)) _ _ (:runs w) (And.left (And.right p))))
  (intros r hr) (simp only [rrow-ok run-stored tbl-all tbl-all-append Bool.and_eq_true] at hr) (simp only [run-refs]) (exact (And.right (And.right (And.right hr))))
  (have f0 := (fork-keep-ok (:edges w) (:next-id w) (:forks w) (esk-fparts _ _ _ _ _ _ (refs-not-edges-rest-of w h))))
  (have st0 (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) (storage-gather w (live-list w))) true))
  (simp only [storage-gather tbl-all-append g0 f0 Bool.and_self])
  (have st (= (tbl-all (ref-ok-k (:edges w) (:next-id w)) (storage w)) true))
  (simp only [storage storage-with anc-close tbl-all-append st0 (anc-all-ok w (storage-gather w (live-list w)) (And.right (And.right p))) Bool.and_self])
  (apply all-of-mem) (intros e hm)
  (have he := (tbl-find-has-edge w e hm))
  (have n1 (= (reach-mem (:id e) (cleanup-rows w)) false))
  (cases hc (reach-mem (:id e) (cleanup-rows w)))
  (case [false] (rfl))
  (case [true] (have z := (all-reach-mem _ (:id e) _ c hc)) (simp [ref-ok-k he] at z))
  (have n2 (= (reach-mem (:id e) (storage w)) false))
  (cases hs (reach-mem (:id e) (storage w)))
  (case [false] (rfl))
  (case [true] (have z := (all-reach-mem _ (:id e) _ st hs)) (simp [ref-ok-k he] at z))
  (simp only [edge-sep n1 n2 Bool.not_false Bool.and_self]))

;; ---- the reference invariants of filter-safe-of-refs

(a/theorem dm-dep-active [cs :- (List CompRow), e :- EdgeRow] (=> (= (dm-one cs e) true) (= (dep-active cs e) true))
  (intro h)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dep-active hk Bool.not_false Bool.true_or]))
  (case [true] (simp only [dm-one hk Bool.true_or Bool.not_true Bool.false_or awake] at h) (simp only [dep-active hk Bool.not_true Bool.false_or]) (exact h)))

(a/theorem p3-refs-of [w :- World]
  (=> (= (i7-idle w) true) (= (marks-on-dep w) true) (= (refs-not-edges w) true) (= (act-runs-alive w) true) (= (p3-refs w) true))
  (intros h7 hm he ha)
  (have q := (i7-idle-keys-ok-parts _ _ _ (i7-idle-rest-of w h7)))
  (have d := (tbl-all-mono EdgeRow (dm-one (:comps w)) (dep-active (:comps w)) (dm-dep-active (:comps w)) (:edges w) (And.left (And.right q))))
  (have m := (marks-on-dep-rest-of w hm)) (simp only [marks-on-dep-rest] at m)
  (simp only [p3-refs d (act-runs-alive-has w ha) m (refs-not-edges-edge-sep w he) Bool.and_self]))

;; ---- the round invariant: every Rule R round is filter-safe

(a/defn round-facts [w :- World] Bool (Bool.and (i7-idle w) (Bool.and (marks-on-dep w) (Bool.and (refs-not-edges w) (Bool.and (act-runs-alive w) (tombs-dormant 0 w))))))
(a/theorem round-facts-parts [w :- World]
  (=> (= (round-facts w) true) (And (= (i7-idle w) true) (And (= (marks-on-dep w) true) (And (= (refs-not-edges w) true) (And (= (act-runs-alive w) true) (= (tombs-dormant 0 w) true))))))
  (intro h) (simp only [round-facts Bool.and_eq_true] at h) (exact h))
(a/theorem round-facts-intro [w :- World]
  (=> (= (i7-idle w) true) (= (marks-on-dep w) true) (= (refs-not-edges w) true) (= (act-runs-alive w) true) (= (tombs-dormant 0 w) true) (= (round-facts w) true))
  (intros h1 h2 h3 h4 h5) (simp only [round-facts h1 h2 h3 h4 h5 Bool.and_self]))

(a/theorem round-facts-round [w :- World]
  (=> (= (round-facts w) true) (And (= (filter-safe (normalize w)) true) (= (round-facts (rule-r-round w)) true)))
  (intro h)
  (have p := (round-facts-parts w h))
  (have aa := (act-runs-alive-acts-alive w (And.left (And.right (And.right (And.right p))))))
  (have n7 := (i7-idle-normalize w aa (And.left p)))
  (have nm := (marks-on-dep-normalize w (And.left (And.right p))))
  (have ne := (refs-not-edges-normalize w (And.left (And.right (And.right p)))))
  (have na := (act-runs-alive-normalize w (And.left (And.right (And.right (And.right p))))))
  (have ny := (tombs-dormant-normalize 0 w (rfl) aa (And.right (And.right (And.right (And.right p))))))
  (have nn := (normalized-ok w (i7-idle-well-formed w (And.left p)) aa))
  (have fs := (filter-safe-of-refs (normalize w) (i7-idle-well-formed _ n7) (act-runs-alive-acts-alive _ na) nn (p3-refs-of _ n7 nm ne na) (tombs-dormant-refs-untomb _ ny)))
  (exact (And.intro fs
           (round-facts-intro _ (i7-idle-rule-r-round w aa (And.left p) fs) (marks-on-dep-rule-r-round w (And.left (And.right p)) fs)
             (refs-not-edges-rule-r-round w (And.left (And.right (And.right p))) fs) (act-runs-alive-rule-r-round w (And.left (And.right (And.right (And.right p)))) fs)
             (tombs-dormant-rule-r-round w aa (And.right (And.right (And.right (And.right p)))) fs)))))

(a/theorem rounds-safe-loop-round-facts [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (round-facts w0) true) (= (rounds-safe-loop fuel w0) true)))
  (induction fuel)
  (case [nil] (intros w0 h) (simp only [rounds-safe-loop]) (exact (And.left (round-facts-round w0 h))))
  (case [cons x f ih]
    (intros w0 h)
    (have p := (round-facts-round w0 h))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [true] (simp only [rounds-safe-loop ho (And.left p) Bool.and_self]))
    (case [false] (simp only [rounds-safe-loop ho (And.left p) (ih (rule-r-round w0) (And.right p)) Bool.and_self]))))

(a/theorem rule-r-safe-round-facts [w :- World] (=> (= (round-facts w) true) (= (rule-r-safe w) true))
  (intro h) (simp only [rule-r-safe]) (exact (rounds-safe-loop-round-facts (rule-r-fuel w) w h)))

(a/theorem round-facts-last-input-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (round-facts w0) true) (= (round-facts (last-input-loop fuel w0)) true)))
  (induction fuel)
  (case [nil] (intros w0 h) (simp only [last-input-loop]) (exact h))
  (case [cons x f ih]
    (intros w0 h)
    (cases ho (no-orphans (rule-r-round w0)))
    (case [true] (simp only [last-input-loop ho]) (exact h))
    (case [false] (simp only [last-input-loop ho]) (exact (ih (rule-r-round w0) (And.right (round-facts-round w0 h)))))))

;; ===========================================================================
;; Part E. The combined bundle and the step theorems with no honest hypothesis
;; ===========================================================================

(a/defn chain-start [w :- World] Bool
  (Bool.and (acts-parked w) (Bool.and (i12-ranks w) (Bool.and (i10-task w) (Bool.and (i9-res w) (round-facts w))))))
(a/theorem chain-start-parts [w :- World]
  (=> (= (chain-start w) true) (And (= (acts-parked w) true) (And (= (i12-ranks w) true) (And (= (i10-task w) true) (And (= (i9-res w) true) (= (round-facts w) true))))))
  (intro h) (simp only [chain-start Bool.and_eq_true] at h) (exact h))
(a/theorem chain-start-intro [w :- World]
  (=> (= (acts-parked w) true) (= (i12-ranks w) true) (= (i10-task w) true) (= (i9-res w) true) (= (round-facts w) true) (= (chain-start w) true))
  (intros h1 h2 h3 h4 h5) (simp only [chain-start h1 h2 h3 h4 h5 Bool.and_self]))

(a/theorem chain-start-empty [] (= (chain-start empty-world) true) (rfl))

(a/theorem round-facts-raw [w :- World, it :- Item] (=> (= (chain-start w) true) (= (round-facts (:world (raw w it))) true))
  (intro h)
  (have p := (chain-start-parts w h))
  (have q := (round-facts-parts w (And.right (And.right (And.right (And.right p))))))
  (exact (round-facts-intro _ (i7-idle-raw w it (And.left q)) (marks-on-dep-raw w it (And.left (And.right q))) (refs-not-edges-raw w it (And.left (And.right (And.right q))))
           (act-runs-alive-raw w it (And.left p) (And.left (And.right (And.right (And.right q)))))
           (tombs-dormant-raw 0 w it (And.left q) (And.right (And.right (And.right (And.right q))))))))

;; Theorem (P3): Rule R's filter is edge-safe in every round of every step (rule-r-safe, the honest
;; hypothesis of step-well-formed and the other step theorems, holds)
(a/theorem step-rule-r-safe [w :- World, it :- Item] (=> (= (chain-start w) true) (= (rule-r-safe (:world (raw w it))) true))
  (intro h) (exact (rule-r-safe-round-facts _ (round-facts-raw w it h))))

;; Theorem: the combined bundle is preserved by every step (no hypothesis)
(a/theorem step-chain-start [w :- World, it :- Item] (=> (= (chain-start w) true) (= (chain-start (:world (world-step w it))) true))
  (intro h)
  (have p := (chain-start-parts w h))
  (have q := (round-facts-parts w (And.right (And.right (And.right (And.right p))))))
  (have hs := (step-rule-r-safe w it h))
  (exact (chain-start-intro _ (step-acts w it (And.left p) hs) (step-i12-ranks w it (And.left (And.right p)) hs)
           (step-i10-task w it (And.left p) (And.left (And.right (And.right p))) hs) (step-i9-res w it (And.left (And.right (And.right (And.right p)))) hs)
           (round-facts-intro _ (step-i7-idle w it (And.left p) (And.left q) hs) (step-marks-on-dep w it (And.left (And.right q)) hs)
             (step-refs-not-edges w it (And.left (And.right (And.right q))) hs) (step-act-runs-alive w it (And.left p) (And.left (And.right (And.right (And.right q)))) hs)
             (step-tombs-dormant w it (And.left p) (And.left q) (And.right (And.right (And.right (And.right q)))) hs)))))

;; the headline theorems of the earlier passes, with the bundle in place of the honest hypotheses
(a/theorem step-well-formed-total [w :- World, it :- Item] (=> (= (chain-start w) true) (= (well-formed (:world (world-step w it))) true))
  (intro h) (exact (step-well-formed w it (acts-parked-well-formed w (And.left (chain-start-parts w h))) (step-rule-r-safe w it h))))
(a/theorem step-acts-total [w :- World, it :- Item] (=> (= (chain-start w) true) (= (acts-parked (:world (world-step w it))) true))
  (intro h) (exact (And.left (chain-start-parts _ (step-chain-start w it h)))))
(a/theorem step-rank-total [w :- World, it :- Item] (=> (= (chain-start w) true) (= (i12-ranks (:world (world-step w it))) true))
  (intro h) (exact (And.left (And.right (chain-start-parts _ (step-chain-start w it h))))))
(a/theorem step-ranks-total [w :- World, it :- Item] (=> (= (chain-start w) true) (= (ranks-ok (:world (world-step w it))) true))
  (intro h) (exact (step-ranks w it (And.left (And.right (chain-start-parts w h))) (step-rule-r-safe w it h))))
(a/theorem step-p3-refs [w :- World, it :- Item] (=> (= (chain-start w) true) (= (p3-refs (:world (world-step w it))) true))
  (intro h)
  (have q := (round-facts-parts _ (And.right (And.right (And.right (And.right (chain-start-parts _ (step-chain-start w it h))))))))
  (exact (p3-refs-of _ (And.left q) (And.left (And.right q)) (And.left (And.right (And.right q))) (And.left (And.right (And.right (And.right q)))))))
(a/theorem step-normalized-p3 [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) true) (= (chain-start w) true) (= (normalized (:world (world-step w it))) true))
  (intros ha h) (exact (step-normalized-acts-parked w it ha (And.left (chain-start-parts w h)) (step-rule-r-safe w it h))))
(a/theorem step-i4-p3 [w :- World, it :- Item, r :- RunRow]
  (=> (= (:accepted (raw w it)) true) (= (chain-start w) true)
      (List.Mem r (:runs (:world (world-step w it)))) (= (run-alive r) true)
      (= (in-live (:world (world-step w it)) (:id r)) true))
  (intros ha h hm hr) (exact (step-i4-acts-parked w it r ha (And.left (chain-start-parts w h)) (step-rule-r-safe w it h) hm hr)))
(a/theorem step-lit-i10-task-total [w :- World, it :- Item] (=> (= (chain-start w) true) (= (inv-i10-task (:world (world-step w it))) true))
  (intro h) (have p := (chain-start-parts w h))
  (exact (step-lit-i10-task w it (And.left p) (And.left (And.right (And.right p))) (step-rule-r-safe w it h))))
(a/theorem step-lit-i9-res-total [w :- World, it :- Item] (=> (= (chain-start w) true) (= (lit-i9-res (:world (world-step w it))) true))
  (intro h) (exact (step-lit-i9-res w it (And.left (And.right (And.right (And.right (chain-start-parts w h))))) (step-rule-r-safe w it h))))
(a/theorem step-lit-i7-total [w :- World, it :- Item] (=> (= (chain-start w) true) (= (inv-i7 (:world (world-step w it))) true))
  (intro h) (have p := (chain-start-parts w h))
  (exact (step-lit-i7 w it (And.left p) (And.left (round-facts-parts w (And.right (And.right (And.right (And.right p)))))) (step-rule-r-safe w it h))))

;; ===========================================================================
;; Part F. I5, observe edges: `seen` never exceeds the debtor's version (versions only grow;
;; an observed debtor is never removed while its observe edge is kept)
;; ===========================================================================

(a/defn fv [A :- Type :implicit, idf :- (=> A Nat), m :- (=> A Nat), d :- Nat, xs :- (List A)] Nat
  (match (tbl-find idf d xs) none 0 (some r) (m r)))
(a/defn sver [s :- SourceRow] Nat (:version s))
(a/defn cver [c :- CompRow] Nat (:version c))
(a/defn dvk [ss :- (List SourceRow), cs :- (List CompRow), d :- Nat] Nat
  (if (tbl-has source-id d ss) (fv source-id sver d ss) (fv comp-id cver d cs)))

(a/theorem find-none-of-has [A :- Type, idf :- (=> A Nat), x :- Nat, xs :- (List A)]
  (=> (= (tbl-has idf x xs) false) (= (tbl-find idf x xs) (Option.none A)))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-find]))
  (case [cons hd t ih]
    (intro h)
    (cases hx (Nat.beq (idf hd) x))
    (case [true] (simp [tbl-has hx] at h))
    (case [false] (simp only [tbl-has hx] at h) (simp only [tbl-find hx (ih h)]))))

(a/theorem dv-eq [w :- World, d :- Nat] (= (deb-version w d) (dvk (:sources w) (:comps w) d))
  (cases hs (tbl-has source-id d (:sources w)))
  (case [false]
    (have n := (find-none-of-has SourceRow source-id d (:sources w) hs))
    (cases hc (comp-find w d))
    (case [none] (simp only [deb-version source-find n hc dvk hs fv comp-find]) (simp only [comp-find] at hc) (simp only [hc]))
    (case [some c] (simp only [deb-version source-find n hc dvk hs fv comp-find]) (simp only [comp-find] at hc) (simp only [hc cver])))
  (case [true]
    (cases hf (source-find w d))
    (case [none] (have z := (tbl-find-none-has SourceRow source-id d (:sources w) hf)) (rw [hs] at z) (cases z))
    (case [some s] (simp only [deb-version hf dvk hs fv]) (simp only [source-find] at hf) (simp only [hf sver]))))

;; ---- fv under the table edits

(a/theorem fv-upd [A :- Type, idf :- (=> A Nat), m :- (=> A Nat), x :- Nat, f :- (=> A A),
                   hid :- (forall [r :- A] (= (idf (f r)) (idf r))), hm :- (forall [r :- A] (<= (m r) (m (f r)))),
                   d :- Nat, xs :- (List A)]
  (<= (fv idf m d xs) (fv idf m d (tbl-upd idf x f xs)))
  (induction xs)
  (case [nil] (simp only [fv tbl-upd tbl-find]) (exact (Nat.le_refl 0)))
  (case [cons hd t ih]
    (simp only [fv] at ih)
    (cases hx (Nat.beq (idf hd) x))
    (case [false]
      (cases hd2 (Nat.beq (idf hd) d))
      (case [true] (simp only [fv tbl-upd hx tbl-find hd2]) (exact (Nat.le_refl _)))
      (case [false] (simp only [fv tbl-upd hx tbl-find hd2]) (exact ih)))
    (case [true]
      (have e (= (idf (f hd)) (idf hd))) (exact (hid hd))
      (cases hd2 (Nat.beq (idf hd) d))
      (case [true] (have e2 (= (Nat.beq (idf (f hd)) d) true)) (rw [e]) (exact hd2)
        (simp only [fv tbl-upd hx tbl-find hd2 e2]) (exact (hm hd)))
      (case [false] (have e2 (= (Nat.beq (idf (f hd)) d) false)) (rw [e]) (exact hd2)
        (simp only [fv tbl-upd hx tbl-find hd2 e2]) (exact ih)))))

(a/theorem fv-ins-ne [A :- Type, idf :- (=> A Nat), m :- (=> A Nat), r :- A, d :- Nat, xs :- (List A)]
  (=> (= (Nat.beq (idf r) d) false) (= (fv idf m d (tbl-ins r xs)) (fv idf m d xs)))
  (intro h) (simp only [fv tbl-ins tbl-find h]))

(a/theorem fv-del-ne [A :- Type, idf :- (=> A Nat), m :- (=> A Nat), x :- Nat, d :- Nat, xs :- (List A)]
  (=> (= (Nat.beq x d) false) (= (fv idf m d (tbl-del idf x xs)) (fv idf m d xs)))
  (intro hne)
  (induction xs)
  (case [nil] (simp only [fv tbl-del tbl-find]))
  (case [cons hd t ih]
    (simp only [fv] at ih)
    (cases hx (Nat.beq (idf hd) x))
    (case [true]
      (have e (= (idf hd) x)) (exact (Nat.eq_of_beq_eq_true hx))
      (have hd2 (= (Nat.beq (idf hd) d) false)) (rw [e]) (exact hne)
      (simp only [fv tbl-del hx tbl-find hd2]) (exact ih))
    (case [false]
      (cases hd2 (Nat.beq (idf hd) d))
      (all_goals (simp only [fv tbl-del hx tbl-find hd2]))
      (exact ih))))

(a/theorem fv-keep [A :- Type, idf :- (=> A Nat), m :- (=> A Nat), K :- (=> Nat Bool), d :- Nat, xs :- (List A)]
  (=> (= (K d) true) (= (fv idf m d (tbl-keep K idf xs)) (fv idf m d xs)))
  (intro hk)
  (induction xs)
  (case [nil] (simp only [fv tbl-keep tbl-find]))
  (case [cons hd t ih]
    (simp only [fv] at ih)
    (cases hd2 (Nat.beq (idf hd) d))
    (case [true]
      (have e (= (idf hd) d)) (exact (Nat.eq_of_beq_eq_true hd2))
      (have k2 (= (K (idf hd)) true)) (rw [e]) (exact hk)
      (simp only [fv tbl-keep k2 tbl-find hd2]))
    (case [false]
      (cases k3 (K (idf hd)))
      (all_goals (simp only [fv tbl-keep k3 tbl-find hd2]))
      (all_goals (exact ih)))))

(a/theorem fv-resync [es :- (List EdgeRow), d :- Nat, cs :- (List CompRow)]
  (= (fv comp-id cver d (comps-resync es cs)) (fv comp-id cver d cs))
  (induction cs)
  (case [nil] (simp only [fv comps-resync tbl-find]))
  (case [cons hd t ih]
    (simp only [fv] at ih)
    (cases hd2 (Nat.beq (comp-id hd) d))
    (all_goals (simp only [fv comps-resync tbl-find comp-resync comp-set-pending comp-id cver hd2]))
    (all_goals (simp only [comp-id] at hd2))
    (simp only [hd2]) (exact ih)
    (simp only [hd2])))

;; ---- the bundle i5-seen: every observe edge's seen is at most its debtor's version

(a/defn i5-seen-rest [w :- World] Bool (tbl-all (seen-ok w) (:edges w)))
(a/defn i5-seen [w :- World] Bool (Bool.and (well-formed w) (i5-seen-rest w)))
(a/theorem i5-seen-well-formed [w :- World] (=> (= (i5-seen w) true) (= (well-formed w) true))
  (intro h) (simp only [i5-seen Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem i5-seen-rest-of [w :- World] (=> (= (i5-seen w) true) (= (i5-seen-rest w) true))
  (intro h) (simp only [i5-seen Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem i5-seen-intro [w :- World] (=> (= (well-formed w) true) (= (i5-seen-rest w) true) (= (i5-seen w) true))
  (intros h1 h2) (simp only [i5-seen h1 h2 Bool.and_self]))
(a/theorem i5-seen-parts [w :- World]
  (=> (= (i5-seen w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (i5-seen-well-formed w h))))

;; the debtor's version does not drop from w to w2 (for an observe edge that has seen)
(a/defn dv-le [w :- World, w2 :- World, e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:kind e) ek-observe))
           (Bool.or (Bool.not (:has-seen e)) (Nat.ble (deb-version w (:debtor e)) (deb-version w2 (:debtor e))))))

(a/theorem seen-ok-trans [w :- World, w2 :- World, e :- EdgeRow]
  (=> (= (seen-ok w e) true) (= (dv-le w w2 e) true) (= (seen-ok w2 e) true))
  (intros h1 h2)
  (cases hk (Nat.beq (:kind e) ek-observe))
  (case [false] (simp only [seen-ok hk Bool.not_false Bool.true_or]))
  (case [true]
    (cases hs (:has-seen e))
    (case [false] (simp only [seen-ok hk hs Bool.not_false Bool.true_or Bool.or_true]))
    (case [true]
      (simp only [seen-ok hk hs Bool.not_true Bool.false_or Nat.ble_eq] at h1)
      (simp only [dv-le hk hs Bool.not_true Bool.false_or Nat.ble_eq] at h2)
      (simp only [seen-ok hk hs Bool.not_true Bool.false_or Nat.ble_eq])
      (omega))))

(a/theorem i5-seen-rest-trans [w :- World, w2 :- World]
  (=> (= (:edges w2) (:edges w)) (= (tbl-all (dv-le w w2) (:edges w)) true) (= (i5-seen-rest w) true) (= (i5-seen-rest w2) true))
  (intros he hd h)
  (simp only [i5-seen-rest he])
  (simp only [i5-seen-rest] at h)
  (exact (tbl-all-mono2 EdgeRow (seen-ok w) (dv-le w w2) (seen-ok w2) (seen-ok-trans w w2) (:edges w) h hd)))

(a/theorem dv-le-all [w :- World, w2 :- World, hd :- (forall [d :- Nat] (<= (deb-version w d) (deb-version w2 d))), es :- (List EdgeRow)]
  (= (tbl-all (dv-le w w2) es) true)
  (apply all-of-mem) (intros e hm)
  (have l (= (Nat.ble (deb-version w (:debtor e)) (deb-version w2 (:debtor e))) true)) (simp only [Nat.ble_eq]) (exact (hd (:debtor e)))
  (simp only [dv-le l Bool.or_true]))

(a/theorem dvk-mono [ss :- (List SourceRow), ss2 :- (List SourceRow), cs :- (List CompRow), cs2 :- (List CompRow), d :- Nat]
  (=> (= (tbl-has source-id d ss2) (tbl-has source-id d ss)) (<= (fv source-id sver d ss) (fv source-id sver d ss2))
      (<= (fv comp-id cver d cs) (fv comp-id cver d cs2)) (<= (dvk ss cs d) (dvk ss2 cs2 d)))
  (intros hh h1 h2)
  (cases hs (tbl-has source-id d ss))
  (case [false] (simp only [dvk hs hh]) (exact h2))
  (case [true] (simp only [dvk hs hh]) (exact h1)))

;; ---- version-growing edits of sources and computations

(a/theorem dv-source-upd [w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                          hid :- (forall [s :- SourceRow] (= (source-id (f s)) (source-id s))),
                          hv :- (forall [s :- SourceRow] (<= (sver s) (sver (f s)))), d :- Nat]
  (<= (deb-version w d) (deb-version (source-upd w x f) d))
  (simp only [dv-eq])
  (exact (dvk-mono _ _ _ _ d (tbl-has-upd SourceRow source-id x d f hid (:sources w))
           (fv-upd SourceRow source-id sver x f hid hv d (:sources w)) (Nat.le_refl _))))

(a/theorem dv-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hv :- (forall [c :- CompRow] (<= (cver c) (cver (f c)))), d :- Nat]
  (<= (deb-version w d) (deb-version (comp-upd w x f) d))
  (simp only [dv-eq])
  (exact (dvk-mono _ _ _ _ d (rfl) (Nat.le_refl _) (fv-upd CompRow comp-id cver x f hid hv d (:comps w)))))

(a/theorem i5-seen-source-upd [w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                           hid :- (forall [s :- SourceRow] (= (source-id (f s)) (source-id s))),
                           hv :- (forall [s :- SourceRow] (<= (sver s) (sver (f s))))]
  (=> (= (i5-seen w) true) (= (i5-seen (source-upd w x f)) true))
  (intro h)
  (exact (i5-seen-intro _ (well-formed-source-upd w x f hid (i5-seen-well-formed w h))
           (i5-seen-rest-trans w (source-upd w x f) (rfl) (dv-le-all w (source-upd w x f) (dv-source-upd w x f hid hv) (:edges w)) (i5-seen-rest-of w h)))))

(a/theorem i5-seen-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                         hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                         hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                         hv :- (forall [c :- CompRow] (<= (cver c) (cver (f c))))]
  (=> (= (i5-seen w) true) (= (i5-seen (comp-upd w x f)) true))
  (intro h)
  (exact (i5-seen-intro _ (well-formed-comp-upd w x f hid hp (i5-seen-well-formed w h))
           (i5-seen-rest-trans w (comp-upd w x f) (rfl) (dv-le-all w (comp-upd w x f) (dv-comp-upd w x f hid hv) (:edges w)) (i5-seen-rest-of w h)))))

;; ---- the rest under edge edits and row insertions/deletions

(a/theorem i5-seen-rest-gen [w :- World, w2 :- World]
  (=> (forall [d :- Nat] (<= (deb-version w d) (deb-version w2 d))) (= (tbl-all (seen-ok w) (:edges w2)) true) (= (i5-seen-rest w2) true))
  (intros hd h)
  (simp only [i5-seen-rest])
  (exact (tbl-all-mono2 EdgeRow (seen-ok w) (dv-le w w2) (seen-ok w2) (seen-ok-trans w w2) (:edges w2) h (dv-le-all w w2 hd (:edges w2)))))

(a/theorem dv-same [w :- World, w2 :- World] (=> (= (:sources w2) (:sources w)) (= (:comps w2) (:comps w)) (forall [d :- Nat] (<= (deb-version w d) (deb-version w2 d))))
  (intros h1 h2 d) (simp only [dv-eq h1 h2]) (exact (Nat.le_refl _)))

(a/theorem dv-pend [w :- World, x :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                    hv :- (forall [c :- CompRow] (= (cver (f c)) (cver c))), w2 :- World]
  (=> (= (:sources w2) (:sources w)) (= (:comps w2) (tbl-upd comp-id x f (:comps w))) (forall [d :- Nat] (<= (deb-version w d) (deb-version w2 d))))
  (intros h1 h2 d)
  (simp only [dv-eq h1 h2])
  (exact (dvk-mono _ _ _ _ d (rfl) (Nat.le_refl _) (fv-upd CompRow comp-id cver x f hid (fn [c :- CompRow] (Nat.le_of_eq (Eq.symm (hv c)))) d (:comps w)))))

(a/theorem i5-seen-rest-remove-edge [w :- World, x :- Nat] (=> (= (i5-seen-rest w) true) (= (i5-seen-rest (remove-edge w x)) true))
  (intro h)
  (simp only [i5-seen-rest] at h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm])
      (exact (i5-seen-rest-gen w (edge-del w x) (dv-same w (edge-del w x) (rfl) (rfl)) (all-sub-del EdgeRow (seen-ok w) edge-id x (:edges w) h))))
    (case [true] (simp only [remove-edge hf hm])
      (exact (i5-seen-rest-gen w (comp-upd (edge-del w x) (:creditor e) comp-dec-pending)
               (dv-pend w (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (cver c))) (comp-upd (edge-del w x) (:creditor e) comp-dec-pending) (rfl) (rfl))
               (all-sub-del EdgeRow (seen-ok w) edge-id x (:edges w) h))))))

(a/theorem seen-marked [w :- World, b :- Bool, e :- EdgeRow] (=> (= (seen-ok w e) true) (= (seen-ok w (edge-set-marked b e)) true))
  (intro h) (simp only [seen-ok edge-set-marked] at h) (simp only [seen-ok edge-set-marked]) (exact h))

(a/theorem i5-seen-rest-mark-edge [w :- World, x :- Nat] (=> (= (i5-seen-rest w) true) (= (i5-seen-rest (mark-edge w x)) true))
  (intro h)
  (simp only [i5-seen-rest] at h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false] (simp only [mark-edge hf hm])
      (exact (i5-seen-rest-gen w (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending)
               (dv-pend w (:creditor e) comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (cver c))) (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending) (rfl) (rfl))
               (tbl-all-upd EdgeRow edge-id x (edge-set-marked true) (seen-ok w) (seen-ok w)
                 (fn [d :- EdgeRow, hd :- (= (seen-ok w d) true), hx :- (= (Nat.beq (edge-id d) x) true)] (seen-marked w true d hd))
                 (fn [d :- EdgeRow, hd :- (= (seen-ok w d) true), hx :- (= (Nat.beq (edge-id d) x) false)] hd) (:edges w) h))))))

(a/theorem i5-seen-rest-unmark-edge [w :- World, x :- Nat] (=> (= (i5-seen-rest w) true) (= (i5-seen-rest (unmark-edge w x)) true))
  (intro h)
  (simp only [i5-seen-rest] at h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true] (simp only [unmark-edge hf hm])
      (exact (i5-seen-rest-gen w (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending)
               (dv-pend w (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (cver c))) (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending) (rfl) (rfl))
               (tbl-all-upd EdgeRow edge-id x (edge-set-marked false) (seen-ok w) (seen-ok w)
                 (fn [d :- EdgeRow, hd :- (= (seen-ok w d) true), hx :- (= (Nat.beq (edge-id d) x) true)] (seen-marked w false d hd))
                 (fn [d :- EdgeRow, hd :- (= (seen-ok w d) true), hx :- (= (Nat.beq (edge-id d) x) false)] hd) (:edges w) h))))))

(a/theorem i5-seen-rest-drop-cred [w :- World, a :- Nat] (=> (= (i5-seen-rest w) true) (= (i5-seen-rest (drop-cred-edges w a)) true))
  (intro h) (simp only [i5-seen-rest] at h)
  (exact (i5-seen-rest-gen w (drop-cred-edges w a)
           (dv-pend w a (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (cver c))) (drop-cred-edges w a) (rfl) (rfl))
           (tbl-all-filter EdgeRow (seen-ok w) (cred-ne a) (:edges w) h))))
(a/theorem i5-seen-rest-drop-act [w :- World, a :- Nat] (=> (= (i5-seen-rest w) true) (= (i5-seen-rest (drop-act w a)) true))
  (intro h) (exact (i5-seen-rest-drop-cred w a h)))

(a/theorem i5-seen-rest-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (=> (= (i5-seen-rest w) true) (= (i5-seen-rest (drop-edges w p)) true))
  (intro h) (simp only [i5-seen-rest] at h)
  (have hd (forall [d :- Nat] (<= (deb-version w d) (deb-version (drop-edges w p) d))))
  (intro d) (simp only [dv-eq drop-edges set-comps set-edges dvk fv-resync]) (exact (Nat.le_refl _))
  (exact (i5-seen-rest-gen w (drop-edges w p) hd (tbl-all-filter EdgeRow (seen-ok w) p (:edges w) h))))

;; ---- row insertions and deletions: an edge's debtor exists (well-formed), so it is below the
;; allocator and no fresh row takes its version; a deleted computation has no edge

(a/theorem deb-below [w :- World, e :- EdgeRow]
  (=> (= (well-formed w) true) (List.Mem e (:edges w)) (= (Nat.beq (:next-id w) (:debtor e)) false))
  (intros h hm)
  (have ho := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                (And.left (And.right (well-formed-parts w h))) hm))
  (simp only [edge-ok deb-ok Bool.and_eq_true Bool.or_eq_true] at ho)
  (have r (= (ref-ok-k (:edges w) (:next-id w) (:debtor e)) true))
  (have hd2 := (And.right ho))
  (cases hd2)
  (case [inl h1] (exact (comp-ref-ok w _ h h1)))
  (case [inr h2]
    (cases h2)
    (case [inl h3] (exact (task-ref-ok w _ h h3)))
    (case [inr h4]
      (cases h4)
      (case [inl h5] (exact (source-ref-ok w _ h h5)))
      (case [inr h6] (exact (res-ref-ok w _ h (And.right h6))))))
  (simp only [ref-ok-k Bool.and_eq_true Nat.blt_eq] at r)
  (cases hb (Nat.beq (:next-id w) (:debtor e)))
  (case [false] (rfl))
  (case [true] (have eq (= (:next-id w) (:debtor e))) (exact (Nat.eq_of_beq_eq_true hb)) (have l := (And.right r)) (omega)))

(a/theorem dv-le-edges [w :- World, w2 :- World,
                        hd :- (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (<= (deb-version w (:debtor e)) (deb-version w2 (:debtor e)))))]
  (= (tbl-all (dv-le w w2) (:edges w)) true)
  (apply all-of-mem) (intros e hm)
  (have l (= (Nat.ble (deb-version w (:debtor e)) (deb-version w2 (:debtor e))) true)) (simp only [Nat.ble_eq]) (exact (hd e hm))
  (simp only [dv-le l Bool.or_true]))

(a/theorem i5-seen-comp-ins [w :- World, r :- CompRow]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w))) (= (i5-seen w) true) (= (i5-seen (bump (comp-ins w r))) true))
  (intros hi hp h)
  (have hs := (i5-seen-well-formed w h))
  (have hd (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (<= (deb-version w (:debtor e)) (deb-version (bump (comp-ins w r)) (:debtor e))))))
  (intros e hm)
  (have nb := (deb-below w e hs hm))
  (have ne (= (Nat.beq (comp-id r) (:debtor e)) false)) (rw [hi]) (exact nb)
  (simp only [dv-eq bump comp-ins set-next-id set-comps dvk (fv-ins-ne CompRow comp-id cver r (:debtor e) (:comps w) ne)])
  (exact (Nat.le_refl _))
  (exact (i5-seen-intro _ (well-formed-comp-ins-fresh w r hi hp hs) (i5-seen-rest-trans w (bump (comp-ins w r)) (rfl) (dv-le-edges w (bump (comp-ins w r)) hd) (i5-seen-rest-of w h)))))

(a/theorem i5-seen-source-ins [w :- World, r :- SourceRow]
  (=> (= (source-id r) (:next-id w)) (= (i5-seen w) true) (= (i5-seen (bump (source-ins w r))) true))
  (intros hi h)
  (have hs := (i5-seen-well-formed w h))
  (have hd (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (<= (deb-version w (:debtor e)) (deb-version (bump (source-ins w r)) (:debtor e))))))
  (intros e hm)
  (have nb := (deb-below w e hs hm))
  (have ne (= (Nat.beq (source-id r) (:debtor e)) false)) (rw [hi]) (exact nb)
  (simp only [dv-eq bump source-ins set-next-id set-sources dvk tbl-has-ins ne Bool.false_or (fv-ins-ne SourceRow source-id sver r (:debtor e) (:sources w) ne)])
  (exact (Nat.le_refl _))
  (exact (i5-seen-intro _ (well-formed-source-ins-fresh w r hi hs) (i5-seen-rest-trans w (bump (source-ins w r)) (rfl) (dv-le-edges w (bump (source-ins w r)) hd) (i5-seen-rest-of w h)))))

(a/theorem i5-seen-comp-del [w :- World, x :- Nat]
  (=> (= (unreferenced w x) true) (= (i5-seen w) true) (= (i5-seen (comp-del w x)) true))
  (intros hu h)
  (have hd (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (<= (deb-version w (:debtor e)) (deb-version (comp-del w x) (:debtor e))))))
  (intros e hm)
  (have a := (tbl-all-mem EdgeRow (edge-avoids x) e (:edges w) hu hm))
  (simp only [edge-avoids Bool.and_eq_true] at a)
  (have ne (= (Nat.beq x (:debtor e)) false)) (exact (Eq.trans (beq-comm x (:debtor e)) (bnot-true _ (And.right a))))
  (simp only [dv-eq comp-del set-comps dvk (fv-del-ne CompRow comp-id cver x (:debtor e) (:comps w) ne)])
  (exact (Nat.le_refl _))
  (exact (i5-seen-intro _ (well-formed-comp-del-unref w x hu (i5-seen-well-formed w h)) (i5-seen-rest-trans w (comp-del w x) (rfl) (dv-le-edges w (comp-del w x) hd) (i5-seen-rest-of w h)))))

(a/theorem i5-seen-filter-world [w :- World, K :- (=> Nat Bool)]
  (=> (= (i5-seen w) true) (= (filter-safe-for K w) true) (= (i5-seen (filter-world K w)) true))
  (intros h hf)
  (have hf2 := hf) (simp only [filter-safe-for Bool.and_eq_true] at hf2)
  (have r (= (i5-seen-rest (filter-world K w)) true))
  (have hr := (i5-seen-rest-of w h))
  (simp only [i5-seen-rest] at hr)
  (have b := (tbl-all-mono2 EdgeRow (seen-ok w) (filter-keeps-ends K) (both (seen-ok w) (filter-keeps-ends K))
               (fn [e :- EdgeRow, h1 :- (= (seen-ok w e) true), h2 :- (= (filter-keeps-ends K e) true)] (both-of EdgeRow (seen-ok w) (filter-keeps-ends K) e h1 h2))
               (:edges w) hr (And.left hf2)))
  (simp only [i5-seen-rest filter-world])
  (apply (tbl-all-keep EdgeRow K edge-id (both (seen-ok w) (filter-keeps-ends K)) (seen-ok (filter-world K w)) _ (:edges w) b))
  (intros e hb hk)
  (have s1 := (both-left EdgeRow (seen-ok w) (filter-keeps-ends K) e hb))
  (have f1 := (both-right EdgeRow (seen-ok w) (filter-keeps-ends K) e hb))
  (have hk2 (= (K (:id e)) true)) (exact hk)
  (have f2 (= (Bool.or (Bool.not (K (:id e))) (Bool.and (Bool.or (host-cred e) (K (:creditor e))) (K (:debtor e)))) true)) (exact f1)
  (simp only [hk2 Bool.not_true Bool.false_or Bool.and_eq_true] at f2)
  (have kd := (And.right f2))
  (have l (= (dv-le w (filter-world K w) e) true))
  (have eq (= (deb-version (filter-world K w) (:debtor e)) (deb-version w (:debtor e))))
  (simp only [dv-eq filter-world dvk tbl-has-keep kd Bool.true_and (fv-keep SourceRow source-id sver K (:debtor e) (:sources w) kd)
              (fv-keep CompRow comp-id cver K (:debtor e) (:comps w) kd)])
  (have l2 (= (Nat.ble (deb-version w (:debtor e)) (deb-version (filter-world K w) (:debtor e))) true)) (rw [eq]) (simp only [Nat.ble_eq]) (exact (Nat.le_refl _))
  (simp only [dv-le l2 Bool.or_true])
  (exact (seen-ok-trans w (filter-world K w) e s1 l))
  (exact (i5-seen-intro _ (well-formed-filter-world w K (i5-seen-well-formed w h) hf) r)))

;; ---- edge updates and insertion

(a/structure SK7 [] (hs Bool) (sn Nat))
(a/defn esk7 [e :- EdgeRow] SK7 (SK7.mk (:has-seen e) (:seen e)))

(a/theorem seen-ok-f [w :- World, f :- (=> EdgeRow EdgeRow),
                      hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                      hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                      hsk :- (forall [e :- EdgeRow] (= (esk7 (f e)) (esk7 e))), e :- EdgeRow]
  (=> (= (seen-ok w e) true) (= (seen-ok w (f e)) true))
  (intro h)
  (have e1 (= (:has-seen (f e)) (:has-seen e))) (exact (congrArg (fn [k :- SK7] (:hs k)) (hsk e)))
  (have e2 (= (:seen (f e)) (:seen e))) (exact (congrArg (fn [k :- SK7] (:sn k)) (hsk e)))
  (simp only [seen-ok (hk e) (hd e) e1 e2]) (simp only [seen-ok] at h) (exact h))

(a/theorem i5-seen-edge-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                         hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                         hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                         hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                         hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                         hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e))),
                         hsk :- (forall [e :- EdgeRow] (= (esk7 (f e)) (esk7 e)))]
  (=> (= (i5-seen w) true) (= (i5-seen (edge-upd w x f)) true))
  (intro h)
  (have hr := (i5-seen-rest-of w h)) (simp only [i5-seen-rest] at hr)
  (exact (i5-seen-intro _ (well-formed-edge-upd w x f hid hk hc hd hm (i5-seen-well-formed w h))
           (i5-seen-rest-gen w (edge-upd w x f) (dv-same w (edge-upd w x f) (rfl) (rfl))
             (tbl-all-upd EdgeRow edge-id x f (seen-ok w) (seen-ok w)
               (fn [e :- EdgeRow, he :- (= (seen-ok w e) true), hx :- (= (Nat.beq (edge-id e) x) true)] (seen-ok-f w f hk hd hsk e he))
               (fn [e :- EdgeRow, he :- (= (seen-ok w e) true), hx :- (= (Nat.beq (edge-id e) x) false)] he) (:edges w) hr)))))

(a/theorem i5-seen-edge-upd-q [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                           hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                           hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                           hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                           hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                           hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e)))]
  (=> (= (tbl-all (same-id-then edge-id x (fn [r :- EdgeRow] (seen-ok w (f r)))) (:edges w)) true) (= (i5-seen w) true) (= (i5-seen (edge-upd w x f)) true))
  (intros hq h)
  (have hr := (i5-seen-rest-of w h)) (simp only [i5-seen-rest] at hr)
  (have b := (tbl-all-mono2 EdgeRow (seen-ok w) (same-id-then edge-id x (fn [r :- EdgeRow] (seen-ok w (f r))))
               (both (seen-ok w) (same-id-then edge-id x (fn [r :- EdgeRow] (seen-ok w (f r)))))
               (fn [e :- EdgeRow, h1 :- (= (seen-ok w e) true), h2 :- (= (same-id-then edge-id x (fn [r :- EdgeRow] (seen-ok w (f r))) e) true)]
                 (both-of EdgeRow (seen-ok w) (same-id-then edge-id x (fn [r :- EdgeRow] (seen-ok w (f r)))) e h1 h2))
               (:edges w) hr hq))
  (have r2 (= (tbl-all (seen-ok w) (:edges (edge-upd w x f))) true))
  (simp only [edge-upd set-edges])
  (apply (tbl-all-upd EdgeRow edge-id x f (both (seen-ok w) (same-id-then edge-id x (fn [r :- EdgeRow] (seen-ok w (f r))))) (seen-ok w) _ _ (:edges w) b))
  (intros e hb hx)
  (have s := (both-right EdgeRow (seen-ok w) (same-id-then edge-id x (fn [r :- EdgeRow] (seen-ok w (f r)))) e hb))
  (simp only [same-id-then hx Bool.not_true Bool.false_or] at s) (exact s)
  (intros e hb hx) (exact (both-left EdgeRow (seen-ok w) (same-id-then edge-id x (fn [r :- EdgeRow] (seen-ok w (f r)))) e hb))
  (exact (i5-seen-intro _ (well-formed-edge-upd w x f hid hk hc hd hm (i5-seen-well-formed w h)) (i5-seen-rest-gen w (edge-upd w x f) (dv-same w (edge-upd w x f) (rfl) (rfl)) r2))))

(a/theorem i5-seen-insert-edge-fresh [w :- World, e :- EdgeRow, hs :- (= (seen-ok w (edge-set-marked false (edge-set-id (:next-id w) e))) true)]
  (=> (= (edge-ok-in w e) true) (= (i5-seen w) true) (= (i5-seen (insert-edge-fresh w e)) true))
  (intros he h)
  (have hr := (i5-seen-rest-of w h)) (simp only [i5-seen-rest] at hr)
  (have r2 (= (tbl-all (seen-ok w) (:edges (insert-edge-fresh w e))) true))
  (simp only [insert-edge-fresh bump insert-edge edge-ins set-next-id set-edges tbl-ins])
  (exact (all-cons EdgeRow (seen-ok w) _ (:edges w) hs hr))
  (exact (i5-seen-intro _ (well-formed-insert-edge-fresh w e he (i5-seen-well-formed w h)) (i5-seen-rest-gen w (insert-edge-fresh w e) (dv-same w (insert-edge-fresh w e) (rfl) (rfl)) r2))))

(a/theorem obs-slice-holder-ok [w :- World, d :- Nat, cb :- Nat, n :- Nat]
  (= (seen-ok w (edge-set-marked false (edge-set-id n (observe-edge w d cb)))) true)
  (cases hr (deb-ready w d))
  (all_goals (simp only [seen-ok edge-set-marked edge-set-id observe-edge hr Bool.not_false Bool.true_or Bool.or_true Nat.ble_eq Nat.le_refl]))
  (simp [Nat.le_refl]))

;; ---- companion edge-debtor-kept y d: every edge row with id y has debtor d, and y is below the allocator
;; (an edge keeps its debtor; a fresh edge id is never y)

(a/defn deb-at [kxy :- Nat, kxd :- Nat, e :- EdgeRow] Bool (Bool.or (Bool.not (Nat.beq (:id e) kxy)) (Nat.beq (:debtor e) kxd)))
(a/defn edge-debtor-kept-rest [kxy :- Nat, kxd :- Nat, w :- World] Bool (Bool.and (Nat.blt kxy (:next-id w)) (tbl-all (deb-at kxy kxd) (:edges w))))
(a/defn edge-debtor-kept [kxy :- Nat, kxd :- Nat, w :- World] Bool (Bool.and (well-formed w) (edge-debtor-kept-rest kxy kxd w)))
(a/theorem edge-debtor-kept-well-formed [kxy :- Nat, kxd :- Nat, w :- World] (=> (= (edge-debtor-kept kxy kxd w) true) (= (well-formed w) true))
  (intro h) (simp only [edge-debtor-kept Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem edge-debtor-kept-rest-of [kxy :- Nat, kxd :- Nat, w :- World] (=> (= (edge-debtor-kept kxy kxd w) true) (= (edge-debtor-kept-rest kxy kxd w) true))
  (intro h) (simp only [edge-debtor-kept Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem edge-debtor-kept-intro [kxy :- Nat, kxd :- Nat, w :- World] (=> (= (well-formed w) true) (= (edge-debtor-kept-rest kxy kxd w) true) (= (edge-debtor-kept kxy kxd w) true))
  (intros h1 h2) (simp only [edge-debtor-kept h1 h2 Bool.and_self]))
(a/theorem edge-debtor-kept-parts [kxy :- Nat, kxd :- Nat, w :- World]
  (=> (= (edge-debtor-kept kxy kxd w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (edge-debtor-kept-well-formed kxy kxd w h))))
(a/theorem edge-debtor-kept-rest-mk [kxy :- Nat, kxd :- Nat, w :- World, w2 :- World]
  (=> (<= (:next-id w) (:next-id w2)) (=> (= (tbl-all (deb-at kxy kxd) (:edges w)) true) (= (tbl-all (deb-at kxy kxd) (:edges w2)) true))
      (= (edge-debtor-kept-rest kxy kxd w) true) (= (edge-debtor-kept-rest kxy kxd w2) true))
  (intros hn he h)
  (simp only [edge-debtor-kept-rest Bool.and_eq_true Nat.blt_eq] at h)
  (have l (= (Nat.blt kxy (:next-id w2)) true)) (simp only [Nat.blt_eq]) (omega)
  (simp only [edge-debtor-kept-rest l (he (And.right h)) Bool.and_self]))

(a/theorem deb-at-f [kxy :- Nat, kxd :- Nat, f :- (=> EdgeRow EdgeRow), hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                     hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))), e :- EdgeRow]
  (=> (= (deb-at kxy kxd e) true) (= (deb-at kxy kxd (f e)) true))
  (intro h) (have e1 (= (:id (f e)) (:id e))) (exact (hid e)) (simp only [deb-at e1 (hd e)]) (simp only [deb-at] at h) (exact h))
(a/theorem deb-at-marked [kxy :- Nat, kxd :- Nat, b :- Bool, e :- EdgeRow]
  (=> (= (deb-at kxy kxd e) true) (= (deb-at kxy kxd (edge-set-marked b e)) true))
  (intro h) (simp only [deb-at edge-set-marked] at h) (simp only [deb-at edge-set-marked]) (exact h))
(a/theorem ep-mark-edge [P :- (=> EdgeRow Bool), hP :- (forall [e :- EdgeRow] (=> (= (P e) true) (= (P (edge-set-marked true e)) true))),
                         w :- World, x :- Nat]
  (=> (= (tbl-all P (:edges w)) true) (= (tbl-all P (:edges (mark-edge w x))) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false] (simp only [mark-edge hf hm comp-upd set-comps]) (exact (ep-edge-upd P w x (edge-set-marked true) hP h)))))
(a/theorem deb-at-new [kxy :- Nat, kxd :- Nat, w :- World, e :- EdgeRow]
  (=> (= (edge-debtor-kept-rest kxy kxd w) true) (= (deb-at kxy kxd (edge-set-marked false (edge-set-id (:next-id w) e))) true))
  (intro h)
  (simp only [edge-debtor-kept-rest Bool.and_eq_true Nat.blt_eq] at h)
  (have ne (= (Nat.beq (:next-id w) kxy) false))
  (cases hb (Nat.beq (:next-id w) kxy))
  (case [false] (rfl))
  (case [true] (have eq (= (:next-id w) kxy)) (exact (Nat.eq_of_beq_eq_true hb)) (have l := (And.left h)) (omega))
  (simp only [deb-at edge-set-marked edge-set-id ne Bool.not_false Bool.true_or]))

(a/theorem next-remove-edge [w :- World, x :- Nat] (= (:next-id (remove-edge w x)) (:next-id w))
  (cases hf (edge-find w x)) (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm comp-upd edge-del set-edges set-comps]))))
(a/theorem next-mark-edge [w :- World, x :- Nat] (= (:next-id (mark-edge w x)) (:next-id w))
  (cases hf (edge-find w x)) (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm comp-upd edge-upd set-edges set-comps]))))
(a/theorem next-unmark-edge [w :- World, x :- Nat] (= (:next-id (unmark-edge w x)) (:next-id w))
  (cases hf (edge-find w x)) (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm comp-upd edge-upd set-edges set-comps]))))

(def KX (mk-bundle 'edge-debtor-kept '[kxy :- Nat, kxd :- Nat] "edge-debtor-kept-" {}))
(swap! (:renames KX) assoc 'well-formed-parts 'edge-debtor-kept-parts)
(doseq [o '[well-formed-scope-upd well-formed-pub-upd well-formed-source-upd well-formed-resource-upd well-formed-cleanup-upd well-formed-cleanup-del well-formed-set-pins
            well-formed-resource-del well-formed-scope-del well-formed-cleanup-ins well-formed-act-upd well-formed-task-upd well-formed-run-upd well-formed-run-del well-formed-comp-upd
            well-formed-comp-del-unref well-formed-fork-del]]
  (prim! KX o nil))
(doseq [[o w2] '[[well-formed-source-ins-fresh (bump (source-ins w r))] [well-formed-fork-ins-fresh (bump (fork-ins w r))] [well-formed-resource-ins-fresh (bump (resource-ins w r))]
                 [well-formed-scope-ins-fresh (bump (scope-ins w r))] [well-formed-act-ins-fresh (bump (act-ins w r))]
                 [well-formed-task-ins-fresh (bump (task-ins w r))] [well-formed-comp-ins-fresh (bump (comp-ins w r))]
                 [well-formed-run-ins-fresh (bump (run-ins w r))] [well-formed-bump (bump w)]]]
  (prim! KX o (list 'edge-debtor-kept-rest-mk 'kxy 'kxd 'w w2 '(Nat.le_succ _) '(fn [h1 :- (= (tbl-all (deb-at kxy kxd) (:edges w)) true)] h1) 'R)))
(prim! KX 'well-formed-edge-upd
  '(edge-debtor-kept-rest-mk kxy kxd w (edge-upd w x f) (Nat.le_refl _)
     (fn [h1 :- (= (tbl-all (deb-at kxy kxd) (:edges w)) true)]
       (tbl-all-upd EdgeRow edge-id x f (deb-at kxy kxd) (deb-at kxy kxd)
         (fn [e :- EdgeRow, he :- (= (deb-at kxy kxd e) true), hx :- (= (Nat.beq (edge-id e) x) true)] (deb-at-f kxy kxd f hid hd e he))
         (fn [e :- EdgeRow, he :- (= (deb-at kxy kxd e) true), hx :- (= (Nat.beq (edge-id e) x) false)] he) (:edges w) h1))
     R))
(prim! KX 'well-formed-remove-edge '(edge-debtor-kept-rest-mk kxy kxd w (remove-edge w x) (Nat.le_of_eq (Eq.symm (next-remove-edge w x))) (fn [h1 :- (= (tbl-all (deb-at kxy kxd) (:edges w)) true)] (ep-remove-edge (deb-at kxy kxd) w x h1)) R))
(prim! KX 'well-formed-mark-edge '(edge-debtor-kept-rest-mk kxy kxd w (mark-edge w x) (Nat.le_of_eq (Eq.symm (next-mark-edge w x))) (fn [h1 :- (= (tbl-all (deb-at kxy kxd) (:edges w)) true)] (ep-mark-edge (deb-at kxy kxd) (deb-at-marked kxy kxd true) w x h1)) R))
(prim! KX 'well-formed-unmark-edge '(edge-debtor-kept-rest-mk kxy kxd w (unmark-edge w x) (Nat.le_of_eq (Eq.symm (next-unmark-edge w x))) (fn [h1 :- (= (tbl-all (deb-at kxy kxd) (:edges w)) true)] (ep-unmark-edge (deb-at kxy kxd) (deb-at-marked kxy kxd false) w x h1)) R))
(prim! KX 'well-formed-drop-cred-edges '(edge-debtor-kept-rest-mk kxy kxd w (drop-cred-edges w a) (Nat.le_refl _) (fn [h1 :- (= (tbl-all (deb-at kxy kxd) (:edges w)) true)] (ep-filter (deb-at kxy kxd) (cred-ne a) (:edges w) h1)) R))
(prim! KX 'well-formed-drop-act '(edge-debtor-kept-rest-mk kxy kxd w (drop-act w a) (Nat.le_refl _) (fn [h1 :- (= (tbl-all (deb-at kxy kxd) (:edges w)) true)] (ep-filter (deb-at kxy kxd) (cred-ne a) (:edges w) h1)) R))
(prim! KX 'well-formed-drop-edges '(edge-debtor-kept-rest-mk kxy kxd w (drop-edges w p) (Nat.le_refl _) (fn [h1 :- (= (tbl-all (deb-at kxy kxd) (:edges w)) true)] (ep-filter (deb-at kxy kxd) p (:edges w) h1)) R))
(a/theorem edge-debtor-kept-rest-ins [kxy :- Nat, kxd :- Nat, w :- World, e :- EdgeRow]
  (=> (= (edge-debtor-kept-rest kxy kxd w) true) (= (edge-debtor-kept-rest kxy kxd (insert-edge-fresh w e)) true))
  (intro h)
  (have n1 := (deb-at-new kxy kxd w e h))
  (simp only [edge-debtor-kept-rest Bool.and_eq_true Nat.blt_eq] at h)
  (have l (= (Nat.blt kxy (+ (:next-id w) 1)) true)) (simp only [Nat.blt_eq]) (omega)
  (simp only [edge-debtor-kept-rest insert-edge-fresh bump insert-edge edge-ins set-next-id set-edges tbl-ins tbl-all n1 (And.right h) l Bool.and_self]))
(prim! KX 'well-formed-insert-edge-fresh '(edge-debtor-kept-rest-ins kxy kxd w e R))

(tree/restate! KX '[well-formed-cancel-pred well-formed-cut-suffix])   ; the generic tree (spindel.v2.pres.tree) instead of a copy

(a/theorem run-ref-ok-edge [w :- World, e :- EdgeRow]
  (=> (= (well-formed w) true) (List.Mem e (:edges w)) (= (Nat.blt (:id e) (:next-id w)) true))
  (intros h hm)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (have r := (all-nat-mem (id-in-range (:next-id w)) (edge-id e) _ (And.left (And.right (And.right (And.right (And.right (And.right hb)))))) (mem-ids-has EdgeRow edge-id e (:edges w) hm)))
  (simp only [id-in-range Bool.and_eq_true] at r)
  (exact (And.right r)))
(a/theorem edge-debtor-kept-rest-from [kxy :- Nat, kxd :- Nat, w :- World]
  (=> (= (Nat.blt kxy (:next-id w)) true) (= (tbl-all (same-id-then edge-id kxy (fn [r :- EdgeRow] (Nat.beq (:debtor r) kxd))) (:edges w)) true)
      (= (edge-debtor-kept-rest kxy kxd w) true))
  (intros h1 h2) (simp only [edge-debtor-kept-rest h1 Bool.true_and]) (exact h2))

(a/theorem edge-debtor-kept-of-mem [w :- World, e :- EdgeRow]
  (=> (= (well-formed w) true) (List.Mem e (:edges w)) (= (edge-debtor-kept (:id e) (:debtor e) w) true))
  (intros h hm)
  (have u := (uniq-all EdgeRow edge-id (fn [r :- EdgeRow] (Nat.beq (:debtor r) (:debtor e))) e (:edges w) (edges-nodup w h) hm (Nat.beq_refl _)))
  (have b := (tbl-find-has-edge w e hm))
  (have l := (run-ref-ok-edge w e h hm))
  (exact (edge-debtor-kept-intro _ _ w h (edge-debtor-kept-rest-from (:id e) (:debtor e) w l u))))

(a/theorem edge-debtor-kept-q [kxy :- Nat, kxd :- Nat, w :- World, f :- (=> EdgeRow EdgeRow),
                 hf :- (forall [r :- EdgeRow] (=> (= (Nat.beq (:debtor r) kxd) true) (= (seen-ok w (f r)) true)))]
  (=> (= (edge-debtor-kept-rest kxy kxd w) true) (= (tbl-all (same-id-then edge-id kxy (fn [r :- EdgeRow] (seen-ok w (f r)))) (:edges w)) true))
  (intro h)
  (simp only [edge-debtor-kept-rest Bool.and_eq_true] at h)
  (apply (tbl-all-mono EdgeRow (deb-at kxy kxd) _ _ (:edges w) (And.right h)))
  (intros r hr)
  (cases hx (Nat.beq (:id r) kxy))
  (case [false] (have hx2 (= (Nat.beq (edge-id r) kxy) false)) (exact hx) (simp only [same-id-then hx2 Bool.not_false Bool.true_or]))
  (case [true]
    (have hx2 (= (Nat.beq (edge-id r) kxy) true)) (exact hx)
    (simp only [deb-at hx Bool.not_true Bool.false_or] at hr)
    (simp only [same-id-then hx2 Bool.not_true Bool.false_or])
    (exact (hf r hr))))

(a/theorem seen-set-cur [w :- World, d :- Nat, r :- EdgeRow]
  (=> (= (Nat.beq (:debtor r) d) true) (= (seen-ok w (edge-set-seen (deb-version w d) r)) true))
  (intro h)
  (have e (= (:debtor r) d)) (exact (Nat.eq_of_beq_eq_true h))
  (simp only [seen-ok edge-set-seen e Nat.ble_eq Nat.le_refl]) (simp))
(a/theorem seen-rearm-cur [w :- World, v :- Nat, d :- Nat, r :- EdgeRow]
  (=> (= (Nat.beq (:debtor r) d) true) (= (seen-ok w (edge-rearm v (deb-version w d) r)) true))
  (intro h)
  (have e (= (:debtor r) d)) (exact (Nat.eq_of_beq_eq_true h))
  (simp only [seen-ok edge-rearm e Nat.ble_eq Nat.le_refl]) (simp))

;; ---- the bundle copy

(a/theorem comp-result-row-hv [res :- RunResult, ep :- Nat, c :- CompRow] (<= (cver c) (cver (comp-result-row res ep c)))
  (cases hs (res-same res (:result c)))
  (all_goals (simp only [cver comp-result-row hs]))
  (exact (Nat.le_succ _)) (exact (Nat.le_refl _)))
(a/theorem source-write-hv [v :- Nat, s :- SourceRow] (<= (sver s) (sver (source-write v s))) (simp only [sver source-write]) (exact (Nat.le_succ _)))
(a/theorem stream-set-tail-hv [t :- Nat, s :- SourceRow] (<= (sver s) (sver (stream-set-tail t s))) (simp only [sver stream-set-tail]) (exact (Nat.le_succ _)))
(a/theorem source-bump-hv [s :- SourceRow] (<= (sver s) (sver (source-bump s))) (simp only [sver source-bump]) (exact (Nat.le_succ _)))
(a/theorem source-consume-hv [s :- SourceRow] (<= (sver s) (sver (source-consume s)))
  (cases ha (source-available s))
  (simp only [source-consume ha]) (exact (Nat.le_refl _))
  (cases hm (Nat.beq (:kind s) sk-mailbox))
  (all_goals (simp only [sver source-consume ha hm]))
  (exact (Nat.le_succ _)) (exact (Nat.le_succ _)))

(def SVB (mk-bundle 'i5-seen [] "i5-seen-"
           {'well-formed-comp-upd ['(fn [c :- CompRow] (Nat.le_refl (:version c))) 5]
            'well-formed-source-upd ['(fn [s :- SourceRow] (Nat.le_refl (:version s))) 4]
            'well-formed-edge-upd ['(fn [e :- EdgeRow] (Eq.refl (esk7 e))) 8]
            'well-formed-insert-edge-fresh ['(Eq.refl true) 2]
            'well-formed-insert-edge-checked ['(Eq.refl true) 2]
            'well-formed-serve-or ['(fn [s :- SourceRow] (Nat.le_refl (:version s))) 5]}))
(swap! (:renames SVB) assoc 'well-formed-parts 'i5-seen-parts 'well-formed-comp-upd 'i5-seen-comp-upd 'well-formed-source-upd 'i5-seen-source-upd
       'well-formed-edge-upd 'i5-seen-edge-upd 'well-formed-insert-edge-fresh 'i5-seen-insert-edge-fresh 'well-formed-comp-ins-fresh 'i5-seen-comp-ins
       'well-formed-source-ins-fresh 'i5-seen-source-ins 'well-formed-comp-del-unref 'i5-seen-comp-del 'well-formed-filter-world 'i5-seen-filter-world)
(defpart SVB :reads '[comps edges sources])
(prim! SVB 'well-formed-remove-edge '(i5-seen-rest-remove-edge w x R))
(prim! SVB 'well-formed-mark-edge '(i5-seen-rest-mark-edge w x R))
(prim! SVB 'well-formed-unmark-edge '(i5-seen-rest-unmark-edge w x R))
(prim! SVB 'well-formed-drop-cred-edges '(i5-seen-rest-drop-cred w a R))
(prim! SVB 'well-formed-drop-act '(i5-seen-rest-drop-act w a R))
(prim! SVB 'well-formed-drop-edges '(i5-seen-rest-drop-edges w p R))

;; i5-seen on the generic tree (spindel.v2.pres.tree): its table; its own proofs follow
(def ^:private svb-fns   ; row functions that only raise the version, with the lemma
  '{comp-result-row comp-result-row-hv source-write source-write-hv source-bump source-bump-hv
    stream-set-tail stream-set-tail-hv source-consume source-consume-hv})
(defn- hv-lemma [F] (let [l (svb-fns (if (seq? F) (first F) F))] (if (seq? F) (apply list l (repeat (count (rest F)) '_)) l)))
(tree/part! SVB
  ;; ---- the part's own proofs (content: a new or rewritten edge has seen its debtor's version)
  :over '{well-formed-insert-edge-checked i5-seen-insert-edge-checked   ; a new edge's seen is current (rfl at each site but the await's)
          well-formed-fire-observe        i5-seen-fire-observe          ; seen := the debtor's version
          well-formed-dep-consumed        i5-seen-dep-consumed          ; rearm: same
          well-formed-serve-or            i5-seen-serve-or              ; the kept source row only raises its version
          well-formed-append-raw          i5-seen-append-raw            ; the new tail link
          well-formed-consume-entry       i5-seen-consume-entry         ; T11's entry edge: rearm
          well-formed-dispatch-raw        i5-seen-dispatch-raw          ; T11: the entry edge is the world's (edge-debtor-kept through the cut)
          well-formed-track-raw           i5-seen-track-raw             ; T7: the site edge is the world's, reread at the source's version
          well-formed-await-step          i5-seen-await-step}           ; T6: a new dep or wait edge, or a re-awaited one
  ;; ---- sites: a source or computation row that only raises its version, by the row function's
  ;; lemma; T8's observe edge has seen the debtor's version (obs-slice-holder-ok)
  :sites (merge (tree/row-sites 'well-formed-comp-upd svb-fns (fn [F] (list 'i5-seen-comp-upd 'w 'x F 'hid 'hp (hv-lemma F) 'h0)))
                (tree/row-sites 'well-formed-source-upd svb-fns (fn [F] (list 'i5-seen-source-upd 'w 'x F 'hf (hv-lemma F) 'h0)))
                '{[well-formed-insert-edge-fresh (observe-edge w d cb)] (i5-seen-insert-edge-fresh w (observe-edge w d cb) h1 h0 h2)})
  ;; ---- facts from the path: the fired or consumed edge is the world's (its id's rows have its
  ;; debtor: the companion edge-debtor-kept)
  :ctx '{well-formed-fire-observe  [(= (edge-debtor-kept (:id e) (:debtor e) w) true)]
         well-formed-dep-consumed  [(= (edge-debtor-kept (:id e) (:debtor e) w) true)]
         well-formed-consume-entry [(= (edge-debtor-kept (:id e) (:debtor e) w) true)]
         [well-formed-insert-edge-fresh (observe-edge w d cb)]
         [(= (seen-ok w (edge-set-marked false (edge-set-id (:next-id w) e))) true)]}
  :pass '{well-formed-fire-edge   {well-formed-fire-observe [(edge-debtor-kept-of-mem w e (base-of w h) (tbl-find-mem EdgeRow edge-id x e (:edges w) hf))]   ; edge-find found it
                           well-formed-fire-dep     [(edge-debtor-kept-of-mem w e (base-of w h) (tbl-find-mem EdgeRow edge-id x e (:edges w) hf))]}
          well-formed-settle-edge {well-formed-fire-dep     [(edge-debtor-kept-of-mem w e (base-of w h) (tbl-find-mem EdgeRow edge-id x e (:edges w) hf))]}
          well-formed-t8-observe-any-kind     {[well-formed-insert-edge-fresh (observe-edge w d cb)] [(obs-slice-holder-ok w d cb (:next-id w))]}})   ; T8's new edge

(a/theorem i5-seen-insert-edge-checked [w :- World, e :- EdgeRow, hs :- (= (seen-ok w (edge-set-marked false (edge-set-id (:next-id w) e))) true)]
  (=> (= (i5-seen w) true) (= (i5-seen (insert-edge-checked w e)) true))
  (intro h)
  (cases hk (edge-ok-in w e))
  (simp only [insert-edge-checked hk]) (exact h)
  (simp only [insert-edge-checked hk]) (exact (i5-seen-insert-edge-fresh w e hs hk h)))

;; ---- fires: the edge is the world's (its id's rows have its debtor)

(a/theorem i5-seen-fire-observe [w :- World, e :- EdgeRow]
  (=> (= (edge-debtor-kept (:id e) (:debtor e) w) true) (= (i5-seen w) true) (= (i5-seen (fire-observe w e)) true))
  (intros hx h)
  (cases hs (observe-new e (deb-version w (:debtor e))))
  (simp only [fire-observe hs]) (exact h)
  (simp only [fire-observe hs])
  (exact (i5-seen-edge-upd-q w (:id e) (edge-set-seen (deb-version w (:debtor e))) (edge-set-seen-edge-id _) (edge-set-seen-kind _)
           (edge-set-seen-creditor _) (edge-set-seen-debtor _) (edge-set-seen-marked _)
           (edge-debtor-kept-q (:id e) (:debtor e) w (edge-set-seen (deb-version w (:debtor e))) (seen-set-cur w (:debtor e)) (edge-debtor-kept-rest-of _ _ w hx)) h)))

(a/theorem i5-seen-dep-consumed [w :- World, e :- EdgeRow]
  (=> (= (edge-debtor-kept (:id e) (:debtor e) w) true) (= (i5-seen w) true) (= (i5-seen (dep-consumed w e)) true))
  (intros hx h)
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf])
  (exact (i5-seen-edge-upd-q w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
           (edge-rearm-edge-id _ _) (edge-rearm-kind _ _) (edge-rearm-creditor _ _) (edge-rearm-debtor _ _) (edge-rearm-marked _ _)
           (edge-debtor-kept-q (:id e) (:debtor e) w _ (seen-rearm-cur w (deb-value w (:debtor e)) (:debtor e)) (edge-debtor-kept-rest-of _ _ w hx)) h))
  (simp only [dep-consumed hf]) (exact (i5-seen-remove-edge w (:id e) h)))

(tree/restate! SVB '[well-formed-fire-edge])
(a/theorem i5-seen-serve-or [w :- World, x :- Nat, res :- RunResult, keep :- (=> SourceRow SourceRow),
                         hk :- (forall [s :- SourceRow] (= (source-id (keep s)) (source-id s))),
                         hv :- (forall [s :- SourceRow] (<= (sver s) (sver (keep s))))]
  (=> (= (i5-seen w) true) (= (i5-seen (serve-or w x res keep)) true))
  (intro h)
  (cases hz (Nat.beq (oldest-waiter w x) 0))
  (simp only [serve-or hz]) (exact (i5-seen-fire-edge res w _ h))
  (simp only [serve-or hz]) (exact (i5-seen-source-upd w x keep hk hv h)))

(tree/restate! SVB '[well-formed-realize-link])
(a/theorem i5-seen-append-raw [w :- World, x :- Nat, v :- Nat, old :- Nat]
  (=> (= (i5-seen w) true) (= (i5-seen (append-raw w x v old)) true))
  (intro h)
  (simp only [append-raw])
  (exact (i5-seen-realize-link _ old v false _
           (i5-seen-source-ins (source-upd w x (stream-set-tail (:next-id w))) (new-link (:next-id w) root-scope-id x) (rfl)
             (i5-seen-source-upd w x (stream-set-tail (:next-id w)) (stream-set-tail-id _) (stream-set-tail-hv (:next-id w)) h)))))

;; ---- T11's entry edge and T7's site edge are the world's

(a/theorem earliest-mem [es :- (List EdgeRow)]
  (forall [best :- (Option EdgeRow), e :- EdgeRow]
    (=> (= (earliest best es) (Option.some EdgeRow e)) (Or (= best (Option.some EdgeRow e)) (List.Mem e es))))
  (induction es)
  (case [nil] (intros best e h) (simp only [earliest] at h) (exact (Or.inl h)))
  (case [cons hd t ih]
    (intros best e h)
    (simp only [earliest] at h)
    (have r := (ih _ e h))
    (cases r)
    (case [inr h2] (exact (Or.inr (List.Mem.tail hd h2))))
    (case [inl h1]
      (cases best)
      (case [none] (simp only [Option.some.injEq] at h1) (rw [← h1]) (exact (Or.inr (List.Mem.head t))))
      (case [some b]
        (cases hb (Nat.blt (:id hd) (:id b)))
        (case [true] (simp only [hb Option.some.injEq] at h1) (rw [← h1]) (exact (Or.inr (List.Mem.head t))))
        (case [false] (simp only [hb] at h1) (exact (Or.inl h1)))))))

(a/theorem filter-mem [A :- Type, q :- (=> A Bool), e :- A, xs :- (List A)] (=> (List.Mem e (tbl-filter q xs)) (List.Mem e xs))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-filter] at h) (cases h))
  (case [cons hd t ih]
    (intro h)
    (cases hq (q hd))
    (case [false] (simp only [tbl-filter hq] at h) (exact (List.Mem.tail hd (ih h))))
    (case [true]
      (simp only [tbl-filter hq] at h)
      (cases h)
      (case [head] (exact (List.Mem.head t)))
      (case [tail h2] (exact (List.Mem.tail hd (ih h2)))))))

(a/theorem entry-mem [w :- World, c :- Nat, e :- EdgeRow] (=> (= (entry-edge w c) (Option.some EdgeRow e)) (List.Mem e (:edges w)))
  (intro h)
  (simp only [entry-edge] at h)
  (have r := (earliest-mem _ (Option.none EdgeRow) e h))
  (cases r)
  (case [inl h1] (cases h1))
  (case [inr h2] (exact (filter-mem EdgeRow (fired-dep-of c) e (:edges w) h2))))

(tree/restate! SVB '[well-formed-edge-set-phase])
(a/theorem i5-seen-consume-entry [w :- World, e :- EdgeRow]
  (=> (= (edge-debtor-kept (:id e) (:debtor e) w) true) (= (i5-seen w) true) (= (i5-seen (consume-entry w e)) true))
  (intros hx h)
  (cases hf (deb-final w (:debtor e)))
  (cases hr (Nat.beq (:cont e) cont-restart))
  (simp only [consume-entry hr hf])
  (exact (i5-seen-edge-upd-q w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
           (edge-rearm-edge-id _ _) (edge-rearm-kind _ _) (edge-rearm-creditor _ _) (edge-rearm-debtor _ _) (edge-rearm-marked _ _)
           (edge-debtor-kept-q (:id e) (:debtor e) w _ (seen-rearm-cur w (deb-value w (:debtor e)) (:debtor e)) (edge-debtor-kept-rest-of _ _ w hx)) h))
  (simp only [consume-entry hr hf]) (exact (i5-seen-edge-set-phase w (:id e) ph-armed h))
  (simp only [consume-entry hf]) (exact (i5-seen-remove-edge w (:id e) h)))

(tree/restate! SVB '[well-formed-cancel-pred well-formed-cut-suffix well-formed-new-run-of])
(a/theorem i5-seen-dispatch-raw [w :- World, c :- CompRow]
  (=> (= (i5-seen w) true) (= (i5-seen (dispatch-raw w c)) true))
  (intro h)
  (have h1 := (i5-seen-cancel-pred w c h))
  (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
  (simp only [dispatch-raw he])
  (exact (i5-seen-new-run-of _ c 0 (i5-seen-cut-suffix _ (:id c) false 0 0 h1)))
  (simp only [dispatch-raw he])
  (have k0 := (edge-debtor-kept-of-mem w e (i5-seen-well-formed w h) (entry-mem w (:id c) e he)))
  (have k1 := (edge-debtor-kept-cut-suffix (:id e) (:debtor e) _ (:id c) true (:at e) (:id e) (edge-debtor-kept-cancel-pred (:id e) (:debtor e) w c k0)))
  (exact (i5-seen-new-run-of _ c _ (i5-seen-consume-entry _ e k1 (i5-seen-cut-suffix _ (:id c) true (:at e) (:id e) h1)))))

(a/theorem site-edge-mem [es :- (List EdgeRow), c :- Nat, at :- Nat, d :- Nat, e :- EdgeRow]
  (=> (= (site-edge es c at d) (Option.some EdgeRow e)) (And (List.Mem e es) (= (Nat.beq (:debtor e) d) true)))
  (induction es)
  (case [nil] (intro h) (simp [site-edge] at h))
  (case [cons hd t ih]
    (intro h)
    (cases hp (site-edge-p c at d hd))
    (case [false] (simp only [site-edge hp] at h) (have r := (ih h)) (exact (And.intro (List.Mem.tail hd (And.left r)) (And.right r))))
    (case [true]
      (simp only [site-edge hp Option.some.injEq] at h)
      (have hp2 := hp)
      (simp only [site-edge-p Bool.and_eq_true] at hp2)
      (have db := (And.right (And.right (And.right hp2))))
      (subst h)
      (exact (And.intro (List.Mem.head t) db)))))

(a/theorem reread-ok [w :- World, x :- Nat, s :- SourceRow, c :- Nat, e :- EdgeRow, r :- EdgeRow]
  (=> (= (source-find w x) (Option.some SourceRow s)) (= (Nat.beq (:debtor e) x) true) (= (Nat.beq (:debtor r) (:debtor e)) true)
      (= (seen-ok w (edge-reread c s r)) true))
  (intros hs he hr)
  (have e1 (= (:debtor r) x)) (exact (Eq.trans (Nat.eq_of_beq_eq_true hr) (Nat.eq_of_beq_eq_true he)))
  (have dv (= (deb-version w x) (:version s))) (simp only [deb-version hs])
  (simp only [seen-ok edge-reread e1 dv Nat.ble_eq Nat.le_refl]) (simp))

(tree/restate! SVB '[well-formed-track-fin])
(a/theorem i5-seen-track-raw [w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat]
  (=> (= (comp-has w (:of r)) true) (= (source-find w x) (Option.some SourceRow s))
      (= (i5-seen w) true) (= (i5-seen (track-raw w r x s k)) true))
  (intros hc hs h)
  (have h2 (= (i5-seen (match (site-edge (:edges w) (:of r) (:effect-index r) x)
                      none (track-new w r x s k)
                      (some e) (comp-upd (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s)))
                                         (:of r) (comp-consume-adopt (:effect-index r) x)))) true))
  (cases he (site-edge (:edges w) (:of r) (:effect-index r) x)) (case' [some e]) (case' [none])
  (simp only [track-new])
  (exact (i5-seen-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) x)
           (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [c :- CompRow] (Nat.le_refl (:version c)))
           (i5-seen-track-fin s (:next-id w) _ (i5-seen-insert-edge-fresh w (track-edge r x s k) (Eq.refl true) (track-edge-ok w r x s k hc hs) h))))
  (have sm := (site-edge-mem (:edges w) (:of r) (:effect-index r) x e he))
  (have kx0 := (edge-debtor-kept-of-mem w e (i5-seen-well-formed w h) (And.left sm)))
  (have q := (edge-debtor-kept-q (:id e) (:debtor e) w (edge-reread (track-cont r k) s)
               (fn [q2 :- EdgeRow, hq :- (= (Nat.beq (:debtor q2) (:debtor e)) true)] (reread-ok w x s (track-cont r k) e q2 hs (And.right sm) hq))
               (edge-debtor-kept-rest-of _ _ w kx0)))
  (exact (i5-seen-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) x)
           (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [c :- CompRow] (Nat.le_refl (:version c)))
           (i5-seen-track-fin s (:id e) _
             (i5-seen-edge-upd-q w (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) (edge-reread-kind _ _)
               (edge-reread-creditor _ _) (edge-reread-debtor _ _) (edge-reread-marked _ _) q h))))
  (simp only [track-raw])
  (exact (i5-seen-run-upd _ (:id r) run-tick run-tick-run-id h2)))

(tree/restate! SVB '[well-formed-raise-for])
(a/theorem i5-seen-await-step [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (i5-seen (:world acc)) true) (= (i5-seen (:world (await-step r a mode k acc d))) true))
  (intro h)
  (cases hd (as-dep (:world acc) r d))
  (case [false]
    (simp only [await-step hd])
    (have hn (= (seen-ok (:world acc) (edge-set-marked false (edge-set-id (:next-id (:world acc)) (await-edge (:world acc) r a mode k d)))) true))
    (simp [seen-ok edge-set-marked edge-set-id await-edge hd ek-wait ek-observe])
    (exact (i5-seen-insert-edge-checked _ _ hn h)))
  (case [true]
    (have hn (= (seen-ok (:world acc) (edge-set-marked false (edge-set-id (:next-id (:world acc)) (await-edge (:world acc) r a mode k d)))) true))
    (simp [seen-ok edge-set-marked edge-set-id await-edge hd ek-dep ek-observe])
    (cases hs (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none]
      (simp only [await-step hd hs])
      (simp only [await-new-dep])
      (exact (i5-seen-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) d)
               (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [c :- CompRow] (Nat.le_refl (:version c)))
               (i5-seen-raise-for _ (:of r) d (i5-seen-insert-edge-checked _ _ hn h)))))
    (case [some e]
      (simp only [await-step hd hs])
      (exact (i5-seen-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) d)
               (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [c :- CompRow] (Nat.le_refl (:version c)))
               (i5-seen-edge-upd _ (:id e) (edge-reawait (await-cont r mode k)) (edge-reawait-edge-id _)
                 (edge-reawait-kind _) (edge-reawait-creditor _) (edge-reawait-debtor _) (edge-reawait-marked _)
                 (fn [q :- EdgeRow] (Eq.refl (esk7 q))) h))))))

(tree/restate! SVB '[well-formed-raw])
(tree/restate! SVB '[well-formed-normalize])

(a/theorem i5-seen-rule-r-round [w :- World]
  (=> (= (i5-seen w) true) (= (filter-safe (normalize w)) true) (= (i5-seen (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (i5-seen-filter-world _ (keep-fn (normalize w)) (i5-seen-normalize w h) hf)))

(a/theorem i5-seen-rule-r-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (i5-seen w0) true) (= (rounds-safe-loop fuel w0) true) (= (i5-seen (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (i5-seen-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (i5-seen-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))

(a/theorem i5-seen-rule-r [w :- World]
  (=> (= (i5-seen w) true) (= (rule-r-safe w) true) (= (i5-seen (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (i5-seen-rule-r-loop (rule-r-fuel w) w h hs)))

(a/theorem step-i5-seen [w :- World, it :- Item]
  (=> (= (i5-seen w) true) (= (rule-r-safe (:world (raw w it))) true) (= (i5-seen (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (i5-seen-rule-r (:world (raw w it)) (i5-seen-raw w it h) hs))))

(a/theorem i5-seen-empty [] (= (i5-seen empty-world) true) (rfl))

;; Theorem: I5 as the model states it (inv-i5: a wait edge's creditor is the host or an existing
;; activation; an observe edge's seen never exceeds its debtor's version) through every step,
;; with no honest hypothesis. The third clause of the spec's I5 (no armed dep edge on a final
;; debtor, `lit-i5-dep-final`) is proved separately (spindel.v2.inv.i5 `step-lit-i5-dep-final-total`);
;; before Z#51 it was false (inv_test literal-i5-reactivation-resolved).
(a/theorem step-i5-seen-total [w :- World, it :- Item]
  (=> (= (chain-start w) true) (= (i5-seen w) true) (= (i5-seen (:world (world-step w it))) true))
  (intros h hv) (exact (step-i5-seen w it hv (step-rule-r-safe w it h))))
(a/theorem i5-seen-i5 [w :- World] (=> (= (i5-seen w) true) (= (inv-i5 w) true))
  (intro h)
  (have w5 := (i5-wait-of-well-formed w (i5-seen-well-formed w h)))
  (have r := (i5-seen-rest-of w h)) (simp only [i5-seen-rest] at r)
  (simp only [inv-i5 w5 r Bool.and_self]))
(a/theorem step-i5-total [w :- World, it :- Item]
  (=> (= (chain-start w) true) (= (i5-seen w) true) (= (inv-i5 (:world (world-step w it))) true))
  (intros h hv) (exact (i5-seen-i5 _ (step-i5-seen-total w it h hv))))
