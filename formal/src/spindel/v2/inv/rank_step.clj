(ns spindel.v2.inv.rank-step
  "Obligation P5: I12 ranks (`ranks-ok`) are preserved by EVERY transition, kernel-checked
  (Init only). The bundle is `i12-ranks w = well-formed w && ranks-ok w`.

    step-i12-ranks   i12-ranks w, rule-r-safe (:world (raw w it)) -> i12-ranks (:world (world-step w it))

  (the hypotheses of `step-well-formed`; ranks themselves need no extra hypothesis.)

  How. `ranks-ok` reads only the dep edges' (kind, creditor, debtor) and the computations'
  (id, rank) (`rank-edge-ok`). Part A proves it once per primitive edit (`ranks-<edit>`):
    - edits that touch neither edges nor computations keep it by `rfl`;
    - computation edits that keep id and rank (`comp-upd` with a rank-preserving row function,
      `comps-resync`) or remove rows (`comp-del`, the filter's `tbl-keep`) keep it: every
      computation of the new world is one of the old world with the same rank
      (`rank-edge-ok-shrink`, `ranks-shrink`);
    - edge edits that keep kind/creditor/debtor (`edge-upd`), remove edges (filter, delete,
      keep) keep it;
    - an inserted edge must be rank-ok itself (`ranks-insert-edge-fresh`): a non-dep edge
      always is (`rank-edge-ok-nondep`); a track edge's debtor is a source, so no
      computation (unique ids, `comp-not-source`); a T6 or reactivation edge comes with the
      raise (spindel.v2.inv.rank: `await-new-dep-ranks`, `react-add-ranks`);
    - a fresh computation (T3) has an id that no edge names (`edge-fresh-ok`, from
      edges-ref-ok and ids-below of well-formed);
    - ranks change only in the raise (spindel.v2.inv.rank).
  Part B lifts each to the bundle (`i12-ranks-<edit>`: the well-formed lemma plus the ranks lemma),
  as the cells of the part `RK` (spindel.v2.pres.part).

  Part C: the composite lemmas under `step-well-formed` are restated for the bundle from the
  generic step tree (spindel.v2.pres.tree, `restate!`), as for every other part. The transitions
  that insert an edge or raise a rank have bundle proofs written here (the part's :over): T7 track,
  reactivation, T22, take, T8 (the inserted edge is rank-ok) and T6 await (the raise's `ok`)."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.inv.rank :refer :all]
            [spindel.v2.pres.part :refer [mk-bundle prim!]]
            [spindel.v2.pres.tree :as tree]))

;; ===========================================================================
;; The bundle
;; ===========================================================================

(a/defn i12-ranks [w :- World] Bool (Bool.and (well-formed w) (ranks-ok w)))

(a/theorem i12-ranks-well-formed [w :- World] (=> (= (i12-ranks w) true) (= (well-formed w) true))
  (intro h) (simp only [i12-ranks Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem i12-ranks-ranks [w :- World] (=> (= (i12-ranks w) true) (= (ranks-ok w) true))
  (intro h) (simp only [i12-ranks Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem i12-ranks-intro [w :- World] (=> (= (well-formed w) true) (= (ranks-ok w) true) (= (i12-ranks w) true))
  (intros h1 h2) (simp only [i12-ranks h1 h2 Bool.and_self]))
(a/theorem i12-ranks-parts [w :- World]
  (=> (= (i12-ranks w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (i12-ranks-well-formed w h))))

;; ===========================================================================
;; Part A. ranks-ok under the primitive edits
;; ===========================================================================

;; ---- the frame: every computation of w2 is one of w with the same rank

(a/theorem rank-edge-ok-shrink [w :- World, w2 :- World, e :- EdgeRow]
  (=> (forall [y :- Nat] (=> (= (comp-has w2 y) true)
                             (And (= (comp-has w y) true) (= (comp-rank w2 y) (comp-rank w y)))))
      (= (rank-edge-ok w e) true) (= (rank-edge-ok w2 e) true))
  (intros hs he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp [rank-edge-ok hk]))
  (case [true]
    (cases hd (comp-has w2 (:debtor e)))
    (case [false] (simp [rank-edge-ok hk hd]))
    (case [true]
      (cases hc (comp-has w2 (:creditor e)))
      (case [false] (simp [rank-edge-ok hk hd hc]))
      (case [true]
        (have pd := (hs (:debtor e) hd))
        (have pc := (hs (:creditor e) hc))
        (simp only [rank-edge-ok hk (And.left pd) (And.left pc) Bool.not_true Bool.false_or] at he)
        (simp only [rank-edge-ok hk hd hc Bool.not_true Bool.false_or (And.right pd) (And.right pc)])
        (exact he)))))

(a/theorem ranks-shrink [w :- World, w2 :- World]
  (=> (forall [y :- Nat] (=> (= (comp-has w2 y) true)
                             (And (= (comp-has w y) true) (= (comp-rank w2 y) (comp-rank w y)))))
      (= (tbl-all (rank-edge-ok w) (:edges w2)) true) (= (ranks-ok w2) true))
  (intros hs he)
  (simp only [ranks-ok])
  (exact (tbl-all-mono EdgeRow (rank-edge-ok w) (rank-edge-ok w2)
           (fn [e :- EdgeRow, h1 :- (= (rank-edge-ok w e) true)] (rank-edge-ok-shrink w w2 e hs h1))
           (:edges w2) he)))

(a/theorem same-comps-within [w :- World, w2 :- World]
  (=> (= (:comps w2) (:comps w))
      (forall [y :- Nat] (=> (= (comp-has w2 y) true)
                             (And (= (comp-has w y) true) (= (comp-rank w2 y) (comp-rank w y))))))
  (intros he y hy)
  (have e1 (= (comp-has w2 y) (comp-has w y))) (simp only [comp-has he])
  (have e2 (= (comp-rank w2 y) (comp-rank w y))) (simp only [comp-rank comp-find he])
  (rw [e1] at hy)
  (exact (And.intro hy e2)))

(a/theorem rank-edge-ok-nondep [w :- World, e :- EdgeRow]
  (=> (= (Nat.beq (:kind e) ek-dep) false) (= (rank-edge-ok w e) true))
  (intro h) (simp [rank-edge-ok h]))

;; ---- computation updates that keep id and rank

(a/theorem crank-upd-same [x :- Nat, f :- (=> CompRow CompRow),
                           hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                           hr :- (forall [c :- CompRow] (= (:rank (f c)) (:rank c))), y :- Nat, cs :- (List CompRow)]
  (= (crank (tbl-upd comp-id x f cs) y) (crank cs y))
  (induction cs)
  (case [nil] (simp only [tbl-upd]))
  (case [cons h t ih]
    (cases hx (Nat.beq (comp-id h) x))
    (case [false]
      (cases hy (Nat.beq (comp-id h) y))
      (case [true] (simp only [crank tbl-upd hx tbl-find hy]))
      (case [false] (simp only [crank tbl-upd hx tbl-find hy]) (exact ih)))
    (case [true]
      (have hid2 (= (comp-id (f h)) (comp-id h))) (exact (hid h))
      (cases hy (Nat.beq (comp-id h) y))
      (case [true]
        (have hy2 (= (Nat.beq (comp-id (f h)) y) true)) (rw [hid2]) (exact hy)
        (simp only [crank tbl-upd hx tbl-find hy hy2]) (exact (hr h)))
      (case [false]
        (have hy2 (= (Nat.beq (comp-id (f h)) y) false)) (rw [hid2]) (exact hy)
        (simp only [crank tbl-upd hx tbl-find hy hy2]) (exact ih)))))

(a/theorem comp-upd-within [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                            hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                            hr :- (forall [c :- CompRow] (= (:rank (f c)) (:rank c)))]
  (forall [y :- Nat] (=> (= (comp-has (comp-upd w x f) y) true)
                         (And (= (comp-has w y) true) (= (comp-rank (comp-upd w x f) y) (comp-rank w y)))))
  (intros y hy)
  (have e1 (= (comp-has (comp-upd w x f) y) (comp-has w y)))
  (simp only [comp-has comp-upd set-comps]) (exact (tbl-has-upd CompRow comp-id x y f hid (:comps w)))
  (rw [e1] at hy)
  (exact (And.intro hy (crank-upd-same x f hid hr y (:comps w)))))

(a/theorem ranks-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                           hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                           hr :- (forall [c :- CompRow] (= (:rank (f c)) (:rank c)))]
  (=> (= (ranks-ok w) true) (= (ranks-ok (comp-upd w x f)) true))
  (intro h)
  (have he (= (tbl-all (rank-edge-ok w) (:edges (comp-upd w x f))) true)) (exact h)
  (exact (ranks-shrink w (comp-upd w x f) (comp-upd-within w x f hid hr) he)))

;; ---- edge updates that keep kind, creditor and debtor; edge removal

(a/theorem ranks-edge-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                           hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                           hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                           hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e)))]
  (=> (= (ranks-ok w) true) (= (ranks-ok (edge-upd w x f)) true))
  (intro h)
  (have hsame (forall [e :- EdgeRow] (= (rank-edge-ok w (f e)) (rank-edge-ok w e))))
  (intro e) (simp only [rank-edge-ok (hk e) (hc e) (hd e)])
  (have hin (forall [r :- EdgeRow] (=> (= (rank-edge-ok w r) true) (= (Nat.beq (edge-id r) x) true)
                                       (= (rank-edge-ok w (f r)) true))))
  (intros r h1 h2) (rw [hsame]) (exact h1)
  (have hout (forall [r :- EdgeRow] (=> (= (rank-edge-ok w r) true) (= (Nat.beq (edge-id r) x) false)
                                        (= (rank-edge-ok w r) true))))
  (intros r h1 h2) (exact h1)
  (have hall (= (tbl-all (rank-edge-ok w) (:edges (edge-upd w x f))) true))
  (exact (tbl-all-upd EdgeRow edge-id x f (rank-edge-ok w) (rank-edge-ok w) hin hout (:edges w) h))
  (exact (ranks-shrink w (edge-upd w x f) (same-comps-within w (edge-upd w x f) (rfl)) hall)))

(a/theorem ranks-edge-del [w :- World, x :- Nat]
  (=> (= (ranks-ok w) true) (= (ranks-ok (edge-del w x)) true))
  (intro h)
  (have hall (= (tbl-all (rank-edge-ok w) (:edges (edge-del w x))) true))
  (simp only [edge-del set-edges tbl-del-filter])
  (exact (tbl-all-filter EdgeRow (rank-edge-ok w) (id-ne edge-id x) (:edges w) h))
  (exact (ranks-shrink w (edge-del w x) (same-comps-within w (edge-del w x) (rfl)) hall)))

(a/theorem ranks-set-edges-filter [w :- World, p :- (=> EdgeRow Bool)]
  (=> (= (ranks-ok w) true) (= (ranks-ok (set-edges w (tbl-filter p (:edges w)))) true))
  (intro h)
  (have hall (= (tbl-all (rank-edge-ok w) (:edges (set-edges w (tbl-filter p (:edges w))))) true))
  (exact (tbl-all-filter EdgeRow (rank-edge-ok w) p (:edges w) h))
  (exact (ranks-shrink w _ (same-comps-within w (set-edges w (tbl-filter p (:edges w))) (rfl)) hall)))

(a/theorem comp-inc-pending-rank [c :- CompRow] (= (:rank (comp-inc-pending c)) (:rank c)) (rfl))
(a/theorem comp-dec-pending-rank [c :- CompRow] (= (:rank (comp-dec-pending c)) (:rank c)) (rfl))
(a/theorem comp-set-pending-rank [n :- Nat, c :- CompRow] (= (:rank (comp-set-pending n c)) (:rank c)) (rfl))
(a/theorem edge-set-marked-kind [b :- Bool, e :- EdgeRow] (= (:kind (edge-set-marked b e)) (:kind e)) (rfl))
(a/theorem edge-set-marked-creditor [b :- Bool, e :- EdgeRow] (= (:creditor (edge-set-marked b e)) (:creditor e)) (rfl))
(a/theorem edge-set-marked-debtor [b :- Bool, e :- EdgeRow] (= (:debtor (edge-set-marked b e)) (:debtor e)) (rfl))

(a/theorem ranks-mark-edge [w :- World, x :- Nat]
  (=> (= (ranks-ok w) true) (= (ranks-ok (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false]
      (simp only [mark-edge hf hm])
      (exact (ranks-comp-upd _ (:creditor e) comp-inc-pending comp-inc-pending-id comp-inc-pending-rank
               (ranks-edge-upd w x (edge-set-marked true) (edge-set-marked-kind true)
                 (edge-set-marked-creditor true) (edge-set-marked-debtor true) h))))))

(a/theorem ranks-unmark-edge [w :- World, x :- Nat]
  (=> (= (ranks-ok w) true) (= (ranks-ok (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true]
      (simp only [unmark-edge hf hm])
      (exact (ranks-comp-upd _ (:creditor e) comp-dec-pending comp-dec-pending-id comp-dec-pending-rank
               (ranks-edge-upd w x (edge-set-marked false) (edge-set-marked-kind false)
                 (edge-set-marked-creditor false) (edge-set-marked-debtor false) h))))))

(a/theorem ranks-remove-edge [w :- World, x :- Nat]
  (=> (= (ranks-ok w) true) (= (ranks-ok (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact (ranks-edge-del w x h)))
    (case [true]
      (simp only [remove-edge hf hm])
      (exact (ranks-comp-upd _ (:creditor e) comp-dec-pending comp-dec-pending-id comp-dec-pending-rank
               (ranks-edge-del w x h))))))

(a/theorem ranks-drop-cred [w :- World, a :- Nat]
  (=> (= (ranks-ok w) true) (= (ranks-ok (drop-cred-edges w a)) true))
  (intro h)
  (simp only [drop-cred-edges])
  (exact (ranks-comp-upd _ a (comp-set-pending 0) (comp-set-pending-id 0) (comp-set-pending-rank 0)
           (ranks-set-edges-filter w (cred-ne a) h))))

;; ---- inserting an edge: the new edge must be rank-ok

(a/theorem ranks-insert-edge-fresh [w :- World, e :- EdgeRow]
  (=> (= (rank-edge-ok w e) true) (= (ranks-ok w) true) (= (ranks-ok (insert-edge-fresh w e)) true))
  (intros he h)
  (have e1 (= (ranks-ok (insert-edge-fresh w e)) (Bool.and (rank-edge-ok w e) (ranks-ok w)))) (rfl)
  (rw [e1])
  (simp only [he h Bool.and_self]))

(a/theorem ranks-insert-edge-checked [w :- World, e :- EdgeRow]
  (=> (= (rank-edge-ok w e) true) (= (ranks-ok w) true) (= (ranks-ok (insert-edge-checked w e)) true))
  (intros he h)
  (cases hk (edge-ok-in w e))
  (case [false] (simp only [insert-edge-checked hk]) (exact h))
  (case [true] (simp only [insert-edge-checked hk]) (exact (ranks-insert-edge-fresh w e he h))))

;; ---- Rule R edits: drop-edges (resync), comp-del, the filter

(a/theorem crank-resync [es :- (List EdgeRow), y :- Nat, cs :- (List CompRow)]
  (= (crank (comps-resync es cs) y) (crank cs y))
  (induction cs)
  (case [nil] (simp only [comps-resync]))
  (case [cons h t ih]
    (cases hy (Nat.beq (comp-id h) y))
    (case [true]
      (have hy2 (= (Nat.beq (comp-id (comp-resync es h)) y) true)) (exact hy)
      (simp only [crank comps-resync tbl-find hy hy2]))
    (case [false]
      (have hy2 (= (Nat.beq (comp-id (comp-resync es h)) y) false)) (exact hy)
      (simp only [crank comps-resync tbl-find hy hy2]) (exact ih))))

(a/theorem ranks-drop-edges [w :- World, p :- (=> EdgeRow Bool)]
  (=> (= (ranks-ok w) true) (= (ranks-ok (drop-edges w p)) true))
  (intro h)
  (have hw (forall [y :- Nat] (=> (= (comp-has (drop-edges w p) y) true)
                                  (And (= (comp-has w y) true) (= (comp-rank (drop-edges w p) y) (comp-rank w y))))))
  (intros y hy)
  (have e1 (= (comp-has (drop-edges w p) y) (comp-has w y)))
  (simp only [comp-has drop-edges set-comps set-edges]) (exact (resync-has (tbl-filter p (:edges w)) (:comps w) y))
  (rw [e1] at hy)
  (exact (And.intro hy (crank-resync (tbl-filter p (:edges w)) y (:comps w))))
  (have hall (= (tbl-all (rank-edge-ok w) (:edges (drop-edges w p))) true))
  (exact (tbl-all-filter EdgeRow (rank-edge-ok w) p (:edges w) h))
  (exact (ranks-shrink w (drop-edges w p) hw hall)))

(a/theorem has-del-self [A :- Type, idf :- (=> A Nat), x :- Nat, xs :- (List A)]
  (= (tbl-has idf x (tbl-del idf x xs)) false)
  (induction xs)
  (case [nil] (simp [tbl-del tbl-has]))
  (case [cons h t ih]
    (cases hx (Nat.beq (idf h) x))
    (case [true] (simp only [tbl-del hx]) (exact ih))
    (case [false] (simp only [tbl-del hx tbl-has]) (exact ih))))

(a/theorem crank-del-ne [x :- Nat, y :- Nat, cs :- (List CompRow)]
  (=> (= (Nat.beq x y) false) (= (crank (tbl-del comp-id x cs) y) (crank cs y)))
  (intro hne)
  (induction cs)
  (case [nil] (simp only [tbl-del]))
  (case [cons h t ih]
    (cases hx (Nat.beq (comp-id h) x))
    (case [true]
      (have hxe (= (comp-id h) x)) (exact (Nat.eq_of_beq_eq_true hx))
      (have hy (= (Nat.beq (comp-id h) y) false)) (rw [hxe]) (exact hne)
      (simp only [crank tbl-del hx tbl-find hy]) (exact ih))
    (case [false]
      (cases hy (Nat.beq (comp-id h) y))
      (case [true] (simp only [crank tbl-del hx tbl-find hy]))
      (case [false] (simp only [crank tbl-del hx tbl-find hy]) (exact ih)))))

(a/theorem ranks-comp-del [w :- World, x :- Nat]
  (=> (= (ranks-ok w) true) (= (ranks-ok (comp-del w x)) true))
  (intro h)
  (have hw (forall [y :- Nat] (=> (= (comp-has (comp-del w x) y) true)
                                  (And (= (comp-has w y) true) (= (comp-rank (comp-del w x) y) (comp-rank w y))))))
  (intros y hy)
  (cases hxy (Nat.beq x y))
  (case [true]
    (have he (= x y)) (exact (Nat.eq_of_beq_eq_true hxy))
    (have hn (= (comp-has (comp-del w x) y) false))
    (rw [← he]) (simp only [comp-has comp-del set-comps]) (exact (has-del-self CompRow comp-id x (:comps w)))
    (rw [hn] at hy) (cases hy))
  (case [false]
    (have e1 (= (comp-has (comp-del w x) y) (comp-has w y)))
    (simp only [comp-has comp-del set-comps]) (exact (tbl-has-del-ne CompRow comp-id x y (:comps w) hxy))
    (rw [e1] at hy)
    (exact (And.intro hy (crank-del-ne x y (:comps w) hxy))))
  (exact (ranks-shrink w (comp-del w x) hw h)))

(a/theorem ranks-filter-world [w :- World, K :- (=> Nat Bool)]
  (=> (= (ranks-ok w) true) (= (ranks-ok (filter-world K w)) true))
  (intro h)
  (have hw (forall [y :- Nat] (=> (= (comp-has (filter-world K w) y) true)
                                  (And (= (comp-has w y) true) (= (comp-rank (filter-world K w) y) (comp-rank w y))))))
  (intros y hy)
  (simp only [comp-has fw-comps (tbl-has-keep CompRow K comp-id y (:comps w)) Bool.and_eq_true] at hy)
  (have e2 (= (comp-rank (filter-world K w) y) (comp-rank w y)))
  (simp only [comp-rank comp-find fw-comps (keep-find-in CompRow K comp-id y (:comps w) (And.left hy))])
  (exact (And.intro (And.right hy) e2))
  (have hall (= (tbl-all (rank-edge-ok w) (:edges (filter-world K w))) true))
  (simp only [fw-edges])
  (exact (tbl-all-keep-same EdgeRow K edge-id (rank-edge-ok w) (:edges w) h))
  (exact (ranks-shrink w (filter-world K w) hw hall)))

;; ---- a fresh computation: no edge names next-id (edges-ref-ok, ids-below)

(a/defn edge-fresh-ok [n :- Nat, e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:kind e) ek-dep))
           (Bool.and (Bool.not (Nat.beq (:creditor e) n)) (Bool.not (Nat.beq (:debtor e) n)))))

(a/theorem ne-of-mem-ids [w :- World, y :- Nat]
  (=> (= (nat-mem (:next-id w) (all-ids w)) false) (= (nat-mem y (all-ids w)) true) (= (Nat.beq y (:next-id w)) false))
  (intros hn hy)
  (cases hb (Nat.beq y (:next-id w)))
  (case [false] (rfl))
  (case [true]
    (have he (= y (:next-id w))) (exact (Nat.eq_of_beq_eq_true hb))
    (rw [he] at hy) (rw [hn] at hy) (cases hy)))

(a/theorem comp-mem-ids [w :- World, y :- Nat]
  (=> (= (tbl-has comp-id y (:comps w)) true) (= (nat-mem y (all-ids w)) true))
  (intro h) (simp only [all-ids nat-mem-app (nat-mem-ids CompRow comp-id y (:comps w)) h]) (simp))
(a/theorem task-mem-ids [w :- World, y :- Nat]
  (=> (= (tbl-has task-id y (:tasks w)) true) (= (nat-mem y (all-ids w)) true))
  (intro h) (simp only [all-ids nat-mem-app (nat-mem-ids TaskRow task-id y (:tasks w)) h]) (simp))
(a/theorem source-mem-ids [w :- World, y :- Nat]
  (=> (= (tbl-has source-id y (:sources w)) true) (= (nat-mem y (all-ids w)) true))
  (intro h) (simp only [all-ids nat-mem-app (nat-mem-ids SourceRow source-id y (:sources w)) h]) (simp))
(a/theorem res-mem-ids [w :- World, y :- Nat]
  (=> (= (tbl-has resource-id y (:res w)) true) (= (nat-mem y (all-ids w)) true))
  (intro h) (simp only [all-ids nat-mem-app (nat-mem-ids ResRow resource-id y (:res w)) h]) (simp))

(a/theorem edge-fresh-of-ok [w :- World, e :- EdgeRow]
  (=> (= (nat-mem (:next-id w) (all-ids w)) false)
      (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) e) true)
      (= (edge-fresh-ok (:next-id w) e) true))
  (intros hn he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp [edge-fresh-ok hk]))
  (case [true]
    (simp only [edge-ok cred-ok deb-ok hk Bool.and_eq_true] at he)
    (have hc := (ne-of-mem-ids w (:creditor e) hn (comp-mem-ids w (:creditor e) (And.left he))))
    (have hd (= (Nat.beq (:debtor e) (:next-id w)) false))
    (have hdd := (And.right he))
    (simp only [Bool.or_eq_true] at hdd)
    (rcases hdd (or h1 (or h2 (or h3 h4))))
    (exact (ne-of-mem-ids w _ hn (comp-mem-ids w _ h1)))
    (exact (ne-of-mem-ids w _ hn (task-mem-ids w _ h2)))
    (exact (ne-of-mem-ids w _ hn (source-mem-ids w _ h3)))
    (simp only [Bool.and_eq_true] at h4)
    (exact (ne-of-mem-ids w _ hn (res-mem-ids w _ (And.right h4))))
    (simp [edge-fresh-ok hk hc hd])))

(a/theorem rank-edge-ok-comp-ins [w :- World, r :- CompRow, e :- EdgeRow]
  (=> (= (comp-id r) (:next-id w)) (= (edge-fresh-ok (:next-id w) e) true) (= (rank-edge-ok w e) true)
      (= (rank-edge-ok (bump (comp-ins w r)) e) true))
  (intros hr hf he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp [rank-edge-ok hk]))
  (case [true]
    (simp only [edge-fresh-ok hk Bool.not_true Bool.false_or Bool.and_eq_true] at hf)
    (have hc (= (Nat.beq (comp-id r) (:creditor e)) false))
    (rw [hr]) (exact (beq-symm-false _ _ (bnot-true _ (And.left hf))))
    (have hd (= (Nat.beq (comp-id r) (:debtor e)) false))
    (rw [hr]) (exact (beq-symm-false _ _ (bnot-true _ (And.right hf))))
    (have e1 (= (rank-edge-ok (bump (comp-ins w r)) e) (rank-edge-ok w e)))
    (simp only [rank-edge-ok comp-has comp-rank comp-find bump set-next-id comp-ins set-comps tbl-ins tbl-has tbl-find hc hd])
    (rw [e1])
    (exact he)))

(a/theorem ranks-comp-ins-fresh [w :- World, r :- CompRow]
  (=> (= (comp-id r) (:next-id w)) (= (well-formed w) true) (= (ranks-ok w) true)
      (= (ranks-ok (bump (comp-ins w r))) true))
  (intros hr hs h)
  (have hp := (well-formed-parts w hs))
  (have hids (= (ids-ok w) true)) (exact (And.right (And.right hp)))
  (simp only [ids-ok ids-below Bool.and_eq_true] at hids)
  (have hn (= (nat-mem (:next-id w) (all-ids w)) false))
  (exact (range-not-mem (:next-id w) (all-ids w) (And.right (And.right hids))))
  (have href (= (tbl-all (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) (:edges w)) true))
  (exact (And.left (And.right hp)))
  (have hfr (= (tbl-all (edge-fresh-ok (:next-id w)) (:edges w)) true))
  (exact (tbl-all-mono EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) (edge-fresh-ok (:next-id w))
           (fn [e :- EdgeRow, he :- (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) e) true)]
             (edge-fresh-of-ok w e hn he))
           (:edges w) href))
  (simp only [ranks-ok])
  (exact (tbl-all-mono2 EdgeRow (edge-fresh-ok (:next-id w)) (rank-edge-ok w) (rank-edge-ok (bump (comp-ins w r)))
           (fn [e :- EdgeRow, h1 :- (= (edge-fresh-ok (:next-id w) e) true), h2 :- (= (rank-edge-ok w e) true)]
             (rank-edge-ok-comp-ins w r e hr h1 h2))
           (:edges w) hfr h)))

;; ---- a track edge's debtor is a source, hence no computation (unique ids)

(a/theorem nodup-app-disjoint [x :- Nat, xs :- (List Nat), ys :- (List Nat)]
  (=> (= (nat-nodup (nat-app xs ys)) true) (= (nat-mem x xs) true) (= (nat-mem x ys) false))
  (induction xs)
  (case [nil] (intros hn hm) (simp [nat-mem] at hm))
  (case [cons h t ih]
    (intros hn hm)
    (simp only [nat-app nat-nodup Bool.and_eq_true] at hn)
    (cases hx (Nat.beq h x))
    (case [true]
      (have he (= h x)) (exact (Nat.eq_of_beq_eq_true hx))
      (have h1 (= (nat-mem h (nat-app t ys)) false)) (exact (bnot-true _ (And.left hn)))
      (simp only [nat-mem-app] at h1)
      (rw [← he])
      (exact (And.right (or-false-parts _ _ h1))))
    (case [false]
      (simp only [nat-mem hx] at hm)
      (exact (ih (And.right hn) hm)))))

(a/theorem comp-not-source [w :- World, x :- Nat]
  (=> (= (ids-ok w) true) (= (tbl-has source-id x (:sources w)) true) (= (comp-has w x) false))
  (intros hi hs)
  (simp only [ids-ok ids-unique Bool.and_eq_true all-ids] at hi)
  (have hn := (nat-nodup-app-right _ _ (And.left hi)))
  (cases hc (comp-has w x))
  (case [false] (rfl))
  (case [true]
    (simp only [comp-has] at hc)
    (have hm (= (nat-mem x (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hc)
    (have hout := (nodup-app-disjoint x _ _ hn hm))
    (have hin (= (nat-mem x (nat-app (tbl-ids task-id (:tasks w)) (nat-app (tbl-ids run-id (:runs w))
                  (nat-app (tbl-ids source-id (:sources w)) (nat-app (tbl-ids edge-id (:edges w))
                  (nat-app (tbl-ids act-id (:acts w)) (nat-app (tbl-ids resource-id (:res w))
                  (nat-app (tbl-ids pub-id (:pubs w)) (tbl-ids fork-id (:forks w)))))))))) true))
    (simp only [nat-mem-app (nat-mem-ids SourceRow source-id x (:sources w)) hs]) (simp)
    (rw [hout] at hin) (cases hin)))

;; ===========================================================================
;; Part B. The bundle under the primitive edits
;; ===========================================================================

;; The bundle's cell for a primitive edit: the well-formed lemma and a ranks proof (`prim!`). The form
;; is over the lemma's binders, its premises `h0 ... hn` and `R` = ranks-ok of the input world; nil =
;; the edit leaves ranks-ok definitionally unchanged.

(def RK (assoc (mk-bundle 'i12-ranks [] "i12-ranks-"
                          ;; a computation update: one more argument, the row function keeps the rank
                          {'well-formed-comp-upd ['(fn [c :- CompRow] (Eq.refl (:rank c))) 5]})
               :names {"-rest" 'ranks-ok "-rest-of" 'i12-ranks-ranks}))

;; edits that touch neither edges nor computations (rfl frame)
(doseq [o '[well-formed-run-upd well-formed-scope-upd well-formed-pub-upd well-formed-source-upd
            well-formed-task-upd well-formed-act-upd well-formed-resource-upd well-formed-cleanup-upd
            well-formed-cleanup-del well-formed-set-pins well-formed-run-del well-formed-resource-del
            well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-fork-del well-formed-resource-ins-fresh
            well-formed-scope-ins-fresh well-formed-run-ins-fresh well-formed-task-ins-fresh well-formed-act-ins-fresh
            well-formed-bump well-formed-scope-del well-formed-cleanup-ins]]
  (prim! RK o nil))
;; edge edits, computation edits
(doseq [[o ranks] '[[well-formed-mark-edge (ranks-mark-edge w x R)]
                    [well-formed-unmark-edge (ranks-unmark-edge w x R)]
                    [well-formed-edge-upd (ranks-edge-upd w x f hk hc hd R)]
                    [well-formed-remove-edge (ranks-remove-edge w x R)]
                    [well-formed-drop-cred-edges (ranks-drop-cred w a R)]
                    [well-formed-drop-edges (ranks-drop-edges w p R)]
                    [well-formed-comp-del-unref (ranks-comp-del w x R)]
                    [well-formed-comp-ins-fresh (ranks-comp-ins-fresh w r h0 (i12-ranks-well-formed w h2) R)]
                    [well-formed-filter-world (ranks-filter-world w K R)]]]
  (prim! RK o ranks))

;; computation updates: the row function keeps the rank
(a/theorem i12-ranks-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hr :- (forall [c :- CompRow] (= (:rank (f c)) (:rank c)))]
  (=> (= (i12-ranks w) true) (= (i12-ranks (comp-upd w x f)) true))
  (intro h)
  (exact (i12-ranks-intro _ (well-formed-comp-upd w x f hid hp (i12-ranks-well-formed w h)) (ranks-comp-upd w x f hid hr (i12-ranks-ranks w h)))))
(swap! (:renames RK) assoc 'well-formed-comp-upd 'i12-ranks-comp-upd 'well-formed-parts 'i12-ranks-parts)

;; activation removal (with its creditor edges)
(a/theorem i12-ranks-drop-act [w :- World, a :- Nat]
  (=> (= (i12-ranks w) true) (= (i12-ranks (drop-act w a)) true))
  (intro h)
  (have hr (= (ranks-ok (drop-act w a)) (ranks-ok (drop-cred-edges w a)))) (rfl)
  (exact (i12-ranks-intro _ (well-formed-drop-act w a (i12-ranks-well-formed w h)) (Eq.trans hr (ranks-drop-cred w a (i12-ranks-ranks w h))))))
(swap! (:renames RK) assoc 'well-formed-drop-act 'i12-ranks-drop-act)

;; inserting an edge: rank-ok edges only
(a/theorem i12-ranks-insert-edge-fresh [w :- World, e :- EdgeRow]
  (=> (= (edge-ok-in w e) true) (= (rank-edge-ok w e) true) (= (i12-ranks w) true)
      (= (i12-ranks (insert-edge-fresh w e)) true))
  (intros he hr h)
  (exact (i12-ranks-intro _ (well-formed-insert-edge-fresh w e he (i12-ranks-well-formed w h))
           (ranks-insert-edge-fresh w e hr (i12-ranks-ranks w h)))))
(a/theorem i12-ranks-insert-edge-checked [w :- World, e :- EdgeRow]
  (=> (= (rank-edge-ok w e) true) (= (i12-ranks w) true) (= (i12-ranks (insert-edge-checked w e)) true))
  (intros hr h)
  (exact (i12-ranks-intro _ (well-formed-insert-edge-checked w e (i12-ranks-well-formed w h))
           (ranks-insert-edge-checked w e hr (i12-ranks-ranks w h)))))
(swap! (:renames RK) assoc 'well-formed-insert-edge-fresh 'i12-ranks-insert-edge-fresh 'well-formed-insert-edge-checked 'i12-ranks-insert-edge-checked)

;; ===========================================================================
;; Part C. The composite lemmas: the generic step tree (spindel.v2.pres.tree)
;; ===========================================================================

;; Every composite well-formed lemma under `step-well-formed` is restated for the bundle from the tree's
;; generic lemma (`restate!`), except the transitions that insert an edge or raise a rank: their
;; bundle proofs are written here (:over), each after the lemmas it uses.
(tree/part! RK
  :over '{well-formed-track-raw           i12-ranks-track-raw             ; T7: a dep edge on a source
          well-formed-react-add           i12-ranks-react-add             ; a reactivation edge, with its raise
          well-formed-host-await-raw      i12-ranks-host-await-raw        ; T22: a wait edge
          well-formed-take-park           i12-ranks-take-park             ; take: a wait edge
          well-formed-t8-observe-any-kind i12-ranks-t8-observe-any-kind   ; T8: no dep edge
          well-formed-t6-await            i12-ranks-t6-await})            ; T6: dep edges, with their raises

(tree/restate! RK '[well-formed-track-fin])

;; T7 track: the debtor is a source, no computation (unique ids), so the dep edge is rank-ok
(a/theorem i12-ranks-track-raw [w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat]
  (=> (= (comp-has w (:of r)) true) (= (source-find w x) (Option.some SourceRow s))
      (= (i12-ranks w) true) (= (i12-ranks (track-raw w r x s k)) true))
  (intros hc hs h)
  (have hx (= (comp-has w x) false))
  (exact (comp-not-source w x (And.right (And.right (i12-ranks-parts w h))) (tbl-find-has SourceRow source-id x s (:sources w) hs)))
  (have hk (= (rank-edge-ok w (track-edge r x s k)) true)) (simp [rank-edge-ok track-edge hx])
  (have h2 (= (i12-ranks (match (site-edge (:edges w) (:of r) (:effect-index r) x)
                             none (track-new w r x s k)
                             (some e) (comp-upd (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s)))
                                                (:of r) (comp-consume-adopt (:effect-index r) x)))) true))
  (cases he (site-edge (:edges w) (:of r) (:effect-index r) x)) (case' [some e]) (case' [none])
  (simp only [track-new])
  (exact (i12-ranks-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) x)
           (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [c :- CompRow] (Eq.refl (:rank c)))
           (i12-ranks-track-fin s (:next-id w) _ (i12-ranks-insert-edge-fresh w (track-edge r x s k) (track-edge-ok w r x s k hc hs) hk h))))
  (exact (i12-ranks-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) x)
           (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [c :- CompRow] (Eq.refl (:rank c)))
           (i12-ranks-track-fin s (:id e) _
             (i12-ranks-edge-upd w (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) (edge-reread-kind _ _)
               (edge-reread-creditor _ _) (edge-reread-debtor _ _) (edge-reread-marked _ _) h))))
  (simp only [track-raw])
  (exact (i12-ranks-run-upd _ (:id r) run-tick run-tick-run-id h2)))

;; a reactivation edge is kept only with an ok raise (spindel.v2.inv.rank)
(a/theorem i12-ranks-react-add [w :- World, c :- Nat, v :- Valid]
  (=> (= (i12-ranks w) true) (= (i12-ranks (react-add w c v)) true))
  (intro h)
  (exact (i12-ranks-intro _ (well-formed-react-add w c v (i12-ranks-well-formed w h)) (react-add-ranks w c v (i12-ranks-ranks w h)))))

;; T22: the host-wait edge is a wait edge
(tree/restate! RK '[well-formed-demand-reactive well-formed-fire-edge])

(a/theorem i12-ranks-host-await-raw [w :- World, d :- Nat]
  (=> (= (i12-ranks w) true) (= (i12-ranks (host-await-raw w d)) true))
  (intro h)
  (have hk (= (rank-edge-ok w (host-wait-edge d)) true)) (apply rank-edge-ok-nondep) (rfl)
  (have h1 (= (i12-ranks (host-await-dem w d)) true))
  (exact (i12-ranks-demand-reactive _ d (i12-ranks-insert-edge-checked w (host-wait-edge d) hk h)))
  (cases hr (fast-ready (host-await-dem w d) d))
  (case [false] (simp only [host-await-raw hr]) (exact h1))
  (case [true] (simp only [host-await-raw hr]) (exact (i12-ranks-fire-edge _ _ (:next-id w) h1))))

;; take: the parked take's edge is a wait edge
(a/theorem i12-ranks-take-park [w :- World, r :- RunRow, x :- Nat, k :- Nat]
  (=> (= (i12-ranks w) true) (= (i12-ranks (take-park w r x k)) true))
  (intro h)
  (have hk (= (rank-edge-ok (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x)) true))
  (apply rank-edge-ok-nondep) (rfl)
  (simp only [take-park])
  (exact (i12-ranks-run-upd _ (:id r) run-tick-park run-tick-park-id
           (i12-ranks-insert-edge-checked _ _ hk (i12-ranks-act-ins-fresh w (take-act w r k) (rfl) h)))))

;; T8: the observe edge is no dep edge
(a/theorem i12-ranks-t8-observe-any-kind [w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (i12-ranks w) true) (= (i12-ranks (:world (t8-observe-any-kind w d cb fresh))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
  (case [false] (simp only [t8-observe-any-kind hg refuse]) (exact h))
  (case [true]
    (have he (= (edge-ok-in w (observe-edge w d cb)) true))
    (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
    (have hk (= (rank-edge-ok w (observe-edge w d cb)) true)) (apply rank-edge-ok-nondep) (rfl)
    (have h1 := (i12-ranks-demand-reactive _ d (i12-ranks-insert-edge-fresh w (observe-edge w d cb) he hk h)))
    (simp only [t8-observe-any-kind hg accept observe-raw])
    (cases hr (deb-ready (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) d))
    (case [false] (simp only [hr]) (exact h1))
    (case [true] (simp only [hr]) (exact (i12-ranks-fire-edge _ _ (:next-id w) h1)))))

;; T6: the accumulator's ranks hold while `ok` (a dep edge on a computation comes with its
;; raise, spindel.v2.inv.rank's await-new-dep-ranks); T6 accepts only an ok accumulator
(a/theorem await-step-ranks [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (=> (= (:ok acc) true) (= (ranks-ok (:world acc)) true))
      (= (:ok (await-step r a mode k acc d)) true)
      (= (ranks-ok (:world (await-step r a mode k acc d))) true))
  (intros hr hok)
  (cases hd (as-dep (:world acc) r d))
  (case [false]
    (simp only [await-step hd] at hok)
    (simp only [await-step hd])
    (have hk (= (rank-edge-ok (:world acc) (await-edge (:world acc) r a mode k d)) true))
    (apply rank-edge-ok-nondep) (simp only [await-edge hd])
    (exact (ranks-insert-edge-checked _ _ hk (hr hok))))
  (case [true]
    (cases hs2 (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none]
      (simp only [await-step hd hs2 Bool.and_eq_true] at hok)
      (simp only [await-step hd hs2])
      (exact (ranks-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) d) (comp-consume-adopt-comp-id _ _)
               (fn [c :- CompRow] (Eq.refl (:rank c)))
               (await-new-dep-ranks (:world acc) r a mode k d (hr (And.left hok)) hd (And.right hok)))))
    (case [some e]
      (simp only [await-step hd hs2] at hok)
      (simp only [await-step hd hs2])
      (exact (ranks-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) d) (comp-consume-adopt-comp-id _ _)
               (fn [c :- CompRow] (Eq.refl (:rank c)))
               (ranks-edge-upd _ (:id e) (edge-reawait (await-cont r mode k)) (edge-reawait-kind _)
                 (edge-reawait-creditor _) (edge-reawait-debtor _) (hr hok)))))))

(a/theorem await-wire-ranks [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, ds :- (List Nat)]
  (forall [acc :- AwAcc]
    (=> (=> (= (:ok acc) true) (= (ranks-ok (:world acc)) true))
        (= (:ok (await-wire r a mode k acc ds)) true)
        (= (ranks-ok (:world (await-wire r a mode k acc ds))) true)))
  (induction ds)
  (case [nil] (intros acc hr hok) (simp only [await-wire] at hok) (simp only [await-wire]) (exact (hr hok)))
  (case [cons d t ih]
    (intros acc hr hok)
    (simp only [await-wire] at hok)
    (simp only [await-wire])
    (exact (ih (await-step r a mode k acc d)
             (fn [hok2 :- (= (:ok (await-step r a mode k acc d)) true)] (await-step-ranks r a mode k acc d hr hok2))
             hok))))

(tree/restate! RK '[well-formed-await-pre well-formed-await-post])

(a/theorem i12-ranks-await-raw [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (i12-ranks w) true) (= (:ok (await-acc w r ds mode k mine)) true)
      (= (i12-ranks (await-raw w r ds mode k mine)) true))
  (intros h hok)
  (have h1 := (i12-ranks-await-pre w r ds mode k mine h))
  (have hs (= (well-formed (:world (await-acc w r ds mode k mine))) true))
  (exact (well-formed-await-wire r (:next-id w) mode k (nat-distinct ds)
           (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (i12-ranks-well-formed _ h1)))
  (have hr (= (ranks-ok (:world (await-acc w r ds mode k mine))) true))
  (exact (await-wire-ranks r (:next-id w) mode k (nat-distinct ds)
           (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true)
           (fn [x :- (= (:ok (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true)) true)] (i12-ranks-ranks _ h1))
           hok))
  (exact (i12-ranks-await-post (:next-id w) (:id r) ds (await-acc w r ds mode k mine) (i12-ranks-intro _ hs hr))))

(a/theorem i12-ranks-t6-await [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
  (=> (= (i12-ranks w) true) (= (i12-ranks (:world (t6-await w st ds mode k fresh mine))) true))
  (intro h)
  (cases ht (tok-run w st))
  (case [none] (simp only [t6-await ht refuse]) (exact h))
  (case [some r]
    (cases hg (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
    (case [false] (simp only [t6-await ht hg refuse]) (exact h))
    (case [true]
      (simp only [t6-await ht hg accept])
      (simp only [Bool.and_eq_true] at hg)
      (exact (i12-ranks-await-raw w r ds mode k mine h (And.right hg))))))

;; ===========================================================================
;; The step
;; ===========================================================================

(tree/restate! RK '[step-well-formed])

(a/theorem i12-ranks-empty [] (= (i12-ranks empty-world) true) (rfl))

;; Theorem (P5): every step keeps the I12 rank order
(a/theorem step-ranks [w :- World, it :- Item]
  (=> (= (i12-ranks w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (ranks-ok (:world (world-step w it))) true))
  (intros h hs) (exact (i12-ranks-ranks _ (step-i12-ranks w it h hs))))
