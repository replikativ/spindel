(ns spindel.v2.rank-step
  "Obligation P5: I12 ranks (`ranks-ok`) are preserved by EVERY transition, kernel-checked
  (Init only). The bundle is `inv-rank w = inv-sample w && ranks-ok w`.

    step-rank   inv-rank w, rule-r-safe (:world (raw w it)) -> inv-rank (:world (world-step w it))

  (the hypotheses of `step-inv`; ranks themselves need no extra hypothesis.)

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
      raise (spindel.v2.rank: `await-new-dep-ranks`, `react-add-ranks`);
    - a fresh computation (T3) has an id that no edge names (`edge-fresh-ok`, from
      edges-ref-ok and ids-below of inv-sample);
    - ranks change only in the raise (spindel.v2.rank).
  Part B lifts each to the bundle (`rk-<edit>`: the inv-sample lemma plus the ranks lemma).

  Part C: every composite inv-sample lemma that `step-inv` depends on is re-checked for the
  bundle by `rank-copy!`: the theorem's source form (read from its namespace, lemma-defining
  macros expanded) with `inv-sample` replaced by `inv-rank` and every inv-sample lemma by its
  bundle version (`inv-X` -> `rk-X`, `X-inv` -> `X-rk`; `inv-comp-upd` gains the rank
  argument `(fn [c] (rfl))`). The transitions whose inv-sample proof does not carry over
  (T6 await: the raise's `ok`; the edge inserts of T7 track, T8, T22, take, reactivation; the
  T3 creation) have hand-written bundle proofs (`rank-overrides`), checked at their place
  in the dependency order. Every copied theorem is an ordinary kernel-checked theorem in the
  env (`rank-copied` lists them); nothing is trusted from the copy mechanism."
  (:require [ansatz.core :as a]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.rank :refer :all]))

;; ===========================================================================
;; The bundle
;; ===========================================================================

(a/defn inv-rank [w :- World] Bool (Bool.and (inv-sample w) (ranks-ok w)))

(a/theorem rk-sample [w :- World] (=> (= (inv-rank w) true) (= (inv-sample w) true))
  (intro h) (simp only [inv-rank Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem rk-ranks [w :- World] (=> (= (inv-rank w) true) (= (ranks-ok w) true))
  (intro h) (simp only [inv-rank Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem rk-intro [w :- World] (=> (= (inv-sample w) true) (= (ranks-ok w) true) (= (inv-rank w) true))
  (intros h1 h2) (simp only [inv-rank h1 h2 Bool.and_self]))
(a/theorem rk-parts [w :- World]
  (=> (= (inv-rank w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (rk-sample w h))))

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
  (=> (= (comp-id r) (:next-id w)) (= (inv-sample w) true) (= (ranks-ok w) true)
      (= (ranks-ok (bump (comp-ins w r))) true))
  (intros hr hs h)
  (have hp := (inv-parts w hs))
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

;; `rk-prim!`: the bundle version of a primitive inv-sample lemma (same binders and
;; premises; the inv-sample premise becomes inv-rank) from the inv-sample lemma and a ranks
;; proof. `ranks` is a form over the source binder names, the premise names `h0 ... hn`, and
;; `R` = ranks-ok of the input world; nil = the edit leaves ranks-ok definitionally unchanged.

(def ^:private rank-ns *ns*)

(defn- ns-source-forms [ns-sym]
  (let [path (str (-> (name ns-sym) (str/replace "." "/") (str/replace "-" "_")) ".clj")
        the-ns (the-ns ns-sym)]
    (binding [*ns* the-ns]
      (with-open [r (java.io.PushbackReader. (io/reader (io/resource path)))]
        (loop [acc []]
          (let [f (read {:eof ::eof} r)]
            (if (= f ::eof) acc (recur (conj acc f)))))))))

(defn- theorem-form? [f]
  (and (seq? f) (contains? #{'a/theorem 'ansatz.core/theorem} (first f))))

(defn- expand-top [ns-sym f]
  ;; lemma-defining macros of the namespace itself are expanded; `do` is flattened
  (cond
    (and (seq? f) (= 'do (first f))) (mapcat #(expand-top ns-sym %) (rest f))
    (and (seq? f) (symbol? (first f)) (not (theorem-form? f)))
    (let [v (binding [*ns* (the-ns ns-sym)] (resolve (first f)))]
      (if (and (var? v) (:macro (meta v)) (= (the-ns ns-sym) (:ns (meta v))))
        (expand-top ns-sym (binding [*ns* (the-ns ns-sym)] (macroexpand-1 f)))
        [f]))
    :else [f]))

(def source-nss '[spindel.v2.edits spindel.v2.step spindel.v2.rule spindel.v2.engine])

(def ^:private source-theorems
  "[name form] of every theorem of the source namespaces, in load order."
  (delay
    (vec (for [nsym source-nss, f (ns-source-forms nsym), g (expand-top nsym f) :when (theorem-form? g)]
           [(second g) g]))))

(defn- theorem-source [nm]
  (or (some (fn [[n g]] (when (= n nm) g)) @source-theorems)
      (throw (ex-info (str "no source for theorem " nm) {:name nm}))))

(defn- binder-names [binders] (vec (take-nth 3 binders)))

(defn- inv-premise? [p] (and (seq? p) (= '= (first p)) (seq? (second p)) (= 'inv-sample (first (second p)))))

(def ^:private renames
  "inv-sample lemma -> its bundle version"
  (atom {}))

(defn- eval-theorem! [form]
  (try (binding [*ns* rank-ns] (eval form))
       (catch Throwable t
         (throw (ex-info (str "rank-step: theorem " (second form) " failed: " (ex-message t)) {:form form} t)))))

(defn- prim-form [orig rk ranks]
  (let [[_ _ binders stmt] (theorem-source orig)
        _ (assert (and (seq? stmt) (= '=> (first stmt))) (str orig ": statement is not an implication"))
        prems (butlast (rest stmt))
        concl (last stmt)
        hs (vec (map-indexed (fn [i _] (symbol (str "h" i))) prems))
        i (first (keep-indexed (fn [i p] (when (inv-premise? p) i)) prems))
        w (second (second (nth prems i)))
        w2 (second (second concl))
        hi (nth hs i)
        args (concat (binder-names binders) (assoc hs i (list 'rk-sample w hi)))
        R (list 'rk-ranks w hi)
        ranks-term (if ranks
                     (walk/postwalk-replace {'R R} ranks)
                     (list 'Eq.trans 'e-frame R))
        sub (fn [x] (walk/postwalk-replace {'inv-sample 'inv-rank} x))]
    (concat
     (list 'a/theorem rk binders (sub stmt) (cons 'intros hs))
     (when-not ranks [(list 'have 'e-frame (list '= (list 'ranks-ok w2) (list 'ranks-ok w))) '(rfl)])
     [(list 'exact (list 'rk-intro w2 (cons orig args) ranks-term))])))

(defn- rk-prim! [orig rk ranks]
  (eval-theorem! (apply list (prim-form orig rk ranks)))
  (swap! renames assoc orig rk))

(defmacro ^:private defrk-prims [& specs]
  `(do ~@(for [[orig rk ranks] (partition 3 specs)] `(rk-prim! '~orig '~rk '~ranks))))

(defrk-prims
  ;; edits that touch neither edges nor computations (rfl frame)
  inv-run-upd rk-run-upd nil
  inv-scope-upd rk-scope-upd nil
  inv-pub-upd rk-pub-upd nil
  inv-source-upd rk-source-upd nil
  inv-task-upd rk-task-upd nil
  inv-act-upd rk-act-upd nil
  inv-resource-upd rk-resource-upd nil
  inv-cleanup-upd rk-cleanup-upd nil
  inv-cleanup-del rk-cleanup-del nil
  inv-set-pins rk-set-pins nil
  inv-run-del rk-run-del nil
  inv-resource-del rk-resource-del nil
  inv-source-ins-fresh rk-source-ins-fresh nil
  inv-resource-ins-fresh rk-resource-ins-fresh nil
  inv-scope-ins-fresh rk-scope-ins-fresh nil
  inv-run-ins-fresh rk-run-ins-fresh nil
  inv-task-ins-fresh rk-task-ins-fresh nil
  inv-act-ins-fresh rk-act-ins-fresh nil
  inv-bump rk-bump nil
  inv-scope-del rk-scope-del nil
  inv-cleanup-ins rk-cleanup-ins nil
  ;; edge edits
  mark-edge-inv-sample mark-edge-rk (ranks-mark-edge w x R)
  unmark-edge-inv-sample unmark-edge-rk (ranks-unmark-edge w x R)
  inv-edge-upd rk-edge-upd (ranks-edge-upd w x f hk hc hd R)
  inv-remove-edge rk-remove-edge (ranks-remove-edge w x R)
  inv-drop-cred rk-drop-cred (ranks-drop-cred w a R)
  inv-drop-edges rk-drop-edges (ranks-drop-edges w p R)
  ;; computation edits
  inv-comp-del-unref rk-comp-del-unref (ranks-comp-del w x R)
  inv-comp-ins-fresh rk-comp-ins-fresh (ranks-comp-ins-fresh w r h0 (rk-sample w h2) R)
  inv-filter-world rk-filter-world (ranks-filter-world w K R))

;; computation updates: one more argument, the row function keeps the rank
(a/theorem rk-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hr :- (forall [c :- CompRow] (= (:rank (f c)) (:rank c)))]
  (=> (= (inv-rank w) true) (= (inv-rank (comp-upd w x f)) true))
  (intro h)
  (exact (rk-intro _ (inv-comp-upd w x f hid hp (rk-sample w h)) (ranks-comp-upd w x f hid hr (rk-ranks w h)))))
(swap! renames assoc 'inv-comp-upd 'rk-comp-upd 'inv-parts 'rk-parts)

;; activation removal (with its creditor edges)
(a/theorem rk-drop-act [w :- World, a :- Nat]
  (=> (= (inv-rank w) true) (= (inv-rank (drop-act w a)) true))
  (intro h)
  (have hr (= (ranks-ok (drop-act w a)) (ranks-ok (drop-cred-edges w a)))) (rfl)
  (exact (rk-intro _ (inv-drop-act w a (rk-sample w h)) (Eq.trans hr (ranks-drop-cred w a (rk-ranks w h))))))
(swap! renames assoc 'inv-drop-act 'rk-drop-act)

;; inserting an edge: rank-ok edges only
(a/theorem insert-edge-fresh-rk [w :- World, e :- EdgeRow]
  (=> (= (edge-ok-in w e) true) (= (rank-edge-ok w e) true) (= (inv-rank w) true)
      (= (inv-rank (insert-edge-fresh w e)) true))
  (intros he hr h)
  (exact (rk-intro _ (insert-edge-fresh-inv-sample w e he (rk-sample w h))
           (ranks-insert-edge-fresh w e hr (rk-ranks w h)))))
(a/theorem rk-insert-edge-checked [w :- World, e :- EdgeRow]
  (=> (= (rank-edge-ok w e) true) (= (inv-rank w) true) (= (inv-rank (insert-edge-checked w e)) true))
  (intros hr h)
  (exact (rk-intro _ (inv-insert-edge-checked w e (rk-sample w h))
           (ranks-insert-edge-checked w e hr (rk-ranks w h)))))
(swap! renames assoc 'insert-edge-fresh-inv-sample 'insert-edge-fresh-rk 'inv-insert-edge-checked 'rk-insert-edge-checked)

;; ===========================================================================
;; Part C. The composite lemmas, copied (see the namespace docstring)
;; ===========================================================================

(defn- statement-mentions-inv? [form]
  (let [[_ _ binders stmt] form] (boolean (some #{'inv-sample} (flatten (list (seq binders) stmt))))))

(defn- rank-name [sym]
  (let [s (name sym)]
    (symbol (cond (str/ends-with? s "-inv-sample") (str (subs s 0 (- (count s) 11)) "-rk")
                  (str/starts-with? s "inv-") (str "rk-" (subs s 4))
                  (str/ends-with? s "-inv") (str (subs s 0 (- (count s) 4)) "-rk")
                  :else (str s "-rk")))))

(defn- rank-subst [x rn]
  (cond
    (and (seq? x) (= 'inv-comp-upd (first x)))
    (let [[_ W X F HID HP & more] x]
      (assert (= 1 (count more)) (str "inv-comp-upd call with unexpected arity: " (pr-str x)))
      (apply list 'rk-comp-upd (map #(rank-subst % rn)
                                    (concat [W X F HID HP '(fn [c :- CompRow] (Eq.refl (:rank c)))] more))))
    (= x 'inv-comp-upd) (throw (ex-info "inv-comp-upd used as a value" {}))
    (seq? x) (apply list (map #(rank-subst % rn) x))
    (vector? x) (mapv #(rank-subst % rn) x)
    (symbol? x) (cond (= x 'inv-sample) 'inv-rank
                      (contains? rn x) (rn x)
                      :else x)
    :else x))

(defn- rank-form [form rk rn]
  (let [[head _ binders stmt & proof] form]
    (apply list head rk (rank-subst binders rn) (rank-subst stmt rn) (map #(rank-subst % rn) proof))))

(def ^:private rank-overrides
  "Bundle proofs written by hand, keyed by the inv-sample lemma they replace (registered in
  load order, so they may use every bundle lemma before them)."
  (atom {}))

(defmacro ^:private defrank-override
  "`orig`: the inv-sample lemma replaced; `deps`: the inv-sample lemmas whose bundle versions
  the form uses (copied first); `form`: the bundle theorem."
  [orig deps form]
  `(swap! rank-overrides assoc '~orig {:deps '~deps :form '~form}))

(def rank-copied
  "the theorems checked by rank-copy!, in order"
  (atom []))

(defn- rank-closure [root]
  (let [thms @source-theorems
        S (set (keep (fn [[n g]] (when (statement-mentions-inv? g) n)) thms))
        deps (fn [n]
               (cond (contains? @renames n) []
                     (contains? @rank-overrides n) (:deps (get @rank-overrides n))
                     :else (let [[_ _ _ _ & proof] (theorem-source n)]
                             (filter S (filter symbol? (flatten proof))))))]
    (loop [todo [root] seen #{}]
      (if-let [n (first todo)]
        (if (seen n) (recur (rest todo) seen) (recur (concat (rest todo) (deps n)) (conj seen n)))
        (filterv seen (map first thms))))))

(defn rank-copy!
  "Check the bundle version of every inv-sample lemma `root` depends on, in load order."
  [root rk-root]
  (doseq [n (rank-closure root) :when (not (contains? @renames n))]
    (let [rk (if (= n root) rk-root (rank-name n))
          form (if-let [o (get @rank-overrides n)]
                 (:form o)
                 (rank-form (theorem-source n) rk @renames))]
      (eval-theorem! form)
      (swap! renames assoc n (second form))
      (swap! rank-copied conj (second form)))))

;; ---- hand-written bundle proofs

;; T7 track: the debtor is a source, no computation (unique ids), so the dep edge is rank-ok
(defrank-override inv-track-raw [inv-track-fin]
  (a/theorem rk-track-raw [w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat]
    (=> (= (comp-has w (:of r)) true) (= (source-find w x) (Option.some SourceRow s))
        (= (inv-rank w) true) (= (inv-rank (track-raw w r x s k)) true))
    (intros hc hs h)
    (have hx (= (comp-has w x) false))
    (exact (comp-not-source w x (And.right (And.right (rk-parts w h))) (tbl-find-has SourceRow source-id x s (:sources w) hs)))
    (have hk (= (rank-edge-ok w (track-edge r x s k)) true)) (simp [rank-edge-ok track-edge hx])
    (have h2 (= (inv-rank (match (site-edge (:edges w) (:of r) (:effect-index r) x)
                               [none (track-new w r x s k)]
                               [(some e) (comp-upd (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s)))
                                                   (:of r) (comp-consume-adopt (:effect-index r) x))])) true))
    (cases he (site-edge (:edges w) (:of r) (:effect-index r) x)) (case' [some e]) (case' [none])
    (simp only [track-new])
    (exact (rk-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) x)
             (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [c :- CompRow] (Eq.refl (:rank c)))
             (rk-track-fin s (:next-id w) _ (insert-edge-fresh-rk w (track-edge r x s k) (track-edge-ok w r x s k hc hs) hk h))))
    (exact (rk-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) x)
             (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [c :- CompRow] (Eq.refl (:rank c)))
             (rk-track-fin s (:id e) _
               (rk-edge-upd w (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) (edge-reread-kind _ _)
                 (edge-reread-creditor _ _) (edge-reread-debtor _ _) (edge-reread-marked _ _) h))))
    (simp only [track-raw])
    (exact (rk-run-upd _ (:id r) run-tick run-tick-run-id h2))))

;; a reactivation edge is kept only with an ok raise (spindel.v2.rank)
(defrank-override inv-react-add []
  (a/theorem rk-react-add [w :- World, c :- Nat, v :- Valid]
    (=> (= (inv-rank w) true) (= (inv-rank (react-add w c v)) true))
    (intro h)
    (exact (rk-intro _ (inv-react-add w c v (rk-sample w h)) (react-add-ranks w c v (rk-ranks w h))))))

;; T22: the host-wait edge is a wait edge
(defrank-override inv-host-await-raw [inv-demand-reactive inv-fire-edge]
  (a/theorem rk-host-await-raw [w :- World, d :- Nat]
    (=> (= (inv-rank w) true) (= (inv-rank (host-await-raw w d)) true))
    (intro h)
    (have hk (= (rank-edge-ok w (host-wait-edge d)) true)) (apply rank-edge-ok-nondep) (rfl)
    (have h1 (= (inv-rank (host-await-dem w d)) true))
    (exact (rk-demand-reactive _ d (rk-insert-edge-checked w (host-wait-edge d) hk h)))
    (cases hr (fast-ready (host-await-dem w d) d))
    (case [false] (simp only [host-await-raw hr]) (exact h1))
    (case [true] (simp only [host-await-raw hr]) (exact (rk-fire-edge _ _ (:next-id w) h1)))))

;; take: the parked take's edge is a wait edge
(defrank-override inv-take-park []
  (a/theorem rk-take-park [w :- World, r :- RunRow, x :- Nat, k :- Nat]
    (=> (= (inv-rank w) true) (= (inv-rank (take-park w r x k)) true))
    (intro h)
    (have hk (= (rank-edge-ok (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x)) true))
    (apply rank-edge-ok-nondep) (rfl)
    (simp only [take-park])
    (exact (rk-run-upd _ (:id r) run-tick-park run-tick-park-id
             (rk-insert-edge-checked _ _ hk (rk-act-ins-fresh w (take-act w r k) (rfl) h))))))

;; T8: the observe edge is no dep edge
(defrank-override t8-full-inv [inv-demand-reactive inv-fire-edge]
  (a/theorem t8-full-rk [w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
    (=> (= (inv-rank w) true) (= (inv-rank (:world (t8-full w d cb fresh))) true))
    (intro h)
    (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
    (case [false] (simp only [t8-full hg refuse]) (exact h))
    (case [true]
      (have he (= (edge-ok-in w (observe-edge w d cb)) true))
      (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
      (have hk (= (rank-edge-ok w (observe-edge w d cb)) true)) (apply rank-edge-ok-nondep) (rfl)
      (have h1 := (rk-demand-reactive _ d (insert-edge-fresh-rk w (observe-edge w d cb) he hk h)))
      (simp only [t8-full hg accept observe-raw])
      (cases hr (deb-ready (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) d))
      (case [false] (simp only [hr]) (exact h1))
      (case [true] (simp only [hr]) (exact (rk-fire-edge _ _ (:next-id w) h1))))))

;; T6: the accumulator's ranks hold while `ok` (a dep edge on a computation comes with its
;; raise, spindel.v2.rank's await-new-dep-ranks); T6 accepts only an ok accumulator
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

(defrank-override inv-await-raw [inv-await-pre inv-await-post]
  (a/theorem rk-await-raw [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
    (=> (= (inv-rank w) true) (= (:ok (await-acc w r ds mode k mine)) true)
        (= (inv-rank (await-raw w r ds mode k mine)) true))
    (intros h hok)
    (have h1 := (rk-await-pre w r ds mode k mine h))
    (have hs (= (inv-sample (:world (await-acc w r ds mode k mine))) true))
    (exact (inv-await-wire r (:next-id w) mode k (nat-distinct ds)
             (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (rk-sample _ h1)))
    (have hr (= (ranks-ok (:world (await-acc w r ds mode k mine))) true))
    (exact (await-wire-ranks r (:next-id w) mode k (nat-distinct ds)
             (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true)
             (fn [x :- (= (:ok (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true)) true)] (rk-ranks _ h1))
             hok))
    (exact (rk-await-post (:next-id w) (:id r) ds (await-acc w r ds mode k mine) (rk-intro _ hs hr)))))

(defrank-override t6-inv [inv-await-raw]
  (a/theorem t6-rk [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
    (=> (= (inv-rank w) true) (= (inv-rank (:world (t6-await w st ds mode k fresh mine))) true))
    (intro h)
    (cases ht (tok-run w st))
    (case [none] (simp only [t6-await ht refuse]) (exact h))
    (case [some r]
      (cases hg (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
      (case [false] (simp only [t6-await ht hg refuse]) (exact h))
      (case [true]
        (simp only [t6-await ht hg accept])
        (simp only [Bool.and_eq_true] at hg)
        (exact (rk-await-raw w r ds mode k mine h (And.right hg)))))))

;; ===========================================================================
;; The step
;; ===========================================================================

(rank-copy! 'step-inv 'step-rank)

(a/theorem inv-rank-empty [] (= (inv-rank empty-world) true) (rfl))

;; Theorem (P5): every step keeps the I12 rank order
(a/theorem step-ranks [w :- World, it :- Item]
  (=> (= (inv-rank w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (ranks-ok (:world (world-step w it))) true))
  (intros h hs) (exact (rk-ranks _ (step-rank w it h hs))))
