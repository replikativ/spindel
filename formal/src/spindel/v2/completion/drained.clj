(ns spindel.v2.completion.drained
  "C1c stage B, proof stage, step 3: normalization. After `[:normalize]` (the layer-1 item `drain ids`, ids the
  cell's inherited markers W-NORMALIZE) the world holds none of them: `drain-clean`. The drain deletes them
  (`fold-del-out`); Z#18's removal (`remove-empty-at`), the any-loser cancel and Rule R add no marker (the bundle
  `markers-gone ids`: no marker with an id in ids, copied over them with spindel.v2.inv.copier's copier)."
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
            [spindel.v2.pres.part :refer [mk-bundle prim!]]
            [spindel.v2.inv.base]
            [spindel.v2.inv.acts]
            [spindel.v2.inv.marks-step :refer [chain-to-marks-waiting]]
            [spindel.v2.completion.quiet-world]
            [spindel.v2.owned :refer :all]))

;; ---- the bundle: no marker with an id in nids
(a/defn fork-out [ids :- (List Nat), f :- ForkRow] Bool (Bool.not (fork-in ids f)))
(a/defn markers-gone-rest [nids :- (List Nat), w :- World] Bool (tbl-all (fork-out nids) (:forks w)))
(a/defn markers-gone [nids :- (List Nat), w :- World] Bool (Bool.and (well-formed w) (markers-gone-rest nids w)))

(a/theorem markers-gone-well-formed [nids :- (List Nat), w :- World] (=> (= (markers-gone nids w) true) (= (well-formed w) true))
  (intro h) (simp only [markers-gone Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem markers-gone-rest-of [nids :- (List Nat), w :- World] (=> (= (markers-gone nids w) true) (= (markers-gone-rest nids w) true))
  (intro h) (simp only [markers-gone Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem markers-gone-intro [nids :- (List Nat), w :- World] (=> (= (well-formed w) true) (= (markers-gone-rest nids w) true) (= (markers-gone nids w) true))
  (intros h1 h2) (simp only [markers-gone h1 h2 Bool.and_self]))
(a/theorem markers-gone-parts [nids :- (List Nat), w :- World]
  (=> (= (markers-gone nids w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (markers-gone-well-formed nids w h))))

(a/theorem markers-gone-rest-fork-del [nids :- (List Nat), w :- World, x :- Nat]
  (=> (= (markers-gone-rest nids w) true) (= (markers-gone-rest nids (fork-del w x)) true))
  (intro h) (simp only [markers-gone-rest] at h) (simp only [markers-gone-rest fork-del set-forks])
  (exact (tbl-all-del ForkRow fork-id x _ _ (fn [f :- ForkRow, p :- (= (fork-out nids f) true), q :- (= (Nat.beq (fork-id f) x) false)] p) _ h)))
(a/theorem markers-gone-rest-filter [nids :- (List Nat), w :- World, K :- (=> Nat Bool)]
  (=> (= (markers-gone-rest nids w) true) (= (markers-gone-rest nids (filter-world K w)) true))
  (intro h) (simp only [markers-gone-rest] at h) (simp only [markers-gone-rest filter-world])
  (exact (tbl-all-keep-same ForkRow K fork-id _ _ h)))

(def GNF (mk-bundle 'markers-gone '[nids :- (List Nat)] "markers-gone-" {}))
(swap! (:renames GNF) assoc 'well-formed-parts 'markers-gone-parts)
(doseq [o '[well-formed-scope-upd well-formed-pub-upd well-formed-source-upd well-formed-resource-upd well-formed-cleanup-upd well-formed-cleanup-del well-formed-set-pins
            well-formed-resource-del well-formed-scope-del well-formed-cleanup-ins well-formed-act-upd well-formed-edge-upd well-formed-drop-cred-edges well-formed-drop-edges
            well-formed-comp-del-unref well-formed-comp-upd well-formed-drop-act well-formed-task-upd well-formed-run-upd well-formed-run-ins-fresh well-formed-run-del
            well-formed-source-ins-fresh well-formed-resource-ins-fresh well-formed-scope-ins-fresh well-formed-comp-ins-fresh well-formed-act-ins-fresh
            well-formed-task-ins-fresh well-formed-bump well-formed-insert-edge-fresh well-formed-set-pending-act well-formed-set-released
            ]]
  (prim! GNF o nil))
(a/theorem markers-gone-rest-mark-edge [nids :- (List Nat), w :- World, x :- Nat] (= (markers-gone-rest nids (mark-edge w x)) (markers-gone-rest nids w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem markers-gone-rest-unmark-edge [nids :- (List Nat), w :- World, x :- Nat] (= (markers-gone-rest nids (unmark-edge w x)) (markers-gone-rest nids w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem markers-gone-rest-remove-edge [nids :- (List Nat), w :- World, x :- Nat] (= (markers-gone-rest nids (remove-edge w x)) (markers-gone-rest nids w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))
(prim! GNF 'well-formed-mark-edge '(Eq.trans (markers-gone-rest-mark-edge nids w x) R))
(prim! GNF 'well-formed-unmark-edge '(Eq.trans (markers-gone-rest-unmark-edge nids w x) R))
(prim! GNF 'well-formed-remove-edge '(Eq.trans (markers-gone-rest-remove-edge nids w x) R))
(prim! GNF 'well-formed-fork-del '(markers-gone-rest-fork-del nids w x R))
(prim! GNF 'well-formed-filter-world '(markers-gone-rest-filter nids w K R))

(tree/restate! GNF '[well-formed-remove-empty-at well-formed-nat-fold well-formed-cancel-losers well-formed-normalize])

(a/theorem markers-gone-rule-r-round [nids :- (List Nat), w :- World]
  (=> (= (markers-gone nids w) true) (= (filter-safe (normalize w)) true) (= (markers-gone nids (rule-r-round w)) true))
  (intros h hf) (simp only [rule-r-round]) (rw [rule-r-filter-eq])
  (exact (markers-gone-filter-world nids (normalize w) (keep-fn (normalize w)) (markers-gone-normalize nids w h) hf)))
(a/theorem markers-gone-rule-r-loop [nids :- (List Nat), fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (markers-gone nids w0) true) (= (rounds-safe-loop fuel w0) true) (= (markers-gone nids (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (markers-gone-rule-r-round nids w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (markers-gone-rule-r-round nids w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))
(a/theorem markers-gone-rule-r [nids :- (List Nat), w :- World] (=> (= (markers-gone nids w) true) (= (rule-r-safe w) true) (= (markers-gone nids (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (markers-gone-rule-r-loop nids (rule-r-fuel w) w h hs)))

;; ---- the drain deletes every marker with an id in ids
(a/theorem out-cons [x :- Nat, t :- (List Nat), f :- ForkRow]
  (=> (= (fork-out t f) true) (= (Bool.not (Nat.beq (:id f) x)) true) (= (fork-out (List.cons Nat x t) f) true))
  (intros p q)
  (have e := (bnot-true _ q))
  (simp [fork-out fork-in] at p)
  (simp [fork-out fork-in reach-mem e])
  (exact p))
(a/theorem any-false-out [ids :- (List Nat), fs :- (List ForkRow)]
  (=> (= (tbl-any (fork-in ids) fs) false) (= (tbl-all (fork-out ids) fs) true))
  (induction fs)
  (case [nil] (intro q) (simp only [tbl-all]))
  (case [cons h t ih]
    (intro q) (simp only [tbl-any Bool.or_eq_false_iff] at q)
    (simp only [tbl-all fork-out (And.left q) (ih (And.right q)) Bool.not_false Bool.and_self])))
(a/theorem fork-del-ne [x :- Nat, fs :- (List ForkRow)] (= (tbl-all (fn [f :- ForkRow] (Bool.not (Nat.beq (:id f) x))) (tbl-del fork-id x fs)) true)
  (induction fs)
  (case [nil] (simp only [tbl-del tbl-all]))
  (case [cons h t ih]
    (cases hx (Nat.beq (fork-id h) x))
    (case [true] (simp only [tbl-del hx ih]))
    (case [false] (have e (= (Nat.beq (:id h) x) false)) (exact hx) (simp only [tbl-del hx tbl-all e ih Bool.not_false Bool.and_self]))))
(a/theorem fold-del-keeps [P :- (=> ForkRow Bool), xs :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all P (:forks w)) true) (= (tbl-all P (:forks (nat-fold fork-del w xs))) true)))
  (induction xs)
  (case [nil] (intros w h) (simp only [nat-fold]) (exact h))
  (case [cons x t ih]
    (intros w h) (simp only [nat-fold])
    (apply (ih (fork-del w x)))
    (simp only [fork-del set-forks])
    (exact (tbl-all-del ForkRow fork-id x P P (fn [f :- ForkRow, p :- (= (P f) true), q :- (= (Nat.beq (fork-id f) x) false)] p) _ h))))
(a/theorem fold-del-out [xs :- (List Nat)]
  (forall [w :- World] (= (tbl-all (fork-out xs) (:forks (nat-fold fork-del w xs))) true))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold])
    (have g (forall [fs :- (List ForkRow)] (= (tbl-all (fork-out (List.nil Nat)) fs) true)))
    (intro fs) (induction fs) (case [nil] (simp only [tbl-all])) (case [cons h t ih2] (simp only [tbl-all fork-out fork-in reach-mem ih2 Bool.not_false Bool.and_self]))
    (exact (g (:forks w))))
  (case [cons x t ih]
    (intro w) (simp only [nat-fold])
    (have a1 := (ih (fork-del w x)))
    (have a2 := (fold-del-keeps (fn [f :- ForkRow] (Bool.not (Nat.beq (:id f) x))) t (fork-del w x) (fork-del-ne x (:forks w))))
    (exact (tbl-all-mono2 ForkRow (fork-out t) (fn [f :- ForkRow] (Bool.not (Nat.beq (:id f) x))) (fork-out (List.cons Nat x t))
             (fn [f :- ForkRow, p :- (= (fork-out t f) true), q :- (= (Bool.not (Nat.beq (:id f) x)) true)]
               (out-cons x t f p q))
             _ a1 a2))))

;; Theorem (normalization): after the drain the world holds no marker with an id in ids (the refused drain: there was
;; none)
(a/theorem drain-clean [w :- World, ids :- (List Nat)]
  (=> (= (chain-to-marks-waiting w) true) (= (tbl-all (fork-out ids) (:forks (drain-world w ids))) true))
  (intro hp)
  (cases hm (tbl-any (fork-in ids) (:forks w)))
  (case [false]
    (have e (= (drain-world w ids) w))
    (simp only [drain-world]) (apply (internal-refused w (Item.drain ids) (rfl))) (simp only [transition t-drain hm refuse])
    (rw [e]) (exact (any-false-out ids (:forks w) hm)))
  (case [true]
    (have ha (= (:accepted (raw w (Item.drain ids))) true))
    (simp only [raw then-cancel-losers host-guarded-transition host-item-refused host-item Bool.false_and Bool.and_false transition t-drain hm accept])
    (have er := (step-accepted w (Item.drain ids) ha))
    (have ew (= (:world (raw w (Item.drain ids)))
                (cancel-losers w (nat-fold remove-empty-at (nat-fold fork-del w ids) (owners-in ids (:forks w))))))
    (simp only [raw then-cancel-losers host-guarded-transition host-item-refused host-item Bool.false_and Bool.and_false transition t-drain hm accept])
    (have hs := (step-rule-r-safe w (Item.drain ids) (chain-to-marks-waiting-implies-chain-start w hp)))
    (rw [ew] at hs)
    (have hi := (acts-parked-well-formed w (And.left (chain-start-parts w (chain-to-marks-waiting-implies-chain-start w hp)))))
    (have g0 (= (markers-gone ids (nat-fold fork-del w ids)) true))
    (exact (markers-gone-intro ids _ (well-formed-nat-fold fork-del well-formed-fork-del ids w hi) (fold-del-out ids w)))
    (have g1 := (markers-gone-nat-fold ids remove-empty-at (markers-gone-remove-empty-at ids) (owners-in ids (:forks w)) (nat-fold fork-del w ids) g0))
    (have g2 := (markers-gone-cancel-losers ids w _ g1))
    (have g3 := (markers-gone-rule-r ids _ g2 hs))
    (simp only [drain-world]) (rw [er ew]) (exact (markers-gone-rest-of ids _ g3))))
