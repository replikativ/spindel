(ns spindel.v2.completion.drained
  "C1c stage B, proof stage, step 3: normalization. After `[:normalize]` (the layer-1 item `drain ids`, ids the
  cell's inherited markers W-NORMALIZE) the world holds none of them: `drain-clean`. The drain deletes them
  (`fold-del-out`); Z#18's removal (`remove-empty-at`), the any-loser cancel and Rule R add no marker (the bundle
  `gnf ids`: no marker with an id in ids, copied over them with spindel.v2.inv.copier's copier)."
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
            [spindel.v2.inv.copier :refer [mk-bundle prim! lcopy! override!]]
            [spindel.v2.inv.base]
            [spindel.v2.inv.acts]
            [spindel.v2.inv.marks-step :refer [p3l]]
            [spindel.v2.completion.quiet-world]
            [spindel.v2.owned :refer :all]))

;; ---- the bundle: no marker with an id in nids
(a/defn fork-out [ids :- (List Nat), f :- ForkRow] Bool (Bool.not (fork-in ids f)))
(a/defn gnf-rest [nids :- (List Nat), w :- World] Bool (tbl-all (fork-out nids) (:forks w)))
(a/defn gnf [nids :- (List Nat), w :- World] Bool (Bool.and (inv-sample w) (gnf-rest nids w)))

(a/theorem gnf-sample [nids :- (List Nat), w :- World] (=> (= (gnf nids w) true) (= (inv-sample w) true))
  (intro h) (simp only [gnf Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem gnf-rest-of [nids :- (List Nat), w :- World] (=> (= (gnf nids w) true) (= (gnf-rest nids w) true))
  (intro h) (simp only [gnf Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem gnf-intro [nids :- (List Nat), w :- World] (=> (= (inv-sample w) true) (= (gnf-rest nids w) true) (= (gnf nids w) true))
  (intros h1 h2) (simp only [gnf h1 h2 Bool.and_self]))
(a/theorem gnf-parts [nids :- (List Nat), w :- World]
  (=> (= (gnf nids w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (gnf-sample nids w h))))

(a/theorem gnf-rest-fork-del [nids :- (List Nat), w :- World, x :- Nat]
  (=> (= (gnf-rest nids w) true) (= (gnf-rest nids (fork-del w x)) true))
  (intro h) (simp only [gnf-rest] at h) (simp only [gnf-rest fork-del set-forks])
  (exact (tbl-all-del ForkRow fork-id x _ _ (fn [f :- ForkRow, p :- (= (fork-out nids f) true), q :- (= (Nat.beq (fork-id f) x) false)] p) _ h)))
(a/theorem gnf-rest-filter [nids :- (List Nat), w :- World, K :- (=> Nat Bool)]
  (=> (= (gnf-rest nids w) true) (= (gnf-rest nids (filter-world K w)) true))
  (intro h) (simp only [gnf-rest] at h) (simp only [gnf-rest filter-world])
  (exact (tbl-all-keep-same ForkRow K fork-id _ _ h)))

(def GNF (mk-bundle 'gnf '[nids :- (List Nat)] "gnf-" {}))
(swap! (:renames GNF) assoc 'inv-parts 'gnf-parts)
(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-set-pins
            inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-edge-upd inv-drop-cred inv-drop-edges
            inv-comp-del-unref inv-comp-upd inv-drop-act inv-task-upd inv-run-upd inv-run-ins-fresh inv-run-del
            inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-comp-ins-fresh inv-act-ins-fresh
            inv-task-ins-fresh inv-bump insert-edge-fresh-inv-sample inv-set-pending-act inv-set-released
            ]]
  (prim! GNF o nil))
(a/theorem gnf-rest-mark-edge [nids :- (List Nat), w :- World, x :- Nat] (= (gnf-rest nids (mark-edge w x)) (gnf-rest nids w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem gnf-rest-unmark-edge [nids :- (List Nat), w :- World, x :- Nat] (= (gnf-rest nids (unmark-edge w x)) (gnf-rest nids w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem gnf-rest-remove-edge [nids :- (List Nat), w :- World, x :- Nat] (= (gnf-rest nids (remove-edge w x)) (gnf-rest nids w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))
(prim! GNF 'mark-edge-inv-sample '(Eq.trans (gnf-rest-mark-edge nids w x) R))
(prim! GNF 'unmark-edge-inv-sample '(Eq.trans (gnf-rest-unmark-edge nids w x) R))
(prim! GNF 'inv-remove-edge '(Eq.trans (gnf-rest-remove-edge nids w x) R))
(prim! GNF 'inv-fork-del '(gnf-rest-fork-del nids w x R))
(prim! GNF 'inv-filter-world '(gnf-rest-filter nids w K R))

(tree/restate! GNF 'p-gnf '[inv-remove-empty-at nat-fold-inv inv-cancel-losers inv-normalize])   ; the generic tree (spindel.v2.pres.tree) instead of a copy

(a/theorem gnf-rule-r-round [nids :- (List Nat), w :- World]
  (=> (= (gnf nids w) true) (= (filter-safe (normalize w)) true) (= (gnf nids (rule-r-round w)) true))
  (intros h hf) (simp only [rule-r-round]) (rw [rule-r-filter-eq])
  (exact (gnf-filter-world nids (normalize w) (keep-fn (normalize w)) (gnf-normalize nids w h) hf)))
(a/theorem gnf-rr-loop [nids :- (List Nat), fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (gnf nids w0) true) (= (rr-safe fuel w0) true) (= (gnf nids (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (gnf-rule-r-round nids w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (gnf-rule-r-round nids w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))
(a/theorem gnf-rule-r [nids :- (List Nat), w :- World] (=> (= (gnf nids w) true) (= (rule-r-safe w) true) (= (gnf nids (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (gnf-rr-loop nids (rr-fuel w) w h hs)))

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
  (=> (= (p3l w) true) (= (tbl-all (fork-out ids) (:forks (drain-world w ids))) true))
  (intro hp)
  (cases hm (tbl-any (fork-in ids) (:forks w)))
  (case [false]
    (have e (= (drain-world w ids) w))
    (simp only [drain-world]) (apply (internal-refused w (Item.drain ids) (rfl))) (simp only [raw0 t-drain hm refuse])
    (rw [e]) (exact (any-false-out ids (:forks w) hm)))
  (case [true]
    (have ha (= (:accepted (raw w (Item.drain ids))) true))
    (simp only [raw post raw0g host-shut host-item Bool.false_and Bool.and_false raw0 t-drain hm accept])
    (have er := (step-accepted w (Item.drain ids) ha))
    (have ew (= (:world (raw w (Item.drain ids)))
                (cancel-losers w (nat-fold remove-empty-at (nat-fold fork-del w ids) (owners-in ids (:forks w))))))
    (simp only [raw post raw0g host-shut host-item Bool.false_and Bool.and_false raw0 t-drain hm accept])
    (have hs := (step-rule-r-safe w (Item.drain ids) (p3l-p3b w hp)))
    (rw [ew] at hs)
    (have hi := (ga-sample w (And.left (p3b-parts w (p3l-p3b w hp)))))
    (have g0 (= (gnf ids (nat-fold fork-del w ids)) true))
    (exact (gnf-intro ids _ (nat-fold-inv fork-del inv-fork-del ids w hi) (fold-del-out ids w)))
    (have g1 := (nat-fold-gnf ids remove-empty-at (gnf-remove-empty-at ids) (owners-in ids (:forks w)) (nat-fold fork-del w ids) g0))
    (have g2 := (gnf-cancel-losers ids w _ g1))
    (have g3 := (gnf-rule-r ids _ g2 hs))
    (simp only [drain-world]) (rw [er ew]) (exact (gnf-rest-of ids _ g3))))
