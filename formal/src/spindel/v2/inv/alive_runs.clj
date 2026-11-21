(ns spindel.v2.inv.alive-runs
  "AR through `world-step` (I10's computation part, `inv-i10-comp`: every alive run of a computation is
  that computation's C.run), kernel-checked (Init only). The h-mem2 proof (spindel.v2.inv.members.fires) needs it at T6
  (a re-awaited site edge is held by no current activation).

  Bundle `alive-run-latest` = well-formed && for every alive run R: R.of < next-id and every computation row C with id
  R.of has C.run = R.id. `alive-run-latest` is a part of the generic step tree (spindel.v2.pres.tree; table in
  Part C). Primitives: a computation edit that keeps (id, run), a run edit that keeps the id and never
  revives a run nor changes an alive run's `of` (idle's `run-down`), deletions and filters, fresh rows
  (a fresh computation id is no alive run's `of`). Own proofs: new runs (a task's run: no computation
  has the task's id; T5/T11: C has no alive run, then C.run := the new run), T13's clear (the retired
  run is dead, so C has no alive run), demote (its cascade kills every alive run of C: idle's
  `demote-dead`), T11's predecessor cancel (idle's KDB: the predecessor is C's only alive run),
  normalization. Facts from the path: a parked run was alive; i7-idle at T5 and acts-parked at T11, from the step's
  input.
  Theorems: step-alive-run-latest, alive-run-latest-empty, alive-run-latest-i10-comp (alive-run-latest w -> inv-i10-comp w)."
  (:require [ansatz.core :as a]
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
            [spindel.v2.pres.tree :as tree]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.idle :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.i10 :refer :all]
            [spindel.v2.inv.i11 :refer :all]
            [spindel.v2.inv.i1-scopes :refer :all]
            [spindel.v2.inv.i8 :refer :all]
            [spindel.v2.inv.comp-facts :refer :all]))

;; ===========================================================================
;; Part A. The bundle
;; ===========================================================================

(a/defn alive-run-latest-c [r :- RunRow, c :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id c) (:of r))) (Nat.beq (:run c) (:id r))))
(a/defn alive-run-latest-one [n :- Nat, cs :- (List CompRow), r :- RunRow] Bool
  (Bool.or (Bool.not (run-alive r)) (Bool.and (Nat.blt (:of r) n) (tbl-all (alive-run-latest-c r) cs))))
(a/defn alive-run-latest-k [n :- Nat, cs :- (List CompRow), rs :- (List RunRow)] Bool (tbl-all (alive-run-latest-one n cs) rs))
(a/defn alive-run-latest-rest [w :- World] Bool (alive-run-latest-k (:next-id w) (:comps w) (:runs w)))
(a/defn alive-run-latest [w :- World] Bool (Bool.and (well-formed w) (alive-run-latest-rest w)))

(a/theorem alive-run-latest-well-formed [w :- World] (=> (= (alive-run-latest w) true) (= (well-formed w) true))
  (intro h) (simp only [alive-run-latest Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem alive-run-latest-rest-of [w :- World] (=> (= (alive-run-latest w) true) (= (alive-run-latest-rest w) true))
  (intro h) (simp only [alive-run-latest Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem alive-run-latest-intro [w :- World] (=> (= (well-formed w) true) (= (alive-run-latest-rest w) true) (= (alive-run-latest w) true))
  (intros h1 h2) (simp only [alive-run-latest h1 h2 Bool.and_self]))
(a/theorem alive-run-latest-parts [w :- World]
  (=> (= (alive-run-latest w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (alive-run-latest-well-formed w h))))

;; ---- the per-run fact, unfolded
(a/theorem alive-run-latest-one-use [n :- Nat, cs :- (List CompRow), r :- RunRow, c :- CompRow]
  (=> (= (alive-run-latest-one n cs r) true) (= (run-alive r) true) (List.Mem c cs) (= (:id c) (:of r)) (= (:run c) (:id r)))
  (intros h ha mc e)
  (simp only [alive-run-latest-one ha Bool.not_true Bool.false_or Bool.and_eq_true] at h)
  (have q := (tbl-all-mem CompRow (alive-run-latest-c r) c cs (And.right h) mc))
  (have i (= (Nat.beq (:id c) (:of r)) true)) (rw [e]) (exact (Nat.beq_refl _))
  (simp only [alive-run-latest-c i Bool.not_true Bool.false_or] at q)
  (exact (Nat.eq_of_beq_eq_true q)))
(a/theorem alive-run-latest-use [w :- World, r :- RunRow, c :- CompRow]
  (=> (= (alive-run-latest w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (List.Mem c (:comps w)) (= (:id c) (:of r)) (= (:run c) (:id r)))
  (intros h mr ha mc e)
  (have h1 := (alive-run-latest-rest-of w h)) (simp only [alive-run-latest-rest alive-run-latest-k] at h1)
  (exact (alive-run-latest-one-use _ _ r c (tbl-all-mem RunRow _ r (:runs w) h1 mr) ha mc e)))

;; ===========================================================================
;; Part B. Transfer lemmas and primitives
;; ===========================================================================

(a/structure ARK [] (id Nat) (run Nat))
(a/defn ark [c :- CompRow] ARK (ARK.mk (:id c) (:run c)))

(a/theorem alive-run-latest-c-key [r :- RunRow, c :- CompRow, c2 :- CompRow]
  (=> (= (ark c2) (ark c)) (= (alive-run-latest-c r c) true) (= (alive-run-latest-c r c2) true))
  (intros e h)
  (have e1 (= (:id c2) (:id c))) (exact (congrArg (fn [k :- ARK] (:id k)) e))
  (have e2 (= (:run c2) (:run c))) (exact (congrArg (fn [k :- ARK] (:run k)) e))
  (simp only [alive-run-latest-c e1 e2]) (simp only [alive-run-latest-c] at h) (exact h))
(a/theorem alive-run-latest-c-same [q :- RunRow, r :- RunRow, c :- CompRow]
  (=> (= (:id q) (:id r)) (= (:of q) (:of r)) (= (alive-run-latest-c r c) true) (= (alive-run-latest-c q c) true))
  (intros e1 e2 h) (simp only [alive-run-latest-c e1 e2]) (simp only [alive-run-latest-c] at h) (exact h))

;; computations: any change that keeps every run's comps fact
(a/theorem alive-run-latest-one-comps [n :- Nat, cs :- (List CompRow), cs2 :- (List CompRow), r :- RunRow]
  (=> (=> (= (tbl-all (alive-run-latest-c r) cs) true) (= (tbl-all (alive-run-latest-c r) cs2) true)) (= (alive-run-latest-one n cs r) true) (= (alive-run-latest-one n cs2 r) true))
  (intros hc h)
  (cases ha (run-alive r))
  (case [false] (simp only [alive-run-latest-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [alive-run-latest-one ha Bool.not_true Bool.false_or Bool.and_eq_true] at h)
    (simp only [alive-run-latest-one ha (And.left h) (hc (And.right h)) Bool.not_true Bool.false_or Bool.and_self])))
(a/theorem alive-run-latest-k-comps [n :- Nat, cs :- (List CompRow), cs2 :- (List CompRow), rs :- (List RunRow)]
  (=> (forall [r :- RunRow] (=> (= (tbl-all (alive-run-latest-c r) cs) true) (= (tbl-all (alive-run-latest-c r) cs2) true)))
      (= (alive-run-latest-k n cs rs) true) (= (alive-run-latest-k n cs2 rs) true))
  (intros hc h)
  (simp only [alive-run-latest-k] at h) (simp only [alive-run-latest-k])
  (have g (forall [r :- RunRow] (=> (= (alive-run-latest-one n cs r) true) (= (alive-run-latest-one n cs2 r) true))))
  (intros r hr) (exact (alive-run-latest-one-comps n cs cs2 r (hc r) hr))
  (exact (tbl-all-mono RunRow _ _ g rs h)))
(a/theorem alive-run-latest-k-next [n :- Nat, n2 :- Nat, cs :- (List CompRow), rs :- (List RunRow)]
  (=> (<= n n2) (= (alive-run-latest-k n cs rs) true) (= (alive-run-latest-k n2 cs rs) true))
  (intros hl h)
  (simp only [alive-run-latest-k] at h) (simp only [alive-run-latest-k])
  (have g (forall [r :- RunRow] (=> (= (alive-run-latest-one n cs r) true) (= (alive-run-latest-one n2 cs r) true))))
  (intros r hr)
  (cases ha (run-alive r))
  (case [false] (simp only [alive-run-latest-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [alive-run-latest-one ha Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
    (have z := (comp-facts-lt-of _ _ (And.left hr)))
    (have b (= (Nat.blt (:of r) n2) true)) (apply comp-facts-blt-of) (omega)
    (simp only [alive-run-latest-one ha b (And.right hr) Bool.not_true Bool.false_or Bool.and_self]))
  (exact (tbl-all-mono RunRow _ _ g rs h)))

(a/theorem alive-run-latest-cs-upd [x :- Nat, f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (ark (f c)) (ark c))), r :- RunRow, cs :- (List CompRow)]
  (=> (= (tbl-all (alive-run-latest-c r) cs) true) (= (tbl-all (alive-run-latest-c r) (tbl-upd comp-id x f cs)) true))
  (intro h)
  (have hin (forall [c :- CompRow] (=> (= (alive-run-latest-c r c) true) (= (Nat.beq (comp-id c) x) true) (= (alive-run-latest-c r (f c)) true))))
  (intros c hc hx) (exact (alive-run-latest-c-key r c (f c) (hk c) hc))
  (have hout (forall [c :- CompRow] (=> (= (alive-run-latest-c r c) true) (= (Nat.beq (comp-id c) x) false) (= (alive-run-latest-c r c) true))))
  (intros c hc hx) (exact hc)
  (exact (tbl-all-upd CompRow comp-id x f (alive-run-latest-c r) (alive-run-latest-c r) hin hout cs h)))
(a/theorem alive-run-latest-cs-del [x :- Nat, r :- RunRow, cs :- (List CompRow)]
  (=> (= (tbl-all (alive-run-latest-c r) cs) true) (= (tbl-all (alive-run-latest-c r) (tbl-del comp-id x cs)) true))
  (intro h)
  (have hout (forall [c :- CompRow] (=> (= (alive-run-latest-c r c) true) (= (Nat.beq (comp-id c) x) false) (= (alive-run-latest-c r c) true))))
  (intros c hc hx) (exact hc)
  (exact (tbl-all-del CompRow comp-id x (alive-run-latest-c r) (alive-run-latest-c r) hout cs h)))
(a/theorem alive-run-latest-cs-keep [K :- (=> Nat Bool), r :- RunRow, cs :- (List CompRow)]
  (=> (= (tbl-all (alive-run-latest-c r) cs) true) (= (tbl-all (alive-run-latest-c r) (tbl-keep K comp-id cs)) true))
  (intro h)
  (have hk (forall [c :- CompRow] (=> (= (alive-run-latest-c r c) true) (= (K (comp-id c)) true) (= (alive-run-latest-c r c) true))))
  (intros c hc hx) (exact hc)
  (exact (tbl-all-keep CompRow K comp-id (alive-run-latest-c r) (alive-run-latest-c r) hk cs h)))
(a/theorem alive-run-latest-cs-resync [es :- (List EdgeRow), r :- RunRow, cs :- (List CompRow)]
  (=> (= (tbl-all (alive-run-latest-c r) cs) true) (= (tbl-all (alive-run-latest-c r) (comps-resync es cs)) true))
  (induction cs)
  (case [nil] (intro h) (simp only [comps-resync tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (simp only [tbl-all Bool.and_eq_true] at h)
    (have a1 (= (alive-run-latest-c r (comp-resync es hd)) true)) (exact (alive-run-latest-c-key r hd (comp-resync es hd) (rfl) (And.left h)))
    (simp only [comps-resync tbl-all a1 (ih (And.right h)) Bool.and_self])))

;; runs: an edit by a row function that keeps the id and never revives (idle's run-down)
(a/theorem alive-run-latest-one-down [n :- Nat, cs :- (List CompRow), f :- (=> RunRow RunRow), r :- RunRow]
  (=> (= (run-down f r) true) (= (:id (f r)) (:id r)) (= (alive-run-latest-one n cs r) true) (= (alive-run-latest-one n cs (f r)) true))
  (intros hd hi h)
  (cases ha (run-alive (f r)))
  (case [false] (simp only [alive-run-latest-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [run-down ha Bool.not_true Bool.false_or Bool.and_eq_true] at hd)
    (have eo (= (:of (f r)) (:of r))) (exact (Nat.eq_of_beq_eq_true (And.right hd)))
    (simp only [alive-run-latest-one (And.left hd) Bool.not_true Bool.false_or Bool.and_eq_true] at h)
    (have g (forall [c :- CompRow] (=> (= (alive-run-latest-c r c) true) (= (alive-run-latest-c (f r) c) true))))
    (intros c hc) (exact (alive-run-latest-c-same (f r) r c hi eo hc))
    (have t (= (tbl-all (alive-run-latest-c (f r)) cs) true)) (exact (tbl-all-mono CompRow _ _ g cs (And.right h)))
    (have b (= (Nat.blt (:of (f r)) n) true)) (rw [eo]) (exact (And.left h))
    (simp only [alive-run-latest-one ha b t Bool.not_true Bool.false_or Bool.and_self])))
(a/theorem alive-run-latest-k-run-upd [n :- Nat, cs :- (List CompRow), x :- Nat, f :- (=> RunRow RunRow),
                         hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         hd :- (forall [r :- RunRow] (= (run-down f r) true)), rs :- (List RunRow)]
  (=> (= (alive-run-latest-k n cs rs) true) (= (alive-run-latest-k n cs (tbl-upd run-id x f rs)) true))
  (intro h)
  (simp only [alive-run-latest-k] at h) (simp only [alive-run-latest-k])
  (have hin (forall [r :- RunRow] (=> (= (alive-run-latest-one n cs r) true) (= (Nat.beq (run-id r) x) true) (= (alive-run-latest-one n cs (f r)) true))))
  (intros r hr hx) (exact (alive-run-latest-one-down n cs f r (hd r) (hid r) hr))
  (have hout (forall [r :- RunRow] (=> (= (alive-run-latest-one n cs r) true) (= (Nat.beq (run-id r) x) false) (= (alive-run-latest-one n cs r) true))))
  (intros r hr hx) (exact hr)
  (exact (tbl-all-upd RunRow run-id x f (alive-run-latest-one n cs) (alive-run-latest-one n cs) hin hout rs h)))

;; ---- full-bundle forms
(a/theorem alive-run-latest-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hk :- (forall [c :- CompRow] (= (ark (f c)) (ark c)))]
  (=> (= (alive-run-latest w) true) (= (alive-run-latest (comp-upd w x f)) true))
  (intro h)
  (have r0 := (alive-run-latest-rest-of w h)) (simp only [alive-run-latest-rest] at r0)
  (have g (forall [r :- RunRow] (=> (= (tbl-all (alive-run-latest-c r) (:comps w)) true) (= (tbl-all (alive-run-latest-c r) (tbl-upd comp-id x f (:comps w))) true))))
  (intros r hr) (exact (alive-run-latest-cs-upd x f hk r (:comps w) hr))
  (have r1 (= (alive-run-latest-rest (comp-upd w x f)) true))
  (simp only [alive-run-latest-rest comp-upd set-comps])
  (exact (alive-run-latest-k-comps _ _ _ _ g r0))
  (exact (alive-run-latest-intro _ (well-formed-comp-upd w x f hid hp (alive-run-latest-well-formed w h)) r1)))
(a/theorem alive-run-latest-run-upd-m [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                         hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         hd :- (forall [r :- RunRow] (= (run-down f r) true))]
  (=> (= (alive-run-latest w) true) (= (alive-run-latest (run-upd w x f)) true))
  (intro h)
  (have r0 := (alive-run-latest-rest-of w h)) (simp only [alive-run-latest-rest] at r0)
  (have r1 (= (alive-run-latest-rest (run-upd w x f)) true))
  (simp only [alive-run-latest-rest run-upd set-runs])
  (exact (alive-run-latest-k-run-upd _ _ x f hid hd _ r0))
  (exact (alive-run-latest-intro _ (well-formed-run-upd w x f hid (alive-run-latest-well-formed w h)) r1)))
;; a run edit that keeps (id, of, alive)
(a/structure ARR [] (id Nat) (of Nat) (alive Bool))
(a/defn arrk [r :- RunRow] ARR (ARR.mk (:id r) (:of r) (run-alive r)))
(a/theorem arrk-down [f :- (=> RunRow RunRow), hk :- (forall [r :- RunRow] (= (arrk (f r)) (arrk r))), r :- RunRow]
  (= (run-down f r) true)
  (have e1 (= (run-alive (f r)) (run-alive r))) (exact (congrArg (fn [k :- ARR] (:alive k)) (hk r)))
  (have e2 (= (:of (f r)) (:of r))) (exact (congrArg (fn [k :- ARR] (:of k)) (hk r)))
  (cases ha (run-alive r))
  (all_goals (simp only [run-down e1 e2 ha Nat.beq_refl Bool.not_true Bool.not_false Bool.true_or Bool.false_or Bool.and_self])))
(a/theorem run-wake-arrk [r :- RunRow] (= (arrk (run-wake r)) (arrk r))
  (simp only [arrk run-wake-alive]))
(a/theorem alive-run-latest-run-upd-a [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (arrk (f r)) (arrk r)))]
  (=> (= (alive-run-latest w) true) (= (alive-run-latest (run-upd w x f)) true))
  (exact (alive-run-latest-run-upd-m w x f hid (arrk-down f hk))))

;; ---- rest lemmas of the table primitives
(a/theorem arr-grow [w :- World, w2 :- World]
  (=> (= (:comps w2) (:comps w)) (= (:runs w2) (:runs w)) (<= (:next-id w) (:next-id w2)) (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest w2) true))
  (intros e1 e2 hl h)
  (simp only [alive-run-latest-rest e1 e2]) (simp only [alive-run-latest-rest] at h)
  (exact (alive-run-latest-k-next _ _ _ _ hl h)))
(a/theorem arr-comps [w :- World, w2 :- World]
  (=> (forall [r :- RunRow] (=> (= (tbl-all (alive-run-latest-c r) (:comps w)) true) (= (tbl-all (alive-run-latest-c r) (:comps w2)) true)))
      (= (:runs w2) (:runs w)) (= (:next-id w2) (:next-id w)) (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest w2) true))
  (intros g e2 e3 h)
  (simp only [alive-run-latest-rest e2 e3]) (simp only [alive-run-latest-rest] at h)
  (exact (alive-run-latest-k-comps _ _ _ _ g h)))
(a/theorem arr-comp-key [w :- World, x :- Nat, f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (ark (f c)) (ark c))), w2 :- World]
  (=> (= (:comps w2) (tbl-upd comp-id x f (:comps w))) (= (:runs w2) (:runs w)) (= (:next-id w2) (:next-id w))
      (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest w2) true))
  (intros e1 e2 e3 h)
  (have g (forall [r :- RunRow] (=> (= (tbl-all (alive-run-latest-c r) (:comps w)) true) (= (tbl-all (alive-run-latest-c r) (:comps w2)) true))))
  (intros r hr) (rw [e1]) (exact (alive-run-latest-cs-upd x f hk r (:comps w) hr))
  (exact (arr-comps w w2 g e2 e3 h)))

(a/theorem ark-inc-pending [c :- CompRow] (= (ark (comp-inc-pending c)) (ark c)) (rfl))
(a/theorem ark-dec-pending [c :- CompRow] (= (ark (comp-dec-pending c)) (ark c)) (rfl))
(a/theorem ark-set-pending [k :- Nat, c :- CompRow] (= (ark (comp-set-pending k c)) (ark c)) (rfl))

(a/theorem arr-mark-edge [w :- World, x :- Nat] (=> (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false]
      (simp only [mark-edge hf hm])
      (exact (arr-comp-key w (:creditor e) comp-inc-pending ark-inc-pending (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending) (rfl) (rfl) (rfl) h)))))
(a/theorem arr-unmark-edge [w :- World, x :- Nat] (=> (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true]
      (simp only [unmark-edge hf hm])
      (exact (arr-comp-key w (:creditor e) comp-dec-pending ark-dec-pending (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending) (rfl) (rfl) (rfl) h)))))
(a/theorem arr-remove-edge [w :- World, x :- Nat] (=> (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact (arr-grow w (edge-del w x) (rfl) (rfl) (Nat.le_refl _) h)))
    (case [true]
      (simp only [remove-edge hf hm])
      (exact (arr-comp-key w (:creditor e) comp-dec-pending ark-dec-pending (comp-upd (edge-del w x) (:creditor e) comp-dec-pending) (rfl) (rfl) (rfl) h)))))
(a/theorem arr-drop-cred [w :- World, a :- Nat] (=> (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest (drop-cred-edges w a)) true))
  (intro h)
  (simp only [drop-cred-edges])
  (exact (arr-comp-key w a (comp-set-pending 0) (ark-set-pending 0) (comp-upd (set-edges w (tbl-filter (cred-ne a) (:edges w))) a (comp-set-pending 0)) (rfl) (rfl) (rfl) h)))
(a/theorem arr-drop-act [w :- World, a :- Nat] (=> (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest (drop-act w a)) true))
  (intro h)
  (simp only [drop-act])
  (exact (arr-grow (drop-cred-edges w a) (act-del (drop-cred-edges w a) a) (rfl) (rfl) (Nat.le_refl _) (arr-drop-cred w a h))))
(a/theorem arr-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (=> (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest (drop-edges w p)) true))
  (intro h)
  (have g (forall [r :- RunRow] (=> (= (tbl-all (alive-run-latest-c r) (:comps w)) true)
                                    (= (tbl-all (alive-run-latest-c r) (:comps (drop-edges w p))) true))))
  (intros r hr) (simp only [drop-edges set-comps set-edges]) (exact (alive-run-latest-cs-resync _ r (:comps w) hr))
  (exact (arr-comps w (drop-edges w p) g (rfl) (rfl) h)))
(a/theorem arr-insert-edge-fresh [w :- World, e :- EdgeRow] (=> (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest (insert-edge-fresh w e)) true))
  (intro h)
  (simp only [insert-edge-fresh])
  (exact (arr-grow w (bump (insert-edge w (edge-set-id (:next-id w) e))) (rfl) (rfl) (Nat.le_succ _) h)))
(a/theorem arr-insert-edge-checked [w :- World, e :- EdgeRow] (=> (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest (insert-edge-checked w e)) true))
  (intro h)
  (cases hk (edge-ok-in w e))
  (simp only [insert-edge-checked hk]) (exact h)
  (simp only [insert-edge-checked hk]) (exact (arr-insert-edge-fresh w e h)))
(a/theorem arr-comp-del [w :- World, x :- Nat] (=> (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest (comp-del w x)) true))
  (intro h)
  (have g (forall [r :- RunRow] (=> (= (tbl-all (alive-run-latest-c r) (:comps w)) true) (= (tbl-all (alive-run-latest-c r) (:comps (comp-del w x))) true))))
  (intros r hr) (simp only [comp-del set-comps]) (exact (alive-run-latest-cs-del x r (:comps w) hr))
  (exact (arr-comps w (comp-del w x) g (rfl) (rfl) h)))
(a/theorem arr-run-del [w :- World, x :- Nat] (=> (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest (run-del w x)) true))
  (intro h)
  (simp only [alive-run-latest-rest alive-run-latest-k run-del set-runs]) (simp only [alive-run-latest-rest alive-run-latest-k] at h)
  (have hout (forall [r :- RunRow] (=> (= (alive-run-latest-one (:next-id w) (:comps w) r) true) (= (Nat.beq (run-id r) x) false) (= (alive-run-latest-one (:next-id w) (:comps w) r) true))))
  (intros r hr hx) (exact hr)
  (exact (tbl-all-del RunRow run-id x _ _ hout (:runs w) h)))
(a/theorem arr-filter-world [w :- World, K :- (=> Nat Bool)] (=> (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest (filter-world K w)) true))
  (intro h)
  (simp only [alive-run-latest-rest alive-run-latest-k] at h)
  (have g (forall [r :- RunRow] (=> (= (alive-run-latest-one (:next-id w) (:comps w) r) true) (= (K (run-id r)) true)
                                    (= (alive-run-latest-one (:next-id w) (tbl-keep K comp-id (:comps w)) r) true))))
  (intros r hr hk)
  (have g2 (=> (= (tbl-all (alive-run-latest-c r) (:comps w)) true) (= (tbl-all (alive-run-latest-c r) (tbl-keep K comp-id (:comps w))) true)))
  (intro q) (exact (alive-run-latest-cs-keep K r (:comps w) q))
  (exact (alive-run-latest-one-comps _ _ _ r g2 hr))
  (simp only [alive-run-latest-rest alive-run-latest-k filter-world])
  (exact (tbl-all-keep RunRow K run-id _ _ g (:runs w) h)))
;; a fresh computation: its id is no alive run's `of`
(a/theorem arr-comp-ins [w :- World, c :- CompRow] (=> (= (comp-id c) (:next-id w)) (= (alive-run-latest-rest w) true) (= (alive-run-latest-rest (bump (comp-ins w c))) true))
  (intros hc h)
  (simp only [alive-run-latest-rest alive-run-latest-k] at h)
  (have g (forall [r :- RunRow] (=> (= (alive-run-latest-one (:next-id w) (:comps w) r) true)
                                    (= (alive-run-latest-one (+ (:next-id w) 1) (tbl-ins c (:comps w)) r) true))))
  (intros r hr)
  (cases ha (run-alive r))
  (case [false] (simp only [alive-run-latest-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [alive-run-latest-one ha Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
    (have z := (comp-facts-lt-of _ _ (And.left hr)))
    (have b (= (Nat.blt (:of r) (+ (:next-id w) 1)) true)) (apply comp-facts-blt-of) (omega)
    (have ne (= (Nat.beq (:id c) (:of r)) false))
    (have e (= (:id c) (:next-id w))) (exact hc)
    (cases hb (Nat.beq (:id c) (:of r))) (rfl) (have e2 := (Nat.eq_of_beq_eq_true hb)) (omega)
    (simp only [alive-run-latest-one ha b tbl-ins tbl-all alive-run-latest-c ne (And.right hr) Bool.not_true Bool.not_false Bool.false_or Bool.true_or Bool.and_self]))
  (simp only [alive-run-latest-rest alive-run-latest-k bump set-next-id comp-ins set-comps])
  (exact (tbl-all-mono RunRow _ _ g (:runs w) h)))
(a/theorem alive-run-latest-comp-ins-fresh [w :- World, r :- CompRow]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (alive-run-latest w) true) (= (alive-run-latest (bump (comp-ins w r))) true))
  (intros h1 h2 h)
  (exact (alive-run-latest-intro _ (well-formed-comp-ins-fresh w r h1 h2 (alive-run-latest-well-formed w h)) (arr-comp-ins w r h1 (alive-run-latest-rest-of w h)))))

;; ===========================================================================
;; Part C. alive-run-latest on the generic tree (spindel.v2.pres.tree): the bundle, its cells, its table
;; ===========================================================================

(def AR (mk-bundle 'alive-run-latest [] "alive-run-latest-" {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (arrk r))) 4]
                                 'well-formed-comp-upd ['(fn [c :- CompRow] (Eq.refl (ark c))) 5]}))
(swap! (:renames AR) assoc 'well-formed-parts 'alive-run-latest-parts 'well-formed-run-upd 'alive-run-latest-run-upd-a 'well-formed-comp-upd 'alive-run-latest-comp-upd
       'well-formed-comp-ins-fresh 'alive-run-latest-comp-ins-fresh)
(defpart AR :reads '[comps next-id runs])
(doseq [[o t] '[[well-formed-source-ins-fresh source-ins] [well-formed-fork-ins-fresh fork-ins] [well-formed-resource-ins-fresh resource-ins] [well-formed-scope-ins-fresh scope-ins]
                [well-formed-act-ins-fresh act-ins] [well-formed-task-ins-fresh task-ins]]]
  (prim! AR o (list 'arr-grow 'w (list 'bump (list t 'w 'r)) '(rfl) '(rfl) '(Nat.le_succ (:next-id w)) 'R)))
(prim! AR 'well-formed-bump '(arr-grow w (bump w) (rfl) (rfl) (Nat.le_succ (:next-id w)) R))
(prim! AR 'well-formed-remove-edge '(arr-remove-edge w x R))
(prim! AR 'well-formed-mark-edge '(arr-mark-edge w x R))
(prim! AR 'well-formed-unmark-edge '(arr-unmark-edge w x R))
(prim! AR 'well-formed-drop-cred-edges '(arr-drop-cred w a R))
(prim! AR 'well-formed-drop-act '(arr-drop-act w a R))
(prim! AR 'well-formed-drop-edges '(arr-drop-edges w p R))
(prim! AR 'well-formed-insert-edge-fresh '(arr-insert-edge-fresh w e R))
(prim! AR 'well-formed-insert-edge-checked '(arr-insert-edge-checked w e R))
(prim! AR 'well-formed-comp-del-unref '(arr-comp-del w x R))
(prim! AR 'well-formed-run-del '(arr-run-del w x R))
(prim! AR 'well-formed-filter-world '(arr-filter-world w K R))

;; a run edit by a row function that ends a run goes through alive-run-latest-run-upd-m (idle's down lemmas)
(def ^:private ar-run-fns '{run-cancel-row run-cancel-row-dwn run-complete-row run-complete-row-dwn
                            run-fin-pop-end run-fin-pop-end-dwn run-drop-fins run-drop-fins-dwn})

(tree/part! AR
  ;; ---- the part's own proofs (content)
  :over '{well-formed-clear-comp-run alive-run-latest-clear-comp-run   ; T13's clear: the retired run is dead, so C has no alive run
          well-formed-add-run-scope  alive-run-latest-add-run-scope    ; a new run of a task: no computation has the task's id
          well-formed-spawn-rows     alive-run-latest-spawn-rows       ; T4: the new task's id is fresh
          well-formed-start-raw      alive-run-latest-start-raw        ; T5: a startable computation has no alive run (i7-idle)
          well-formed-dispatch-raw   alive-run-latest-dispatch-raw     ; T11: the predecessor's cancel kills C's only alive run (alive-runs-listed)
          well-formed-demote-finish  alive-run-latest-demote-finish    ; demote: C.run := 0 once no run of C is alive
          well-formed-demote         alive-run-latest-demote           ;   which its cascade ensures (idle's demote-dead)
          well-formed-normalize-round     alive-run-latest-normalize-round       ; normalization with acts-alive (demote's cascade)
          well-formed-normalize-loop      alive-run-latest-normalize-loop
          well-formed-normalize      alive-run-latest-normalize}
  ;; ---- sites: the run edits that change (id, of, alive)
  :sites (merge
          (tree/row-sites 'well-formed-run-upd (set (keys ar-run-fns))                                  ; a run ends
                          (fn [F] (list 'alive-run-latest-run-upd-m 'w 'x F 'hf (ar-run-fns F) 'h0)))
          '{[well-formed-run-upd run-wake]      (alive-run-latest-run-upd-a w x run-wake hf run-wake-arrk h0)          ; resume: key kept, by lemma
            [well-formed-run-upd run-park-row]  (alive-run-latest-run-upd-on w x run-park-row hf (fn [q :- RunRow] (Eq.refl (:of q))) h0 h1)    ; await: made
            [well-formed-run-upd run-tick-park] (alive-run-latest-run-upd-on w x run-tick-park hf (fn [q :- RunRow] (Eq.refl (:of q))) h0 h1)}) ; parked; take
  ;; ---- facts from the path: what ar's own proofs and sites take ...
  :ctx '{[well-formed-run-upd run-park-row]  [(= (tbl-all (run-ok-for x) (:runs w)) true)]              ; every row of the run is alive
         [well-formed-run-upd run-tick-park] [(= (tbl-all (run-ok-for x) (:runs w)) true)]
         well-formed-clear-comp-run [(List.Mem r (:runs w)) (= (run-alive r) false)]                    ; t13-retire-with-subtree and retire-run forward it: inferred
         well-formed-add-run-scope  [(= (tbl-has comp-id of (:comps w)) false) (< of (:next-id w))]
         well-formed-start-raw      [(= (i7-idle w) true) (List.Mem c (:comps w)) (= (startable w c) true)]
         well-formed-dispatch-raw   [(= (acts-alive w) true) (List.Mem c (:comps w))]
         well-formed-demote-finish  [(= (tbl-all (not-alive-of cid) (:runs w)) true)]
         well-formed-demote         [(= (acts-alive w) true)]
         well-formed-normalize-round     [(= (acts-alive w) true)]
         well-formed-normalize-loop      [(= (acts-alive w) true)]
         well-formed-normalize      [(= (acts-alive w) true)]}
  ;; ---- ... and the facts nodes take from above them and pass on
  :own '{;; i7-idle (T5: a startable computation has no alive run) and acts-parked (T11's cascade), from the step's input;
         ;; transition passes each to its transition's branch (inferred)
         well-formed-raw        [hg7 (= (i7-idle w) true) hga (= (acts-parked w) true)]
         well-formed-host-guarded-transition      [hg7 (= (i7-idle w) true) hga (= (acts-parked w) true)]
         well-formed-transition       [hg7 (= (i7-idle w) true) hga (= (acts-parked w) true)]
         well-formed-t5-start         [hg7 (= (i7-idle w) true)]
         well-formed-t11-dispatch        [hga (= (acts-parked w) true)]
         well-formed-take-park  [hm (List.Mem r (:runs w)) hal (= (run-alive r) true)]                 ; the parked run was alive
         well-formed-arm-park   [hm (List.Mem r (:runs w)) hal (= (run-alive r) true)]
         well-formed-await-raw  [hm (List.Mem r (:runs w)) hal (= (run-alive r) true)]
         well-formed-await-post [hk (= (awaiting-run-alive rid (:world acc)) true)]}                                 ;   carried by i8's awaiting-run-alive
  :pass '{well-formed-t5-start         {well-formed-start-raw [hg7 (tbl-find-mem CompRow comp-id cid c (:comps w) hc) (bool-and-right _ _ hg)]}
          well-formed-t11-dispatch        {well-formed-dispatch-raw [(acts-parked-acts-alive w hga) (tbl-find-mem CompRow comp-id cid c (:comps w) hc)]}
          well-formed-job-apply  {well-formed-retire-run [(And.left (find-run-mem w rid r hf)) (retirable-dead r ha)]}   ; a retirable run is dead
          well-formed-take-park  {[well-formed-run-upd run-tick-park] [(take-park-ok w r x k (run-ok-of-mem w r (base-of w h) hm hal))]}
          well-formed-arm-park   {well-formed-take-park [(arm-raw-mem w r kind hm) hal]}
          well-formed-t-take     {well-formed-take-park [(And.left (tok-facts w st r ht)) (normal-alive r (bool-and-left _ _ (bool-and-right _ _ hg)))]}
          well-formed-t17-arm        {well-formed-arm-park [(And.left (tok-facts w st r ht)) (normal-alive r (bool-and-left _ _ (bool-and-right _ _ hg)))]}
          well-formed-t6-await         {well-formed-await-raw [(And.left (tok-facts w st r ht)) (normal-alive r (await-ok-normal w r ds mode fresh _ hg))]}
          well-formed-await-raw  {well-formed-await-post [(awaiting-run-alive-await-wire (:id r) r (:next-id w) mode k (nat-distinct ds)
                                            (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true)
                                            (awaiting-run-alive-await-pre (:id r) w r ds mode k mine
                                              (awaiting-run-alive-intro (:id r) w (base-of w h) (run-ok-of-mem w r (base-of w h) hm hal))))]}
          well-formed-await-post {well-formed-park-if [(awaiting-run-alive-rest-of rid _ (awaiting-run-alive-nat-fold rid (fast-fill (:pairs acc)) (awaiting-run-alive-fast-fill rid (:pairs acc)) (nat-distinct ds) _
                                         (awaiting-run-alive-act-upd rid (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))
                                           (act-set-members-id (mk-members (:pairs acc) 0 ds)) hk)))]}})

;; ===========================================================================
;; Part D. ar's own proofs (the table's :over)
;; ===========================================================================

;; ---- T13's clear: the retired run is dead, so its computation has no alive run (AR + unique ids)
(a/theorem alive-run-latest-dead-id [w :- World, r :- RunRow, q :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (= (run-alive r) false) (List.Mem q (:runs w)) (= (:id q) (:id r))
      (= (run-alive q) false))
  (intros hs mr hd mq e)
  (have nd (= (Bool.not (run-alive r)) true)) (simp only [hd Bool.not_false])
  (have D := (uniq-all RunRow run-id (fn [x :- RunRow] (Bool.not (run-alive x))) r (:runs w) (lit-runs-nodup w hs) mr nd))
  (have dq := (tbl-all-mem RunRow _ q (:runs w) D mq))
  (have i (= (Nat.beq (run-id q) (run-id r)) true)) (simp only [run-id]) (rw [e]) (exact (Nat.beq_refl _))
  (simp only [same-id-then i Bool.not_true Bool.false_or] at dq)
  (exact (bnot-true _ dq)))
;; no alive run has `of` = cid
(a/theorem alive-run-latest-k-clear [n :- Nat, cid :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                       cs :- (List CompRow), rs :- (List RunRow)]
  (=> (= (tbl-all (not-alive-of cid) rs) true) (= (alive-run-latest-k n cs rs) true) (= (alive-run-latest-k n (tbl-upd comp-id cid f cs) rs) true))
  (intros hn h)
  (simp only [alive-run-latest-k] at h) (simp only [alive-run-latest-k])
  (have g (forall [q :- RunRow] (=> (= (alive-run-latest-one n cs q) true) (= (not-alive-of cid q) true) (= (alive-run-latest-one n (tbl-upd comp-id cid f cs) q) true))))
  (intros q hq hnq)
  (cases ha (run-alive q))
  (case [false] (simp only [alive-run-latest-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [not-alive-of ha Bool.not_true Bool.false_or] at hnq)
    (have ho := (bnot-true _ hnq))
    (simp only [alive-run-latest-one ha Bool.not_true Bool.false_or Bool.and_eq_true] at hq)
    (have hin (forall [c :- CompRow] (=> (= (alive-run-latest-c q c) true) (= (Nat.beq (comp-id c) cid) true) (= (alive-run-latest-c q (f c)) true))))
    (intros c hc hx)
    (have e1 (= (:id (f c)) cid)) (exact (Eq.trans (hid c) (Nat.eq_of_beq_eq_true hx)))
    (have e2 (= (Nat.beq (:id (f c)) (:of q)) false)) (rw [e1]) (exact (Eq.trans (beq-comm cid (:of q)) ho))
    (simp only [alive-run-latest-c e2 Bool.not_false Bool.true_or])
    (have hout (forall [c :- CompRow] (=> (= (alive-run-latest-c q c) true) (= (Nat.beq (comp-id c) cid) false) (= (alive-run-latest-c q c) true))))
    (intros c hc hx) (exact hc)
    (have t (= (tbl-all (alive-run-latest-c q) (tbl-upd comp-id cid f cs)) true)) (exact (tbl-all-upd CompRow comp-id cid f (alive-run-latest-c q) (alive-run-latest-c q) hin hout cs (And.right hq)))
    (simp only [alive-run-latest-one ha (And.left hq) t Bool.not_true Bool.false_or Bool.and_self]))
  (exact (tbl-all-mono2 RunRow _ _ _ g rs h hn)))
;; C.run = R.id with R dead: no alive run of C
(a/theorem alive-run-latest-none-of-dead [w :- World, r :- RunRow, c :- CompRow]
  (=> (= (alive-run-latest w) true) (List.Mem r (:runs w)) (= (run-alive r) false) (List.Mem c (:comps w)) (= (:run c) (:id r))
      (= (tbl-all (not-alive-of (:id c)) (:runs w)) true))
  (intros h mr hd mc ec)
  (have hs := (alive-run-latest-well-formed w h))
  (apply (all-of-mem RunRow (not-alive-of (:id c)) (:runs w)))
  (intros q mq)
  (cases ha (run-alive q))
  (case [false] (simp only [not-alive-of ha Bool.not_false Bool.true_or]))
  (case [true]
    (cases ho (Nat.beq (:of q) (:id c)))
    (case [false] (simp only [not-alive-of ho Bool.not_false Bool.or_true]))
    (case [true]
      (have e1 := (alive-run-latest-use w q c h mq ha mc (Eq.symm (Nat.eq_of_beq_eq_true ho))))
      (have d := (alive-run-latest-dead-id w r q hs mr hd mq (Eq.trans (Eq.symm e1) ec)))
      (rw [ha] at d) (cases d))))

(tree/restate! AR '[well-formed-clear-task-run])
(a/theorem alive-run-latest-clear-comp-run [w :- World, r :- RunRow]
  (=> (List.Mem r (:runs w)) (= (run-alive r) false) (= (alive-run-latest w) true) (= (alive-run-latest (clear-comp-run w r)) true))
  (intros mr hd h)
  (have hs := (alive-run-latest-well-formed w h))
  (cases hc (comp-find w (:of r))) (case' [some c]) (case' [none])
  (simp only [clear-comp-run hc]) (exact (alive-run-latest-clear-task-run w r h))
  (cases hr (Nat.beq (:run c) (:id r)))
  (simp only [clear-comp-run hc hr]) (exact h)
  (simp only [clear-comp-run hc hr])
  (have mc := (tbl-find-mem CompRow comp-id (:of r) c (:comps w) hc))
  (have ic (= (:id c) (:of r))) (exact (tbl-find-id CompRow comp-id (:of r) c (:comps w) hc))
  (have hn := (alive-run-latest-none-of-dead w r c h mr hd mc (Nat.eq_of_beq_eq_true hr)))
  (rw [ic] at hn)
  (have r0 := (alive-run-latest-rest-of w h)) (simp only [alive-run-latest-rest] at r0)
  (have r1 (= (alive-run-latest-rest (comp-upd w (:of r) comp-clear-run)) true))
  (simp only [alive-run-latest-rest comp-upd set-comps])
  (exact (alive-run-latest-k-clear _ (:of r) comp-clear-run comp-clear-run-id _ _ hn r0))
  (exact (alive-run-latest-intro _ (well-formed-comp-upd w (:of r) comp-clear-run comp-clear-run-id comp-clear-run-pending hs) r1)))

;; ---- parks: the parked run was alive (the cell of the table's two park sites)
(a/theorem alive-run-latest-k-run-on [n :- Nat, cs :- (List CompRow), x :- Nat, f :- (=> RunRow RunRow),
                        hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hof :- (forall [r :- RunRow] (= (:of (f r)) (:of r))), rs :- (List RunRow)]
  (=> (= (tbl-all (run-ok-for x) rs) true) (= (alive-run-latest-k n cs rs) true) (= (alive-run-latest-k n cs (tbl-upd run-id x f rs)) true))
  (intros ho h)
  (simp only [alive-run-latest-k] at h) (simp only [alive-run-latest-k])
  (have b := (tbl-all-mono2 RunRow (alive-run-latest-one n cs) (run-ok-for x) (both (alive-run-latest-one n cs) (run-ok-for x))
               (fn [q :- RunRow, h1 :- (= (alive-run-latest-one n cs q) true), h2 :- (= (run-ok-for x q) true)] (both-of RunRow (alive-run-latest-one n cs) (run-ok-for x) q h1 h2))
               rs h ho))
  (have hin (forall [r :- RunRow] (=> (= (both (alive-run-latest-one n cs) (run-ok-for x) r) true) (= (Nat.beq (run-id r) x) true) (= (alive-run-latest-one n cs (f r)) true))))
  (intros r hb hx)
  (have hr := (both-left RunRow (alive-run-latest-one n cs) (run-ok-for x) r hb))
  (have hk := (both-right RunRow (alive-run-latest-one n cs) (run-ok-for x) r hb))
  (have hx2 (= (Nat.beq (:id r) x) true)) (exact hx)
  (simp only [run-ok-for hx2 Bool.not_true Bool.false_or] at hk)
  (simp only [alive-run-latest-one hk Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
  (have g (forall [c :- CompRow] (=> (= (alive-run-latest-c r c) true) (= (alive-run-latest-c (f r) c) true))))
  (intros c hc) (exact (alive-run-latest-c-same (f r) r c (hid r) (hof r) hc))
  (have t (= (tbl-all (alive-run-latest-c (f r)) cs) true)) (exact (tbl-all-mono CompRow _ _ g cs (And.right hr)))
  (have b2 (= (Nat.blt (:of (f r)) n) true)) (rw [(hof r)]) (exact (And.left hr))
  (simp only [alive-run-latest-one b2 t Bool.and_self Bool.or_true])
  (have hout (forall [r :- RunRow] (=> (= (both (alive-run-latest-one n cs) (run-ok-for x) r) true) (= (Nat.beq (run-id r) x) false) (= (alive-run-latest-one n cs r) true))))
  (intros r hb hx) (exact (both-left RunRow (alive-run-latest-one n cs) (run-ok-for x) r hb))
  (exact (tbl-all-upd RunRow run-id x f _ (alive-run-latest-one n cs) hin hout rs b)))
(a/theorem alive-run-latest-run-upd-on [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                          hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                          hof :- (forall [r :- RunRow] (= (:of (f r)) (:of r)))]
  (=> (= (tbl-all (run-ok-for x) (:runs w)) true) (= (alive-run-latest w) true) (= (alive-run-latest (run-upd w x f)) true))
  (intros ho h)
  (have r0 := (alive-run-latest-rest-of w h)) (simp only [alive-run-latest-rest] at r0)
  (have r1 (= (alive-run-latest-rest (run-upd w x f)) true))
  (simp only [alive-run-latest-rest run-upd set-runs])
  (exact (alive-run-latest-k-run-on _ _ x f hid hof _ ho r0))
  (exact (alive-run-latest-intro _ (well-formed-run-upd w x f hid (alive-run-latest-well-formed w h)) r1)))


;; ---- new runs of a task: no computation has the task's id
(a/theorem alive-run-latest-k-newrun-free [n :- Nat, n2 :- Nat, cs :- (List CompRow), rs :- (List RunRow), q :- RunRow]
  (=> (= (tbl-has comp-id (:of q) cs) false) (< (:of q) n2) (<= n n2) (= (alive-run-latest-k n cs rs) true) (= (alive-run-latest-k n2 cs (List.cons RunRow q rs)) true))
  (intros hc hl hle h)
  (have h2 := (alive-run-latest-k-next n n2 cs rs hle h))
  (simp only [alive-run-latest-k] at h2)
  (have ne := (has-false-ne CompRow comp-id (:of q) cs hc))
  (have g (forall [c :- CompRow] (=> (= (Bool.not (Nat.beq (comp-id c) (:of q))) true) (= (alive-run-latest-c q c) true))))
  (intros c hcc) (simp only [comp-id] at hcc) (simp only [alive-run-latest-c hcc Bool.true_or])
  (have t (= (tbl-all (alive-run-latest-c q) cs) true)) (exact (tbl-all-mono CompRow _ _ g cs ne))
  (have b (= (Nat.blt (:of q) n2) true)) (exact (comp-facts-blt-of _ _ hl))
  (have o (= (alive-run-latest-one n2 cs q) true)) (simp only [alive-run-latest-one b t Bool.and_self Bool.or_true])
  (simp only [alive-run-latest-k tbl-all o h2 Bool.and_self]))
(a/theorem alive-run-latest-add-run-scope [w :- World, of :- Nat, ep :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (tbl-has comp-id of (:comps w)) false) (< of (:next-id w)) (= (alive-run-latest w) true) (= (alive-run-latest (add-run-scope w of ep parent ei)) true))
  (intros hc hl h)
  (have r0 := (alive-run-latest-rest-of w h)) (simp only [alive-run-latest-rest] at r0)
  (have l2 (< of (+ (+ (:next-id w) 1) 1))) (omega)
  (have l3 (<= (:next-id w) (+ (+ (:next-id w) 1) 1))) (omega)
  (have rr (= (alive-run-latest-rest (add-run-scope w of ep parent ei)) true))
  (show (= (alive-run-latest-k (+ (+ (:next-id w) 1) 1) (:comps w) (List.cons RunRow (new-run-row (:next-id w) of ep (+ (:next-id w) 1) ei) (:runs w))) true))
  (exact (alive-run-latest-k-newrun-free _ _ _ _ (new-run-row (:next-id w) of ep (+ (:next-id w) 1) ei) hc l2 l3 r0))
  (exact (alive-run-latest-intro _ (well-formed-add-run-scope w of ep parent ei (alive-run-latest-well-formed w h)) rr)))
(a/theorem alive-run-latest-has-next [w :- World] (=> (= (well-formed w) true) (= (tbl-has comp-id (:next-id w) (:comps w)) false))
  (intro hs)
  (cases hb (tbl-has comp-id (:next-id w) (:comps w)))
  (case [false] (rfl))
  (case [true] (have z := (comp-below w (:next-id w) hs hb)) (omega)))
(a/theorem alive-run-latest-spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat), loc :- Bool]
  (=> (= (alive-run-latest w) true) (= (alive-run-latest (spawn-rows w owner inputs loc)) true))
  (intro h)
  (have hc := (alive-run-latest-has-next w (alive-run-latest-well-formed w h)))
  (have hl (< (:next-id w) (:next-id (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc)))))) (show (< (:next-id w) (+ (:next-id w) 1))) (omega)
  (simp only [spawn-rows])
  (exact (alive-run-latest-add-run-scope (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc)))
           (:next-id w) 0 (task-scope-parent w owner) 0 hc hl
           (alive-run-latest-task-ins-fresh w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc) (rfl) h))))

;; ---- T5/T11: C has no alive run; the new run becomes C.run
(a/theorem alive-run-latest-cs-own [cid :- Nat, rid :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                      hrun :- (forall [c :- CompRow] (= (:run (f c)) rid)), q :- RunRow, cs :- (List CompRow)]
  (=> (= (:id q) rid) (= (:of q) cid) (= (tbl-all (alive-run-latest-c q) (tbl-upd comp-id cid f cs)) true))
  (induction cs)
  (case [nil] (intros e1 e2) (simp only [tbl-upd tbl-all]))
  (case [cons hd t ih]
    (intros e1 e2)
    (cases hx (Nat.beq (comp-id hd) cid))
    (case [true]
      (have a1 (= (alive-run-latest-c q (f hd)) true)) (simp only [alive-run-latest-c (hrun hd) e1 Nat.beq_refl Bool.or_true])
      (simp only [tbl-upd hx tbl-all a1 (ih e1 e2) Bool.and_self]))
    (case [false]
      (have hx2 (= (Nat.beq (:id hd) (:of q)) false)) (rw [e2]) (exact hx)
      (have a1 (= (alive-run-latest-c q hd) true)) (simp only [alive-run-latest-c hx2 Bool.not_false Bool.true_or])
      (simp only [tbl-upd hx tbl-all a1 (ih e1 e2) Bool.and_self]))))
(a/theorem alive-run-latest-k-newrun-own [n :- Nat, n2 :- Nat, cid :- Nat, rid :- Nat, f :- (=> CompRow CompRow),
                            hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                            hrun :- (forall [c :- CompRow] (= (:run (f c)) rid)),
                            cs :- (List CompRow), rs :- (List RunRow), q :- RunRow]
  (=> (= (:id q) rid) (= (:of q) cid) (< cid n2) (<= n n2) (= (tbl-all (not-alive-of cid) rs) true) (= (alive-run-latest-k n cs rs) true)
      (= (alive-run-latest-k n2 (tbl-upd comp-id cid f cs) (List.cons RunRow q rs)) true))
  (intros e1 e2 hl hle hn h)
  (have h1 := (alive-run-latest-k-next n n2 _ rs hle (alive-run-latest-k-clear n cid f hid cs rs hn h)))
  (simp only [alive-run-latest-k] at h1)
  (have t := (alive-run-latest-cs-own cid rid f hid hrun q cs e1 e2))
  (have b (= (Nat.blt (:of q) n2) true)) (rw [e2]) (exact (comp-facts-blt-of _ _ hl))
  (have o (= (alive-run-latest-one n2 (tbl-upd comp-id cid f cs) q) true)) (simp only [alive-run-latest-one b t Bool.and_self Bool.or_true])
  (simp only [alive-run-latest-k tbl-all o h1 Bool.and_self]))
(a/theorem alive-run-latest-mem-lt [w :- World, c :- CompRow] (=> (= (well-formed w) true) (List.Mem c (:comps w)) (< (:id c) (:next-id w)))
  (intros hs mc) (exact (comp-below w (:id c) hs (comp-mem-has w c mc))))
(a/theorem alive-run-latest-start-raw-x [w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (tbl-all (not-alive-of (:id c)) (:runs w)) true) (= (alive-run-latest w) true) (= (alive-run-latest (start-raw w c)) true))
  (intros mc hn h)
  (have hs := (alive-run-latest-well-formed w h))
  (have r0 := (alive-run-latest-rest-of w h)) (simp only [alive-run-latest-rest] at r0)
  (have z := (alive-run-latest-mem-lt w c hs mc))
  (have l2 (< (:id c) (+ (+ (:next-id w) 1) 1))) (omega)
  (have l3 (<= (:next-id w) (+ (+ (:next-id w) 1) 1))) (omega)
  (have rr (= (alive-run-latest-rest (start-raw w c)) true))
  (show (= (alive-run-latest-k (+ (+ (:next-id w) 1) 1) (tbl-upd comp-id (:id c) (comp-start-row (:next-id w)) (:comps w))
                 (List.cons RunRow (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0) (:runs w))) true))
  (exact (alive-run-latest-k-newrun-own _ _ (:id c) (:next-id w) (comp-start-row (:next-id w)) (comp-start-row-id (:next-id w))
           (fn [x :- CompRow] (Eq.refl (:next-id w))) _ _ (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0)
           (rfl) (rfl) l2 l3 hn r0))
  (exact (alive-run-latest-intro _ (well-formed-start-raw w c hs) rr)))
(a/theorem alive-run-latest-new-run-of-x [w :- World, c :- CompRow, ei :- Nat]
  (=> (= (comp-has w (:id c)) true) (= (tbl-all (not-alive-of (:id c)) (:runs w)) true) (= (alive-run-latest w) true) (= (alive-run-latest (new-run-of w c ei)) true))
  (intros hc hn h)
  (have hs := (alive-run-latest-well-formed w h))
  (have r0 := (alive-run-latest-rest-of w h)) (simp only [alive-run-latest-rest] at r0)
  (have z := (comp-below w (:id c) hs hc))
  (have l2 (< (:id c) (+ (+ (:next-id w) 1) 1))) (omega)
  (have l3 (<= (:next-id w) (+ (+ (:next-id w) 1) 1))) (omega)
  (have rr (= (alive-run-latest-rest (new-run-of w c ei)) true))
  (show (= (alive-run-latest-k (+ (+ (:next-id w) 1) 1) (tbl-upd comp-id (:id c) (comp-set-run (:next-id w)) (:comps w))
                 (List.cons RunRow (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w))) true))
  (exact (alive-run-latest-k-newrun-own _ _ (:id c) (:next-id w) (comp-set-run (:next-id w)) (comp-set-run-id (:next-id w))
           (fn [x :- CompRow] (Eq.refl (:next-id w))) _ _ (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei)
           (rfl) (rfl) l2 l3 hn r0))
  (exact (alive-run-latest-intro _ (well-formed-new-run-of w c ei hs) rr)))

;; T5: a startable computation has no alive run (AR; g7's a7 for an idle one; run ids are not 0)
(a/theorem alive-run-latest-startable-none [w :- World, c :- CompRow]
  (=> (= (i7-idle w) true) (= (alive-run-latest w) true) (List.Mem c (:comps w)) (= (startable w c) true)
      (= (tbl-all (not-alive-of (:id c)) (:runs w)) true))
  (intros hg h mc hst)
  (have hs := (alive-run-latest-well-formed w h))
  (apply (all-of-mem RunRow (not-alive-of (:id c)) (:runs w)))
  (intros q mq)
  (cases ha (run-alive q))
  (case [false] (simp only [not-alive-of ha Bool.not_false Bool.true_or]))
  (case [true]
    (cases ho (Nat.beq (:of q) (:id c)))
    (case [false] (simp only [not-alive-of ho Bool.not_false Bool.or_true]))
    (case [true]
      (have eo (= (:id c) (:of q))) (exact (Eq.symm (Nat.eq_of_beq_eq_true ho)))
      (have e1 := (alive-run-latest-use w q c h mq ha mc eo))
      (exfalso)
      (simp only [startable Bool.or_eq_true Bool.and_eq_true] at hst)
      (cases hst)
      (case [inl A]
        (have nb := (And.right A))
        (cases hf (run-find w (:run c)))
        (case [none]
          (have z := (tbl-find-none-has RunRow run-id (:run c) (:runs w) hf))
          (have z2 := (mem-ids-has RunRow run-id q (:runs w) mq)) (rw [nat-mem-ids] at z2)
          (have z3 (= (tbl-has run-id (:run c) (:runs w)) true)) (rw [e1]) (exact z2)
          (rw [z] at z3) (cases z3))
        (case [some r]
          (simp only [run-busy hf] at nb)
          (have dr := (bnot-true _ nb))
          (have p := (find-run-mem w (:run c) r hf))
          (have d := (alive-run-latest-dead-id w r q hs (And.left p) dr mq (Eq.trans (Eq.symm e1) (Eq.symm (And.right p)))))
          (rw [ha] at d) (cases d)))
      (case [inr B]
        (cases B)
        (case [inl B1]
          (have hi := (And.left B1))
          (have p := (i7-idle-keys-ok-parts _ _ _ (i7-idle-rest-of w hg)))
          (have a1 := (tbl-all-mem RunRow _ q (:runs w) (And.left p) mq))
          (simp only [a7-one ha Bool.not_true Bool.false_or awake] at a1)
          (have a2 := (tbl-all-mem CompRow _ c (:comps w) a1 mc))
          (have i2 (= (Nat.beq (:id c) (:of q)) true)) (rw [eo]) (exact (Nat.beq_refl _))
          (simp only [not-idle-if-id i2 hi Bool.not_true Bool.false_or] at a2)
          (cases a2))
        (case [inr C]
          (have z := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right C)))))
          (have zq := (run-id-pos w q hs mq))
          (have e2 (= (:id q) 0)) (exact (Eq.trans (Eq.symm e1) z))
          (rw [e2] at zq) (cases zq))))))
(a/theorem alive-run-latest-start-raw [w :- World, c :- CompRow]
  (=> (= (i7-idle w) true) (List.Mem c (:comps w)) (= (startable w c) true) (= (alive-run-latest w) true) (= (alive-run-latest (start-raw w c)) true))
  (intros hg mc hst h) (exact (alive-run-latest-start-raw-x w c mc (alive-run-latest-startable-none w c hg h mc hst) h)))

;; T11: the predecessor cancel kills C's only alive run (idle's KDB), the cut and the entry keep the runs
(a/theorem alive-run-latest-none-find-none [w :- World, c :- CompRow]
  (=> (= (alive-run-latest w) true) (List.Mem c (:comps w)) (= (run-find w (:run c)) (Option.none RunRow)) (= (tbl-all (not-alive-of (:id c)) (:runs w)) true))
  (intros h mc hf)
  (apply (all-of-mem RunRow (not-alive-of (:id c)) (:runs w)))
  (intros q mq)
  (cases ha (run-alive q))
  (case [false] (simp only [not-alive-of ha Bool.not_false Bool.true_or]))
  (case [true]
    (cases ho (Nat.beq (:of q) (:id c)))
    (case [false] (simp only [not-alive-of ho Bool.not_false Bool.or_true]))
    (case [true]
      (have e1 := (alive-run-latest-use w q c h mq ha mc (Eq.symm (Nat.eq_of_beq_eq_true ho))))
      (have z := (tbl-find-none-has RunRow run-id (:run c) (:runs w) hf))
      (have z2 := (mem-ids-has RunRow run-id q (:runs w) mq)) (rw [nat-mem-ids] at z2)
      (have z3 (= (tbl-has run-id (:run c) (:runs w)) true)) (rw [e1]) (exact z2)
      (rw [z] at z3) (cases z3))))
(a/theorem alive-run-latest-alive-runs-listed-init [w :- World, c :- CompRow, r :- RunRow]
  (=> (= (alive-run-latest w) true) (List.Mem c (:comps w)) (= (:id r) (:run c))
      (= (alive-runs-listed (:id c) (List.cons Nat (:id r) (List.nil Nat)) (List.nil Nat) w) true))
  (intros h mc er)
  (have hs := (alive-run-latest-well-formed w h))
  (apply (alive-runs-listed-intro _ _ _ w hs))
  (simp only [alive-runs-listed-rest])
  (apply (all-of-mem RunRow (kd-one (:id c) (List.cons Nat (:id r) (List.nil Nat)) (List.nil Nat)) (:runs w)))
  (intros q mq)
  (cases ha (run-alive q))
  (case [false] (simp only [kd-one ha reach-mem Bool.not_false Bool.true_or Bool.and_self]))
  (case [true]
    (cases ho (Nat.beq (:of q) (:id c)))
    (case [false] (simp only [kd-one ha ho reach-mem Bool.not_false Bool.not_true Bool.false_or Bool.true_or Bool.and_self]))
    (case [true]
      (have e1 := (alive-run-latest-use w q c h mq ha mc (Eq.symm (Nat.eq_of_beq_eq_true ho))))
      (have m (= (reach-mem (:id q) (List.cons Nat (:id r) (List.nil Nat))) true))
      (have i (= (Nat.beq (:id q) (:id r)) true)) (rw [er (Eq.symm e1)]) (exact (Nat.beq_refl _))
      (simp only [reach-mem-cons i Bool.true_or])
      (simp only [kd-one ha ho m reach-mem Bool.not_false Bool.not_true Bool.false_or Bool.true_or Bool.or_true Bool.and_self]))))
(a/theorem alive-run-latest-cancel-pred-none [w :- World, c :- CompRow]
  (=> (= (acts-alive w) true) (= (alive-run-latest w) true) (List.Mem c (:comps w))
      (= (tbl-all (not-alive-of (:id c)) (:runs (cancel-pred w c))) true))
  (intros haa h mc)
  (have hs := (alive-run-latest-well-formed w h))
  (cases hf (run-find w (:run c))) (case' [some r]) (case' [none])
  (simp only [cancel-pred hf]) (exact (alive-run-latest-none-find-none w c h mc hf))
  (have p := (find-run-mem w (:run c) r hf))
  (cases ha (run-alive r))
  (simp only [cancel-pred hf ha]) (exact (alive-run-latest-none-of-dead w r c h (And.left p) ha mc (Eq.symm (And.right p))))
  (simp only [cancel-pred hf ha run-cascade cascade-run])
  (have k0 := (alive-run-latest-alive-runs-listed-init w c r h mc (And.right p)))
  (have cv (= (tbl-all (cov-one (List.nil Nat) (List.cons Job (Job.jcancel (:id r) true) (List.nil Job))) (List.cons Nat (:id r) (List.nil Nat))) true))
  (simp only [tbl-all cov-one tbl-any job-cancels reach-mem Nat.beq_refl Bool.true_or Bool.false_or Bool.and_self])
  (have cd := (cascade-done-ok w (List.cons Job (Job.jcancel (:id r) true) (List.nil Job)) hs haa))
  (simp only [cascade-done cascade-run] at cd)
  (exact (cascade-kill (:id c) _ _ w _ (List.nil Nat) k0 cv cd)))
(a/theorem alive-run-latest-runs-cut [w :- World, c :- Nat, has :- Bool, cut :- Nat, cid :- Nat] (= (:runs (cut-suffix w c has cut cid)) (:runs w)) (rfl))
(a/theorem alive-run-latest-runs-consume [w :- World, e :- EdgeRow] (= (:runs (consume-entry w e)) (:runs w))
  (cases hf (deb-final w (:debtor e)))
  (case [true] (simp only [consume-entry hf]) (exact (runs-remove-edge w (:id e))))
  (case [false] (cases hc (Nat.beq (:cont e) cont-restart)) (all_goals (simp only [consume-entry hf hc edge-upd set-edges]))))
(tree/restate! AR '[well-formed-cancel-pred well-formed-cut-suffix well-formed-consume-entry])
(a/theorem alive-run-latest-dispatch-raw [w :- World, c :- CompRow]
  (=> (= (acts-alive w) true) (List.Mem c (:comps w)) (= (alive-run-latest w) true) (= (alive-run-latest (dispatch-raw w c)) true))
  (intros haa mc h)
  (have hs := (alive-run-latest-well-formed w h))
  (have h1 := (alive-run-latest-cancel-pred w c h))
  (have n1 := (alive-run-latest-cancel-pred-none w c haa h mc))
  (have c1 := (comp-exists-cancel-pred (:id c) w c (comp-exists-intro (:id c) w hs (comp-mem-has w c mc))))
  (cases he (entry-edge w (:id c)))
  (case [none]
    (simp only [dispatch-raw he])
    (have c2 := (comp-exists-cut-suffix (:id c) _ (:id c) false 0 0 c1))
    (have n2 (= (tbl-all (not-alive-of (:id c)) (:runs (cut-suffix (cancel-pred w c) (:id c) false 0 0))) true)) (rw [alive-run-latest-runs-cut]) (exact n1)
    (exact (alive-run-latest-new-run-of-x _ c 0 (comp-exists-rest-of (:id c) _ c2) n2 (alive-run-latest-cut-suffix _ (:id c) false 0 0 h1))))
  (case [some e]
    (simp only [dispatch-raw he])
    (have c2 := (comp-exists-consume-entry (:id c) _ e (comp-exists-cut-suffix (:id c) _ (:id c) true (:at e) (:id e) c1)))
    (have n2 (= (tbl-all (not-alive-of (:id c)) (:runs (consume-entry (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e))) true))
    (rw [alive-run-latest-runs-consume alive-run-latest-runs-cut]) (exact n1)
    (exact (alive-run-latest-new-run-of-x _ c (entry-ei e) (comp-exists-rest-of (:id c) _ c2) n2
             (alive-run-latest-consume-entry _ e (alive-run-latest-cut-suffix _ (:id c) true (:at e) (:id e) h1))))))


;; ---- demote: its cascade kills every alive run of C (idle's demote-dead), then C.run := 0
(a/theorem alive-run-latest-demote-finish [w :- World, cid :- Nat, vs :- (List Valid)]
  (=> (= (tbl-all (not-alive-of cid) (:runs w)) true) (= (alive-run-latest w) true) (= (alive-run-latest (demote-finish w cid vs)) true))
  (intros hna h)
  (cases hf (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [demote-finish hf]) (exact h)
  (cases hk (demote-keep w c))
  (simp only [demote-finish hf hk])
  (exact (alive-run-latest-comp-del-unref _ cid (drop-edges-avoids w cid) (alive-run-latest-drop-edges w (edge-avoids cid) h)))
  (simp only [demote-finish hf hk])
  (have r0 := (alive-run-latest-rest-of w h)) (simp only [alive-run-latest-rest] at r0)
  (have r1 (= (alive-run-latest-rest (comp-upd w cid (comp-demote-row vs))) true))
  (simp only [alive-run-latest-rest comp-upd set-comps])
  (exact (alive-run-latest-k-clear _ cid (comp-demote-row vs) (comp-demote-row-id vs) _ _ hna r0))
  (exact (alive-run-latest-intro _ (well-formed-comp-upd w cid (comp-demote-row vs) (comp-demote-row-id vs) (comp-demote-row-pending vs) (alive-run-latest-well-formed w h)) r1)))
(tree/restate! AR '[well-formed-run-cascade well-formed-demote-epoch well-formed-drop-edges well-formed-end-basis])
(a/theorem alive-run-latest-demote [w :- World, cid :- Nat]
  (=> (= (acts-alive w) true) (= (alive-run-latest w) true) (= (alive-run-latest (demote w cid)) true))
  (intros ha h)
  (cases hf (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [demote hf]) (exact h)
  (cases hi (:idle c))
  (simp only [demote hf hi demote-edges])
  (have e (= (:id c) cid)) (exact (tbl-find-id CompRow comp-id cid c (:comps w) hf))
  (have na := (demote-dead w c (alive-run-latest-well-formed w h) ha))
  (rw [e] at na)
  (have g1 := (alive-run-latest-run-cascade w (cancel-jobs (demote-cancels w c)) h))
  (have g2 := (alive-run-latest-demote-epoch _ cid (demote-cur w c) g1))
  (have g3 := (alive-run-latest-drop-edges _ (not-dep-of cid) g2))
  (have na3 (= (tbl-all (not-alive-of cid) (:runs (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) cid (demote-cur w c)) (not-dep-of cid)))) true))
  (simp only [drop-edges set-comps set-edges runs-demote-epoch]) (exact na)
  (exact (alive-run-latest-demote-finish _ cid _ (end-basis-dead _ cid cid (alive-run-latest-well-formed _ g3) na3) (alive-run-latest-end-basis _ cid g3)))
  (simp only [demote hf hi]) (exact h))
(a/theorem alive-run-latest-demote-fold [a :- Nat, k :- Nat, xs :- (List Nat)]
  (forall [w :- World] (=> (= (round-bound a k w) true) (= (alive-run-latest w) true) (= (alive-run-latest (nat-fold demote w xs)) true)))
  (induction xs)
  (case [nil] (intros w hb h) (simp only [nat-fold]) (exact h))
  (case [cons hd t ih]
    (intros w hb h) (simp only [nat-fold])
    (exact (ih (demote w hd) (round-bound-demote a k w hd hb) (alive-run-latest-demote w hd (And.left (And.right (round-bound-parts a k w hb))) h)))))
;; normalization: demote takes acts-alive, which the round's cascade and the demotions keep (idle's round-bound)
(tree/restate! AR '[well-formed-run-cascade well-formed-detach])
(a/theorem alive-run-latest-normalize-round [w :- World]
  (=> (= (acts-alive w) true) (= (alive-run-latest w) true) (= (alive-run-latest (normalize-round w)) true))
  (intros ha h)
  (simp only [normalize-round normalize-round-with-live])
  (have b0 := (round-bound-intro (alive-cnt w) (act-cnt w) w (alive-run-latest-well-formed w h) ha (Nat.le_refl _) (Nat.le_refl _)))
  (exact (alive-run-latest-detach _ (alive-run-latest-demote-fold (alive-cnt w) (act-cnt w) _ _
           (round-bound-run-cascade _ _ w _ b0) (alive-run-latest-run-cascade w _ h)))))
(a/theorem alive-run-latest-normalize-loop [fuel :- (List Nat)]
  (forall [w :- World] (=> (= (acts-alive w) true) (= (alive-run-latest w) true) (= (alive-run-latest (normalize-loop fuel w)) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w ha hw) (simp only [normalize-loop]) (exact hw)
  (intros w ha hw)
  (cases hn (normalized w))
  (simp only [normalize-loop hn])
  (exact (ih (normalize-round w) (And.right (round-bound-round w (alive-run-latest-well-formed w hw) ha)) (alive-run-latest-normalize-round w ha hw)))
  (simp only [normalize-loop hn]) (exact hw))
(a/theorem alive-run-latest-normalize [w :- World]
  (=> (= (acts-alive w) true) (= (alive-run-latest w) true) (= (alive-run-latest (normalize w)) true))
  (intros ha h)
  (have b := (round-bound-detach (alive-cnt w) (act-cnt w) w (round-bound-intro (alive-cnt w) (act-cnt w) w (alive-run-latest-well-formed w h) ha (Nat.le_refl _) (Nat.le_refl _))))
  (exact (alive-run-latest-normalize-loop (normalize-fuel (detach w)) (detach w) (And.left (And.right (round-bound-parts _ _ _ b))) (alive-run-latest-detach w h))))

;; ===========================================================================
;; Part E. The raw step, Rule R, the step, the literal I10 computation part
;; ===========================================================================

(tree/restate! AR '[well-formed-raw])

(a/theorem alive-run-latest-rule-r-round [w :- World]
  (=> (= (acts-alive w) true) (= (alive-run-latest w) true) (= (filter-safe (normalize w)) true) (= (alive-run-latest (rule-r-round w)) true))
  (intros ha h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (alive-run-latest-filter-world _ (keep-fn (normalize w)) (alive-run-latest-normalize w ha h) hf)))
(a/theorem alive-run-latest-rule-r-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (acts-alive w0) true) (= (alive-run-latest w0) true) (= (rounds-safe-loop fuel w0) true)
                            (= (alive-run-latest (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 ha h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (alive-run-latest-rule-r-round w0 ha h hs)))
  (case [cons x f ih]
    (intros w0 ha h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (alive-run-latest-rule-r-round w0 ha h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false]
      (simp only [ho] at hs) (simp only [rule-r-loop ho])
      (exact (ih (rule-r-round w0) (acts-alive-round w0 (alive-run-latest-well-formed w0 h) ha) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))
(a/theorem alive-run-latest-rule-r [w :- World]
  (=> (= (acts-alive w) true) (= (alive-run-latest w) true) (= (rule-r-safe w) true) (= (alive-run-latest (rule-r w)) true))
  (intros ha h hs)
  (simp only [rule-r-safe] at hs) (simp only [rule-r])
  (exact (alive-run-latest-rule-r-loop (rule-r-fuel w) w ha h hs)))

;; Theorem: AR is preserved by every step (hypotheses: i7-idle, acts-parked of the input, rule-r-safe of the raw world)
(a/theorem step-alive-run-latest [w :- World, it :- Item]
  (=> (= (i7-idle w) true) (= (acts-parked w) true) (= (alive-run-latest w) true) (= (rule-r-safe (:world (raw w it))) true) (= (alive-run-latest (:world (world-step w it))) true))
  (intros hg7 hga h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true]
    (have e2 := (step-accepted w it ha)) (rw [e2])
    (exact (alive-run-latest-rule-r (:world (raw w it)) (raw-acts-alive w it hga) (alive-run-latest-raw w it hg7 hga h) hs))))
(a/theorem alive-run-latest-empty [] (= (alive-run-latest empty-world) true) (rfl))

;; the literal reading (inv.clj `inv-i10-comp`)
(a/theorem alive-run-latest-i10-comp [w :- World] (=> (= (alive-run-latest w) true) (= (inv-i10-comp w) true))
  (intro h)
  (simp only [inv-i10-comp])
  (apply (all-of-mem RunRow (comp-run-is w) (:runs w)))
  (intros r mr)
  (cases ha (run-alive r))
  (case [false] (simp only [comp-run-is ha Bool.not_false Bool.true_or]))
  (case [true]
    (cases hf (comp-find w (:of r)))
    (case [none] (simp only [comp-run-is ha hf Bool.not_true Bool.false_or]))
    (case [some c]
      (have mc := (tbl-find-mem CompRow comp-id (:of r) c (:comps w) hf))
      (have ic (= (:id c) (:of r))) (exact (tbl-find-id CompRow comp-id (:of r) c (:comps w) hf))
      (have e := (alive-run-latest-use w r c h mr ha mc ic))
      (simp only [comp-run-is ha hf e Nat.beq_refl Bool.not_true Bool.false_or]))))
