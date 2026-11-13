(ns spindel.v2.ar
  "AR through `world-step` (I10's computation part, `inv-i10-comp`: every alive run of a computation is
  that computation's C.run), kernel-checked (Init only). The h-mem2 proof (spindel.v2.hm4) needs it at T6
  (a re-awaited site edge is held by no current activation).

  Bundle `ar` = inv-sample && for every alive run R: R.of < next-id and every computation row C with id
  R.of has C.run = R.id. Every composite inv-sample lemma is re-checked by lit's copier (`AR`, prefix ar-).
  Primitives: a computation edit that keeps (id, run), a run edit that keeps the id and never revives a
  run nor changes an alive run's `of` (idle's `run-down`), deletions and filters, fresh rows (a fresh
  computation id is no alive run's `of`). Overrides: parks (the parked run is alive), new runs (a task's
  run: no computation has the task's id; T5/T11: C has no alive run, then C.run := the new run), T13's
  clear (the retired run is dead, so C has no alive run), demote (its cascade kills every alive run of C:
  idle's `demote-dead`), T11's predecessor cancel (idle's KDB: the predecessor is C's only alive run).
  Theorems: step-ar, ar-empty, ar-i10-comp (ar w -> inv-i10-comp w)."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [clojure.walk :as walk]
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
            [spindel.v2.i10 :refer :all]
            [spindel.v2.i11 :refer :all]
            [spindel.v2.i1 :refer :all]
            [spindel.v2.i8 :refer :all]
            [spindel.v2.hm :refer :all]))

;; ===========================================================================
;; Part A. The bundle
;; ===========================================================================

(a/defn ar-c [r :- RunRow, c :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id c) (:of r))) (Nat.beq (:run c) (:id r))))
(a/defn ar-one [n :- Nat, cs :- (List CompRow), r :- RunRow] Bool
  (Bool.or (Bool.not (run-alive r)) (Bool.and (Nat.blt (:of r) n) (tbl-all (ar-c r) cs))))
(a/defn ar-k [n :- Nat, cs :- (List CompRow), rs :- (List RunRow)] Bool (tbl-all (ar-one n cs) rs))
(a/defn ar-rest [w :- World] Bool (ar-k (:next-id w) (:comps w) (:runs w)))
(a/defn ar [w :- World] Bool (Bool.and (inv-sample w) (ar-rest w)))

(a/theorem ar-sample [w :- World] (=> (= (ar w) true) (= (inv-sample w) true))
  (intro h) (simp only [ar Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem ar-rest-of [w :- World] (=> (= (ar w) true) (= (ar-rest w) true))
  (intro h) (simp only [ar Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem ar-intro [w :- World] (=> (= (inv-sample w) true) (= (ar-rest w) true) (= (ar w) true))
  (intros h1 h2) (simp only [ar h1 h2 Bool.and_self]))
(a/theorem ar-parts [w :- World]
  (=> (= (ar w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (ar-sample w h))))

;; ---- the per-run fact, unfolded
(a/theorem ar-one-use [n :- Nat, cs :- (List CompRow), r :- RunRow, c :- CompRow]
  (=> (= (ar-one n cs r) true) (= (run-alive r) true) (List.Mem c cs) (= (:id c) (:of r)) (= (:run c) (:id r)))
  (intros h ha mc e)
  (simp only [ar-one ha Bool.not_true Bool.false_or Bool.and_eq_true] at h)
  (have q := (tbl-all-mem CompRow (ar-c r) c cs (And.right h) mc))
  (have i (= (Nat.beq (:id c) (:of r)) true)) (rw [e]) (exact (Nat.beq_refl _))
  (simp only [ar-c i Bool.not_true Bool.false_or] at q)
  (exact (Nat.eq_of_beq_eq_true q)))
(a/theorem ar-use [w :- World, r :- RunRow, c :- CompRow]
  (=> (= (ar w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (List.Mem c (:comps w)) (= (:id c) (:of r)) (= (:run c) (:id r)))
  (intros h mr ha mc e)
  (have h1 := (ar-rest-of w h)) (simp only [ar-rest ar-k] at h1)
  (exact (ar-one-use _ _ r c (tbl-all-mem RunRow _ r (:runs w) h1 mr) ha mc e)))

;; ===========================================================================
;; Part B. Transfer lemmas and primitives
;; ===========================================================================

(a/structure ARK [] (id Nat) (run Nat))
(a/defn ark [c :- CompRow] ARK (ARK.mk (:id c) (:run c)))

(a/theorem ar-c-key [r :- RunRow, c :- CompRow, c2 :- CompRow]
  (=> (= (ark c2) (ark c)) (= (ar-c r c) true) (= (ar-c r c2) true))
  (intros e h)
  (have e1 (= (:id c2) (:id c))) (exact (congrArg (fn [k :- ARK] (:id k)) e))
  (have e2 (= (:run c2) (:run c))) (exact (congrArg (fn [k :- ARK] (:run k)) e))
  (simp only [ar-c e1 e2]) (simp only [ar-c] at h) (exact h))
(a/theorem ar-c-same [q :- RunRow, r :- RunRow, c :- CompRow]
  (=> (= (:id q) (:id r)) (= (:of q) (:of r)) (= (ar-c r c) true) (= (ar-c q c) true))
  (intros e1 e2 h) (simp only [ar-c e1 e2]) (simp only [ar-c] at h) (exact h))

;; computations: any change that keeps every run's comps fact
(a/theorem ar-one-comps [n :- Nat, cs :- (List CompRow), cs2 :- (List CompRow), r :- RunRow]
  (=> (=> (= (tbl-all (ar-c r) cs) true) (= (tbl-all (ar-c r) cs2) true)) (= (ar-one n cs r) true) (= (ar-one n cs2 r) true))
  (intros hc h)
  (cases ha (run-alive r))
  (case [false] (simp only [ar-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ar-one ha Bool.not_true Bool.false_or Bool.and_eq_true] at h)
    (simp only [ar-one ha (And.left h) (hc (And.right h)) Bool.not_true Bool.false_or Bool.and_self])))
(a/theorem ar-k-comps [n :- Nat, cs :- (List CompRow), cs2 :- (List CompRow), rs :- (List RunRow)]
  (=> (forall [r :- RunRow] (=> (= (tbl-all (ar-c r) cs) true) (= (tbl-all (ar-c r) cs2) true)))
      (= (ar-k n cs rs) true) (= (ar-k n cs2 rs) true))
  (intros hc h)
  (simp only [ar-k] at h) (simp only [ar-k])
  (have g (forall [r :- RunRow] (=> (= (ar-one n cs r) true) (= (ar-one n cs2 r) true))))
  (intros r hr) (exact (ar-one-comps n cs cs2 r (hc r) hr))
  (exact (tbl-all-mono RunRow _ _ g rs h)))
(a/theorem ar-k-next [n :- Nat, n2 :- Nat, cs :- (List CompRow), rs :- (List RunRow)]
  (=> (<= n n2) (= (ar-k n cs rs) true) (= (ar-k n2 cs rs) true))
  (intros hl h)
  (simp only [ar-k] at h) (simp only [ar-k])
  (have g (forall [r :- RunRow] (=> (= (ar-one n cs r) true) (= (ar-one n2 cs r) true))))
  (intros r hr)
  (cases ha (run-alive r))
  (case [false] (simp only [ar-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ar-one ha Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
    (have z := (gd-lt-of _ _ (And.left hr)))
    (have b (= (Nat.blt (:of r) n2) true)) (apply gd-blt-of) (omega)
    (simp only [ar-one ha b (And.right hr) Bool.not_true Bool.false_or Bool.and_self]))
  (exact (tbl-all-mono RunRow _ _ g rs h)))

(a/theorem ar-cs-upd [x :- Nat, f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (ark (f c)) (ark c))), r :- RunRow, cs :- (List CompRow)]
  (=> (= (tbl-all (ar-c r) cs) true) (= (tbl-all (ar-c r) (tbl-upd comp-id x f cs)) true))
  (intro h)
  (have hin (forall [c :- CompRow] (=> (= (ar-c r c) true) (= (Nat.beq (comp-id c) x) true) (= (ar-c r (f c)) true))))
  (intros c hc hx) (exact (ar-c-key r c (f c) (hk c) hc))
  (have hout (forall [c :- CompRow] (=> (= (ar-c r c) true) (= (Nat.beq (comp-id c) x) false) (= (ar-c r c) true))))
  (intros c hc hx) (exact hc)
  (exact (tbl-all-upd CompRow comp-id x f (ar-c r) (ar-c r) hin hout cs h)))
(a/theorem ar-cs-del [x :- Nat, r :- RunRow, cs :- (List CompRow)]
  (=> (= (tbl-all (ar-c r) cs) true) (= (tbl-all (ar-c r) (tbl-del comp-id x cs)) true))
  (intro h)
  (have hout (forall [c :- CompRow] (=> (= (ar-c r c) true) (= (Nat.beq (comp-id c) x) false) (= (ar-c r c) true))))
  (intros c hc hx) (exact hc)
  (exact (tbl-all-del CompRow comp-id x (ar-c r) (ar-c r) hout cs h)))
(a/theorem ar-cs-keep [K :- (=> Nat Bool), r :- RunRow, cs :- (List CompRow)]
  (=> (= (tbl-all (ar-c r) cs) true) (= (tbl-all (ar-c r) (tbl-keep K comp-id cs)) true))
  (intro h)
  (have hk (forall [c :- CompRow] (=> (= (ar-c r c) true) (= (K (comp-id c)) true) (= (ar-c r c) true))))
  (intros c hc hx) (exact hc)
  (exact (tbl-all-keep CompRow K comp-id (ar-c r) (ar-c r) hk cs h)))
(a/theorem ar-cs-resync [es :- (List EdgeRow), r :- RunRow, cs :- (List CompRow)]
  (=> (= (tbl-all (ar-c r) cs) true) (= (tbl-all (ar-c r) (comps-resync es cs)) true))
  (induction cs)
  (case [nil] (intro h) (simp only [comps-resync tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (simp only [tbl-all Bool.and_eq_true] at h)
    (have a1 (= (ar-c r (comp-resync es hd)) true)) (exact (ar-c-key r hd (comp-resync es hd) (rfl) (And.left h)))
    (simp only [comps-resync tbl-all a1 (ih (And.right h)) Bool.and_self])))

;; runs: an edit by a row function that keeps the id and never revives (idle's run-down)
(a/theorem ar-one-down [n :- Nat, cs :- (List CompRow), f :- (=> RunRow RunRow), r :- RunRow]
  (=> (= (run-down f r) true) (= (:id (f r)) (:id r)) (= (ar-one n cs r) true) (= (ar-one n cs (f r)) true))
  (intros hd hi h)
  (cases ha (run-alive (f r)))
  (case [false] (simp only [ar-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [run-down ha Bool.not_true Bool.false_or Bool.and_eq_true] at hd)
    (have eo (= (:of (f r)) (:of r))) (exact (Nat.eq_of_beq_eq_true (And.right hd)))
    (simp only [ar-one (And.left hd) Bool.not_true Bool.false_or Bool.and_eq_true] at h)
    (have g (forall [c :- CompRow] (=> (= (ar-c r c) true) (= (ar-c (f r) c) true))))
    (intros c hc) (exact (ar-c-same (f r) r c hi eo hc))
    (have t (= (tbl-all (ar-c (f r)) cs) true)) (exact (tbl-all-mono CompRow _ _ g cs (And.right h)))
    (have b (= (Nat.blt (:of (f r)) n) true)) (rw [eo]) (exact (And.left h))
    (simp only [ar-one ha b t Bool.not_true Bool.false_or Bool.and_self])))
(a/theorem ar-k-run-upd [n :- Nat, cs :- (List CompRow), x :- Nat, f :- (=> RunRow RunRow),
                         hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         hd :- (forall [r :- RunRow] (= (run-down f r) true)), rs :- (List RunRow)]
  (=> (= (ar-k n cs rs) true) (= (ar-k n cs (tbl-upd run-id x f rs)) true))
  (intro h)
  (simp only [ar-k] at h) (simp only [ar-k])
  (have hin (forall [r :- RunRow] (=> (= (ar-one n cs r) true) (= (Nat.beq (run-id r) x) true) (= (ar-one n cs (f r)) true))))
  (intros r hr hx) (exact (ar-one-down n cs f r (hd r) (hid r) hr))
  (have hout (forall [r :- RunRow] (=> (= (ar-one n cs r) true) (= (Nat.beq (run-id r) x) false) (= (ar-one n cs r) true))))
  (intros r hr hx) (exact hr)
  (exact (tbl-all-upd RunRow run-id x f (ar-one n cs) (ar-one n cs) hin hout rs h)))

;; ---- full-bundle forms
(a/theorem ar-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hk :- (forall [c :- CompRow] (= (ark (f c)) (ark c)))]
  (=> (= (ar w) true) (= (ar (comp-upd w x f)) true))
  (intro h)
  (have r0 := (ar-rest-of w h)) (simp only [ar-rest] at r0)
  (have g (forall [r :- RunRow] (=> (= (tbl-all (ar-c r) (:comps w)) true) (= (tbl-all (ar-c r) (tbl-upd comp-id x f (:comps w))) true))))
  (intros r hr) (exact (ar-cs-upd x f hk r (:comps w) hr))
  (have r1 (= (ar-rest (comp-upd w x f)) true))
  (simp only [ar-rest comp-upd set-comps])
  (exact (ar-k-comps _ _ _ _ g r0))
  (exact (ar-intro _ (inv-comp-upd w x f hid hp (ar-sample w h)) r1)))
(a/theorem ar-run-upd-m [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                         hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         hd :- (forall [r :- RunRow] (= (run-down f r) true))]
  (=> (= (ar w) true) (= (ar (run-upd w x f)) true))
  (intro h)
  (have r0 := (ar-rest-of w h)) (simp only [ar-rest] at r0)
  (have r1 (= (ar-rest (run-upd w x f)) true))
  (simp only [ar-rest run-upd set-runs])
  (exact (ar-k-run-upd _ _ x f hid hd _ r0))
  (exact (ar-intro _ (inv-run-upd w x f hid (ar-sample w h)) r1)))
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
(a/theorem ar-run-upd-a [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (arrk (f r)) (arrk r)))]
  (=> (= (ar w) true) (= (ar (run-upd w x f)) true))
  (exact (ar-run-upd-m w x f hid (arrk-down f hk))))

;; ---- rest lemmas of the table primitives
(a/theorem arr-grow [w :- World, w2 :- World]
  (=> (= (:comps w2) (:comps w)) (= (:runs w2) (:runs w)) (<= (:next-id w) (:next-id w2)) (= (ar-rest w) true) (= (ar-rest w2) true))
  (intros e1 e2 hl h)
  (simp only [ar-rest e1 e2]) (simp only [ar-rest] at h)
  (exact (ar-k-next _ _ _ _ hl h)))
(a/theorem arr-comps [w :- World, w2 :- World]
  (=> (forall [r :- RunRow] (=> (= (tbl-all (ar-c r) (:comps w)) true) (= (tbl-all (ar-c r) (:comps w2)) true)))
      (= (:runs w2) (:runs w)) (= (:next-id w2) (:next-id w)) (= (ar-rest w) true) (= (ar-rest w2) true))
  (intros g e2 e3 h)
  (simp only [ar-rest e2 e3]) (simp only [ar-rest] at h)
  (exact (ar-k-comps _ _ _ _ g h)))
(a/theorem arr-comp-key [w :- World, x :- Nat, f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (ark (f c)) (ark c))), w2 :- World]
  (=> (= (:comps w2) (tbl-upd comp-id x f (:comps w))) (= (:runs w2) (:runs w)) (= (:next-id w2) (:next-id w))
      (= (ar-rest w) true) (= (ar-rest w2) true))
  (intros e1 e2 e3 h)
  (have g (forall [r :- RunRow] (=> (= (tbl-all (ar-c r) (:comps w)) true) (= (tbl-all (ar-c r) (:comps w2)) true))))
  (intros r hr) (rw [e1]) (exact (ar-cs-upd x f hk r (:comps w) hr))
  (exact (arr-comps w w2 g e2 e3 h)))

(a/theorem ark-inc-pending [c :- CompRow] (= (ark (comp-inc-pending c)) (ark c)) (rfl))
(a/theorem ark-dec-pending [c :- CompRow] (= (ark (comp-dec-pending c)) (ark c)) (rfl))
(a/theorem ark-set-pending [k :- Nat, c :- CompRow] (= (ark (comp-set-pending k c)) (ark c)) (rfl))

(a/theorem arr-mark-edge [w :- World, x :- Nat] (=> (= (ar-rest w) true) (= (ar-rest (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false]
      (simp only [mark-edge hf hm])
      (exact (arr-comp-key w (:creditor e) comp-inc-pending ark-inc-pending (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending) (rfl) (rfl) (rfl) h)))))
(a/theorem arr-unmark-edge [w :- World, x :- Nat] (=> (= (ar-rest w) true) (= (ar-rest (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true]
      (simp only [unmark-edge hf hm])
      (exact (arr-comp-key w (:creditor e) comp-dec-pending ark-dec-pending (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending) (rfl) (rfl) (rfl) h)))))
(a/theorem arr-remove-edge [w :- World, x :- Nat] (=> (= (ar-rest w) true) (= (ar-rest (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact (arr-grow w (edge-del w x) (rfl) (rfl) (Nat.le_refl _) h)))
    (case [true]
      (simp only [remove-edge hf hm])
      (exact (arr-comp-key w (:creditor e) comp-dec-pending ark-dec-pending (comp-upd (edge-del w x) (:creditor e) comp-dec-pending) (rfl) (rfl) (rfl) h)))))
(a/theorem arr-drop-cred [w :- World, a :- Nat] (=> (= (ar-rest w) true) (= (ar-rest (drop-cred-edges w a)) true))
  (intro h)
  (simp only [drop-cred-edges])
  (exact (arr-comp-key w a (comp-set-pending 0) (ark-set-pending 0) (comp-upd (set-edges w (tbl-filter (cred-ne a) (:edges w))) a (comp-set-pending 0)) (rfl) (rfl) (rfl) h)))
(a/theorem arr-drop-act [w :- World, a :- Nat] (=> (= (ar-rest w) true) (= (ar-rest (drop-act w a)) true))
  (intro h)
  (simp only [drop-act])
  (exact (arr-grow (drop-cred-edges w a) (act-del (drop-cred-edges w a) a) (rfl) (rfl) (Nat.le_refl _) (arr-drop-cred w a h))))
(a/theorem arr-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (=> (= (ar-rest w) true) (= (ar-rest (drop-edges w p)) true))
  (intro h)
  (have g (forall [r :- RunRow] (=> (= (tbl-all (ar-c r) (:comps w)) true)
                                    (= (tbl-all (ar-c r) (:comps (drop-edges w p))) true))))
  (intros r hr) (simp only [drop-edges set-comps set-edges]) (exact (ar-cs-resync _ r (:comps w) hr))
  (exact (arr-comps w (drop-edges w p) g (rfl) (rfl) h)))
(a/theorem arr-insert-edge-fresh [w :- World, e :- EdgeRow] (=> (= (ar-rest w) true) (= (ar-rest (insert-edge-fresh w e)) true))
  (intro h)
  (simp only [insert-edge-fresh])
  (exact (arr-grow w (bump (insert-edge w (edge-set-id (:next-id w) e))) (rfl) (rfl) (Nat.le_succ _) h)))
(a/theorem arr-insert-edge-checked [w :- World, e :- EdgeRow] (=> (= (ar-rest w) true) (= (ar-rest (insert-edge-checked w e)) true))
  (intro h)
  (cases hk (edge-ok-in w e))
  (simp only [insert-edge-checked hk]) (exact h)
  (simp only [insert-edge-checked hk]) (exact (arr-insert-edge-fresh w e h)))
(a/theorem arr-comp-del [w :- World, x :- Nat] (=> (= (ar-rest w) true) (= (ar-rest (comp-del w x)) true))
  (intro h)
  (have g (forall [r :- RunRow] (=> (= (tbl-all (ar-c r) (:comps w)) true) (= (tbl-all (ar-c r) (:comps (comp-del w x))) true))))
  (intros r hr) (simp only [comp-del set-comps]) (exact (ar-cs-del x r (:comps w) hr))
  (exact (arr-comps w (comp-del w x) g (rfl) (rfl) h)))
(a/theorem arr-run-del [w :- World, x :- Nat] (=> (= (ar-rest w) true) (= (ar-rest (run-del w x)) true))
  (intro h)
  (simp only [ar-rest ar-k run-del set-runs]) (simp only [ar-rest ar-k] at h)
  (have hout (forall [r :- RunRow] (=> (= (ar-one (:next-id w) (:comps w) r) true) (= (Nat.beq (run-id r) x) false) (= (ar-one (:next-id w) (:comps w) r) true))))
  (intros r hr hx) (exact hr)
  (exact (tbl-all-del RunRow run-id x _ _ hout (:runs w) h)))
(a/theorem arr-filter-world [w :- World, K :- (=> Nat Bool)] (=> (= (ar-rest w) true) (= (ar-rest (filter-world K w)) true))
  (intro h)
  (simp only [ar-rest ar-k] at h)
  (have g (forall [r :- RunRow] (=> (= (ar-one (:next-id w) (:comps w) r) true) (= (K (run-id r)) true)
                                    (= (ar-one (:next-id w) (tbl-keep K comp-id (:comps w)) r) true))))
  (intros r hr hk)
  (have g2 (=> (= (tbl-all (ar-c r) (:comps w)) true) (= (tbl-all (ar-c r) (tbl-keep K comp-id (:comps w))) true)))
  (intro q) (exact (ar-cs-keep K r (:comps w) q))
  (exact (ar-one-comps _ _ _ r g2 hr))
  (simp only [ar-rest ar-k filter-world])
  (exact (tbl-all-keep RunRow K run-id _ _ g (:runs w) h)))
;; a fresh computation: its id is no alive run's `of`
(a/theorem arr-comp-ins [w :- World, c :- CompRow] (=> (= (comp-id c) (:next-id w)) (= (ar-rest w) true) (= (ar-rest (bump (comp-ins w c))) true))
  (intros hc h)
  (simp only [ar-rest ar-k] at h)
  (have g (forall [r :- RunRow] (=> (= (ar-one (:next-id w) (:comps w) r) true)
                                    (= (ar-one (+ (:next-id w) 1) (tbl-ins c (:comps w)) r) true))))
  (intros r hr)
  (cases ha (run-alive r))
  (case [false] (simp only [ar-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ar-one ha Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
    (have z := (gd-lt-of _ _ (And.left hr)))
    (have b (= (Nat.blt (:of r) (+ (:next-id w) 1)) true)) (apply gd-blt-of) (omega)
    (have ne (= (Nat.beq (:id c) (:of r)) false))
    (have e (= (:id c) (:next-id w))) (exact hc)
    (cases hb (Nat.beq (:id c) (:of r))) (rfl) (have e2 := (Nat.eq_of_beq_eq_true hb)) (omega)
    (simp only [ar-one ha b tbl-ins tbl-all ar-c ne (And.right hr) Bool.not_true Bool.not_false Bool.false_or Bool.true_or Bool.and_self]))
  (simp only [ar-rest ar-k bump set-next-id comp-ins set-comps])
  (exact (tbl-all-mono RunRow _ _ g (:runs w) h)))
(a/theorem ar-comp-ins-fresh [w :- World, r :- CompRow]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (ar w) true) (= (ar (bump (comp-ins w r))) true))
  (intros h1 h2 h)
  (exact (ar-intro _ (inv-comp-ins-fresh w r h1 h2 (ar-sample w h)) (arr-comp-ins w r h1 (ar-rest-of w h)))))

;; ===========================================================================
;; Part C. The bundle copy
;; ===========================================================================

(def AR (mk-bundle 'ar [] "ar-" {'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (arrk r))) 4]
                                 'inv-comp-upd ['(fn [c :- CompRow] (Eq.refl (ark c))) 5]}))
(swap! (:renames AR) assoc 'inv-parts 'ar-parts 'inv-run-upd 'ar-run-upd-a 'inv-comp-upd 'ar-comp-upd
       'inv-comp-ins-fresh 'ar-comp-ins-fresh 'inv-run-ins-fresh 'ar-run-ins-NONE)
(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-set-pins
            inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-task-upd inv-edge-upd inv-set-released
            inv-set-pending-act]]
  (prim! AR o nil))
(doseq [[o t] '[[inv-source-ins-fresh source-ins] [inv-resource-ins-fresh resource-ins] [inv-scope-ins-fresh scope-ins]
                [inv-act-ins-fresh act-ins] [inv-task-ins-fresh task-ins]]]
  (prim! AR o (list 'arr-grow 'w (list 'bump (list t 'w 'r)) '(rfl) '(rfl) '(Nat.le_succ (:next-id w)) 'R)))
(prim! AR 'inv-bump '(arr-grow w (bump w) (rfl) (rfl) (Nat.le_succ (:next-id w)) R))
(prim! AR 'inv-remove-edge '(arr-remove-edge w x R))
(prim! AR 'mark-edge-inv-sample '(arr-mark-edge w x R))
(prim! AR 'unmark-edge-inv-sample '(arr-unmark-edge w x R))
(prim! AR 'inv-drop-cred '(arr-drop-cred w a R))
(prim! AR 'inv-drop-act '(arr-drop-act w a R))
(prim! AR 'inv-drop-edges '(arr-drop-edges w p R))
(prim! AR 'insert-edge-fresh-inv-sample '(arr-insert-edge-fresh w e R))
(prim! AR 'inv-insert-edge-checked '(arr-insert-edge-checked w e R))
(prim! AR 'inv-comp-del-unref '(arr-comp-del w x R))
(prim! AR 'inv-run-del '(arr-run-del w x R))
(prim! AR 'inv-filter-world '(arr-filter-world w K R))

;; the source patch: run edits by a row function that ends a run go through ar-run-upd-m, a wake through arrk
(def ^:private ar-run-fns '{run-cancel-row run-cancel-row-dwn run-complete-row run-complete-row-dwn
                            run-fin-pop-end run-fin-pop-end-dwn})
(defn- ar-fhead [f] (if (seq? f) (first f) f))
(defn- ar-lapp [f lem] (if (seq? f) (apply list lem (rest f)) lem))
(defn ar-patch [form]
  (->> (@#'spindel.v2.idle/fix-f form)
       (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (contains? ar-run-fns (ar-fhead (nth y 3 nil)))))
                    (fn [[_ w x f hid & more]] (apply list 'ar-run-upd-m w x f hid (ar-lapp f (ar-run-fns (ar-fhead f))) more)))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (= 'run-wake (nth y 3 nil))))
                    (fn [[_ w x f hid & more]] (apply list 'ar-run-upd-a w x f hid 'run-wake-arrk more)))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! AR n ar-patch))

;; ===========================================================================
;; Part D. Overrides
;; ===========================================================================

;; ---- T13's clear: the retired run is dead, so its computation has no alive run (AR + unique ids)
(a/theorem ar-dead-id [w :- World, r :- RunRow, q :- RunRow]
  (=> (= (inv-sample w) true) (List.Mem r (:runs w)) (= (run-alive r) false) (List.Mem q (:runs w)) (= (:id q) (:id r))
      (= (run-alive q) false))
  (intros hs mr hd mq e)
  (have nd (= (Bool.not (run-alive r)) true)) (simp only [hd Bool.not_false])
  (have D := (uniq-all RunRow run-id (fn [x :- RunRow] (Bool.not (run-alive x))) r (:runs w) (lit-runs-nodup w hs) mr nd))
  (have dq := (tbl-all-mem RunRow _ q (:runs w) D mq))
  (have i (= (Nat.beq (run-id q) (run-id r)) true)) (simp only [run-id]) (rw [e]) (exact (Nat.beq_refl _))
  (simp only [same-id-then i Bool.not_true Bool.false_or] at dq)
  (exact (bnot-true _ dq)))
;; no alive run has `of` = cid
(a/theorem ar-k-clear [n :- Nat, cid :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                       cs :- (List CompRow), rs :- (List RunRow)]
  (=> (= (tbl-all (not-alive-of cid) rs) true) (= (ar-k n cs rs) true) (= (ar-k n (tbl-upd comp-id cid f cs) rs) true))
  (intros hn h)
  (simp only [ar-k] at h) (simp only [ar-k])
  (have g (forall [q :- RunRow] (=> (= (ar-one n cs q) true) (= (not-alive-of cid q) true) (= (ar-one n (tbl-upd comp-id cid f cs) q) true))))
  (intros q hq hnq)
  (cases ha (run-alive q))
  (case [false] (simp only [ar-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [not-alive-of ha Bool.not_true Bool.false_or] at hnq)
    (have ho := (bnot-true _ hnq))
    (simp only [ar-one ha Bool.not_true Bool.false_or Bool.and_eq_true] at hq)
    (have hin (forall [c :- CompRow] (=> (= (ar-c q c) true) (= (Nat.beq (comp-id c) cid) true) (= (ar-c q (f c)) true))))
    (intros c hc hx)
    (have e1 (= (:id (f c)) cid)) (exact (Eq.trans (hid c) (Nat.eq_of_beq_eq_true hx)))
    (have e2 (= (Nat.beq (:id (f c)) (:of q)) false)) (rw [e1]) (exact (Eq.trans (beq-comm cid (:of q)) ho))
    (simp only [ar-c e2 Bool.not_false Bool.true_or])
    (have hout (forall [c :- CompRow] (=> (= (ar-c q c) true) (= (Nat.beq (comp-id c) cid) false) (= (ar-c q c) true))))
    (intros c hc hx) (exact hc)
    (have t (= (tbl-all (ar-c q) (tbl-upd comp-id cid f cs)) true)) (exact (tbl-all-upd CompRow comp-id cid f (ar-c q) (ar-c q) hin hout cs (And.right hq)))
    (simp only [ar-one ha (And.left hq) t Bool.not_true Bool.false_or Bool.and_self]))
  (exact (tbl-all-mono2 RunRow _ _ _ g rs h hn)))
;; C.run = R.id with R dead: no alive run of C
(a/theorem ar-none-of-dead [w :- World, r :- RunRow, c :- CompRow]
  (=> (= (ar w) true) (List.Mem r (:runs w)) (= (run-alive r) false) (List.Mem c (:comps w)) (= (:run c) (:id r))
      (= (tbl-all (not-alive-of (:id c)) (:runs w)) true))
  (intros h mr hd mc ec)
  (have hs := (ar-sample w h))
  (apply (all-of-mem RunRow (not-alive-of (:id c)) (:runs w)))
  (intros q mq)
  (cases ha (run-alive q))
  (case [false] (simp only [not-alive-of ha Bool.not_false Bool.true_or]))
  (case [true]
    (cases ho (Nat.beq (:of q) (:id c)))
    (case [false] (simp only [not-alive-of ho Bool.not_false Bool.or_true]))
    (case [true]
      (have e1 := (ar-use w q c h mq ha mc (Eq.symm (Nat.eq_of_beq_eq_true ho))))
      (have d := (ar-dead-id w r q hs mr hd mq (Eq.trans (Eq.symm e1) ec)))
      (rw [ha] at d) (cases d))))

(override! AR 'inv-clear-comp-run '[inv-clear-task-run]
  '(a/theorem ar-clear-comp-run [w :- World, r :- RunRow]
     (=> (List.Mem r (:runs w)) (= (run-alive r) false) (= (ar w) true) (= (ar (clear-comp-run w r)) true))
     (intros mr hd h)
     (have hs := (ar-sample w h))
     (cases hc (comp-find w (:of r))) (case' [some c]) (case' [none])
     (simp only [clear-comp-run hc]) (exact (ar-clear-task-run w r h))
     (cases hr (Nat.beq (:run c) (:id r)))
     (simp only [clear-comp-run hc hr]) (exact h)
     (simp only [clear-comp-run hc hr])
     (have mc := (tbl-find-mem CompRow comp-id (:of r) c (:comps w) hc))
     (have ic (= (:id c) (:of r))) (exact (tbl-find-id CompRow comp-id (:of r) c (:comps w) hc))
     (have hn := (ar-none-of-dead w r c h mr hd mc (Nat.eq_of_beq_eq_true hr)))
     (rw [ic] at hn)
     (have r0 := (ar-rest-of w h)) (simp only [ar-rest] at r0)
     (have r1 (= (ar-rest (comp-upd w (:of r) comp-clear-run)) true))
     (simp only [ar-rest comp-upd set-comps])
     (exact (ar-k-clear _ (:of r) comp-clear-run comp-clear-run-id _ _ hn r0))
     (exact (ar-intro _ (inv-comp-upd w (:of r) comp-clear-run comp-clear-run-id comp-clear-run-pending hs) r1))))
(override! AR 'inv-retire-with '[inv-remove-if-empty inv-cleanup-del inv-run-del inv-close-local inv-clear-comp-run]
  '(a/theorem ar-retire-with [w :- World, r :- RunRow, sub :- (List Nat)]
     (=> (List.Mem r (:runs w)) (= (run-alive r) false) (= (ar w) true) (= (ar (retire-with w r sub)) true))
     (intros mr hd h)
     (simp only [retire-with])
     (exact (ar-remove-if-empty _ sub
              (ar-cleanup-del _ (:id r) (ar-run-del _ (:id r) (ar-close-local _ sub (ar-clear-comp-run w r mr hd h))))))))
(override! AR 'inv-retire-local '[inv-retire-with]
  '(a/theorem ar-retire-local [w :- World, r :- RunRow]
     (=> (List.Mem r (:runs w)) (= (run-alive r) false) (= (ar w) true) (= (ar (retire-local w r)) true))
     (intros mr hd h) (exact (ar-retire-with w r (scope-subtree w (:scope r)) mr hd h))))
(override! AR 'inv-job-apply '[inv-cancel-run-local inv-retire-local inv-close-scope-local]
  '(a/theorem ar-job-apply [w :- World, j :- Job]
     (=> (= (ar w) true) (= (ar (job-apply w j)) true))
     (intro h)
     (cases j)
     (rename_i rid rep)
     (cases hf (run-find w rid)) (case' [some r]) (case' [none])
     (simp only [job-apply hf]) (exact h)
     (cases ha (run-alive r))
     (simp only [job-apply hf ha]) (exact h)
     (simp only [job-apply hf ha]) (exact (ar-cancel-run-local w r rep h))
     (rename_i rid)
     (cases hf (run-find w rid)) (case' [some r]) (case' [none])
     (simp only [job-apply hf]) (exact h)
     (cases ha (retirable r))
     (simp only [job-apply hf ha]) (exact h)
     (simp only [job-apply hf ha]) (exact (ar-retire-local w r (And.left (find-run-mem w rid r hf)) (retirable-dead r ha) h))
     (rename_i s)
     (cases hs (scope-has w s))
     (simp only [job-apply hs]) (exact h)
     (simp only [job-apply hs]) (exact (ar-close-scope-local w s h))))

;; ---- parks: the parked run was alive
(a/theorem ar-k-run-on [n :- Nat, cs :- (List CompRow), x :- Nat, f :- (=> RunRow RunRow),
                        hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hof :- (forall [r :- RunRow] (= (:of (f r)) (:of r))), rs :- (List RunRow)]
  (=> (= (tbl-all (run-ok-for x) rs) true) (= (ar-k n cs rs) true) (= (ar-k n cs (tbl-upd run-id x f rs)) true))
  (intros ho h)
  (simp only [ar-k] at h) (simp only [ar-k])
  (have b := (tbl-all-mono2 RunRow (ar-one n cs) (run-ok-for x) (both (ar-one n cs) (run-ok-for x))
               (fn [q :- RunRow, h1 :- (= (ar-one n cs q) true), h2 :- (= (run-ok-for x q) true)] (both-of RunRow (ar-one n cs) (run-ok-for x) q h1 h2))
               rs h ho))
  (have hin (forall [r :- RunRow] (=> (= (both (ar-one n cs) (run-ok-for x) r) true) (= (Nat.beq (run-id r) x) true) (= (ar-one n cs (f r)) true))))
  (intros r hb hx)
  (have hr := (both-left RunRow (ar-one n cs) (run-ok-for x) r hb))
  (have hk := (both-right RunRow (ar-one n cs) (run-ok-for x) r hb))
  (have hx2 (= (Nat.beq (:id r) x) true)) (exact hx)
  (simp only [run-ok-for hx2 Bool.not_true Bool.false_or] at hk)
  (simp only [ar-one hk Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
  (have g (forall [c :- CompRow] (=> (= (ar-c r c) true) (= (ar-c (f r) c) true))))
  (intros c hc) (exact (ar-c-same (f r) r c (hid r) (hof r) hc))
  (have t (= (tbl-all (ar-c (f r)) cs) true)) (exact (tbl-all-mono CompRow _ _ g cs (And.right hr)))
  (have b2 (= (Nat.blt (:of (f r)) n) true)) (rw [(hof r)]) (exact (And.left hr))
  (simp only [ar-one b2 t Bool.and_self Bool.or_true])
  (have hout (forall [r :- RunRow] (=> (= (both (ar-one n cs) (run-ok-for x) r) true) (= (Nat.beq (run-id r) x) false) (= (ar-one n cs r) true))))
  (intros r hb hx) (exact (both-left RunRow (ar-one n cs) (run-ok-for x) r hb))
  (exact (tbl-all-upd RunRow run-id x f _ (ar-one n cs) hin hout rs b)))
(a/theorem ar-run-upd-on [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                          hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                          hof :- (forall [r :- RunRow] (= (:of (f r)) (:of r)))]
  (=> (= (tbl-all (run-ok-for x) (:runs w)) true) (= (ar w) true) (= (ar (run-upd w x f)) true))
  (intros ho h)
  (have r0 := (ar-rest-of w h)) (simp only [ar-rest] at r0)
  (have r1 (= (ar-rest (run-upd w x f)) true))
  (simp only [ar-rest run-upd set-runs])
  (exact (ar-k-run-on _ _ x f hid hof _ ho r0))
  (exact (ar-intro _ (inv-run-upd w x f hid (ar-sample w h)) r1)))

(override! AR 'inv-park-if '[]
  '(a/theorem ar-park-if [w :- World, a :- Nat, rid :- Nat]
     (=> (= (tbl-all (run-ok-for rid) (:runs w)) true) (= (ar w) true) (= (ar (park-if w a rid)) true))
     (intros hk h)
     (cases ha (act-has w a))
     (simp only [park-if ha]) (exact h)
     (simp only [park-if ha]) (exact (ar-run-upd-on w rid run-park-row run-park-row-id (fn [q :- RunRow] (Eq.refl (:of q))) hk h))))
(override! AR 'inv-take-park '[inv-insert-edge-checked]
  '(a/theorem ar-take-park [w :- World, r :- RunRow, x :- Nat, k :- Nat]
     (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (ar w) true) (= (ar (take-park w r x k)) true))
     (intros hm hal h)
     (have o := (run-ok-of-mem w r (ar-sample w h) hm hal))
     (have h1 := (ar-insert-edge-checked _ (take-edge r (:next-id w) x) (ar-act-ins-fresh w (take-act w r k) (rfl) h)))
     (have o2 (= (tbl-all (run-ok-for (:id r)) (:runs (insert-edge-checked (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x)))) true))
     (rw [runs-iec]) (exact o)
     (simp only [take-park])
     (exact (ar-run-upd-on _ (:id r) run-tick-park run-tick-park-id (fn [q :- RunRow] (Eq.refl (:of q))) o2 h1))))
;; T6/take/arm: i8's overrides (the parked run is alive; KA through the await wiring), for ar
(defn- ar-from-g8 [form]
  (letfn [(strip [x] (cond (seq? x) (apply list (map strip (remove #{'x8s} x)))
                           (vector? x) (let [v (vec x) i (.indexOf v 'x8s)] (mapv strip (if (>= i 0) (into (subvec v 0 i) (subvec v (+ i 3))) v)))
                           (symbol? x) (let [n (name x)]
                                         (cond (= n "g8") 'ar
                                               (str/starts-with? n "g8-") (symbol (str "ar-" (subs n 3)))
                                               (str/ends-with? n "-g8") (symbol (str (subs n 0 (- (count n) 3)) "-ar"))
                                               :else x))
                           :else x))]
    (strip form)))
(doseq [o '[t-take-inv inv-arm-park t17-inv inv-await-post inv-await-raw t6-inv]]
  (let [{:keys [deps form]} (get @(:overrides spindel.v2.i8/G8) o)]
    (override! AR o deps (ar-from-g8 form))))

;; ---- new runs of a task: no computation has the task's id
(a/theorem ar-k-newrun-free [n :- Nat, n2 :- Nat, cs :- (List CompRow), rs :- (List RunRow), q :- RunRow]
  (=> (= (tbl-has comp-id (:of q) cs) false) (< (:of q) n2) (<= n n2) (= (ar-k n cs rs) true) (= (ar-k n2 cs (List.cons RunRow q rs)) true))
  (intros hc hl hle h)
  (have h2 := (ar-k-next n n2 cs rs hle h))
  (simp only [ar-k] at h2)
  (have ne := (has-false-ne CompRow comp-id (:of q) cs hc))
  (have g (forall [c :- CompRow] (=> (= (Bool.not (Nat.beq (comp-id c) (:of q))) true) (= (ar-c q c) true))))
  (intros c hcc) (simp only [comp-id] at hcc) (simp only [ar-c hcc Bool.true_or])
  (have t (= (tbl-all (ar-c q) cs) true)) (exact (tbl-all-mono CompRow _ _ g cs ne))
  (have b (= (Nat.blt (:of q) n2) true)) (exact (gd-blt-of _ _ hl))
  (have o (= (ar-one n2 cs q) true)) (simp only [ar-one b t Bool.and_self Bool.or_true])
  (simp only [ar-k tbl-all o h2 Bool.and_self]))
(override! AR 'inv-add-run-scope '[]
  '(a/theorem ar-add-run-scope [w :- World, of :- Nat, ep :- Nat, parent :- Nat, ei :- Nat]
     (=> (= (tbl-has comp-id of (:comps w)) false) (< of (:next-id w)) (= (ar w) true) (= (ar (add-run-scope w of ep parent ei)) true))
     (intros hc hl h)
     (have r0 := (ar-rest-of w h)) (simp only [ar-rest] at r0)
     (have l2 (< of (+ (+ (:next-id w) 1) 1))) (omega)
     (have l3 (<= (:next-id w) (+ (+ (:next-id w) 1) 1))) (omega)
     (have rr (= (ar-rest (add-run-scope w of ep parent ei)) true))
     (show (= (ar-k (+ (+ (:next-id w) 1) 1) (:comps w) (List.cons RunRow (new-run-row (:next-id w) of ep (+ (:next-id w) 1) ei) (:runs w))) true))
     (exact (ar-k-newrun-free _ _ _ _ (new-run-row (:next-id w) of ep (+ (:next-id w) 1) ei) hc l2 l3 r0))
     (exact (ar-intro _ (inv-add-run-scope w of ep parent ei (ar-sample w h)) rr))))
(a/theorem ar-has-next [w :- World] (=> (= (inv-sample w) true) (= (tbl-has comp-id (:next-id w) (:comps w)) false))
  (intro hs)
  (cases hb (tbl-has comp-id (:next-id w) (:comps w)))
  (case [false] (rfl))
  (case [true] (have z := (comp-below w (:next-id w) hs hb)) (omega)))
(override! AR 'inv-spawn-rows '[inv-add-run-scope]
  '(a/theorem ar-spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat)]
     (=> (= (ar w) true) (= (ar (spawn-rows w owner inputs)) true))
     (intro h)
     (have hc := (ar-has-next w (ar-sample w h)))
     (have hl (< (:next-id w) (:next-id (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs)))))) (show (< (:next-id w) (+ (:next-id w) 1))) (omega)
     (simp only [spawn-rows])
     (exact (ar-add-run-scope (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs)))
              (:next-id w) 0 (task-scope-parent w owner) 0 hc hl
              (ar-task-ins-fresh w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs) (rfl) h)))))

;; ---- T5/T11: C has no alive run; the new run becomes C.run
(a/theorem ar-cs-own [cid :- Nat, rid :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                      hrun :- (forall [c :- CompRow] (= (:run (f c)) rid)), q :- RunRow, cs :- (List CompRow)]
  (=> (= (:id q) rid) (= (:of q) cid) (= (tbl-all (ar-c q) (tbl-upd comp-id cid f cs)) true))
  (induction cs)
  (case [nil] (intros e1 e2) (simp only [tbl-upd tbl-all]))
  (case [cons hd t ih]
    (intros e1 e2)
    (cases hx (Nat.beq (comp-id hd) cid))
    (case [true]
      (have a1 (= (ar-c q (f hd)) true)) (simp only [ar-c (hrun hd) e1 Nat.beq_refl Bool.or_true])
      (simp only [tbl-upd hx tbl-all a1 (ih e1 e2) Bool.and_self]))
    (case [false]
      (have hx2 (= (Nat.beq (:id hd) (:of q)) false)) (rw [e2]) (exact hx)
      (have a1 (= (ar-c q hd) true)) (simp only [ar-c hx2 Bool.not_false Bool.true_or])
      (simp only [tbl-upd hx tbl-all a1 (ih e1 e2) Bool.and_self]))))
(a/theorem ar-k-newrun-own [n :- Nat, n2 :- Nat, cid :- Nat, rid :- Nat, f :- (=> CompRow CompRow),
                            hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                            hrun :- (forall [c :- CompRow] (= (:run (f c)) rid)),
                            cs :- (List CompRow), rs :- (List RunRow), q :- RunRow]
  (=> (= (:id q) rid) (= (:of q) cid) (< cid n2) (<= n n2) (= (tbl-all (not-alive-of cid) rs) true) (= (ar-k n cs rs) true)
      (= (ar-k n2 (tbl-upd comp-id cid f cs) (List.cons RunRow q rs)) true))
  (intros e1 e2 hl hle hn h)
  (have h1 := (ar-k-next n n2 _ rs hle (ar-k-clear n cid f hid cs rs hn h)))
  (simp only [ar-k] at h1)
  (have t := (ar-cs-own cid rid f hid hrun q cs e1 e2))
  (have b (= (Nat.blt (:of q) n2) true)) (rw [e2]) (exact (gd-blt-of _ _ hl))
  (have o (= (ar-one n2 (tbl-upd comp-id cid f cs) q) true)) (simp only [ar-one b t Bool.and_self Bool.or_true])
  (simp only [ar-k tbl-all o h1 Bool.and_self]))
(a/theorem ar-mem-lt [w :- World, c :- CompRow] (=> (= (inv-sample w) true) (List.Mem c (:comps w)) (< (:id c) (:next-id w)))
  (intros hs mc) (exact (comp-below w (:id c) hs (comp-mem-has w c mc))))
(a/theorem ar-start-raw-x [w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (tbl-all (not-alive-of (:id c)) (:runs w)) true) (= (ar w) true) (= (ar (start-raw w c)) true))
  (intros mc hn h)
  (have hs := (ar-sample w h))
  (have r0 := (ar-rest-of w h)) (simp only [ar-rest] at r0)
  (have z := (ar-mem-lt w c hs mc))
  (have l2 (< (:id c) (+ (+ (:next-id w) 1) 1))) (omega)
  (have l3 (<= (:next-id w) (+ (+ (:next-id w) 1) 1))) (omega)
  (have rr (= (ar-rest (start-raw w c)) true))
  (show (= (ar-k (+ (+ (:next-id w) 1) 1) (tbl-upd comp-id (:id c) (comp-start-row (:next-id w)) (:comps w))
                 (List.cons RunRow (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0) (:runs w))) true))
  (exact (ar-k-newrun-own _ _ (:id c) (:next-id w) (comp-start-row (:next-id w)) (comp-start-row-id (:next-id w))
           (fn [x :- CompRow] (Eq.refl (:next-id w))) _ _ (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0)
           (rfl) (rfl) l2 l3 hn r0))
  (exact (ar-intro _ (inv-start-raw w c hs) rr)))
(a/theorem ar-new-run-of-x [w :- World, c :- CompRow, ei :- Nat]
  (=> (= (comp-has w (:id c)) true) (= (tbl-all (not-alive-of (:id c)) (:runs w)) true) (= (ar w) true) (= (ar (new-run-of w c ei)) true))
  (intros hc hn h)
  (have hs := (ar-sample w h))
  (have r0 := (ar-rest-of w h)) (simp only [ar-rest] at r0)
  (have z := (comp-below w (:id c) hs hc))
  (have l2 (< (:id c) (+ (+ (:next-id w) 1) 1))) (omega)
  (have l3 (<= (:next-id w) (+ (+ (:next-id w) 1) 1))) (omega)
  (have rr (= (ar-rest (new-run-of w c ei)) true))
  (show (= (ar-k (+ (+ (:next-id w) 1) 1) (tbl-upd comp-id (:id c) (comp-set-run (:next-id w)) (:comps w))
                 (List.cons RunRow (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w))) true))
  (exact (ar-k-newrun-own _ _ (:id c) (:next-id w) (comp-set-run (:next-id w)) (comp-set-run-id (:next-id w))
           (fn [x :- CompRow] (Eq.refl (:next-id w))) _ _ (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei)
           (rfl) (rfl) l2 l3 hn r0))
  (exact (ar-intro _ (inv-new-run-of w c ei hs) rr)))

;; T5: a startable computation has no alive run (AR; g7's a7 for an idle one; run ids are not 0)
(a/theorem ar-startable-none [w :- World, c :- CompRow]
  (=> (= (g7 w) true) (= (ar w) true) (List.Mem c (:comps w)) (= (startable w c) true)
      (= (tbl-all (not-alive-of (:id c)) (:runs w)) true))
  (intros hg h mc hst)
  (have hs := (ar-sample w h))
  (apply (all-of-mem RunRow (not-alive-of (:id c)) (:runs w)))
  (intros q mq)
  (cases ha (run-alive q))
  (case [false] (simp only [not-alive-of ha Bool.not_false Bool.true_or]))
  (case [true]
    (cases ho (Nat.beq (:of q) (:id c)))
    (case [false] (simp only [not-alive-of ho Bool.not_false Bool.or_true]))
    (case [true]
      (have eo (= (:id c) (:of q))) (exact (Eq.symm (Nat.eq_of_beq_eq_true ho)))
      (have e1 := (ar-use w q c h mq ha mc eo))
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
          (have d := (ar-dead-id w r q hs (And.left p) dr mq (Eq.trans (Eq.symm e1) (Eq.symm (And.right p)))))
          (rw [ha] at d) (cases d)))
      (case [inr B]
        (cases B)
        (case [inl B1]
          (have hi := (And.left B1))
          (have p := (g7k-parts _ _ _ (g7-rest-of w hg)))
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
(override! AR 'inv-start-raw '[]
  '(a/theorem ar-start-raw [w :- World, c :- CompRow]
     (=> (= (g7 w) true) (List.Mem c (:comps w)) (= (startable w c) true) (= (ar w) true) (= (ar (start-raw w c)) true))
     (intros hg mc hst h) (exact (ar-start-raw-x w c mc (ar-startable-none w c hg h mc hst) h))))
(override! AR 't5-inv '[inv-start-raw]
  '(a/theorem t5-ar [w :- World, cid :- Nat, fresh :- Nat]
     (=> (= (g7 w) true) (= (ar w) true) (= (ar (:world (t5-start w cid fresh))) true))
     (intros hg h)
     (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
     (simp only [t5-start hc refuse]) (exact h)
     (cases hg2 (Bool.and (Nat.beq fresh (:next-id w)) (startable w c)))
     (simp only [t5-start hc hg2 refuse]) (exact h)
     (have hst (= (startable w c) true)) (simp only [Bool.and_eq_true] at hg2) (exact (And.right hg2))
     (simp only [t5-start hc hg2 accept]) (exact (ar-start-raw w c hg (tbl-find-mem CompRow comp-id cid c (:comps w) hc) hst h))))

;; T11: the predecessor cancel kills C's only alive run (idle's KDB), the cut and the entry keep the runs
(a/theorem ar-none-find-none [w :- World, c :- CompRow]
  (=> (= (ar w) true) (List.Mem c (:comps w)) (= (run-find w (:run c)) (Option.none RunRow)) (= (tbl-all (not-alive-of (:id c)) (:runs w)) true))
  (intros h mc hf)
  (apply (all-of-mem RunRow (not-alive-of (:id c)) (:runs w)))
  (intros q mq)
  (cases ha (run-alive q))
  (case [false] (simp only [not-alive-of ha Bool.not_false Bool.true_or]))
  (case [true]
    (cases ho (Nat.beq (:of q) (:id c)))
    (case [false] (simp only [not-alive-of ho Bool.not_false Bool.or_true]))
    (case [true]
      (have e1 := (ar-use w q c h mq ha mc (Eq.symm (Nat.eq_of_beq_eq_true ho))))
      (have z := (tbl-find-none-has RunRow run-id (:run c) (:runs w) hf))
      (have z2 := (mem-ids-has RunRow run-id q (:runs w) mq)) (rw [nat-mem-ids] at z2)
      (have z3 (= (tbl-has run-id (:run c) (:runs w)) true)) (rw [e1]) (exact z2)
      (rw [z] at z3) (cases z3))))
(a/theorem ar-kdb-init [w :- World, c :- CompRow, r :- RunRow]
  (=> (= (ar w) true) (List.Mem c (:comps w)) (= (:id r) (:run c))
      (= (kdb (:id c) (List.cons Nat (:id r) (List.nil Nat)) (List.nil Nat) w) true))
  (intros h mc er)
  (have hs := (ar-sample w h))
  (apply (kdb-intro _ _ _ w hs))
  (simp only [kdb-rest])
  (apply (all-of-mem RunRow (kd-one (:id c) (List.cons Nat (:id r) (List.nil Nat)) (List.nil Nat)) (:runs w)))
  (intros q mq)
  (cases ha (run-alive q))
  (case [false] (simp only [kd-one ha reach-mem Bool.not_false Bool.true_or Bool.and_self]))
  (case [true]
    (cases ho (Nat.beq (:of q) (:id c)))
    (case [false] (simp only [kd-one ha ho reach-mem Bool.not_false Bool.not_true Bool.false_or Bool.true_or Bool.and_self]))
    (case [true]
      (have e1 := (ar-use w q c h mq ha mc (Eq.symm (Nat.eq_of_beq_eq_true ho))))
      (have m (= (reach-mem (:id q) (List.cons Nat (:id r) (List.nil Nat))) true))
      (have i (= (Nat.beq (:id q) (:id r)) true)) (rw [er (Eq.symm e1)]) (exact (Nat.beq_refl _))
      (simp only [reach-mem-cons i Bool.true_or])
      (simp only [kd-one ha ho m reach-mem Bool.not_false Bool.not_true Bool.false_or Bool.true_or Bool.or_true Bool.and_self]))))
(a/theorem ar-cancel-pred-none [w :- World, c :- CompRow]
  (=> (= (acts-alive w) true) (= (ar w) true) (List.Mem c (:comps w))
      (= (tbl-all (not-alive-of (:id c)) (:runs (cancel-pred w c))) true))
  (intros haa h mc)
  (have hs := (ar-sample w h))
  (cases hf (run-find w (:run c))) (case' [some r]) (case' [none])
  (simp only [cancel-pred hf]) (exact (ar-none-find-none w c h mc hf))
  (have p := (find-run-mem w (:run c) r hf))
  (cases ha (run-alive r))
  (simp only [cancel-pred hf ha]) (exact (ar-none-of-dead w r c h (And.left p) ha mc (Eq.symm (And.right p))))
  (simp only [cancel-pred hf ha run-cascade cascade-run])
  (have k0 := (ar-kdb-init w c r h mc (And.right p)))
  (have cv (= (tbl-all (cov-one (List.nil Nat) (List.cons Job (Job.jcancel (:id r) true) (List.nil Job))) (List.cons Nat (:id r) (List.nil Nat))) true))
  (simp only [tbl-all cov-one tbl-any job-cancels reach-mem Nat.beq_refl Bool.true_or Bool.false_or Bool.and_self])
  (have cd := (casc-done-ok w (List.cons Job (Job.jcancel (:id r) true) (List.nil Job)) hs haa))
  (simp only [casc-done cascade-run] at cd)
  (exact (casc-kill (:id c) _ _ w _ (List.nil Nat) k0 cv cd)))
(a/theorem ar-runs-cut [w :- World, c :- Nat, has :- Bool, cut :- Nat, cid :- Nat] (= (:runs (cut-suffix w c has cut cid)) (:runs w)) (rfl))
(a/theorem ar-runs-consume [w :- World, e :- EdgeRow] (= (:runs (consume-entry w e)) (:runs w))
  (cases hf (deb-final w (:debtor e)))
  (case [true] (simp only [consume-entry hf]) (exact (runs-remove-edge w (:id e))))
  (case [false] (cases hc (Nat.beq (:cont e) cont-restart)) (all_goals (simp only [consume-entry hf hc edge-upd set-edges]))))
(override! AR 'inv-dispatch-raw '[inv-cancel-pred inv-cut-suffix inv-consume-entry]
  '(a/theorem ar-dispatch-raw [w :- World, c :- CompRow]
     (=> (= (acts-alive w) true) (List.Mem c (:comps w)) (= (ar w) true) (= (ar (dispatch-raw w c)) true))
     (intros haa mc h)
     (have hs := (ar-sample w h))
     (have h1 := (ar-cancel-pred w c h))
     (have n1 := (ar-cancel-pred-none w c haa h mc))
     (have c1 := (ch-cancel-pred (:id c) w c (ch-intro (:id c) w hs (comp-mem-has w c mc))))
     (cases he (entry-edge w (:id c)))
     (case [none]
       (simp only [dispatch-raw he])
       (have c2 := (ch-cut-suffix (:id c) _ (:id c) false 0 0 c1))
       (have n2 (= (tbl-all (not-alive-of (:id c)) (:runs (cut-suffix (cancel-pred w c) (:id c) false 0 0))) true)) (rw [ar-runs-cut]) (exact n1)
       (exact (ar-new-run-of-x _ c 0 (ch-rest-of (:id c) _ c2) n2 (ar-cut-suffix _ (:id c) false 0 0 h1))))
     (case [some e]
       (simp only [dispatch-raw he])
       (have c2 := (ch-consume-entry (:id c) _ e (ch-cut-suffix (:id c) _ (:id c) true (:at e) (:id e) c1)))
       (have n2 (= (tbl-all (not-alive-of (:id c)) (:runs (consume-entry (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e))) true))
       (rw [ar-runs-consume ar-runs-cut]) (exact n1)
       (exact (ar-new-run-of-x _ c (entry-ei e) (ch-rest-of (:id c) _ c2) n2
                (ar-consume-entry _ e (ar-cut-suffix _ (:id c) true (:at e) (:id e) h1)))))))
(override! AR 't11-inv '[inv-dispatch-raw]
  '(a/theorem t11-ar [w :- World, cid :- Nat, fresh :- Nat]
     (=> (= (ga w) true) (= (ar w) true) (= (ar (:world (t11-dispatch w cid fresh))) true))
     (intros hga h)
     (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
     (simp only [t11-dispatch hc refuse]) (exact h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))))
     (simp only [t11-dispatch hc hg refuse]) (exact h)
     (simp only [t11-dispatch hc hg accept])
     (exact (ar-dispatch-raw w c (ga-acts-alive w hga) (tbl-find-mem CompRow comp-id cid c (:comps w) hc) h))))

;; ---- raw0 / raw0g / raw: g7 (T5) and ga (T11's cascade) threaded from the step's input
(def ^:private ar-calls '{(t5-inv w _ _ h) (t5-inv w _ _ hg7 h)
                          (t11-inv w _ _ h) (t11-inv w _ _ hga h)})
(defn- ar-add-hyps [form calls]
  (let [[hd nm binders stmt & proof] form
        stmt2 (apply list '=> '(= (g7 w) true) '(= (ga w) true) (rest stmt))
        proof2 (map (fn [t] (if (= t '(intro h)) '(intros hg7 hga h) t)) proof)]
    (subst-forms #(contains? calls %) calls (apply list hd nm binders stmt2 proof2))))
(patch! AR 'raw0-inv (fn [form] (ar-add-hyps (ar-patch form) ar-calls)))
(patch! AR 'raw0g-inv (fn [form] (ar-add-hyps (ar-patch form) '{(raw0-inv w it h) (raw0-inv w it hg7 hga h)})))
(patch! AR 'raw-inv (fn [form] (ar-add-hyps (ar-patch form) '{(raw0g-inv w it h) (raw0g-inv w it hg7 hga h)})))

;; ---- demote: its cascade kills every alive run of C (idle's demote-dead), then C.run := 0
(override! AR 'inv-demote-finish '[inv-drop-edges inv-comp-del-unref]
  '(a/theorem ar-demote-finish [w :- World, cid :- Nat, vs :- (List Valid)]
     (=> (= (tbl-all (not-alive-of cid) (:runs w)) true) (= (ar w) true) (= (ar (demote-finish w cid vs)) true))
     (intros hna h)
     (cases hf (comp-find w cid)) (case' [some c]) (case' [none])
     (simp only [demote-finish hf]) (exact h)
     (cases hk (demote-keep w c))
     (simp only [demote-finish hf hk])
     (exact (ar-comp-del-unref _ cid (drop-edges-avoids w cid) (ar-drop-edges w (edge-avoids cid) h)))
     (simp only [demote-finish hf hk])
     (have r0 := (ar-rest-of w h)) (simp only [ar-rest] at r0)
     (have r1 (= (ar-rest (comp-upd w cid (comp-make-idle vs))) true))
     (simp only [ar-rest comp-upd set-comps])
     (exact (ar-k-clear _ cid (comp-make-idle vs) (comp-make-idle-id vs) _ _ hna r0))
     (exact (ar-intro _ (inv-comp-upd w cid (comp-make-idle vs) (comp-make-idle-id vs) (comp-make-idle-pending vs) (ar-sample w h)) r1))))
(override! AR 'inv-demote '[inv-run-cascade inv-demote-epoch inv-drop-edges inv-demote-finish]
  '(a/theorem ar-demote [w :- World, cid :- Nat]
     (=> (= (acts-alive w) true) (= (ar w) true) (= (ar (demote w cid)) true))
     (intros ha h)
     (cases hf (comp-find w cid)) (case' [some c]) (case' [none])
     (simp only [demote hf]) (exact h)
     (cases hi (:idle c))
     (simp only [demote hf hi demote-edges])
     (have e (= (:id c) cid)) (exact (tbl-find-id CompRow comp-id cid c (:comps w) hf))
     (have na := (demote-dead w c (ar-sample w h) ha))
     (rw [e] at na)
     (have g1 := (ar-run-cascade w (cancel-jobs (demote-cancels w c)) h))
     (have g2 := (ar-demote-epoch _ cid (demote-cur w c) g1))
     (have g3 := (ar-drop-edges _ (not-dep-of cid) g2))
     (have na3 (= (tbl-all (not-alive-of cid) (:runs (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) cid (demote-cur w c)) (not-dep-of cid)))) true))
     (simp only [drop-edges set-comps set-edges runs-demote-epoch]) (exact na)
     (exact (ar-demote-finish _ cid _ na3 g3))
     (simp only [demote hf hi]) (exact h)))
(lcopy! AR 'inv-demote)
(a/theorem ar-demote-fold [a :- Nat, k :- Nat, xs :- (List Nat)]
  (forall [w :- World] (=> (= (bn a k w) true) (= (ar w) true) (= (ar (nat-fold demote w xs)) true)))
  (induction xs)
  (case [nil] (intros w hb h) (simp only [nat-fold]) (exact h))
  (case [cons hd t ih]
    (intros w hb h) (simp only [nat-fold])
    (exact (ih (demote w hd) (bn-demote a k w hd hb) (ar-demote w hd (And.left (And.right (bn-parts a k w hb))) h)))))
(defn- ar-from-g7 [form]
  (walk/postwalk (fn [x] (if (symbol? x)
                           (let [n (name x)]
                             (cond (= n "g7") 'ar
                                   (str/starts-with? n "g7-") (symbol (str "ar-" (subs n 3)))
                                   :else x))
                           x))
                 form))
(doseq [o '[inv-norm-round inv-norm-loop inv-normalize]]
  (let [{:keys [deps form]} (get @(:overrides spindel.v2.idle/G7) o)]
    (override! AR o deps (ar-from-g7 form))))

;; ===========================================================================
;; Part E. The copy, Rule R, the step, the literal I10 computation part
;; ===========================================================================

(lcopy! AR 'raw-inv)
(lcopy! AR 'inv-normalize)

(a/theorem ar-rule-r-round [w :- World]
  (=> (= (acts-alive w) true) (= (ar w) true) (= (filter-safe (normalize w)) true) (= (ar (rule-r-round w)) true))
  (intros ha h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (ar-filter-world _ (keep-fn (normalize w)) (ar-normalize w ha h) hf)))
(a/theorem ar-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (acts-alive w0) true) (= (ar w0) true) (= (rr-safe fuel w0) true)
                            (= (ar (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 ha h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (ar-rule-r-round w0 ha h hs)))
  (case [cons x f ih]
    (intros w0 ha h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (ar-rule-r-round w0 ha h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false]
      (simp only [ho] at hs) (simp only [rr-loop ho])
      (exact (ih (rule-r-round w0) (acts-alive-round w0 (ar-sample w0 h) ha) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))
(a/theorem ar-rule-r [w :- World]
  (=> (= (acts-alive w) true) (= (ar w) true) (= (rule-r-safe w) true) (= (ar (rule-r w)) true))
  (intros ha h hs)
  (simp only [rule-r-safe] at hs) (simp only [rule-r])
  (exact (ar-rr-loop (rr-fuel w) w ha h hs)))

;; Theorem: AR is preserved by every step (hypotheses: g7, ga of the input, rule-r-safe of the raw world)
(a/theorem step-ar [w :- World, it :- Item]
  (=> (= (g7 w) true) (= (ga w) true) (= (ar w) true) (= (rule-r-safe (:world (raw w it))) true) (= (ar (:world (world-step w it))) true))
  (intros hg7 hga h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true]
    (have e2 := (step-accepted w it ha)) (rw [e2])
    (exact (ar-rule-r (:world (raw w it)) (raw-acts-alive w it hga) (raw-ar w it hg7 hga h) hs))))
(a/theorem ar-empty [] (= (ar empty-world) true) (rfl))

;; the literal reading (inv.clj `inv-i10-comp`)
(a/theorem ar-i10-comp [w :- World] (=> (= (ar w) true) (= (inv-i10-comp w) true))
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
      (have e := (ar-use w r c h mr ha mc ic))
      (simp only [comp-run-is ha hf e Nat.beq_refl Bool.not_true Bool.false_or]))))
