(ns spindel.v2.inv.tomb
  "C1 Q6: tombstones are dormant. A tombstone (`CompRow.tomb`, made by Rule R's demotion of a
  computation with neither a result nor a handle whose run is in cleanup, spec §3.2) is no
  computation of an alive run and no creditor of a dep edge. With it a normalized world keeps the
  creditor of every dep edge live (spindel.v2.inv.copier `filter-safe-of-refs`, premise `refs-untomb`).

    tombs-dormant y w   well-formed w, `tombs-dormant-keys-ok`: every alive run's computation and every dep edge's creditor is no
             tombstone (`ta-one`, `dep-untomb`), and neither is computation y (`untomb`); the bundle
             copy of the raw transition (`tombs-dormant-raw`), y the computation an await/track/reactivation
             adds a dep edge for. Only start (T5), dispatch (T11), reactivation and demand rows clear
             the flag (handle-new refuses a tombstone), only `comp-demote-row` sets it.
    gn w     tombs-dormant 0 w (no computation has id 0): the bundle copy of normalization (`gn-normalize`; the
             demotion makes its computation a tombstone only after its dep edges are gone and its runs
             are cancelled, `demote-dead`), the filter, and the step (`step-gn`).

  tombs-dormant is a part of the generic tree (spindel.v2.pres.tree; table in Part C)."
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
            [spindel.v2.progress.casc :refer :all]
            [spindel.v2.inv.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.pres.part :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.idle :refer :all]))

;; ===========================================================================
;; Part A. The rest part and the row-set lemmas
;; ===========================================================================

(a/defn ta-one [cs :- (List CompRow), r :- RunRow] Bool (Bool.or (Bool.not (run-alive r)) (untomb cs (:of r))))
(a/defn gtk [cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)] Bool
  (Bool.and (tbl-all (ta-one cs) rs) (tbl-all (dep-untomb cs) es)))
(a/defn tombs-dormant-keys-ok [y :- Nat, cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)] Bool
  (Bool.and (gtk cs rs es) (untomb cs y)))

(a/theorem gtk-parts [cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (gtk cs rs es) true) (And (= (tbl-all (ta-one cs) rs) true) (= (tbl-all (dep-untomb cs) es) true)))
  (intro h) (simp only [gtk Bool.and_eq_true] at h) (exact h))
(a/theorem gtk-intro [cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (tbl-all (ta-one cs) rs) true) (= (tbl-all (dep-untomb cs) es) true) (= (gtk cs rs es) true))
  (intros h1 h2) (simp only [gtk h1 h2 Bool.and_self]))
(a/theorem tombs-dormant-keys-ok-parts [y :- Nat, cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (tombs-dormant-keys-ok y cs rs es) true) (And (= (gtk cs rs es) true) (= (untomb cs y) true)))
  (intro h) (simp only [tombs-dormant-keys-ok Bool.and_eq_true] at h) (exact h))
(a/theorem tombs-dormant-keys-ok-intro [y :- Nat, cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (gtk cs rs es) true) (= (untomb cs y) true) (= (tombs-dormant-keys-ok y cs rs es) true))
  (intros h1 h2) (simp only [tombs-dormant-keys-ok h1 h2 Bool.and_self]))

;; ---- untomb under computation edits

;; a computation edit that never makes a row a tombstone (pointwise)
(a/defn no-entomb [f :- (=> CompRow CompRow), c :- CompRow] Bool (Bool.or (Bool.not (:tomb (f c))) (:tomb c)))

(a/theorem untomb-upd [x :- Nat, f :- (=> CompRow CompRow),
                       hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                       hn :- (forall [c :- CompRow] (= (no-entomb f c) true)), cs :- (List CompRow), y :- Nat]
  (=> (= (untomb cs y) true) (= (untomb (tbl-upd comp-id x f cs) y) true))
  (intro h) (simp only [untomb] at h) (simp only [untomb])
  (apply (tbl-all-upd CompRow comp-id x f (nt-if-id y) (nt-if-id y) _ _ cs h))
  (intros c hc hx)
  (have e (= (:id (f c)) (:id c))) (exact (hid c))
  (have s := (hn c))
  (cases hi (:tomb (f c)))
  (case [false] (simp only [nt-if-id hi Bool.not_false Bool.or_true]))
  (case [true]
    (simp only [no-entomb hi Bool.not_true Bool.false_or] at s)
    (simp only [nt-if-id s Bool.not_true Bool.or_false] at hc)
    (simp only [nt-if-id e hi hc Bool.not_true Bool.or_false]))
  (intros c hc hx) (exact hc))

;; a row edit that clears the flag: afterwards no row with id x is a tombstone
(a/theorem untomb-clear [x :- Nat, f :- (=> CompRow CompRow),
                         hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                         hw :- (forall [c :- CompRow] (= (:tomb (f c)) false)), cs :- (List CompRow)]
  (= (untomb (tbl-upd comp-id x f cs) x) true)
  (induction cs)
  (case [nil] (simp [untomb tbl-upd tbl-all]))
  (case [cons hd t ih]
    (simp only [untomb] at ih)
    (cases hx (Nat.beq (comp-id hd) x))
    (case [true] (simp only [untomb tbl-upd hx tbl-all ih nt-if-id (hw hd) Bool.not_false Bool.or_true Bool.and_self]))
    (case [false]
      (have e (= (Nat.beq (:id hd) x) false)) (exact hx)
      (simp only [untomb tbl-upd hx tbl-all ih nt-if-id e Bool.not_false Bool.true_or Bool.and_self]))))

(a/theorem untomb-del [x :- Nat, cs :- (List CompRow), y :- Nat]
  (=> (= (untomb cs y) true) (= (untomb (tbl-del comp-id x cs) y) true))
  (intro h) (simp only [untomb] at h) (simp only [untomb])
  (exact (tbl-all-del CompRow comp-id x (nt-if-id y) (nt-if-id y) (fn [c :- CompRow, hc :- (= (nt-if-id y c) true), hx :- (= (Nat.beq (comp-id c) x) false)] hc) cs h)))

(a/theorem untomb-keep [K :- (=> Nat Bool), cs :- (List CompRow), y :- Nat]
  (=> (= (untomb cs y) true) (= (untomb (tbl-keep K comp-id cs) y) true))
  (intro h) (simp only [untomb] at h) (simp only [untomb])
  (exact (tbl-all-keep-same CompRow K comp-id (nt-if-id y) cs h)))

(a/theorem untomb-ins [r :- CompRow, cs :- (List CompRow), y :- Nat]
  (=> (= (:tomb r) false) (= (untomb cs y) true) (= (untomb (tbl-ins r cs) y) true))
  (intros hr h) (simp only [untomb] at h) (simp only [untomb tbl-ins tbl-all nt-if-id hr h Bool.not_false Bool.or_true Bool.and_self]))

(a/theorem untomb-absent [cs :- (List CompRow), y :- Nat]
  (=> (= (tbl-has comp-id y cs) false) (= (untomb cs y) true))
  (induction cs)
  (case [nil] (intro h) (simp [untomb tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (cases e (Nat.beq (comp-id hd) y))
    (case [true] (simp [tbl-has e] at h))
    (case [false]
      (simp only [tbl-has e] at h)
      (have h1 := (ih h))
      (simp only [untomb] at h1)
      (have e2 (= (Nat.beq (:id hd) y) false)) (exact e)
      (simp only [untomb tbl-all nt-if-id e2 h1 Bool.not_false Bool.true_or Bool.and_self]))))

(a/theorem untomb-resync [es :- (List EdgeRow), cs :- (List CompRow), y :- Nat]
  (= (untomb (comps-resync es cs) y) (untomb cs y))
  (induction cs)
  (case [nil] (simp only [comps-resync]))
  (case [cons hd t ih]
    (simp only [untomb] at ih)
    (simp only [untomb comps-resync tbl-all ih nt-if-id comp-resync comp-set-pending])))

;; the computation x is no tombstone: a member row with id x has tomb = false
(a/theorem untomb-mem [cs :- (List CompRow), c :- CompRow, x :- Nat]
  (=> (= (untomb cs x) true) (List.Mem c cs) (= (Nat.beq (:id c) x) true) (= (:tomb c) false))
  (intros h hm hx)
  (simp only [untomb] at h)
  (have n := (tbl-all-mem CompRow (nt-if-id x) c cs h hm))
  (simp only [nt-if-id hx Bool.not_true Bool.false_or] at n)
  (exact (bnot-true _ n)))

;; ---- the rest part under row-set changes

(a/theorem gtk-comp-sub [cs :- (List CompRow), cs2 :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow),
                         ha :- (forall [y :- Nat] (=> (= (untomb cs y) true) (= (untomb cs2 y) true)))]
  (=> (= (gtk cs rs es) true) (= (gtk cs2 rs es) true))
  (intro h)
  (have p := (gtk-parts cs rs es h))
  (have h1 (= (tbl-all (ta-one cs2) rs) true))
  (apply (tbl-all-mono RunRow (ta-one cs) (ta-one cs2) _ rs (And.left p)))
  (intros r hr)
  (cases hl (run-alive r))
  (case [false] (simp only [ta-one hl Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ta-one hl Bool.not_true Bool.false_or] at hr)
    (simp only [ta-one hl Bool.not_true Bool.false_or])
    (exact (ha (:of r) hr)))
  (have h2 (= (tbl-all (dep-untomb cs2) es) true))
  (apply (tbl-all-mono EdgeRow (dep-untomb cs) (dep-untomb cs2) _ es (And.right p)))
  (intros e he)
  (cases hd (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dep-untomb hd Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dep-untomb hd Bool.not_true Bool.false_or] at he)
    (simp only [dep-untomb hd Bool.not_true Bool.false_or])
    (exact (ha (:creditor e) he)))
  (exact (gtk-intro _ _ _ h1 h2)))

(a/theorem tombs-dormant-keys-ok-comp-sub [y :- Nat, cs :- (List CompRow), cs2 :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow),
                         ha :- (forall [z :- Nat] (=> (= (untomb cs z) true) (= (untomb cs2 z) true)))]
  (=> (= (tombs-dormant-keys-ok y cs rs es) true) (= (tombs-dormant-keys-ok y cs2 rs es) true))
  (intro h)
  (have p := (tombs-dormant-keys-ok-parts y cs rs es h))
  (exact (tombs-dormant-keys-ok-intro y _ _ _ (gtk-comp-sub cs cs2 rs es ha (And.left p)) (ha y (And.right p)))))

(a/theorem tombs-dormant-keys-ok-run-sub [y :- Nat, cs :- (List CompRow), rs :- (List RunRow), rs2 :- (List RunRow), es :- (List EdgeRow),
                        hs :- (forall [P :- (=> RunRow Bool)] (=> (= (tbl-all P rs) true) (= (tbl-all P rs2) true)))]
  (=> (= (tombs-dormant-keys-ok y cs rs es) true) (= (tombs-dormant-keys-ok y cs rs2 es) true))
  (intro h)
  (have p := (tombs-dormant-keys-ok-parts y cs rs es h))
  (have q := (gtk-parts cs rs es (And.left p)))
  (exact (tombs-dormant-keys-ok-intro y _ _ _ (gtk-intro _ _ _ (hs (ta-one cs) (And.left q)) (And.right q)) (And.right p))))

(a/theorem tombs-dormant-keys-ok-edge-sub [y :- Nat, cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow), es2 :- (List EdgeRow),
                         hs :- (forall [P :- (=> EdgeRow Bool)] (=> (= (tbl-all P es) true) (= (tbl-all P es2) true)))]
  (=> (= (tombs-dormant-keys-ok y cs rs es) true) (= (tombs-dormant-keys-ok y cs rs es2) true))
  (intro h)
  (have p := (tombs-dormant-keys-ok-parts y cs rs es h))
  (have q := (gtk-parts cs rs es (And.left p)))
  (exact (tombs-dormant-keys-ok-intro y _ _ _ (gtk-intro _ _ _ (And.left q) (hs (dep-untomb cs) (And.right q))) (And.right p))))

(a/theorem tombs-dormant-keys-ok-comp-upd [y :- Nat, x :- Nat, f :- (=> CompRow CompRow),
                         hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                         hn :- (forall [c :- CompRow] (= (no-entomb f c) true)),
                         cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (tombs-dormant-keys-ok y cs rs es) true) (= (tombs-dormant-keys-ok y (tbl-upd comp-id x f cs) rs es) true))
  (intro h) (exact (tombs-dormant-keys-ok-comp-sub y cs _ rs es (fn [z :- Nat, hz :- (= (untomb cs z) true)] (untomb-upd x f hid hn cs z hz)) h)))

(a/theorem tombs-dormant-keys-ok-run-upd [y :- Nat, x :- Nat, f :- (=> RunRow RunRow),
                        hd :- (forall [r :- RunRow] (= (run-down f r) true)),
                        cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (tombs-dormant-keys-ok y cs rs es) true) (= (tombs-dormant-keys-ok y cs (tbl-upd run-id x f rs) es) true))
  (intro h)
  (have p := (tombs-dormant-keys-ok-parts y cs rs es h))
  (have q := (gtk-parts cs rs es (And.left p)))
  (have h1 (= (tbl-all (ta-one cs) (tbl-upd run-id x f rs)) true))
  (apply (tbl-all-upd RunRow run-id x f (ta-one cs) (ta-one cs) _ _ rs (And.left q)))
  (intros r hr hx)
  (have d := (hd r))
  (cases ha (run-alive (f r)))
  (case [false] (simp only [ta-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [run-down ha Bool.not_true Bool.false_or Bool.and_eq_true] at d)
    (have eo (= (:of (f r)) (:of r))) (exact (Nat.eq_of_beq_eq_true (And.right d)))
    (simp only [ta-one (And.left d) Bool.not_true Bool.false_or] at hr)
    (simp only [ta-one ha eo hr Bool.not_true Bool.false_or]))
  (intros r hr hx) (exact hr)
  (exact (tombs-dormant-keys-ok-intro y _ _ _ (gtk-intro _ _ _ h1 (And.right q)) (And.right p))))

(a/theorem tombs-dormant-keys-ok-edge-upd [y :- Nat, x :- Nat, f :- (=> EdgeRow EdgeRow),
                         hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                         hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                         cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (tombs-dormant-keys-ok y cs rs es) true) (= (tombs-dormant-keys-ok y cs rs (tbl-upd edge-id x f es)) true))
  (intro h)
  (have p := (tombs-dormant-keys-ok-parts y cs rs es h))
  (have q := (gtk-parts cs rs es (And.left p)))
  (have h2 (= (tbl-all (dep-untomb cs) (tbl-upd edge-id x f es)) true))
  (apply (tbl-all-upd EdgeRow edge-id x f (dep-untomb cs) (dep-untomb cs) _ _ es (And.right q)))
  (intros e he hx) (simp only [dep-untomb (hk e) (hc e)]) (exact he)
  (intros e he hx) (exact he)
  (exact (tombs-dormant-keys-ok-intro y _ _ _ (gtk-intro _ _ _ (And.left q) h2) (And.right p))))

;; ---- key forms (frames provable by rfl)

(a/structure CKT [] (id Nat) (tomb Bool))
(a/defn ckt [c :- CompRow] CKT (CKT.mk (:id c) (:tomb c)))

(a/theorem ckt-ne [f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (ckt (f c)) (ckt c))), c :- CompRow]
  (= (no-entomb f c) true)
  (have e (= (:tomb (f c)) (:tomb c))) (exact (congrArg (fn [k :- CKT] (:tomb k)) (hk c)))
  (cases hi (:tomb c))
  (all_goals (simp only [no-entomb e hi Bool.not_true Bool.not_false Bool.or_true Bool.true_or])))
(a/theorem clear-ne [f :- (=> CompRow CompRow), hw :- (forall [c :- CompRow] (= (:tomb (f c)) false)), c :- CompRow]
  (= (no-entomb f c) true)
  (simp only [no-entomb (hw c) Bool.not_false Bool.true_or]))

;; ===========================================================================
;; Part B. The bundle tombs-dormant and its primitives
;; ===========================================================================

(a/defn tombs-dormant-rest [y :- Nat, w :- World] Bool (tombs-dormant-keys-ok y (:comps w) (:runs w) (:edges w)))
(a/defn tombs-dormant [y :- Nat, w :- World] Bool (Bool.and (well-formed w) (tombs-dormant-rest y w)))

(a/theorem tombs-dormant-well-formed [y :- Nat, w :- World] (=> (= (tombs-dormant y w) true) (= (well-formed w) true))
  (intro h) (simp only [tombs-dormant Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem tombs-dormant-rest-of [y :- Nat, w :- World] (=> (= (tombs-dormant y w) true) (= (tombs-dormant-rest y w) true))
  (intro h) (simp only [tombs-dormant Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem tombs-dormant-intro [y :- Nat, w :- World] (=> (= (well-formed w) true) (= (tombs-dormant-rest y w) true) (= (tombs-dormant y w) true))
  (intros h1 h2) (simp only [tombs-dormant h1 h2 Bool.and_self]))
(a/theorem tombs-dormant-parts [y :- Nat, w :- World]
  (=> (= (tombs-dormant y w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (tombs-dormant-well-formed y w h))))
(a/theorem tombs-dormant-untomb [y :- Nat, w :- World] (=> (= (tombs-dormant y w) true) (= (untomb (:comps w) y) true))
  (intro h) (exact (And.right (tombs-dormant-keys-ok-parts y _ _ _ (tombs-dormant-rest-of y w h)))))
(a/theorem tombs-dormant-gtk [y :- Nat, w :- World] (=> (= (tombs-dormant y w) true) (= (gtk (:comps w) (:runs w) (:edges w)) true))
  (intro h) (exact (And.left (tombs-dormant-keys-ok-parts y _ _ _ (tombs-dormant-rest-of y w h)))))
;; switch the tracked computation
(a/theorem tombs-dormant-switch [y :- Nat, z :- Nat, w :- World]
  (=> (= (tombs-dormant y w) true) (= (untomb (:comps w) z) true) (= (tombs-dormant z w) true))
  (intros h hz) (exact (tombs-dormant-intro z w (tombs-dormant-well-formed y w h) (tombs-dormant-keys-ok-intro z _ _ _ (tombs-dormant-gtk y w h) hz))))

(a/theorem tombs-dormant-comp-upd-m [y :- Nat, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                          hn :- (forall [c :- CompRow] (= (no-entomb f c) true))]
  (=> (= (tombs-dormant y w) true) (= (tombs-dormant y (comp-upd w x f)) true))
  (intro h)
  (exact (tombs-dormant-intro y _ (well-formed-comp-upd w x f hid hp (tombs-dormant-well-formed y w h))
           (tombs-dormant-keys-ok-comp-upd y x f hid hn (:comps w) (:runs w) (:edges w) (tombs-dormant-rest-of y w h)))))
(a/theorem tombs-dormant-comp-upd [y :- Nat, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hk :- (forall [c :- CompRow] (= (ckt (f c)) (ckt c)))]
  (=> (= (tombs-dormant y w) true) (= (tombs-dormant y (comp-upd w x f)) true))
  (exact (tombs-dormant-comp-upd-m y w x f hid hp (ckt-ne f hk))))

(a/theorem tombs-dormant-run-upd-m [y :- Nat, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                         hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         hd :- (forall [r :- RunRow] (= (run-down f r) true))]
  (=> (= (tombs-dormant y w) true) (= (tombs-dormant y (run-upd w x f)) true))
  (intro h)
  (exact (tombs-dormant-intro y _ (well-formed-run-upd w x f hf (tombs-dormant-well-formed y w h))
           (tombs-dormant-keys-ok-run-upd y x f hd (:comps w) (:runs w) (:edges w) (tombs-dormant-rest-of y w h)))))
(a/theorem tombs-dormant-run-upd [y :- Nat, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (i7-idle-run-key (f r)) (i7-idle-run-key r)))]
  (=> (= (tombs-dormant y w) true) (= (tombs-dormant y (run-upd w x f)) true))
  (exact (tombs-dormant-run-upd-m y w x f hf (i7-idle-run-key-down f hk))))

(a/theorem tombs-dormant-comp-ins-fresh [y :- Nat, w :- World, r :- CompRow, hnt :- (= (:tomb r) false)]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (tombs-dormant y w) true) (= (tombs-dormant y (bump (comp-ins w r))) true))
  (intros h1 h2 h)
  (have hr (= (tombs-dormant-rest y (bump (comp-ins w r))) true))
  (simp only [tombs-dormant-rest bump comp-ins set-next-id set-comps])
  (exact (tombs-dormant-keys-ok-comp-sub y (:comps w) (tbl-ins r (:comps w)) (:runs w) (:edges w)
           (fn [z :- Nat, hz :- (= (untomb (:comps w) z) true)] (untomb-ins r (:comps w) z hnt hz)) (tombs-dormant-rest-of y w h)))
  (exact (tombs-dormant-intro y _ (well-formed-comp-ins-fresh w r h1 h2 (tombs-dormant-well-formed y w h)) hr)))

;; a new edge: a dep edge's creditor is no tombstone
(a/theorem tombs-dormant-insert-edge-fresh [y :- Nat, w :- World, e :- EdgeRow, hn :- (= (dep-untomb (:comps w) e) true)]
  (=> (= (edge-ok-in w e) true) (= (tombs-dormant y w) true) (= (tombs-dormant y (insert-edge-fresh w e)) true))
  (intros he h)
  (have p := (tombs-dormant-keys-ok-parts y _ _ _ (tombs-dormant-rest-of y w h)))
  (have q := (gtk-parts _ _ _ (And.left p)))
  (have d1 (= (dep-untomb (:comps w) (edge-set-id (:next-id w) (edge-set-marked false e))) true))
  (simp only [dep-untomb edge-set-id edge-set-marked]) (simp only [dep-untomb] at hn) (exact hn)
  (have hr (= (tombs-dormant-rest y (insert-edge-fresh w e)) true))
  (simp only [tombs-dormant-rest insert-edge-fresh bump insert-edge edge-ins set-next-id set-edges tbl-ins])
  (exact (tombs-dormant-keys-ok-intro y _ _ _ (gtk-intro _ _ _ (And.left q) (all-cons EdgeRow _ _ _ d1 (And.right q))) (And.right p)))
  (exact (tombs-dormant-intro y _ (well-formed-insert-edge-fresh w e he (tombs-dormant-well-formed y w h)) hr)))
(a/theorem tombs-dormant-insert-edge-checked [y :- Nat, w :- World, e :- EdgeRow, hn :- (= (dep-untomb (:comps w) e) true)]
  (=> (= (tombs-dormant y w) true) (= (tombs-dormant y (insert-edge-checked w e)) true))
  (intro h)
  (cases hk (edge-ok-in w e))
  (case [false] (simp only [insert-edge-checked hk]) (exact h))
  (case [true] (simp only [insert-edge-checked hk]) (exact (tombs-dormant-insert-edge-fresh y w e hn hk h))))

(a/theorem tombs-dormant-rest-edge-upd [y :- Nat, w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                             hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                             hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e)))]
  (=> (= (tombs-dormant-rest y w) true) (= (tombs-dormant-rest y (edge-upd w x f)) true))
  (intro h) (exact (tombs-dormant-keys-ok-edge-upd y x f hk hc (:comps w) (:runs w) (:edges w) h)))
(a/theorem tombs-dormant-rest-drop-edges [y :- Nat, w :- World, p :- (=> EdgeRow Bool)]
  (=> (= (tombs-dormant-rest y w) true) (= (tombs-dormant-rest y (drop-edges w p)) true))
  (intro h)
  (have h1 := (tombs-dormant-keys-ok-edge-sub y (:comps w) (:runs w) (:edges w) (tbl-filter p (:edges w))
                (fn [P :- (=> EdgeRow Bool), hp :- (= (tbl-all P (:edges w)) true)] (tbl-all-filter EdgeRow P p (:edges w) hp)) h))
  (exact (tombs-dormant-keys-ok-comp-sub y (:comps w) (comps-resync (tbl-filter p (:edges w)) (:comps w)) (:runs w) (tbl-filter p (:edges w))
           (fn [z :- Nat, hz :- (= (untomb (:comps w) z) true)] (Eq.trans (untomb-resync (tbl-filter p (:edges w)) (:comps w) z) hz)) h1)))
(a/theorem tombs-dormant-rest-drop-cred [y :- Nat, w :- World, a :- Nat]
  (=> (= (tombs-dormant-rest y w) true) (= (tombs-dormant-rest y (drop-cred-edges w a)) true))
  (intro h)
  (have h1 := (tombs-dormant-keys-ok-edge-sub y (:comps w) (:runs w) (:edges w) (tbl-filter (cred-ne a) (:edges w))
                (fn [P :- (=> EdgeRow Bool), hp :- (= (tbl-all P (:edges w)) true)] (tbl-all-filter EdgeRow P (cred-ne a) (:edges w) hp)) h))
  (exact (tombs-dormant-keys-ok-comp-upd y a (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (comp-id c)))
           (ckt-ne _ (fn [c :- CompRow] (Eq.refl (ckt c)))) (:comps w) (:runs w) _ h1)))
(a/theorem tombs-dormant-rest-drop-act [y :- Nat, w :- World, a :- Nat]
  (=> (= (tombs-dormant-rest y w) true) (= (tombs-dormant-rest y (drop-act w a)) true))
  (intro h) (exact (tombs-dormant-rest-drop-cred y w a h)))
(a/theorem tombs-dormant-rest-run-del [y :- Nat, w :- World, x :- Nat]
  (=> (= (tombs-dormant-rest y w) true) (= (tombs-dormant-rest y (run-del w x)) true))
  (intro h)
  (exact (tombs-dormant-keys-ok-run-sub y (:comps w) (:runs w) _ (:edges w)
           (fn [P :- (=> RunRow Bool), hp :- (= (tbl-all P (:runs w)) true)]
             (tbl-all-del RunRow run-id x P P (fn [r :- RunRow, hr :- (= (P r) true), hx :- (= (Nat.beq (run-id r) x) false)] hr) (:runs w) hp))
           h)))
(a/theorem tombs-dormant-rest-comp-del [y :- Nat, w :- World, x :- Nat]
  (=> (= (tombs-dormant-rest y w) true) (= (tombs-dormant-rest y (comp-del w x)) true))
  (intro h)
  (exact (tombs-dormant-keys-ok-comp-sub y (:comps w) _ (:runs w) (:edges w) (fn [z :- Nat, hz :- (= (untomb (:comps w) z) true)] (untomb-del x (:comps w) z hz)) h)))
(a/theorem tombs-dormant-rest-filter-world [y :- Nat, w :- World, K :- (=> Nat Bool)]
  (=> (= (tombs-dormant-rest y w) true) (= (tombs-dormant-rest y (filter-world K w)) true))
  (intro h)
  (have h1 := (tombs-dormant-keys-ok-comp-sub y (:comps w) (tbl-keep K comp-id (:comps w)) (:runs w) (:edges w)
                (fn [z :- Nat, hz :- (= (untomb (:comps w) z) true)] (untomb-keep K (:comps w) z hz)) h))
  (have h2 := (tombs-dormant-keys-ok-run-sub y _ (:runs w) (tbl-keep K run-id (:runs w)) (:edges w)
                (fn [P :- (=> RunRow Bool), hp :- (= (tbl-all P (:runs w)) true)] (tbl-all-keep-same RunRow K run-id P (:runs w) hp)) h1))
  (exact (tombs-dormant-keys-ok-edge-sub y _ _ (:edges w) (tbl-keep K edge-id (:edges w))
           (fn [P :- (=> EdgeRow Bool), hp :- (= (tbl-all P (:edges w)) true)] (tbl-all-keep-same EdgeRow K edge-id P (:edges w) hp)) h2)))
(a/theorem tombs-dormant-rest-edge-del [y :- Nat, w :- World, x :- Nat]
  (=> (= (tombs-dormant-rest y w) true) (= (tombs-dormant-rest y (edge-del w x)) true))
  (intro h)
  (exact (tombs-dormant-keys-ok-edge-sub y (:comps w) (:runs w) (:edges w) _
           (fn [P :- (=> EdgeRow Bool), hp :- (= (tbl-all P (:edges w)) true)]
             (tbl-all-del EdgeRow edge-id x P P (fn [e :- EdgeRow, he :- (= (P e) true), hx :- (= (Nat.beq (edge-id e) x) false)] he) (:edges w) hp))
           h)))
(a/theorem tombs-dormant-rest-remove-edge [y :- Nat, w :- World, x :- Nat]
  (=> (= (tombs-dormant-rest y w) true) (= (tombs-dormant-rest y (remove-edge w x)) true))
  (intro h)
  (have h1 := (tombs-dormant-rest-edge-del y w x h))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact h1))
    (case [true]
      (simp only [remove-edge hf hm])
      (exact (tombs-dormant-keys-ok-comp-upd y (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c)))
               (ckt-ne _ (fn [c :- CompRow] (Eq.refl (ckt c)))) _ _ _ h1)))))
(a/theorem tombs-dormant-rest-mark-edge [y :- Nat, w :- World, x :- Nat]
  (=> (= (tombs-dormant-rest y w) true) (= (tombs-dormant-rest y (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false]
      (simp only [mark-edge hf hm])
      (have h1 := (tombs-dormant-rest-edge-upd y w x (edge-set-marked true) (fn [q :- EdgeRow] (Eq.refl (:kind q))) (fn [q :- EdgeRow] (Eq.refl (:creditor q))) h))
      (exact (tombs-dormant-keys-ok-comp-upd y (:creditor e) comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c)))
               (ckt-ne _ (fn [c :- CompRow] (Eq.refl (ckt c)))) _ _ _ h1)))))
(a/theorem tombs-dormant-rest-unmark-edge [y :- Nat, w :- World, x :- Nat]
  (=> (= (tombs-dormant-rest y w) true) (= (tombs-dormant-rest y (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true]
      (simp only [unmark-edge hf hm])
      (have h1 := (tombs-dormant-rest-edge-upd y w x (edge-set-marked false) (fn [q :- EdgeRow] (Eq.refl (:kind q))) (fn [q :- EdgeRow] (Eq.refl (:creditor q))) h))
      (exact (tombs-dormant-keys-ok-comp-upd y (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c)))
               (ckt-ne _ (fn [c :- CompRow] (Eq.refl (ckt c)))) _ _ _ h1)))))

;; ---- run creation: the new run's computation is no tombstone

(a/theorem tombs-dormant-add-run-scope [y :- Nat, w :- World, of :- Nat, ep :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (untomb (:comps w) of) true) (= (tombs-dormant y w) true) (= (tombs-dormant y (add-run-scope w of ep parent ei)) true))
  (intros ha h)
  (have p := (tombs-dormant-keys-ok-parts y _ _ _ (tombs-dormant-rest-of y w h)))
  (have q := (gtk-parts _ _ _ (And.left p)))
  (have t1 (= (ta-one (:comps w) (new-run-row (:next-id w) of ep (+ (:next-id w) 1) ei)) true))
  (simp only [ta-one new-run-row ha Bool.or_true])
  (have hr (= (tombs-dormant-rest y (add-run-scope w of ep parent ei)) true))
  (simp only [tombs-dormant-rest add-run-scope bump scope-ins run-ins set-next-id set-scopes set-runs])
  (exact (tombs-dormant-keys-ok-intro y _ _ _ (gtk-intro _ _ _ (all-cons RunRow _ _ _ t1 (And.left q)) (And.right q)) (And.right p)))
  (exact (tombs-dormant-intro y _ (well-formed-add-run-scope w of ep parent ei (tombs-dormant-well-formed y w h)) hr)))

(a/theorem untomb-fresh [w :- World] (=> (= (well-formed w) true) (= (untomb (:comps w) (:next-id w)) true))
  (intro h)
  (apply untomb-absent)
  (cases hc (tbl-has comp-id (:next-id w) (:comps w)))
  (case [false] (rfl))
  (case [true] (have l := (comp-below w (:next-id w) h hc)) (omega)))

;; a start (T5) or a dispatch (T11) of computation x: the run is inserted first, then x's row clears
;; the flag; the rest part holds at the end
(a/theorem tombs-dormant-keys-ok-start [y :- Nat, x :- Nat, f :- (=> CompRow CompRow), r :- RunRow,
                      hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                      hw :- (forall [c :- CompRow] (= (:tomb (f c)) false)),
                      cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (:of r) x) (= (tombs-dormant-keys-ok y cs rs es) true) (= (tombs-dormant-keys-ok y (tbl-upd comp-id x f cs) (tbl-ins r rs) es) true))
  (intros ho h)
  (have h1 := (tombs-dormant-keys-ok-comp-upd y x f hid (clear-ne f hw) cs rs es h))
  (have p := (tombs-dormant-keys-ok-parts y _ _ _ h1))
  (have q := (gtk-parts _ _ _ (And.left p)))
  (have t1 (= (ta-one (tbl-upd comp-id x f cs) r) true))
  (simp only [ta-one ho (untomb-clear x f hid hw cs) Bool.or_true])
  (exact (tombs-dormant-keys-ok-intro y _ _ _ (gtk-intro _ _ _ (all-cons RunRow _ _ _ t1 (And.left q)) (And.right q)) (And.right p))))

;; ===========================================================================
;; Part C. The GY copy
;; ===========================================================================

(defonce GY (mk-bundle 'tombs-dormant '[ty :- Nat] "tombs-dormant-"
          {'well-formed-comp-upd ['(fn [c :- CompRow] (Eq.refl (ckt c))) 5]
           'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (i7-idle-run-key r))) 4]
           'well-formed-insert-edge-fresh ['(Eq.refl true) 2]
           'well-formed-comp-ins-fresh ['(Eq.refl false) 2]
           'well-formed-insert-edge-checked ['(Eq.refl true) 2]}))
(swap! (:renames GY) assoc 'well-formed-parts 'tombs-dormant-parts 'well-formed-comp-upd 'tombs-dormant-comp-upd 'well-formed-run-upd 'tombs-dormant-run-upd
       'well-formed-insert-edge-fresh 'tombs-dormant-insert-edge-fresh 'well-formed-comp-ins-fresh 'tombs-dormant-comp-ins-fresh
       'well-formed-insert-edge-checked 'tombs-dormant-insert-edge-checked)

(defpart GY :reads '[comps edges runs])
(prim! GY 'well-formed-edge-upd '(tombs-dormant-rest-edge-upd ty w x f hk hc R))
(prim! GY 'well-formed-drop-cred-edges '(tombs-dormant-rest-drop-cred ty w a R))
(prim! GY 'well-formed-drop-act '(tombs-dormant-rest-drop-act ty w a R))
(prim! GY 'well-formed-drop-edges '(tombs-dormant-rest-drop-edges ty w p R))
(prim! GY 'well-formed-comp-del-unref '(tombs-dormant-rest-comp-del ty w x R))
(prim! GY 'well-formed-run-del '(tombs-dormant-rest-run-del ty w x R))
(prim! GY 'well-formed-remove-edge '(tombs-dormant-rest-remove-edge ty w x R))
(prim! GY 'well-formed-mark-edge '(tombs-dormant-rest-mark-edge ty w x R))
(prim! GY 'well-formed-unmark-edge '(tombs-dormant-rest-unmark-edge ty w x R))
(prim! GY 'well-formed-filter-world '(tombs-dormant-rest-filter-world ty w K R))

;; the generic source patch: a computation edit by a row that clears the flag, a run edit that ends a run
(def ^:private clear-fns '#{comp-react-row comp-demand-row comp-start-row comp-replace-row comp-set-run comp-make-idle})
(def ^:private down-fns '{run-cancel-row run-cancel-row-dwn run-complete-row run-complete-row-dwn run-fin-pop-end run-fin-pop-end-dwn
                          run-enter-row enter-dwn run-drop-fins run-drop-fins-dwn})
(defn- fhead [f] (if (seq? f) (first f) f))
(defn- lemma-app [f lem] (if (seq? f) (apply list lem (rest f)) lem))
;; tombs-dormant on the generic tree (spindel.v2.pres.tree): its table; its own proofs follow (Parts D, E)
(tree/part! GY
  ;; ---- the part's own proofs (content: dep edges, new runs, parked runs, the demotion's tombstone)
  :over '{well-formed-add-run-scope tombs-dormant-add-run-scope
          well-formed-track-raw     tombs-dormant-track-raw
          well-formed-t7-track            tombs-dormant-t7-track
          well-formed-react-add     tombs-dormant-react-add
          well-formed-react-edges   tombs-dormant-react-edges
          well-formed-react-one     tombs-dormant-react-one
          well-formed-spawn-rows    tombs-dormant-spawn-rows
          well-formed-start-raw     tombs-dormant-start-raw
          well-formed-new-run-of    tombs-dormant-new-run-of
          well-formed-take-park     tombs-dormant-take-park
          well-formed-t-take        tombs-dormant-t-take
          well-formed-arm-park      tombs-dormant-arm-park
          well-formed-t17-arm           tombs-dormant-t17-arm
          well-formed-park-if       tombs-dormant-park-if
          well-formed-await-step    tombs-dormant-await-step
          well-formed-await-wire    tombs-dormant-await-wire
          well-formed-await-post    tombs-dormant-await-post
          well-formed-await-raw     tombs-dormant-await-raw
          well-formed-t6-await            tombs-dormant-t6-await
          well-formed-demote-finish tombs-dormant-demote-finish
          well-formed-demote        tombs-dormant-demote
          well-formed-normalize-round    tombs-dormant-normalize-round
          well-formed-normalize-loop     tombs-dormant-normalize-loop
          well-formed-normalize     tombs-dormant-normalize}
  ;; ---- sites: a run that ends or leaves its slice (by its down lemma), resume (keys kept), a
  ;; computation edit that clears the flag
  :sites (merge
          (tree/row-sites 'well-formed-run-upd (set (keys down-fns))
                          (fn [F] (list 'tombs-dormant-run-upd-m 'ty 'w 'x F 'hf (lemma-app F (down-fns (fhead F))) 'h0)))
          (tree/row-sites 'well-formed-comp-upd clear-fns
                          (fn [F] (list 'tombs-dormant-comp-upd-m 'ty 'w 'x F 'hid 'hp (list 'clear-ne F '(fn [c :- CompRow] (Eq.refl false))) 'h0)))
          '{[well-formed-run-upd run-wake] (tombs-dormant-run-upd ty w x run-wake hf run-wake-i7-idle-run-key h0)})
  ;; ---- facts from the path: T6 and T7 take i7-idle (the awaiting / tracking run is alive), from the
  ;; step's input; T7 also transition's guard (not in a cleanup slice)
  :ctx '{well-formed-t7-track [(= (i7-idle w) true) (= (in-cleanup w st) false)]
         well-formed-t6-await [(= (i7-idle w) true)]}
  :own '{well-formed-raw        [hg7 (= (i7-idle w) true)]
         well-formed-host-guarded-transition      [hg7 (= (i7-idle w) true)]
         well-formed-transition       [hg7 (= (i7-idle w) true)]
         well-formed-transition-track [hg7 (= (i7-idle w) true)]}
  :pass '{well-formed-transition-track {well-formed-t7-track [hg7 hc]}})

;; ===========================================================================
;; Part D. Overrides: dep edges, new runs, parked runs
;; ===========================================================================

(a/theorem untomb-of-alive [y :- Nat, w :- World, r :- RunRow]
  (=> (= (tombs-dormant y w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (untomb (:comps w) (:of r)) true))
  (intros h hm ha)
  (have q := (gtk-parts _ _ _ (tombs-dormant-gtk y w h)))
  (have t := (tbl-all-mem RunRow (ta-one (:comps w)) r (:runs w) (And.left q) hm))
  (simp only [ta-one ha Bool.not_true Bool.false_or] at t)
  (exact t))

;; T7's tracking run holds the slice in normal mode (not a cleanup slice), so it is alive (i7-idle's sn)
(a/theorem tok-alive [w :- World, st :- Nat, r :- RunRow]
  (=> (= (i7-idle w) true) (= (tok-run w st) (Option.some RunRow r)) (= (in-cleanup w st) false) (= (run-alive r) true))
  (intros h ht hc)
  (have p := (tok-facts w st r ht))
  (have hu := (cleanup-not-unw w st r hc ht))
  (have hv := (tok-valid w st r ht))
  (simp only [run-unwinding] at hu)
  (simp only [run-valid hu Bool.false_and Bool.or_false Bool.and_eq_true] at hv)
  (have q := (i7-idle-keys-ok-parts _ _ _ (i7-idle-rest-of w h)))
  (have hs := (tbl-all-mem RunRow sn-one r (:runs w) (And.left (And.right (And.right (And.right q)))) (And.left p)))
  (simp only [sn-one (And.left hv) (And.right hv) Bool.and_self Bool.not_true Bool.false_or] at hs)
  (exact hs))

(a/theorem track-untomb [w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat]
  (=> (= (untomb (:comps w) (:of r)) true) (= (dep-untomb (:comps w) (track-edge r x s k)) true))
  (intro h) (simp only [dep-untomb track-edge h Bool.or_true]))
(a/theorem valid-untomb [w :- World, c :- Nat, v :- Valid]
  (=> (= (untomb (:comps w) c) true) (= (dep-untomb (:comps w) (valid-edge w c v)) true))
  (intro h) (simp only [dep-untomb valid-edge h Bool.or_true]))
(a/theorem await-untomb [w :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat]
  (=> (= (untomb (:comps w) (:of r)) true) (= (dep-untomb (:comps w) (await-edge w r a mode k d)) true))
  (intro h)
  (cases hd (as-dep w r d))
  (case [true] (simp only [dep-untomb await-edge hd h Bool.or_true]))
  (case [false] (simp [dep-untomb await-edge hd ek-wait ek-dep])))

;; a run edit on the rows with id x that keeps every alive row's computation no tombstone
(a/defn rq-t [cs :- (List CompRow), f :- (=> RunRow RunRow), q :- RunRow] Bool
  (Bool.or (Bool.not (run-alive (f q))) (untomb cs (:of (f q)))))
(a/theorem tombs-dormant-keys-ok-run-upd-q [y :- Nat, x :- Nat, f :- (=> RunRow RunRow), cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (tbl-all (same-id-then run-id x (rq-t cs f)) rs) true) (= (tombs-dormant-keys-ok y cs rs es) true) (= (tombs-dormant-keys-ok y cs (tbl-upd run-id x f rs) es) true))
  (intros hq h)
  (have p := (tombs-dormant-keys-ok-parts y cs rs es h))
  (have q := (gtk-parts cs rs es (And.left p)))
  (have b1 := (tbl-all-mono2 RunRow (ta-one cs) (same-id-then run-id x (rq-t cs f)) (both (ta-one cs) (same-id-then run-id x (rq-t cs f)))
                (fn [z :- RunRow, h1 :- (= (ta-one cs z) true), h2 :- (= (same-id-then run-id x (rq-t cs f) z) true)]
                  (both-of RunRow (ta-one cs) (same-id-then run-id x (rq-t cs f)) z h1 h2))
                rs (And.left q) hq))
  (have h1 (= (tbl-all (ta-one cs) (tbl-upd run-id x f rs)) true))
  (apply (tbl-all-upd RunRow run-id x f (both (ta-one cs) (same-id-then run-id x (rq-t cs f))) (ta-one cs) _ _ rs b1))
  (intros r hb hx)
  (have hs := (both-right RunRow (ta-one cs) (same-id-then run-id x (rq-t cs f)) r hb))
  (simp only [same-id-then hx Bool.not_true Bool.false_or rq-t] at hs)
  (simp only [ta-one]) (exact hs)
  (intros r hb hx) (exact (both-left RunRow (ta-one cs) (same-id-then run-id x (rq-t cs f)) r hb))
  (exact (tombs-dormant-keys-ok-intro y _ _ _ (gtk-intro _ _ _ h1 (And.right q)) (And.right p))))

;; park run rid: its rows keep their computation z, which is no tombstone
(a/theorem park-rqt [rid :- Nat, z :- Nat, f :- (=> RunRow RunRow), hof :- (forall [q :- RunRow] (= (:of (f q)) (:of q))),
                     cs :- (List CompRow), rs :- (List RunRow)]
  (=> (= (tbl-all (run-of-at rid z) rs) true) (= (untomb cs z) true) (= (tbl-all (same-id-then run-id rid (rq-t cs f)) rs) true))
  (intros ho hz)
  (apply (tbl-all-mono RunRow (run-of-at rid z) (same-id-then run-id rid (rq-t cs f)) _ rs ho))
  (intros q hq)
  (cases hx (Nat.beq (run-id q) rid))
  (case [false] (simp only [same-id-then hx Bool.not_false Bool.true_or]))
  (case [true]
    (have hx2 (= (Nat.beq (:id q) rid) true)) (exact hx)
    (simp only [run-of-at hx2 Bool.not_true Bool.false_or] at hq)
    (have e (= (:of (f q)) z)) (exact (Eq.trans (hof q) (Nat.eq_of_beq_eq_true hq)))
    (simp only [same-id-then hx rq-t e hz Bool.not_true Bool.false_or Bool.or_true])))

(a/theorem runs-iec-t [w :- World, e :- EdgeRow] (= (:runs (insert-edge-checked w e)) (:runs w))
  (cases hk (edge-ok-in w e)) (all_goals (simp only [insert-edge-checked hk insert-edge-fresh bump insert-edge edge-ins set-next-id set-edges])))
(a/theorem comps-iec-t [w :- World, e :- EdgeRow] (= (:comps (insert-edge-checked w e)) (:comps w))
  (cases hk (edge-ok-in w e)) (all_goals (simp only [insert-edge-checked hk insert-edge-fresh bump insert-edge edge-ins set-next-id set-edges])))

(a/theorem of-at-mem [w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (= (tbl-all (run-of-at (:id r) (:of r)) (:runs w)) true))
  (intros h hm)
  (exact (uniq-all RunRow run-id (fn [b :- RunRow] (Nat.beq (:of b) (:of r))) r (:runs w) (lit-runs-nodup w h) hm (Nat.beq_refl (:of r)))))

(tree/restate! GY '[well-formed-track-fin])
(a/theorem tombs-dormant-track-raw [y :- Nat, w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat]
  (=> (= (comp-has w (:of r)) true) (= (source-find w x) (Option.some SourceRow s))
      (= (untomb (:comps w) (:of r)) true) (= (tombs-dormant y w) true) (= (tombs-dormant y (track-raw w r x s k)) true))
  (intros hc hs hut h)
  (have h2 (= (tombs-dormant y (match (site-edge (:edges w) (:of r) (:effect-index r) x)
                      none (track-new w r x s k)
                      (some e) (comp-upd (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s)))
                                         (:of r) (comp-consume-adopt (:effect-index r) x)))) true))
  (cases he (site-edge (:edges w) (:of r) (:effect-index r) x)) (case' [some e]) (case' [none])
  (simp only [track-new])
  (exact (tombs-dormant-comp-upd y _ (:of r) (comp-consume-adopt (:effect-index r) x)
           (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [q :- CompRow] (Eq.refl (ckt q)))
           (tombs-dormant-track-fin y s (:next-id w) _ (tombs-dormant-insert-edge-fresh y w (track-edge r x s k) (track-untomb w r x s k hut) (track-edge-ok w r x s k hc hs) h))))
  (exact (tombs-dormant-comp-upd y _ (:of r) (comp-consume-adopt (:effect-index r) x)
           (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [q :- CompRow] (Eq.refl (ckt q)))
           (tombs-dormant-track-fin y s (:id e) _
             (tombs-dormant-edge-upd y w (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) (edge-reread-kind _ _)
               (edge-reread-creditor _ _) (edge-reread-debtor _ _) (edge-reread-marked _ _) h))))
  (simp only [track-raw])
  (exact (tombs-dormant-run-upd y _ (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (i7-idle-run-key q))) h2)))
(a/theorem tombs-dormant-t7-track [y :- Nat, w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (i7-idle w) true) (= (in-cleanup w st) false) (= (tombs-dormant y w) true) (= (tombs-dormant y (:world (t7-track w st x k fresh))) true))
  (intros hg hcl h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t7-track ht refuse]) (exact h)
  (have hut := (untomb-of-alive y w r h (And.left (tok-facts w st r ht)) (tok-alive w st r hg ht hcl)))
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t7-track ht hs refuse]) (exact h)
  (cases hk (trackable s))
  (simp only [t7-track ht hs hk refuse]) (exact h)
  (cases hc (comp-has w (:of r)))
  (cases hta (task-has w (:of r)))
  (simp only [t7-track ht hs hk hc hta refuse]) (exact h)
  (simp only [t7-track ht hs hk hc hta accept]) (exact (tombs-dormant-run-upd y w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (i7-idle-run-key q))) h))
  (cases hf (Bool.or (Nat.beq fresh (:next-id w)) (opt-some (site-edge (:edges w) (:of r) (:effect-index r) x))))
  (simp only [t7-track ht hs hk hc hf refuse]) (exact h)
  (simp only [t7-track ht hs hk hc hf accept]) (exact (tombs-dormant-track-raw y w r x s k hc hs hut h)))
(tree/restate! GY '[well-formed-insert-edge-checked well-formed-raise-for])
(a/theorem tombs-dormant-react-add [y :- Nat, w :- World, c :- Nat, v :- Valid]
  (=> (= (untomb (:comps w) c) true) (= (tombs-dormant y w) true) (= (tombs-dormant y (react-add w c v)) true))
  (intros hut h)
  (cases hk (react-ok w c v))
  (simp only [react-add hk]) (exact h)
  (simp only [react-add hk])
  (exact (tombs-dormant-raise-for y _ c (:debtor v) (tombs-dormant-insert-edge-checked y w (valid-edge w c v) (valid-untomb w c v hut) h))))
(a/theorem tombs-dormant-react-edges [y :- Nat, vs :- (List Valid)]
  (forall [w :- World, c :- Nat] (=> (= (tombs-dormant c w) true) (= (tombs-dormant y w) true) (= (tombs-dormant y (react-edges w c vs)) true)))
  (induction vs)
  (case' [cons h t ih])
  (case' [nil])
  (intros w c hc hw) (simp only [react-edges]) (exact hw)
  (intros w c hc hw) (simp only [react-edges])
  (exact (ih _ c (tombs-dormant-react-add c w c h (tombs-dormant-untomb c w hc) hc) (tombs-dormant-react-add y w c h (tombs-dormant-untomb c w hc) hw))))
(a/theorem tombs-dormant-react-one [y :- Nat, w :- World, c :- CompRow]
  (=> (= (tombs-dormant y w) true) (= (tombs-dormant y (react-one w c)) true))
  (intro h)
  (simp only [react-one])
  (have h1 := (tombs-dormant-comp-upd-m y w (:id c) comp-react-row comp-react-row-id comp-react-row-pending
                (clear-ne comp-react-row (fn [q :- CompRow] (Eq.refl false))) h))
  (have hc := (tombs-dormant-switch y (:id c) _ h1 (untomb-clear (:id c) comp-react-row comp-react-row-id (fn [q :- CompRow] (Eq.refl false)) (:comps w))))
  (exact (tombs-dormant-react-edges y (:validity c) _ (:id c) hc h1)))
(a/theorem tombs-dormant-spawn-rows [y :- Nat, w :- World, owner :- Nat, inputs :- (List Nat), loc :- Bool]
  (=> (= (tombs-dormant y w) true) (= (tombs-dormant y (spawn-rows w owner inputs loc)) true))
  (intro h)
  (simp only [spawn-rows])
  (have h1 := (tombs-dormant-task-ins-fresh y w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc) (rfl) h))
  (have a1 (= (untomb (:comps (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc)))) (:next-id w)) true))
  (exact (untomb-fresh w (tombs-dormant-well-formed y w h)))
  (exact (tombs-dormant-add-run-scope y _ (:next-id w) 0 (task-scope-parent w owner) 0 a1 h1)))
(a/theorem tombs-dormant-start-raw [y :- Nat, w :- World, c :- CompRow]
  (=> (= (tombs-dormant y w) true) (= (tombs-dormant y (start-raw w c)) true))
  (intro h)
  (have hr (= (tombs-dormant-rest y (start-raw w c)) true))
  (simp only [tombs-dormant-rest start-raw comp-upd add-run-scope bump scope-ins run-ins set-next-id set-scopes set-runs set-comps])
  (exact (tombs-dormant-keys-ok-start y (:id c) (comp-start-row (:next-id w)) (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0)
           (comp-start-row-id (:next-id w)) (fn [q :- CompRow] (Eq.refl false)) (:comps w) (:runs w) (:edges w) (rfl) (tombs-dormant-rest-of y w h)))
  (exact (tombs-dormant-intro y _ (well-formed-start-raw w c (tombs-dormant-well-formed y w h)) hr)))
(a/theorem tombs-dormant-new-run-of [y :- Nat, w :- World, c :- CompRow, ei :- Nat]
  (=> (= (tombs-dormant y w) true) (= (tombs-dormant y (new-run-of w c ei)) true))
  (intro h)
  (have hr (= (tombs-dormant-rest y (new-run-of w c ei)) true))
  (simp only [tombs-dormant-rest new-run-of comp-upd add-run-scope bump scope-ins run-ins set-next-id set-scopes set-runs set-comps])
  (exact (tombs-dormant-keys-ok-start y (:id c) (comp-set-run (:next-id w)) (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei)
           (comp-set-run-id (:next-id w)) (fn [q :- CompRow] (Eq.refl false)) (:comps w) (:runs w) (:edges w) (rfl) (tombs-dormant-rest-of y w h)))
  (exact (tombs-dormant-intro y _ (well-formed-new-run-of w c ei (tombs-dormant-well-formed y w h)) hr)))
(tree/restate! GY '[well-formed-insert-edge-checked])
(a/theorem tombs-dormant-take-park [y :- Nat, w :- World, r :- RunRow, x :- Nat, k :- Nat]
  (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (tombs-dormant y w) true) (= (tombs-dormant y (take-park w r x k)) true))
  (intros hm ha h)
  (have hut := (untomb-of-alive y w r h hm ha))
  (have h1 := (tombs-dormant-insert-edge-checked y _ (take-edge r (:next-id w) x) (Eq.refl true)
                (tombs-dormant-act-ins-fresh y w (take-act w r k) (rfl) h)))
  (have hm2 (List.Mem r (:runs (insert-edge-checked (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x)))))
  (rw [runs-iec-t]) (exact hm)
  (have ho := (of-at-mem _ r (tombs-dormant-well-formed y _ h1) hm2))
  (have hut2 (= (untomb (:comps (insert-edge-checked (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x))) (:of r)) true))
  (rw [comps-iec-t]) (exact hut)
  (simp only [take-park])
  (exact (tombs-dormant-intro y _ (well-formed-run-upd _ (:id r) run-tick-park run-tick-park-id (tombs-dormant-well-formed y _ h1))
           (tombs-dormant-keys-ok-run-upd-q y (:id r) run-tick-park
             (:comps (insert-edge-checked (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x)))
             (:runs (insert-edge-checked (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x)))
             (:edges (insert-edge-checked (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x)))
             (park-rqt (:id r) (:of r) run-tick-park (fn [q :- RunRow] (Eq.refl (:of q)))
               (:comps (insert-edge-checked (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x)))
               (:runs (insert-edge-checked (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x))) ho hut2)
             (tombs-dormant-rest-of y _ h1)))))
(tree/restate! GY '[well-formed-take-now])
(a/theorem tombs-dormant-t-take [y :- Nat, w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (tombs-dormant y w) true) (= (tombs-dormant y (:world (t-take w st x k fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-take ht refuse]) (exact h)
  (have p := (tok-facts w st r ht))
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-take ht hs refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (takeable s))))
  (simp only [t-take ht hs hg refuse]) (exact h)
  (have hn (= (run-normal r) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.left (And.right hg)))
  (cases hv (take-ready s))
  (simp only [t-take ht hs hg hv accept]) (exact (tombs-dormant-take-park y w r x k (And.left p) (normal-alive r hn) h))
  (simp only [t-take ht hs hg hv accept]) (exact (tombs-dormant-take-now y w r x h)))
(tree/restate! GY '[well-formed-arm-raw])
(a/theorem tombs-dormant-arm-park [y :- Nat, w :- World, r :- RunRow, kind :- Nat, k :- Nat]
  (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (tombs-dormant y w) true) (= (tombs-dormant y (arm-park w r kind k)) true))
  (intros hm ha h)
  (simp only [arm-park])
  (exact (tombs-dormant-take-park y _ (run-arm (:next-id w) r) (:next-id w) k (arm-raw-mem w r kind hm) ha (tombs-dormant-arm-raw y w r kind h))))
(a/theorem tombs-dormant-t17-arm [y :- Nat, w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (tombs-dormant y w) true) (= (tombs-dormant y (:world (t17-arm w st kind k fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t17-arm ht refuse]) (exact h)
  (have p := (tok-facts w st r ht))
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind))))
  (simp only [t17-arm ht hg refuse]) (exact h)
  (have hn (= (run-normal r) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.left (And.right hg)))
  (simp only [t17-arm ht hg accept]) (exact (tombs-dormant-arm-park y w r kind k (And.left p) (normal-alive r hn) h)))
(a/theorem tombs-dormant-park-if [y :- Nat, z :- Nat, w :- World, a :- Nat, rid :- Nat]
  (=> (= (tbl-all (run-of-at rid z) (:runs w)) true) (= (untomb (:comps w) z) true) (= (tombs-dormant y w) true) (= (tombs-dormant y (park-if w a rid)) true))
  (intros ho hz h)
  (cases ha (act-has w a))
  (simp only [park-if ha]) (exact h)
  (simp only [park-if ha])
  (exact (tombs-dormant-intro y _ (well-formed-run-upd w rid run-park-row run-park-row-id (tombs-dormant-well-formed y w h))
           (tombs-dormant-keys-ok-run-upd-q y rid run-park-row (:comps w) (:runs w) (:edges w)
             (park-rqt rid z run-park-row (fn [q :- RunRow] (Eq.refl (:of q))) (:comps w) (:runs w) ho hz)
             (tombs-dormant-rest-of y w h)))))
(tree/restate! GY '[well-formed-insert-edge-checked well-formed-raise-for well-formed-edge-upd])
(a/theorem tombs-dormant-await-step [y :- Nat, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (untomb (:comps (:world acc)) (:of r)) true) (= (tombs-dormant y (:world acc)) true) (= (tombs-dormant y (:world (await-step r a mode k acc d))) true))
  (intros hut h)
  (cases hd (as-dep (:world acc) r d))
  (case [false]
    (simp only [await-step hd])
    (exact (tombs-dormant-insert-edge-checked y _ _ (await-untomb (:world acc) r a mode k d hut) h)))
  (case [true]
    (cases hs (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none]
      (simp only [await-step hd hs])
      (simp only [await-new-dep])
      (exact (tombs-dormant-comp-upd y _ (:of r) (comp-consume-adopt (:effect-index r) d)
               (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [q :- CompRow] (Eq.refl (ckt q)))
               (tombs-dormant-raise-for y _ (:of r) d (tombs-dormant-insert-edge-checked y _ _ (await-untomb (:world acc) r a mode k d hut) h)))))
    (case [some e]
      (simp only [await-step hd hs])
      (exact (tombs-dormant-comp-upd y _ (:of r) (comp-consume-adopt (:effect-index r) d)
               (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [q :- CompRow] (Eq.refl (ckt q)))
               (tombs-dormant-edge-upd y _ (:id e) (edge-reawait (await-cont r mode k)) (edge-reawait-edge-id _)
                 (edge-reawait-kind _) (edge-reawait-creditor _) (edge-reawait-debtor _) (edge-reawait-marked _) h))))))
(a/theorem tombs-dormant-await-wire [y :- Nat, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, ds :- (List Nat)]
  (forall [acc :- AwAcc] (=> (= (tombs-dormant (:of r) (:world acc)) true) (= (tombs-dormant y (:world acc)) true)
                             (= (tombs-dormant y (:world (await-wire r a mode k acc ds))) true)))
  (induction ds)
  (case' [cons d t ih])
  (case' [nil])
  (intros acc hz h) (simp only [await-wire]) (exact h)
  (intros acc hz h) (simp only [await-wire])
  (exact (ih _ (tombs-dormant-await-step (:of r) r a mode k acc d (tombs-dormant-untomb (:of r) _ hz) hz)
           (tombs-dormant-await-step y r a mode k acc d (tombs-dormant-untomb (:of r) _ hz) h))))
(tree/restate! GY '[well-formed-fast-fill well-formed-finalize-if-final well-formed-nat-fold])
(a/theorem tombs-dormant-await-post [y :- Nat, z :- Nat, a :- Nat, rid :- Nat, ds :- (List Nat), acc :- AwAcc]
  (=> (= (comp-awake-owns-run z rid (:world acc)) true) (= (tombs-dormant z (:world acc)) true) (= (tombs-dormant y (:world acc)) true) (= (tombs-dormant y (await-post a rid ds acc)) true))
  (intros ka hz h)
  (have h2 := (tombs-dormant-act-upd y (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))
                (act-set-members-id (mk-members (:pairs acc) 0 ds)) h))
  (have z2 := (tombs-dormant-act-upd z (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))
                (act-set-members-id (mk-members (:pairs acc) 0 ds)) hz))
  (have k2 := (comp-awake-owns-run-act-upd z rid (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))
                (act-set-members-id (mk-members (:pairs acc) 0 ds)) ka))
  (have h3 := (tombs-dormant-nat-fold y (fast-fill (:pairs acc)) (tombs-dormant-fast-fill y (:pairs acc)) (nat-distinct ds)
                (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))) h2))
  (have z3 := (tombs-dormant-nat-fold z (fast-fill (:pairs acc)) (tombs-dormant-fast-fill z (:pairs acc)) (nat-distinct ds)
                (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))) z2))
  (have k3 := (comp-awake-owns-run-nat-fold z rid (fast-fill (:pairs acc)) (comp-awake-owns-run-fast-fill z rid (:pairs acc)) (nat-distinct ds)
                (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))) k2))
  (have h4 := (tombs-dormant-park-if y z _ a rid (comp-awake-owns-run-of z rid _ k3) (tombs-dormant-untomb z _ z3) h3))
  (exact (tombs-dormant-nat-fold y finalize-if-final (tombs-dormant-finalize-if-final y) (nat-distinct ds) _ h4)))
(tree/restate! GY '[well-formed-await-pre])
(a/theorem tombs-dormant-await-raw [y :- Nat, w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (i7-idle w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (tombs-dormant y w) true) (= (tombs-dormant y (await-raw w r ds mode k mine)) true))
  (intros hg hm hal h)
  (have q := (i7-idle-keys-ok-parts _ _ _ (i7-idle-rest-of w hg)))
  (have a0 := (tbl-all-mem RunRow (a7-one (:comps w)) r (:runs w) (And.left q) hm))
  (simp only [a7-one hal Bool.not_true Bool.false_or] at a0)
  (have k0 := (comp-awake-owns-run-intro (:of r) (:id r) w (tombs-dormant-well-formed y w h) (comp-awake-owns-run-rest-mk (:of r) (:id r) w a0 (of-at-mem w r (tombs-dormant-well-formed y w h) hm))))
  (have z0 := (tombs-dormant-switch y (:of r) w h (untomb-of-alive y w r h hm hal)))
  (have g1 := (tombs-dormant-await-pre y w r ds mode k mine h))
  (have z1 := (tombs-dormant-await-pre (:of r) w r ds mode k mine z0))
  (have k1 := (comp-awake-owns-run-await-pre (:of r) (:id r) w r ds mode k mine k0))
  (have g2 := (tombs-dormant-await-wire y r (:next-id w) mode k (nat-distinct ds) (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) z1 g1))
  (have z2 := (tombs-dormant-await-wire (:of r) r (:next-id w) mode k (nat-distinct ds) (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) z1 z1))
  (have k2 := (comp-awake-owns-run-await-wire (:of r) (:id r) r (:next-id w) mode k (nat-distinct ds) (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) k1))
  (exact (tombs-dormant-await-post y (:of r) (:next-id w) (:id r) ds (await-acc w r ds mode k mine) k2 z2 g2)))
(a/theorem tombs-dormant-t6-await [y :- Nat, w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
  (=> (= (i7-idle w) true) (= (tombs-dormant y w) true) (= (tombs-dormant y (:world (t6-await w st ds mode k fresh mine))) true))
  (intros hg h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t6-await ht refuse]) (exact h)
  (have p := (tok-facts w st r ht))
  (cases hgd (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
  (simp only [t6-await ht hgd refuse]) (exact h)
  (have hn (= (run-normal r) true)) (simp only [await-ok Bool.and_eq_true] at hgd) (exact (And.left (And.right (And.left hgd))))
  (simp only [t6-await ht hgd accept]) (exact (tombs-dormant-await-raw y w r ds mode k mine hg (And.left p) (normal-alive r hn) h)))


(tree/restate! GY '[well-formed-raw])

;; ===========================================================================
;; Part E. Normalization: the demotion makes a tombstone only of a computation without an alive run
;; and without a dep edge (tombs-dormant at 0: no computation has id 0)
;; ===========================================================================

(a/theorem untomb-upd-ne [x :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          cs :- (List CompRow), y :- Nat]
  (=> (= (Nat.beq y x) false) (= (untomb cs y) true) (= (untomb (tbl-upd comp-id x f cs) y) true))
  (intros hy h) (simp only [untomb] at h) (simp only [untomb])
  (apply (tbl-all-upd CompRow comp-id x f (nt-if-id y) (nt-if-id y) _ _ cs h))
  (intros c hc hx)
  (have e (= (:id (f c)) x)) (exact (Eq.trans (hid c) (Nat.eq_of_beq_eq_true hx)))
  (have hy2 (= (Nat.beq x y) false)) (exact (Eq.trans (beq-comm x y) hy))
  (simp only [nt-if-id e hy2 Bool.not_false Bool.true_or])
  (intros c hc hx) (exact hc))

(a/theorem gtk-entomb [x :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                       cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (tbl-all (not-alive-of x) rs) true) (= (tbl-all (not-dep-of x) es) true) (= (gtk cs rs es) true)
      (= (gtk (tbl-upd comp-id x f cs) rs es) true))
  (intros hna hnd h)
  (have q := (gtk-parts cs rs es h))
  (have b1 := (tbl-all-mono2 RunRow (ta-one cs) (not-alive-of x) (both (ta-one cs) (not-alive-of x))
                (fn [z :- RunRow, h1 :- (= (ta-one cs z) true), h2 :- (= (not-alive-of x z) true)] (both-of RunRow (ta-one cs) (not-alive-of x) z h1 h2))
                rs (And.left q) hna))
  (have h1 (= (tbl-all (ta-one (tbl-upd comp-id x f cs)) rs) true))
  (apply (tbl-all-mono RunRow (both (ta-one cs) (not-alive-of x)) (ta-one (tbl-upd comp-id x f cs)) _ rs b1))
  (intros r hb)
  (have ht := (both-left RunRow (ta-one cs) (not-alive-of x) r hb))
  (have hn := (both-right RunRow (ta-one cs) (not-alive-of x) r hb))
  (cases ha (run-alive r))
  (case [false] (simp only [ta-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [not-alive-of ha Bool.not_true Bool.false_or] at hn)
    (simp only [ta-one ha Bool.not_true Bool.false_or] at ht)
    (simp only [ta-one ha Bool.not_true Bool.false_or])
    (exact (untomb-upd-ne x f hid cs (:of r) (bnot-true _ hn) ht)))
  (have b2 := (tbl-all-mono2 EdgeRow (dep-untomb cs) (not-dep-of x) (both (dep-untomb cs) (not-dep-of x))
                (fn [z :- EdgeRow, h1 :- (= (dep-untomb cs z) true), h2 :- (= (not-dep-of x z) true)] (both-of EdgeRow (dep-untomb cs) (not-dep-of x) z h1 h2))
                es (And.right q) hnd))
  (have h2 (= (tbl-all (dep-untomb (tbl-upd comp-id x f cs)) es) true))
  (apply (tbl-all-mono EdgeRow (both (dep-untomb cs) (not-dep-of x)) (dep-untomb (tbl-upd comp-id x f cs)) _ es b2))
  (intros e hb)
  (have ht := (both-left EdgeRow (dep-untomb cs) (not-dep-of x) e hb))
  (have hn := (both-right EdgeRow (dep-untomb cs) (not-dep-of x) e hb))
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dep-untomb hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [not-dep-of dep-of hk Bool.true_and Bool.not_true Bool.false_or] at hn)
    (simp only [dep-untomb hk Bool.not_true Bool.false_or] at ht)
    (simp only [dep-untomb hk Bool.not_true Bool.false_or])
    (exact (untomb-upd-ne x f hid cs (:creditor e) (bnot-true _ hn) ht)))
  (exact (gtk-intro _ _ _ h1 h2)))

(tree/restate! GY '[well-formed-drop-edges well-formed-comp-del-unref])
(a/theorem tombs-dormant-demote-finish [ty :- Nat, w :- World, cid :- Nat, vs :- (List Valid)]
  (=> (= ty 0) (= (tbl-all (not-alive-of cid) (:runs w)) true) (= (tbl-all (not-dep-of cid) (:edges w)) true)
      (= (tombs-dormant ty w) true) (= (tombs-dormant ty (demote-finish w cid vs)) true))
  (intros hz hna hnd h)
  (cases hf (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [demote-finish hf]) (exact h)
  (cases hk (demote-keep w c))
  (simp only [demote-finish hf hk])
  (exact (tombs-dormant-comp-del-unref ty _ cid (drop-edges-avoids w cid) (tombs-dormant-drop-edges ty w (edge-avoids cid) h)))
  (simp only [demote-finish hf hk])
  (have s2 := (well-formed-comp-upd w cid (comp-demote-row vs) (comp-demote-row-id vs) (comp-demote-row-pending vs) (tombs-dormant-well-formed ty w h)))
  (have u0 (= (untomb (:comps (comp-upd w cid (comp-demote-row vs))) ty) true))
  (rw [hz]) (exact (untomb-absent _ 0 (comp-has-zero (comp-upd w cid (comp-demote-row vs)) s2)))
  (have hr (= (tombs-dormant-rest ty (comp-upd w cid (comp-demote-row vs))) true))
  (simp only [tombs-dormant-rest])
  (exact (tombs-dormant-keys-ok-intro ty _ _ _ (gtk-entomb cid (comp-demote-row vs) (comp-demote-row-id vs) (:comps w) (:runs w) (:edges w) hna hnd (tombs-dormant-gtk ty w h)) u0))
  (exact (tombs-dormant-intro ty _ s2 hr)))
(tree/restate! GY '[well-formed-run-cascade well-formed-demote-epoch well-formed-drop-edges well-formed-end-basis])
(a/theorem tombs-dormant-demote [ty :- Nat, w :- World, cid :- Nat]
  (=> (= ty 0) (= (acts-alive w) true) (= (tombs-dormant ty w) true) (= (tombs-dormant ty (demote w cid)) true))
  (intros hz ha h)
  (cases hf (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [demote hf]) (exact h)
  (cases hi (:idle c))
  (simp only [demote hf hi demote-edges])
  (have e (= (:id c) cid)) (exact (tbl-find-id CompRow comp-id cid c (:comps w) hf))
  (have na := (demote-dead w c (tombs-dormant-well-formed ty w h) ha))
  (rw [e] at na)
  (have g1 := (tombs-dormant-run-cascade ty w (cancel-jobs (demote-cancels w c)) h))
  (have g2 := (tombs-dormant-demote-epoch ty _ cid (demote-cur w c) g1))
  (have g3 := (tombs-dormant-drop-edges ty _ (not-dep-of cid) g2))
  (have na3 (= (tbl-all (not-alive-of cid) (:runs (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) cid (demote-cur w c)) (not-dep-of cid)))) true))
  (simp only [drop-edges set-comps set-edges runs-demote-epoch]) (exact na)
  (have nd3 (= (tbl-all (not-dep-of cid) (:edges (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) cid (demote-cur w c)) (not-dep-of cid)))) true))
  (simp only [drop-edges set-comps set-edges]) (exact (tbl-all-filter-self EdgeRow (not-dep-of cid) _))
  (have g4 := (tombs-dormant-end-basis ty _ cid g3))
  (have na4 := (end-basis-dead _ cid cid (tombs-dormant-well-formed ty _ g3) na3))
  (have nd4 := (end-basis-no-dep _ cid cid (tombs-dormant-well-formed ty _ g3) nd3))
  (exact (tombs-dormant-demote-finish ty _ cid _ hz na4 nd4 g4))
  (simp only [demote hf hi]) (exact h))
(a/theorem tombs-dormant-demote-fold [ty :- Nat, hz :- (= ty 0), a :- Nat, k :- Nat, xs :- (List Nat)]
  (forall [w :- World] (=> (= (round-bound a k w) true) (= (tombs-dormant ty w) true) (= (tombs-dormant ty (nat-fold demote w xs)) true)))
  (induction xs)
  (case [nil] (intros w hb h) (simp only [nat-fold]) (exact h))
  (case [cons hd t ih]
    (intros w hb h) (simp only [nat-fold])
    (exact (ih (demote w hd) (round-bound-demote a k w hd hb) (tombs-dormant-demote ty w hd hz (And.left (And.right (round-bound-parts a k w hb))) h)))))

(tree/restate! GY '[well-formed-run-cascade well-formed-detach])
(a/theorem tombs-dormant-normalize-round [ty :- Nat, w :- World]
  (=> (= ty 0) (= (acts-alive w) true) (= (tombs-dormant ty w) true) (= (tombs-dormant ty (normalize-round w)) true))
  (intros hz ha h)
  (simp only [normalize-round normalize-round-with-live])
  (have b0 := (round-bound-intro (alive-cnt w) (act-cnt w) w (tombs-dormant-well-formed ty w h) ha (Nat.le_refl _) (Nat.le_refl _)))
  (exact (tombs-dormant-detach ty _ (tombs-dormant-demote-fold ty hz (alive-cnt w) (act-cnt w) _ _
           (round-bound-run-cascade _ _ w _ b0) (tombs-dormant-run-cascade ty w _ h)))))
(a/theorem tombs-dormant-normalize-loop [ty :- Nat, fuel :- (List Nat)]
  (forall [w :- World] (=> (= ty 0) (= (acts-alive w) true) (= (tombs-dormant ty w) true) (= (tombs-dormant ty (normalize-loop fuel w)) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w hz ha hw) (simp only [normalize-loop]) (exact hw)
  (intros w hz ha hw)
  (cases hn (normalized w))
  (simp only [normalize-loop hn])
  (exact (ih (normalize-round w) hz (And.right (round-bound-round w (tombs-dormant-well-formed ty w hw) ha)) (tombs-dormant-normalize-round ty w hz ha hw)))
  (simp only [normalize-loop hn]) (exact hw))
(tree/restate! GY '[well-formed-detach])
(a/theorem tombs-dormant-normalize [ty :- Nat, w :- World]
  (=> (= ty 0) (= (acts-alive w) true) (= (tombs-dormant ty w) true) (= (tombs-dormant ty (normalize w)) true))
  (intros hz ha h)
  (have b := (round-bound-detach (alive-cnt w) (act-cnt w) w (round-bound-intro (alive-cnt w) (act-cnt w) w (tombs-dormant-well-formed ty w h) ha (Nat.le_refl _) (Nat.le_refl _))))
  (exact (tombs-dormant-normalize-loop ty (normalize-fuel (detach w)) (detach w) hz (And.left (And.right (round-bound-parts _ _ _ b))) (tombs-dormant-detach ty w h))))


;; ===========================================================================
;; Part F. Rule R and the step (tombs-dormant at 0)
;; ===========================================================================

(a/theorem tombs-dormant-rule-r-round [w :- World]
  (=> (= (acts-alive w) true) (= (tombs-dormant 0 w) true) (= (filter-safe (normalize w)) true) (= (tombs-dormant 0 (rule-r-round w)) true))
  (intros ha h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (tombs-dormant-filter-world 0 _ (keep-fn (normalize w)) (tombs-dormant-normalize 0 w (rfl) ha h) hf)))

(a/theorem tombs-dormant-rule-r-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (acts-alive w0) true) (= (tombs-dormant 0 w0) true) (= (rounds-safe-loop fuel w0) true)
                            (= (tombs-dormant 0 (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 ha h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (tombs-dormant-rule-r-round w0 ha h hs)))
  (case [cons x f ih]
    (intros w0 ha h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (tombs-dormant-rule-r-round w0 ha h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false]
      (simp only [ho] at hs) (simp only [rule-r-loop ho])
      (exact (ih (rule-r-round w0) (acts-alive-round w0 (tombs-dormant-well-formed 0 w0 h) ha) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))

(a/theorem tombs-dormant-rule-r [w :- World]
  (=> (= (acts-alive w) true) (= (tombs-dormant 0 w) true) (= (rule-r-safe w) true) (= (tombs-dormant 0 (rule-r w)) true))
  (intros ha h hs)
  (simp only [rule-r-safe] at hs) (simp only [rule-r])
  (exact (tombs-dormant-rule-r-loop (rule-r-fuel w) w ha h hs)))

;; Theorem (C1 Q6): tombstones stay dormant through every step
(a/theorem step-tombs-dormant [w :- World, it :- Item]
  (=> (= (acts-parked w) true) (= (i7-idle w) true) (= (tombs-dormant 0 w) true) (= (rule-r-safe (:world (raw w it))) true) (= (tombs-dormant 0 (:world (world-step w it))) true))
  (intros hg h7 h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true]
    (have e2 := (step-accepted w it ha)) (rw [e2])
    (exact (tombs-dormant-rule-r (:world (raw w it)) (raw-acts-alive w it hg) (tombs-dormant-raw 0 w it h7 h) hs))))

(a/theorem tombs-dormant-empty [] (= (tombs-dormant 0 empty-world) true) (rfl))
;; the P3 premise
(a/theorem tombs-dormant-refs-untomb [w :- World] (=> (= (tombs-dormant 0 w) true) (= (refs-untomb w) true))
  (intro h) (exact (And.right (gtk-parts _ _ _ (tombs-dormant-gtk 0 w h)))))

;; ---- the round context of the other bundles' normalization proofs: acts-alive and tombs-dormant 0
(a/defn trc [w :- World] Bool (Bool.and (acts-alive w) (tombs-dormant 0 w)))
(a/theorem trc-parts [w :- World] (=> (= (trc w) true) (And (= (acts-alive w) true) (= (tombs-dormant 0 w) true)))
  (intro h) (simp only [trc Bool.and_eq_true] at h) (exact h))
(a/theorem trc-intro [w :- World] (=> (= (acts-alive w) true) (= (tombs-dormant 0 w) true) (= (trc w) true))
  (intros h1 h2) (simp only [trc h1 h2 Bool.and_self]))
(a/theorem trc-refs [w :- World] (=> (= (trc w) true) (= (refs-untomb w) true))
  (intro h) (exact (tombs-dormant-refs-untomb w (And.right (trc-parts w h)))))
(a/theorem trc-ta [w :- World] (=> (= (trc w) true) (= (tbl-all (ta-one (:comps w)) (:runs w)) true))
  (intro h) (exact (And.left (gtk-parts _ _ _ (tombs-dormant-gtk 0 w (And.right (trc-parts w h)))))))
(a/theorem trc-normalize-round [w :- World] (=> (= (trc w) true) (= (trc (normalize-round w)) true))
  (intro h)
  (have p := (trc-parts w h))
  (exact (trc-intro _ (And.right (round-bound-round w (tombs-dormant-well-formed 0 w (And.right p)) (And.left p))) (tombs-dormant-normalize-round 0 w (rfl) (And.left p) (And.right p)))))
(a/theorem trc-detach [w :- World] (=> (= (trc w) true) (= (trc (detach w)) true))
  (intro h)
  (have p := (trc-parts w h))
  (have b := (round-bound-detach (alive-cnt w) (act-cnt w) w (round-bound-intro (alive-cnt w) (act-cnt w) w (tombs-dormant-well-formed 0 w (And.right p)) (And.left p) (Nat.le_refl _) (Nat.le_refl _))))
  (exact (trc-intro _ (And.left (And.right (round-bound-parts _ _ _ b))) (tombs-dormant-detach 0 w (And.right p)))))
(a/theorem trc-rule-r-round [w :- World] (=> (= (trc w) true) (= (filter-safe (normalize w)) true) (= (trc (rule-r-round w)) true))
  (intros h hf)
  (have p := (trc-parts w h))
  (exact (trc-intro _ (acts-alive-round w (tombs-dormant-well-formed 0 w (And.right p)) (And.left p)) (tombs-dormant-rule-r-round w (And.left p) (And.right p) hf))))
(a/theorem trc-raw [w :- World, it :- Item] (=> (= (acts-parked w) true) (= (i7-idle w) true) (= (tombs-dormant 0 w) true) (= (trc (:world (raw w it))) true))
  (intros hg h7 h) (exact (trc-intro _ (raw-acts-alive w it hg) (tombs-dormant-raw 0 w it h7 h))))
