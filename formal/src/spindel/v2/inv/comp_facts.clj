(ns spindel.v2.inv.comp-facts
  "L5's state facts through `world-step` (P11), kernel-checked (Init only). Part A-C: the auxiliary
  bundle `comp-facts` (notes/history/PLAN.md, branch z59 (0)), the per-computation facts an h-mark proof needs:
    dle   done-epoch <= epoch, and 0 < epoch
    hrb   C.run is below the allocator (a fresh run is no computation's current run)
    rof   C.run names a run of C (or no run)
    cde   when done-epoch = epoch, C has no alive run at its epoch (by `of`, any run id)
  comp-facts = well-formed && comp-facts-rest, every well-formed lemma restated for comp-facts by the generic tree (`GD`'s table).
  Computation edits: a row function that keeps the id, keeps C.run or clears it, does not lower
  the epoch, and keeps done-epoch or clears it (`cmono`) is a frame; run edits that keep id, of and
  epoch and never revive (`rmono`) are frames (the table's sites). comp-facts's own proofs: T12's result row (done-epoch := epoch: the
  completed run is C.run by i10's cur-ok, so no other alive run is current), reactivation
  (done-epoch := epoch on an idle computation: no alive run, i7-idle's a7), T5/T11 (a new run at C's
  epoch: C needs a run, done-epoch /= its epoch), new runs of tasks (their `of` is no computation).
  Threads: i7-idle (reactivation: T6, T8, T22) and i10-current (T12) from the step's input (own facts); T11's
  new run is at the epoch read before the predecessor's cancel: watch bundle `dispatch-epoch-kept c e` (rows with id
  c keep epoch >= e and done-epoch /= e), a parameterised part restated through cancel-pred/cut-suffix/consume-entry; parks
  reuse i8's KA. Theorems: step-comp-facts (i7-idle w, i10-current w, comp-facts w, rule-r-safe raw -> comp-facts (world-step w it)),
  chain-to-comp-facts = chain-to-i8-closed && comp-facts with step-chain-to-comp-facts / chain-to-comp-facts-empty (no honest hypothesis), step-comp-facts-facts-total.
  Part F (toward h-mark, PLAN z59 (1)): `reach-closure-inv`/`reach-run-inv` (a visited node is a
  root or a successor of a visited node; no convergence), `hm-dirty-back`, `hm-cone-back`.
  h-mark and h-mem2 themselves are proved in spindel.v2.inv.marks-step and spindel.v2.inv.members.step."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [spindel.v2.pres.tree :as tree]
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
            [spindel.v2.inv.idle :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.i10 :refer :all]
            [spindel.v2.inv.i11 :refer :all]
            [spindel.v2.inv.i1-scopes :refer :all]
            [spindel.v2.inv.i8 :refer :all]))

;; ===========================================================================
;; Part A. The auxiliary facts and their transfer lemmas
;; ===========================================================================

(a/structure GDK [] (id Nat) (run Nat) (epoch Nat) (done Nat))
(a/defn gdkey [c :- CompRow] GDK (GDK.mk (:id c) (:run c) (:epoch c) (:done-epoch c)))
(a/defn gdk-id [k :- GDK] Nat (:id k))
(a/defn gdkeys [cs :- (List CompRow)] (List GDK)
  (match cs nil (List.nil GDK) (cons h t) (List.cons GDK (gdkey h) (gdkeys t))))
(a/defn comp-facts-dle [c :- GDK] Bool (Bool.and (Nat.ble (:done c) (:epoch c)) (Nat.blt 0 (:epoch c))))
(a/defn comp-facts-rof [c :- GDK, r :- RunRow] Bool (Bool.or (Bool.not (Nat.beq (:id r) (:run c))) (Nat.beq (:of r) (:id c))))
(a/defn comp-facts-ncur [c :- GDK, r :- RunRow] Bool
  (Bool.not (Bool.and (Nat.beq (:of r) (:id c)) (Bool.and (Nat.beq (:epoch r) (:epoch c)) (run-alive r)))))
(a/defn comp-facts-cde [rs :- (List RunRow), c :- GDK] Bool
  (Bool.or (Bool.not (Nat.beq (:done c) (:epoch c))) (tbl-all (comp-facts-ncur c) rs)))
(a/defn comp-facts-c [rs :- (List RunRow), n :- Nat, c :- GDK] Bool
  (Bool.and (comp-facts-dle c) (Bool.and (Nat.blt (:run c) n) (Bool.and (tbl-all (comp-facts-rof c) rs) (comp-facts-cde rs c)))))
(a/defn gdk [cs :- (List GDK), rs :- (List RunRow), n :- Nat] Bool
  (Bool.and (Nat.blt 0 n) (tbl-all (comp-facts-c rs n) cs)))
(a/defn comp-facts-rest [w :- World] Bool (gdk (gdkeys (:comps w)) (:runs w) (:next-id w)))
(a/defn comp-facts [w :- World] Bool (Bool.and (well-formed w) (comp-facts-rest w)))

(a/theorem comp-facts-well-formed [w :- World] (=> (= (comp-facts w) true) (= (well-formed w) true))
  (intro h) (simp only [comp-facts Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem comp-facts-rest-of [w :- World] (=> (= (comp-facts w) true) (= (comp-facts-rest w) true))
  (intro h) (simp only [comp-facts Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem comp-facts-intro [w :- World] (=> (= (well-formed w) true) (= (comp-facts-rest w) true) (= (comp-facts w) true))
  (intros h1 h2) (simp only [comp-facts h1 h2 Bool.and_self]))
(a/theorem comp-facts-parts [w :- World]
  (=> (= (comp-facts w) true) (And (= (well-formed w) true) (= (comp-facts-rest w) true)))
  (intro h) (exact (And.intro (comp-facts-well-formed w h) (comp-facts-rest-of w h))))

(a/theorem gdk-parts [cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (gdk cs rs n) true) (And (= (Nat.blt 0 n) true) (= (tbl-all (comp-facts-c rs n) cs) true)))
  (intro h) (simp only [gdk Bool.and_eq_true] at h) (exact h))
(a/theorem comp-facts-c-parts [rs :- (List RunRow), n :- Nat, c :- GDK]
  (=> (= (comp-facts-c rs n c) true)
      (And (= (comp-facts-dle c) true) (And (= (Nat.blt (:run c) n) true) (And (= (tbl-all (comp-facts-rof c) rs) true) (= (comp-facts-cde rs c) true)))))
  (intro h) (simp only [comp-facts-c Bool.and_eq_true] at h) (exact h))
(a/theorem comp-facts-c-intro [rs :- (List RunRow), n :- Nat, c :- GDK]
  (=> (= (comp-facts-dle c) true) (= (Nat.blt (:run c) n) true) (= (tbl-all (comp-facts-rof c) rs) true) (= (comp-facts-cde rs c) true)
      (= (comp-facts-c rs n c) true))
  (intros h1 h2 h3 h4) (simp only [comp-facts-c h1 h2 h3 h4 Bool.and_self]))

;; Nat comparisons
(a/theorem comp-facts-lt-of [a :- Nat, b :- Nat] (=> (= (Nat.blt a b) true) (< a b)) (intro h) (simp only [Nat.blt_eq] at h) (exact h))
(a/theorem comp-facts-blt-of [a :- Nat, b :- Nat] (=> (< a b) (= (Nat.blt a b) true)) (intro h) (simp only [Nat.blt_eq]) (exact h))
(a/theorem comp-facts-le-of [a :- Nat, b :- Nat] (=> (= (Nat.ble a b) true) (<= a b)) (intro h) (simp only [Nat.ble_eq] at h) (exact h))
(a/theorem comp-facts-ble-of [a :- Nat, b :- Nat] (=> (<= a b) (= (Nat.ble a b) true)) (intro h) (simp only [Nat.ble_eq]) (exact h))

;; ---- computation rows: cmono c c' (id kept, run kept or cleared, epoch not lowered, done-epoch kept or cleared)
(a/defn comp-facts-cmono [c :- GDK, d :- GDK] Bool
  (Bool.and (Nat.beq (:id d) (:id c))
   (Bool.and (Bool.or (Nat.beq (:run d) (:run c)) (Nat.beq (:run d) 0))
    (Bool.and (Nat.ble (:epoch c) (:epoch d))
              (Bool.or (Nat.beq (:done d) (:done c)) (Nat.beq (:done d) 0))))))

;; no run has id 0
(a/defn comp-facts-rnz [r :- RunRow] Bool (Bool.not (Nat.beq (:id r) 0)))

(a/theorem comp-facts-c-mono [rs :- (List RunRow), n :- Nat, c :- GDK, d :- GDK]
  (=> (= (Nat.blt 0 n) true) (= (tbl-all comp-facts-rnz rs) true) (= (comp-facts-cmono c d) true) (= (comp-facts-c rs n c) true) (= (comp-facts-c rs n d) true))
  (intros hn hz hm hc)
  (have p := (comp-facts-c-parts rs n c hc))
  (simp only [comp-facts-cmono Bool.and_eq_true Bool.or_eq_true] at hm)
  (have hid := (Nat.eq_of_beq_eq_true (And.left hm)))
  (have hr := (And.left (And.right hm)))
  (have he := (comp-facts-le-of _ _ (And.left (And.right (And.right hm)))))
  (have hd := (And.right (And.right (And.right hm))))
  (have dl := (And.left p))
  (simp only [comp-facts-dle Bool.and_eq_true] at dl)
  (have dl1 := (comp-facts-le-of _ _ (And.left dl)))
  (have dl2 := (comp-facts-lt-of _ _ (And.right dl)))
  (have hdd (<= (:done d) (:done c)))
  (cases hd)
  (case [inl q] (rw [(Nat.eq_of_beq_eq_true q)]) (exact (Nat.le_refl _)))
  (case [inr q] (rw [(Nat.eq_of_beq_eq_true q)]) (exact (Nat.zero_le _)))
  (have g1 (= (comp-facts-dle d) true))
  (simp only [comp-facts-dle Bool.and_eq_true])
  (exact (And.intro (comp-facts-ble-of _ _ (Nat.le_trans hdd (Nat.le_trans dl1 he)))
                    (comp-facts-blt-of _ _ (Nat.lt_of_lt_of_le dl2 he))))
  (have g2 (= (Nat.blt (:run d) n) true))
  (cases hr)
  (case [inl q] (rw [(Nat.eq_of_beq_eq_true q)]) (exact (And.left (And.right p))))
  (case [inr q] (rw [(Nat.eq_of_beq_eq_true q)]) (exact hn))
  (have g3 (= (tbl-all (comp-facts-rof d) rs) true))
  (apply (tbl-all-mem-mono RunRow (both comp-facts-rnz (comp-facts-rof c)) (comp-facts-rof d) rs))
  (intros r mr hb)
  (simp only [both Bool.and_eq_true] at hb)
  (simp only [comp-facts-rof hid])
  (cases hr)
  (case [inl q] (rw [(Nat.eq_of_beq_eq_true q)]) (have z := (And.right hb)) (simp only [comp-facts-rof] at z) (exact z))
  (case [inr q] (rw [(Nat.eq_of_beq_eq_true q)]) (have z := (And.left hb)) (simp only [comp-facts-rnz] at z)
    (simp only [z Bool.true_or]))
  (exact (tbl-all-mono2 RunRow comp-facts-rnz (comp-facts-rof c) (both comp-facts-rnz (comp-facts-rof c))
           (fn [q :- RunRow, h1 :- (= (comp-facts-rnz q) true), h2 :- (= (comp-facts-rof c q) true)] (both-of RunRow comp-facts-rnz (comp-facts-rof c) q h1 h2))
           rs hz (And.left (And.right (And.right p)))))
  (have g4 (= (comp-facts-cde rs d) true))
  (cases hde (Nat.beq (:done d) (:epoch d)))
  (case [false] (simp only [comp-facts-cde hde Bool.not_false Bool.true_or]))
  (case [true]
    (have e1 := (Nat.eq_of_beq_eq_true hde))
    (cases hd)
    (case [inr q] (have e0 := (Nat.eq_of_beq_eq_true q)) (rw [e0] at e1) (rw [← e1] at he) (omega))
    (case [inl q]
      (have e0 := (Nat.eq_of_beq_eq_true q))
      (have ee (= (:epoch d) (:epoch c))) (omega)
      (have hc4 := (And.right (And.right (And.right p))))
      (have hce (= (Nat.beq (:done c) (:epoch c)) true)) (simp only [Nat.beq_eq]) (omega)
      (simp only [comp-facts-cde hce Bool.not_true Bool.false_or] at hc4)
      (simp only [comp-facts-cde hde Bool.not_true Bool.false_or])
      (apply (tbl-all-mono RunRow (comp-facts-ncur c) (comp-facts-ncur d) _ rs hc4))
      (intros r hr2)
      (simp only [comp-facts-ncur hid ee]) (simp only [comp-facts-ncur] at hr2) (exact hr2)))
  (exact (comp-facts-c-intro rs n d g1 g2 g3 g4)))

;; ---- key lists
(a/theorem all-gdkeys [P :- (=> GDK Bool), cs :- (List CompRow)]
  (= (tbl-all P (gdkeys cs)) (tbl-all (fn [c :- CompRow] (P (gdkey c))) cs))
  (induction cs) (case [nil] (simp only [gdkeys tbl-all])) (case [cons h t ih] (simp only [gdkeys tbl-all ih])))
(a/theorem gdkeys-upd [x :- Nat, f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (gdkey (f c)) (gdkey c))),
                       cs :- (List CompRow)]
  (= (gdkeys (tbl-upd comp-id x f cs)) (gdkeys cs))
  (induction cs)
  (case [nil] (simp only [tbl-upd gdkeys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (comp-id h) x))
    (case [false] (simp only [tbl-upd hx gdkeys ih]))
    (case [true] (simp only [tbl-upd hx gdkeys ih (hk h)]))))
(a/theorem gdkeys-del [x :- Nat, cs :- (List CompRow)] (= (gdkeys (tbl-del comp-id x cs)) (tbl-del gdk-id x (gdkeys cs)))
  (induction cs)
  (case [nil] (simp only [tbl-del gdkeys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (comp-id h) x))
    (case [false] (have hx2 (= (Nat.beq (gdk-id (gdkey h)) x) false)) (exact hx) (simp only [tbl-del hx gdkeys hx2 ih]))
    (case [true] (have hx2 (= (Nat.beq (gdk-id (gdkey h)) x) true)) (exact hx) (simp only [tbl-del hx gdkeys hx2 ih]))))
(a/theorem gdkeys-keep [K :- (=> Nat Bool), cs :- (List CompRow)] (= (gdkeys (tbl-keep K comp-id cs)) (tbl-keep K gdk-id (gdkeys cs)))
  (induction cs)
  (case [nil] (simp only [tbl-keep gdkeys]))
  (case [cons h t ih]
    (cases hx (K (comp-id h)))
    (case [false] (have hx2 (= (K (gdk-id (gdkey h))) false)) (exact hx) (simp only [tbl-keep hx gdkeys hx2 ih]))
    (case [true] (have hx2 (= (K (gdk-id (gdkey h))) true)) (exact hx) (simp only [tbl-keep hx gdkeys hx2 ih]))))
(a/theorem gdkeys-resync [es :- (List EdgeRow), cs :- (List CompRow)] (= (gdkeys (comps-resync es cs)) (gdkeys cs))
  (induction cs)
  (case [nil] (simp only [comps-resync gdkeys]))
  (case [cons h t ih] (simp only [comps-resync gdkeys ih comp-resync gdkey comp-set-pending])))

;; ---- gdk transfers
(a/theorem comp-facts-c-next [rs :- (List RunRow), n :- Nat, m :- Nat, c :- GDK]
  (=> (<= n m) (= (comp-facts-c rs n c) true) (= (comp-facts-c rs m c) true))
  (intros hl h)
  (have p := (comp-facts-c-parts rs n c h))
  (have q := (comp-facts-lt-of _ _ (And.left (And.right p))))
  (exact (comp-facts-c-intro rs m c (And.left p) (comp-facts-blt-of _ _ (Nat.lt_of_lt_of_le q hl)) (And.left (And.right (And.right p)))
           (And.right (And.right (And.right p))))))
(a/theorem gdk-next [cs :- (List GDK), rs :- (List RunRow), n :- Nat, m :- Nat]
  (=> (<= n m) (= (gdk cs rs n) true) (= (gdk cs rs m) true))
  (intros hl h)
  (have p := (gdk-parts cs rs n h))
  (simp only [gdk Bool.and_eq_true])
  (exact (And.intro (comp-facts-blt-of _ _ (Nat.lt_of_lt_of_le (comp-facts-lt-of _ _ (And.left p)) hl))
           (tbl-all-mono GDK (comp-facts-c rs n) (comp-facts-c rs m) (fn [c :- GDK, hc :- (= (comp-facts-c rs n c) true)] (comp-facts-c-next rs n m c hl hc))
             cs (And.right p)))))
(a/theorem gdk-sub [cs :- (List GDK), cs2 :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (=> (= (tbl-all (comp-facts-c rs n) cs) true) (= (tbl-all (comp-facts-c rs n) cs2) true)) (= (gdk cs rs n) true) (= (gdk cs2 rs n) true))
  (intros hs h)
  (have p := (gdk-parts cs rs n h))
  (simp only [gdk Bool.and_eq_true])
  (exact (And.intro (And.left p) (hs (And.right p)))))
(a/theorem gdk-comp-m [x :- Nat, f :- (=> CompRow CompRow),
                       hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                       hm :- (forall [c :- CompRow] (= (comp-facts-cmono (gdkey c) (gdkey (f c))) true)),
                       cs :- (List CompRow), rs :- (List RunRow), n :- Nat]
  (=> (= (tbl-all comp-facts-rnz rs) true) (= (gdk (gdkeys cs) rs n) true) (= (gdk (gdkeys (tbl-upd comp-id x f cs)) rs n) true))
  (intros hz h)
  (have p := (gdk-parts _ rs n h))
  (simp only [gdk Bool.and_eq_true])
  (apply And.intro) (exact (And.left p))
  (have q := (And.right p))
  (rw [all-gdkeys] at q) (rw [all-gdkeys])
  (exact (tbl-all-upd CompRow comp-id x f (fn [c :- CompRow] (comp-facts-c rs n (gdkey c))) (fn [c :- CompRow] (comp-facts-c rs n (gdkey c)))
           (fn [c :- CompRow, h1 :- (= (comp-facts-c rs n (gdkey c)) true), h2 :- (= (Nat.beq (comp-id c) x) true)]
             (comp-facts-c-mono rs n (gdkey c) (gdkey (f c)) (And.left p) hz (hm c) h1))
           (fn [c :- CompRow, h1 :- (= (comp-facts-c rs n (gdkey c)) true), h2 :- (= (Nat.beq (comp-id c) x) false)] h1)
           cs q)))
(a/theorem gdk-del [x :- Nat, cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (gdk cs rs n) true) (= (gdk (tbl-del gdk-id x cs) rs n) true))
  (intro h)
  (exact (gdk-sub cs _ rs n (tbl-all-del GDK gdk-id x (comp-facts-c rs n) (comp-facts-c rs n)
                               (fn [c :- GDK, h1 :- (= (comp-facts-c rs n c) true), h2 :- (= (Nat.beq (gdk-id c) x) false)] h1) cs) h)))
(a/theorem gdk-keep [K :- (=> Nat Bool), cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (gdk cs rs n) true) (= (gdk (tbl-keep K gdk-id cs) rs n) true))
  (intro h)
  (exact (gdk-sub cs _ rs n (tbl-all-keep GDK K gdk-id (comp-facts-c rs n) (comp-facts-c rs n)
                               (fn [c :- GDK, h1 :- (= (comp-facts-c rs n c) true), h2 :- (= (K (gdk-id c)) true)] h1) cs) h)))

;; ---- run rows: rmono r r' (id, of, epoch kept; never revived)
(a/defn comp-facts-rmono [r :- RunRow, q :- RunRow] Bool
  (Bool.and (Nat.beq (:id q) (:id r))
   (Bool.and (Nat.beq (:of q) (:of r)) (Bool.and (Nat.beq (:epoch q) (:epoch r)) (Bool.or (Bool.not (run-alive q)) (run-alive r))))))

;; the run part of comp-facts-c, generic in the run list
(a/defn comp-facts-cr [rs :- (List RunRow), c :- GDK] Bool (Bool.and (tbl-all (comp-facts-rof c) rs) (comp-facts-cde rs c)))
(a/theorem comp-facts-c-runs [rs :- (List RunRow), rs2 :- (List RunRow), n :- Nat, c :- GDK]
  (=> (=> (= (comp-facts-cr rs c) true) (= (comp-facts-cr rs2 c) true)) (= (comp-facts-c rs n c) true) (= (comp-facts-c rs2 n c) true))
  (intros hs h)
  (have p := (comp-facts-c-parts rs n c h))
  (have q (= (comp-facts-cr rs c) true)) (simp only [comp-facts-cr (And.left (And.right (And.right p))) (And.right (And.right (And.right p))) Bool.and_self])
  (have q2 := (hs q))
  (simp only [comp-facts-cr Bool.and_eq_true] at q2)
  (exact (comp-facts-c-intro rs2 n c (And.left p) (And.left (And.right p)) (And.left q2) (And.right q2))))
(a/theorem gdk-runs [cs :- (List GDK), rs :- (List RunRow), rs2 :- (List RunRow), n :- Nat]
  (=> (forall [c :- GDK] (=> (= (comp-facts-cr rs c) true) (= (comp-facts-cr rs2 c) true))) (= (gdk cs rs n) true) (= (gdk cs rs2 n) true))
  (intros hs h)
  (have p := (gdk-parts cs rs n h))
  (simp only [gdk Bool.and_eq_true])
  (exact (And.intro (And.left p) (tbl-all-mono GDK (comp-facts-c rs n) (comp-facts-c rs2 n)
                                    (fn [c :- GDK, hc :- (= (comp-facts-c rs n c) true)] (comp-facts-c-runs rs rs2 n c (hs c) hc)) cs (And.right p)))))
;; a run list edit that keeps every row's rof and ncur facts
(a/theorem comp-facts-cr-of [rs :- (List RunRow), rs2 :- (List RunRow), c :- GDK]
  (=> (forall [P :- (=> RunRow Bool)] (=> (forall [r :- RunRow] (=> (= (P r) true) (= (comp-facts-rof c r) true)))
                                           (= (tbl-all P rs) true) (= (tbl-all (comp-facts-rof c) rs2) true)))
      (forall [P :- (=> RunRow Bool)] (=> (forall [r :- RunRow] (=> (= (P r) true) (= (comp-facts-ncur c r) true)))
                                           (= (tbl-all P rs) true) (= (tbl-all (comp-facts-ncur c) rs2) true)))
      (= (comp-facts-cr rs c) true) (= (comp-facts-cr rs2 c) true))
  (intros h1 h2 h)
  (simp only [comp-facts-cr Bool.and_eq_true] at h)
  (have a1 := (h1 (comp-facts-rof c) (fn [r :- RunRow, x :- (= (comp-facts-rof c r) true)] x) (And.left h)))
  (have h3 := (And.right h))
  (cases hd (Nat.beq (:done c) (:epoch c)))
  (case [false] (simp only [comp-facts-cr a1 comp-facts-cde hd Bool.not_false Bool.true_or Bool.and_self]))
  (case [true]
    (simp only [comp-facts-cde hd Bool.not_true Bool.false_or] at h3)
    (have a2 := (h2 (comp-facts-ncur c) (fn [r :- RunRow, x :- (= (comp-facts-ncur c r) true)] x) h3))
    (simp only [comp-facts-cr a1 comp-facts-cde hd a2 Bool.not_true Bool.false_or Bool.and_self])))
(a/theorem comp-facts-rof-mono [c :- GDK, r :- RunRow, q :- RunRow]
  (=> (= (comp-facts-rmono r q) true) (= (comp-facts-rof c r) true) (= (comp-facts-rof c q) true))
  (intros hm h)
  (simp only [comp-facts-rmono Bool.and_eq_true] at hm)
  (simp only [comp-facts-rof (Nat.eq_of_beq_eq_true (And.left hm)) (Nat.eq_of_beq_eq_true (And.left (And.right hm)))])
  (exact h))
(a/theorem comp-facts-ncur-mono [c :- GDK, r :- RunRow, q :- RunRow]
  (=> (= (comp-facts-rmono r q) true) (= (comp-facts-ncur c r) true) (= (comp-facts-ncur c q) true))
  (intros hm h)
  (simp only [comp-facts-rmono Bool.and_eq_true] at hm)
  (have e2 := (Nat.eq_of_beq_eq_true (And.left (And.right hm))))
  (have e3 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right hm)))))
  (have al := (And.right (And.right (And.right hm))))
  (simp only [comp-facts-ncur e2 e3]) (simp only [comp-facts-ncur] at h)
  (cases ha (run-alive q))
  (case [false] (simp only [Bool.and_false Bool.not_false]))
  (case [true]
    (simp only [ha Bool.not_true Bool.false_or] at al)
    (simp only [al] at h) (exact h)))
(a/theorem gdk-run-m [x :- Nat, f :- (=> RunRow RunRow), hm :- (forall [r :- RunRow] (= (comp-facts-rmono r (f r)) true)),
                      cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (gdk cs rs n) true) (= (gdk cs (tbl-upd run-id x f rs) n) true))
  (intro h)
  (apply (gdk-runs cs rs _ n _ h))
  (intros c hc)
  (apply (comp-facts-cr-of rs _ c _ _ hc))
  (intros P hP hr)
  (exact (tbl-all-upd RunRow run-id x f P (comp-facts-rof c)
           (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (run-id r) x) true)] (comp-facts-rof-mono c r (f r) (hm r) (hP r h1)))
           (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (run-id r) x) false)] (hP r h1)) rs hr))
  (intros P hP hr)
  (exact (tbl-all-upd RunRow run-id x f P (comp-facts-ncur c)
           (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (run-id r) x) true)] (comp-facts-ncur-mono c r (f r) (hm r) (hP r h1)))
           (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (run-id r) x) false)] (hP r h1)) rs hr)))
(a/theorem gdk-run-del [x :- Nat, cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (gdk cs rs n) true) (= (gdk cs (tbl-del run-id x rs) n) true))
  (intro h)
  (apply (gdk-runs cs rs _ n _ h))
  (intros c hc)
  (apply (comp-facts-cr-of rs _ c _ _ hc))
  (intros P hP hr)
  (exact (tbl-all-del RunRow run-id x P (comp-facts-rof c) (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (run-id r) x) false)] (hP r h1)) rs hr))
  (intros P hP hr)
  (exact (tbl-all-del RunRow run-id x P (comp-facts-ncur c) (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (run-id r) x) false)] (hP r h1)) rs hr)))
(a/theorem gdk-run-keep [K :- (=> Nat Bool), cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (gdk cs rs n) true) (= (gdk cs (tbl-keep K run-id rs) n) true))
  (intro h)
  (apply (gdk-runs cs rs _ n _ h))
  (intros c hc)
  (apply (comp-facts-cr-of rs _ c _ _ hc))
  (intros P hP hr)
  (exact (tbl-all-keep RunRow K run-id P (comp-facts-rof c) (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (K (run-id r)) true)] (hP r h1)) rs hr))
  (intros P hP hr)
  (exact (tbl-all-keep RunRow K run-id P (comp-facts-ncur c) (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (K (run-id r)) true)] (hP r h1)) rs hr)))
;; a new run: fine for every computation it is checked against
(a/defn comp-facts-new-ok [r :- RunRow, c :- GDK] Bool
  (Bool.and (comp-facts-rof c r) (Bool.or (Bool.not (Nat.beq (:done c) (:epoch c))) (comp-facts-ncur c r))))
(a/theorem gdk-run-ins [r :- RunRow, cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (tbl-all (comp-facts-new-ok r) cs) true) (= (gdk cs rs n) true) (= (gdk cs (tbl-ins r rs) n) true))
  (intros hn h)
  (have p := (gdk-parts cs rs n h))
  (simp only [gdk Bool.and_eq_true])
  (apply (And.intro (And.left p)))
  (apply (tbl-all-mono2 GDK (comp-facts-c rs n) (comp-facts-new-ok r) (comp-facts-c (tbl-ins r rs) n) _ cs (And.right p) hn))
  (intros c h1 h2)
  (apply (comp-facts-c-runs rs _ n c _ h1))
  (intro hc)
  (simp only [comp-facts-new-ok Bool.and_eq_true] at h2)
  (simp only [comp-facts-cr Bool.and_eq_true] at hc)
  (have a1 := (And.left hc)) (have a2 := (And.right hc))
  (cases hd (Nat.beq (:done c) (:epoch c)))
  (case [false] (simp only [comp-facts-cr comp-facts-cde tbl-ins tbl-all hd (And.left h2) a1 Bool.not_false Bool.true_or Bool.and_self]))
  (case [true]
    (have b := (And.right h2))
    (simp only [hd Bool.not_true Bool.false_or] at b)
    (simp only [comp-facts-cde hd Bool.not_true Bool.false_or] at a2)
    (simp only [comp-facts-cr comp-facts-cde tbl-ins tbl-all hd (And.left h2) a1 b a2 Bool.not_true Bool.false_or Bool.and_self])))

;; ===========================================================================
;; Part B. The bundle's primitives
;; ===========================================================================

(a/theorem comp-facts-rnz-of [w :- World] (=> (= (well-formed w) true) (= (tbl-all comp-facts-rnz (:runs w)) true))
  (intro hs)
  (exact (all-of-mem RunRow comp-facts-rnz (:runs w)
           (fn [r :- RunRow, mr :- (List.Mem r (:runs w))]
             (Eq.trans (congrArg Bool.not (run-id-pos w r hs mr)) (rfl))))))

(a/theorem comp-facts-rest-grow [w :- World, w2 :- World]
  (=> (= (gdkeys (:comps w2)) (gdkeys (:comps w))) (= (:runs w2) (:runs w)) (<= (:next-id w) (:next-id w2))
      (= (comp-facts-rest w) true) (= (comp-facts-rest w2) true))
  (intros e1 e2 hl h)
  (simp only [comp-facts-rest e1 e2]) (simp only [comp-facts-rest] at h)
  (exact (gdk-next _ _ _ _ hl h)))
(a/theorem comp-facts-rest-same [w :- World, w2 :- World]
  (=> (= (gdkeys (:comps w2)) (gdkeys (:comps w))) (= (:runs w2) (:runs w)) (= (:next-id w2) (:next-id w))
      (= (comp-facts-rest w) true) (= (comp-facts-rest w2) true))
  (intros e1 e2 e3 h)
  (exact (comp-facts-rest-grow w w2 e1 e2 (Nat.le_of_eq (Eq.symm e3)) h)))

(a/theorem comp-facts-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hk :- (forall [c :- CompRow] (= (gdkey (f c)) (gdkey c)))]
  (=> (= (comp-facts w) true) (= (comp-facts (comp-upd w x f)) true))
  (intro h)
  (have r := (comp-facts-rest-same w (comp-upd w x f) (gdkeys-upd x f hk (:comps w)) (rfl) (rfl) (comp-facts-rest-of w h)))
  (exact (comp-facts-intro _ (well-formed-comp-upd w x f hid hp (comp-facts-well-formed w h)) r)))
(a/theorem comp-facts-comp-upd-m [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                          hm :- (forall [c :- CompRow] (= (comp-facts-cmono (gdkey c) (gdkey (f c))) true))]
  (=> (= (comp-facts w) true) (= (comp-facts (comp-upd w x f)) true))
  (intro h)
  (have r0 := (comp-facts-rest-of w h))
  (have r (= (comp-facts-rest (comp-upd w x f)) true))
  (simp only [comp-facts-rest comp-upd set-comps]) (simp only [comp-facts-rest] at r0)
  (exact (gdk-comp-m x f hid hm (:comps w) (:runs w) (:next-id w) (comp-facts-rnz-of w (comp-facts-well-formed w h)) r0))
  (exact (comp-facts-intro _ (well-formed-comp-upd w x f hid hp (comp-facts-well-formed w h)) r)))
(a/theorem comp-facts-run-upd-m [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                         hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         hm :- (forall [r :- RunRow] (= (comp-facts-rmono r (f r)) true))]
  (=> (= (comp-facts w) true) (= (comp-facts (run-upd w x f)) true))
  (intro h)
  (have r0 := (comp-facts-rest-of w h))
  (have r (= (comp-facts-rest (run-upd w x f)) true))
  (simp only [comp-facts-rest run-upd set-runs]) (simp only [comp-facts-rest] at r0)
  (exact (gdk-run-m x f hm _ (:runs w) (:next-id w) r0))
  (exact (comp-facts-intro _ (well-formed-run-upd w x f hf (comp-facts-well-formed w h)) r)))

;; a new computation row: run 0, dle, and done-epoch /= epoch (checked by rfl at T3's `new-comp-row`)
(a/defn comp-facts-newc [k :- GDK] Bool
  (Bool.and (Nat.beq (:run k) 0) (Bool.and (comp-facts-dle k) (Bool.not (Nat.beq (:done k) (:epoch k))))))
(a/theorem comp-facts-rof-zero [k :- GDK, rs :- (List RunRow)]
  (=> (= (:run k) 0) (= (tbl-all comp-facts-rnz rs) true) (= (tbl-all (comp-facts-rof k) rs) true))
  (intros e hz)
  (apply (tbl-all-mono RunRow comp-facts-rnz (comp-facts-rof k) _ rs hz))
  (intros q hq)
  (have hq2 := (bnot-true _ hq))
  (simp only [comp-facts-rof e hq2 Bool.not_false Bool.true_or]))
(a/theorem gdk-cons [k :- GDK, cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (comp-facts-c rs (+ n 1) k) true) (= (gdk cs rs n) true) (= (gdk (List.cons GDK k cs) rs (+ n 1)) true))
  (intros hc h)
  (have p := (gdk-parts _ _ _ (gdk-next cs rs n (+ n 1) (Nat.le_succ n) h)))
  (simp only [gdk tbl-all (And.left p) hc (And.right p) Bool.and_self]))
(a/theorem comp-facts-comp-ins [w :- World, r :- CompRow, hn :- (= (comp-facts-newc (gdkey r)) true)]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (comp-facts w) true) (= (comp-facts (bump (comp-ins w r))) true))
  (intros h1 h2 h)
  (have r0 := (comp-facts-rest-of w h))
  (simp only [comp-facts-rest] at r0)
  (simp only [comp-facts-newc Bool.and_eq_true] at hn)
  (have e0 := (Nat.eq_of_beq_eq_true (And.left hn)))
  (have hz := (comp-facts-rnz-of w (comp-facts-well-formed w h)))
  (have c1 := (comp-facts-rof-zero (gdkey r) (:runs w) e0 hz))
  (have c2 (= (comp-facts-cde (:runs w) (gdkey r)) true))
  (simp only [comp-facts-cde (And.right (And.right hn)) Bool.not_false Bool.true_or])
  (have c3 (= (Nat.blt (:run (gdkey r)) (+ (:next-id w) 1)) true))
  (apply comp-facts-blt-of) (show (< (:run r) (+ (:next-id w) 1))) (rw [e0]) (exact (Nat.zero_lt_succ _))
  (have hc := (comp-facts-c-intro (:runs w) (+ (:next-id w) 1) (gdkey r) (And.left (And.right hn)) c3 c1 c2))
  (have rr (= (comp-facts-rest (bump (comp-ins w r))) true))
  (show (= (gdk (List.cons GDK (gdkey r) (gdkeys (:comps w))) (:runs w) (+ (:next-id w) 1)) true))
  (exact (gdk-cons _ _ _ _ hc r0))
  (exact (comp-facts-intro _ (well-formed-comp-ins-fresh w r h1 h2 (comp-facts-well-formed w h)) rr)))

;; ---- rest lemmas of the edge and table primitives
(a/theorem comp-facts-key-inc-pending [c :- CompRow] (= (gdkey (comp-inc-pending c)) (gdkey c)) (rfl))
(a/theorem comp-facts-key-dec-pending [c :- CompRow] (= (gdkey (comp-dec-pending c)) (gdkey c)) (rfl))
(a/theorem comp-facts-key-set-pending [k :- Nat, c :- CompRow] (= (gdkey (comp-set-pending k c)) (gdkey c)) (rfl))

(a/theorem gdr-mark-edge [w :- World, x :- Nat] (=> (= (comp-facts-rest w) true) (= (comp-facts-rest (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false]
      (simp only [mark-edge hf hm])
      (exact (comp-facts-rest-same w (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending)
               (gdkeys-upd (:creditor e) comp-inc-pending comp-facts-key-inc-pending (:comps w)) (rfl) (rfl) h)))))
(a/theorem gdr-unmark-edge [w :- World, x :- Nat] (=> (= (comp-facts-rest w) true) (= (comp-facts-rest (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true]
      (simp only [unmark-edge hf hm])
      (exact (comp-facts-rest-same w (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending)
               (gdkeys-upd (:creditor e) comp-dec-pending comp-facts-key-dec-pending (:comps w)) (rfl) (rfl) h)))))
(a/theorem gdr-remove-edge [w :- World, x :- Nat] (=> (= (comp-facts-rest w) true) (= (comp-facts-rest (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact (comp-facts-rest-same w (edge-del w x) (rfl) (rfl) (rfl) h)))
    (case [true]
      (simp only [remove-edge hf hm])
      (exact (comp-facts-rest-same w (comp-upd (edge-del w x) (:creditor e) comp-dec-pending)
               (gdkeys-upd (:creditor e) comp-dec-pending comp-facts-key-dec-pending (:comps w)) (rfl) (rfl) h)))))
(a/theorem gdr-drop-cred [w :- World, a :- Nat] (=> (= (comp-facts-rest w) true) (= (comp-facts-rest (drop-cred-edges w a)) true))
  (intro h)
  (simp only [drop-cred-edges])
  (exact (comp-facts-rest-same w (comp-upd (set-edges w (tbl-filter (cred-ne a) (:edges w))) a (comp-set-pending 0))
           (gdkeys-upd a (comp-set-pending 0) (comp-facts-key-set-pending 0) (:comps w)) (rfl) (rfl) h)))
(a/theorem gdr-drop-act [w :- World, a :- Nat] (=> (= (comp-facts-rest w) true) (= (comp-facts-rest (drop-act w a)) true))
  (intro h)
  (simp only [drop-act])
  (exact (comp-facts-rest-same (drop-cred-edges w a) (act-del (drop-cred-edges w a) a) (rfl) (rfl) (rfl) (gdr-drop-cred w a h))))
(a/theorem gdr-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (=> (= (comp-facts-rest w) true) (= (comp-facts-rest (drop-edges w p)) true))
  (intro h)
  (simp only [drop-edges])
  (exact (comp-facts-rest-same w (set-comps (set-edges w (tbl-filter p (:edges w))) (comps-resync (tbl-filter p (:edges w)) (:comps w)))
           (gdkeys-resync (tbl-filter p (:edges w)) (:comps w)) (rfl) (rfl) h)))
(a/theorem gdr-insert-edge-fresh [w :- World, e :- EdgeRow] (=> (= (comp-facts-rest w) true) (= (comp-facts-rest (insert-edge-fresh w e)) true))
  (intro h)
  (simp only [insert-edge-fresh])
  (exact (comp-facts-rest-grow w (bump (insert-edge w (edge-set-id (:next-id w) e))) (rfl) (rfl) (Nat.le_succ _) h)))
(a/theorem gdr-insert-edge-checked [w :- World, e :- EdgeRow] (=> (= (comp-facts-rest w) true) (= (comp-facts-rest (insert-edge-checked w e)) true))
  (intro h)
  (cases hk (edge-ok-in w e))
  (simp only [insert-edge-checked hk]) (exact h)
  (simp only [insert-edge-checked hk]) (exact (gdr-insert-edge-fresh w e h)))
(a/theorem gdr-comp-del [w :- World, x :- Nat] (=> (= (comp-facts-rest w) true) (= (comp-facts-rest (comp-del w x)) true))
  (intro h)
  (simp only [comp-facts-rest comp-del set-comps gdkeys-del]) (simp only [comp-facts-rest] at h)
  (exact (gdk-del x _ _ _ h)))
(a/theorem gdr-run-del [w :- World, x :- Nat] (=> (= (comp-facts-rest w) true) (= (comp-facts-rest (run-del w x)) true))
  (intro h)
  (simp only [comp-facts-rest run-del set-runs]) (simp only [comp-facts-rest] at h)
  (exact (gdk-run-del x _ _ _ h)))
(a/theorem gdr-filter-world [w :- World, K :- (=> Nat Bool)] (=> (= (comp-facts-rest w) true) (= (comp-facts-rest (filter-world K w)) true))
  (intro h)
  (simp only [comp-facts-rest filter-world gdkeys-keep]) (simp only [comp-facts-rest] at h)
  (exact (gdk-run-keep K _ _ _ (gdk-keep K _ _ _ h))))

;; ---- row functions: the computation edits that change the key (cmono) and the run edits that end a run
(a/structure GDRK [] (id Nat) (of Nat) (epoch Nat) (alive Bool))
(a/defn gdrk [r :- RunRow] GDRK (GDRK.mk (:id r) (:of r) (:epoch r) (run-alive r)))
(a/theorem comp-facts-rmono-key [r :- RunRow, q :- RunRow] (=> (= (gdrk q) (gdrk r)) (= (comp-facts-rmono r q) true))
  (intro h)
  (have e1 (= (:id q) (:id r))) (exact (congrArg (fn [k :- GDRK] (:id k)) h))
  (have e2 (= (:of q) (:of r))) (exact (congrArg (fn [k :- GDRK] (:of k)) h))
  (have e3 (= (:epoch q) (:epoch r))) (exact (congrArg (fn [k :- GDRK] (:epoch k)) h))
  (have e4 (= (run-alive q) (run-alive r))) (exact (congrArg (fn [k :- GDRK] (:alive k)) h))
  (simp only [comp-facts-rmono e1 e2 e3 e4 Nat.beq_refl Bool.true_and])
  (cases ha (run-alive r)) (all_goals (simp only [Bool.not_false Bool.not_true Bool.true_or Bool.or_true])))
(a/theorem run-cancel-row-grm [r :- RunRow] (= (comp-facts-rmono r (run-cancel-row r)) true)
  (simp [comp-facts-rmono run-cancel-row run-alive act-done Nat.beq_refl]))
(a/theorem run-complete-row-grm [r :- RunRow] (= (comp-facts-rmono r (run-complete-row r)) true)
  (simp [comp-facts-rmono run-complete-row run-alive act-done Nat.beq_refl]))

(a/theorem comp-facts-ble-refl [n :- Nat] (= (Nat.ble n n) true) (exact (comp-facts-ble-of n n (Nat.le_refl n))))
(a/theorem run-wake-grm [r :- RunRow] (= (comp-facts-rmono r (run-wake r)) true)
  (apply comp-facts-rmono-key)
  (show (= (GDRK.mk (:id r) (:of r) (:epoch r) (run-alive (run-wake r))) (GDRK.mk (:id r) (:of r) (:epoch r) (run-alive r))))
  (rw [run-wake-alive]))
(a/theorem comp-facts-cmono-key [c :- CompRow, d :- CompRow] (=> (= (gdkey d) (gdkey c)) (= (comp-facts-cmono (gdkey c) (gdkey d)) true))
  (intro h) (rw [h]) (simp only [comp-facts-cmono Nat.beq_refl comp-facts-ble-refl Bool.true_or Bool.and_self]))
(a/theorem comp-inc-epoch-gcm [c :- CompRow] (= (comp-facts-cmono (gdkey c) (gdkey (comp-inc-epoch c))) true)
  (simp only [comp-facts-cmono gdkey comp-inc-epoch Nat.beq_refl Bool.true_or Bool.and_true Bool.true_and])
  (apply comp-facts-ble-of) (omega))
(a/theorem comp-demand-row-gcm [c :- CompRow] (= (comp-facts-cmono (gdkey c) (gdkey (comp-demand-row c))) true)
  (cases hd (Nat.beq (:done-epoch c) 0))
  (all_goals (simp only [comp-facts-cmono gdkey comp-demand-row hd Nat.beq_refl Bool.true_or Bool.and_true Bool.true_and comp-facts-ble-refl]))
  (all_goals (apply comp-facts-ble-of) (omega)))
(a/theorem comp-replace-row-gcm [i :- (List Nat), b :- Nat, c :- CompRow] (= (comp-facts-cmono (gdkey c) (gdkey (comp-replace-row i b c))) true)
  (cases hi (:idle c))
  (all_goals (simp only [comp-facts-cmono gdkey comp-replace-row hi Nat.beq_refl Bool.true_or Bool.or_true Bool.and_true Bool.true_and]))
  (all_goals (apply comp-facts-ble-of) (omega)))
(a/theorem comp-make-idle-gcm [vs :- (List Valid), c :- CompRow] (= (comp-facts-cmono (gdkey c) (gdkey (comp-make-idle vs c))) true)
  (simp only [comp-facts-cmono gdkey comp-make-idle Nat.beq_refl comp-facts-ble-refl Bool.true_or Bool.or_true Bool.and_self]))
(a/theorem comp-demote-row-gcm [vs :- (List Valid), c :- CompRow] (= (comp-facts-cmono (gdkey c) (gdkey (comp-demote-row vs c))) true)
  (cases h (demote-idle c))
  (all_goals (simp only [comp-facts-cmono gdkey comp-demote-row h Nat.beq_refl comp-facts-ble-refl Bool.true_or Bool.or_true Bool.and_self])))
(a/theorem comp-clear-run-gcm [c :- CompRow] (= (comp-facts-cmono (gdkey c) (gdkey (comp-clear-run c))) true)
  (simp only [comp-facts-cmono gdkey comp-clear-run Nat.beq_refl comp-facts-ble-refl Bool.true_or Bool.or_true Bool.and_self]))

;; ===========================================================================
;; Part C. The bundle copy
;; ===========================================================================

(def GD (mk-bundle 'comp-facts [] "comp-facts-" {'well-formed-comp-ins-fresh ['(Eq.refl true) 2]}))
(swap! (:renames GD) assoc 'well-formed-parts 'comp-facts-parts 'well-formed-comp-ins-fresh 'comp-facts-comp-ins)
(defpart GD :reads '[comps next-id runs])
(doseq [[o t] '[[well-formed-source-ins-fresh source-ins] [well-formed-fork-ins-fresh fork-ins] [well-formed-resource-ins-fresh resource-ins] [well-formed-scope-ins-fresh scope-ins]
                [well-formed-act-ins-fresh act-ins] [well-formed-task-ins-fresh task-ins]]]
  (prim! GD o (list 'comp-facts-rest-grow 'w (list 'bump (list t 'w 'r)) '(rfl) '(rfl) '(Nat.le_succ (:next-id w)) 'R)))
(prim! GD 'well-formed-bump '(comp-facts-rest-grow w (bump w) (rfl) (rfl) (Nat.le_succ (:next-id w)) R))
(prim! GD 'well-formed-remove-edge '(gdr-remove-edge w x R))
(prim! GD 'well-formed-mark-edge '(gdr-mark-edge w x R))
(prim! GD 'well-formed-unmark-edge '(gdr-unmark-edge w x R))
(prim! GD 'well-formed-drop-cred-edges '(gdr-drop-cred w a R))
(prim! GD 'well-formed-drop-act '(gdr-drop-act w a R))
(prim! GD 'well-formed-drop-edges '(gdr-drop-edges w p R))
(prim! GD 'well-formed-insert-edge-fresh '(gdr-insert-edge-fresh w e R))
(prim! GD 'well-formed-insert-edge-checked '(gdr-insert-edge-checked w e R))
(prim! GD 'well-formed-comp-del-unref '(gdr-comp-del w x R))
(prim! GD 'well-formed-run-del '(gdr-run-del w x R))
(prim! GD 'well-formed-filter-world '(gdr-filter-world w K R))

;; the row functions that change comp-facts's keys (computation / run edits), by lemma (comp-facts's sites)
(def ^:private gd-cm '#{comp-inc-epoch comp-demand-row comp-replace-row comp-make-idle comp-demote-row comp-clear-run})
(def ^:private gd-rm '#{run-cancel-row run-complete-row run-wake})
(defn- gd-fhead [f] (if (seq? f) (first f) f))
(defn- gd-lapp [f lem] (if (seq? f) (apply list lem (rest f)) lem))
;; comp-facts on the generic tree (spindel.v2.pres.tree): its table; its own proofs follow (Part D)
(tree/part! GD
  ;; ---- the part's own proofs (content)
  :over '{well-formed-add-run-scope   comp-facts-add-run-scope     ; a new run: fine for every computation (comp-facts-ok-new)
          well-formed-spawn-rows      comp-facts-spawn-rows        ; T4: a task's run (no computation has its id)
          well-formed-start-raw       comp-facts-start-raw         ; T5: a startable computation's first run
          well-formed-t5-start              comp-facts-t5-start
          well-formed-new-run-of      comp-facts-new-run-of        ; T11: a computation's new run at its epoch (dispatch-epoch-kept)
          well-formed-dispatch-raw    comp-facts-dispatch-raw
          well-formed-t11-dispatch             comp-facts-t11-dispatch
          well-formed-complete-body   comp-facts-complete-body     ; T12: a completing run marks its computation done (comp-facts-cce)
          well-formed-complete-raw    comp-facts-complete-raw
          well-formed-retire-one      comp-facts-retire-one
          well-formed-t12-complete             comp-facts-t12-complete
          well-formed-react-one       comp-facts-react-one         ; reactivation: an idle computation wakes (i7-idle)
          well-formed-react-loop      comp-facts-react-loop
          well-formed-demand-reactive comp-facts-demand-reactive
          well-formed-await-pre       comp-facts-await-pre         ; T6, T22, T8: the demanded computations react (i7-idle)
          well-formed-await-raw       comp-facts-await-raw
          well-formed-host-await-raw  comp-facts-host-await-raw
          well-formed-t8-observe-any-kind         comp-facts-t8-observe-any-kind}
  ;; ---- sites: every computation and run edit is monotone in comp-facts's keys (cmono / rmono); by lemma
  ;; where the row function changes them, else the keys are kept
  :sites (merge
          (tree/row-sites 'well-formed-comp-upd (constantly true)
                          (fn [F] (if (contains? gd-cm (gd-fhead F))
                                    (list 'comp-facts-comp-upd-m 'w 'x F 'hid 'hp (gd-lapp F (symbol (str (gd-fhead F) "-gcm"))) 'h0)
                                    (list 'comp-facts-comp-upd 'w 'x F 'hid 'hp '(fn [c :- CompRow] (Eq.refl (gdkey c))) 'h0))))
          (tree/row-sites 'well-formed-run-upd (constantly true)
                          (fn [F] (if (contains? gd-rm (gd-fhead F))
                                    (list 'comp-facts-run-upd-m 'w 'x F 'hf (gd-lapp F (symbol (str (gd-fhead F) "-grm"))) 'h0)
                                    (list 'comp-facts-run-upd-m 'w 'x F 'hf (list 'fn '[r :- RunRow] (list 'comp-facts-rmono-key 'r (list F 'r) '(Eq.refl (gdrk r)))) 'h0))))
          '{[well-formed-run-upd run-park-row]  (comp-facts-run-upd-on w x run-park-row hf comp-facts-keeps-park h0 h1)       ; await: the parked rows are alive
            [well-formed-run-upd run-tick-park] (comp-facts-run-upd-on w x run-tick-park hf comp-facts-keeps-tick-park h0 h1)}) ; take: same
  ;; ---- facts from the path: what comp-facts's own proofs and sites take ...
  :ctx '{[well-formed-run-upd run-park-row]  [(= (tbl-all (run-ok-for x) (:runs w)) true)]
         [well-formed-run-upd run-tick-park] [(= (tbl-all (run-ok-for x) (:runs w)) true)]
         well-formed-await-raw               [(= (i7-idle w) true) (List.Mem r (:runs w)) (= (run-alive r) true)]
         well-formed-host-await-raw          [(= (i7-idle w) true)]
         well-formed-t8-observe-any-kind                 [(= (i7-idle w) true)]
         well-formed-t12-complete                     [(= (i10-current w) true)]}
  ;; ---- ... and the facts nodes take from above them and pass on
  :own '{;; i7-idle (reactivation wakes idle computations) and i10-current (T12's cur-ok), from the step's input
         well-formed-raw        [hg7 (= (i7-idle w) true) hg10 (= (i10-current w) true)]
         well-formed-host-guarded-transition      [hg7 (= (i7-idle w) true) hg10 (= (i10-current w) true)]
         well-formed-transition       [hg7 (= (i7-idle w) true) hg10 (= (i10-current w) true)]
         well-formed-t8-observe     [hg7 (= (i7-idle w) true) hg10 (= (i10-current w) true)]   ; C0: T8 goes through t8-observe
         well-formed-t6-await         [hg7 (= (i7-idle w) true)]
         well-formed-take-park  [hm (List.Mem r (:runs w)) hal (= (run-alive r) true)]   ; the parked run was alive
         well-formed-arm-park   [hm (List.Mem r (:runs w)) hal (= (run-alive r) true)]
         well-formed-await-post [hk (= (awaiting-run-alive rid (:world acc)) true)]}                   ; the awaiting run's rows, by i8's awaiting-run-alive
  :pass '{well-formed-take-park  {[well-formed-run-upd run-tick-park] [(take-park-ok w r x k (run-ok-of-mem w r (base-of w h) hm hal))]}
          well-formed-arm-park   {well-formed-take-park [(arm-raw-mem w r kind hm) hal]}
          well-formed-t-take     {well-formed-take-park [(And.left (tok-facts w st r ht)) (normal-alive r (bool-and-left _ _ (bool-and-right _ _ hg)))]}
          well-formed-t17-arm        {well-formed-arm-park [(And.left (tok-facts w st r ht)) (normal-alive r (bool-and-left _ _ (bool-and-right _ _ hg)))]}
          well-formed-t6-await         {well-formed-await-raw [hg7 (And.left (tok-facts w st r ht)) (normal-alive r (await-ok-normal w r ds mode fresh _ hg))]}
          well-formed-await-post {well-formed-park-if [(awaiting-run-alive-rest-of rid _ (awaiting-run-alive-nat-fold rid (fast-fill (:pairs acc)) (awaiting-run-alive-fast-fill rid (:pairs acc)) (nat-distinct ds) _
                                         (awaiting-run-alive-act-upd rid (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))
                                           (act-set-members-id (mk-members (:pairs acc) 0 ds)) hk)))]}})

;; ===========================================================================
;; Part D. comp-facts's own proofs: new runs, dispatch, completion, reactivation
;; ===========================================================================

;; a run edit on the rows with id x, all alive: the edit keeps id, of and epoch
(a/defn comp-facts-keeps [f :- (=> RunRow RunRow), r :- RunRow] Bool
  (Bool.and (Nat.beq (:id (f r)) (:id r)) (Bool.and (Nat.beq (:of (f r)) (:of r)) (Nat.beq (:epoch (f r)) (:epoch r)))))
(a/theorem comp-facts-rmono-alive [f :- (=> RunRow RunRow), r :- RunRow]
  (=> (= (comp-facts-keeps f r) true) (= (run-alive r) true) (= (comp-facts-rmono r (f r)) true))
  (intros hk ha)
  (simp only [comp-facts-keeps Bool.and_eq_true] at hk)
  (simp only [comp-facts-rmono (And.left hk) (And.left (And.right hk)) (And.right (And.right hk)) ha Bool.or_true Bool.and_self]))
(a/theorem comp-facts-all-upd-on [x :- Nat, f :- (=> RunRow RunRow), P :- (=> RunRow Bool), Q :- (=> RunRow Bool),
                          hq :- (forall [r :- RunRow] (=> (= (P r) true) (= (run-alive r) true) (= (Q (f r)) true))),
                          hq2 :- (forall [r :- RunRow] (=> (= (P r) true) (= (Q r) true))), rs :- (List RunRow)]
  (=> (= (tbl-all (run-ok-for x) rs) true) (= (tbl-all P rs) true) (= (tbl-all Q (tbl-upd run-id x f rs)) true))
  (induction rs)
  (case [nil] (intros h1 h2) (simp only [tbl-upd tbl-all]))
  (case [cons h t ih]
    (intros h1 h2)
    (simp only [tbl-all Bool.and_eq_true] at h1 h2)
    (have r2 := (ih (And.right h1) (And.right h2)))
    (cases hx (Nat.beq (run-id h) x))
    (case [false] (simp only [tbl-upd hx tbl-all r2 (hq2 h (And.left h2)) Bool.and_self]))
    (case [true]
      (have hx2 (= (Nat.beq (:id h) x) true)) (exact hx)
      (have al := (And.left h1)) (simp only [run-ok-for hx2 Bool.not_true Bool.false_or] at al)
      (simp only [tbl-upd hx tbl-all r2 (hq h (And.left h2) al) Bool.and_self]))))
(a/theorem gdk-run-on [x :- Nat, f :- (=> RunRow RunRow), hk :- (forall [r :- RunRow] (= (comp-facts-keeps f r) true)),
                       cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (tbl-all (run-ok-for x) rs) true) (= (gdk cs rs n) true) (= (gdk cs (tbl-upd run-id x f rs) n) true))
  (intros ho h)
  (apply (gdk-runs cs rs _ n _ h))
  (intros c hc)
  (apply (comp-facts-cr-of rs _ c _ _ hc))
  (intros P hP hr)
  (exact (comp-facts-all-upd-on x f P (comp-facts-rof c)
           (fn [r :- RunRow, h1 :- (= (P r) true), al :- (= (run-alive r) true)] (comp-facts-rof-mono c r (f r) (comp-facts-rmono-alive f r (hk r) al) (hP r h1)))
           hP rs ho hr))
  (intros P hP hr)
  (exact (comp-facts-all-upd-on x f P (comp-facts-ncur c)
           (fn [r :- RunRow, h1 :- (= (P r) true), al :- (= (run-alive r) true)] (comp-facts-ncur-mono c r (f r) (comp-facts-rmono-alive f r (hk r) al) (hP r h1)))
           hP rs ho hr)))
(a/theorem comp-facts-run-upd-on [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                          hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                          hk :- (forall [r :- RunRow] (= (comp-facts-keeps f r) true))]
  (=> (= (tbl-all (run-ok-for x) (:runs w)) true) (= (comp-facts w) true) (= (comp-facts (run-upd w x f)) true))
  (intros ho h)
  (have r0 := (comp-facts-rest-of w h))
  (have r (= (comp-facts-rest (run-upd w x f)) true))
  (simp only [comp-facts-rest run-upd set-runs]) (simp only [comp-facts-rest] at r0)
  (exact (gdk-run-on x f hk _ (:runs w) (:next-id w) ho r0))
  (exact (comp-facts-intro _ (well-formed-run-upd w x f hf (comp-facts-well-formed w h)) r)))
(a/theorem comp-facts-keeps-park [r :- RunRow] (= (comp-facts-keeps run-park-row r) true) (simp only [comp-facts-keeps run-park-row Nat.beq_refl Bool.and_self]))
(a/theorem comp-facts-keeps-tick-park [r :- RunRow] (= (comp-facts-keeps run-tick-park r) true) (simp only [comp-facts-keeps run-tick-park Nat.beq_refl Bool.and_self]))


;; ---- new runs (T4, T5, T11): a new run of `of` at epoch `ep` is fine for every computation
(a/defn comp-facts-ok-new [o :- Nat, e :- Nat, k :- GDK] Bool
  (Bool.or (Bool.not (Nat.beq (:id k) o)) (Bool.or (Bool.not (Nat.beq (:epoch k) e)) (Bool.not (Nat.beq (:done k) (:epoch k))))))
(a/theorem comp-facts-beq-lt [a :- Nat, b :- Nat] (=> (< a b) (= (Nat.beq b a) false))
  (intro h) (cases hb (Nat.beq b a)) (case [false] (rfl)) (case [true] (have e := (Nat.eq_of_beq_eq_true hb)) (omega)))
(a/theorem comp-facts-beq-lt2 [a :- Nat, b :- Nat] (=> (< a b) (= (Nat.beq a b) false))
  (intro h) (cases hb (Nat.beq a b)) (case [false] (rfl)) (case [true] (have e := (Nat.eq_of_beq_eq_true hb)) (omega)))
(a/theorem comp-facts-new-of [rs :- (List RunRow), n :- Nat, k :- GDK, o :- Nat, e :- Nat, s :- Nat, ei :- Nat]
  (=> (= (comp-facts-c rs n k) true) (= (comp-facts-ok-new o e k) true) (= (comp-facts-new-ok (new-run-row n o e s ei) k) true))
  (intros hc ho)
  (have p := (comp-facts-c-parts rs n k hc))
  (have b1 := (comp-facts-beq-lt _ _ (comp-facts-lt-of _ _ (And.left (And.right p)))))
  (have r1 (= (comp-facts-rof k (new-run-row n o e s ei)) true)) (simp only [comp-facts-rof new-run-row b1 Bool.not_false Bool.true_or])
  (simp only [comp-facts-ok-new Bool.or_eq_true] at ho)
  (simp only [comp-facts-new-ok r1 Bool.true_and])
  (cases ho)
  (case [inl a1] (have a2 := (bnot-true _ a1))
    (have z (= (comp-facts-ncur k (new-run-row n o e s ei)) true))
    (simp only [comp-facts-ncur new-run-row]) (rw [(beq-comm o (:id k))]) (simp only [a2 Bool.false_and Bool.not_false])
    (simp only [z Bool.or_true]))
  (case [inr b]
    (cases b)
    (case [inl a1] (have a2 := (bnot-true _ a1))
      (have z (= (comp-facts-ncur k (new-run-row n o e s ei)) true))
      (simp only [comp-facts-ncur new-run-row]) (rw [(beq-comm e (:epoch k))]) (simp only [a2 Bool.false_and Bool.and_false Bool.not_false])
      (simp only [z Bool.or_true]))
    (case [inr a1] (simp only [a1 Bool.true_or]))))
(a/theorem comp-facts-ok-new-zero [rs :- (List RunRow), n :- Nat, o :- Nat, k :- GDK]
  (=> (= (comp-facts-c rs n k) true) (= (comp-facts-ok-new o 0 k) true))
  (intro hc)
  (have dl := (And.left (comp-facts-c-parts rs n k hc)))
  (simp only [comp-facts-dle Bool.and_eq_true] at dl)
  (have z := (comp-facts-beq-lt _ _ (comp-facts-lt-of _ _ (And.right dl))))
  (simp only [comp-facts-ok-new z Bool.not_false Bool.true_or Bool.or_true]))

(a/theorem comp-facts-add-run-scope [w :- World, of :- Nat, ep :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (tbl-all (comp-facts-ok-new of ep) (gdkeys (:comps w))) true) (= (comp-facts w) true) (= (comp-facts (add-run-scope w of ep parent ei)) true))
  (intros ho h)
  (have r0 := (comp-facts-rest-of w h)) (simp only [comp-facts-rest] at r0)
  (have p := (gdk-parts _ _ _ r0))
  (have hn := (tbl-all-mono2 GDK (comp-facts-c (:runs w) (:next-id w)) (comp-facts-ok-new of ep)
                (comp-facts-new-ok (new-run-row (:next-id w) of ep (+ (:next-id w) 1) ei))
                (fn [k :- GDK, h1 :- (= (comp-facts-c (:runs w) (:next-id w) k) true), h2 :- (= (comp-facts-ok-new of ep k) true)]
                  (comp-facts-new-of (:runs w) (:next-id w) k of ep (+ (:next-id w) 1) ei h1 h2))
                (gdkeys (:comps w)) (And.right p) ho))
  (have r1 := (gdk-run-ins (new-run-row (:next-id w) of ep (+ (:next-id w) 1) ei) _ _ _ hn r0))
  (have rr (= (comp-facts-rest (add-run-scope w of ep parent ei)) true))
  (show (= (gdk (gdkeys (:comps w)) (tbl-ins (new-run-row (:next-id w) of ep (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1)) true))
  (exact (gdk-next _ _ _ _ (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _)) r1))
  (exact (comp-facts-intro _ (well-formed-add-run-scope w of ep parent ei (comp-facts-well-formed w h)) rr)))
(a/theorem comp-facts-spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat), loc :- Bool]
  (=> (= (comp-facts w) true) (= (comp-facts (spawn-rows w owner inputs loc)) true))
  (intro h)
  (have p := (gdk-parts _ _ _ (comp-facts-rest-of w h)))
  (have ho := (tbl-all-mono GDK (comp-facts-c (:runs w) (:next-id w)) (comp-facts-ok-new (:next-id w) 0)
                (fn [k :- GDK, h1 :- (= (comp-facts-c (:runs w) (:next-id w) k) true)] (comp-facts-ok-new-zero (:runs w) (:next-id w) (:next-id w) k h1))
                (gdkeys (:comps w)) (And.right p)))
  (simp only [spawn-rows])
  (exact (comp-facts-add-run-scope (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc)))
           (:next-id w) 0 (task-scope-parent w owner) 0 ho
           (comp-facts-task-ins-fresh w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc) (rfl) h))))


;; ---- T5: the started run is at start-epoch, where the computation has no result (startable)
(a/theorem comp-facts-start-ne [w :- World, c :- CompRow]
  (=> (= (startable w c) true) (= (comp-facts-dle (gdkey c)) true) (= (Nat.beq (:done-epoch c) (start-epoch c)) false))
  (intros hs hd)
  (simp only [comp-facts-dle gdkey Bool.and_eq_true] at hd)
  (have d1 := (comp-facts-le-of _ _ (And.left hd))) (have d2 := (comp-facts-lt-of _ _ (And.right hd)))
  (cases hi (:idle c))
  (case [true]
    (cases hz (Nat.beq (:done-epoch c) 0))
    (case [true] (have z := (Nat.eq_of_beq_eq_true hz)) (simp only [start-epoch hi hz Bool.not_true Bool.and_false]) (rw [z]) (exact (comp-facts-beq-lt2 _ _ d2)))
    (case [false] (simp only [start-epoch hi hz Bool.not_false Bool.and_self]) (apply comp-facts-beq-lt2) (omega)))
  (case [false]
    (have se (= (start-epoch c) (:epoch c))) (simp only [start-epoch hi Bool.false_and])
    (rw [se])
    (simp only [startable hi Bool.not_false Bool.false_and Bool.true_and Bool.false_or Bool.or_eq_true Bool.and_eq_true] at hs)
    (cases hs)
    (case [inl a1] (have z := (Nat.eq_of_beq_eq_true (And.left a1))) (rw [z]) (exact (comp-facts-beq-lt2 _ _ d2)))
    (case [inr a1] (exact (bnot-true _ (And.left a1))))))
(a/theorem comp-facts-runs-below [w :- World] (=> (= (well-formed w) true) (= (tbl-all (fn [r :- RunRow] (Nat.blt (:id r) (:next-id w))) (:runs w)) true))
  (intro hs)
  (have b := (runs-below w hs))
  (rw [all-i10-current-run-keys] at b)
  (exact b))
(a/theorem comp-facts-start-c [rs :- (List RunRow), n :- Nat, c :- CompRow, w :- World]
  (=> (= (comp-facts-c rs n (gdkey c)) true) (= (startable w c) true) (= (tbl-all (fn [r :- RunRow] (Nat.blt (:id r) n)) rs) true)
      (= (comp-facts-c (tbl-ins (new-run-row n (:id c) (start-epoch c) (+ n 1) 0) rs) (+ (+ n 1) 1) (gdkey (comp-start-row n c))) true))
  (intros hc hst hb)
  (have p := (comp-facts-c-parts _ _ _ hc))
  (have ne := (comp-facts-start-ne w c hst (And.left p)))
  (have dl := (And.left p)) (simp only [comp-facts-dle gdkey Bool.and_eq_true] at dl)
  (have d1 := (comp-facts-le-of _ _ (And.left dl))) (have d2 := (comp-facts-lt-of _ _ (And.right dl)))
  (have sge (<= (:epoch c) (start-epoch c)))
  (cases hz (Bool.and (:idle c) (Bool.not (Nat.beq (:done-epoch c) 0))))
  (simp only [start-epoch hz]) (exact (Nat.le_refl _))
  (simp only [start-epoch hz]) (exact (Nat.le_succ _))
  (have g1 (= (comp-facts-dle (gdkey (comp-start-row n c))) true))
  (simp only [comp-facts-dle gdkey comp-start-row Bool.and_eq_true])
  (exact (And.intro (comp-facts-ble-of _ _ (Nat.le_trans d1 sge)) (comp-facts-blt-of _ _ (Nat.lt_of_lt_of_le d2 sge))))
  (have g2 (= (Nat.blt (:run (gdkey (comp-start-row n c))) (+ (+ n 1) 1)) true))
  (apply comp-facts-blt-of) (show (< n (+ (+ n 1) 1))) (omega)
  (have g3 (= (tbl-all (comp-facts-rof (gdkey (comp-start-row n c))) (tbl-ins (new-run-row n (:id c) (start-epoch c) (+ n 1) 0) rs)) true))
  (simp only [tbl-ins tbl-all comp-facts-rof gdkey comp-start-row new-run-row Nat.beq_refl Bool.or_true Bool.true_and])
  (apply (tbl-all-mono RunRow _ _ _ rs hb))
  (intros r hr)
  (have z := (comp-facts-beq-lt2 _ _ (comp-facts-lt-of _ _ hr)))
  (simp only [comp-facts-rof gdkey comp-start-row z Bool.not_false Bool.true_or])
  (have g4 (= (comp-facts-cde (tbl-ins (new-run-row n (:id c) (start-epoch c) (+ n 1) 0) rs) (gdkey (comp-start-row n c))) true))
  (simp only [comp-facts-cde gdkey comp-start-row ne Bool.not_false Bool.true_or])
  (exact (comp-facts-c-intro _ _ _ g1 g2 g3 g4)))
(a/theorem comp-facts-start-ok [w :- World, c :- CompRow]
  (=> (= (startable w c) true) (= (comp-facts-dle (gdkey c)) true) (= (comp-facts-ok-new (:id c) (start-epoch c) (gdkey c)) true))
  (intros hst hd)
  (have ne := (comp-facts-start-ne w c hst hd))
  (cases he (Nat.beq (:epoch c) (start-epoch c)))
  (case [false] (simp only [comp-facts-ok-new gdkey he Bool.not_false Bool.true_or Bool.or_true]))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true he))
    (have ne2 (= (Nat.beq (:done-epoch c) (:epoch c)) false)) (rw [e]) (exact ne)
    (simp only [comp-facts-ok-new gdkey ne2 Bool.not_false Bool.or_true])))
;; rows with c's id are c (unique ids): a fact of c holds for every row with its id
(a/theorem comp-facts-same-id [w :- World, c :- CompRow, Q :- (=> CompRow Bool)]
  (=> (= (well-formed w) true) (List.Mem c (:comps w)) (= (Q c) true)
      (= (tbl-all (same-id-then comp-id (:id c) Q) (:comps w)) true))
  (intros hs hm hq) (exact (uniq-all CompRow comp-id Q c (:comps w) (comps-nodup w hs) hm hq)))

(a/theorem comp-facts-upd-same [x :- Nat, f :- (=> CompRow CompRow), P :- (=> CompRow Bool), Q :- (=> CompRow Bool),
                        hq :- (forall [r :- CompRow] (=> (= (P r) true) (= (Q r) true))), cs :- (List CompRow)]
  (=> (= (tbl-all P cs) true) (= (tbl-all (same-id-then comp-id x (fn [y :- CompRow] (Q (f y)))) cs) true)
      (= (tbl-all Q (tbl-upd comp-id x f cs)) true))
  (induction cs)
  (case [nil] (intros h1 h2) (simp only [tbl-upd tbl-all]))
  (case [cons h t ih]
    (intros h1 h2)
    (simp only [tbl-all Bool.and_eq_true] at h1 h2)
    (have r2 := (ih (And.right h1) (And.right h2)))
    (cases hx (Nat.beq (comp-id h) x))
    (case [false] (simp only [tbl-upd hx tbl-all r2 (hq h (And.left h1)) Bool.and_self]))
    (case [true]
      (have a := (And.left h2)) (simp only [same-id-then hx Bool.not_true Bool.false_or] at a)
      (simp only [tbl-upd hx tbl-all r2 a Bool.and_self]))))
(a/theorem comp-facts-start-raw [w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (startable w c) true) (= (comp-facts w) true) (= (comp-facts (start-raw w c)) true))
  (intros hm hst h)
  (have hs := (comp-facts-well-formed w h))
  (have p := (gdk-parts _ _ _ (comp-facts-rest-of w h)))
  (have q := (And.right p)) (rw [all-gdkeys] at q)
  (have hc0 := (tbl-all-mem CompRow (fn [x :- CompRow] (comp-facts-c (:runs w) (:next-id w) (gdkey x))) c (:comps w) q hm))
  (have u := (comp-facts-same-id w c (fn [x :- CompRow] (comp-facts-ok-new (:id c) (start-epoch c) (gdkey x))) hs hm
               (comp-facts-start-ok w c hst (And.left (comp-facts-c-parts _ _ _ hc0)))))
  (have ho (= (tbl-all (comp-facts-ok-new (:id c) (start-epoch c)) (gdkeys (:comps w))) true))
  (rw [all-gdkeys])
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) u))
  (intros x hx)
  (cases hi (Nat.beq (comp-id x) (:id c)))
  (case [false] (have hi2 (= (Nat.beq (:id x) (:id c)) false)) (exact hi) (simp only [comp-facts-ok-new gdkey hi2 Bool.not_false Bool.true_or]))
  (case [true] (simp only [same-id-then hi Bool.not_true Bool.false_or] at hx) (exact hx))
  (have h1 := (comp-facts-add-run-scope w (:id c) (start-epoch c) 0 0 ho h))
  (have s1 := (comp-facts-well-formed _ h1))
  (have u2 := (comp-facts-same-id w c (fn [x :- CompRow] (comp-facts-c (tbl-ins (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0) (:runs w))
                                                            (+ (+ (:next-id w) 1) 1) (gdkey (comp-start-row (:next-id w) x)))) hs hm
               (comp-facts-start-c (:runs w) (:next-id w) c w hc0 hst (comp-facts-runs-below w hs))))
  (have r1 := (gdk-parts _ _ _ (comp-facts-rest-of _ h1)))
  (have q1 := (And.right r1))
  (change (= (tbl-all (comp-facts-c (tbl-ins (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0) (:runs w)) (+ (+ (:next-id w) 1) 1))
                      (gdkeys (:comps w))) true) at q1)
  (rw [all-gdkeys] at q1)
  (have rr (= (comp-facts-rest (start-raw w c)) true))
  (show (= (gdk (gdkeys (tbl-upd comp-id (:id c) (comp-start-row (:next-id w)) (:comps w)))
                (tbl-ins (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0) (:runs w)) (+ (+ (:next-id w) 1) 1)) true))
  (simp only [gdk (And.left r1) Bool.true_and])
  (rw [all-gdkeys])
  (exact (comp-facts-upd-same (:id c) (comp-start-row (:next-id w)) _ _ (fn [x :- CompRow, hx :- (= (comp-facts-c (tbl-ins (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0) (:runs w)) (+ (+ (:next-id w) 1) 1) (gdkey x)) true)] hx) (:comps w) q1 u2))
  (exact (comp-facts-intro _ (well-formed-start-raw w c hs) rr)))
(a/theorem comp-facts-t5-start [w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (comp-facts w) true) (= (comp-facts (:world (t5-start w cid fresh))) true))
  (intro h)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [t5-start hc refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (startable w c)))
  (simp only [t5-start hc hg refuse]) (exact h)
  (have hst (= (startable w c) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
  (simp only [t5-start hc hg accept]) (exact (comp-facts-start-raw w c (tbl-find-mem CompRow comp-id cid c (:comps w) hc) hst h)))

;; ---- T11: the new run is at C's epoch e as read before the predecessor's cancel. Bundle dispatch-epoch-kept c e:
;; every row with id c has epoch >= e and done-epoch /= e (cmono edits keep it: the epoch only
;; grows, done-epoch is kept or cleared, e > 0); at C's dispatch, needs-run gives it
(a/defn dispatch-epoch-kept-one [kc :- Nat, ke :- Nat, k :- GDK] Bool
  (Bool.or (Bool.not (Nat.beq (:id k) kc)) (Bool.and (Nat.ble ke (:epoch k)) (Bool.not (Nat.beq (:done k) ke)))))
(a/defn dispatch-epoch-kept-rest [kc :- Nat, ke :- Nat, w :- World] Bool (Bool.and (Nat.blt 0 ke) (tbl-all (dispatch-epoch-kept-one kc ke) (gdkeys (:comps w)))))
(a/defn dispatch-epoch-kept [kc :- Nat, ke :- Nat, w :- World] Bool (Bool.and (well-formed w) (dispatch-epoch-kept-rest kc ke w)))
(a/theorem dispatch-epoch-kept-well-formed [kc :- Nat, ke :- Nat, w :- World] (=> (= (dispatch-epoch-kept kc ke w) true) (= (well-formed w) true))
  (intro h) (simp only [dispatch-epoch-kept Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem dispatch-epoch-kept-rest-of [kc :- Nat, ke :- Nat, w :- World] (=> (= (dispatch-epoch-kept kc ke w) true) (= (dispatch-epoch-kept-rest kc ke w) true))
  (intro h) (simp only [dispatch-epoch-kept Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem dispatch-epoch-kept-intro [kc :- Nat, ke :- Nat, w :- World] (=> (= (well-formed w) true) (= (dispatch-epoch-kept-rest kc ke w) true) (= (dispatch-epoch-kept kc ke w) true))
  (intros h1 h2) (simp only [dispatch-epoch-kept h1 h2 Bool.and_self]))
(a/theorem dispatch-epoch-kept-parts [kc :- Nat, ke :- Nat, w :- World]
  (=> (= (dispatch-epoch-kept kc ke w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (dispatch-epoch-kept-well-formed kc ke w h))))
(a/theorem dispatch-epoch-kept-rest-same [kc :- Nat, ke :- Nat, w :- World, w2 :- World]
  (=> (= (gdkeys (:comps w2)) (gdkeys (:comps w))) (= (dispatch-epoch-kept-rest kc ke w) true) (= (dispatch-epoch-kept-rest kc ke w2) true))
  (intros e h) (simp only [dispatch-epoch-kept-rest e]) (simp only [dispatch-epoch-kept-rest] at h) (exact h))
(a/theorem dispatch-epoch-kept-one-mono [kc :- Nat, ke :- Nat, k :- GDK, d :- GDK]
  (=> (= (Nat.blt 0 ke) true) (= (comp-facts-cmono k d) true) (= (dispatch-epoch-kept-one kc ke k) true) (= (dispatch-epoch-kept-one kc ke d) true))
  (intros he hm h)
  (simp only [comp-facts-cmono Bool.and_eq_true Bool.or_eq_true] at hm)
  (have hid := (Nat.eq_of_beq_eq_true (And.left hm)))
  (have hep := (comp-facts-le-of _ _ (And.left (And.right (And.right hm)))))
  (have hd := (And.right (And.right (And.right hm))))
  (have e0 := (comp-facts-lt-of _ _ he))
  (simp only [dispatch-epoch-kept-one hid]) (simp only [dispatch-epoch-kept-one Bool.or_eq_true Bool.and_eq_true] at h)
  (cases h)
  (case [inl a1] (simp only [a1 Bool.true_or]))
  (case [inr a1]
    (have q1 := (comp-facts-le-of _ _ (And.left a1)))
    (have q2 := (bnot-true _ (And.right a1)))
    (have r1 := (comp-facts-ble-of _ _ (Nat.le_trans q1 hep)))
    (have r2 (= (Nat.beq (:done d) ke) false))
    (cases hd)
    (case [inl z] (rw [(Nat.eq_of_beq_eq_true z)]) (exact q2))
    (case [inr z] (rw [(Nat.eq_of_beq_eq_true z)]) (exact (comp-facts-beq-lt2 _ _ e0)))
    (simp only [r1 r2 Bool.not_false Bool.and_self Bool.or_true])))
(a/theorem dispatch-epoch-kept-comp-upd [kc :- Nat, ke :- Nat, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hk :- (forall [c :- CompRow] (= (gdkey (f c)) (gdkey c)))]
  (=> (= (dispatch-epoch-kept kc ke w) true) (= (dispatch-epoch-kept kc ke (comp-upd w x f)) true))
  (intro h)
  (exact (dispatch-epoch-kept-intro kc ke _ (well-formed-comp-upd w x f hid hp (dispatch-epoch-kept-well-formed kc ke w h))
           (dispatch-epoch-kept-rest-same kc ke w (comp-upd w x f) (gdkeys-upd x f hk (:comps w)) (dispatch-epoch-kept-rest-of kc ke w h)))))
(a/theorem dispatch-epoch-kept-comp-upd-m [kc :- Nat, ke :- Nat, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                          hm :- (forall [c :- CompRow] (= (comp-facts-cmono (gdkey c) (gdkey (f c))) true))]
  (=> (= (dispatch-epoch-kept kc ke w) true) (= (dispatch-epoch-kept kc ke (comp-upd w x f)) true))
  (intro h)
  (have r := (dispatch-epoch-kept-rest-of kc ke w h))
  (simp only [dispatch-epoch-kept-rest Bool.and_eq_true] at r)
  (have r2 (= (dispatch-epoch-kept-rest kc ke (comp-upd w x f)) true))
  (simp only [dispatch-epoch-kept-rest comp-upd set-comps (And.left r) Bool.true_and])
  (have q := (And.right r)) (rw [all-gdkeys] at q) (rw [all-gdkeys])
  (exact (tbl-all-upd CompRow comp-id x f (fn [c :- CompRow] (dispatch-epoch-kept-one kc ke (gdkey c))) (fn [c :- CompRow] (dispatch-epoch-kept-one kc ke (gdkey c)))
           (fn [c :- CompRow, h1 :- (= (dispatch-epoch-kept-one kc ke (gdkey c)) true), h2 :- (= (Nat.beq (comp-id c) x) true)]
             (dispatch-epoch-kept-one-mono kc ke (gdkey c) (gdkey (f c)) (And.left r) (hm c) h1))
           (fn [c :- CompRow, h1 :- (= (dispatch-epoch-kept-one kc ke (gdkey c)) true), h2 :- (= (Nat.beq (comp-id c) x) false)] h1)
           (:comps w) q))
  (exact (dispatch-epoch-kept-intro kc ke _ (well-formed-comp-upd w x f hid hp (dispatch-epoch-kept-well-formed kc ke w h)) r2)))
(a/theorem hkwr-mark-edge [kc :- Nat, ke :- Nat, w :- World, x :- Nat] (=> (= (dispatch-epoch-kept-rest kc ke w) true) (= (dispatch-epoch-kept-rest kc ke (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false]
      (simp only [mark-edge hf hm])
      (exact (dispatch-epoch-kept-rest-same kc ke w (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending)
               (gdkeys-upd (:creditor e) comp-inc-pending comp-facts-key-inc-pending (:comps w)) h)))))
(a/theorem hkwr-unmark-edge [kc :- Nat, ke :- Nat, w :- World, x :- Nat] (=> (= (dispatch-epoch-kept-rest kc ke w) true) (= (dispatch-epoch-kept-rest kc ke (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true]
      (simp only [unmark-edge hf hm])
      (exact (dispatch-epoch-kept-rest-same kc ke w (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending)
               (gdkeys-upd (:creditor e) comp-dec-pending comp-facts-key-dec-pending (:comps w)) h)))))
(a/theorem hkwr-remove-edge [kc :- Nat, ke :- Nat, w :- World, x :- Nat] (=> (= (dispatch-epoch-kept-rest kc ke w) true) (= (dispatch-epoch-kept-rest kc ke (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact (dispatch-epoch-kept-rest-same kc ke w (edge-del w x) (rfl) h)))
    (case [true]
      (simp only [remove-edge hf hm])
      (exact (dispatch-epoch-kept-rest-same kc ke w (comp-upd (edge-del w x) (:creditor e) comp-dec-pending)
               (gdkeys-upd (:creditor e) comp-dec-pending comp-facts-key-dec-pending (:comps w)) h)))))
(a/theorem hkwr-drop-cred [kc :- Nat, ke :- Nat, w :- World, a :- Nat] (=> (= (dispatch-epoch-kept-rest kc ke w) true) (= (dispatch-epoch-kept-rest kc ke (drop-cred-edges w a)) true))
  (intro h) (simp only [drop-cred-edges])
  (exact (dispatch-epoch-kept-rest-same kc ke w (comp-upd (set-edges w (tbl-filter (cred-ne a) (:edges w))) a (comp-set-pending 0))
           (gdkeys-upd a (comp-set-pending 0) (comp-facts-key-set-pending 0) (:comps w)) h)))
(a/theorem hkwr-drop-act [kc :- Nat, ke :- Nat, w :- World, a :- Nat] (=> (= (dispatch-epoch-kept-rest kc ke w) true) (= (dispatch-epoch-kept-rest kc ke (drop-act w a)) true))
  (intro h) (simp only [drop-act])
  (exact (dispatch-epoch-kept-rest-same kc ke (drop-cred-edges w a) (act-del (drop-cred-edges w a) a) (rfl) (hkwr-drop-cred kc ke w a h))))
(a/theorem hkwr-drop-edges [kc :- Nat, ke :- Nat, w :- World, p :- (=> EdgeRow Bool)] (=> (= (dispatch-epoch-kept-rest kc ke w) true) (= (dispatch-epoch-kept-rest kc ke (drop-edges w p)) true))
  (intro h) (simp only [drop-edges])
  (exact (dispatch-epoch-kept-rest-same kc ke w (set-comps (set-edges w (tbl-filter p (:edges w))) (comps-resync (tbl-filter p (:edges w)) (:comps w)))
           (gdkeys-resync (tbl-filter p (:edges w)) (:comps w)) h)))
(a/theorem hkwr-comp-del [kc :- Nat, ke :- Nat, w :- World, x :- Nat] (=> (= (dispatch-epoch-kept-rest kc ke w) true) (= (dispatch-epoch-kept-rest kc ke (comp-del w x)) true))
  (intro h) (simp only [dispatch-epoch-kept-rest comp-del set-comps gdkeys-del Bool.and_eq_true]) (simp only [dispatch-epoch-kept-rest Bool.and_eq_true] at h)
  (exact (And.intro (And.left h) (tbl-all-del GDK gdk-id x (dispatch-epoch-kept-one kc ke) (dispatch-epoch-kept-one kc ke)
                                    (fn [k :- GDK, h1 :- (= (dispatch-epoch-kept-one kc ke k) true), h2 :- (= (Nat.beq (gdk-id k) x) false)] h1) _ (And.right h)))))
(a/theorem hkwr-filter-world [kc :- Nat, ke :- Nat, w :- World, K :- (=> Nat Bool)] (=> (= (dispatch-epoch-kept-rest kc ke w) true) (= (dispatch-epoch-kept-rest kc ke (filter-world K w)) true))
  (intro h) (simp only [dispatch-epoch-kept-rest filter-world gdkeys-keep Bool.and_eq_true]) (simp only [dispatch-epoch-kept-rest Bool.and_eq_true] at h)
  (exact (And.intro (And.left h) (tbl-all-keep GDK K gdk-id (dispatch-epoch-kept-one kc ke) (dispatch-epoch-kept-one kc ke)
                                    (fn [k :- GDK, h1 :- (= (dispatch-epoch-kept-one kc ke k) true), h2 :- (= (K (gdk-id k)) true)] h1) _ (And.right h)))))
(a/theorem hkwr-insert-edge-checked [kc :- Nat, ke :- Nat, w :- World, e :- EdgeRow]
  (=> (= (dispatch-epoch-kept-rest kc ke w) true) (= (dispatch-epoch-kept-rest kc ke (insert-edge-checked w e)) true))
  (intro h)
  (cases hk (edge-ok-in w e))
  (simp only [insert-edge-checked hk]) (exact h)
  (simp only [insert-edge-checked hk]) (exact h))

(def HKW (mk-bundle 'dispatch-epoch-kept '[hkc :- Nat, hke :- Nat] "dispatch-epoch-kept-" {}))
(swap! (:renames HKW) assoc 'well-formed-parts 'dispatch-epoch-kept-parts)
(doseq [o '[well-formed-scope-upd well-formed-pub-upd well-formed-source-upd well-formed-resource-upd well-formed-cleanup-upd well-formed-cleanup-del well-formed-set-pins
            well-formed-resource-del well-formed-scope-del well-formed-cleanup-ins well-formed-act-upd well-formed-task-upd well-formed-edge-upd well-formed-run-upd well-formed-run-del
            well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-resource-ins-fresh well-formed-scope-ins-fresh well-formed-act-ins-fresh well-formed-task-ins-fresh well-formed-run-ins-fresh
            well-formed-bump well-formed-insert-edge-fresh well-formed-fork-del]]
  (prim! HKW o nil))
(prim! HKW 'well-formed-insert-edge-checked '(hkwr-insert-edge-checked hkc hke w e R))
(prim! HKW 'well-formed-remove-edge '(hkwr-remove-edge hkc hke w x R))
(prim! HKW 'well-formed-mark-edge '(hkwr-mark-edge hkc hke w x R))
(prim! HKW 'well-formed-unmark-edge '(hkwr-unmark-edge hkc hke w x R))
(prim! HKW 'well-formed-drop-cred-edges '(hkwr-drop-cred hkc hke w a R))
(prim! HKW 'well-formed-drop-act '(hkwr-drop-act hkc hke w a R))
(prim! HKW 'well-formed-drop-edges '(hkwr-drop-edges hkc hke w p R))
(prim! HKW 'well-formed-comp-del-unref '(hkwr-comp-del hkc hke w x R))
(prim! HKW 'well-formed-filter-world '(hkwr-filter-world hkc hke w K R))
;; dispatch-epoch-kept on the generic tree: a computation edit keeps dispatch-epoch-kept by comp-facts's key lemmas (as comp-facts's sites)
(tree/part! HKW
  :sites (tree/row-sites 'well-formed-comp-upd (constantly true)
                         (fn [F] (if (contains? gd-cm (gd-fhead F))
                                   (list 'dispatch-epoch-kept-comp-upd-m 'hkc 'hke 'w 'x F 'hid 'hp (gd-lapp F (symbol (str (gd-fhead F) "-gcm"))) 'h0)
                                   (list 'dispatch-epoch-kept-comp-upd 'hkc 'hke 'w 'x F 'hid 'hp '(fn [c :- CompRow] (Eq.refl (gdkey c))) 'h0)))))
(tree/restate! HKW '[well-formed-cancel-pred well-formed-cut-suffix well-formed-consume-entry])

(a/theorem dispatch-epoch-kept-ok-new [kc :- Nat, ke :- Nat, k :- GDK] (=> (= (dispatch-epoch-kept-one kc ke k) true) (= (comp-facts-ok-new kc ke k) true))
  (intro h)
  (simp only [dispatch-epoch-kept-one Bool.or_eq_true Bool.and_eq_true] at h)
  (cases h)
  (case [inl a1] (simp only [comp-facts-ok-new a1 Bool.true_or]))
  (case [inr a1]
    (cases he (Nat.beq (:epoch k) ke))
    (case [false] (simp only [comp-facts-ok-new he Bool.not_false Bool.true_or Bool.or_true]))
    (case [true]
      (have e := (Nat.eq_of_beq_eq_true he))
      (have d (= (Nat.beq (:done k) (:epoch k)) false)) (rw [e]) (exact (bnot-true _ (And.right a1)))
      (simp only [comp-facts-ok-new d Bool.not_false Bool.or_true]))))
(a/theorem comp-facts-setrun-c [rs :- (List RunRow), n :- Nat, k :- GDK, c :- Nat, e :- Nat, ei :- Nat]
  (=> (= (comp-facts-c (tbl-ins (new-run-row n c e (+ n 1) ei) rs) (+ (+ n 1) 1) k) true)
      (= (tbl-all (fn [r :- RunRow] (Nat.blt (:id r) n)) rs) true) (= (:id k) c)
      (= (comp-facts-c (tbl-ins (new-run-row n c e (+ n 1) ei) rs) (+ (+ n 1) 1) (GDK.mk (:id k) n (:epoch k) (:done k))) true))
  (intros hc hb hi)
  (have p := (comp-facts-c-parts _ _ _ hc))
  (have g1 (= (comp-facts-dle (GDK.mk (:id k) n (:epoch k) (:done k))) true)) (exact (And.left p))
  (have g2 (= (Nat.blt (:run (GDK.mk (:id k) n (:epoch k) (:done k))) (+ (+ n 1) 1)) true))
  (apply comp-facts-blt-of) (show (< n (+ (+ n 1) 1))) (omega)
  (have g3 (= (tbl-all (comp-facts-rof (GDK.mk (:id k) n (:epoch k) (:done k))) (tbl-ins (new-run-row n c e (+ n 1) ei) rs)) true))
  (simp only [tbl-ins tbl-all comp-facts-rof new-run-row hi Nat.beq_refl Bool.or_true Bool.true_and])
  (apply (tbl-all-mono RunRow _ _ _ rs hb))
  (intros r hr)
  (have z := (comp-facts-beq-lt2 _ _ (comp-facts-lt-of _ _ hr)))
  (simp only [comp-facts-rof z Bool.not_false Bool.true_or])
  (have g4 (= (comp-facts-cde (tbl-ins (new-run-row n c e (+ n 1) ei) rs) (GDK.mk (:id k) n (:epoch k) (:done k))) true))
  (have q := (And.right (And.right (And.right p)))) (simp only [comp-facts-cde] at q) (simp only [comp-facts-cde]) (exact q)
  (exact (comp-facts-c-intro _ _ _ g1 g2 g3 g4)))

(a/theorem comp-facts-new-run-of [w :- World, c :- CompRow, ei :- Nat]
  (=> (= (dispatch-epoch-kept (:id c) (:epoch c) w) true) (= (comp-facts w) true) (= (comp-facts (new-run-of w c ei)) true))
  (intros k h)
  (have hs := (comp-facts-well-formed w h))
  (have kr := (dispatch-epoch-kept-rest-of _ _ w k)) (simp only [dispatch-epoch-kept-rest Bool.and_eq_true] at kr)
  (have ho := (tbl-all-mono GDK (dispatch-epoch-kept-one (:id c) (:epoch c)) (comp-facts-ok-new (:id c) (:epoch c))
                (fn [x :- GDK, hx :- (= (dispatch-epoch-kept-one (:id c) (:epoch c) x) true)] (dispatch-epoch-kept-ok-new _ _ x hx)) _ (And.right kr)))
  (have h1 := (comp-facts-add-run-scope w (:id c) (:epoch c) 0 ei ho h))
  (have r1 := (gdk-parts _ _ _ (comp-facts-rest-of _ h1)))
  (have q1 := (And.right r1))
  (change (= (tbl-all (comp-facts-c (tbl-ins (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1))
                      (gdkeys (:comps w))) true) at q1)
  (rw [all-gdkeys] at q1)
  (have hb := (comp-facts-runs-below w hs))
  (have rr (= (comp-facts-rest (new-run-of w c ei)) true))
  (show (= (gdk (gdkeys (tbl-upd comp-id (:id c) (comp-set-run (:next-id w)) (:comps w)))
                (tbl-ins (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1)) true))
  (simp only [gdk (And.left r1) Bool.true_and])
  (rw [all-gdkeys])
  (exact (tbl-all-upd CompRow comp-id (:id c) (comp-set-run (:next-id w))
           (fn [x :- CompRow] (comp-facts-c (tbl-ins (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1) (gdkey x)))
           (fn [x :- CompRow] (comp-facts-c (tbl-ins (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1) (gdkey x)))
           (fn [x :- CompRow, hx :- (= (comp-facts-c (tbl-ins (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1) (gdkey x)) true),
                hi :- (= (Nat.beq (comp-id x) (:id c)) true)]
             (comp-facts-setrun-c (:runs w) (:next-id w) (gdkey x) (:id c) (:epoch c) ei hx hb (Nat.eq_of_beq_eq_true hi)))
           (fn [x :- CompRow, hx :- (= (comp-facts-c (tbl-ins (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1) (gdkey x)) true),
                hi :- (= (Nat.beq (comp-id x) (:id c)) false)] hx)
           (:comps w) q1))
  (exact (comp-facts-intro _ (well-formed-new-run-of w c ei hs) rr)))

(a/theorem dispatch-epoch-kept-start [w :- World, c :- CompRow]
  (=> (= (comp-facts w) true) (List.Mem c (:comps w)) (= (Nat.beq (:done-epoch c) (:epoch c)) false) (= (dispatch-epoch-kept (:id c) (:epoch c) w) true))
  (intros h hm hd)
  (have hs := (comp-facts-well-formed w h))
  (have p := (gdk-parts _ _ _ (comp-facts-rest-of w h)))
  (have q := (And.right p)) (rw [all-gdkeys] at q)
  (have hc0 := (tbl-all-mem CompRow (fn [x :- CompRow] (comp-facts-c (:runs w) (:next-id w) (gdkey x))) c (:comps w) q hm))
  (have dl := (And.left (comp-facts-c-parts _ _ _ hc0))) (simp only [comp-facts-dle gdkey Bool.and_eq_true] at dl)
  (have qc (= (dispatch-epoch-kept-one (:id c) (:epoch c) (gdkey c)) true))
  (simp only [dispatch-epoch-kept-one gdkey comp-facts-ble-refl hd Bool.not_false Bool.and_self Bool.or_true])
  (have u := (comp-facts-same-id w c (fn [x :- CompRow] (dispatch-epoch-kept-one (:id c) (:epoch c) (gdkey x))) hs hm qc))
  (have r (= (dispatch-epoch-kept-rest (:id c) (:epoch c) w) true))
  (simp only [dispatch-epoch-kept-rest (And.right dl) Bool.true_and])
  (rw [all-gdkeys])
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) u))
  (intros x hx)
  (cases hi (Nat.beq (comp-id x) (:id c)))
  (case [false] (have hi2 (= (Nat.beq (:id x) (:id c)) false)) (exact hi) (simp only [dispatch-epoch-kept-one gdkey hi2 Bool.not_false Bool.true_or]))
  (case [true] (simp only [same-id-then hi Bool.not_true Bool.false_or] at hx) (exact hx))
  (exact (dispatch-epoch-kept-intro _ _ w hs r)))

(tree/restate! GD '[well-formed-cancel-pred well-formed-cut-suffix well-formed-consume-entry])
(a/theorem comp-facts-dispatch-raw [w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (Nat.beq (:done-epoch c) (:epoch c)) false) (= (comp-facts w) true) (= (comp-facts (dispatch-raw w c)) true))
  (intros hm hd h)
  (have k0 := (dispatch-epoch-kept-start w c h hm hd))
  (have h1 := (comp-facts-cancel-pred w c h))
  (have k1 := (dispatch-epoch-kept-cancel-pred (:id c) (:epoch c) w c k0))
  (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
  (simp only [dispatch-raw he])
  (exact (comp-facts-new-run-of (cut-suffix (cancel-pred w c) (:id c) false 0 0) c 0
           (dispatch-epoch-kept-cut-suffix (:id c) (:epoch c) (cancel-pred w c) (:id c) false 0 0 k1)
           (comp-facts-cut-suffix (cancel-pred w c) (:id c) false 0 0 h1)))
  (simp only [dispatch-raw he])
  (exact (comp-facts-new-run-of (consume-entry (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e) c (entry-ei e)
           (dispatch-epoch-kept-consume-entry (:id c) (:epoch c) (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e
             (dispatch-epoch-kept-cut-suffix (:id c) (:epoch c) (cancel-pred w c) (:id c) true (:at e) (:id e) k1))
           (comp-facts-consume-entry (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e
             (comp-facts-cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e) h1)))))
(a/theorem comp-facts-t11-dispatch [w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (comp-facts w) true) (= (comp-facts (:world (t11-dispatch w cid fresh))) true))
  (intro h)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [t11-dispatch hc refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))))
  (simp only [t11-dispatch hc hg refuse]) (exact h)
  (have hd (= (Nat.beq (:done-epoch c) (:epoch c)) false))
  (simp only [needs-run Bool.and_eq_true] at hg) (exact (bnot-true _ (And.left (And.left (And.right (And.right hg))))))
  (simp only [t11-dispatch hc hg accept]) (exact (comp-facts-dispatch-raw w c (tbl-find-mem CompRow comp-id cid c (:comps w) hc) hd h)))

;; ---- T12: done-epoch := epoch for the completed current run's computation; its run is done and,
;; by i10's cur-ok (a run at C's epoch is C.run, unique ids), it was C's only run at that epoch
(a/defn comp-facts-noal [o :- Nat, e :- Nat, q :- RunRow] Bool
  (Bool.not (Bool.and (Nat.beq (:of q) o) (Bool.and (Nat.beq (:epoch q) e) (run-alive q)))))
(a/defn comp-facts-u1 [r :- RunRow, q :- RunRow] Bool (Bool.or (Nat.beq (:id q) (:id r)) (comp-facts-noal (:of r) (:epoch r) q)))
(a/defn comp-facts-cce [w :- World, r :- RunRow] Bool
  (match (comp-find w (:of r)) none false (some c) (Nat.beq (:epoch r) (:epoch c))))

(a/theorem comp-facts-result-c [rs :- (List RunRow), n :- Nat, c :- CompRow, ep :- Nat, res :- RunResult]
  (=> (= (comp-facts-c rs n (gdkey c)) true) (= ep (:epoch c)) (= (tbl-all (comp-facts-noal (:id c) (:epoch c)) rs) true)
      (= (comp-facts-c rs n (gdkey (comp-result-row res ep c))) true))
  (intros hc he hn)
  (have p := (comp-facts-c-parts _ _ _ hc))
  (have dl := (And.left p)) (simp only [comp-facts-dle gdkey Bool.and_eq_true] at dl)
  (have g1 (= (comp-facts-dle (gdkey (comp-result-row res ep c))) true))
  (simp only [comp-facts-dle gdkey comp-result-row he comp-facts-ble-refl (And.right dl) Bool.and_self])
  (have g4 (= (comp-facts-cde rs (gdkey (comp-result-row res ep c))) true))
  (simp only [comp-facts-cde gdkey comp-result-row he Nat.beq_refl Bool.not_true Bool.false_or])
  (apply (tbl-all-mono RunRow _ _ _ rs hn))
  (intros q hq) (simp only [comp-facts-noal] at hq) (simp only [comp-facts-ncur]) (exact hq)
  (exact (comp-facts-c-intro _ _ _ g1 (And.left (And.right p)) (And.left (And.right (And.right p))) g4)))

(tree/restate! GD '[well-formed-settle well-formed-cancel-res well-formed-nat-fold well-formed-fire-edge well-formed-task-upd])
(a/theorem comp-facts-complete-body [w :- World, r :- RunRow, res :- RunResult]
  (=> (= (Bool.or (Bool.not (comp-facts-cce w r)) (tbl-all (comp-facts-noal (:of r) (:epoch r)) (:runs w))) true) (= (comp-facts w) true)
      (= (comp-facts (:world (complete-body w r res))) true))
  (intros hpre h)
  (cases hc (comp-find w (:of r)))
  (case [none]
    (cases hk (task-find w (:of r)))
    (case [none] (simp only [complete-body hc hk]) (exact h))
    (case [some k]
      (simp only [complete-body hc hk complete-task])
      (exact (comp-facts-nat-fold (fire-edge res) (comp-facts-fire-edge res) _ _
               (comp-facts-cancel-res _ r (comp-facts-task-upd w (:id k) (task-result-row res) (task-result-row-id res) h))))))
  (case [some c]
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [complete-body hc he]) (exact h))
    (case [true]
      (have hs := (comp-facts-well-formed w h))
      (have mc := (tbl-find-mem CompRow comp-id (:of r) c (:comps w) hc))
      (have ic (= (:id c) (:of r))) (exact (tbl-find-id CompRow comp-id (:of r) c (:comps w) hc))
      (have ee := (Nat.eq_of_beq_eq_true he))
      (simp only [comp-facts-cce hc he Bool.not_true Bool.false_or] at hpre)
      (have hn (= (tbl-all (comp-facts-noal (:id c) (:epoch c)) (:runs w)) true)) (rw [ic]) (rw [← ee]) (exact hpre)
      (have p := (gdk-parts _ _ _ (comp-facts-rest-of w h)))
      (have q := (And.right p)) (rw [all-gdkeys] at q)
      (have hc0 := (tbl-all-mem CompRow (fn [x :- CompRow] (comp-facts-c (:runs w) (:next-id w) (gdkey x))) c (:comps w) q mc))
      (have u := (comp-facts-same-id w c (fn [x :- CompRow] (comp-facts-c (:runs w) (:next-id w) (gdkey (comp-result-row res (:epoch r) x)))) hs mc
                   (comp-facts-result-c (:runs w) (:next-id w) c (:epoch r) res hc0 ee hn)))
      (have r1 (= (comp-facts-rest (comp-upd w (:id c) (comp-result-row res (:epoch r)))) true))
      (show (= (gdk (gdkeys (tbl-upd comp-id (:id c) (comp-result-row res (:epoch r)) (:comps w))) (:runs w) (:next-id w)) true))
      (simp only [gdk (And.left p) Bool.true_and])
      (rw [all-gdkeys])
      (exact (comp-facts-upd-same (:id c) (comp-result-row res (:epoch r)) _ _
               (fn [x :- CompRow, hx :- (= (comp-facts-c (:runs w) (:next-id w) (gdkey x)) true)] hx) (:comps w) q u))
      (have h1 := (comp-facts-intro _ (well-formed-comp-upd w (:id c) (comp-result-row res (:epoch r)) (comp-result-row-id res (:epoch r))
                                (comp-result-row-pending res (:epoch r)) hs) r1))
      (simp only [complete-body hc he complete-comp])
      (exact (comp-facts-settle _ (:id c) _ (comp-facts-cancel-res _ r h1))))))

(a/theorem comp-facts-noal-done [o :- Nat, e :- Nat, q :- RunRow] (= (comp-facts-noal o e (run-complete-row q)) true)
  (simp [comp-facts-noal run-complete-row run-alive act-done]))
(a/theorem comp-facts-u1-ne [r :- RunRow, q :- RunRow]
  (=> (= (comp-facts-u1 r q) true) (= (Nat.beq (run-id q) (:id r)) false) (= (comp-facts-noal (:of r) (:epoch r) q) true))
  (intros h1 h2)
  (have h3 (= (Nat.beq (:id q) (:id r)) false)) (exact h2)
  (simp only [comp-facts-u1 h3 Bool.false_or] at h1) (exact h1))
(a/theorem comp-facts-noal-upd [r :- RunRow, rs :- (List RunRow)]
  (=> (= (tbl-all (comp-facts-u1 r) rs) true) (= (tbl-all (comp-facts-noal (:of r) (:epoch r)) (tbl-upd run-id (:id r) run-complete-row rs)) true))
  (intro h)
  (exact (tbl-all-upd RunRow run-id (:id r) run-complete-row (comp-facts-u1 r) (comp-facts-noal (:of r) (:epoch r))
           (fn [q :- RunRow, h1 :- (= (comp-facts-u1 r q) true), h2 :- (= (Nat.beq (run-id q) (:id r)) true)] (comp-facts-noal-done (:of r) (:epoch r) q))
           (fn [q :- RunRow, h1 :- (= (comp-facts-u1 r q) true), h2 :- (= (Nat.beq (run-id q) (:id r)) false)] (comp-facts-u1-ne r q h1 h2))
           rs h)))
(a/theorem comp-facts-u1-of-i10-current [w :- World, r :- RunRow]
  (=> (= (i10-current w) true) (List.Mem r (:runs w)) (= (Bool.or (Bool.not (comp-facts-cce w r)) (tbl-all (comp-facts-u1 r) (:runs w))) true))
  (intros h mr)
  (cases hc (comp-find w (:of r)))
  (case [none] (simp only [comp-facts-cce hc Bool.not_false Bool.true_or]))
  (case [some c]
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [comp-facts-cce hc he Bool.not_false Bool.true_or]))
    (case [true]
      (simp only [comp-facts-cce hc he Bool.not_true Bool.false_or])
      (have mc := (tbl-find-mem CompRow comp-id (:of r) c (:comps w) hc))
      (have ic (= (:id c) (:of r))) (exact (tbl-find-id CompRow comp-id (:of r) c (:comps w) hc))
      (have ee := (Nat.eq_of_beq_eq_true he))
      (have pr := (rc-parts _ _ (i10-current-run-key r) (i10-current-comp-key c) (i10-current-exempt-rc _ _ w r c h mr mc) (Eq.refl false)))
      (have hor (= (Nat.beq (:of (i10-current-run-key r)) (:id (i10-current-comp-key c))) true)) (show (= (Nat.beq (:of r) (:id c)) true)) (rw [ic]) (exact (Nat.beq_refl _))
      (have cr := (And.left (cur-eq _ (i10-current-run-key r) (i10-current-comp-key c) (And.left pr) hor he)))
      (apply (all-of-mem RunRow _ (:runs w)))
      (intros q mq)
      (simp only [comp-facts-u1 Bool.or_eq_true])
      (cases hi (Nat.beq (:id q) (:id r)))
      (case [true] (exact (Or.inl (rfl))))
      (case [false]
        (apply Or.inr)
        (cases hq (Bool.and (Nat.beq (:of q) (:of r)) (Bool.and (Nat.beq (:epoch q) (:epoch r)) (run-alive q))))
        (case [false] (simp only [comp-facts-noal hq Bool.not_false]))
        (case [true]
          (simp only [Bool.and_eq_true] at hq)
          (have pq := (rc-parts _ _ (i10-current-run-key q) (i10-current-comp-key c) (i10-current-exempt-rc _ _ w q c h mq mc) (Eq.refl false)))
          (have hoq (= (Nat.beq (:of (i10-current-run-key q)) (:id (i10-current-comp-key c))) true))
          (show (= (Nat.beq (:of q) (:id c)) true)) (rw [ic]) (exact (And.left hq))
          (have heq (= (Nat.beq (:epoch (i10-current-run-key q)) (:epoch (i10-current-comp-key c))) true))
          (show (= (Nat.beq (:epoch q) (:epoch c)) true)) (rw [← ee]) (exact (And.left (And.right hq)))
          (have cq := (And.left (cur-eq _ (i10-current-run-key q) (i10-current-comp-key c) (And.left pq) hoq heq)))
          (have e2 (= (:id q) (:id r))) (exact (Eq.trans (Eq.symm cq) cr))
          (rw [e2] at hi) (simp [Nat.beq_refl] at hi))))))

(tree/restate! GD '[well-formed-finalize-if-final well-formed-retire-after well-formed-run-cascade])
(a/theorem comp-facts-complete-raw [w :- World, r :- RunRow, res :- RunResult]
  (=> (= (Bool.or (Bool.not (comp-facts-cce w r)) (tbl-all (comp-facts-u1 r) (:runs w))) true) (= (comp-facts w) true) (= (comp-facts (complete-raw w r res)) true))
  (intros hpre h)
  (have h0 := (comp-facts-run-upd-m w (:id r) run-complete-row run-complete-row-id run-complete-row-grm h))
  (have ce (= (comp-facts-cce (run-upd w (:id r) run-complete-row) r) (comp-facts-cce w r))) (rfl)
  (have p2 (= (Bool.or (Bool.not (comp-facts-cce (run-upd w (:id r) run-complete-row) r))
                       (tbl-all (comp-facts-noal (:of r) (:epoch r)) (:runs (run-upd w (:id r) run-complete-row)))) true))
  (cases hc (comp-facts-cce w r))
  (case [false] (simp only [ce hc Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [hc Bool.not_true Bool.false_or] at hpre)
    (simp only [ce hc Bool.not_true Bool.false_or])
    (exact (comp-facts-noal-upd r (:runs w) hpre)))
  (simp only [complete-raw])
  (exact (comp-facts-finalize-if-final _ (:of r) (comp-facts-run-cascade _ _ (comp-facts-retire-after _ (:id r) (comp-facts-complete-body _ r res p2 h0))))))
(tree/restate! GD '[well-formed-retire-pre well-formed-run-cascade])
(a/theorem comp-facts-retire-one [v :- Nat, w :- World, rid :- Nat]
  (=> (= (comp-facts w) true) (= (comp-facts (retire-one v w rid)) true))
  (intro h)
  (cases hf (run-find w rid))
  (case [none] (simp only [retire-one hf]) (exact h))
  (case [some r]
    (have hp := (comp-facts-retire-pre w r h))
    
    (cases hf1 (run-find (retire-pre w r) rid))
    (case [none] (simp only [retire-one hf hf1]) (exact hp))
    (case [some r1]
      (have hm1 := (retire-r1-mem w r r1 rid hf1))
      (have hn1 := (retire-r1-noact w r r1 rid hf hf1))
      (have ht1 := (task-final-res-tag (retire-pre w r) (:of r1) v))
      (cases ha (Bool.and (run-alive r1) (run-of-local (retire-pre w r) r1)))
      (case [true] (simp only [retire-one hf hf1 ha]) (have hnc := (local-run-nocomp _ r1 (comp-facts-well-formed _ hp) (bool-and-right _ _ ha)))
      (have pre (= (Bool.or (Bool.not (comp-facts-cce (retire-pre w r) r1)) (tbl-all (comp-facts-u1 r1) (:runs (retire-pre w r)))) true))
      (simp only [comp-facts-cce hnc Bool.not_false Bool.true_or])
      (exact (comp-facts-complete-raw _ r1 _ pre hp)))
      (case [false] (simp only [retire-one hf hf1 ha t13-retire]) (exact (comp-facts-run-cascade _ _ hp))))))

(a/theorem comp-facts-t12-complete [w :- World, st :- Nat, tag :- Nat, v :- Nat]
  (=> (= (i10-current w) true) (= (comp-facts w) true) (= (comp-facts (:world (t12-complete w st tag v))) true))
  (intros hg h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t12-complete ht refuse]) (exact h)
  (cases hn (run-normal r))
  (simp only [t12-complete ht hn refuse]) (exact h)
  (simp only [t12-complete ht hn accept])
  (exact (comp-facts-complete-raw w r _ (comp-facts-u1-of-i10-current w r hg (And.left (tok-facts w st r ht))) h)))

;; ---- reactivation (done-epoch := epoch on an idle computation): no alive run (i7-idle's a7, threaded)
(a/theorem comp-facts-noal-idle [w :- World, c :- CompRow]
  (=> (= (i7-idle w) true) (List.Mem c (:comps w)) (= (:idle c) true) (= (tbl-all (comp-facts-noal (:id c) (:epoch c)) (:runs w)) true))
  (intros h mc hi)
  (have p := (i7-idle-keys-ok-parts _ _ _ (i7-idle-rest-of w h)))
  (apply (tbl-all-mono RunRow (a7-one (:comps w)) _ _ (:runs w) (And.left p)))
  (intros q hq)
  (cases ha (Bool.and (Nat.beq (:of q) (:id c)) (Bool.and (Nat.beq (:epoch q) (:epoch c)) (run-alive q))))
  (case [false] (simp only [comp-facts-noal ha Bool.not_false]))
  (case [true]
    (simp only [Bool.and_eq_true] at ha)
    (simp only [a7-one (And.right (And.right ha)) Bool.not_true Bool.false_or awake] at hq)
    (have z := (tbl-all-mem CompRow (not-idle-if-id (:of q)) c (:comps w) hq mc))
    (have e := (Nat.eq_of_beq_eq_true (And.left ha)))
    (simp only [not-idle-if-id] at z) (rw [e] at z)
    (simp [Nat.beq_refl hi] at z)))
(a/theorem comp-facts-react-c [rs :- (List RunRow), n :- Nat, c :- CompRow]
  (=> (= (comp-facts-c rs n (gdkey c)) true) (= (tbl-all (comp-facts-noal (:id c) (:epoch c)) rs) true) (= (comp-facts-c rs n (gdkey (comp-react-row c))) true))
  (intros hc hn)
  (have p := (comp-facts-c-parts _ _ _ hc))
  (have dl := (And.left p)) (simp only [comp-facts-dle gdkey Bool.and_eq_true] at dl)
  (have g1 (= (comp-facts-dle (gdkey (comp-react-row c))) true))
  (simp only [comp-facts-dle gdkey comp-react-row comp-facts-ble-refl (And.right dl) Bool.and_self])
  (have g4 (= (comp-facts-cde rs (gdkey (comp-react-row c))) true))
  (simp only [comp-facts-cde gdkey comp-react-row Nat.beq_refl Bool.not_true Bool.false_or])
  (apply (tbl-all-mono RunRow _ _ _ rs hn))
  (intros q hq) (simp only [comp-facts-noal] at hq) (simp only [comp-facts-ncur]) (exact hq)
  (exact (comp-facts-c-intro _ _ _ g1 (And.left (And.right p)) (And.left (And.right (And.right p))) g4)))
(tree/restate! GD '[well-formed-react-edges])
(a/theorem comp-facts-react-one [w :- World, c :- CompRow]
  (=> (= (i7-idle w) true) (List.Mem c (:comps w)) (= (:idle c) true) (= (comp-facts w) true) (= (comp-facts (react-one w c)) true))
  (intros hg mc hi h)
  (have hs := (comp-facts-well-formed w h))
  (have p := (gdk-parts _ _ _ (comp-facts-rest-of w h)))
  (have q := (And.right p)) (rw [all-gdkeys] at q)
  (have hc0 := (tbl-all-mem CompRow (fn [x :- CompRow] (comp-facts-c (:runs w) (:next-id w) (gdkey x))) c (:comps w) q mc))
  (have u := (comp-facts-same-id w c (fn [x :- CompRow] (comp-facts-c (:runs w) (:next-id w) (gdkey (comp-react-row x)))) hs mc
               (comp-facts-react-c (:runs w) (:next-id w) c hc0 (comp-facts-noal-idle w c hg mc hi))))
  (have r1 (= (comp-facts-rest (comp-upd w (:id c) comp-react-row)) true))
  (show (= (gdk (gdkeys (tbl-upd comp-id (:id c) comp-react-row (:comps w))) (:runs w) (:next-id w)) true))
  (simp only [gdk (And.left p) Bool.true_and])
  (rw [all-gdkeys])
  (exact (comp-facts-upd-same (:id c) comp-react-row _ _ (fn [x :- CompRow, hx :- (= (comp-facts-c (:runs w) (:next-id w) (gdkey x)) true)] hx) (:comps w) q u))
  (have h1 := (comp-facts-intro _ (well-formed-comp-upd w (:id c) comp-react-row comp-react-row-id comp-react-row-pending hs) r1))
  (simp only [react-one])
  (exact (comp-facts-react-edges (:validity c) (comp-upd w (:id c) comp-react-row) (:id c) h1)))
(a/theorem comp-facts-react-loop [fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)] (=> (= (i7-idle w) true) (= (comp-facts w) true) (= (comp-facts (react-loop fuel w q)) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w q hg hw) (simp only [react-loop]) (exact hw)
  (intros w q hg hw)
  (cases q)
  (simp only [react-loop]) (exact hw)
  (rename_i x t)
  (cases hc (comp-find w x)) (case' [some c]) (case' [none])
  (simp only [react-loop hc]) (exact (ih w t hg hw))
  (cases hi (:idle c))
  (simp only [react-loop hc hi]) (exact (ih w t hg hw))
  (have mc := (tbl-find-mem CompRow comp-id x c (:comps w) hc))
  (simp only [react-loop hc hi])
  (exact (ih (react-one w c) _ (i7-idle-react-one w c hg) (comp-facts-react-one w c hg mc hi hw))))
(a/theorem comp-facts-demand-reactive [w :- World, d :- Nat]
  (=> (= (i7-idle w) true) (= (comp-facts w) true) (= (comp-facts (demand-reactive w d)) true))
  (intros hg h)
  (cases hc (comp-find w d)) (case' [some c]) (case' [none])
  (simp only [demand-reactive hc]) (exact h)
  (cases hi (:idle c))
  (simp only [demand-reactive hc hi]) (exact h)
  (cases hv (valid-idle w c))
  (simp only [demand-reactive hc hi hv]) (exact (comp-facts-comp-upd-m w d comp-demand-row comp-demand-row-id comp-demand-row-pending comp-demand-row-gcm h))
  (simp only [demand-reactive hc hi hv]) (exact (comp-facts-react-loop (react-fuel w) w _ hg h)))
(a/theorem comp-facts-df [ds :- (List Nat)]
  (forall [w :- World] (=> (= (i7-idle w) true) (= (comp-facts w) true) (= (comp-facts (nat-fold demand-reactive w ds)) true)))
  (induction ds)
  (case [nil] (intros w hg h) (simp only [nat-fold]) (exact h))
  (case [cons x t ih]
    (intros w hg h) (simp only [nat-fold])
    (exact (ih (demand-reactive w x) (i7-idle-demand-reactive w x hg) (comp-facts-demand-reactive w x hg h)))))
(a/theorem comp-facts-await-pre [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (i7-idle w) true) (= (comp-facts w) true) (= (comp-facts (await-pre w r ds mode k mine)) true))
  (intros hg h)
  (have h1 := (comp-facts-run-upd-m w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (comp-facts-rmono-key q (run-tick q) (Eq.refl (gdrk q)))) h))
  (have g1 := (i7-idle-run-upd w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (i7-idle-run-key q))) hg))
  (have he (= (act-id (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine))
              (:next-id (run-upd w (:id r) run-tick))))
  (rfl)
  (simp only [await-pre])
  (exact (comp-facts-df (nat-distinct ds) _ (i7-idle-act-ins-fresh _ _ he g1) (comp-facts-act-ins-fresh _ _ he h1))))
(tree/restate! GD '[well-formed-await-wire well-formed-await-post])
(a/theorem comp-facts-await-raw [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (i7-idle w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (comp-facts w) true) (= (comp-facts (await-raw w r ds mode k mine)) true))
  (intros hg hm hal h)
  (have hs := (comp-facts-well-formed w h))
  (have k0 := (awaiting-run-alive-intro (:id r) w hs (run-ok-of-mem w r hs hm hal)))
  (have k1 := (awaiting-run-alive-await-wire (:id r) r (:next-id w) mode k (nat-distinct ds)
                (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (awaiting-run-alive-await-pre (:id r) w r ds mode k mine k0)))
  (have h1 := (comp-facts-await-wire r (:next-id w) mode k (nat-distinct ds)
                (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (comp-facts-await-pre w r ds mode k mine hg h)))
  (exact (comp-facts-await-post (:next-id w) (:id r) ds (await-acc w r ds mode k mine) k1 h1)))
(tree/restate! GD '[well-formed-insert-edge-checked well-formed-fire-edge])
(a/theorem comp-facts-host-await-raw [w :- World, d :- Nat]
  (=> (= (i7-idle w) true) (= (comp-facts w) true) (= (comp-facts (host-await-raw w d)) true))
  (intros hg h)
  (have h1 (= (comp-facts (host-await-dem w d)) true))
  (exact (comp-facts-demand-reactive _ d (i7-idle-insert-edge-checked w (host-wait-edge d) (Eq.refl true) hg) (comp-facts-insert-edge-checked w (host-wait-edge d) h)))
  (cases hr (fast-ready (host-await-dem w d) d))
  (simp only [host-await-raw hr]) (exact h1)
  (simp only [host-await-raw hr]) (exact (comp-facts-fire-edge _ _ (:next-id w) h1)))
(tree/restate! GD '[well-formed-insert-edge-fresh well-formed-fire-edge])
(a/theorem comp-facts-t8-observe-any-kind [w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (i7-idle w) true) (= (comp-facts w) true) (= (comp-facts (:world (t8-observe-any-kind w d cb fresh))) true))
  (intros hg7 h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
  (simp only [t8-observe-any-kind hg refuse]) (exact h)
  (have he (= (edge-ok-in w (observe-edge w d cb)) true))
  (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
  (have h1 := (comp-facts-demand-reactive _ d (i7-idle-insert-edge-fresh w (observe-edge w d cb) (Eq.refl true) he hg7)
                (comp-facts-insert-edge-fresh w (observe-edge w d cb) he h)))
  (simp only [t8-observe-any-kind hg accept observe-raw])
  (cases hr (deb-ready (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) d))
  (simp only [hr]) (exact h1)
  (simp only [hr]) (exact (comp-facts-fire-edge _ _ (:next-id w) h1)))


;; ===========================================================================
;; Part E. The copy, Rule R, the step
;; ===========================================================================

(tree/restate! GD '[well-formed-raw well-formed-normalize])

(a/theorem comp-facts-rule-r-round [w :- World]
  (=> (= (comp-facts w) true) (= (filter-safe (normalize w)) true) (= (comp-facts (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (comp-facts-filter-world _ (keep-fn (normalize w)) (comp-facts-normalize w h) hf)))
(a/theorem comp-facts-rule-r-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (comp-facts w0) true) (= (rounds-safe-loop fuel w0) true) (= (comp-facts (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (comp-facts-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (comp-facts-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))
(a/theorem comp-facts-rule-r [w :- World] (=> (= (comp-facts w) true) (= (rule-r-safe w) true) (= (comp-facts (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (comp-facts-rule-r-loop (rule-r-fuel w) w h hs)))
(a/theorem step-comp-facts [w :- World, it :- Item]
  (=> (= (i7-idle w) true) (= (i10-current w) true) (= (comp-facts w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (comp-facts (:world (world-step w it))) true))
  (intros hg7 hg10 h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (comp-facts-rule-r (:world (raw w it)) (comp-facts-raw w it hg7 hg10 h) hs))))
(a/theorem comp-facts-empty [] (= (comp-facts empty-world) true) (rfl))

;; the context facts from chain-to-i8-closed: i7-idle (in chain-start's round-facts) and i10-current (chain-to-i10-current)
(a/theorem chain-to-i8-closed-ctx [w :- World] (=> (= (chain-to-i8-closed w) true) (And (= (chain-start w) true) (= (i10-current w) true)))
  (intro h)
  (have ph := (And.left (chain-to-i8-closed-parts w h)))
  (have pg := (chain-to-i1-detached-closed-parts w (And.left (chain-to-i1-runs-parts w ph))))
  (have pf := (chain-to-i5-dep-final-parts w (And.left pg)))
  (have pe := (chain-to-i1-scopes-parts w (And.left pf)))
  (have pd := (chain-to-i11a-parts w (And.left pe)))
  (exact (chain-to-i10-current-parts w (And.left pd))))
(a/theorem chain-to-i8-closed-i7-idle [w :- World] (=> (= (chain-to-i8-closed w) true) (= (i7-idle w) true))
  (intro h)
  (have pb := (chain-start-parts w (And.left (chain-to-i8-closed-ctx w h))))
  (exact (And.left (round-facts-parts w (And.right (And.right (And.right (And.right pb))))))))

;; the combined bundle: chain-to-comp-facts = chain-to-i8-closed && comp-facts (no honest hypothesis)
(a/defn chain-to-comp-facts [w :- World] Bool (Bool.and (chain-to-i8-closed w) (comp-facts w)))
(a/theorem chain-to-comp-facts-parts [w :- World] (=> (= (chain-to-comp-facts w) true) (And (= (chain-to-i8-closed w) true) (= (comp-facts w) true)))
  (intro h) (simp only [chain-to-comp-facts Bool.and_eq_true] at h) (exact h))
(a/theorem chain-to-comp-facts-empty [] (= (chain-to-comp-facts empty-world) true) (rfl))
(a/theorem step-chain-to-comp-facts [w :- World, it :- Item] (=> (= (chain-to-comp-facts w) true) (= (chain-to-comp-facts (:world (world-step w it))) true))
  (intro h)
  (have p := (chain-to-comp-facts-parts w h))
  (have c := (chain-to-i8-closed-ctx w (And.left p)))
  (have a1 := (step-chain-to-i8-closed w it (And.left p)))
  (have a2 := (step-comp-facts w it (chain-to-i8-closed-i7-idle w (And.left p)) (And.right c) (And.right p) (step-rule-r-safe w it (And.left c))))
  (simp only [chain-to-comp-facts a1 a2 Bool.and_self]))

;; Theorem (the aux facts of the h-mark plan, PLAN z59 (0)): after every step from a chain-to-comp-facts world,
;; every computation has done-epoch <= epoch, 0 < epoch, and has no alive run at its epoch once
;; its result is set (done-epoch = epoch)
(a/defn comp-facts-fact [w :- World, c :- CompRow] Bool
  (Bool.and (Nat.ble (:done-epoch c) (:epoch c))
            (Bool.or (Bool.not (Nat.beq (:done-epoch c) (:epoch c))) (tbl-all (comp-facts-noal (:id c) (:epoch c)) (:runs w)))))
(a/theorem comp-facts-facts [w :- World] (=> (= (comp-facts w) true) (= (tbl-all (comp-facts-fact w) (:comps w)) true))
  (intro h)
  (have p := (gdk-parts _ _ _ (comp-facts-rest-of w h)))
  (have q := (And.right p)) (rw [all-gdkeys] at q)
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) q))
  (intros c hc)
  (have pc := (comp-facts-c-parts _ _ _ hc))
  (have dl := (And.left pc)) (simp only [comp-facts-dle gdkey Bool.and_eq_true] at dl)
  (have cd := (And.right (And.right (And.right pc))))
  (cases hd (Nat.beq (:done-epoch c) (:epoch c)))
  (case [false] (simp only [comp-facts-fact (And.left dl) hd Bool.not_false Bool.true_or Bool.and_self]))
  (case [true]
    (simp only [comp-facts-cde gdkey hd Bool.not_true Bool.false_or] at cd)
    (simp only [comp-facts-fact (And.left dl) hd Bool.not_true Bool.false_or Bool.true_and])
    (apply (tbl-all-mono RunRow _ _ _ (:runs w) cd))
    (intros q hq) (simp only [comp-facts-ncur gdkey] at hq) (simp only [comp-facts-noal]) (exact hq)))
(a/theorem step-comp-facts-facts-total [w :- World, it :- Item]
  (=> (= (chain-to-comp-facts w) true) (= (tbl-all (comp-facts-fact (:world (world-step w it))) (:comps (:world (world-step w it)))) true))
  (intro h) (exact (comp-facts-facts _ (And.right (chain-to-comp-facts-parts _ (step-chain-to-comp-facts w it h))))))

;; ===========================================================================
;; Part F. For the h-mark proof (PLAN z59 (1)): the marking's dirty set is closed backwards
;; ===========================================================================

;; every visited node of the worklist closure is a root or a successor of a visited node (no
;; convergence needed): the T2/T3 final-state argument reads a marked edge's debtor this way
(a/defn rinv-par [succ :- (=> Nat (List Nat)), z :- Nat, y :- Nat] Bool (reach-mem z (succ y)))
(a/defn rinv-q [succ :- (=> Nat (List Nat)), roots :- (List Nat), seen :- (List Nat), z :- Nat] Bool
  (Bool.or (reach-mem z roots) (tbl-any (rinv-par succ z) seen)))
(a/theorem rinv-mono [succ :- (=> Nat (List Nat)), roots :- (List Nat), seen :- (List Nat), x :- Nat, z :- Nat]
  (=> (= (rinv-q succ roots seen z) true) (= (rinv-q succ roots (List.cons Nat x seen) z) true))
  (intro h)
  (simp only [rinv-q Bool.or_eq_true] at h)
  (simp only [rinv-q tbl-any Bool.or_eq_true])
  (cases h)
  (case [inl a1] (exact (Or.inl a1)))
  (case [inr a1] (exact (Or.inr (Or.inr a1)))))
(a/theorem reach-closure-inv [succ :- (=> Nat (List Nat)), roots :- (List Nat), fuel :- Nat]
  (forall [work :- (List Nat)] (forall [seen :- (List Nat)]
    (=> (forall [z :- Nat] (=> (= (reach-mem z seen) true) (= (rinv-q succ roots seen z) true)))
        (forall [z :- Nat] (=> (= (reach-mem z work) true) (= (rinv-q succ roots seen z) true)))
        (forall [v :- Nat] (=> (= (reach-mem v (ReachResult.visited (reach-closure fuel succ work seen))) true)
                               (= (rinv-q succ roots (ReachResult.visited (reach-closure fuel succ work seen)) v) true))))))
  (induction fuel)
  (case [zero]
    (intro work seen hs hw v hv)
    (cases work)
    (all_goals (simp only [reach-closure] at hv))
    (all_goals (simp only [reach-closure]))
    (all_goals (exact (hs v hv))))
  (case [succ n ih]
    (intro work seen hs hw v hv)
    (cases work)
    (case [nil] (simp only [reach-closure] at hv) (simp only [reach-closure]) (exact (hs v hv)))
    (case [cons x rest]
      (cases hm (reach-mem x seen))
      (case [true]
        (simp only [reach-closure hm] at hv) (simp only [reach-closure hm])
        (have hw2 (forall [z :- Nat] (=> (= (reach-mem z rest) true) (= (rinv-q succ roots seen z) true))))
        (intro z hz) (apply hw) (simp [reach-mem-cons hz])
        (exact (ih rest seen hs hw2 v hv)))
      (case [false]
        (simp only [reach-closure hm] at hv) (simp only [reach-closure hm])
        (have hx (= (rinv-q succ roots seen x) true)) (apply hw) (simp [reach-mem-cons Nat.beq_refl])
        (have hs2 (forall [z :- Nat] (=> (= (reach-mem z (List.cons Nat x seen)) true) (= (rinv-q succ roots (List.cons Nat x seen) z) true))))
        (intro z hz)
        (simp [reach-mem-cons] at hz)
        (rcases hz (or h1 h2))
        (subst h1) (exact (rinv-mono succ roots seen z z hx))
        (exact (rinv-mono succ roots seen x z (hs z h2)))
        (have hw2 (forall [z :- Nat] (=> (= (reach-mem z (HAppend.hAppend (succ x) rest)) true) (= (rinv-q succ roots (List.cons Nat x seen) z) true))))
        (intro z hz)
        (simp [reach-mem-app] at hz)
        (rcases hz (or h1 h2))
        (simp only [rinv-q tbl-any rinv-par h1 Bool.true_or Bool.or_true])
        (apply (rinv-mono succ roots seen x z)) (apply hw) (simp [reach-mem-cons h2])
        (exact (ih (HAppend.hAppend (succ x) rest) (List.cons Nat x seen) hs2 hw2 v hv))))))
(a/theorem reach-run-inv [fuel :- Nat, succ :- (=> Nat (List Nat)), roots :- (List Nat), v :- Nat]
  (=> (= (reach-mem v (ReachResult.visited (reach-run fuel succ roots))) true)
      (= (rinv-q succ roots (ReachResult.visited (reach-run fuel succ roots)) v) true))
  (intro hv)
  (apply (reach-closure-inv succ roots fuel roots (List.nil Nat) _ _ v hv))
  (intro z hz) (simp [reach-mem] at hz)
  (intro z hz) (simp only [rinv-q hz Bool.true_or]))
;; T2 (Z#59 a): a dirty computation is a creditor of an armed dep edge on the written source, or a
;; dep creditor of a dirty computation (whose in-edge is then a mark target); T3: the same for the cone
(a/theorem hm-dirty-back [w :- World, x :- Nat, z :- Nat]
  (=> (= (reach-mem z (dirty-set w x)) true)
      (= (rinv-q (dep-creditors (:edges w)) (armed-creditors (:edges w) x) (dirty-set w x) z) true))
  (intro h)
  (exact (reach-run-inv (+ (* 2 (edge-count (:edges w))) 1) (dep-creditors (:edges w)) (armed-creditors (:edges w) x) z h)))
(a/theorem hm-cone-back [w :- World, c :- Nat, z :- Nat]
  (=> (= (reach-mem z (cone-set w c)) true)
      (= (rinv-q (dep-creditors (:edges w)) (dep-creditors (:edges w) c) (cone-set w c) z) true))
  (intro h)
  (exact (reach-run-inv (+ (* 2 (edge-count (:edges w))) 1) (dep-creditors (:edges w)) (dep-creditors (:edges w) c) z h)))
