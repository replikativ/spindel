(ns spindel.v2.hm
  "L5's state facts through `world-step` (P11), kernel-checked (Init only). Part A-C: the auxiliary
  bundle `gd` (notes/PLAN.md, branch z59 (0)), the per-computation facts an h-mark proof needs:
    dle   done-epoch <= epoch, and 0 < epoch
    hrb   C.run is below the allocator (a fresh run is no computation's current run)
    rof   C.run names a run of C (or no run)
    cde   when done-epoch = epoch, C has no alive run at its epoch (by `of`, any run id)
  gd = inv-sample && gd-rest, every inv-sample lemma re-checked for gd by lit's copier (`GD`).
  Computation edits: a row function that keeps the id, keeps C.run or clears it, does not lower
  the epoch, and keeps done-epoch or clears it (`cmono`) is a frame; run edits that keep id, of and
  epoch and never revive (`rmono`) are frames. Overrides: T12's result row (done-epoch := epoch: the
  completed run is C.run by i10's cur-ok, so no other alive run is current), reactivation
  (done-epoch := epoch on an idle computation: no alive run, g7's a7), T5/T11 (a new run at C's
  epoch: C needs a run, done-epoch /= its epoch), new runs of tasks (their `of` is no computation).
  Threads: g7 (reactivation: T6, T8, T22) and g10r (T12) from the step's input (raw0 patched); T11's
  new run is at the epoch read before the predecessor's cancel: watch bundle `hkw c e` (rows with id
  c keep epoch >= e and done-epoch /= e) copied through cancel-pred/cut-suffix/consume-entry; parks
  reuse i8's KA. Theorems: step-gd (g7 w, g10r w, gd w, rule-r-safe raw -> gd (world-step w it)),
  p3j = p3i && gd with step-p3j / p3j-empty (no honest hypothesis), step-gd-facts-total.
  Part F (toward h-mark, PLAN z59 (1)): `reach-closure-inv`/`reach-run-inv` (a visited node is a
  root or a successor of a visited node; no convergence), `hm-dirty-back`, `hm-cone-back`.
  h-mark and h-mem2 themselves are not proved here (notes/PLAN.md, branch l5b)."
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
            [spindel.v2.i8 :refer :all]))

;; ===========================================================================
;; Part A. The auxiliary facts and their transfer lemmas
;; ===========================================================================

(a/structure GDK [] (id Nat) (run Nat) (epoch Nat) (done Nat))
(a/defn gdkey [c :- CompRow] GDK (GDK.mk (:id c) (:run c) (:epoch c) (:done-epoch c)))
(a/defn gdk-id [k :- GDK] Nat (:id k))
(a/defn gdkeys [cs :- (List CompRow)] (List GDK)
  (match cs [nil (List.nil GDK)] [(cons h t) (List.cons GDK (gdkey h) (gdkeys t))]))
(a/defn gd-dle [c :- GDK] Bool (Bool.and (Nat.ble (:done c) (:epoch c)) (Nat.blt 0 (:epoch c))))
(a/defn gd-rof [c :- GDK, r :- RunRow] Bool (Bool.or (Bool.not (Nat.beq (:id r) (:run c))) (Nat.beq (:of r) (:id c))))
(a/defn gd-ncur [c :- GDK, r :- RunRow] Bool
  (Bool.not (Bool.and (Nat.beq (:of r) (:id c)) (Bool.and (Nat.beq (:epoch r) (:epoch c)) (run-alive r)))))
(a/defn gd-cde [rs :- (List RunRow), c :- GDK] Bool
  (Bool.or (Bool.not (Nat.beq (:done c) (:epoch c))) (tbl-all (gd-ncur c) rs)))
(a/defn gd-c [rs :- (List RunRow), n :- Nat, c :- GDK] Bool
  (Bool.and (gd-dle c) (Bool.and (Nat.blt (:run c) n) (Bool.and (tbl-all (gd-rof c) rs) (gd-cde rs c)))))
(a/defn gdk [cs :- (List GDK), rs :- (List RunRow), n :- Nat] Bool
  (Bool.and (Nat.blt 0 n) (tbl-all (gd-c rs n) cs)))
(a/defn gd-rest [w :- World] Bool (gdk (gdkeys (:comps w)) (:runs w) (:next-id w)))
(a/defn gd [w :- World] Bool (Bool.and (inv-sample w) (gd-rest w)))

(a/theorem gd-sample [w :- World] (=> (= (gd w) true) (= (inv-sample w) true))
  (intro h) (simp only [gd Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem gd-rest-of [w :- World] (=> (= (gd w) true) (= (gd-rest w) true))
  (intro h) (simp only [gd Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem gd-intro [w :- World] (=> (= (inv-sample w) true) (= (gd-rest w) true) (= (gd w) true))
  (intros h1 h2) (simp only [gd h1 h2 Bool.and_self]))
(a/theorem gd-parts [w :- World]
  (=> (= (gd w) true) (And (= (inv-sample w) true) (= (gd-rest w) true)))
  (intro h) (exact (And.intro (gd-sample w h) (gd-rest-of w h))))

(a/theorem gdk-parts [cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (gdk cs rs n) true) (And (= (Nat.blt 0 n) true) (= (tbl-all (gd-c rs n) cs) true)))
  (intro h) (simp only [gdk Bool.and_eq_true] at h) (exact h))
(a/theorem gd-c-parts [rs :- (List RunRow), n :- Nat, c :- GDK]
  (=> (= (gd-c rs n c) true)
      (And (= (gd-dle c) true) (And (= (Nat.blt (:run c) n) true) (And (= (tbl-all (gd-rof c) rs) true) (= (gd-cde rs c) true)))))
  (intro h) (simp only [gd-c Bool.and_eq_true] at h) (exact h))
(a/theorem gd-c-intro [rs :- (List RunRow), n :- Nat, c :- GDK]
  (=> (= (gd-dle c) true) (= (Nat.blt (:run c) n) true) (= (tbl-all (gd-rof c) rs) true) (= (gd-cde rs c) true)
      (= (gd-c rs n c) true))
  (intros h1 h2 h3 h4) (simp only [gd-c h1 h2 h3 h4 Bool.and_self]))

;; Nat comparisons
(a/theorem gd-lt-of [a :- Nat, b :- Nat] (=> (= (Nat.blt a b) true) (< a b)) (intro h) (simp only [Nat.blt_eq] at h) (exact h))
(a/theorem gd-blt-of [a :- Nat, b :- Nat] (=> (< a b) (= (Nat.blt a b) true)) (intro h) (simp only [Nat.blt_eq]) (exact h))
(a/theorem gd-le-of [a :- Nat, b :- Nat] (=> (= (Nat.ble a b) true) (<= a b)) (intro h) (simp only [Nat.ble_eq] at h) (exact h))
(a/theorem gd-ble-of [a :- Nat, b :- Nat] (=> (<= a b) (= (Nat.ble a b) true)) (intro h) (simp only [Nat.ble_eq]) (exact h))

;; ---- computation rows: cmono c c' (id kept, run kept or cleared, epoch not lowered, done-epoch kept or cleared)
(a/defn gd-cmono [c :- GDK, d :- GDK] Bool
  (Bool.and (Nat.beq (:id d) (:id c))
   (Bool.and (Bool.or (Nat.beq (:run d) (:run c)) (Nat.beq (:run d) 0))
    (Bool.and (Nat.ble (:epoch c) (:epoch d))
              (Bool.or (Nat.beq (:done d) (:done c)) (Nat.beq (:done d) 0))))))

;; no run has id 0
(a/defn gd-rnz [r :- RunRow] Bool (Bool.not (Nat.beq (:id r) 0)))

(a/theorem gd-c-mono [rs :- (List RunRow), n :- Nat, c :- GDK, d :- GDK]
  (=> (= (Nat.blt 0 n) true) (= (tbl-all gd-rnz rs) true) (= (gd-cmono c d) true) (= (gd-c rs n c) true) (= (gd-c rs n d) true))
  (intros hn hz hm hc)
  (have p := (gd-c-parts rs n c hc))
  (simp only [gd-cmono Bool.and_eq_true Bool.or_eq_true] at hm)
  (have hid := (Nat.eq_of_beq_eq_true (And.left hm)))
  (have hr := (And.left (And.right hm)))
  (have he := (gd-le-of _ _ (And.left (And.right (And.right hm)))))
  (have hd := (And.right (And.right (And.right hm))))
  (have dl := (And.left p))
  (simp only [gd-dle Bool.and_eq_true] at dl)
  (have dl1 := (gd-le-of _ _ (And.left dl)))
  (have dl2 := (gd-lt-of _ _ (And.right dl)))
  (have hdd (<= (:done d) (:done c)))
  (cases hd)
  (case [inl q] (rw [(Nat.eq_of_beq_eq_true q)]) (exact (Nat.le_refl _)))
  (case [inr q] (rw [(Nat.eq_of_beq_eq_true q)]) (exact (Nat.zero_le _)))
  (have g1 (= (gd-dle d) true))
  (simp only [gd-dle Bool.and_eq_true])
  (exact (And.intro (gd-ble-of _ _ (Nat.le_trans hdd (Nat.le_trans dl1 he)))
                    (gd-blt-of _ _ (Nat.lt_of_lt_of_le dl2 he))))
  (have g2 (= (Nat.blt (:run d) n) true))
  (cases hr)
  (case [inl q] (rw [(Nat.eq_of_beq_eq_true q)]) (exact (And.left (And.right p))))
  (case [inr q] (rw [(Nat.eq_of_beq_eq_true q)]) (exact hn))
  (have g3 (= (tbl-all (gd-rof d) rs) true))
  (apply (tbl-all-mem-mono RunRow (both gd-rnz (gd-rof c)) (gd-rof d) rs))
  (intros r mr hb)
  (simp only [both Bool.and_eq_true] at hb)
  (simp only [gd-rof hid])
  (cases hr)
  (case [inl q] (rw [(Nat.eq_of_beq_eq_true q)]) (have z := (And.right hb)) (simp only [gd-rof] at z) (exact z))
  (case [inr q] (rw [(Nat.eq_of_beq_eq_true q)]) (have z := (And.left hb)) (simp only [gd-rnz] at z)
    (simp only [z Bool.true_or]))
  (exact (tbl-all-mono2 RunRow gd-rnz (gd-rof c) (both gd-rnz (gd-rof c))
           (fn [q :- RunRow, h1 :- (= (gd-rnz q) true), h2 :- (= (gd-rof c q) true)] (both-of RunRow gd-rnz (gd-rof c) q h1 h2))
           rs hz (And.left (And.right (And.right p)))))
  (have g4 (= (gd-cde rs d) true))
  (cases hde (Nat.beq (:done d) (:epoch d)))
  (case [false] (simp only [gd-cde hde Bool.not_false Bool.true_or]))
  (case [true]
    (have e1 := (Nat.eq_of_beq_eq_true hde))
    (cases hd)
    (case [inr q] (have e0 := (Nat.eq_of_beq_eq_true q)) (rw [e0] at e1) (rw [← e1] at he) (omega))
    (case [inl q]
      (have e0 := (Nat.eq_of_beq_eq_true q))
      (have ee (= (:epoch d) (:epoch c))) (omega)
      (have hc4 := (And.right (And.right (And.right p))))
      (have hce (= (Nat.beq (:done c) (:epoch c)) true)) (simp only [Nat.beq_eq]) (omega)
      (simp only [gd-cde hce Bool.not_true Bool.false_or] at hc4)
      (simp only [gd-cde hde Bool.not_true Bool.false_or])
      (apply (tbl-all-mono RunRow (gd-ncur c) (gd-ncur d) _ rs hc4))
      (intros r hr2)
      (simp only [gd-ncur hid ee]) (simp only [gd-ncur] at hr2) (exact hr2)))
  (exact (gd-c-intro rs n d g1 g2 g3 g4)))

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
(a/theorem gd-c-next [rs :- (List RunRow), n :- Nat, m :- Nat, c :- GDK]
  (=> (<= n m) (= (gd-c rs n c) true) (= (gd-c rs m c) true))
  (intros hl h)
  (have p := (gd-c-parts rs n c h))
  (have q := (gd-lt-of _ _ (And.left (And.right p))))
  (exact (gd-c-intro rs m c (And.left p) (gd-blt-of _ _ (Nat.lt_of_lt_of_le q hl)) (And.left (And.right (And.right p)))
           (And.right (And.right (And.right p))))))
(a/theorem gdk-next [cs :- (List GDK), rs :- (List RunRow), n :- Nat, m :- Nat]
  (=> (<= n m) (= (gdk cs rs n) true) (= (gdk cs rs m) true))
  (intros hl h)
  (have p := (gdk-parts cs rs n h))
  (simp only [gdk Bool.and_eq_true])
  (exact (And.intro (gd-blt-of _ _ (Nat.lt_of_lt_of_le (gd-lt-of _ _ (And.left p)) hl))
           (tbl-all-mono GDK (gd-c rs n) (gd-c rs m) (fn [c :- GDK, hc :- (= (gd-c rs n c) true)] (gd-c-next rs n m c hl hc))
             cs (And.right p)))))
(a/theorem gdk-sub [cs :- (List GDK), cs2 :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (=> (= (tbl-all (gd-c rs n) cs) true) (= (tbl-all (gd-c rs n) cs2) true)) (= (gdk cs rs n) true) (= (gdk cs2 rs n) true))
  (intros hs h)
  (have p := (gdk-parts cs rs n h))
  (simp only [gdk Bool.and_eq_true])
  (exact (And.intro (And.left p) (hs (And.right p)))))
(a/theorem gdk-comp-m [x :- Nat, f :- (=> CompRow CompRow),
                       hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                       hm :- (forall [c :- CompRow] (= (gd-cmono (gdkey c) (gdkey (f c))) true)),
                       cs :- (List CompRow), rs :- (List RunRow), n :- Nat]
  (=> (= (tbl-all gd-rnz rs) true) (= (gdk (gdkeys cs) rs n) true) (= (gdk (gdkeys (tbl-upd comp-id x f cs)) rs n) true))
  (intros hz h)
  (have p := (gdk-parts _ rs n h))
  (simp only [gdk Bool.and_eq_true])
  (apply And.intro) (exact (And.left p))
  (have q := (And.right p))
  (rw [all-gdkeys] at q) (rw [all-gdkeys])
  (exact (tbl-all-upd CompRow comp-id x f (fn [c :- CompRow] (gd-c rs n (gdkey c))) (fn [c :- CompRow] (gd-c rs n (gdkey c)))
           (fn [c :- CompRow, h1 :- (= (gd-c rs n (gdkey c)) true), h2 :- (= (Nat.beq (comp-id c) x) true)]
             (gd-c-mono rs n (gdkey c) (gdkey (f c)) (And.left p) hz (hm c) h1))
           (fn [c :- CompRow, h1 :- (= (gd-c rs n (gdkey c)) true), h2 :- (= (Nat.beq (comp-id c) x) false)] h1)
           cs q)))
(a/theorem gdk-del [x :- Nat, cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (gdk cs rs n) true) (= (gdk (tbl-del gdk-id x cs) rs n) true))
  (intro h)
  (exact (gdk-sub cs _ rs n (tbl-all-del GDK gdk-id x (gd-c rs n) (gd-c rs n)
                               (fn [c :- GDK, h1 :- (= (gd-c rs n c) true), h2 :- (= (Nat.beq (gdk-id c) x) false)] h1) cs) h)))
(a/theorem gdk-keep [K :- (=> Nat Bool), cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (gdk cs rs n) true) (= (gdk (tbl-keep K gdk-id cs) rs n) true))
  (intro h)
  (exact (gdk-sub cs _ rs n (tbl-all-keep GDK K gdk-id (gd-c rs n) (gd-c rs n)
                               (fn [c :- GDK, h1 :- (= (gd-c rs n c) true), h2 :- (= (K (gdk-id c)) true)] h1) cs) h)))

;; ---- run rows: rmono r r' (id, of, epoch kept; never revived)
(a/defn gd-rmono [r :- RunRow, q :- RunRow] Bool
  (Bool.and (Nat.beq (:id q) (:id r))
   (Bool.and (Nat.beq (:of q) (:of r)) (Bool.and (Nat.beq (:epoch q) (:epoch r)) (Bool.or (Bool.not (run-alive q)) (run-alive r))))))

;; the run part of gd-c, generic in the run list
(a/defn gd-cr [rs :- (List RunRow), c :- GDK] Bool (Bool.and (tbl-all (gd-rof c) rs) (gd-cde rs c)))
(a/theorem gd-c-runs [rs :- (List RunRow), rs2 :- (List RunRow), n :- Nat, c :- GDK]
  (=> (=> (= (gd-cr rs c) true) (= (gd-cr rs2 c) true)) (= (gd-c rs n c) true) (= (gd-c rs2 n c) true))
  (intros hs h)
  (have p := (gd-c-parts rs n c h))
  (have q (= (gd-cr rs c) true)) (simp only [gd-cr (And.left (And.right (And.right p))) (And.right (And.right (And.right p))) Bool.and_self])
  (have q2 := (hs q))
  (simp only [gd-cr Bool.and_eq_true] at q2)
  (exact (gd-c-intro rs2 n c (And.left p) (And.left (And.right p)) (And.left q2) (And.right q2))))
(a/theorem gdk-runs [cs :- (List GDK), rs :- (List RunRow), rs2 :- (List RunRow), n :- Nat]
  (=> (forall [c :- GDK] (=> (= (gd-cr rs c) true) (= (gd-cr rs2 c) true))) (= (gdk cs rs n) true) (= (gdk cs rs2 n) true))
  (intros hs h)
  (have p := (gdk-parts cs rs n h))
  (simp only [gdk Bool.and_eq_true])
  (exact (And.intro (And.left p) (tbl-all-mono GDK (gd-c rs n) (gd-c rs2 n)
                                    (fn [c :- GDK, hc :- (= (gd-c rs n c) true)] (gd-c-runs rs rs2 n c (hs c) hc)) cs (And.right p)))))
;; a run list edit that keeps every row's rof and ncur facts
(a/theorem gd-cr-of [rs :- (List RunRow), rs2 :- (List RunRow), c :- GDK]
  (=> (forall [P :- (=> RunRow Bool)] (=> (forall [r :- RunRow] (=> (= (P r) true) (= (gd-rof c r) true)))
                                           (= (tbl-all P rs) true) (= (tbl-all (gd-rof c) rs2) true)))
      (forall [P :- (=> RunRow Bool)] (=> (forall [r :- RunRow] (=> (= (P r) true) (= (gd-ncur c r) true)))
                                           (= (tbl-all P rs) true) (= (tbl-all (gd-ncur c) rs2) true)))
      (= (gd-cr rs c) true) (= (gd-cr rs2 c) true))
  (intros h1 h2 h)
  (simp only [gd-cr Bool.and_eq_true] at h)
  (have a1 := (h1 (gd-rof c) (fn [r :- RunRow, x :- (= (gd-rof c r) true)] x) (And.left h)))
  (have h3 := (And.right h))
  (cases hd (Nat.beq (:done c) (:epoch c)))
  (case [false] (simp only [gd-cr a1 gd-cde hd Bool.not_false Bool.true_or Bool.and_self]))
  (case [true]
    (simp only [gd-cde hd Bool.not_true Bool.false_or] at h3)
    (have a2 := (h2 (gd-ncur c) (fn [r :- RunRow, x :- (= (gd-ncur c r) true)] x) h3))
    (simp only [gd-cr a1 gd-cde hd a2 Bool.not_true Bool.false_or Bool.and_self])))
(a/theorem gd-rof-mono [c :- GDK, r :- RunRow, q :- RunRow]
  (=> (= (gd-rmono r q) true) (= (gd-rof c r) true) (= (gd-rof c q) true))
  (intros hm h)
  (simp only [gd-rmono Bool.and_eq_true] at hm)
  (simp only [gd-rof (Nat.eq_of_beq_eq_true (And.left hm)) (Nat.eq_of_beq_eq_true (And.left (And.right hm)))])
  (exact h))
(a/theorem gd-ncur-mono [c :- GDK, r :- RunRow, q :- RunRow]
  (=> (= (gd-rmono r q) true) (= (gd-ncur c r) true) (= (gd-ncur c q) true))
  (intros hm h)
  (simp only [gd-rmono Bool.and_eq_true] at hm)
  (have e2 := (Nat.eq_of_beq_eq_true (And.left (And.right hm))))
  (have e3 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right hm)))))
  (have al := (And.right (And.right (And.right hm))))
  (simp only [gd-ncur e2 e3]) (simp only [gd-ncur] at h)
  (cases ha (run-alive q))
  (case [false] (simp only [Bool.and_false Bool.not_false]))
  (case [true]
    (simp only [ha Bool.not_true Bool.false_or] at al)
    (simp only [al] at h) (exact h)))
(a/theorem gdk-run-m [x :- Nat, f :- (=> RunRow RunRow), hm :- (forall [r :- RunRow] (= (gd-rmono r (f r)) true)),
                      cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (gdk cs rs n) true) (= (gdk cs (tbl-upd run-id x f rs) n) true))
  (intro h)
  (apply (gdk-runs cs rs _ n _ h))
  (intros c hc)
  (apply (gd-cr-of rs _ c _ _ hc))
  (intros P hP hr)
  (exact (tbl-all-upd RunRow run-id x f P (gd-rof c)
           (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (run-id r) x) true)] (gd-rof-mono c r (f r) (hm r) (hP r h1)))
           (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (run-id r) x) false)] (hP r h1)) rs hr))
  (intros P hP hr)
  (exact (tbl-all-upd RunRow run-id x f P (gd-ncur c)
           (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (run-id r) x) true)] (gd-ncur-mono c r (f r) (hm r) (hP r h1)))
           (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (run-id r) x) false)] (hP r h1)) rs hr)))
(a/theorem gdk-run-del [x :- Nat, cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (gdk cs rs n) true) (= (gdk cs (tbl-del run-id x rs) n) true))
  (intro h)
  (apply (gdk-runs cs rs _ n _ h))
  (intros c hc)
  (apply (gd-cr-of rs _ c _ _ hc))
  (intros P hP hr)
  (exact (tbl-all-del RunRow run-id x P (gd-rof c) (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (run-id r) x) false)] (hP r h1)) rs hr))
  (intros P hP hr)
  (exact (tbl-all-del RunRow run-id x P (gd-ncur c) (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (run-id r) x) false)] (hP r h1)) rs hr)))
(a/theorem gdk-run-keep [K :- (=> Nat Bool), cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (gdk cs rs n) true) (= (gdk cs (tbl-keep K run-id rs) n) true))
  (intro h)
  (apply (gdk-runs cs rs _ n _ h))
  (intros c hc)
  (apply (gd-cr-of rs _ c _ _ hc))
  (intros P hP hr)
  (exact (tbl-all-keep RunRow K run-id P (gd-rof c) (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (K (run-id r)) true)] (hP r h1)) rs hr))
  (intros P hP hr)
  (exact (tbl-all-keep RunRow K run-id P (gd-ncur c) (fn [r :- RunRow, h1 :- (= (P r) true), h2 :- (= (K (run-id r)) true)] (hP r h1)) rs hr)))
;; a new run: fine for every computation it is checked against
(a/defn gd-new-ok [r :- RunRow, c :- GDK] Bool
  (Bool.and (gd-rof c r) (Bool.or (Bool.not (Nat.beq (:done c) (:epoch c))) (gd-ncur c r))))
(a/theorem gdk-run-ins [r :- RunRow, cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (tbl-all (gd-new-ok r) cs) true) (= (gdk cs rs n) true) (= (gdk cs (tbl-ins r rs) n) true))
  (intros hn h)
  (have p := (gdk-parts cs rs n h))
  (simp only [gdk Bool.and_eq_true])
  (apply (And.intro (And.left p)))
  (apply (tbl-all-mono2 GDK (gd-c rs n) (gd-new-ok r) (gd-c (tbl-ins r rs) n) _ cs (And.right p) hn))
  (intros c h1 h2)
  (apply (gd-c-runs rs _ n c _ h1))
  (intro hc)
  (simp only [gd-new-ok Bool.and_eq_true] at h2)
  (simp only [gd-cr Bool.and_eq_true] at hc)
  (have a1 := (And.left hc)) (have a2 := (And.right hc))
  (cases hd (Nat.beq (:done c) (:epoch c)))
  (case [false] (simp only [gd-cr gd-cde tbl-ins tbl-all hd (And.left h2) a1 Bool.not_false Bool.true_or Bool.and_self]))
  (case [true]
    (have b := (And.right h2))
    (simp only [hd Bool.not_true Bool.false_or] at b)
    (simp only [gd-cde hd Bool.not_true Bool.false_or] at a2)
    (simp only [gd-cr gd-cde tbl-ins tbl-all hd (And.left h2) a1 b a2 Bool.not_true Bool.false_or Bool.and_self])))

;; ===========================================================================
;; Part B. The bundle's primitives
;; ===========================================================================

(a/theorem gd-rnz-of [w :- World] (=> (= (inv-sample w) true) (= (tbl-all gd-rnz (:runs w)) true))
  (intro hs)
  (exact (all-of-mem RunRow gd-rnz (:runs w)
           (fn [r :- RunRow, mr :- (List.Mem r (:runs w))]
             (Eq.trans (congrArg Bool.not (run-id-pos w r hs mr)) (rfl))))))

(a/theorem gd-rest-grow [w :- World, w2 :- World]
  (=> (= (gdkeys (:comps w2)) (gdkeys (:comps w))) (= (:runs w2) (:runs w)) (<= (:next-id w) (:next-id w2))
      (= (gd-rest w) true) (= (gd-rest w2) true))
  (intros e1 e2 hl h)
  (simp only [gd-rest e1 e2]) (simp only [gd-rest] at h)
  (exact (gdk-next _ _ _ _ hl h)))
(a/theorem gd-rest-same [w :- World, w2 :- World]
  (=> (= (gdkeys (:comps w2)) (gdkeys (:comps w))) (= (:runs w2) (:runs w)) (= (:next-id w2) (:next-id w))
      (= (gd-rest w) true) (= (gd-rest w2) true))
  (intros e1 e2 e3 h)
  (exact (gd-rest-grow w w2 e1 e2 (Nat.le_of_eq (Eq.symm e3)) h)))

(a/theorem gd-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hk :- (forall [c :- CompRow] (= (gdkey (f c)) (gdkey c)))]
  (=> (= (gd w) true) (= (gd (comp-upd w x f)) true))
  (intro h)
  (have r := (gd-rest-same w (comp-upd w x f) (gdkeys-upd x f hk (:comps w)) (rfl) (rfl) (gd-rest-of w h)))
  (exact (gd-intro _ (inv-comp-upd w x f hid hp (gd-sample w h)) r)))
(a/theorem gd-comp-upd-m [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                          hm :- (forall [c :- CompRow] (= (gd-cmono (gdkey c) (gdkey (f c))) true))]
  (=> (= (gd w) true) (= (gd (comp-upd w x f)) true))
  (intro h)
  (have r0 := (gd-rest-of w h))
  (have r (= (gd-rest (comp-upd w x f)) true))
  (simp only [gd-rest comp-upd set-comps]) (simp only [gd-rest] at r0)
  (exact (gdk-comp-m x f hid hm (:comps w) (:runs w) (:next-id w) (gd-rnz-of w (gd-sample w h)) r0))
  (exact (gd-intro _ (inv-comp-upd w x f hid hp (gd-sample w h)) r)))
(a/theorem gd-run-upd-m [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                         hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         hm :- (forall [r :- RunRow] (= (gd-rmono r (f r)) true))]
  (=> (= (gd w) true) (= (gd (run-upd w x f)) true))
  (intro h)
  (have r0 := (gd-rest-of w h))
  (have r (= (gd-rest (run-upd w x f)) true))
  (simp only [gd-rest run-upd set-runs]) (simp only [gd-rest] at r0)
  (exact (gdk-run-m x f hm _ (:runs w) (:next-id w) r0))
  (exact (gd-intro _ (inv-run-upd w x f hf (gd-sample w h)) r)))

;; a new computation row: run 0, dle, and done-epoch /= epoch (checked by rfl at T3's `new-comp-row`)
(a/defn gd-newc [k :- GDK] Bool
  (Bool.and (Nat.beq (:run k) 0) (Bool.and (gd-dle k) (Bool.not (Nat.beq (:done k) (:epoch k))))))
(a/theorem gd-rof-zero [k :- GDK, rs :- (List RunRow)]
  (=> (= (:run k) 0) (= (tbl-all gd-rnz rs) true) (= (tbl-all (gd-rof k) rs) true))
  (intros e hz)
  (apply (tbl-all-mono RunRow gd-rnz (gd-rof k) _ rs hz))
  (intros q hq)
  (have hq2 := (bnot-true _ hq))
  (simp only [gd-rof e hq2 Bool.not_false Bool.true_or]))
(a/theorem gdk-cons [k :- GDK, cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (gd-c rs (+ n 1) k) true) (= (gdk cs rs n) true) (= (gdk (List.cons GDK k cs) rs (+ n 1)) true))
  (intros hc h)
  (have p := (gdk-parts _ _ _ (gdk-next cs rs n (+ n 1) (Nat.le_succ n) h)))
  (simp only [gdk tbl-all (And.left p) hc (And.right p) Bool.and_self]))
(a/theorem gd-comp-ins [w :- World, r :- CompRow, hn :- (= (gd-newc (gdkey r)) true)]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (gd w) true) (= (gd (bump (comp-ins w r))) true))
  (intros h1 h2 h)
  (have r0 := (gd-rest-of w h))
  (simp only [gd-rest] at r0)
  (simp only [gd-newc Bool.and_eq_true] at hn)
  (have e0 := (Nat.eq_of_beq_eq_true (And.left hn)))
  (have hz := (gd-rnz-of w (gd-sample w h)))
  (have c1 := (gd-rof-zero (gdkey r) (:runs w) e0 hz))
  (have c2 (= (gd-cde (:runs w) (gdkey r)) true))
  (simp only [gd-cde (And.right (And.right hn)) Bool.not_false Bool.true_or])
  (have c3 (= (Nat.blt (:run (gdkey r)) (+ (:next-id w) 1)) true))
  (apply gd-blt-of) (show (< (:run r) (+ (:next-id w) 1))) (rw [e0]) (exact (Nat.zero_lt_succ _))
  (have hc := (gd-c-intro (:runs w) (+ (:next-id w) 1) (gdkey r) (And.left (And.right hn)) c3 c1 c2))
  (have rr (= (gd-rest (bump (comp-ins w r))) true))
  (show (= (gdk (List.cons GDK (gdkey r) (gdkeys (:comps w))) (:runs w) (+ (:next-id w) 1)) true))
  (exact (gdk-cons _ _ _ _ hc r0))
  (exact (gd-intro _ (inv-comp-ins-fresh w r h1 h2 (gd-sample w h)) rr)))

;; ---- rest lemmas of the edge and table primitives
(a/theorem gd-key-inc-pending [c :- CompRow] (= (gdkey (comp-inc-pending c)) (gdkey c)) (rfl))
(a/theorem gd-key-dec-pending [c :- CompRow] (= (gdkey (comp-dec-pending c)) (gdkey c)) (rfl))
(a/theorem gd-key-set-pending [k :- Nat, c :- CompRow] (= (gdkey (comp-set-pending k c)) (gdkey c)) (rfl))

(a/theorem gdr-mark-edge [w :- World, x :- Nat] (=> (= (gd-rest w) true) (= (gd-rest (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false]
      (simp only [mark-edge hf hm])
      (exact (gd-rest-same w (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending)
               (gdkeys-upd (:creditor e) comp-inc-pending gd-key-inc-pending (:comps w)) (rfl) (rfl) h)))))
(a/theorem gdr-unmark-edge [w :- World, x :- Nat] (=> (= (gd-rest w) true) (= (gd-rest (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true]
      (simp only [unmark-edge hf hm])
      (exact (gd-rest-same w (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending)
               (gdkeys-upd (:creditor e) comp-dec-pending gd-key-dec-pending (:comps w)) (rfl) (rfl) h)))))
(a/theorem gdr-remove-edge [w :- World, x :- Nat] (=> (= (gd-rest w) true) (= (gd-rest (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact (gd-rest-same w (edge-del w x) (rfl) (rfl) (rfl) h)))
    (case [true]
      (simp only [remove-edge hf hm])
      (exact (gd-rest-same w (comp-upd (edge-del w x) (:creditor e) comp-dec-pending)
               (gdkeys-upd (:creditor e) comp-dec-pending gd-key-dec-pending (:comps w)) (rfl) (rfl) h)))))
(a/theorem gdr-drop-cred [w :- World, a :- Nat] (=> (= (gd-rest w) true) (= (gd-rest (drop-cred-edges w a)) true))
  (intro h)
  (simp only [drop-cred-edges])
  (exact (gd-rest-same w (comp-upd (set-edges w (tbl-filter (cred-ne a) (:edges w))) a (comp-set-pending 0))
           (gdkeys-upd a (comp-set-pending 0) (gd-key-set-pending 0) (:comps w)) (rfl) (rfl) h)))
(a/theorem gdr-drop-act [w :- World, a :- Nat] (=> (= (gd-rest w) true) (= (gd-rest (drop-act w a)) true))
  (intro h)
  (simp only [drop-act])
  (exact (gd-rest-same (drop-cred-edges w a) (act-del (drop-cred-edges w a) a) (rfl) (rfl) (rfl) (gdr-drop-cred w a h))))
(a/theorem gdr-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (=> (= (gd-rest w) true) (= (gd-rest (drop-edges w p)) true))
  (intro h)
  (simp only [drop-edges])
  (exact (gd-rest-same w (set-comps (set-edges w (tbl-filter p (:edges w))) (comps-resync (tbl-filter p (:edges w)) (:comps w)))
           (gdkeys-resync (tbl-filter p (:edges w)) (:comps w)) (rfl) (rfl) h)))
(a/theorem gdr-insert-edge-fresh [w :- World, e :- EdgeRow] (=> (= (gd-rest w) true) (= (gd-rest (insert-edge-fresh w e)) true))
  (intro h)
  (simp only [insert-edge-fresh])
  (exact (gd-rest-grow w (bump (insert-edge w (edge-set-id (:next-id w) e))) (rfl) (rfl) (Nat.le_succ _) h)))
(a/theorem gdr-insert-edge-checked [w :- World, e :- EdgeRow] (=> (= (gd-rest w) true) (= (gd-rest (insert-edge-checked w e)) true))
  (intro h)
  (cases hk (edge-ok-in w e))
  (simp only [insert-edge-checked hk]) (exact h)
  (simp only [insert-edge-checked hk]) (exact (gdr-insert-edge-fresh w e h)))
(a/theorem gdr-comp-del [w :- World, x :- Nat] (=> (= (gd-rest w) true) (= (gd-rest (comp-del w x)) true))
  (intro h)
  (simp only [gd-rest comp-del set-comps gdkeys-del]) (simp only [gd-rest] at h)
  (exact (gdk-del x _ _ _ h)))
(a/theorem gdr-run-del [w :- World, x :- Nat] (=> (= (gd-rest w) true) (= (gd-rest (run-del w x)) true))
  (intro h)
  (simp only [gd-rest run-del set-runs]) (simp only [gd-rest] at h)
  (exact (gdk-run-del x _ _ _ h)))
(a/theorem gdr-filter-world [w :- World, K :- (=> Nat Bool)] (=> (= (gd-rest w) true) (= (gd-rest (filter-world K w)) true))
  (intro h)
  (simp only [gd-rest filter-world gdkeys-keep]) (simp only [gd-rest] at h)
  (exact (gdk-run-keep K _ _ _ (gdk-keep K _ _ _ h))))

;; ---- row functions: the computation edits that change the key (cmono) and the run edits that end a run
(a/structure GDRK [] (id Nat) (of Nat) (epoch Nat) (alive Bool))
(a/defn gdrk [r :- RunRow] GDRK (GDRK.mk (:id r) (:of r) (:epoch r) (run-alive r)))
(a/theorem gd-rmono-key [r :- RunRow, q :- RunRow] (=> (= (gdrk q) (gdrk r)) (= (gd-rmono r q) true))
  (intro h)
  (have e1 (= (:id q) (:id r))) (exact (congrArg (fn [k :- GDRK] (:id k)) h))
  (have e2 (= (:of q) (:of r))) (exact (congrArg (fn [k :- GDRK] (:of k)) h))
  (have e3 (= (:epoch q) (:epoch r))) (exact (congrArg (fn [k :- GDRK] (:epoch k)) h))
  (have e4 (= (run-alive q) (run-alive r))) (exact (congrArg (fn [k :- GDRK] (:alive k)) h))
  (simp only [gd-rmono e1 e2 e3 e4 Nat.beq_refl Bool.true_and])
  (cases ha (run-alive r)) (all_goals (simp only [Bool.not_false Bool.not_true Bool.true_or Bool.or_true])))
(a/theorem run-cancel-row-grm [r :- RunRow] (= (gd-rmono r (run-cancel-row r)) true)
  (simp [gd-rmono run-cancel-row run-alive act-done Nat.beq_refl]))
(a/theorem run-complete-row-grm [r :- RunRow] (= (gd-rmono r (run-complete-row r)) true)
  (simp [gd-rmono run-complete-row run-alive act-done Nat.beq_refl]))

(a/theorem gd-ble-refl [n :- Nat] (= (Nat.ble n n) true) (exact (gd-ble-of n n (Nat.le_refl n))))
(a/theorem run-wake-grm [r :- RunRow] (= (gd-rmono r (run-wake r)) true)
  (apply gd-rmono-key)
  (show (= (GDRK.mk (:id r) (:of r) (:epoch r) (run-alive (run-wake r))) (GDRK.mk (:id r) (:of r) (:epoch r) (run-alive r))))
  (rw [run-wake-alive]))
(a/theorem gd-cmono-key [c :- CompRow, d :- CompRow] (=> (= (gdkey d) (gdkey c)) (= (gd-cmono (gdkey c) (gdkey d)) true))
  (intro h) (rw [h]) (simp only [gd-cmono Nat.beq_refl gd-ble-refl Bool.true_or Bool.and_self]))
(a/theorem comp-inc-epoch-gcm [c :- CompRow] (= (gd-cmono (gdkey c) (gdkey (comp-inc-epoch c))) true)
  (simp only [gd-cmono gdkey comp-inc-epoch Nat.beq_refl Bool.true_or Bool.and_true Bool.true_and])
  (apply gd-ble-of) (omega))
(a/theorem comp-demand-row-gcm [c :- CompRow] (= (gd-cmono (gdkey c) (gdkey (comp-demand-row c))) true)
  (cases hd (Nat.beq (:done-epoch c) 0))
  (all_goals (simp only [gd-cmono gdkey comp-demand-row hd Nat.beq_refl Bool.true_or Bool.and_true Bool.true_and gd-ble-refl]))
  (all_goals (apply gd-ble-of) (omega)))
(a/theorem comp-replace-row-gcm [i :- (List Nat), b :- Nat, c :- CompRow] (= (gd-cmono (gdkey c) (gdkey (comp-replace-row i b c))) true)
  (cases hi (:idle c))
  (all_goals (simp only [gd-cmono gdkey comp-replace-row hi Nat.beq_refl Bool.true_or Bool.or_true Bool.and_true Bool.true_and]))
  (all_goals (apply gd-ble-of) (omega)))
(a/theorem comp-make-idle-gcm [vs :- (List Valid), c :- CompRow] (= (gd-cmono (gdkey c) (gdkey (comp-make-idle vs c))) true)
  (simp only [gd-cmono gdkey comp-make-idle Nat.beq_refl gd-ble-refl Bool.true_or Bool.or_true Bool.and_self]))
(a/theorem comp-clear-run-gcm [c :- CompRow] (= (gd-cmono (gdkey c) (gdkey (comp-clear-run c))) true)
  (simp only [gd-cmono gdkey comp-clear-run Nat.beq_refl gd-ble-refl Bool.true_or Bool.or_true Bool.and_self]))

;; ===========================================================================
;; Part C. The bundle copy
;; ===========================================================================

(def GD (mk-bundle 'gd [] "gd-" {'inv-comp-ins-fresh ['(Eq.refl true) 2]}))
(swap! (:renames GD) assoc 'inv-parts 'gd-parts 'inv-comp-ins-fresh 'gd-comp-ins)
(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-set-pins
            inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-task-upd inv-edge-upd]]
  (prim! GD o nil))
(doseq [[o t] '[[inv-source-ins-fresh source-ins] [inv-resource-ins-fresh resource-ins] [inv-scope-ins-fresh scope-ins]
                [inv-act-ins-fresh act-ins] [inv-task-ins-fresh task-ins]]]
  (prim! GD o (list 'gd-rest-grow 'w (list 'bump (list t 'w 'r)) '(rfl) '(rfl) '(Nat.le_succ (:next-id w)) 'R)))
(prim! GD 'inv-bump '(gd-rest-grow w (bump w) (rfl) (rfl) (Nat.le_succ (:next-id w)) R))
(prim! GD 'inv-remove-edge '(gdr-remove-edge w x R))
(prim! GD 'mark-edge-inv-sample '(gdr-mark-edge w x R))
(prim! GD 'unmark-edge-inv-sample '(gdr-unmark-edge w x R))
(prim! GD 'inv-drop-cred '(gdr-drop-cred w a R))
(prim! GD 'inv-drop-act '(gdr-drop-act w a R))
(prim! GD 'inv-drop-edges '(gdr-drop-edges w p R))
(prim! GD 'insert-edge-fresh-inv-sample '(gdr-insert-edge-fresh w e R))
(prim! GD 'inv-insert-edge-checked '(gdr-insert-edge-checked w e R))
(prim! GD 'inv-comp-del-unref '(gdr-comp-del w x R))
(prim! GD 'inv-run-del '(gdr-run-del w x R))
(prim! GD 'inv-filter-world '(gdr-filter-world w K R))

;; the source patch: every computation / run edit goes through gd-comp-upd(-m) / gd-run-upd-m
(def ^:private gd-cm '#{comp-inc-epoch comp-demand-row comp-replace-row comp-make-idle comp-clear-run})
(def ^:private gd-rm '#{run-cancel-row run-complete-row run-wake})
(defn- gd-fhead [f] (if (seq? f) (first f) f))
(defn- gd-lapp [f lem] (if (seq? f) (apply list lem (rest f)) lem))
(defn gd-patch [form]
  (->> (@#'spindel.v2.idle/fix-f form)
       (subst-forms (fn [y] (and (seq? y) (= 'inv-comp-upd (first y)) (>= (count y) 6)))
                    (fn [[_ w x f hid hp & more]]
                      (let [h (gd-fhead f)]
                        (if (contains? gd-cm h)
                          (apply list 'gd-comp-upd-m w x f hid hp (gd-lapp f (symbol (str h "-gcm"))) more)
                          (apply list 'gd-comp-upd w x f hid hp '(fn [c :- CompRow] (Eq.refl (gdkey c))) more)))))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (>= (count y) 5)))
                    (fn [[_ w x f hf & more]]
                      (let [h (gd-fhead f)]
                        (if (contains? gd-rm h)
                          (apply list 'gd-run-upd-m w x f hf (gd-lapp f (symbol (str h "-grm"))) more)
                          (apply list 'gd-run-upd-m w x f hf
                                 (list 'fn '[r :- RunRow] (list 'gd-rmono-key 'r (list f 'r) '(Eq.refl (gdrk r)))) more)))))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! GD n gd-patch))

;; ===========================================================================
;; Part D. Overrides: parks (the parked run was alive; await through i8's KA), new runs
;; ===========================================================================

;; a run edit on the rows with id x, all alive: the edit keeps id, of and epoch
(a/defn gd-keeps [f :- (=> RunRow RunRow), r :- RunRow] Bool
  (Bool.and (Nat.beq (:id (f r)) (:id r)) (Bool.and (Nat.beq (:of (f r)) (:of r)) (Nat.beq (:epoch (f r)) (:epoch r)))))
(a/theorem gd-rmono-alive [f :- (=> RunRow RunRow), r :- RunRow]
  (=> (= (gd-keeps f r) true) (= (run-alive r) true) (= (gd-rmono r (f r)) true))
  (intros hk ha)
  (simp only [gd-keeps Bool.and_eq_true] at hk)
  (simp only [gd-rmono (And.left hk) (And.left (And.right hk)) (And.right (And.right hk)) ha Bool.or_true Bool.and_self]))
(a/theorem gd-all-upd-on [x :- Nat, f :- (=> RunRow RunRow), P :- (=> RunRow Bool), Q :- (=> RunRow Bool),
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
(a/theorem gdk-run-on [x :- Nat, f :- (=> RunRow RunRow), hk :- (forall [r :- RunRow] (= (gd-keeps f r) true)),
                       cs :- (List GDK), rs :- (List RunRow), n :- Nat]
  (=> (= (tbl-all (run-ok-for x) rs) true) (= (gdk cs rs n) true) (= (gdk cs (tbl-upd run-id x f rs) n) true))
  (intros ho h)
  (apply (gdk-runs cs rs _ n _ h))
  (intros c hc)
  (apply (gd-cr-of rs _ c _ _ hc))
  (intros P hP hr)
  (exact (gd-all-upd-on x f P (gd-rof c)
           (fn [r :- RunRow, h1 :- (= (P r) true), al :- (= (run-alive r) true)] (gd-rof-mono c r (f r) (gd-rmono-alive f r (hk r) al) (hP r h1)))
           hP rs ho hr))
  (intros P hP hr)
  (exact (gd-all-upd-on x f P (gd-ncur c)
           (fn [r :- RunRow, h1 :- (= (P r) true), al :- (= (run-alive r) true)] (gd-ncur-mono c r (f r) (gd-rmono-alive f r (hk r) al) (hP r h1)))
           hP rs ho hr)))
(a/theorem gd-run-upd-on [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                          hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                          hk :- (forall [r :- RunRow] (= (gd-keeps f r) true))]
  (=> (= (tbl-all (run-ok-for x) (:runs w)) true) (= (gd w) true) (= (gd (run-upd w x f)) true))
  (intros ho h)
  (have r0 := (gd-rest-of w h))
  (have r (= (gd-rest (run-upd w x f)) true))
  (simp only [gd-rest run-upd set-runs]) (simp only [gd-rest] at r0)
  (exact (gdk-run-on x f hk _ (:runs w) (:next-id w) ho r0))
  (exact (gd-intro _ (inv-run-upd w x f hf (gd-sample w h)) r)))
(a/theorem gd-keeps-park [r :- RunRow] (= (gd-keeps run-park-row r) true) (simp only [gd-keeps run-park-row Nat.beq_refl Bool.and_self]))
(a/theorem gd-keeps-tick-park [r :- RunRow] (= (gd-keeps run-tick-park r) true) (simp only [gd-keeps run-tick-park Nat.beq_refl Bool.and_self]))

(override! GD 'inv-park-if '[]
  '(a/theorem gd-park-if [w :- World, a :- Nat, rid :- Nat]
     (=> (= (tbl-all (run-ok-for rid) (:runs w)) true) (= (gd w) true) (= (gd (park-if w a rid)) true))
     (intros hk h)
     (cases ha (act-has w a))
     (simp only [park-if ha]) (exact h)
     (simp only [park-if ha]) (exact (gd-run-upd-on w rid run-park-row run-park-row-id gd-keeps-park hk h))))
(override! GD 'inv-take-park '[inv-insert-edge-checked]
  '(a/theorem gd-take-park [w :- World, r :- RunRow, x :- Nat, k :- Nat]
     (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (gd w) true) (= (gd (take-park w r x k)) true))
     (intros hm hal h)
     (have o := (run-ok-of-mem w r (gd-sample w h) hm hal))
     (have h1 := (gd-insert-edge-checked _ (take-edge r (:next-id w) x) (gd-act-ins-fresh w (take-act w r k) (rfl) h)))
     (have o2 (= (tbl-all (run-ok-for (:id r)) (:runs (insert-edge-checked (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x)))) true))
     (rw [runs-iec]) (exact o)
     (simp only [take-park])
     (exact (gd-run-upd-on _ (:id r) run-tick-park run-tick-park-id gd-keeps-tick-park o2 h1))))

;; ---- new runs (T4, T5, T11): a new run of `of` at epoch `ep` is fine for every computation
(a/defn gd-ok-new [o :- Nat, e :- Nat, k :- GDK] Bool
  (Bool.or (Bool.not (Nat.beq (:id k) o)) (Bool.or (Bool.not (Nat.beq (:epoch k) e)) (Bool.not (Nat.beq (:done k) (:epoch k))))))
(a/theorem gd-beq-lt [a :- Nat, b :- Nat] (=> (< a b) (= (Nat.beq b a) false))
  (intro h) (cases hb (Nat.beq b a)) (case [false] (rfl)) (case [true] (have e := (Nat.eq_of_beq_eq_true hb)) (omega)))
(a/theorem gd-beq-lt2 [a :- Nat, b :- Nat] (=> (< a b) (= (Nat.beq a b) false))
  (intro h) (cases hb (Nat.beq a b)) (case [false] (rfl)) (case [true] (have e := (Nat.eq_of_beq_eq_true hb)) (omega)))
(a/theorem gd-new-of [rs :- (List RunRow), n :- Nat, k :- GDK, o :- Nat, e :- Nat, s :- Nat, ei :- Nat]
  (=> (= (gd-c rs n k) true) (= (gd-ok-new o e k) true) (= (gd-new-ok (new-run-row n o e s ei) k) true))
  (intros hc ho)
  (have p := (gd-c-parts rs n k hc))
  (have b1 := (gd-beq-lt _ _ (gd-lt-of _ _ (And.left (And.right p)))))
  (have r1 (= (gd-rof k (new-run-row n o e s ei)) true)) (simp only [gd-rof new-run-row b1 Bool.not_false Bool.true_or])
  (simp only [gd-ok-new Bool.or_eq_true] at ho)
  (simp only [gd-new-ok r1 Bool.true_and])
  (cases ho)
  (case [inl a1] (have a2 := (bnot-true _ a1))
    (have z (= (gd-ncur k (new-run-row n o e s ei)) true))
    (simp only [gd-ncur new-run-row]) (rw [(beq-comm o (:id k))]) (simp only [a2 Bool.false_and Bool.not_false])
    (simp only [z Bool.or_true]))
  (case [inr b]
    (cases b)
    (case [inl a1] (have a2 := (bnot-true _ a1))
      (have z (= (gd-ncur k (new-run-row n o e s ei)) true))
      (simp only [gd-ncur new-run-row]) (rw [(beq-comm e (:epoch k))]) (simp only [a2 Bool.false_and Bool.and_false Bool.not_false])
      (simp only [z Bool.or_true]))
    (case [inr a1] (simp only [a1 Bool.true_or]))))
(a/theorem gd-ok-new-zero [rs :- (List RunRow), n :- Nat, o :- Nat, k :- GDK]
  (=> (= (gd-c rs n k) true) (= (gd-ok-new o 0 k) true))
  (intro hc)
  (have dl := (And.left (gd-c-parts rs n k hc)))
  (simp only [gd-dle Bool.and_eq_true] at dl)
  (have z := (gd-beq-lt _ _ (gd-lt-of _ _ (And.right dl))))
  (simp only [gd-ok-new z Bool.not_false Bool.true_or Bool.or_true]))

(override! GD 'inv-add-run-scope '[]
  '(a/theorem gd-add-run-scope [w :- World, of :- Nat, ep :- Nat, parent :- Nat, ei :- Nat]
     (=> (= (tbl-all (gd-ok-new of ep) (gdkeys (:comps w))) true) (= (gd w) true) (= (gd (add-run-scope w of ep parent ei)) true))
     (intros ho h)
     (have r0 := (gd-rest-of w h)) (simp only [gd-rest] at r0)
     (have p := (gdk-parts _ _ _ r0))
     (have hn := (tbl-all-mono2 GDK (gd-c (:runs w) (:next-id w)) (gd-ok-new of ep)
                   (gd-new-ok (new-run-row (:next-id w) of ep (+ (:next-id w) 1) ei))
                   (fn [k :- GDK, h1 :- (= (gd-c (:runs w) (:next-id w) k) true), h2 :- (= (gd-ok-new of ep k) true)]
                     (gd-new-of (:runs w) (:next-id w) k of ep (+ (:next-id w) 1) ei h1 h2))
                   (gdkeys (:comps w)) (And.right p) ho))
     (have r1 := (gdk-run-ins (new-run-row (:next-id w) of ep (+ (:next-id w) 1) ei) _ _ _ hn r0))
     (have rr (= (gd-rest (add-run-scope w of ep parent ei)) true))
     (show (= (gdk (gdkeys (:comps w)) (tbl-ins (new-run-row (:next-id w) of ep (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1)) true))
     (exact (gdk-next _ _ _ _ (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _)) r1))
     (exact (gd-intro _ (inv-add-run-scope w of ep parent ei (gd-sample w h)) rr))))
(override! GD 'inv-spawn-rows '[inv-add-run-scope]
  '(a/theorem gd-spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat)]
     (=> (= (gd w) true) (= (gd (spawn-rows w owner inputs)) true))
     (intro h)
     (have p := (gdk-parts _ _ _ (gd-rest-of w h)))
     (have ho := (tbl-all-mono GDK (gd-c (:runs w) (:next-id w)) (gd-ok-new (:next-id w) 0)
                   (fn [k :- GDK, h1 :- (= (gd-c (:runs w) (:next-id w) k) true)] (gd-ok-new-zero (:runs w) (:next-id w) (:next-id w) k h1))
                   (gdkeys (:comps w)) (And.right p)))
     (simp only [spawn-rows])
     (exact (gd-add-run-scope (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs)))
              (:next-id w) 0 (task-scope-parent w owner) 0 ho
              (gd-task-ins-fresh w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs) (rfl) h)))))

;; T6/take/arm: i8's overrides (the parked run is alive; KA through the await wiring), for gd
(defn- gd-from-g8 [form]
  (letfn [(strip [x] (cond (seq? x) (apply list (map strip (remove #{'x8s} x)))
                           (vector? x) (let [v (vec x) i (.indexOf v 'x8s)] (mapv strip (if (>= i 0) (into (subvec v 0 i) (subvec v (+ i 3))) v)))
                           (symbol? x) (let [n (name x)]
                                         (cond (= n "g8") 'gd
                                               (str/starts-with? n "g8-") (symbol (str "gd-" (subs n 3)))
                                               (str/ends-with? n "-g8") (symbol (str (subs n 0 (- (count n) 3)) "-gd"))
                                               :else x))
                           :else x))]
    (strip form)))
(doseq [o '[t-take-inv inv-arm-park t17-inv inv-await-post inv-await-raw t6-inv]]
  (let [{:keys [deps form]} (get @(:overrides spindel.v2.i8/G8) o)]
    (override! GD o deps (gd-from-g8 form))))

;; ---- T5: the started run is at start-epoch, where the computation has no result (startable)
(a/theorem gd-start-ne [w :- World, c :- CompRow]
  (=> (= (startable w c) true) (= (gd-dle (gdkey c)) true) (= (Nat.beq (:done-epoch c) (start-epoch c)) false))
  (intros hs hd)
  (simp only [gd-dle gdkey Bool.and_eq_true] at hd)
  (have d1 := (gd-le-of _ _ (And.left hd))) (have d2 := (gd-lt-of _ _ (And.right hd)))
  (cases hi (:idle c))
  (case [true]
    (cases hz (Nat.beq (:done-epoch c) 0))
    (case [true] (have z := (Nat.eq_of_beq_eq_true hz)) (simp only [start-epoch hi hz Bool.not_true Bool.and_false]) (rw [z]) (exact (gd-beq-lt2 _ _ d2)))
    (case [false] (simp only [start-epoch hi hz Bool.not_false Bool.and_self]) (apply gd-beq-lt2) (omega)))
  (case [false]
    (have se (= (start-epoch c) (:epoch c))) (simp only [start-epoch hi Bool.false_and])
    (rw [se])
    (simp only [startable hi Bool.not_false Bool.false_and Bool.true_and Bool.false_or Bool.or_eq_true Bool.and_eq_true] at hs)
    (cases hs)
    (case [inl a1] (have z := (Nat.eq_of_beq_eq_true (And.left a1))) (rw [z]) (exact (gd-beq-lt2 _ _ d2)))
    (case [inr a1] (exact (bnot-true _ (And.left a1))))))
(a/theorem gd-runs-below [w :- World] (=> (= (inv-sample w) true) (= (tbl-all (fn [r :- RunRow] (Nat.blt (:id r) (:next-id w))) (:runs w)) true))
  (intro hs)
  (have b := (runs-below w hs))
  (rw [all-rk10s] at b)
  (exact b))
(a/theorem gd-start-c [rs :- (List RunRow), n :- Nat, c :- CompRow, w :- World]
  (=> (= (gd-c rs n (gdkey c)) true) (= (startable w c) true) (= (tbl-all (fn [r :- RunRow] (Nat.blt (:id r) n)) rs) true)
      (= (gd-c (tbl-ins (new-run-row n (:id c) (start-epoch c) (+ n 1) 0) rs) (+ (+ n 1) 1) (gdkey (comp-start-row n c))) true))
  (intros hc hst hb)
  (have p := (gd-c-parts _ _ _ hc))
  (have ne := (gd-start-ne w c hst (And.left p)))
  (have dl := (And.left p)) (simp only [gd-dle gdkey Bool.and_eq_true] at dl)
  (have d1 := (gd-le-of _ _ (And.left dl))) (have d2 := (gd-lt-of _ _ (And.right dl)))
  (have sge (<= (:epoch c) (start-epoch c)))
  (cases hz (Bool.and (:idle c) (Bool.not (Nat.beq (:done-epoch c) 0))))
  (simp only [start-epoch hz]) (exact (Nat.le_refl _))
  (simp only [start-epoch hz]) (exact (Nat.le_succ _))
  (have g1 (= (gd-dle (gdkey (comp-start-row n c))) true))
  (simp only [gd-dle gdkey comp-start-row Bool.and_eq_true])
  (exact (And.intro (gd-ble-of _ _ (Nat.le_trans d1 sge)) (gd-blt-of _ _ (Nat.lt_of_lt_of_le d2 sge))))
  (have g2 (= (Nat.blt (:run (gdkey (comp-start-row n c))) (+ (+ n 1) 1)) true))
  (apply gd-blt-of) (show (< n (+ (+ n 1) 1))) (omega)
  (have g3 (= (tbl-all (gd-rof (gdkey (comp-start-row n c))) (tbl-ins (new-run-row n (:id c) (start-epoch c) (+ n 1) 0) rs)) true))
  (simp only [tbl-ins tbl-all gd-rof gdkey comp-start-row new-run-row Nat.beq_refl Bool.or_true Bool.true_and])
  (apply (tbl-all-mono RunRow _ _ _ rs hb))
  (intros r hr)
  (have z := (gd-beq-lt2 _ _ (gd-lt-of _ _ hr)))
  (simp only [gd-rof gdkey comp-start-row z Bool.not_false Bool.true_or])
  (have g4 (= (gd-cde (tbl-ins (new-run-row n (:id c) (start-epoch c) (+ n 1) 0) rs) (gdkey (comp-start-row n c))) true))
  (simp only [gd-cde gdkey comp-start-row ne Bool.not_false Bool.true_or])
  (exact (gd-c-intro _ _ _ g1 g2 g3 g4)))
(a/theorem gd-start-ok [w :- World, c :- CompRow]
  (=> (= (startable w c) true) (= (gd-dle (gdkey c)) true) (= (gd-ok-new (:id c) (start-epoch c) (gdkey c)) true))
  (intros hst hd)
  (have ne := (gd-start-ne w c hst hd))
  (cases he (Nat.beq (:epoch c) (start-epoch c)))
  (case [false] (simp only [gd-ok-new gdkey he Bool.not_false Bool.true_or Bool.or_true]))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true he))
    (have ne2 (= (Nat.beq (:done-epoch c) (:epoch c)) false)) (rw [e]) (exact ne)
    (simp only [gd-ok-new gdkey ne2 Bool.not_false Bool.or_true])))
;; rows with c's id are c (unique ids): a fact of c holds for every row with its id
(a/theorem gd-same-id [w :- World, c :- CompRow, Q :- (=> CompRow Bool)]
  (=> (= (inv-sample w) true) (List.Mem c (:comps w)) (= (Q c) true)
      (= (tbl-all (same-id-then comp-id (:id c) Q) (:comps w)) true))
  (intros hs hm hq) (exact (uniq-all CompRow comp-id Q c (:comps w) (comps-nodup w hs) hm hq)))

(a/theorem gd-upd-same [x :- Nat, f :- (=> CompRow CompRow), P :- (=> CompRow Bool), Q :- (=> CompRow Bool),
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
(override! GD 'inv-start-raw '[inv-add-run-scope]
  '(a/theorem gd-start-raw [w :- World, c :- CompRow]
     (=> (List.Mem c (:comps w)) (= (startable w c) true) (= (gd w) true) (= (gd (start-raw w c)) true))
     (intros hm hst h)
     (have hs := (gd-sample w h))
     (have p := (gdk-parts _ _ _ (gd-rest-of w h)))
     (have q := (And.right p)) (rw [all-gdkeys] at q)
     (have hc0 := (tbl-all-mem CompRow (fn [x :- CompRow] (gd-c (:runs w) (:next-id w) (gdkey x))) c (:comps w) q hm))
     (have u := (gd-same-id w c (fn [x :- CompRow] (gd-ok-new (:id c) (start-epoch c) (gdkey x))) hs hm
                  (gd-start-ok w c hst (And.left (gd-c-parts _ _ _ hc0)))))
     (have ho (= (tbl-all (gd-ok-new (:id c) (start-epoch c)) (gdkeys (:comps w))) true))
     (rw [all-gdkeys])
     (apply (tbl-all-mono CompRow _ _ _ (:comps w) u))
     (intros x hx)
     (cases hi (Nat.beq (comp-id x) (:id c)))
     (case [false] (have hi2 (= (Nat.beq (:id x) (:id c)) false)) (exact hi) (simp only [gd-ok-new gdkey hi2 Bool.not_false Bool.true_or]))
     (case [true] (simp only [same-id-then hi Bool.not_true Bool.false_or] at hx) (exact hx))
     (have h1 := (gd-add-run-scope w (:id c) (start-epoch c) 0 0 ho h))
     (have s1 := (gd-sample _ h1))
     (have u2 := (gd-same-id w c (fn [x :- CompRow] (gd-c (tbl-ins (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0) (:runs w))
                                                               (+ (+ (:next-id w) 1) 1) (gdkey (comp-start-row (:next-id w) x)))) hs hm
                  (gd-start-c (:runs w) (:next-id w) c w hc0 hst (gd-runs-below w hs))))
     (have r1 := (gdk-parts _ _ _ (gd-rest-of _ h1)))
     (have q1 := (And.right r1))
     (change (= (tbl-all (gd-c (tbl-ins (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0) (:runs w)) (+ (+ (:next-id w) 1) 1))
                         (gdkeys (:comps w))) true) at q1)
     (rw [all-gdkeys] at q1)
     (have rr (= (gd-rest (start-raw w c)) true))
     (show (= (gdk (gdkeys (tbl-upd comp-id (:id c) (comp-start-row (:next-id w)) (:comps w)))
                   (tbl-ins (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0) (:runs w)) (+ (+ (:next-id w) 1) 1)) true))
     (simp only [gdk (And.left r1) Bool.true_and])
     (rw [all-gdkeys])
     (exact (gd-upd-same (:id c) (comp-start-row (:next-id w)) _ _ (fn [x :- CompRow, hx :- (= (gd-c (tbl-ins (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0) (:runs w)) (+ (+ (:next-id w) 1) 1) (gdkey x)) true)] hx) (:comps w) q1 u2))
     (exact (gd-intro _ (inv-start-raw w c hs) rr))))
(override! GD 't5-inv '[inv-start-raw]
  '(a/theorem t5-gd [w :- World, cid :- Nat, fresh :- Nat]
     (=> (= (gd w) true) (= (gd (:world (t5-start w cid fresh))) true))
     (intro h)
     (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
     (simp only [t5-start hc refuse]) (exact h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (startable w c)))
     (simp only [t5-start hc hg refuse]) (exact h)
     (have hst (= (startable w c) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
     (simp only [t5-start hc hg accept]) (exact (gd-start-raw w c (tbl-find-mem CompRow comp-id cid c (:comps w) hc) hst h))))

;; ---- T11: the new run is at C's epoch e as read before the predecessor's cancel. Bundle hkw c e:
;; every row with id c has epoch >= e and done-epoch /= e (cmono edits keep it: the epoch only
;; grows, done-epoch is kept or cleared, e > 0); at C's dispatch, needs-run gives it
(a/defn hkw-one [kc :- Nat, ke :- Nat, k :- GDK] Bool
  (Bool.or (Bool.not (Nat.beq (:id k) kc)) (Bool.and (Nat.ble ke (:epoch k)) (Bool.not (Nat.beq (:done k) ke)))))
(a/defn hkw-rest [kc :- Nat, ke :- Nat, w :- World] Bool (Bool.and (Nat.blt 0 ke) (tbl-all (hkw-one kc ke) (gdkeys (:comps w)))))
(a/defn hkw [kc :- Nat, ke :- Nat, w :- World] Bool (Bool.and (inv-sample w) (hkw-rest kc ke w)))
(a/theorem hkw-sample [kc :- Nat, ke :- Nat, w :- World] (=> (= (hkw kc ke w) true) (= (inv-sample w) true))
  (intro h) (simp only [hkw Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem hkw-rest-of [kc :- Nat, ke :- Nat, w :- World] (=> (= (hkw kc ke w) true) (= (hkw-rest kc ke w) true))
  (intro h) (simp only [hkw Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem hkw-intro [kc :- Nat, ke :- Nat, w :- World] (=> (= (inv-sample w) true) (= (hkw-rest kc ke w) true) (= (hkw kc ke w) true))
  (intros h1 h2) (simp only [hkw h1 h2 Bool.and_self]))
(a/theorem hkw-parts [kc :- Nat, ke :- Nat, w :- World]
  (=> (= (hkw kc ke w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (hkw-sample kc ke w h))))
(a/theorem hkw-rest-same [kc :- Nat, ke :- Nat, w :- World, w2 :- World]
  (=> (= (gdkeys (:comps w2)) (gdkeys (:comps w))) (= (hkw-rest kc ke w) true) (= (hkw-rest kc ke w2) true))
  (intros e h) (simp only [hkw-rest e]) (simp only [hkw-rest] at h) (exact h))
(a/theorem hkw-one-mono [kc :- Nat, ke :- Nat, k :- GDK, d :- GDK]
  (=> (= (Nat.blt 0 ke) true) (= (gd-cmono k d) true) (= (hkw-one kc ke k) true) (= (hkw-one kc ke d) true))
  (intros he hm h)
  (simp only [gd-cmono Bool.and_eq_true Bool.or_eq_true] at hm)
  (have hid := (Nat.eq_of_beq_eq_true (And.left hm)))
  (have hep := (gd-le-of _ _ (And.left (And.right (And.right hm)))))
  (have hd := (And.right (And.right (And.right hm))))
  (have e0 := (gd-lt-of _ _ he))
  (simp only [hkw-one hid]) (simp only [hkw-one Bool.or_eq_true Bool.and_eq_true] at h)
  (cases h)
  (case [inl a1] (simp only [a1 Bool.true_or]))
  (case [inr a1]
    (have q1 := (gd-le-of _ _ (And.left a1)))
    (have q2 := (bnot-true _ (And.right a1)))
    (have r1 := (gd-ble-of _ _ (Nat.le_trans q1 hep)))
    (have r2 (= (Nat.beq (:done d) ke) false))
    (cases hd)
    (case [inl z] (rw [(Nat.eq_of_beq_eq_true z)]) (exact q2))
    (case [inr z] (rw [(Nat.eq_of_beq_eq_true z)]) (exact (gd-beq-lt2 _ _ e0)))
    (simp only [r1 r2 Bool.not_false Bool.and_self Bool.or_true])))
(a/theorem hkw-comp-upd [kc :- Nat, ke :- Nat, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hk :- (forall [c :- CompRow] (= (gdkey (f c)) (gdkey c)))]
  (=> (= (hkw kc ke w) true) (= (hkw kc ke (comp-upd w x f)) true))
  (intro h)
  (exact (hkw-intro kc ke _ (inv-comp-upd w x f hid hp (hkw-sample kc ke w h))
           (hkw-rest-same kc ke w (comp-upd w x f) (gdkeys-upd x f hk (:comps w)) (hkw-rest-of kc ke w h)))))
(a/theorem hkw-comp-upd-m [kc :- Nat, ke :- Nat, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                          hm :- (forall [c :- CompRow] (= (gd-cmono (gdkey c) (gdkey (f c))) true))]
  (=> (= (hkw kc ke w) true) (= (hkw kc ke (comp-upd w x f)) true))
  (intro h)
  (have r := (hkw-rest-of kc ke w h))
  (simp only [hkw-rest Bool.and_eq_true] at r)
  (have r2 (= (hkw-rest kc ke (comp-upd w x f)) true))
  (simp only [hkw-rest comp-upd set-comps (And.left r) Bool.true_and])
  (have q := (And.right r)) (rw [all-gdkeys] at q) (rw [all-gdkeys])
  (exact (tbl-all-upd CompRow comp-id x f (fn [c :- CompRow] (hkw-one kc ke (gdkey c))) (fn [c :- CompRow] (hkw-one kc ke (gdkey c)))
           (fn [c :- CompRow, h1 :- (= (hkw-one kc ke (gdkey c)) true), h2 :- (= (Nat.beq (comp-id c) x) true)]
             (hkw-one-mono kc ke (gdkey c) (gdkey (f c)) (And.left r) (hm c) h1))
           (fn [c :- CompRow, h1 :- (= (hkw-one kc ke (gdkey c)) true), h2 :- (= (Nat.beq (comp-id c) x) false)] h1)
           (:comps w) q))
  (exact (hkw-intro kc ke _ (inv-comp-upd w x f hid hp (hkw-sample kc ke w h)) r2)))
(a/theorem hkwr-mark-edge [kc :- Nat, ke :- Nat, w :- World, x :- Nat] (=> (= (hkw-rest kc ke w) true) (= (hkw-rest kc ke (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false]
      (simp only [mark-edge hf hm])
      (exact (hkw-rest-same kc ke w (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending)
               (gdkeys-upd (:creditor e) comp-inc-pending gd-key-inc-pending (:comps w)) h)))))
(a/theorem hkwr-unmark-edge [kc :- Nat, ke :- Nat, w :- World, x :- Nat] (=> (= (hkw-rest kc ke w) true) (= (hkw-rest kc ke (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true]
      (simp only [unmark-edge hf hm])
      (exact (hkw-rest-same kc ke w (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending)
               (gdkeys-upd (:creditor e) comp-dec-pending gd-key-dec-pending (:comps w)) h)))))
(a/theorem hkwr-remove-edge [kc :- Nat, ke :- Nat, w :- World, x :- Nat] (=> (= (hkw-rest kc ke w) true) (= (hkw-rest kc ke (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact (hkw-rest-same kc ke w (edge-del w x) (rfl) h)))
    (case [true]
      (simp only [remove-edge hf hm])
      (exact (hkw-rest-same kc ke w (comp-upd (edge-del w x) (:creditor e) comp-dec-pending)
               (gdkeys-upd (:creditor e) comp-dec-pending gd-key-dec-pending (:comps w)) h)))))
(a/theorem hkwr-drop-cred [kc :- Nat, ke :- Nat, w :- World, a :- Nat] (=> (= (hkw-rest kc ke w) true) (= (hkw-rest kc ke (drop-cred-edges w a)) true))
  (intro h) (simp only [drop-cred-edges])
  (exact (hkw-rest-same kc ke w (comp-upd (set-edges w (tbl-filter (cred-ne a) (:edges w))) a (comp-set-pending 0))
           (gdkeys-upd a (comp-set-pending 0) (gd-key-set-pending 0) (:comps w)) h)))
(a/theorem hkwr-drop-act [kc :- Nat, ke :- Nat, w :- World, a :- Nat] (=> (= (hkw-rest kc ke w) true) (= (hkw-rest kc ke (drop-act w a)) true))
  (intro h) (simp only [drop-act])
  (exact (hkw-rest-same kc ke (drop-cred-edges w a) (act-del (drop-cred-edges w a) a) (rfl) (hkwr-drop-cred kc ke w a h))))
(a/theorem hkwr-drop-edges [kc :- Nat, ke :- Nat, w :- World, p :- (=> EdgeRow Bool)] (=> (= (hkw-rest kc ke w) true) (= (hkw-rest kc ke (drop-edges w p)) true))
  (intro h) (simp only [drop-edges])
  (exact (hkw-rest-same kc ke w (set-comps (set-edges w (tbl-filter p (:edges w))) (comps-resync (tbl-filter p (:edges w)) (:comps w)))
           (gdkeys-resync (tbl-filter p (:edges w)) (:comps w)) h)))
(a/theorem hkwr-comp-del [kc :- Nat, ke :- Nat, w :- World, x :- Nat] (=> (= (hkw-rest kc ke w) true) (= (hkw-rest kc ke (comp-del w x)) true))
  (intro h) (simp only [hkw-rest comp-del set-comps gdkeys-del Bool.and_eq_true]) (simp only [hkw-rest Bool.and_eq_true] at h)
  (exact (And.intro (And.left h) (tbl-all-del GDK gdk-id x (hkw-one kc ke) (hkw-one kc ke)
                                    (fn [k :- GDK, h1 :- (= (hkw-one kc ke k) true), h2 :- (= (Nat.beq (gdk-id k) x) false)] h1) _ (And.right h)))))
(a/theorem hkwr-filter-world [kc :- Nat, ke :- Nat, w :- World, K :- (=> Nat Bool)] (=> (= (hkw-rest kc ke w) true) (= (hkw-rest kc ke (filter-world K w)) true))
  (intro h) (simp only [hkw-rest filter-world gdkeys-keep Bool.and_eq_true]) (simp only [hkw-rest Bool.and_eq_true] at h)
  (exact (And.intro (And.left h) (tbl-all-keep GDK K gdk-id (hkw-one kc ke) (hkw-one kc ke)
                                    (fn [k :- GDK, h1 :- (= (hkw-one kc ke k) true), h2 :- (= (K (gdk-id k)) true)] h1) _ (And.right h)))))
(a/theorem hkwr-insert-edge-checked [kc :- Nat, ke :- Nat, w :- World, e :- EdgeRow]
  (=> (= (hkw-rest kc ke w) true) (= (hkw-rest kc ke (insert-edge-checked w e)) true))
  (intro h)
  (cases hk (edge-ok-in w e))
  (simp only [insert-edge-checked hk]) (exact h)
  (simp only [insert-edge-checked hk]) (exact h))

(def HKW (mk-bundle 'hkw '[hkc :- Nat, hke :- Nat] "hkw-" {}))
(swap! (:renames HKW) assoc 'inv-parts 'hkw-parts)
(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-set-pins
            inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-task-upd inv-edge-upd inv-run-upd inv-run-del
            inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-act-ins-fresh inv-task-ins-fresh inv-run-ins-fresh
            inv-bump insert-edge-fresh-inv-sample]]
  (prim! HKW o nil))
(prim! HKW 'inv-insert-edge-checked '(hkwr-insert-edge-checked hkc hke w e R))
(prim! HKW 'inv-remove-edge '(hkwr-remove-edge hkc hke w x R))
(prim! HKW 'mark-edge-inv-sample '(hkwr-mark-edge hkc hke w x R))
(prim! HKW 'unmark-edge-inv-sample '(hkwr-unmark-edge hkc hke w x R))
(prim! HKW 'inv-drop-cred '(hkwr-drop-cred hkc hke w a R))
(prim! HKW 'inv-drop-act '(hkwr-drop-act hkc hke w a R))
(prim! HKW 'inv-drop-edges '(hkwr-drop-edges hkc hke w p R))
(prim! HKW 'inv-comp-del-unref '(hkwr-comp-del hkc hke w x R))
(prim! HKW 'inv-filter-world '(hkwr-filter-world hkc hke w K R))
(defn hkw-patch [form]
  (->> (@#'spindel.v2.idle/fix-f form)
       (subst-forms (fn [y] (and (seq? y) (= 'inv-comp-upd (first y)) (>= (count y) 6)))
                    (fn [[_ w x f hid hp & more]]
                      (let [h (gd-fhead f)]
                        (if (contains? gd-cm h)
                          (apply list 'hkw-comp-upd-m 'hkc 'hke w x f hid hp (gd-lapp f (symbol (str h "-gcm"))) more)
                          (apply list 'hkw-comp-upd 'hkc 'hke w x f hid hp '(fn [c :- CompRow] (Eq.refl (gdkey c))) more)))))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! HKW n hkw-patch))
(lcopy! HKW 'inv-cancel-pred)
(lcopy! HKW 'inv-cut-suffix)
(lcopy! HKW 'inv-consume-entry)

(a/theorem hkw-ok-new [kc :- Nat, ke :- Nat, k :- GDK] (=> (= (hkw-one kc ke k) true) (= (gd-ok-new kc ke k) true))
  (intro h)
  (simp only [hkw-one Bool.or_eq_true Bool.and_eq_true] at h)
  (cases h)
  (case [inl a1] (simp only [gd-ok-new a1 Bool.true_or]))
  (case [inr a1]
    (cases he (Nat.beq (:epoch k) ke))
    (case [false] (simp only [gd-ok-new he Bool.not_false Bool.true_or Bool.or_true]))
    (case [true]
      (have e := (Nat.eq_of_beq_eq_true he))
      (have d (= (Nat.beq (:done k) (:epoch k)) false)) (rw [e]) (exact (bnot-true _ (And.right a1)))
      (simp only [gd-ok-new d Bool.not_false Bool.or_true]))))
(a/theorem gd-setrun-c [rs :- (List RunRow), n :- Nat, k :- GDK, c :- Nat, e :- Nat, ei :- Nat]
  (=> (= (gd-c (tbl-ins (new-run-row n c e (+ n 1) ei) rs) (+ (+ n 1) 1) k) true)
      (= (tbl-all (fn [r :- RunRow] (Nat.blt (:id r) n)) rs) true) (= (:id k) c)
      (= (gd-c (tbl-ins (new-run-row n c e (+ n 1) ei) rs) (+ (+ n 1) 1) (GDK.mk (:id k) n (:epoch k) (:done k))) true))
  (intros hc hb hi)
  (have p := (gd-c-parts _ _ _ hc))
  (have g1 (= (gd-dle (GDK.mk (:id k) n (:epoch k) (:done k))) true)) (exact (And.left p))
  (have g2 (= (Nat.blt (:run (GDK.mk (:id k) n (:epoch k) (:done k))) (+ (+ n 1) 1)) true))
  (apply gd-blt-of) (show (< n (+ (+ n 1) 1))) (omega)
  (have g3 (= (tbl-all (gd-rof (GDK.mk (:id k) n (:epoch k) (:done k))) (tbl-ins (new-run-row n c e (+ n 1) ei) rs)) true))
  (simp only [tbl-ins tbl-all gd-rof new-run-row hi Nat.beq_refl Bool.or_true Bool.true_and])
  (apply (tbl-all-mono RunRow _ _ _ rs hb))
  (intros r hr)
  (have z := (gd-beq-lt2 _ _ (gd-lt-of _ _ hr)))
  (simp only [gd-rof z Bool.not_false Bool.true_or])
  (have g4 (= (gd-cde (tbl-ins (new-run-row n c e (+ n 1) ei) rs) (GDK.mk (:id k) n (:epoch k) (:done k))) true))
  (have q := (And.right (And.right (And.right p)))) (simp only [gd-cde] at q) (simp only [gd-cde]) (exact q)
  (exact (gd-c-intro _ _ _ g1 g2 g3 g4)))

(override! GD 'inv-new-run-of '[inv-add-run-scope]
  '(a/theorem gd-new-run-of [w :- World, c :- CompRow, ei :- Nat]
     (=> (= (hkw (:id c) (:epoch c) w) true) (= (gd w) true) (= (gd (new-run-of w c ei)) true))
     (intros k h)
     (have hs := (gd-sample w h))
     (have kr := (hkw-rest-of _ _ w k)) (simp only [hkw-rest Bool.and_eq_true] at kr)
     (have ho := (tbl-all-mono GDK (hkw-one (:id c) (:epoch c)) (gd-ok-new (:id c) (:epoch c))
                   (fn [x :- GDK, hx :- (= (hkw-one (:id c) (:epoch c) x) true)] (hkw-ok-new _ _ x hx)) _ (And.right kr)))
     (have h1 := (gd-add-run-scope w (:id c) (:epoch c) 0 ei ho h))
     (have r1 := (gdk-parts _ _ _ (gd-rest-of _ h1)))
     (have q1 := (And.right r1))
     (change (= (tbl-all (gd-c (tbl-ins (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1))
                         (gdkeys (:comps w))) true) at q1)
     (rw [all-gdkeys] at q1)
     (have hb := (gd-runs-below w hs))
     (have rr (= (gd-rest (new-run-of w c ei)) true))
     (show (= (gdk (gdkeys (tbl-upd comp-id (:id c) (comp-set-run (:next-id w)) (:comps w)))
                   (tbl-ins (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1)) true))
     (simp only [gdk (And.left r1) Bool.true_and])
     (rw [all-gdkeys])
     (exact (tbl-all-upd CompRow comp-id (:id c) (comp-set-run (:next-id w))
              (fn [x :- CompRow] (gd-c (tbl-ins (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1) (gdkey x)))
              (fn [x :- CompRow] (gd-c (tbl-ins (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1) (gdkey x)))
              (fn [x :- CompRow, hx :- (= (gd-c (tbl-ins (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1) (gdkey x)) true),
                   hi :- (= (Nat.beq (comp-id x) (:id c)) true)]
                (gd-setrun-c (:runs w) (:next-id w) (gdkey x) (:id c) (:epoch c) ei hx hb (Nat.eq_of_beq_eq_true hi)))
              (fn [x :- CompRow, hx :- (= (gd-c (tbl-ins (new-run-row (:next-id w) (:id c) (:epoch c) (+ (:next-id w) 1) ei) (:runs w)) (+ (+ (:next-id w) 1) 1) (gdkey x)) true),
                   hi :- (= (Nat.beq (comp-id x) (:id c)) false)] hx)
              (:comps w) q1))
     (exact (gd-intro _ (inv-new-run-of w c ei hs) rr))))

(a/theorem hkw-start [w :- World, c :- CompRow]
  (=> (= (gd w) true) (List.Mem c (:comps w)) (= (Nat.beq (:done-epoch c) (:epoch c)) false) (= (hkw (:id c) (:epoch c) w) true))
  (intros h hm hd)
  (have hs := (gd-sample w h))
  (have p := (gdk-parts _ _ _ (gd-rest-of w h)))
  (have q := (And.right p)) (rw [all-gdkeys] at q)
  (have hc0 := (tbl-all-mem CompRow (fn [x :- CompRow] (gd-c (:runs w) (:next-id w) (gdkey x))) c (:comps w) q hm))
  (have dl := (And.left (gd-c-parts _ _ _ hc0))) (simp only [gd-dle gdkey Bool.and_eq_true] at dl)
  (have qc (= (hkw-one (:id c) (:epoch c) (gdkey c)) true))
  (simp only [hkw-one gdkey gd-ble-refl hd Bool.not_false Bool.and_self Bool.or_true])
  (have u := (gd-same-id w c (fn [x :- CompRow] (hkw-one (:id c) (:epoch c) (gdkey x))) hs hm qc))
  (have r (= (hkw-rest (:id c) (:epoch c) w) true))
  (simp only [hkw-rest (And.right dl) Bool.true_and])
  (rw [all-gdkeys])
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) u))
  (intros x hx)
  (cases hi (Nat.beq (comp-id x) (:id c)))
  (case [false] (have hi2 (= (Nat.beq (:id x) (:id c)) false)) (exact hi) (simp only [hkw-one gdkey hi2 Bool.not_false Bool.true_or]))
  (case [true] (simp only [same-id-then hi Bool.not_true Bool.false_or] at hx) (exact hx))
  (exact (hkw-intro _ _ w hs r)))

(override! GD 'inv-dispatch-raw '[inv-cancel-pred inv-cut-suffix inv-consume-entry inv-new-run-of]
  '(a/theorem gd-dispatch-raw [w :- World, c :- CompRow]
     (=> (List.Mem c (:comps w)) (= (Nat.beq (:done-epoch c) (:epoch c)) false) (= (gd w) true) (= (gd (dispatch-raw w c)) true))
     (intros hm hd h)
     (have k0 := (hkw-start w c h hm hd))
     (have h1 := (gd-cancel-pred w c h))
     (have k1 := (hkw-cancel-pred (:id c) (:epoch c) w c k0))
     (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
     (simp only [dispatch-raw he])
     (exact (gd-new-run-of (cut-suffix (cancel-pred w c) (:id c) false 0 0) c 0
              (hkw-cut-suffix (:id c) (:epoch c) (cancel-pred w c) (:id c) false 0 0 k1)
              (gd-cut-suffix (cancel-pred w c) (:id c) false 0 0 h1)))
     (simp only [dispatch-raw he])
     (exact (gd-new-run-of (consume-entry (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e) c (entry-ei e)
              (hkw-consume-entry (:id c) (:epoch c) (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e
                (hkw-cut-suffix (:id c) (:epoch c) (cancel-pred w c) (:id c) true (:at e) (:id e) k1))
              (gd-consume-entry (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e
                (gd-cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e) h1))))))
(override! GD 't11-inv '[inv-dispatch-raw]
  '(a/theorem t11-gd [w :- World, cid :- Nat, fresh :- Nat]
     (=> (= (gd w) true) (= (gd (:world (t11-dispatch w cid fresh))) true))
     (intro h)
     (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
     (simp only [t11-dispatch hc refuse]) (exact h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))))
     (simp only [t11-dispatch hc hg refuse]) (exact h)
     (have hd (= (Nat.beq (:done-epoch c) (:epoch c)) false))
     (simp only [needs-run Bool.and_eq_true] at hg) (exact (bnot-true _ (And.left (And.left (And.right (And.right hg))))))
     (simp only [t11-dispatch hc hg accept]) (exact (gd-dispatch-raw w c (tbl-find-mem CompRow comp-id cid c (:comps w) hc) hd h))))

;; ---- T12: done-epoch := epoch for the completed current run's computation; its run is done and,
;; by i10's cur-ok (a run at C's epoch is C.run, unique ids), it was C's only run at that epoch
(a/defn gd-noal [o :- Nat, e :- Nat, q :- RunRow] Bool
  (Bool.not (Bool.and (Nat.beq (:of q) o) (Bool.and (Nat.beq (:epoch q) e) (run-alive q)))))
(a/defn gd-u1 [r :- RunRow, q :- RunRow] Bool (Bool.or (Nat.beq (:id q) (:id r)) (gd-noal (:of r) (:epoch r) q)))
(a/defn gd-cce [w :- World, r :- RunRow] Bool
  (match (comp-find w (:of r)) [none false] [(some c) (Nat.beq (:epoch r) (:epoch c))]))

(a/theorem gd-result-c [rs :- (List RunRow), n :- Nat, c :- CompRow, ep :- Nat, res :- RunResult]
  (=> (= (gd-c rs n (gdkey c)) true) (= ep (:epoch c)) (= (tbl-all (gd-noal (:id c) (:epoch c)) rs) true)
      (= (gd-c rs n (gdkey (comp-result-row res ep c))) true))
  (intros hc he hn)
  (have p := (gd-c-parts _ _ _ hc))
  (have dl := (And.left p)) (simp only [gd-dle gdkey Bool.and_eq_true] at dl)
  (have g1 (= (gd-dle (gdkey (comp-result-row res ep c))) true))
  (simp only [gd-dle gdkey comp-result-row he gd-ble-refl (And.right dl) Bool.and_self])
  (have g4 (= (gd-cde rs (gdkey (comp-result-row res ep c))) true))
  (simp only [gd-cde gdkey comp-result-row he Nat.beq_refl Bool.not_true Bool.false_or])
  (apply (tbl-all-mono RunRow _ _ _ rs hn))
  (intros q hq) (simp only [gd-noal] at hq) (simp only [gd-ncur]) (exact hq)
  (exact (gd-c-intro _ _ _ g1 (And.left (And.right p)) (And.left (And.right (And.right p))) g4)))

(override! GD 'inv-complete-body '[inv-settle inv-cancel-res nat-fold-inv inv-fire-edge inv-task-upd]
  '(a/theorem gd-complete-body [w :- World, r :- RunRow, res :- RunResult]
     (=> (= (Bool.or (Bool.not (gd-cce w r)) (tbl-all (gd-noal (:of r) (:epoch r)) (:runs w))) true) (= (gd w) true)
         (= (gd (:world (complete-body w r res))) true))
     (intros hpre h)
     (cases hc (comp-find w (:of r)))
     (case [none]
       (cases hk (task-find w (:of r)))
       (case [none] (simp only [complete-body hc hk]) (exact h))
       (case [some k]
         (simp only [complete-body hc hk complete-task])
         (exact (nat-fold-gd (fire-edge res) (gd-fire-edge res) _ _
                  (gd-cancel-res _ r (gd-task-upd w (:id k) (task-result-row res) (task-result-row-id res) h))))))
     (case [some c]
       (cases he (Nat.beq (:epoch r) (:epoch c)))
       (case [false] (simp only [complete-body hc he]) (exact h))
       (case [true]
         (have hs := (gd-sample w h))
         (have mc := (tbl-find-mem CompRow comp-id (:of r) c (:comps w) hc))
         (have ic (= (:id c) (:of r))) (exact (tbl-find-id CompRow comp-id (:of r) c (:comps w) hc))
         (have ee := (Nat.eq_of_beq_eq_true he))
         (simp only [gd-cce hc he Bool.not_true Bool.false_or] at hpre)
         (have hn (= (tbl-all (gd-noal (:id c) (:epoch c)) (:runs w)) true)) (rw [ic]) (rw [← ee]) (exact hpre)
         (have p := (gdk-parts _ _ _ (gd-rest-of w h)))
         (have q := (And.right p)) (rw [all-gdkeys] at q)
         (have hc0 := (tbl-all-mem CompRow (fn [x :- CompRow] (gd-c (:runs w) (:next-id w) (gdkey x))) c (:comps w) q mc))
         (have u := (gd-same-id w c (fn [x :- CompRow] (gd-c (:runs w) (:next-id w) (gdkey (comp-result-row res (:epoch r) x)))) hs mc
                      (gd-result-c (:runs w) (:next-id w) c (:epoch r) res hc0 ee hn)))
         (have r1 (= (gd-rest (comp-upd w (:id c) (comp-result-row res (:epoch r)))) true))
         (show (= (gdk (gdkeys (tbl-upd comp-id (:id c) (comp-result-row res (:epoch r)) (:comps w))) (:runs w) (:next-id w)) true))
         (simp only [gdk (And.left p) Bool.true_and])
         (rw [all-gdkeys])
         (exact (gd-upd-same (:id c) (comp-result-row res (:epoch r)) _ _
                  (fn [x :- CompRow, hx :- (= (gd-c (:runs w) (:next-id w) (gdkey x)) true)] hx) (:comps w) q u))
         (have h1 := (gd-intro _ (inv-comp-upd w (:id c) (comp-result-row res (:epoch r)) (comp-result-row-id res (:epoch r))
                                   (comp-result-row-pending res (:epoch r)) hs) r1))
         (simp only [complete-body hc he complete-comp])
         (exact (gd-settle _ (:id c) _ (gd-cancel-res _ r h1)))))))

(a/theorem gd-noal-done [o :- Nat, e :- Nat, q :- RunRow] (= (gd-noal o e (run-complete-row q)) true)
  (simp [gd-noal run-complete-row run-alive act-done]))
(a/theorem gd-u1-ne [r :- RunRow, q :- RunRow]
  (=> (= (gd-u1 r q) true) (= (Nat.beq (run-id q) (:id r)) false) (= (gd-noal (:of r) (:epoch r) q) true))
  (intros h1 h2)
  (have h3 (= (Nat.beq (:id q) (:id r)) false)) (exact h2)
  (simp only [gd-u1 h3 Bool.false_or] at h1) (exact h1))
(a/theorem gd-noal-upd [r :- RunRow, rs :- (List RunRow)]
  (=> (= (tbl-all (gd-u1 r) rs) true) (= (tbl-all (gd-noal (:of r) (:epoch r)) (tbl-upd run-id (:id r) run-complete-row rs)) true))
  (intro h)
  (exact (tbl-all-upd RunRow run-id (:id r) run-complete-row (gd-u1 r) (gd-noal (:of r) (:epoch r))
           (fn [q :- RunRow, h1 :- (= (gd-u1 r q) true), h2 :- (= (Nat.beq (run-id q) (:id r)) true)] (gd-noal-done (:of r) (:epoch r) q))
           (fn [q :- RunRow, h1 :- (= (gd-u1 r q) true), h2 :- (= (Nat.beq (run-id q) (:id r)) false)] (gd-u1-ne r q h1 h2))
           rs h)))
(a/theorem gd-u1-of-g10r [w :- World, r :- RunRow]
  (=> (= (g10r w) true) (List.Mem r (:runs w)) (= (Bool.or (Bool.not (gd-cce w r)) (tbl-all (gd-u1 r) (:runs w))) true))
  (intros h mr)
  (cases hc (comp-find w (:of r)))
  (case [none] (simp only [gd-cce hc Bool.not_false Bool.true_or]))
  (case [some c]
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [gd-cce hc he Bool.not_false Bool.true_or]))
    (case [true]
      (simp only [gd-cce hc he Bool.not_true Bool.false_or])
      (have mc := (tbl-find-mem CompRow comp-id (:of r) c (:comps w) hc))
      (have ic (= (:id c) (:of r))) (exact (tbl-find-id CompRow comp-id (:of r) c (:comps w) hc))
      (have ee := (Nat.eq_of_beq_eq_true he))
      (have pr := (rc-parts _ _ (rk10 r) (ck10 c) (g10-rc _ _ w r c h mr mc) (Eq.refl false)))
      (have hor (= (Nat.beq (:of (rk10 r)) (:id (ck10 c))) true)) (show (= (Nat.beq (:of r) (:id c)) true)) (rw [ic]) (exact (Nat.beq_refl _))
      (have cr := (And.left (cur-eq _ (rk10 r) (ck10 c) (And.left pr) hor he)))
      (apply (all-of-mem RunRow _ (:runs w)))
      (intros q mq)
      (simp only [gd-u1 Bool.or_eq_true])
      (cases hi (Nat.beq (:id q) (:id r)))
      (case [true] (exact (Or.inl (rfl))))
      (case [false]
        (apply Or.inr)
        (cases hq (Bool.and (Nat.beq (:of q) (:of r)) (Bool.and (Nat.beq (:epoch q) (:epoch r)) (run-alive q))))
        (case [false] (simp only [gd-noal hq Bool.not_false]))
        (case [true]
          (simp only [Bool.and_eq_true] at hq)
          (have pq := (rc-parts _ _ (rk10 q) (ck10 c) (g10-rc _ _ w q c h mq mc) (Eq.refl false)))
          (have hoq (= (Nat.beq (:of (rk10 q)) (:id (ck10 c))) true))
          (show (= (Nat.beq (:of q) (:id c)) true)) (rw [ic]) (exact (And.left hq))
          (have heq (= (Nat.beq (:epoch (rk10 q)) (:epoch (ck10 c))) true))
          (show (= (Nat.beq (:epoch q) (:epoch c)) true)) (rw [← ee]) (exact (And.left (And.right hq)))
          (have cq := (And.left (cur-eq _ (rk10 q) (ck10 c) (And.left pq) hoq heq)))
          (have e2 (= (:id q) (:id r))) (exact (Eq.trans (Eq.symm cq) cr))
          (rw [e2] at hi) (simp [Nat.beq_refl] at hi))))))

(override! GD 'inv-complete-raw '[inv-fin-if-final inv-retire-after inv-complete-body inv-run-cascade]
  '(a/theorem gd-complete-raw [w :- World, r :- RunRow, res :- RunResult]
     (=> (= (Bool.or (Bool.not (gd-cce w r)) (tbl-all (gd-u1 r) (:runs w))) true) (= (gd w) true) (= (gd (complete-raw w r res)) true))
     (intros hpre h)
     (have h0 := (gd-run-upd-m w (:id r) run-complete-row run-complete-row-id run-complete-row-grm h))
     (have ce (= (gd-cce (run-upd w (:id r) run-complete-row) r) (gd-cce w r))) (rfl)
     (have p2 (= (Bool.or (Bool.not (gd-cce (run-upd w (:id r) run-complete-row) r))
                          (tbl-all (gd-noal (:of r) (:epoch r)) (:runs (run-upd w (:id r) run-complete-row)))) true))
     (cases hc (gd-cce w r))
     (case [false] (simp only [ce hc Bool.not_false Bool.true_or]))
     (case [true]
       (simp only [hc Bool.not_true Bool.false_or] at hpre)
       (simp only [ce hc Bool.not_true Bool.false_or])
       (exact (gd-noal-upd r (:runs w) hpre)))
     (simp only [complete-raw])
     (exact (gd-fin-if-final _ (:of r) (gd-run-cascade _ _ (gd-retire-after _ (:id r) (gd-complete-body _ r res p2 h0)))))))
(override! GD 't12-inv '[inv-complete-raw]
  '(a/theorem t12-gd [w :- World, st :- Nat, tag :- Nat, v :- Nat]
     (=> (= (g10r w) true) (= (gd w) true) (= (gd (:world (t12-complete w st tag v))) true))
     (intros hg h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t12-complete ht refuse]) (exact h)
     (cases hn (run-normal r))
     (simp only [t12-complete ht hn refuse]) (exact h)
     (simp only [t12-complete ht hn accept])
     (exact (gd-complete-raw w r _ (gd-u1-of-g10r w r hg (And.left (tok-facts w st r ht))) h))))

;; ---- reactivation (done-epoch := epoch on an idle computation): no alive run (g7's a7, threaded)
(a/theorem gd-noal-idle [w :- World, c :- CompRow]
  (=> (= (g7 w) true) (List.Mem c (:comps w)) (= (:idle c) true) (= (tbl-all (gd-noal (:id c) (:epoch c)) (:runs w)) true))
  (intros h mc hi)
  (have p := (g7k-parts _ _ _ (g7-rest-of w h)))
  (apply (tbl-all-mono RunRow (a7-one (:comps w)) _ _ (:runs w) (And.left p)))
  (intros q hq)
  (cases ha (Bool.and (Nat.beq (:of q) (:id c)) (Bool.and (Nat.beq (:epoch q) (:epoch c)) (run-alive q))))
  (case [false] (simp only [gd-noal ha Bool.not_false]))
  (case [true]
    (simp only [Bool.and_eq_true] at ha)
    (simp only [a7-one (And.right (And.right ha)) Bool.not_true Bool.false_or awake] at hq)
    (have z := (tbl-all-mem CompRow (not-idle-if-id (:of q)) c (:comps w) hq mc))
    (have e := (Nat.eq_of_beq_eq_true (And.left ha)))
    (simp only [not-idle-if-id] at z) (rw [e] at z)
    (simp [Nat.beq_refl hi] at z)))
(a/theorem gd-react-c [rs :- (List RunRow), n :- Nat, c :- CompRow]
  (=> (= (gd-c rs n (gdkey c)) true) (= (tbl-all (gd-noal (:id c) (:epoch c)) rs) true) (= (gd-c rs n (gdkey (comp-react-row c))) true))
  (intros hc hn)
  (have p := (gd-c-parts _ _ _ hc))
  (have dl := (And.left p)) (simp only [gd-dle gdkey Bool.and_eq_true] at dl)
  (have g1 (= (gd-dle (gdkey (comp-react-row c))) true))
  (simp only [gd-dle gdkey comp-react-row gd-ble-refl (And.right dl) Bool.and_self])
  (have g4 (= (gd-cde rs (gdkey (comp-react-row c))) true))
  (simp only [gd-cde gdkey comp-react-row Nat.beq_refl Bool.not_true Bool.false_or])
  (apply (tbl-all-mono RunRow _ _ _ rs hn))
  (intros q hq) (simp only [gd-noal] at hq) (simp only [gd-ncur]) (exact hq)
  (exact (gd-c-intro _ _ _ g1 (And.left (And.right p)) (And.left (And.right (And.right p))) g4)))
(override! GD 'inv-react-one '[inv-react-edges]
  '(a/theorem gd-react-one [w :- World, c :- CompRow]
     (=> (= (g7 w) true) (List.Mem c (:comps w)) (= (:idle c) true) (= (gd w) true) (= (gd (react-one w c)) true))
     (intros hg mc hi h)
     (have hs := (gd-sample w h))
     (have p := (gdk-parts _ _ _ (gd-rest-of w h)))
     (have q := (And.right p)) (rw [all-gdkeys] at q)
     (have hc0 := (tbl-all-mem CompRow (fn [x :- CompRow] (gd-c (:runs w) (:next-id w) (gdkey x))) c (:comps w) q mc))
     (have u := (gd-same-id w c (fn [x :- CompRow] (gd-c (:runs w) (:next-id w) (gdkey (comp-react-row x)))) hs mc
                  (gd-react-c (:runs w) (:next-id w) c hc0 (gd-noal-idle w c hg mc hi))))
     (have r1 (= (gd-rest (comp-upd w (:id c) comp-react-row)) true))
     (show (= (gdk (gdkeys (tbl-upd comp-id (:id c) comp-react-row (:comps w))) (:runs w) (:next-id w)) true))
     (simp only [gdk (And.left p) Bool.true_and])
     (rw [all-gdkeys])
     (exact (gd-upd-same (:id c) comp-react-row _ _ (fn [x :- CompRow, hx :- (= (gd-c (:runs w) (:next-id w) (gdkey x)) true)] hx) (:comps w) q u))
     (have h1 := (gd-intro _ (inv-comp-upd w (:id c) comp-react-row comp-react-row-id comp-react-row-pending hs) r1))
     (simp only [react-one])
     (exact (gd-react-edges (:validity c) (comp-upd w (:id c) comp-react-row) (:id c) h1))))
(override! GD 'inv-react-loop '[inv-react-one]
  '(a/theorem gd-react-loop [fuel :- (List Nat)]
     (forall [w :- World, q :- (List Nat)] (=> (= (g7 w) true) (= (gd w) true) (= (gd (react-loop fuel w q)) true)))
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
     (exact (ih (react-one w c) _ (g7-react-one w c hg) (gd-react-one w c hg mc hi hw)))))
(override! GD 'inv-demand-reactive '[inv-react-loop]
  '(a/theorem gd-demand-reactive [w :- World, d :- Nat]
     (=> (= (g7 w) true) (= (gd w) true) (= (gd (demand-reactive w d)) true))
     (intros hg h)
     (cases hc (comp-find w d)) (case' [some c]) (case' [none])
     (simp only [demand-reactive hc]) (exact h)
     (cases hi (:idle c))
     (simp only [demand-reactive hc hi]) (exact h)
     (cases hv (valid-idle w c))
     (simp only [demand-reactive hc hi hv]) (exact (gd-comp-upd-m w d comp-demand-row comp-demand-row-id comp-demand-row-pending comp-demand-row-gcm h))
     (simp only [demand-reactive hc hi hv]) (exact (gd-react-loop (react-fuel w) w _ hg h))))
(lcopy! GD 'inv-demand-reactive)
(a/theorem gd-df [ds :- (List Nat)]
  (forall [w :- World] (=> (= (g7 w) true) (= (gd w) true) (= (gd (nat-fold demand-reactive w ds)) true)))
  (induction ds)
  (case [nil] (intros w hg h) (simp only [nat-fold]) (exact h))
  (case [cons x t ih]
    (intros w hg h) (simp only [nat-fold])
    (exact (ih (demand-reactive w x) (g7-demand-reactive w x hg) (gd-demand-reactive w x hg h)))))
(override! GD 'inv-await-pre '[inv-demand-reactive]
  '(a/theorem gd-await-pre [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
     (=> (= (g7 w) true) (= (gd w) true) (= (gd (await-pre w r ds mode k mine)) true))
     (intros hg h)
     (have h1 := (gd-run-upd-m w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (gd-rmono-key q (run-tick q) (Eq.refl (gdrk q)))) h))
     (have g1 := (g7-run-upd w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (rk7 q))) hg))
     (have he (= (act-id (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine))
                 (:next-id (run-upd w (:id r) run-tick))))
     (rfl)
     (simp only [await-pre])
     (exact (gd-df (nat-distinct ds) _ (g7-act-ins-fresh _ _ he g1) (gd-act-ins-fresh _ _ he h1)))))
(override! GD 'inv-await-raw '[inv-await-wire inv-await-pre inv-await-post]
  '(a/theorem gd-await-raw [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
     (=> (= (g7 w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (gd w) true) (= (gd (await-raw w r ds mode k mine)) true))
     (intros hg hm hal h)
     (have hs := (gd-sample w h))
     (have k0 := (ka-intro (:id r) w hs (run-ok-of-mem w r hs hm hal)))
     (have k1 := (ka-await-wire (:id r) r (:next-id w) mode k (nat-distinct ds)
                   (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (ka-await-pre (:id r) w r ds mode k mine k0)))
     (have h1 := (gd-await-wire r (:next-id w) mode k (nat-distinct ds)
                   (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (gd-await-pre w r ds mode k mine hg h)))
     (exact (gd-await-post (:next-id w) (:id r) ds (await-acc w r ds mode k mine) k1 h1))))
(override! GD 't6-inv '[inv-await-raw]
  '(a/theorem t6-gd [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
     (=> (= (g7 w) true) (= (gd w) true) (= (gd (:world (t6-await w st ds mode k fresh mine))) true))
     (intros hg7 h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t6-await ht refuse]) (exact h)
     (have p := (tok-facts w st r ht))
     (cases hg (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
     (simp only [t6-await ht hg refuse]) (exact h)
     (have hn (= (run-normal r) true)) (simp only [await-ok Bool.and_eq_true] at hg) (exact (And.left (And.right (And.left hg))))
     (simp only [t6-await ht hg accept]) (exact (gd-await-raw w r ds mode k mine hg7 (And.left p) (normal-alive r hn) h))))
(override! GD 'inv-host-await-raw '[inv-demand-reactive inv-insert-edge-checked inv-fire-edge]
  '(a/theorem gd-host-await-raw [w :- World, d :- Nat]
     (=> (= (g7 w) true) (= (gd w) true) (= (gd (host-await-raw w d)) true))
     (intros hg h)
     (have h1 (= (gd (host-await-dem w d)) true))
     (exact (gd-demand-reactive _ d (g7-insert-edge-checked w (host-wait-edge d) (Eq.refl true) hg) (gd-insert-edge-checked w (host-wait-edge d) h)))
     (cases hr (fast-ready (host-await-dem w d) d))
     (simp only [host-await-raw hr]) (exact h1)
     (simp only [host-await-raw hr]) (exact (gd-fire-edge _ _ (:next-id w) h1))))
(override! GD 't22-inv '[inv-host-await-raw]
  '(a/theorem t22-gd [w :- World, d :- Nat, fresh :- Nat]
     (=> (= (g7 w) true) (= (gd w) true) (= (gd (:world (t22-host-await w d fresh))) true))
     (intros hg7 h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (deb-exists w d)))
     (simp only [t22-host-await hg refuse]) (exact h)
     (simp only [t22-host-await hg accept]) (exact (gd-host-await-raw w d hg7 h))))
(override! GD 't8-full-inv '[inv-demand-reactive insert-edge-fresh-inv-sample inv-fire-edge]
  '(a/theorem t8-full-gd [w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
     (=> (= (g7 w) true) (= (gd w) true) (= (gd (:world (t8-full w d cb fresh))) true))
     (intros hg7 h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
     (simp only [t8-full hg refuse]) (exact h)
     (have he (= (edge-ok-in w (observe-edge w d cb)) true))
     (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
     (have h1 := (gd-demand-reactive _ d (g7-insert-edge-fresh w (observe-edge w d cb) (Eq.refl true) he hg7)
                   (insert-edge-fresh-gd w (observe-edge w d cb) he h)))
     (simp only [t8-full hg accept observe-raw])
     (cases hr (deb-ready (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) d))
     (simp only [hr]) (exact h1)
     (simp only [hr]) (exact (gd-fire-edge _ _ (:next-id w) h1))))

;; ---- raw0 / raw0g / raw: g7 (reactivation) and g10r (T12's cur-ok) threaded from the step's input
(def ^:private gd-calls
  '{(t6-inv w _ _ _ _ _ _ h) (t6-inv w _ _ _ _ _ _ hg7 h)
    (t22-inv w _ _ h) (t22-inv w _ _ hg7 h)
    (t8-full-inv w _ _ _ h) (t8-full-inv w _ _ _ hg7 h)
    (t12-inv w _ _ _ h) (t12-inv w _ _ _ hg10 h)})
(defn- gd-add-hyps [form calls]
  (let [[hd nm binders stmt & proof] form
        stmt2 (apply list '=> '(= (g7 w) true) '(= (g10r w) true) (rest stmt))
        proof2 (map (fn [t] (if (= t '(intro h)) '(intros hg7 hg10 h) t)) proof)]
    (subst-forms #(contains? calls %) calls (apply list hd nm binders stmt2 proof2))))
(patch! GD 'raw0-inv (fn [form] (gd-add-hyps (gd-patch form) gd-calls)))
(patch! GD 'raw0g-inv (fn [form] (gd-add-hyps (gd-patch form) '{(raw0-inv w it h) (raw0-inv w it hg7 hg10 h)})))
(patch! GD 'raw-inv (fn [form] (gd-add-hyps (gd-patch form) '{(raw0g-inv w it h) (raw0g-inv w it hg7 hg10 h)})))

;; ===========================================================================
;; Part E. The copy, Rule R, the step
;; ===========================================================================

(lcopy! GD 'raw-inv)
(lcopy! GD 'inv-normalize)

(a/theorem gd-rule-r-round [w :- World]
  (=> (= (gd w) true) (= (filter-safe (normalize w)) true) (= (gd (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (gd-filter-world _ (keep-fn (normalize w)) (gd-normalize w h) hf)))
(a/theorem gd-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (gd w0) true) (= (rr-safe fuel w0) true) (= (gd (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (gd-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (gd-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))
(a/theorem gd-rule-r [w :- World] (=> (= (gd w) true) (= (rule-r-safe w) true) (= (gd (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (gd-rr-loop (rr-fuel w) w h hs)))
(a/theorem step-gd [w :- World, it :- Item]
  (=> (= (g7 w) true) (= (g10r w) true) (= (gd w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (gd (:world (world-step w it))) true))
  (intros hg7 hg10 h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (gd-rule-r (:world (raw w it)) (raw-gd w it hg7 hg10 h) hs))))
(a/theorem gd-empty [] (= (gd empty-world) true) (rfl))

;; the context facts from p3i: g7 (in p3b's ri) and g10r (p3c)
(a/theorem p3i-ctx [w :- World] (=> (= (p3i w) true) (And (= (p3b w) true) (= (g10r w) true)))
  (intro h)
  (have ph := (And.left (p3i-parts w h)))
  (have pg := (p3g-parts w (And.left (p3h-parts w ph))))
  (have pf := (p3f-parts w (And.left pg)))
  (have pe := (p3e-parts w (And.left pf)))
  (have pd := (p3d-parts w (And.left pe)))
  (exact (p3c-parts w (And.left pd))))
(a/theorem p3i-g7 [w :- World] (=> (= (p3i w) true) (= (g7 w) true))
  (intro h)
  (have pb := (p3b-parts w (And.left (p3i-ctx w h))))
  (exact (And.left (ri-parts w (And.right (And.right (And.right (And.right pb))))))))

;; the combined bundle: p3j = p3i && gd (no honest hypothesis)
(a/defn p3j [w :- World] Bool (Bool.and (p3i w) (gd w)))
(a/theorem p3j-parts [w :- World] (=> (= (p3j w) true) (And (= (p3i w) true) (= (gd w) true)))
  (intro h) (simp only [p3j Bool.and_eq_true] at h) (exact h))
(a/theorem p3j-empty [] (= (p3j empty-world) true) (rfl))
(a/theorem step-p3j [w :- World, it :- Item] (=> (= (p3j w) true) (= (p3j (:world (world-step w it))) true))
  (intro h)
  (have p := (p3j-parts w h))
  (have c := (p3i-ctx w (And.left p)))
  (have a1 := (step-p3i w it (And.left p)))
  (have a2 := (step-gd w it (p3i-g7 w (And.left p)) (And.right c) (And.right p) (step-rule-r-safe w it (And.left c))))
  (simp only [p3j a1 a2 Bool.and_self]))

;; Theorem (the aux facts of the h-mark plan, PLAN z59 (0)): after every step from a p3j world,
;; every computation has done-epoch <= epoch, 0 < epoch, and has no alive run at its epoch once
;; its result is set (done-epoch = epoch)
(a/defn gd-fact [w :- World, c :- CompRow] Bool
  (Bool.and (Nat.ble (:done-epoch c) (:epoch c))
            (Bool.or (Bool.not (Nat.beq (:done-epoch c) (:epoch c))) (tbl-all (gd-noal (:id c) (:epoch c)) (:runs w)))))
(a/theorem gd-facts [w :- World] (=> (= (gd w) true) (= (tbl-all (gd-fact w) (:comps w)) true))
  (intro h)
  (have p := (gdk-parts _ _ _ (gd-rest-of w h)))
  (have q := (And.right p)) (rw [all-gdkeys] at q)
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) q))
  (intros c hc)
  (have pc := (gd-c-parts _ _ _ hc))
  (have dl := (And.left pc)) (simp only [gd-dle gdkey Bool.and_eq_true] at dl)
  (have cd := (And.right (And.right (And.right pc))))
  (cases hd (Nat.beq (:done-epoch c) (:epoch c)))
  (case [false] (simp only [gd-fact (And.left dl) hd Bool.not_false Bool.true_or Bool.and_self]))
  (case [true]
    (simp only [gd-cde gdkey hd Bool.not_true Bool.false_or] at cd)
    (simp only [gd-fact (And.left dl) hd Bool.not_true Bool.false_or Bool.true_and])
    (apply (tbl-all-mono RunRow _ _ _ (:runs w) cd))
    (intros q hq) (simp only [gd-ncur gdkey] at hq) (simp only [gd-noal]) (exact hq)))
(a/theorem step-gd-facts-total [w :- World, it :- Item]
  (=> (= (p3j w) true) (= (tbl-all (gd-fact (:world (world-step w it))) (:comps (:world (world-step w it)))) true))
  (intro h) (exact (gd-facts _ (And.right (p3j-parts _ (step-p3j w it h))))))

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
