(ns spindel.v2.idle
  "I7 (the idle shape of a computation) through the model's step `world-step`, kernel-checked
  (Init only). Bundle `g7` = inv-sample and:
    a7     an alive run's computation (if any) is not idle
    dm     a dep or marked edge's creditor computation (if any) is not idle (I7's edge part,
           P3's `dep-active`; marked: its pending count is exact, so an idle computation has
           pending 0)
    clean  an idle computation has no run and no adoption basis or baselines
    sn     a run that holds the slice in normal mode is alive (a track / an await is by an
           alive run, so its computation is not idle)
  Every composite inv-sample lemma is re-checked for the bundle by spindel.v2.lit's `lcopy!`;
  primitives: an edit that keeps the computation keys (id, idle, clean), the run keys (id, of,
  alive, slice and mode) and the edge keys (kind, creditor, marked) is a frame; overrides where
  a computation wakes or sleeps, a run is created or parked, a dep edge is inserted."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.rank :refer :all]
            [spindel.v2.casc :refer :all]
            [spindel.v2.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.lit :refer :all]))

;; ===========================================================================
;; Part A. The bundle
;; ===========================================================================

;; no computation row with id x is idle
(a/defn awake [cs :- (List CompRow), x :- Nat] Bool (tbl-all (not-idle-if-id x) cs))
(a/defn a7-one [cs :- (List CompRow), r :- RunRow] Bool (Bool.or (Bool.not (run-alive r)) (awake cs (:of r))))
(a/defn dm-one [cs :- (List CompRow), e :- EdgeRow] Bool
  (Bool.or (Bool.not (Bool.or (Nat.beq (:kind e) ek-dep) (:marked e))) (awake cs (:creditor e))))
(a/defn idle-clean [c :- CompRow] Bool
  (Bool.and (Nat.beq (:run c) 0) (Bool.and (created-empty (:adopt-basis c)) (bases-empty (:adopt-baselines c)))))
(a/defn clean-one [c :- CompRow] Bool (Bool.or (Bool.not (:idle c)) (idle-clean c)))
(a/defn sn-one [r :- RunRow] Bool
  (Bool.or (Bool.not (Bool.and (:slice r) (Nat.beq (:mode r) mode-normal))) (run-alive r)))
;; an observe edge's creditor is the host (0)
(a/defn obs-one [e :- EdgeRow] Bool (Bool.or (Bool.not (Nat.beq (:kind e) ek-observe)) (Nat.beq (:creditor e) 0)))

(a/defn g7k [cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)] Bool
  (Bool.and (tbl-all (a7-one cs) rs)
  (Bool.and (tbl-all (dm-one cs) es)
  (Bool.and (tbl-all clean-one cs) (Bool.and (tbl-all sn-one rs) (tbl-all obs-one es))))))
(a/defn g7-rest [w :- World] Bool (g7k (:comps w) (:runs w) (:edges w)))
(a/defn g7 [w :- World] Bool (Bool.and (inv-sample w) (g7-rest w)))

(a/theorem g7-sample [w :- World] (=> (= (g7 w) true) (= (inv-sample w) true))
  (intro h) (simp only [g7 Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem g7-rest-of [w :- World] (=> (= (g7 w) true) (= (g7-rest w) true))
  (intro h) (simp only [g7 Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem g7-intro [w :- World] (=> (= (inv-sample w) true) (= (g7-rest w) true) (= (g7 w) true))
  (intros h1 h2) (simp only [g7 h1 h2 Bool.and_self]))
(a/theorem g7-parts [w :- World]
  (=> (= (g7 w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (g7-sample w h))))
(a/theorem g7k-parts [cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (g7k cs rs es) true)
      (And (= (tbl-all (a7-one cs) rs) true)
      (And (= (tbl-all (dm-one cs) es) true)
      (And (= (tbl-all clean-one cs) true) (And (= (tbl-all sn-one rs) true) (= (tbl-all obs-one es) true))))))
  (intro h) (simp only [g7k Bool.and_eq_true] at h) (exact h))
(a/theorem g7k-intro [cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (tbl-all (a7-one cs) rs) true) (= (tbl-all (dm-one cs) es) true)
      (= (tbl-all clean-one cs) true) (= (tbl-all sn-one rs) true) (= (tbl-all obs-one es) true) (= (g7k cs rs es) true))
  (intros h1 h2 h3 h4 h5) (simp only [g7k h1 h2 h3 h4 h5 Bool.and_self]))
;; the last three parts
(a/defn p345 [cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)] Prop
  (And (= (tbl-all clean-one cs) true) (And (= (tbl-all sn-one rs) true) (= (tbl-all obs-one es) true))))

;; ---- awake under computation edits

;; a computation edit that never makes a row idle that was not (pointwise)
(a/defn no-sleep [f :- (=> CompRow CompRow), c :- CompRow] Bool (Bool.or (Bool.not (:idle (f c))) (:idle c)))

(a/theorem awake-upd [x :- Nat, f :- (=> CompRow CompRow),
                      hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                      hs :- (forall [c :- CompRow] (= (no-sleep f c) true)), cs :- (List CompRow), y :- Nat]
  (=> (= (awake cs y) true) (= (awake (tbl-upd comp-id x f cs) y) true))
  (intro h) (simp only [awake] at h) (simp only [awake])
  (apply (tbl-all-upd CompRow comp-id x f (not-idle-if-id y) (not-idle-if-id y) _ _ cs h))
  (intros c hc hx)
  (have e (= (:id (f c)) (:id c))) (exact (hid c))
  (have s := (hs c))
  (cases hi (:idle (f c)))
  (case [false] (simp only [not-idle-if-id hi Bool.not_false Bool.or_true]))
  (case [true]
    (simp only [no-sleep hi Bool.not_true Bool.false_or] at s)
    (simp only [not-idle-if-id s Bool.not_true Bool.or_false] at hc)
    (simp only [not-idle-if-id e hi hc Bool.not_true Bool.or_false]))
  (intros c hc hx) (exact hc))

(a/theorem awake-del [x :- Nat, cs :- (List CompRow), y :- Nat]
  (=> (= (awake cs y) true) (= (awake (tbl-del comp-id x cs) y) true))
  (intro h) (simp only [awake] at h) (simp only [awake])
  (exact (tbl-all-del CompRow comp-id x (not-idle-if-id y) (not-idle-if-id y) (fn [c :- CompRow, hc :- (= (not-idle-if-id y c) true), hx :- (= (Nat.beq (comp-id c) x) false)] hc) cs h)))

(a/theorem awake-keep [K :- (=> Nat Bool), cs :- (List CompRow), y :- Nat]
  (=> (= (awake cs y) true) (= (awake (tbl-keep K comp-id cs) y) true))
  (intro h) (simp only [awake] at h) (simp only [awake])
  (exact (tbl-all-keep-same CompRow K comp-id (not-idle-if-id y) cs h)))

(a/theorem awake-filter [q :- (=> CompRow Bool), cs :- (List CompRow), y :- Nat]
  (=> (= (awake cs y) true) (= (awake (tbl-filter q cs) y) true))
  (intro h) (simp only [awake] at h) (simp only [awake])
  (exact (tbl-all-filter CompRow (not-idle-if-id y) q cs h)))

(a/theorem awake-ins [r :- CompRow, cs :- (List CompRow), y :- Nat]
  (=> (= (:idle r) false) (= (awake cs y) true) (= (awake (tbl-ins r cs) y) true))
  (intros hr h) (simp only [awake] at h) (simp only [awake tbl-ins tbl-all not-idle-if-id hr h Bool.not_false Bool.or_true Bool.and_self]))

(a/theorem awake-absent [cs :- (List CompRow), y :- Nat]
  (=> (= (tbl-has comp-id y cs) false) (= (awake cs y) true))
  (induction cs)
  (case [nil] (intro h) (simp [awake tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (cases e (Nat.beq (comp-id hd) y))
    (case [true] (simp [tbl-has e] at h))
    (case [false]
      (simp only [tbl-has e] at h)
      (have h1 := (ih h))
      (simp only [awake] at h1)
      (have e2 (= (Nat.beq (:id hd) y) false)) (exact e)
      (simp only [awake tbl-all not-idle-if-id e2 h1 Bool.not_false Bool.true_or Bool.and_self]))))

;; ---- the parts under a computation edit that never makes a row idle and keeps the
;; idle rows clean

(a/defn keeps-clean [f :- (=> CompRow CompRow), c :- CompRow] Bool (Bool.or (Bool.not (clean-one c)) (clean-one (f c))))

(a/theorem g7k-comp-upd [x :- Nat, f :- (=> CompRow CompRow),
                         hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                         hs :- (forall [c :- CompRow] (= (no-sleep f c) true)),
                         hc :- (forall [c :- CompRow] (= (keeps-clean f c) true)),
                         cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (g7k cs rs es) true) (= (g7k (tbl-upd comp-id x f cs) rs es) true))
  (intro h)
  (have p := (g7k-parts cs rs es h))
  (have h1 (= (tbl-all (a7-one (tbl-upd comp-id x f cs)) rs) true))
  (apply (tbl-all-mono RunRow (a7-one cs) (a7-one (tbl-upd comp-id x f cs)) _ rs (And.left p)))
  (intros r hr)
  (cases ha (run-alive r))
  (case [false] (simp only [a7-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [a7-one ha Bool.not_true Bool.false_or] at hr)
    (simp only [a7-one ha Bool.not_true Bool.false_or])
    (exact (awake-upd x f hid hs cs (:of r) hr)))
  (have h2 (= (tbl-all (dm-one (tbl-upd comp-id x f cs)) es) true))
  (apply (tbl-all-mono EdgeRow (dm-one cs) (dm-one (tbl-upd comp-id x f cs)) _ es (And.left (And.right p))))
  (intros e he)
  (cases hd (Bool.or (Nat.beq (:kind e) ek-dep) (:marked e)))
  (case [false] (simp only [dm-one hd Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dm-one hd Bool.not_true Bool.false_or] at he)
    (simp only [dm-one hd Bool.not_true Bool.false_or])
    (exact (awake-upd x f hid hs cs (:creditor e) he)))
  (have h3 (= (tbl-all clean-one (tbl-upd comp-id x f cs)) true))
  (apply (tbl-all-upd CompRow comp-id x f clean-one clean-one _ _ cs (And.left (And.right (And.right p)))))
  (intros c h4 hx)
  (have k := (hc c)) (simp only [keeps-clean h4 Bool.not_true Bool.false_or] at k) (exact k)
  (intros c h4 hx) (exact h4)
  (exact (g7k-intro _ _ _ h1 h2 h3 (And.left (And.right (And.right (And.right p)))) (And.right (And.right (And.right (And.right p)))))))

;; ---- the parts under run, edge and row-set edits

;; a run edit that never revives a run nor changes the entity of an alive one (pointwise)
(a/defn run-down [f :- (=> RunRow RunRow), r :- RunRow] Bool
  (Bool.or (Bool.not (run-alive (f r))) (Bool.and (run-alive r) (Nat.beq (:of (f r)) (:of r)))))
(a/defn sn-keep [f :- (=> RunRow RunRow), r :- RunRow] Bool (Bool.or (Bool.not (sn-one r)) (sn-one (f r))))

(a/theorem g7k-run-upd [x :- Nat, f :- (=> RunRow RunRow),
                        hd :- (forall [r :- RunRow] (= (run-down f r) true)),
                        hs :- (forall [r :- RunRow] (= (sn-keep f r) true)),
                        cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (g7k cs rs es) true) (= (g7k cs (tbl-upd run-id x f rs) es) true))
  (intro h)
  (have p := (g7k-parts cs rs es h))
  (have h1 (= (tbl-all (a7-one cs) (tbl-upd run-id x f rs)) true))
  (apply (tbl-all-upd RunRow run-id x f (a7-one cs) (a7-one cs) _ _ rs (And.left p)))
  (intros r hr hx)
  (have d := (hd r))
  (cases ha (run-alive (f r)))
  (case [false] (simp only [a7-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [run-down ha Bool.not_true Bool.false_or Bool.and_eq_true] at d)
    (have eo (= (:of (f r)) (:of r))) (exact (Nat.eq_of_beq_eq_true (And.right d)))
    (simp only [a7-one (And.left d) Bool.not_true Bool.false_or] at hr)
    (simp only [a7-one ha eo hr Bool.not_true Bool.false_or]))
  (intros r hr hx) (exact hr)
  (have h4 (= (tbl-all sn-one (tbl-upd run-id x f rs)) true))
  (apply (tbl-all-upd RunRow run-id x f sn-one sn-one _ _ rs (And.left (And.right (And.right (And.right p))))))
  (intros r hr hx)
  (have k := (hs r)) (simp only [sn-keep hr Bool.not_true Bool.false_or] at k) (exact k)
  (intros r hr hx) (exact hr)
  (exact (g7k-intro _ _ _ h1 (And.left (And.right p)) (And.left (And.right (And.right p))) h4 (And.right (And.right (And.right (And.right p)))))))

(a/theorem g7k-run-sub [cs :- (List CompRow), rs :- (List RunRow), rs2 :- (List RunRow), es :- (List EdgeRow),
                        hs :- (forall [P :- (=> RunRow Bool)] (=> (= (tbl-all P rs) true) (= (tbl-all P rs2) true)))]
  (=> (= (g7k cs rs es) true) (= (g7k cs rs2 es) true))
  (intro h)
  (have p := (g7k-parts cs rs es h))
  (exact (g7k-intro _ _ _ (hs (a7-one cs) (And.left p)) (And.left (And.right p)) (And.left (And.right (And.right p)))
           (hs sn-one (And.left (And.right (And.right (And.right p))))) (And.right (And.right (And.right (And.right p)))))))

(a/theorem g7k-edge-sub [cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow), es2 :- (List EdgeRow),
                         hs :- (forall [P :- (=> EdgeRow Bool)] (=> (= (tbl-all P es) true) (= (tbl-all P es2) true)))]
  (=> (= (g7k cs rs es) true) (= (g7k cs rs es2) true))
  (intro h)
  (have p := (g7k-parts cs rs es h))
  (exact (g7k-intro _ _ _ (And.left p) (hs (dm-one cs) (And.left (And.right p))) (And.left (And.right (And.right p)))
           (And.left (And.right (And.right (And.right p)))) (hs obs-one (And.right (And.right (And.right (And.right p))))))))

;; fewer computation rows (a subset in the sense of every awake fact and every clean row)
(a/theorem g7k-comp-sub [cs :- (List CompRow), cs2 :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow),
                         ha :- (forall [y :- Nat] (=> (= (awake cs y) true) (= (awake cs2 y) true))),
                         hc :- (=> (= (tbl-all clean-one cs) true) (= (tbl-all clean-one cs2) true))]
  (=> (= (g7k cs rs es) true) (= (g7k cs2 rs es) true))
  (intro h)
  (have p := (g7k-parts cs rs es h))
  (have h1 (= (tbl-all (a7-one cs2) rs) true))
  (apply (tbl-all-mono RunRow (a7-one cs) (a7-one cs2) _ rs (And.left p)))
  (intros r hr)
  (cases hl (run-alive r))
  (case [false] (simp only [a7-one hl Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [a7-one hl Bool.not_true Bool.false_or] at hr)
    (simp only [a7-one hl Bool.not_true Bool.false_or])
    (exact (ha (:of r) hr)))
  (have h2 (= (tbl-all (dm-one cs2) es) true))
  (apply (tbl-all-mono EdgeRow (dm-one cs) (dm-one cs2) _ es (And.left (And.right p))))
  (intros e he)
  (cases hd (Bool.or (Nat.beq (:kind e) ek-dep) (:marked e)))
  (case [false] (simp only [dm-one hd Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dm-one hd Bool.not_true Bool.false_or] at he)
    (simp only [dm-one hd Bool.not_true Bool.false_or])
    (exact (ha (:creditor e) he)))
  (exact (g7k-intro _ _ _ h1 h2 (hc (And.left (And.right (And.right p)))) (And.left (And.right (And.right (And.right p))))
           (And.right (And.right (And.right (And.right p)))))))

;; an edge edit keeping kind, creditor and marked
(a/theorem g7k-edge-upd [x :- Nat, f :- (=> EdgeRow EdgeRow),
                         hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                         hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                         hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e))),
                         cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (g7k cs rs es) true) (= (g7k cs rs (tbl-upd edge-id x f es)) true))
  (intro h)
  (have p := (g7k-parts cs rs es h))
  (have h2 (= (tbl-all (dm-one cs) (tbl-upd edge-id x f es)) true))
  (apply (tbl-all-upd EdgeRow edge-id x f (dm-one cs) (dm-one cs) _ _ es (And.left (And.right p))))
  (intros e he hx) (simp only [dm-one (hk e) (hc e) (hm e)]) (exact he)
  (intros e he hx) (exact he)
  (have h5 (= (tbl-all obs-one (tbl-upd edge-id x f es)) true))
  (apply (tbl-all-upd EdgeRow edge-id x f obs-one obs-one _ _ es (And.right (And.right (And.right (And.right p))))))
  (intros e he hx) (simp only [obs-one (hk e) (hc e)]) (exact he)
  (intros e he hx) (exact he)
  (exact (g7k-intro _ _ _ (And.left p) h2 (And.left (And.right (And.right p))) (And.left (And.right (And.right (And.right p)))) h5)))

;; ---- key forms (frames provable by rfl)

(a/structure CK7 [] (id Nat) (idle Bool) (clean Bool))
(a/defn ck7 [c :- CompRow] CK7 (CK7.mk (:id c) (:idle c) (idle-clean c)))
(a/structure RK7 [] (id Nat) (of Nat) (alive Bool) (slice Bool) (mode Nat))
(a/defn rk7 [r :- RunRow] RK7 (RK7.mk (:id r) (:of r) (run-alive r) (:slice r) (:mode r)))

(a/theorem ck7-no-sleep [f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (ck7 (f c)) (ck7 c))), c :- CompRow]
  (= (no-sleep f c) true)
  (have e (= (:idle (f c)) (:idle c))) (exact (congrArg (fn [k :- CK7] (:idle k)) (hk c)))
  (cases hi (:idle c))
  (all_goals (simp only [no-sleep e hi Bool.not_true Bool.not_false Bool.or_true Bool.true_or])))

(a/theorem ck7-keeps-clean [f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (ck7 (f c)) (ck7 c))), c :- CompRow]
  (= (keeps-clean f c) true)
  (have e1 (= (:idle (f c)) (:idle c))) (exact (congrArg (fn [k :- CK7] (:idle k)) (hk c)))
  (have e2 (= (idle-clean (f c)) (idle-clean c))) (exact (congrArg (fn [k :- CK7] (:clean k)) (hk c)))
  (have e3 (= (clean-one (f c)) (clean-one c))) (simp only [clean-one e1 e2])
  (cases hc (clean-one c))
  (all_goals (simp only [keeps-clean e3 hc Bool.not_true Bool.not_false Bool.or_true Bool.true_or])))

(a/theorem rk7-down [f :- (=> RunRow RunRow), hk :- (forall [r :- RunRow] (= (rk7 (f r)) (rk7 r))), r :- RunRow]
  (= (run-down f r) true)
  (have e1 (= (run-alive (f r)) (run-alive r))) (exact (congrArg (fn [k :- RK7] (:alive k)) (hk r)))
  (have e2 (= (:of (f r)) (:of r))) (exact (congrArg (fn [k :- RK7] (:of k)) (hk r)))
  (cases ha (run-alive r))
  (all_goals (simp only [run-down e1 e2 ha Nat.beq_refl Bool.not_true Bool.not_false Bool.true_or Bool.false_or Bool.and_self])))

(a/theorem rk7-sn [f :- (=> RunRow RunRow), hk :- (forall [r :- RunRow] (= (rk7 (f r)) (rk7 r))), r :- RunRow]
  (= (sn-keep f r) true)
  (have e1 (= (run-alive (f r)) (run-alive r))) (exact (congrArg (fn [k :- RK7] (:alive k)) (hk r)))
  (have e2 (= (:slice (f r)) (:slice r))) (exact (congrArg (fn [k :- RK7] (:slice k)) (hk r)))
  (have e3 (= (:mode (f r)) (:mode r))) (exact (congrArg (fn [k :- RK7] (:mode k)) (hk r)))
  (have e4 (= (sn-one (f r)) (sn-one r))) (simp only [sn-one e1 e2 e3])
  (cases hs (sn-one r))
  (all_goals (simp only [sn-keep e4 hs Bool.not_true Bool.not_false Bool.or_true Bool.true_or])))

;; ---- primitives: computation and run edits

(a/theorem g7-comp-upd-m [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                          hs :- (forall [c :- CompRow] (= (no-sleep f c) true)),
                          hc :- (forall [c :- CompRow] (= (keeps-clean f c) true))]
  (=> (= (g7 w) true) (= (g7 (comp-upd w x f)) true))
  (intro h)
  (exact (g7-intro _ (inv-comp-upd w x f hid hp (g7-sample w h))
           (g7k-comp-upd x f hid hs hc (:comps w) (:runs w) (:edges w) (g7-rest-of w h)))))

(a/theorem g7-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hk :- (forall [c :- CompRow] (= (ck7 (f c)) (ck7 c)))]
  (=> (= (g7 w) true) (= (g7 (comp-upd w x f)) true))
  (exact (g7-comp-upd-m w x f hid hp (ck7-no-sleep f hk) (ck7-keeps-clean f hk))))

(a/theorem g7-run-upd-m [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                         hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         hd :- (forall [r :- RunRow] (= (run-down f r) true)),
                         hs :- (forall [r :- RunRow] (= (sn-keep f r) true))]
  (=> (= (g7 w) true) (= (g7 (run-upd w x f)) true))
  (intro h)
  (exact (g7-intro _ (inv-run-upd w x f hf (g7-sample w h))
           (g7k-run-upd x f hd hs (:comps w) (:runs w) (:edges w) (g7-rest-of w h)))))

(a/theorem g7-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (rk7 (f r)) (rk7 r)))]
  (=> (= (g7 w) true) (= (g7 (run-upd w x f)) true))
  (exact (g7-run-upd-m w x f hf (rk7-down f hk) (rk7-sn f hk))))

;; ---- primitives: edges and row sets

(a/theorem awake-resync [es :- (List EdgeRow), cs :- (List CompRow), y :- Nat]
  (= (awake (comps-resync es cs) y) (awake cs y))
  (induction cs)
  (case [nil] (simp only [comps-resync]))
  (case [cons hd t ih]
    (simp only [awake] at ih)
    (simp only [awake comps-resync tbl-all ih not-idle-if-id comp-resync comp-set-pending])))

(a/theorem clean-resync [es :- (List EdgeRow), cs :- (List CompRow)]
  (= (tbl-all clean-one (comps-resync es cs)) (tbl-all clean-one cs))
  (induction cs)
  (case [nil] (simp only [comps-resync]))
  (case [cons hd t ih]
    (simp only [comps-resync tbl-all ih clean-one idle-clean comp-resync comp-set-pending])))

(a/theorem g7k-edges-filter [q :- (=> EdgeRow Bool), cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (g7k cs rs es) true) (= (g7k cs rs (tbl-filter q es)) true))
  (intro h)
  (exact (g7k-edge-sub cs rs es _ (fn [P :- (=> EdgeRow Bool), hp :- (= (tbl-all P es) true)] (tbl-all-filter EdgeRow P q es hp)) h)))

(a/theorem g7k-edges-del [x :- Nat, cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (g7k cs rs es) true) (= (g7k cs rs (tbl-del edge-id x es)) true))
  (intro h)
  (exact (g7k-edge-sub cs rs es _
           (fn [P :- (=> EdgeRow Bool), hp :- (= (tbl-all P es) true)]
             (tbl-all-del EdgeRow edge-id x P P (fn [e :- EdgeRow, he :- (= (P e) true), hx :- (= (Nat.beq (edge-id e) x) false)] he) es hp))
           h)))

(a/theorem g7k-runs-del [x :- Nat, cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (g7k cs rs es) true) (= (g7k cs (tbl-del run-id x rs) es) true))
  (intro h)
  (exact (g7k-run-sub cs rs _ es
           (fn [P :- (=> RunRow Bool), hp :- (= (tbl-all P rs) true)]
             (tbl-all-del RunRow run-id x P P (fn [r :- RunRow, hr :- (= (P r) true), hx :- (= (Nat.beq (run-id r) x) false)] hr) rs hp))
           h)))

(a/theorem g7k-comps-del [x :- Nat, cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (g7k cs rs es) true) (= (g7k (tbl-del comp-id x cs) rs es) true))
  (intro h)
  (exact (g7k-comp-sub cs _ rs es (fn [y :- Nat, hy :- (= (awake cs y) true)] (awake-del x cs y hy))
           (fn [hc :- (= (tbl-all clean-one cs) true)]
             (tbl-all-del CompRow comp-id x clean-one clean-one (fn [c :- CompRow, h1 :- (= (clean-one c) true), hx :- (= (Nat.beq (comp-id c) x) false)] h1) cs hc))
           h)))

(a/theorem g7k-resync [es2 :- (List EdgeRow), cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (g7k cs rs es) true) (= (g7k (comps-resync es2 cs) rs es) true))
  (intro h)
  (exact (g7k-comp-sub cs _ rs es (fn [y :- Nat, hy :- (= (awake cs y) true)] (Eq.trans (awake-resync es2 cs y) hy))
           (fn [hc :- (= (tbl-all clean-one cs) true)] (Eq.trans (clean-resync es2 cs) hc))
           h)))

(a/theorem g7k-keep [K :- (=> Nat Bool), cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (g7k cs rs es) true) (= (g7k (tbl-keep K comp-id cs) (tbl-keep K run-id rs) (tbl-keep K edge-id es)) true))
  (intro h)
  (have h1 := (g7k-comp-sub cs (tbl-keep K comp-id cs) rs es (fn [y :- Nat, hy :- (= (awake cs y) true)] (awake-keep K cs y hy))
                (fn [hc :- (= (tbl-all clean-one cs) true)] (tbl-all-keep-same CompRow K comp-id clean-one cs hc)) h))
  (have h2 := (g7k-run-sub _ rs (tbl-keep K run-id rs) es
                (fn [P :- (=> RunRow Bool), hp :- (= (tbl-all P rs) true)] (tbl-all-keep-same RunRow K run-id P rs hp)) h1))
  (exact (g7k-edge-sub _ _ es (tbl-keep K edge-id es)
           (fn [P :- (=> EdgeRow Bool), hp :- (= (tbl-all P es) true)] (tbl-all-keep-same EdgeRow K edge-id P es hp)) h2)))

(a/theorem g7-rest-edge-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                             hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                             hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                             hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e)))]
  (=> (= (g7-rest w) true) (= (g7-rest (edge-upd w x f)) true))
  (intro h) (exact (g7k-edge-upd x f hk hc hm (:comps w) (:runs w) (:edges w) h)))

(a/theorem g7-rest-drop-edges [w :- World, p :- (=> EdgeRow Bool)]
  (=> (= (g7-rest w) true) (= (g7-rest (drop-edges w p)) true))
  (intro h)
  (exact (g7k-resync _ (:comps w) (:runs w) _ (g7k-edges-filter p (:comps w) (:runs w) (:edges w) h))))

(a/theorem g7-rest-drop-cred [w :- World, a :- Nat]
  (=> (= (g7-rest w) true) (= (g7-rest (drop-cred-edges w a)) true))
  (intro h)
  (exact (g7k-comp-upd a (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (comp-id c)))
           (ck7-no-sleep _ (fn [c :- CompRow] (Eq.refl (ck7 c)))) (ck7-keeps-clean _ (fn [c :- CompRow] (Eq.refl (ck7 c))))
           (:comps w) (:runs w) _ (g7k-edges-filter (cred-ne a) (:comps w) (:runs w) (:edges w) h))))

(a/theorem g7-rest-drop-act [w :- World, a :- Nat]
  (=> (= (g7-rest w) true) (= (g7-rest (drop-act w a)) true))
  (intro h) (exact (g7-rest-drop-cred w a h)))

(a/theorem g7-rest-run-del [w :- World, x :- Nat]
  (=> (= (g7-rest w) true) (= (g7-rest (run-del w x)) true))
  (intro h) (exact (g7k-runs-del x (:comps w) (:runs w) (:edges w) h)))

(a/theorem g7-rest-comp-del [w :- World, x :- Nat]
  (=> (= (g7-rest w) true) (= (g7-rest (comp-del w x)) true))
  (intro h) (exact (g7k-comps-del x (:comps w) (:runs w) (:edges w) h)))

(a/theorem g7-rest-filter-world [w :- World, K :- (=> Nat Bool)]
  (=> (= (g7-rest w) true) (= (g7-rest (filter-world K w)) true))
  (intro h) (exact (g7k-keep K (:comps w) (:runs w) (:edges w) h)))

(a/theorem g7-rest-remove-edge [w :- World, x :- Nat]
  (=> (= (g7-rest w) true) (= (g7-rest (remove-edge w x)) true))
  (intro h)
  (have h1 (= (g7-rest (edge-del w x)) true)) (exact (g7k-edges-del x (:comps w) (:runs w) (:edges w) h))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact h1))
    (case [true]
      (simp only [remove-edge hf hm])
      (exact (g7k-comp-upd (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c)))
               (ck7-no-sleep _ (fn [c :- CompRow] (Eq.refl (ck7 c)))) (ck7-keeps-clean _ (fn [c :- CompRow] (Eq.refl (ck7 c))))
               _ _ _ h1)))))

(a/theorem g7-rest-unmark-edge [w :- World, x :- Nat]
  (=> (= (g7-rest w) true) (= (g7-rest (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true]
      (simp only [unmark-edge hf hm])
      (have p := (g7k-parts _ _ _ h))
      (have h2 (= (tbl-all (dm-one (:comps w)) (tbl-upd edge-id x (edge-set-marked false) (:edges w))) true))
      (apply (tbl-all-upd EdgeRow edge-id x (edge-set-marked false) (dm-one (:comps w)) (dm-one (:comps w)) _ _ (:edges w) (And.left (And.right p))))
      (intros d hd hx)
      (cases hk (Nat.beq (:kind d) ek-dep))
      (case [true] (simp only [dm-one hk Bool.true_or Bool.not_true Bool.false_or] at hd)
                   (simp only [dm-one edge-set-marked hk hd Bool.true_or Bool.not_true Bool.false_or]))
      (case [false] (simp only [dm-one edge-set-marked hk Bool.false_or Bool.not_false Bool.true_or]))
      (intros d hd hx) (exact hd)
      (have h5 (= (tbl-all obs-one (tbl-upd edge-id x (edge-set-marked false) (:edges w))) true))
      (apply (tbl-all-upd EdgeRow edge-id x (edge-set-marked false) obs-one obs-one _ _ (:edges w) (And.right (And.right (And.right (And.right p))))))
      (intros d hd hx) (simp only [obs-one edge-set-marked]) (exact hd)
      (intros d hd hx) (exact hd)
      (have h6 := (g7k-intro (:comps w) (:runs w) _ (And.left p) h2 (And.left (And.right (And.right p)))
                    (And.left (And.right (And.right (And.right p)))) h5))
      (exact (g7k-comp-upd (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c)))
               (ck7-no-sleep _ (fn [c :- CompRow] (Eq.refl (ck7 c)))) (ck7-keeps-clean _ (fn [c :- CompRow] (Eq.refl (ck7 c))))
               _ _ _ h6)))))

;; ---- the creditor of every edge is awake (dep: dm; observe/host wait: 0, no computation;
;; otherwise an activation, no computation by unique ids)

(a/theorem comp-has-zero [w :- World] (=> (= (inv-sample w) true) (= (tbl-has comp-id 0 (:comps w)) false))
  (intro h)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (cases hc (tbl-has comp-id 0 (:comps w)))
  (case [false] (rfl))
  (case [true]
    (have z := (has-pos CompRow comp-id 0 (:next-id w) (:comps w) (And.left (And.right hb)) hc))
    (simp at z)))

(a/theorem act-not-comp [w :- World, y :- Nat]
  (=> (= (inv-sample w) true) (= (tbl-has act-id y (:acts w)) true) (= (tbl-has comp-id y (:comps w)) false))
  (intros h ha)
  (cases hc (tbl-has comp-id y (:comps w)))
  (case [false] (rfl))
  (case [true]
    (have u := (ids-unique-of w h))
    (simp only [all-ids] at u)
    (have u2 := (nat-nodup-app-right _ _ u))
    (have hm (= (nat-mem y (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hc)
    (have hm2 (= (nat-mem y (tbl-ids act-id (:acts w))) true)) (rw [nat-mem-ids]) (exact ha)
    (have d := (nodup-app-disj y _ _ u2 hm))
    (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
    (have d2 := (And.left (And.right (And.right (And.right (And.right d))))))
    (rw [hm2] at d2) (cases d2)))

(a/defn cred-awake [cs :- (List CompRow), e :- EdgeRow] Bool (awake cs (:creditor e)))

(a/theorem cred-awake-mem [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (g7-rest w) true) (List.Mem e (:edges w)) (= (cred-awake (:comps w) e) true))
  (intros h hr hm)
  (have p := (g7k-parts _ _ _ hr))
  (have hd := (tbl-all-mem EdgeRow (dm-one (:comps w)) e (:edges w) (And.left (And.right p)) hm))
  (have ho := (tbl-all-mem EdgeRow obs-one e (:edges w) (And.right (And.right (And.right (And.right p)))) hm))
  (have hok := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                 (And.left (And.right (inv-parts w h))) hm))
  (simp only [edge-ok Bool.and_eq_true] at hok)
  (have hco := (And.left hok))
  (simp only [cred-awake])
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [true] (simp only [dm-one hk Bool.true_or Bool.not_true Bool.false_or] at hd) (exact hd))
  (case [false]
    (cases hh (host-cred e))
    (case [true]
      (have z (= (:creditor e) 0))
      (simp only [host-cred Bool.or_eq_true Bool.and_eq_true] at hh)
      (cases hh)
      (case [inl ho2] (simp only [obs-one ho2 Bool.not_true Bool.false_or] at ho) (exact (Nat.eq_of_beq_eq_true ho)))
      (case [inr hw] (exact (Nat.eq_of_beq_eq_true (And.right hw))))
      (rw [z]) (exact (awake-absent (:comps w) 0 (comp-has-zero w h))))
    (case [false]
      (simp only [cred-ok hk hh] at hco)
      (exact (awake-absent (:comps w) (:creditor e) (act-not-comp w (:creditor e) h hco))))))

(a/theorem both-of [A :- Type, p :- (=> A Bool), q :- (=> A Bool), a :- A]
  (=> (= (p a) true) (= (q a) true) (= (both p q a) true))
  (intros h1 h2) (simp only [both h1 h2 Bool.and_self]))

(a/theorem g7-mark-edge-o [w :- World, x :- Nat]
  (=> (= (g7 w) true) (= (g7 (mark-edge w x)) true))
  (intro h)
  (have hs := (g7-sample w h))
  (have hr := (g7-rest-of w h))
  (have p := (g7k-parts _ _ _ hr))
  (have hca (= (tbl-all (cred-awake (:comps w)) (:edges w)) true))
  (exact (all-of-mem EdgeRow (cred-awake (:comps w)) (:edges w) (fn [e :- EdgeRow, hm :- (List.Mem e (:edges w))] (cred-awake-mem w e hs hr hm))))
  (have hr2 (= (g7-rest (mark-edge w x)) true))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact hr))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact hr))
    (case [false]
      (simp only [mark-edge hf hm])
      (have hb := (tbl-all-mono2 EdgeRow (dm-one (:comps w)) (cred-awake (:comps w)) (both (dm-one (:comps w)) (cred-awake (:comps w)))
                    (fn [d :- EdgeRow, h1 :- (= (dm-one (:comps w) d) true), h2 :- (= (cred-awake (:comps w) d) true)]
                      (both-of EdgeRow (dm-one (:comps w)) (cred-awake (:comps w)) d h1 h2))
                    (:edges w) (And.left (And.right p)) hca))
      (have h2 (= (tbl-all (dm-one (:comps w)) (tbl-upd edge-id x (edge-set-marked true) (:edges w))) true))
      (apply (tbl-all-upd EdgeRow edge-id x (edge-set-marked true) (both (dm-one (:comps w)) (cred-awake (:comps w))) (dm-one (:comps w)) _ _ (:edges w) hb))
      (intros d hd hx)
      (have ca := (both-right EdgeRow (dm-one (:comps w)) (cred-awake (:comps w)) d hd))
      (simp only [cred-awake] at ca)
      (simp only [dm-one edge-set-marked ca Bool.or_true])
      (intros d hd hx) (exact (both-left EdgeRow (dm-one (:comps w)) (cred-awake (:comps w)) d hd))
      (have h5 (= (tbl-all obs-one (tbl-upd edge-id x (edge-set-marked true) (:edges w))) true))
      (apply (tbl-all-upd EdgeRow edge-id x (edge-set-marked true) obs-one obs-one _ _ (:edges w) (And.right (And.right (And.right (And.right p))))))
      (intros d hd hx) (simp only [obs-one edge-set-marked]) (exact hd)
      (intros d hd hx) (exact hd)
      (have h6 := (g7k-intro (:comps w) (:runs w) _ (And.left p) h2 (And.left (And.right (And.right p)))
                    (And.left (And.right (And.right (And.right p)))) h5))
      (exact (g7k-comp-upd (:creditor e) comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c)))
               (ck7-no-sleep _ (fn [c :- CompRow] (Eq.refl (ck7 c)))) (ck7-keeps-clean _ (fn [c :- CompRow] (Eq.refl (ck7 c))))
               _ _ _ h6))))
  (exact (g7-intro _ (mark-edge-inv-sample w x hs) hr2)))

(a/theorem all-cons [A :- Type, P :- (=> A Bool), x :- A, xs :- (List A)]
  (=> (= (P x) true) (= (tbl-all P xs) true) (= (tbl-all P (List.cons A x xs)) true))
  (intros h1 h2) (simp only [tbl-all h1 h2 Bool.and_self]))

;; ---- insertions: a new edge (a dep edge needs an awake creditor, an observe edge the host
;; as creditor), a new computation (not idle)

(a/defn edge-new-ok [cs :- (List CompRow), e :- EdgeRow] Bool
  (Bool.and (Bool.or (Bool.not (Nat.beq (:kind e) ek-dep)) (awake cs (:creditor e))) (obs-one e)))

(a/theorem g7-insert-edge-fresh [w :- World, e :- EdgeRow, hn :- (= (edge-new-ok (:comps w) e) true)]
  (=> (= (edge-ok-in w e) true) (= (g7 w) true) (= (g7 (insert-edge-fresh w e)) true))
  (intros he h)
  (have p := (g7k-parts _ _ _ (g7-rest-of w h)))
  (simp only [edge-new-ok Bool.and_eq_true] at hn)
  (have d1 (= (dm-one (:comps w) (edge-set-id (:next-id w) (edge-set-marked false e))) true))
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dm-one edge-set-id edge-set-marked hk Bool.or_false Bool.not_false Bool.true_or]))
  (case [true]
    (have aw := (And.left hn)) (simp only [hk Bool.not_true Bool.false_or] at aw)
    (simp only [dm-one edge-set-id edge-set-marked aw Bool.or_true]))
  (have o1 (= (obs-one (edge-set-id (:next-id w) (edge-set-marked false e))) true))
  (simp only [obs-one edge-set-id edge-set-marked]) (exact (And.right hn))
  (have hr (= (g7-rest (insert-edge-fresh w e)) true))
  (simp only [g7-rest insert-edge-fresh bump insert-edge edge-ins set-next-id set-edges tbl-ins])
  (exact (g7k-intro _ _ _ (And.left p) (all-cons EdgeRow _ _ _ d1 (And.left (And.right p))) (And.left (And.right (And.right p)))
           (And.left (And.right (And.right (And.right p)))) (all-cons EdgeRow _ _ _ o1 (And.right (And.right (And.right (And.right p)))))))
  (exact (g7-intro _ (insert-edge-fresh-inv-sample w e he (g7-sample w h)) hr)))

(a/theorem g7-comp-ins-fresh [w :- World, r :- CompRow, hni :- (= (:idle r) false)]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (g7 w) true) (= (g7 (bump (comp-ins w r))) true))
  (intros h1 h2 h)
  (have hc (= (clean-one r) true)) (simp only [clean-one hni Bool.not_false Bool.true_or])
  (have hr (= (g7-rest (bump (comp-ins w r))) true))
  (simp only [g7-rest bump comp-ins set-next-id set-comps])
  (exact (g7k-comp-sub (:comps w) (tbl-ins r (:comps w)) (:runs w) (:edges w)
           (fn [y :- Nat, hy :- (= (awake (:comps w) y) true)] (awake-ins r (:comps w) y hni hy))
           (fn [h3 :- (= (tbl-all clean-one (:comps w)) true)] (all-cons CompRow clean-one r (:comps w) hc h3))
           (g7-rest-of w h)))
  (exact (g7-intro _ (inv-comp-ins-fresh w r h1 h2 (g7-sample w h)) hr)))

;; ===========================================================================
;; Part B. The bundle copy
;; ===========================================================================

(def G7 (mk-bundle 'g7 [] "g7-"
          {'inv-comp-upd ['(fn [c :- CompRow] (Eq.refl (ck7 c))) 5]
           'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (rk7 r))) 4]
           'insert-edge-fresh-inv-sample ['(Eq.refl true) 2]
           'inv-comp-ins-fresh ['(Eq.refl false) 2]
           'inv-insert-edge-checked ['(Eq.refl true) 2]}))
(swap! (:renames G7) assoc 'inv-parts 'g7-parts 'inv-comp-upd 'g7-comp-upd 'inv-run-upd 'g7-run-upd
       'insert-edge-fresh-inv-sample 'g7-insert-edge-fresh 'inv-comp-ins-fresh 'g7-comp-ins-fresh
       'mark-edge-inv-sample 'g7-mark-edge-o)

(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del
            inv-set-pins inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-task-upd
            inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-act-ins-fresh inv-task-ins-fresh inv-bump]]
  (prim! G7 o nil))
(prim! G7 'inv-edge-upd '(g7-rest-edge-upd w x f hk hc hm R))
(prim! G7 'inv-drop-cred '(g7-rest-drop-cred w a R))
(prim! G7 'inv-drop-act '(g7-rest-drop-act w a R))
(prim! G7 'inv-drop-edges '(g7-rest-drop-edges w p R))
(prim! G7 'inv-comp-del-unref '(g7-rest-comp-del w x R))
(prim! G7 'inv-run-del '(g7-rest-run-del w x R))
(prim! G7 'inv-remove-edge '(g7-rest-remove-edge w x R))
(prim! G7 'unmark-edge-inv-sample '(g7-rest-unmark-edge w x R))
(prim! G7 'inv-filter-world '(g7-rest-filter-world w K R))

;; ---- row functions that change a key: the pointwise facts

(a/theorem ce-filter [q :- (=> Created Bool), xs :- (List Created)]
  (=> (= (created-empty xs) true) (= (created-empty (tbl-filter q xs)) true))
  (cases xs) (case [nil] (intro h) (simp only [tbl-filter created-empty])) (case [cons h t] (intro e) (simp [created-empty] at e)))
(a/theorem be-filter [q :- (=> AdoptBase Bool), xs :- (List AdoptBase)]
  (=> (= (bases-empty xs) true) (= (bases-empty (tbl-filter q xs)) true))
  (cases xs) (case [nil] (intro h) (simp only [tbl-filter bases-empty])) (case [cons h t] (intro e) (simp [bases-empty] at e)))

;; waking rows
(defmacro ^:private defwake [& specs]
  `(do ~@(for [[f params] (partition 2 specs)
               :let [app (concat [f] (map first (partition 3 params)))]]
           `(do (a/theorem ~(symbol (str f "-nsl")) [~@params ~'c :- ~'CompRow] (~'= (~'no-sleep ~app ~'c) true)
                  (~'simp [~'no-sleep ~f]))
                (a/theorem ~(symbol (str f "-kcl")) [~@params ~'c :- ~'CompRow] (~'= (~'keeps-clean ~app ~'c) true)
                  (~'simp [~'keeps-clean ~'clean-one ~f]))))))
(defwake comp-react-row [] comp-demand-row [] comp-start-row [rid :- Nat] comp-replace-row [inputs :- (List Nat), body :- Nat])

(a/theorem comp-consume-adopt-nsl [site :- Nat, x :- Nat, c :- CompRow] (= (no-sleep (comp-consume-adopt site x) c) true)
  (cases hi (:idle c)) (all_goals (simp only [no-sleep comp-consume-adopt hi Bool.not_true Bool.not_false Bool.or_true Bool.true_or])))
(a/theorem comp-consume-adopt-kcl [site :- Nat, x :- Nat, c :- CompRow] (= (keeps-clean (comp-consume-adopt site x) c) true)
  (cases hk (clean-one c))
  (case [false] (simp only [keeps-clean hk Bool.not_false Bool.true_or]))
  (case [true]
    (cases hi (:idle c))
    (case [false] (simp only [keeps-clean clean-one comp-consume-adopt hi Bool.not_false Bool.true_or Bool.or_true]))
    (case [true]
      (simp only [clean-one idle-clean hi Bool.not_true Bool.false_or Bool.and_eq_true] at hk)
      (simp only [keeps-clean clean-one idle-clean comp-consume-adopt hi Bool.not_true Bool.false_or (And.left hk) (And.left (And.right hk))
                  (be-filter (adopt-other site x) _ (And.right (And.right hk))) Bool.and_self Bool.or_true]))))

(a/theorem comp-rebasis-nsl [b :- Created, c :- CompRow] (= (no-sleep (comp-rebasis b) c) true)
  (cases hi (:idle c)) (all_goals (simp only [no-sleep comp-rebasis hi Bool.not_true Bool.not_false Bool.or_true Bool.true_or])))
(a/theorem comp-rebasis-kcl [b :- Created, c :- CompRow] (= (keeps-clean (comp-rebasis b) c) true)
  (cases hk (clean-one c))
  (case [false] (simp only [keeps-clean hk Bool.not_false Bool.true_or]))
  (case [true]
    (cases hi (:idle c))
    (case [false] (simp only [keeps-clean clean-one comp-rebasis hi Bool.not_false Bool.true_or Bool.or_true]))
    (case [true]
      (simp only [clean-one idle-clean hi Bool.not_true Bool.false_or Bool.and_eq_true] at hk)
      (simp only [keeps-clean clean-one idle-clean comp-rebasis hi Bool.not_true Bool.false_or (And.left hk) (And.right (And.right hk))
                  (ce-filter (created-other (:id b)) _ (And.left (And.right hk))) Bool.and_self Bool.or_true]))))

(a/theorem comp-result-row-nsl [res :- RunResult, ep :- Nat, c :- CompRow] (= (no-sleep (comp-result-row res ep) c) true)
  (cases hi (:idle c)) (all_goals (simp only [no-sleep comp-result-row hi Bool.not_true Bool.not_false Bool.or_true Bool.true_or])))
(a/theorem comp-result-row-kcl [res :- RunResult, ep :- Nat, c :- CompRow] (= (keeps-clean (comp-result-row res ep) c) true)
  (cases hk (clean-one c))
  (case [false] (simp only [keeps-clean hk Bool.not_false Bool.true_or]))
  (case [true]
    (cases hi (:idle c))
    (case [false] (simp only [keeps-clean clean-one comp-result-row hi Bool.not_false Bool.true_or Bool.or_true]))
    (case [true]
      (simp only [clean-one idle-clean hi Bool.not_true Bool.false_or Bool.and_eq_true] at hk)
      (simp only [keeps-clean clean-one idle-clean comp-result-row hi Bool.not_true Bool.false_or (And.left hk)
                  created-empty bases-empty Bool.and_self Bool.or_true]))))

(a/theorem comp-clear-run-nsl [c :- CompRow] (= (no-sleep comp-clear-run c) true)
  (cases hi (:idle c)) (all_goals (simp only [no-sleep comp-clear-run hi Bool.not_true Bool.not_false Bool.or_true Bool.true_or])))
(a/theorem comp-clear-run-kcl [c :- CompRow] (= (keeps-clean comp-clear-run c) true)
  (cases hk (clean-one c))
  (case [false] (simp only [keeps-clean hk Bool.not_false Bool.true_or]))
  (case [true]
    (cases hi (:idle c))
    (case [false] (simp only [keeps-clean clean-one comp-clear-run hi Bool.not_false Bool.true_or Bool.or_true]))
    (case [true]
      (simp only [clean-one idle-clean hi Bool.not_true Bool.false_or Bool.and_eq_true] at hk)
      (simp only [keeps-clean clean-one idle-clean comp-clear-run hi Bool.not_true Bool.false_or (And.left (And.right hk))
                  (And.right (And.right hk)) Nat.beq_refl Bool.and_self Bool.or_true]))))

;; run rows that end a run or leave its slice
(defmacro ^:private defdown [& fs]
  `(do ~@(for [f fs]
           `(do (a/theorem ~(symbol (str f "-dwn")) [~'r :- ~'RunRow] (~'= (~'run-down ~f ~'r) true)
                  (~'simp [~'run-down ~'run-alive ~f ~'act-done ~'act-parked ~'act-active]))
                (a/theorem ~(symbol (str f "-snk")) [~'r :- ~'RunRow] (~'= (~'sn-keep ~f ~'r) true)
                  (~'simp [~'sn-keep ~'sn-one ~'run-alive ~f ~'mode-normal ~'mode-unwinding ~'act-done]))))))
(defdown run-cancel-row run-complete-row run-fin-pop-end)

(a/theorem run-wake-rk7 [r :- RunRow] (= (rk7 (run-wake r)) (rk7 r))
  (simp only [rk7 run-wake-alive]))

;; the generic source patch: a run / computation edit by a row function of the tables above
(def ^:private run-fns '{run-cancel-row [run-cancel-row-dwn run-cancel-row-snk]
                         run-complete-row [run-complete-row-dwn run-complete-row-snk]
                         run-fin-pop-end [run-fin-pop-end-dwn run-fin-pop-end-snk]})
(def ^:private comp-fns '#{comp-react-row comp-demand-row comp-start-row comp-replace-row comp-consume-adopt
                           comp-rebasis comp-result-row comp-clear-run})
(defn- fhead [f] (if (seq? f) (first f) f))
;; `_` as the row function: read it off the id lemma (`<f>-id`, `<f>-run-id`, `<f>-comp-id`)
(defn- f-of-hid [f hid]
  (if (not= '_ f) f
      (let [h (fhead hid) n (name h)
            base (some (fn [suf] (when (str/ends-with? n suf) (subs n 0 (- (count n) (count suf))))) ["-run-id" "-comp-id" "-id"])]
        (if base (if (seq? hid) (apply list (symbol base) (rest hid)) (symbol base)) f))))
(defn- lemma-app [f lem] (if (seq? f) (apply list lem (rest f)) lem))
(defn- fix-f [form]
  (subst-forms (fn [y] (and (seq? y) (#{'inv-run-upd 'inv-comp-upd} (first y)) (= '_ (nth y 3 nil))))
               (fn [y] (let [v (vec y)] (apply list (assoc v 3 (f-of-hid (nth v 3) (nth v 4)))))) form))
(defn g7-patch [form]
  (->> (fix-f form)
       (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (contains? run-fns (fhead (nth y 3 nil)))))
                    (fn [[_ w x f hid & more]]
                      (let [[d s] (run-fns (fhead f))]
                        (apply list 'g7-run-upd-m w x f hid (lemma-app f d) (lemma-app f s) more))))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (= 'run-wake (nth y 3 nil))))
                    (fn [[_ w x f hid & more]] (apply list 'g7-run-upd w x f hid 'run-wake-rk7 more)))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-comp-upd (first y)) (contains? comp-fns (fhead (nth y 3 nil)))))
                    (fn [[_ w x f hid hp & more]]
                      (let [h (name (fhead f))]
                        (apply list 'g7-comp-upd-m w x f hid hp (lemma-app f (symbol (str h "-nsl"))) (lemma-app f (symbol (str h "-kcl"))) more))))))

(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! G7 n g7-patch))

;; ===========================================================================
;; Part C. Overrides
;; ===========================================================================

;; ---- a run edit on the rows with one id, all satisfying the conditions (unique ids)

(a/defn rq [f :- (=> RunRow RunRow), r :- RunRow] Bool (Bool.and (run-down f r) (sn-keep f r)))

(a/theorem g7k-run-upd-q [x :- Nat, f :- (=> RunRow RunRow), cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (tbl-all (same-id-then run-id x (rq f)) rs) true) (= (g7k cs rs es) true) (= (g7k cs (tbl-upd run-id x f rs) es) true))
  (intros hq h)
  (have p := (g7k-parts cs rs es h))
  (have b1 := (tbl-all-mono2 RunRow (a7-one cs) (same-id-then run-id x (rq f)) (both (a7-one cs) (same-id-then run-id x (rq f)))
                (fn [q :- RunRow, h1 :- (= (a7-one cs q) true), h2 :- (= (same-id-then run-id x (rq f) q) true)]
                  (both-of RunRow (a7-one cs) (same-id-then run-id x (rq f)) q h1 h2))
                rs (And.left p) hq))
  (have h1 (= (tbl-all (a7-one cs) (tbl-upd run-id x f rs)) true))
  (apply (tbl-all-upd RunRow run-id x f (both (a7-one cs) (same-id-then run-id x (rq f))) (a7-one cs) _ _ rs b1))
  (intros r hb hx)
  (have hr := (both-left RunRow (a7-one cs) (same-id-then run-id x (rq f)) r hb))
  (have hs := (both-right RunRow (a7-one cs) (same-id-then run-id x (rq f)) r hb))
  (simp only [same-id-then hx Bool.not_true Bool.false_or rq Bool.and_eq_true] at hs)
  (have d := (And.left hs))
  (cases ha (run-alive (f r)))
  (case [false] (simp only [a7-one ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [run-down ha Bool.not_true Bool.false_or Bool.and_eq_true] at d)
    (have eo (= (:of (f r)) (:of r))) (exact (Nat.eq_of_beq_eq_true (And.right d)))
    (simp only [a7-one (And.left d) Bool.not_true Bool.false_or] at hr)
    (simp only [a7-one ha eo hr Bool.not_true Bool.false_or]))
  (intros r hb hx) (exact (both-left RunRow (a7-one cs) (same-id-then run-id x (rq f)) r hb))
  (have b4 := (tbl-all-mono2 RunRow sn-one (same-id-then run-id x (rq f)) (both sn-one (same-id-then run-id x (rq f)))
                (fn [q :- RunRow, h1 :- (= (sn-one q) true), h2 :- (= (same-id-then run-id x (rq f) q) true)]
                  (both-of RunRow sn-one (same-id-then run-id x (rq f)) q h1 h2))
                rs (And.left (And.right (And.right (And.right p)))) hq))
  (have h4 (= (tbl-all sn-one (tbl-upd run-id x f rs)) true))
  (apply (tbl-all-upd RunRow run-id x f (both sn-one (same-id-then run-id x (rq f))) sn-one _ _ rs b4))
  (intros r hb hx)
  (have hr := (both-left RunRow sn-one (same-id-then run-id x (rq f)) r hb))
  (have hs := (both-right RunRow sn-one (same-id-then run-id x (rq f)) r hb))
  (simp only [same-id-then hx Bool.not_true Bool.false_or rq Bool.and_eq_true] at hs)
  (have k := (And.right hs)) (simp only [sn-keep hr Bool.not_true Bool.false_or] at k) (exact k)
  (intros r hb hx) (exact (both-left RunRow sn-one (same-id-then run-id x (rq f)) r hb))
  (exact (g7k-intro _ _ _ h1 (And.left (And.right p)) (And.left (And.right (And.right p))) h4 (And.right (And.right (And.right (And.right p)))))))

(a/theorem g7-run-upd-at [w :- World, r :- RunRow, f :- (=> RunRow RunRow),
                          hf :- (forall [q :- RunRow] (= (run-id (f q)) (run-id q)))]
  (=> (List.Mem r (:runs w)) (= (run-down f r) true) (= (sn-keep f r) true) (= (g7 w) true) (= (g7 (run-upd w (:id r) f)) true))
  (intros hm hd hs h)
  (have hq := (uniq-all RunRow run-id (rq f) r (:runs w) (lit-runs-nodup w (g7-sample w h)) hm (both-of RunRow (run-down f) (sn-keep f) r hd hs)))
  (exact (g7-intro _ (inv-run-upd w (:id r) f hf (g7-sample w h))
           (g7k-run-upd-q (:id r) f (:comps w) (:runs w) (:edges w) hq (g7-rest-of w h)))))

;; ---- T-schedule and finalize enter a slice: an active run (alive), or an unwinding one

(a/theorem enter-dwn [r :- RunRow] (= (run-down run-enter-row r) true)
  (simp [run-down run-enter-row run-alive]))

(a/theorem sched-sn [w :- World, r :- RunRow] (=> (= (sched-ok w r) true) (= (sn-keep run-enter-row r) true))
  (intro h)
  (simp only [sched-ok Bool.and_eq_true] at h)
  (have e (= (:act r) act-active)) (exact (Nat.eq_of_beq_eq_true (And.left h)))
  (simp [sn-keep sn-one run-enter-row run-alive e act-active act-done]))

(a/theorem fin-sn [w :- World, r :- RunRow] (=> (= (cleanup-ready w r) true) (= (sn-keep run-enter-row r) true))
  (intro h)
  (simp only [cleanup-ready run-unwinding Bool.and_eq_true] at h)
  (have e (= (:mode r) mode-unwinding)) (exact (Nat.eq_of_beq_eq_true (And.left (And.right h))))
  (simp [sn-keep sn-one run-enter-row e mode-unwinding mode-normal]))

(a/theorem find-run-mem [w :- World, rid :- Nat, r :- RunRow]
  (=> (= (run-find w rid) (Option.some RunRow r)) (And (List.Mem r (:runs w)) (= (:id r) rid)))
  (intro hf)
  (exact (And.intro (tbl-find-mem RunRow run-id rid r (:runs w) hf) (tbl-find-id RunRow run-id rid r (:runs w) hf))))

(override! G7 'sched-inv '[]
  '(a/theorem sched-g7 [w :- World, rid :- Nat]
     (=> (= (g7 w) true) (= (g7 (:world (t-schedule w rid))) true))
     (intro h)
     (cases hf (run-find w rid)) (case' [some r]) (case' [none])
     (simp only [t-schedule hf refuse]) (exact h)
     (cases hg (sched-ok w r))
     (simp only [t-schedule hf hg refuse]) (exact h)
     (simp only [t-schedule hf hg accept])
     (have p := (find-run-mem w rid r hf))
     (rw [← (And.right p)])
     (exact (g7-run-upd-at w r run-enter-row run-enter-row-id (And.left p) (enter-dwn r) (sched-sn w r hg) h))))

(override! G7 't-finalize-inv '[]
  '(a/theorem t-finalize-g7 [w :- World, rid :- Nat]
     (=> (= (g7 w) true) (= (g7 (:world (t-finalize w rid))) true))
     (intro h)
     (cases hf (run-find w rid)) (case' [some r]) (case' [none])
     (simp only [t-finalize hf refuse]) (exact h)
     (cases hg (cleanup-ready w r))
     (simp only [t-finalize hf hg refuse]) (exact h)
     (simp only [t-finalize hf hg accept])
     (have p := (find-run-mem w rid r hf))
     (rw [← (And.right p)])
     (exact (g7-run-upd-at w r run-enter-row run-enter-row-id (And.left p) (enter-dwn r) (fin-sn w r hg) h))))

;; ---- take: the run parks (alive: run-normal), its new wait edge is no dep edge

(a/theorem park-dwn [r :- RunRow, f :- (=> RunRow RunRow), hal :- (= (run-alive r) true),
                     hof :- (= (:of (f r)) (:of r))]
  (= (run-down f r) true)
  (simp only [run-down hal hof Nat.beq_refl Bool.and_self Bool.or_true]))
(a/theorem tick-park-snk [r :- RunRow] (= (sn-keep run-tick-park r) true)
  (simp [sn-keep sn-one run-tick-park]))
(a/theorem park-snk [r :- RunRow] (= (sn-keep run-park-row r) true)
  (simp [sn-keep sn-one run-park-row]))

(a/theorem runs-iec [w :- World, e :- EdgeRow] (= (:runs (insert-edge-checked w e)) (:runs w))
  (cases hk (edge-ok-in w e)) (all_goals (simp only [insert-edge-checked hk insert-edge-fresh bump insert-edge edge-ins set-next-id set-edges])))

(override! G7 'inv-take-park '[inv-insert-edge-checked]
  '(a/theorem g7-take-park [w :- World, r :- RunRow, x :- Nat, k :- Nat]
     (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (g7 w) true) (= (g7 (take-park w r x k)) true))
     (intros hm ha h)
     (have h1 := (g7-insert-edge-checked _ (take-edge r (:next-id w) x) (Eq.refl true)
                   (g7-act-ins-fresh w (take-act w r k) (rfl) h)))
     (have hm2 (List.Mem r (:runs (insert-edge-checked (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x)))))
     (rw [runs-iec]) (exact hm)
     (simp only [take-park])
     (exact (g7-run-upd-at _ r run-tick-park run-tick-park-id hm2 (park-dwn r run-tick-park ha (Eq.refl (:of r))) (tick-park-snk r) h1))))

(a/theorem normal-alive [r :- RunRow] (=> (= (run-normal r) true) (= (run-alive r) true))
  (intro h) (simp only [run-normal Bool.and_eq_true] at h) (exact (And.left h)))

(override! G7 't-take-inv '[inv-take-park inv-take-now]
  '(a/theorem t-take-g7 [w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
     (=> (= (g7 w) true) (= (g7 (:world (t-take w st x k fresh))) true))
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
     (simp only [t-take ht hs hg hv accept]) (exact (g7-take-park w r x k (And.left p) (normal-alive r hn) h))
     (simp only [t-take ht hs hg hv accept]) (exact (g7-take-now w r x h))))

;; Z#55: arm = arm-raw (the resource), then take-park on the armed row
(override! G7 'inv-arm-park '[inv-take-park inv-arm-raw]
  '(a/theorem g7-arm-park [w :- World, r :- RunRow, kind :- Nat, k :- Nat]
     (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (g7 w) true) (= (g7 (arm-park w r kind k)) true))
     (intros hm ha h)
     (simp only [arm-park])
     (exact (g7-take-park _ (run-arm (:next-id w) r) (:next-id w) k (arm-raw-mem w r kind hm) ha (g7-arm-raw w r kind h)))))

(override! G7 't17-inv '[inv-arm-park]
  '(a/theorem t17-g7 [w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
     (=> (= (g7 w) true) (= (g7 (:world (t17-arm w st kind k fresh))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t17-arm ht refuse]) (exact h)
     (have p := (tok-facts w st r ht))
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind))))
     (simp only [t17-arm ht hg refuse]) (exact h)
     (have hn (= (run-normal r) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.left (And.right hg)))
     (simp only [t17-arm ht hg accept]) (exact (g7-arm-park w r kind k (And.left p) (normal-alive r hn) h))))

;; ---- edge insertion behind the endpoint check

(override! G7 'inv-insert-edge-checked '[]
  '(a/theorem g7-insert-edge-checked [w :- World, e :- EdgeRow, hn :- (= (edge-new-ok (:comps w) e) true)]
     (=> (= (g7 w) true) (= (g7 (insert-edge-checked w e)) true))
     (intro h)
     (cases hk (edge-ok-in w e))
     (simp only [insert-edge-checked hk]) (exact h)
     (simp only [insert-edge-checked hk]) (exact (g7-insert-edge-fresh w e hn hk h))))

;; ---- T7 track: the tracking run holds the slice in normal mode (not in a cleanup slice), so it
;; is alive (sn) and its computation is awake (a7)

(a/theorem tok-valid [w :- World, st :- Nat, r :- RunRow] (=> (= (tok-run w st) (Option.some RunRow r)) (= (run-valid r) true))
  (intro h)
  (cases hf (tbl-find run-stamp st (:runs w)))
  (case [none] (simp [tok-run hf] at h))
  (case [some r2]
    (cases hv (run-valid r2))
    (case [false] (simp [tok-run hf hv] at h))
    (case [true]
      (simp only [tok-run hf hv Option.some.injEq] at h)
      (rw [← h]) (exact hv))))

(a/theorem tok-awake [w :- World, st :- Nat, r :- RunRow]
  (=> (= (g7 w) true) (= (tok-run w st) (Option.some RunRow r)) (= (in-cleanup w st) false) (= (awake (:comps w) (:of r)) true))
  (intros h ht hc)
  (have p := (tok-facts w st r ht))
  (have hu := (cleanup-not-unw w st r hc ht))
  (have hv := (tok-valid w st r ht))
  (simp only [run-unwinding] at hu)
  (simp only [run-valid hu Bool.false_and Bool.or_false Bool.and_eq_true] at hv)
  (have q := (g7k-parts _ _ _ (g7-rest-of w h)))
  (have hs := (tbl-all-mem RunRow sn-one r (:runs w) (And.left (And.right (And.right (And.right q)))) (And.left p)))
  (simp only [sn-one (And.left hv) (And.right hv) Bool.and_self Bool.not_true Bool.false_or] at hs)
  (have ha := (tbl-all-mem RunRow (a7-one (:comps w)) r (:runs w) (And.left q) (And.left p)))
  (simp only [a7-one hs Bool.not_true Bool.false_or] at ha)
  (exact ha))

(override! G7 'inv-track-raw '[inv-track-fin]
  '(a/theorem g7-track-raw [w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat]
     (=> (= (comp-has w (:of r)) true) (= (source-find w x) (Option.some SourceRow s))
         (= (awake (:comps w) (:of r)) true) (= (g7 w) true) (= (g7 (track-raw w r x s k)) true))
     (intros hc hs haw h)
     (have hn (= (edge-new-ok (:comps w) (track-edge r x s k)) true))
     (simp [edge-new-ok track-edge obs-one haw ek-dep ek-observe])
     (have h2 (= (g7 (match (site-edge (:edges w) (:of r) (:effect-index r) x)
                        [none (track-new w r x s k)]
                        [(some e) (comp-upd (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s)))
                                            (:of r) (comp-consume-adopt (:effect-index r) x))])) true))
     (cases he (site-edge (:edges w) (:of r) (:effect-index r) x)) (case' [some e]) (case' [none])
     (simp only [track-new])
     (exact (g7-comp-upd-m _ (:of r) (comp-consume-adopt (:effect-index r) x)
              (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (comp-consume-adopt-nsl _ _) (comp-consume-adopt-kcl _ _)
              (g7-track-fin s (:next-id w) _ (g7-insert-edge-fresh w (track-edge r x s k) hn (track-edge-ok w r x s k hc hs) h))))
     (exact (g7-comp-upd-m _ (:of r) (comp-consume-adopt (:effect-index r) x)
              (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (comp-consume-adopt-nsl _ _) (comp-consume-adopt-kcl _ _)
              (g7-track-fin s (:id e) _
                (g7-edge-upd w (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) (edge-reread-kind _ _)
                  (edge-reread-creditor _ _) (edge-reread-debtor _ _) (edge-reread-marked _ _) h))))
     (simp only [track-raw])
     (exact (g7-run-upd _ (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (rk7 q))) h2))))

(override! G7 't7-inv '[inv-track-raw]
  '(a/theorem t7-g7 [w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
     (=> (= (in-cleanup w st) false) (= (g7 w) true) (= (g7 (:world (t7-track w st x k fresh))) true))
     (intros hcl h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t7-track ht refuse]) (exact h)
     (have haw := (tok-awake w st r h ht hcl))
     (cases hs (source-find w x)) (case' [some s]) (case' [none])
     (simp only [t7-track ht hs refuse]) (exact h)
     (cases hk (trackable s))
     (simp only [t7-track ht hs hk refuse]) (exact h)
     (cases hc (comp-has w (:of r)))
     (cases hta (task-has w (:of r)))
     (simp only [t7-track ht hs hk hc hta refuse]) (exact h)
     (simp only [t7-track ht hs hk hc hta accept]) (exact (g7-run-upd w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (rk7 q))) h))
     (cases hf (Bool.or (Nat.beq fresh (:next-id w)) (opt-some (site-edge (:edges w) (:of r) (:effect-index r) x))))
     (simp only [t7-track ht hs hk hc hf refuse]) (exact h)
     (simp only [t7-track ht hs hk hc hf accept]) (exact (g7-track-raw w r x s k hc hs haw h))))

(patch! G7 'raw0-inv
  (fn [form] (g7-patch (subst-forms #(= % '(t7-inv w _ _ _ _ h)) (fn [_] '(t7-inv w _ _ _ _ hc h)) form))))

;; ---- run creation: the new run's entity is awake (a task: no computation has its id)

(a/theorem g7k-run-ins [cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow), r :- RunRow]
  (=> (= (awake cs (:of r)) true) (= (sn-one r) true) (= (g7k cs rs es) true) (= (g7k cs (tbl-ins r rs) es) true))
  (intros ha hs h)
  (have p := (g7k-parts cs rs es h))
  (have a1 (= (a7-one cs r) true)) (simp only [a7-one ha Bool.or_true])
  (exact (g7k-intro _ _ _ (all-cons RunRow (a7-one cs) r rs a1 (And.left p)) (And.left (And.right p)) (And.left (And.right (And.right p)))
           (all-cons RunRow sn-one r rs hs (And.left (And.right (And.right (And.right p))))) (And.right (And.right (And.right (And.right p)))))))

(a/theorem g7-add-run-scope [w :- World, of :- Nat, ep :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (awake (:comps w) of) true) (= (g7 w) true) (= (g7 (add-run-scope w of ep parent ei)) true))
  (intros ha h)
  (have hr (= (g7-rest (add-run-scope w of ep parent ei)) true))
  (simp only [g7-rest add-run-scope bump scope-ins run-ins set-next-id set-scopes set-runs])
  (exact (g7k-run-ins (:comps w) (:runs w) (:edges w) (new-run-row (:next-id w) of ep (+ (:next-id w) 1) ei) ha (Eq.refl true) (g7-rest-of w h)))
  (exact (g7-intro _ (inv-add-run-scope w of ep parent ei (g7-sample w h)) hr)))

(a/theorem awake-fresh [w :- World] (=> (= (inv-sample w) true) (= (awake (:comps w) (:next-id w)) true))
  (intro h)
  (apply awake-absent)
  (cases hc (tbl-has comp-id (:next-id w) (:comps w)))
  (case [false] (rfl))
  (case [true] (have l := (comp-below w (:next-id w) h hc)) (omega)))

(override! G7 'inv-spawn-rows '[]
  '(a/theorem g7-spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat)]
     (=> (= (g7 w) true) (= (g7 (spawn-rows w owner inputs)) true))
     (intro h)
     (simp only [spawn-rows])
     (have h1 := (g7-task-ins-fresh w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs) (rfl) h))
     (have a1 (= (awake (:comps (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs)))) (:next-id w)) true))
     (exact (awake-fresh w (g7-sample w h)))
     (exact (g7-add-run-scope _ (:next-id w) 0 (task-scope-parent w owner) 0 a1 h1))))

(a/theorem awake-wake [x :- Nat, f :- (=> CompRow CompRow),
                       hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                       hw :- (forall [c :- CompRow] (= (:idle (f c)) false)), cs :- (List CompRow)]
  (= (awake (tbl-upd comp-id x f cs) x) true)
  (induction cs)
  (case [nil] (simp [awake tbl-upd tbl-all]))
  (case [cons hd t ih]
    (simp only [awake] at ih)
    (cases hx (Nat.beq (comp-id hd) x))
    (case [true] (simp only [awake tbl-upd hx tbl-all ih not-idle-if-id (hw hd) Bool.not_false Bool.or_true Bool.and_self]))
    (case [false]
      (have e (= (Nat.beq (:id hd) x) false)) (exact hx)
      (simp only [awake tbl-upd hx tbl-all ih not-idle-if-id e Bool.not_false Bool.true_or Bool.and_self]))))

(override! G7 'inv-start-raw '[]
  '(a/theorem g7-start-raw [w :- World, c :- CompRow]
     (=> (= (g7 w) true) (= (g7 (start-raw w c)) true))
     (intro h)
     (have hr (= (g7-rest (start-raw w c)) true))
     (simp only [g7-rest start-raw comp-upd add-run-scope bump scope-ins run-ins set-next-id set-scopes set-runs set-comps])
     (have h1 := (g7k-comp-upd (:id c) (comp-start-row (:next-id w)) (comp-start-row-id (:next-id w))
                   (comp-start-row-nsl (:next-id w)) (comp-start-row-kcl (:next-id w)) (:comps w) (:runs w) (:edges w) (g7-rest-of w h)))
     (exact (g7k-run-ins _ (:runs w) (:edges w) (new-run-row (:next-id w) (:id c) (start-epoch c) (+ (:next-id w) 1) 0)
              (awake-wake (:id c) (comp-start-row (:next-id w)) (comp-start-row-id (:next-id w)) (fn [q :- CompRow] (Eq.refl false)) (:comps w))
              (Eq.refl true) h1))
     (exact (g7-intro _ (inv-start-raw w c (g7-sample w h)) hr))))

;; ===========================================================================
;; Part D. The companion bundle awo awc awr: computation awc is awake and every run row with id
;; awr belongs to awc (carried through the T6 await, T11 dispatch and reactivation chains)
;; ===========================================================================

(a/defn run-of-at [awr :- Nat, awc :- Nat, q :- RunRow] Bool (Bool.or (Bool.not (Nat.beq (:id q) awr)) (Nat.beq (:of q) awc)))
(a/defn awo-rest [awc :- Nat, awr :- Nat, w :- World] Bool
  (Bool.and (awake (:comps w) awc) (tbl-all (run-of-at awr awc) (:runs w))))
(a/defn awo [awc :- Nat, awr :- Nat, w :- World] Bool (Bool.and (inv-sample w) (awo-rest awc awr w)))

(a/theorem awo-sample [awc :- Nat, awr :- Nat, w :- World] (=> (= (awo awc awr w) true) (= (inv-sample w) true))
  (intro h) (simp only [awo Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem awo-rest-of [awc :- Nat, awr :- Nat, w :- World] (=> (= (awo awc awr w) true) (= (awo-rest awc awr w) true))
  (intro h) (simp only [awo Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem awo-intro [awc :- Nat, awr :- Nat, w :- World] (=> (= (inv-sample w) true) (= (awo-rest awc awr w) true) (= (awo awc awr w) true))
  (intros h1 h2) (simp only [awo h1 h2 Bool.and_self]))
(a/theorem awo-parts [awc :- Nat, awr :- Nat, w :- World]
  (=> (= (awo awc awr w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (awo-sample awc awr w h))))
(a/theorem awo-awake [awc :- Nat, awr :- Nat, w :- World] (=> (= (awo awc awr w) true) (= (awake (:comps w) awc) true))
  (intro h) (have r := (awo-rest-of awc awr w h)) (simp only [awo-rest Bool.and_eq_true] at r) (exact (And.left r)))
(a/theorem awo-of [awc :- Nat, awr :- Nat, w :- World] (=> (= (awo awc awr w) true) (= (tbl-all (run-of-at awr awc) (:runs w)) true))
  (intro h) (have r := (awo-rest-of awc awr w h)) (simp only [awo-rest Bool.and_eq_true] at r) (exact (And.right r)))
(a/theorem awo-rest-mk [awc :- Nat, awr :- Nat, w :- World]
  (=> (= (awake (:comps w) awc) true) (= (tbl-all (run-of-at awr awc) (:runs w)) true) (= (awo-rest awc awr w) true))
  (intros h1 h2) (simp only [awo-rest h1 h2 Bool.and_self]))

;; the rest under the edits
(a/theorem awo-rest-comps [awc :- Nat, awr :- Nat, w :- World, w2 :- World,
                           ha :- (=> (= (awake (:comps w) awc) true) (= (awake (:comps w2) awc) true)),
                           hr :- (= (:runs w2) (:runs w))]
  (=> (= (awo-rest awc awr w) true) (= (awo-rest awc awr w2) true))
  (intro h) (simp only [awo-rest Bool.and_eq_true] at h)
  (simp only [awo-rest hr (ha (And.left h)) (And.right h) Bool.and_self]))

(a/theorem awo-run-upd [awc :- Nat, awr :- Nat, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                        hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        ho :- (forall [r :- RunRow] (= (:of (f r)) (:of r)))]
  (=> (= (awo awc awr w) true) (= (awo awc awr (run-upd w x f)) true))
  (intro h)
  (have r1 (= (tbl-all (run-of-at awr awc) (:runs (run-upd w x f))) true))
  (simp only [run-upd set-runs])
  (apply (tbl-all-upd RunRow run-id x f (run-of-at awr awc) (run-of-at awr awc) _ _ (:runs w) (awo-of awc awr w h)))
  (intros q hq hx)
  (have e1 (= (:id (f q)) (:id q))) (exact (hf q))
  (simp only [run-of-at] at hq) (simp only [run-of-at e1 (ho q)]) (exact hq)
  (intros q hq hx) (exact hq)
  (exact (awo-intro awc awr _ (inv-run-upd w x f hf (awo-sample awc awr w h)) (awo-rest-mk awc awr (run-upd w x f) (awo-awake awc awr w h) r1))))

(a/theorem awo-run-del [awc :- Nat, awr :- Nat, w :- World, x :- Nat]
  (=> (= (awo awc awr w) true) (= (awo awc awr (run-del w x)) true))
  (intro h)
  (have r1 (= (tbl-all (run-of-at awr awc) (:runs (run-del w x))) true))
  (simp only [run-del set-runs])
  (exact (tbl-all-del RunRow run-id x (run-of-at awr awc) (run-of-at awr awc) (fn [q :- RunRow, hq :- (= (run-of-at awr awc q) true), hx :- (= (Nat.beq (run-id q) x) false)] hq)
           (:runs w) (awo-of awc awr w h)))
  (exact (awo-intro awc awr _ (inv-run-del w x (awo-sample awc awr w h)) (awo-rest-mk awc awr (run-del w x) (awo-awake awc awr w h) r1))))

(a/theorem awo-comp-upd-m [awc :- Nat, awr :- Nat, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                           hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                           hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                           hs :- (forall [c :- CompRow] (= (no-sleep f c) true))]
  (=> (= (awo awc awr w) true) (= (awo awc awr (comp-upd w x f)) true))
  (intro h)
  (exact (awo-intro awc awr _ (inv-comp-upd w x f hid hp (awo-sample awc awr w h))
           (awo-rest-comps awc awr w (comp-upd w x f) (fn [a1 :- (= (awake (:comps w) awc) true)] (awake-upd x f hid hs (:comps w) awc a1)) (rfl)
             (awo-rest-of awc awr w h)))))

(a/theorem awo-comp-upd [awc :- Nat, awr :- Nat, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                         hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                         hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                         hk :- (forall [c :- CompRow] (= (ck7 (f c)) (ck7 c)))]
  (=> (= (awo awc awr w) true) (= (awo awc awr (comp-upd w x f)) true))
  (exact (awo-comp-upd-m awc awr w x f hid hp (ck7-no-sleep f hk))))

(a/theorem awo-comp-ins-fresh [awc :- Nat, awr :- Nat, w :- World, r :- CompRow, hni :- (= (:idle r) false)]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (awo awc awr w) true) (= (awo awc awr (bump (comp-ins w r))) true))
  (intros h1 h2 h)
  (exact (awo-intro awc awr _ (inv-comp-ins-fresh w r h1 h2 (awo-sample awc awr w h))
           (awo-rest-comps awc awr w (bump (comp-ins w r)) (fn [a1 :- (= (awake (:comps w) awc) true)] (awake-ins r (:comps w) awc hni a1)) (rfl)
             (awo-rest-of awc awr w h)))))

;; edge edits keep the computation rows up to pending
(a/theorem awake-pending [x :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hk :- (forall [c :- CompRow] (= (ck7 (f c)) (ck7 c))), cs :- (List CompRow), y :- Nat]
  (=> (= (awake cs y) true) (= (awake (tbl-upd comp-id x f cs) y) true))
  (exact (awake-upd x f hid (ck7-no-sleep f hk) cs y)))

(a/theorem awake-remove-edge [w :- World, x :- Nat, y :- Nat]
  (=> (= (awake (:comps w) y) true) (= (awake (:comps (remove-edge w x)) y) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm edge-del set-edges]) (exact h))
    (case [true] (simp only [remove-edge hf hm comp-upd edge-del set-edges set-comps])
      (exact (awake-pending _ comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (ck7 c))) _ y h)))))
(a/theorem awake-mark-edge [w :- World, x :- Nat, y :- Nat]
  (=> (= (awake (:comps w) y) true) (= (awake (:comps (mark-edge w x)) y) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false] (simp only [mark-edge hf hm comp-upd edge-upd set-edges set-comps])
      (exact (awake-pending _ comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (ck7 c))) _ y h)))))
(a/theorem awake-unmark-edge [w :- World, x :- Nat, y :- Nat]
  (=> (= (awake (:comps w) y) true) (= (awake (:comps (unmark-edge w x)) y) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true] (simp only [unmark-edge hf hm comp-upd edge-upd set-edges set-comps])
      (exact (awake-pending _ comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (ck7 c))) _ y h)))))
(a/theorem runs-remove-edge [w :- World, x :- Nat] (= (:runs (remove-edge w x)) (:runs w))
  (cases hf (edge-find w x)) (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm comp-upd edge-del set-edges set-comps]))))
(a/theorem runs-mark-edge [w :- World, x :- Nat] (= (:runs (mark-edge w x)) (:runs w))
  (cases hf (edge-find w x)) (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm comp-upd edge-upd set-edges set-comps]))))
(a/theorem runs-unmark-edge [w :- World, x :- Nat] (= (:runs (unmark-edge w x)) (:runs w))
  (cases hf (edge-find w x)) (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm comp-upd edge-upd set-edges set-comps]))))

(def AWO (mk-bundle 'awo '[awc :- Nat, awr :- Nat] "awo-"
           {'inv-comp-upd ['(fn [c :- CompRow] (Eq.refl (ck7 c))) 5]
            'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (:of r))) 4]
            'inv-comp-ins-fresh ['(Eq.refl false) 2]}))
(swap! (:renames AWO) assoc 'inv-parts 'awo-parts 'inv-comp-upd 'awo-comp-upd 'inv-run-upd 'awo-run-upd
       'inv-comp-ins-fresh 'awo-comp-ins-fresh 'inv-run-del 'awo-run-del)

(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del
            inv-set-pins inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-task-upd inv-edge-upd
            inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-act-ins-fresh inv-task-ins-fresh inv-bump
            insert-edge-fresh-inv-sample]]
  (prim! AWO o nil))
(prim! AWO 'inv-drop-cred '(awo-rest-comps awc awr w (drop-cred-edges w a) (fn [a1 :- (= (awake (:comps w) awc) true)] (awake-pending a (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (ck7 c))) _ awc a1)) (rfl) R))
(prim! AWO 'inv-drop-act '(awo-rest-comps awc awr w (drop-act w a) (fn [a1 :- (= (awake (:comps w) awc) true)] (awake-pending a (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (comp-id c))) (fn [c :- CompRow] (Eq.refl (ck7 c))) _ awc a1)) (rfl) R))
(prim! AWO 'inv-drop-edges '(awo-rest-comps awc awr w (drop-edges w p) (fn [a1 :- (= (awake (:comps w) awc) true)] (Eq.trans (awake-resync _ (:comps w) awc) a1)) (rfl) R))
(prim! AWO 'inv-comp-del-unref '(awo-rest-comps awc awr w (comp-del w x) (fn [a1 :- (= (awake (:comps w) awc) true)] (awake-del x (:comps w) awc a1)) (rfl) R))
(prim! AWO 'inv-remove-edge '(awo-rest-comps awc awr w (remove-edge w x) (awake-remove-edge w x awc) (runs-remove-edge w x) R))
(prim! AWO 'mark-edge-inv-sample '(awo-rest-comps awc awr w (mark-edge w x) (awake-mark-edge w x awc) (runs-mark-edge w x) R))
(prim! AWO 'unmark-edge-inv-sample '(awo-rest-comps awc awr w (unmark-edge w x) (awake-unmark-edge w x awc) (runs-unmark-edge w x) R))

(a/theorem comp-cut-row-nsl [has :- Bool, cut :- Nat, bs :- (List AdoptBase), c :- CompRow] (= (no-sleep (comp-cut-row has cut bs) c) true)
  (cases hi (:idle c)) (all_goals (simp only [no-sleep comp-cut-row hi Bool.not_true Bool.not_false Bool.or_true Bool.true_or])))
(a/theorem comp-set-run-nsl [rid :- Nat, c :- CompRow] (= (no-sleep (comp-set-run rid) c) true)
  (cases hi (:idle c)) (all_goals (simp only [no-sleep comp-set-run hi Bool.not_true Bool.not_false Bool.or_true Bool.true_or])))
(def ^:private awo-comp-fns (conj comp-fns 'comp-cut-row 'comp-set-run))

(defn awo-patch [form]
  (subst-forms (fn [y] (and (seq? y) (= 'inv-comp-upd (first y)) (contains? awo-comp-fns (fhead (nth y 3 nil)))))
               (fn [[_ w x f hid hp & more]]
                 (apply list 'awo-comp-upd-m 'awc 'awr w x f hid hp (lemma-app f (symbol (str (name (fhead f)) "-nsl"))) more))
               (fix-f form)))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! AWO n awo-patch))

;; ===========================================================================
;; Part E. Overrides through the chains (with awo)
;; ===========================================================================

(a/theorem of-at-zero [awc :- Nat, w :- World] (=> (= (inv-sample w) true) (= (tbl-all (run-of-at 0 awc) (:runs w)) true))
  (intro h)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (have hr := (And.left (And.right (And.right (And.right hb)))))
  (apply (all-of-mem RunRow (run-of-at 0 awc) (:runs w)))
  (intros q hm)
  (have hh := (mem-ids-has RunRow run-id q (:runs w) hm))
  (have hi := (all-nat-mem (id-in-range (:next-id w)) (run-id q) _ hr hh))
  (simp only [id-in-range Bool.and_eq_true Nat.blt_eq] at hi)
  (cases hz (Nat.beq (:id q) 0))
  (case [false] (simp only [run-of-at hz Bool.not_false Bool.true_or]))
  (case [true] (have e (= (:id q) 0)) (exact (Nat.eq_of_beq_eq_true hz)) (have l := (And.left hi)) (simp only [run-id e] at l) (omega)))

(a/theorem awo-zero [awc :- Nat, w :- World]
  (=> (= (inv-sample w) true) (= (awake (:comps w) awc) true) (= (awo awc 0 w) true))
  (intros h ha) (exact (awo-intro awc 0 w h (awo-rest-mk awc 0 w ha (of-at-zero awc w h)))))

;; ---- reactivation: the reactivated computation is awake while its edges are added

(override! G7 'inv-react-add '[inv-insert-edge-checked inv-raise-for]
  '(a/theorem g7-react-add [w :- World, c :- Nat, v :- Valid]
     (=> (= (awake (:comps w) c) true) (= (g7 w) true) (= (g7 (react-add w c v)) true))
     (intros ha h)
     (have hn (= (edge-new-ok (:comps w) (valid-edge w c v)) true))
     (simp [edge-new-ok valid-edge obs-one ha ek-dep ek-observe])
     (cases hk (react-ok w c v))
     (simp only [react-add hk]) (exact h)
     (simp only [react-add hk])
     (exact (g7-raise-for _ c (:debtor v) (g7-insert-edge-checked w _ hn h)))))

(override! G7 'inv-react-edges '[inv-react-add]
  '(a/theorem g7-react-edges [vs :- (List Valid)]
     (forall [w :- World, c :- Nat] (=> (= (awo c 0 w) true) (= (g7 w) true) (= (g7 (react-edges w c vs)) true)))
     (induction vs)
     (case' [cons h t ih])
     (case' [nil])
     (intros w c ha hw) (simp only [react-edges]) (exact hw)
     (intros w c ha hw) (simp only [react-edges])
     (exact (ih _ c (awo-react-add c 0 w c h ha) (g7-react-add w c h (awo-awake c 0 w ha) hw)))))

(override! G7 'inv-react-one '[inv-react-edges]
  '(a/theorem g7-react-one [w :- World, c :- CompRow]
     (=> (= (g7 w) true) (= (g7 (react-one w c)) true))
     (intro h)
     (simp only [react-one])
     (have h1 := (g7-comp-upd-m w (:id c) comp-react-row comp-react-row-id comp-react-row-pending comp-react-row-nsl comp-react-row-kcl h))
     (have a1 (= (awake (:comps (comp-upd w (:id c) comp-react-row)) (:id c)) true))
     (exact (awake-wake (:id c) comp-react-row comp-react-row-id (fn [q :- CompRow] (Eq.refl false)) (:comps w)))
     (exact (g7-react-edges (:validity c) _ (:id c) (awo-zero (:id c) _ (g7-sample _ h1) a1) h1))))

;; ---- T11: C is awake (not idle) through the predecessor's cancel, the cut and the entry

(a/theorem find-awake [w :- World, x :- Nat, c :- CompRow]
  (=> (= (inv-sample w) true) (= (comp-find w x) (Option.some CompRow c)) (= (:idle c) false) (= (awake (:comps w) x) true))
  (intros h hf hi)
  (have hm := (tbl-find-mem CompRow comp-id x c (:comps w) hf))
  (have e (= (comp-id c) x)) (exact (tbl-find-id CompRow comp-id x c (:comps w) hf))
  (have hq (= (Bool.not (:idle c)) true)) (simp only [hi Bool.not_false])
  (have u := (uniq-all CompRow comp-id (fn [b :- CompRow] (Bool.not (:idle b))) c (:comps w) (comps-nodup w h) hm hq))
  (rw [e] at u)
  (exact u))


(a/theorem idle-same-ns [f :- (=> CompRow CompRow), hs :- (forall [c :- CompRow] (= (:idle (f c)) (:idle c)))]
  (forall [c :- CompRow] (= (no-sleep f c) true))
  (intro c) (cases hi (:idle c)) (all_goals (simp only [no-sleep (hs c) hi Bool.not_true Bool.not_false Bool.or_true Bool.true_or])))

(a/theorem g7k-comp-upd-aw [x :- Nat, f :- (=> CompRow CompRow),
                            hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                            hs :- (forall [c :- CompRow] (= (:idle (f c)) (:idle c))),
                            cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (awake cs x) true) (= (g7k cs rs es) true) (= (g7k (tbl-upd comp-id x f cs) rs es) true))
  (intros ha h)
  (have ns := (idle-same-ns f hs))
  (have hc (=> (= (tbl-all clean-one cs) true) (= (tbl-all clean-one (tbl-upd comp-id x f cs)) true)))
  (intro hc0)
  (have b := (tbl-all-mono2 CompRow clean-one (not-idle-if-id x) (both clean-one (not-idle-if-id x))
               (fn [c :- CompRow, h1 :- (= (clean-one c) true), h2 :- (= (not-idle-if-id x c) true)] (both-of CompRow clean-one (not-idle-if-id x) c h1 h2))
               cs hc0 ha))
  (apply (tbl-all-upd CompRow comp-id x f (both clean-one (not-idle-if-id x)) clean-one _ _ cs b))
  (intros c hb hx)
  (have hn := (both-right CompRow clean-one (not-idle-if-id x) c hb))
  (have hx2 (= (Nat.beq (:id c) x) true)) (exact hx)
  (simp only [not-idle-if-id hx2 Bool.not_true Bool.false_or] at hn)
  (have hi := (bnot-true _ hn))
  (simp only [clean-one (hs c) hi Bool.not_false Bool.true_or])
  (intros c hb hx) (exact (both-left CompRow clean-one (not-idle-if-id x) c hb))
  (exact (g7k-comp-sub cs (tbl-upd comp-id x f cs) rs es (fn [y :- Nat, hy :- (= (awake cs y) true)] (awake-upd x f hid ns cs y hy)) hc h)))

(a/theorem g7-comp-upd-aw [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                           hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                           hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                           hs :- (forall [c :- CompRow] (= (:idle (f c)) (:idle c)))]
  (=> (= (awake (:comps w) x) true) (= (g7 w) true) (= (g7 (comp-upd w x f)) true))
  (intros ha h)
  (exact (g7-intro _ (inv-comp-upd w x f hid hp (g7-sample w h))
           (g7k-comp-upd-aw x f hid hs (:comps w) (:runs w) (:edges w) ha (g7-rest-of w h)))))

(override! G7 'inv-cut-suffix '[]
  '(a/theorem g7-cut-suffix [w :- World, c :- Nat, has :- Bool, cut :- Nat, cid :- Nat]
     (=> (= (awake (:comps w) c) true) (= (g7 w) true) (= (g7 (cut-suffix w c has cut cid)) true))
     (intros ha h)
     (simp only [cut-suffix])
     (have a1 (= (awake (:comps (drop-edges w (keep-prefix c has cid))) c) true))
     (simp only [drop-edges set-comps set-edges awake-resync]) (exact ha)
     (exact (g7-comp-upd-aw _ c _ (comp-cut-row-id has cut _) (comp-cut-row-pending has cut _) (fn [q :- CompRow] (Eq.refl (:idle q))) a1
              (g7-drop-edges w (keep-prefix c has cid) h)))))

(override! G7 'inv-new-run-of '[]
  '(a/theorem g7-new-run-of [w :- World, c :- CompRow, ei :- Nat]
     (=> (= (awake (:comps w) (:id c)) true) (= (g7 w) true) (= (g7 (new-run-of w c ei)) true))
     (intros ha h)
     (simp only [new-run-of])
     (have h1 := (g7-add-run-scope w (:id c) (:epoch c) 0 ei ha h))
     (have a1 (= (awake (:comps (add-run-scope w (:id c) (:epoch c) 0 ei)) (:id c)) true)) (exact ha)
     (exact (g7-comp-upd-aw _ (:id c) (comp-set-run (:next-id w)) (comp-set-run-id (:next-id w)) (comp-set-run-pending (:next-id w))
              (fn [q :- CompRow] (Eq.refl (:idle q))) a1 h1))))

(override! G7 'inv-dispatch-raw '[inv-cancel-pred inv-consume-entry inv-new-run-of inv-cut-suffix]
  '(a/theorem g7-dispatch-raw [w :- World, c :- CompRow]
     (=> (= (awake (:comps w) (:id c)) true) (= (g7 w) true) (= (g7 (dispatch-raw w c)) true))
     (intros ha h)
     (have h1 := (g7-cancel-pred w c h))
     (have k1 := (awo-cancel-pred (:id c) 0 w c (awo-zero (:id c) w (g7-sample w h) ha)))
     (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
     (simp only [dispatch-raw he])
     (have k2 := (awo-cut-suffix (:id c) 0 _ (:id c) false 0 0 k1))
     (exact (g7-new-run-of _ c 0 (awo-awake (:id c) 0 _ k2) (g7-cut-suffix _ (:id c) false 0 0 (awo-awake (:id c) 0 _ k1) h1)))
     (simp only [dispatch-raw he])
     (have k3 := (awo-consume-entry (:id c) 0 _ e (awo-cut-suffix (:id c) 0 _ (:id c) true (:at e) (:id e) k1)))
     (exact (g7-new-run-of _ c _ (awo-awake (:id c) 0 _ k3)
              (g7-consume-entry _ e (g7-cut-suffix _ (:id c) true (:at e) (:id e) (awo-awake (:id c) 0 _ k1) h1))))))

(override! G7 't11-inv '[inv-dispatch-raw]
  '(a/theorem t11-g7 [w :- World, cid :- Nat, fresh :- Nat]
     (=> (= (g7 w) true) (= (g7 (:world (t11-dispatch w cid fresh))) true))
     (intro h)
     (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
     (simp only [t11-dispatch hc refuse]) (exact h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))))
     (simp only [t11-dispatch hc hg refuse]) (exact h)
     (have hi (= (:idle c) false)) (simp only [Bool.and_eq_true] at hg) (exact (bnot-true _ (And.left (And.right hg))))
     (have e (= (:id c) cid)) (exact (tbl-find-id CompRow comp-id cid c (:comps w) hc))
     (have ha (= (awake (:comps w) (:id c)) true)) (rw [e]) (exact (find-awake w cid c (g7-sample w h) hc hi))
     (simp only [t11-dispatch hc hg accept]) (exact (g7-dispatch-raw w c ha h))))

;; ---- T6 await: the awaiting run's computation is awake, and the parked rows belong to it

(a/defn rq2 [cs :- (List CompRow), f :- (=> RunRow RunRow), q :- RunRow] Bool (Bool.and (a7-one cs (f q)) (sn-one (f q))))

(a/theorem g7k-run-upd-abs [x :- Nat, f :- (=> RunRow RunRow), cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (tbl-all (same-id-then run-id x (rq2 cs f)) rs) true) (= (g7k cs rs es) true) (= (g7k cs (tbl-upd run-id x f rs) es) true))
  (intros hq h)
  (have p := (g7k-parts cs rs es h))
  (have b1 := (tbl-all-mono2 RunRow (a7-one cs) (same-id-then run-id x (rq2 cs f)) (both (a7-one cs) (same-id-then run-id x (rq2 cs f)))
                (fn [q :- RunRow, h1 :- (= (a7-one cs q) true), h2 :- (= (same-id-then run-id x (rq2 cs f) q) true)]
                  (both-of RunRow (a7-one cs) (same-id-then run-id x (rq2 cs f)) q h1 h2))
                rs (And.left p) hq))
  (have h1 (= (tbl-all (a7-one cs) (tbl-upd run-id x f rs)) true))
  (apply (tbl-all-upd RunRow run-id x f (both (a7-one cs) (same-id-then run-id x (rq2 cs f))) (a7-one cs) _ _ rs b1))
  (intros r hb hx)
  (have hs := (both-right RunRow (a7-one cs) (same-id-then run-id x (rq2 cs f)) r hb))
  (simp only [same-id-then hx Bool.not_true Bool.false_or rq2 Bool.and_eq_true] at hs) (exact (And.left hs))
  (intros r hb hx) (exact (both-left RunRow (a7-one cs) (same-id-then run-id x (rq2 cs f)) r hb))
  (have b4 := (tbl-all-mono2 RunRow sn-one (same-id-then run-id x (rq2 cs f)) (both sn-one (same-id-then run-id x (rq2 cs f)))
                (fn [q :- RunRow, h1 :- (= (sn-one q) true), h2 :- (= (same-id-then run-id x (rq2 cs f) q) true)]
                  (both-of RunRow sn-one (same-id-then run-id x (rq2 cs f)) q h1 h2))
                rs (And.left (And.right (And.right (And.right p)))) hq))
  (have h4 (= (tbl-all sn-one (tbl-upd run-id x f rs)) true))
  (apply (tbl-all-upd RunRow run-id x f (both sn-one (same-id-then run-id x (rq2 cs f))) sn-one _ _ rs b4))
  (intros r hb hx)
  (have hs := (both-right RunRow sn-one (same-id-then run-id x (rq2 cs f)) r hb))
  (simp only [same-id-then hx Bool.not_true Bool.false_or rq2 Bool.and_eq_true] at hs) (exact (And.right hs))
  (intros r hb hx) (exact (both-left RunRow sn-one (same-id-then run-id x (rq2 cs f)) r hb))
  (exact (g7k-intro _ _ _ h1 (And.left (And.right p)) (And.left (And.right (And.right p))) h4 (And.right (And.right (And.right (And.right p)))))))

(a/theorem park-rq2 [awc :- Nat, rid :- Nat, cs :- (List CompRow), rs :- (List RunRow)]
  (=> (= (awake cs awc) true) (= (tbl-all (run-of-at rid awc) rs) true)
      (= (tbl-all (same-id-then run-id rid (rq2 cs run-park-row)) rs) true))
  (intros ha h)
  (apply (tbl-all-mono RunRow (run-of-at rid awc) (same-id-then run-id rid (rq2 cs run-park-row)) _ rs h))
  (intros q hq)
  (cases hx (Nat.beq (run-id q) rid))
  (case [false] (simp only [same-id-then hx Bool.not_false Bool.true_or]))
  (case [true]
    (have hx2 (= (Nat.beq (:id q) rid) true)) (exact hx)
    (simp only [run-of-at hx2 Bool.not_true Bool.false_or] at hq)
    (have e (= (:of q) awc)) (exact (Nat.eq_of_beq_eq_true hq))
    (have a1 (= (a7-one cs (run-park-row q)) true)) (simp only [a7-one run-park-row e ha Bool.or_true])
    (have s1 (= (sn-one (run-park-row q)) true)) (simp [sn-one run-park-row])
    (simp only [same-id-then hx rq2 a1 s1 Bool.and_self Bool.or_true])))

(override! G7 'inv-park-if '[]
  '(a/theorem g7-park-if [awc :- Nat, w :- World, a :- Nat, rid :- Nat]
     (=> (= (awo awc rid w) true) (= (g7 w) true) (= (g7 (park-if w a rid)) true))
     (intros k h)
     (cases ha (act-has w a))
     (simp only [park-if ha]) (exact h)
     (simp only [park-if ha])
     (have q := (park-rq2 awc rid (:comps w) (:runs w) (awo-awake awc rid w k) (awo-of awc rid w k)))
     (exact (g7-intro _ (inv-run-upd w rid run-park-row run-park-row-id (g7-sample w h))
              (g7k-run-upd-abs rid run-park-row (:comps w) (:runs w) (:edges w) q (g7-rest-of w h))))))

(override! G7 'inv-await-step '[inv-insert-edge-checked inv-raise-for inv-edge-upd]
  '(a/theorem g7-await-step [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
     (=> (= (awake (:comps (:world acc)) (:of r)) true) (= (g7 (:world acc)) true) (= (g7 (:world (await-step r a mode k acc d))) true))
     (intros haw h)
     (cases hd (as-dep (:world acc) r d))
     (case [false]
       (simp only [await-step hd])
       (have hn (= (edge-new-ok (:comps (:world acc)) (await-edge (:world acc) r a mode k d)) true))
       (simp [edge-new-ok await-edge hd obs-one ek-dep ek-wait ek-observe])
       (exact (g7-insert-edge-checked _ _ hn h)))
     (case [true]
       (have hn (= (edge-new-ok (:comps (:world acc)) (await-edge (:world acc) r a mode k d)) true))
       (simp [edge-new-ok await-edge hd obs-one haw ek-dep ek-observe])
       (cases hs (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
       (case [none]
         (simp only [await-step hd hs])
         (simp only [await-new-dep])
         (exact (g7-comp-upd-m _ (:of r) (comp-consume-adopt (:effect-index r) d)
                  (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (comp-consume-adopt-nsl _ _) (comp-consume-adopt-kcl _ _)
                  (g7-raise-for _ (:of r) d (g7-insert-edge-checked _ _ hn h)))))
       (case [some e]
         (simp only [await-step hd hs])
         (exact (g7-comp-upd-m _ (:of r) (comp-consume-adopt (:effect-index r) d)
                  (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (comp-consume-adopt-nsl _ _) (comp-consume-adopt-kcl _ _)
                  (g7-edge-upd _ (:id e) (edge-reawait (await-cont r mode k)) (edge-reawait-edge-id _)
                    (edge-reawait-kind _) (edge-reawait-creditor _) (edge-reawait-debtor _) (edge-reawait-marked _) h)))))))

(override! G7 'inv-await-wire '[inv-await-step]
  '(a/theorem g7-await-wire [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, ds :- (List Nat)]
     (forall [acc :- AwAcc] (=> (= (awo (:of r) (:id r) (:world acc)) true) (= (g7 (:world acc)) true)
                                (= (g7 (:world (await-wire r a mode k acc ds))) true)))
     (induction ds)
     (case' [cons d t ih])
     (case' [nil])
     (intros acc ka h) (simp only [await-wire]) (exact h)
     (intros acc ka h) (simp only [await-wire])
     (exact (ih _ (awo-await-step (:of r) (:id r) r a mode k acc d ka)
              (g7-await-step r a mode k acc d (awo-awake (:of r) (:id r) (:world acc) ka) h)))))

(override! G7 'inv-await-post '[inv-fast-fill inv-park-if inv-fin-if-final]
  '(a/theorem g7-await-post [awc :- Nat, a :- Nat, rid :- Nat, ds :- (List Nat), acc :- AwAcc]
     (=> (= (awo awc rid (:world acc)) true) (= (g7 (:world acc)) true) (= (g7 (await-post a rid ds acc)) true))
     (intros ka h)
     (have h2 := (g7-act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))
                   (act-set-members-id (mk-members (:pairs acc) 0 ds)) h))
     (have k2 := (awo-act-upd awc rid (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))
                   (act-set-members-id (mk-members (:pairs acc) 0 ds)) ka))
     (have h3 := (nat-fold-g7 (fast-fill (:pairs acc)) (g7-fast-fill (:pairs acc)) (nat-distinct ds)
                   (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))) h2))
     (have k3 := (nat-fold-awo awc rid (fast-fill (:pairs acc)) (awo-fast-fill awc rid (:pairs acc)) (nat-distinct ds)
                   (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))) k2))
     (have h4 := (g7-park-if awc _ a rid k3 h3))
     (exact (nat-fold-g7 fin-if-final g7-fin-if-final (nat-distinct ds) _ h4))))

(override! G7 'inv-await-raw '[inv-await-wire inv-await-pre inv-await-post]
  '(a/theorem g7-await-raw [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
     (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (g7 w) true) (= (g7 (await-raw w r ds mode k mine)) true))
     (intros hm hal h)
     (have q := (g7k-parts _ _ _ (g7-rest-of w h)))
     (have a0 := (tbl-all-mem RunRow (a7-one (:comps w)) r (:runs w) (And.left q) hm))
     (simp only [a7-one hal Bool.not_true Bool.false_or] at a0)
     (have o0 (= (tbl-all (run-of-at (:id r) (:of r)) (:runs w)) true))
     (exact (uniq-all RunRow run-id (fn [b :- RunRow] (Nat.beq (:of b) (:of r))) r (:runs w) (lit-runs-nodup w (g7-sample w h)) hm (Nat.beq_refl (:of r))))
     (have k0 := (awo-intro (:of r) (:id r) w (g7-sample w h) (awo-rest-mk (:of r) (:id r) w a0 o0)))
     (have g1 := (g7-await-pre w r ds mode k mine h))
     (have k1 := (awo-await-pre (:of r) (:id r) w r ds mode k mine k0))
     (have g2 := (g7-await-wire r (:next-id w) mode k (nat-distinct ds) (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) k1 g1))
     (have k2 := (awo-await-wire (:of r) (:id r) r (:next-id w) mode k (nat-distinct ds) (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) k1))
     (exact (g7-await-post (:of r) (:next-id w) (:id r) ds (await-acc w r ds mode k mine) k2 g2))))

(override! G7 't6-inv '[inv-await-raw]
  '(a/theorem t6-g7 [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
     (=> (= (g7 w) true) (= (g7 (:world (t6-await w st ds mode k fresh mine))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t6-await ht refuse]) (exact h)
     (have p := (tok-facts w st r ht))
     (cases hg (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
     (simp only [t6-await ht hg refuse]) (exact h)
     (have hn (= (run-normal r) true)) (simp only [await-ok Bool.and_eq_true] at hg) (exact (And.left (And.right (And.left hg))))
     (simp only [t6-await ht hg accept]) (exact (g7-await-raw w r ds mode k mine (And.left p) (normal-alive r hn) h))))

;; ===========================================================================
;; Part G. Cascade completeness for one computation (demote): after run-cascade with the cancel
;; jobs of every alive run of C, and an empty worklist, no run of C is alive. Bundle kdb kc kl kd:
;; an alive run of kc is listed in kl, and every run listed in kd is done (no revival, no new run)
;; ===========================================================================

(a/defn kd-one [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), q :- RunRow] Bool
  (Bool.and (Bool.or (Bool.not (run-alive q)) (Bool.or (Bool.not (Nat.beq (:of q) kc0)) (reach-mem (:id q) kl0)))
            (Bool.or (Bool.not (reach-mem (:id q) kd0)) (Bool.not (run-alive q)))))
(a/defn kdb-rest [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World] Bool (tbl-all (kd-one kc0 kl0 kd0) (:runs w)))
(a/defn kdb [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World] Bool (Bool.and (inv-sample w) (kdb-rest kc0 kl0 kd0 w)))

(a/theorem kdb-sample [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World] (=> (= (kdb kc0 kl0 kd0 w) true) (= (inv-sample w) true))
  (intro h) (simp only [kdb Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem kdb-rest-of [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World] (=> (= (kdb kc0 kl0 kd0 w) true) (= (kdb-rest kc0 kl0 kd0 w) true))
  (intro h) (simp only [kdb Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem kdb-intro [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World]
  (=> (= (inv-sample w) true) (= (kdb-rest kc0 kl0 kd0 w) true) (= (kdb kc0 kl0 kd0 w) true))
  (intros h1 h2) (simp only [kdb h1 h2 Bool.and_self]))
(a/theorem kdb-parts [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World]
  (=> (= (kdb kc0 kl0 kd0 w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (kdb-sample kc0 kl0 kd0 w h))))

(a/theorem kdb-run-upd-m [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                          hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                          hd :- (forall [r :- RunRow] (= (run-down f r) true))]
  (=> (= (kdb kc0 kl0 kd0 w) true) (= (kdb kc0 kl0 kd0 (run-upd w x f)) true))
  (intro h)
  (have r1 (= (kdb-rest kc0 kl0 kd0 (run-upd w x f)) true))
  (simp only [kdb-rest run-upd set-runs])
  (apply (tbl-all-upd RunRow run-id x f (kd-one kc0 kl0 kd0) (kd-one kc0 kl0 kd0) _ _ (:runs w) (kdb-rest-of kc0 kl0 kd0 w h)))
  (intros q hq hx)
  (have e1 (= (:id (f q)) (:id q))) (exact (hf q))
  (have d := (hd q))
  (simp only [kd-one Bool.and_eq_true] at hq)
  (cases ha (run-alive (f q)))
  (case [false] (simp only [kd-one ha Bool.not_false Bool.true_or Bool.or_true Bool.and_self]))
  (case [true]
    (simp only [run-down ha Bool.not_true Bool.false_or Bool.and_eq_true] at d)
    (have eo (= (:of (f q)) (:of q))) (exact (Nat.eq_of_beq_eq_true (And.right d)))
    (have q1 := (And.left hq)) (have q2 := (And.right hq))
    (simp only [(And.left d) Bool.not_true Bool.false_or] at q1)
    (simp only [(And.left d) Bool.not_true Bool.or_false] at q2)
    (simp only [kd-one ha eo e1 q1 q2 Bool.not_true Bool.false_or Bool.not_false Bool.true_or Bool.and_self]))
  (intros q hq hx) (exact hq)
  (exact (kdb-intro kc0 kl0 kd0 _ (inv-run-upd w x f hf (kdb-sample kc0 kl0 kd0 w h)) r1)))

(a/theorem kdb-run-upd [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                        hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hk :- (forall [r :- RunRow] (= (rk7 (f r)) (rk7 r)))]
  (=> (= (kdb kc0 kl0 kd0 w) true) (= (kdb kc0 kl0 kd0 (run-upd w x f)) true))
  (exact (kdb-run-upd-m kc0 kl0 kd0 w x f hf (rk7-down f hk))))

(a/theorem kdb-run-del [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World, x :- Nat]
  (=> (= (kdb kc0 kl0 kd0 w) true) (= (kdb kc0 kl0 kd0 (run-del w x)) true))
  (intro h)
  (have r1 (= (kdb-rest kc0 kl0 kd0 (run-del w x)) true))
  (simp only [kdb-rest run-del set-runs])
  (exact (tbl-all-del RunRow run-id x (kd-one kc0 kl0 kd0) (kd-one kc0 kl0 kd0)
           (fn [q :- RunRow, hq :- (= (kd-one kc0 kl0 kd0 q) true), hx :- (= (Nat.beq (run-id q) x) false)] hq) (:runs w) (kdb-rest-of kc0 kl0 kd0 w h)))
  (exact (kdb-intro kc0 kl0 kd0 _ (inv-run-del w x (kdb-sample kc0 kl0 kd0 w h)) r1)))

(def KDB (mk-bundle 'kdb '[kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat)] "kdb-"
           {'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (rk7 r))) 4]}))
(swap! (:renames KDB) assoc 'inv-parts 'kdb-parts 'inv-run-upd 'kdb-run-upd 'inv-run-del 'kdb-run-del)
(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del
            inv-set-pins inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-task-upd inv-edge-upd
            inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-act-ins-fresh inv-task-ins-fresh inv-bump
            insert-edge-fresh-inv-sample inv-drop-cred inv-drop-act inv-drop-edges inv-comp-del-unref
            inv-comp-upd inv-comp-ins-fresh]]
  (prim! KDB o nil))
(a/theorem kdb-rest-runs [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w2 :- World, w :- World]
  (=> (= (:runs w2) (:runs w)) (= (kdb-rest kc0 kl0 kd0 w2) (kdb-rest kc0 kl0 kd0 w)))
  (intro h) (simp only [kdb-rest h]))
(prim! KDB 'inv-remove-edge '(Eq.trans (kdb-rest-runs kc0 kl0 kd0 (remove-edge w x) w (runs-remove-edge w x)) R))
(prim! KDB 'mark-edge-inv-sample '(Eq.trans (kdb-rest-runs kc0 kl0 kd0 (mark-edge w x) w (runs-mark-edge w x)) R))
(prim! KDB 'unmark-edge-inv-sample '(Eq.trans (kdb-rest-runs kc0 kl0 kd0 (unmark-edge w x) w (runs-unmark-edge w x)) R))
(defn kdb-patch [form]
  (->> (fix-f form)
       (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (contains? run-fns (fhead (nth y 3 nil)))))
                    (fn [[_ w x f hid & more]]
                      (let [[d _] (run-fns (fhead f))]
                        (apply list 'kdb-run-upd-m 'kc0 'kl0 'kd0 w x f hid (lemma-app f d) more))))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (= 'run-wake (nth y 3 nil))))
                    (fn [[_ w x f hid & more]] (apply list 'kdb-run-upd 'kc0 'kl0 'kd0 w x f hid 'run-wake-rk7 more)))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! KDB n kdb-patch))
(lcopy! KDB 'inv-job-apply)

;; ---- a cancel job kills its run

(a/theorem has-false-ne [A :- Type, idf :- (=> A Nat), x :- Nat, xs :- (List A)]
  (=> (= (tbl-has idf x xs) false) (= (tbl-all (fn [q :- A] (Bool.not (Nat.beq (idf q) x))) xs) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (cases hx (Nat.beq (idf hd) x))
    (case [true] (simp [tbl-has hx] at h))
    (case [false] (simp only [tbl-has hx] at h) (simp only [tbl-all hx (ih h) Bool.not_false Bool.and_self]))))

(a/theorem bor-l [a :- Bool, b :- Bool] (=> (= a true) (= (Bool.or a b) true)) (intro h) (simp only [h Bool.true_or]))

(a/theorem kd-add [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), x :- Nat, q :- RunRow]
  (=> (= (kd-one kc0 kl0 kd0 q) true) (= (Bool.or (Bool.not (Nat.beq (:id q) x)) (Bool.not (run-alive q))) true)
      (= (kd-one kc0 kl0 (List.cons Nat x kd0) q) true))
  (intros h1 h2)
  (simp only [kd-one Bool.and_eq_true] at h1)
  (cases hx (Nat.beq (:id q) x))
  (case [false] (simp only [kd-one reach-mem-cons hx Bool.false_or (And.left h1) (And.right h1) Bool.and_self]))
  (case [true]
    (simp only [hx Bool.not_true Bool.false_or] at h2)
    (have ha := (bnot-true _ h2))
    (simp only [kd-one ha Bool.not_false Bool.true_or Bool.or_true Bool.and_self])))

(a/theorem kd-cancel-none [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World, x :- Nat]
  (=> (= (kdb kc0 kl0 kd0 w) true) (= (run-find w x) (Option.none RunRow)) (= (kdb kc0 kl0 (List.cons Nat x kd0) w) true))
  (intros h hf)
  (have hs := (kdb-sample kc0 kl0 kd0 w h))
  (have hr := (kdb-rest-of kc0 kl0 kd0 w h))
  (simp only [kdb-rest] at hr)
  (have hn := (tbl-find-none-has RunRow run-id x (:runs w) hf))
  (have a1 := (has-false-ne RunRow run-id x (:runs w) hn))
  (have b := (tbl-all-mono2 RunRow (kd-one kc0 kl0 kd0) (fn [q :- RunRow] (Bool.not (Nat.beq (run-id q) x))) (kd-one kc0 kl0 (List.cons Nat x kd0))
               (fn [q :- RunRow, h1 :- (= (kd-one kc0 kl0 kd0 q) true), h2 :- (= (Bool.not (Nat.beq (run-id q) x)) true)]
                 (kd-add kc0 kl0 kd0 x q h1 (bor-l _ _ h2)))
               (:runs w) hr a1))
  (exact (kdb-intro kc0 kl0 (List.cons Nat x kd0) w hs b)))

(a/theorem kd-cancel-dead [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World, x :- Nat, r :- RunRow]
  (=> (= (kdb kc0 kl0 kd0 w) true) (= (run-find w x) (Option.some RunRow r)) (= (run-alive r) false)
      (= (kdb kc0 kl0 (List.cons Nat x kd0) w) true))
  (intros h hf ha)
  (have hs := (kdb-sample kc0 kl0 kd0 w h))
  (have hr := (kdb-rest-of kc0 kl0 kd0 w h))
  (simp only [kdb-rest] at hr)
  (have p := (find-run-mem w x r hf))
  (have hq (= (Bool.not (run-alive r)) true)) (simp only [ha Bool.not_false])
  (have u := (uniq-all RunRow run-id (fn [q :- RunRow] (Bool.not (run-alive q))) r (:runs w) (lit-runs-nodup w hs) (And.left p) hq))
  (have e (= (run-id r) x)) (exact (And.right p))
  (rw [e] at u)
  (have b := (tbl-all-mono2 RunRow (kd-one kc0 kl0 kd0) (same-id-then run-id x (fn [q :- RunRow] (Bool.not (run-alive q))))
               (kd-one kc0 kl0 (List.cons Nat x kd0))
               (fn [q :- RunRow, h1 :- (= (kd-one kc0 kl0 kd0 q) true), h2 :- (= (same-id-then run-id x (fn [q2 :- RunRow] (Bool.not (run-alive q2))) q) true)]
                 (kd-add kc0 kl0 kd0 x q h1 h2))
               (:runs w) hr u))
  (exact (kdb-intro kc0 kl0 (List.cons Nat x kd0) w hs b)))

(a/theorem kd-cancel-row [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World, x :- Nat]
  (=> (= (kdb kc0 kl0 kd0 w) true) (= (kdb kc0 kl0 (List.cons Nat x kd0) (run-upd w x run-cancel-row)) true))
  (intro h)
  (have hs := (kdb-sample kc0 kl0 kd0 w h))
  (have hr := (kdb-rest-of kc0 kl0 kd0 w h))
  (simp only [kdb-rest] at hr)
  (have r1 (= (kdb-rest kc0 kl0 (List.cons Nat x kd0) (run-upd w x run-cancel-row)) true))
  (simp only [kdb-rest run-upd set-runs])
  (apply (tbl-all-upd RunRow run-id x run-cancel-row (kd-one kc0 kl0 kd0) (kd-one kc0 kl0 (List.cons Nat x kd0)) _ _ (:runs w) hr))
  (intros q hq hx)
  (have hd (= (run-alive (run-cancel-row q)) false)) (simp [run-alive run-cancel-row act-done])
  (simp only [kd-one hd Bool.not_false Bool.true_or Bool.or_true Bool.and_self])
  (intros q hq hx)
  (have hx2 (= (Nat.beq (:id q) x) false)) (exact hx)
  (have hn (= (Bool.not (Nat.beq (:id q) x)) true)) (simp only [hx2 Bool.not_false])
  (exact (kd-add kc0 kl0 kd0 x q hq (bor-l _ _ hn)))
  (exact (kdb-intro kc0 kl0 (List.cons Nat x kd0) _ (inv-run-upd w x run-cancel-row run-cancel-row-id hs) r1)))

(a/theorem kd-cancel [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World, x :- Nat, rep :- Bool]
  (=> (= (kdb kc0 kl0 kd0 w) true) (= (kdb kc0 kl0 (List.cons Nat x kd0) (job-apply w (Job.jcancel x rep))) true))
  (intro h)
  (cases hf (run-find w x))
  (case [none] (simp only [job-apply hf]) (exact (kd-cancel-none kc0 kl0 kd0 w x h hf)))
  (case [some r]
    (cases ha (run-alive r))
    (case [false] (simp only [job-apply hf ha]) (exact (kd-cancel-dead kc0 kl0 kd0 w x r h hf ha)))
    (case [true]
      (simp only [job-apply hf ha cancel-run-local])
      (have e (= (:id r) x)) (exact (And.right (find-run-mem w x r hf)))
      (have k1 := (kd-cancel-row kc0 kl0 kd0 w x h))
      (rw [e])
      (exact (kdb-cancel-debtor kc0 kl0 (List.cons Nat x kd0) rep _ r
               (kdb-cleanup-set kc0 kl0 (List.cons Nat x kd0) _ x (cleanup-rows-of w r)
                 (kdb-cancel-res kc0 kl0 (List.cons Nat x kd0) _ r
                   (kdb-cancel-acts kc0 kl0 (List.cons Nat x kd0) _ x k1))))))))

;; ---- the cascade: every listed run either is in kd or has a cancel job queued

(a/theorem all-reach-mem [p :- (=> Nat Bool), x :- Nat, xs :- (List Nat)]
  (=> (= (tbl-all p xs) true) (= (reach-mem x xs) true) (= (p x) true))
  (induction xs)
  (case [nil] (intros h hm) (simp [reach-mem] at hm))
  (case [cons hd t ih]
    (intros h hm)
    (simp only [tbl-all Bool.and_eq_true] at h)
    (cases hx (Nat.beq x hd))
    (case [true] (have e (= x hd)) (exact (Nat.eq_of_beq_eq_true hx)) (rw [e]) (exact (And.left h)))
    (case [false] (simp only [reach-mem hx] at hm) (exact (ih (And.right h) hm)))))

(a/defn job-cancels [x :- Nat, j :- Job] Bool
  (match j [(jcancel y rep) (Nat.beq y x)] [(jretire y) false] [(jclose s) false]))
(a/defn cov-one [kd0 :- (List Nat), js :- (List Job), x :- Nat] Bool (Bool.or (reach-mem x kd0) (tbl-any (job-cancels x) js)))
(a/defn not-alive-of [c :- Nat, q :- RunRow] Bool (Bool.or (Bool.not (run-alive q)) (Bool.not (Nat.beq (:of q) c))))

(a/theorem kd-final [kc0 :- Nat, kl0 :- (List Nat), kd0 :- (List Nat), w :- World]
  (=> (= (kdb kc0 kl0 kd0 w) true) (= (tbl-all (cov-one kd0 (List.nil Job)) kl0) true)
      (= (tbl-all (not-alive-of kc0) (:runs w)) true))
  (intros h hc)
  (have hr := (kdb-rest-of kc0 kl0 kd0 w h))
  (simp only [kdb-rest] at hr)
  (apply (tbl-all-mono RunRow (kd-one kc0 kl0 kd0) (not-alive-of kc0) _ (:runs w) hr))
  (intros q hq)
  (simp only [kd-one Bool.and_eq_true] at hq)
  (cases ha (run-alive q))
  (case [false] (simp only [not-alive-of ha Bool.not_false Bool.true_or]))
  (case [true]
    (cases ho (Nat.beq (:of q) kc0))
    (case [false] (simp only [not-alive-of ho Bool.not_false Bool.or_true]))
    (case [true]
      (have q1 := (And.left hq)) (simp only [ha ho Bool.not_true Bool.false_or] at q1)
      (have c1 := (all-reach-mem (cov-one kd0 (List.nil Job)) (:id q) kl0 hc q1))
      (simp only [cov-one tbl-any Bool.or_false] at c1)
      (have q2 := (And.right hq)) (simp only [c1 ha Bool.not_true Bool.or_false] at q2) (cases q2))))
(a/theorem cov-cancel-one [kd0 :- (List Nat), x :- Nat, rep :- Bool, t :- (List Job), nx :- (List Job), y :- Nat]
  (=> (= (cov-one kd0 (List.cons Job (Job.jcancel x rep) t) y) true)
      (= (cov-one (List.cons Nat x kd0) (List.append Job t nx) y) true))
  (intro h)
  (simp only [cov-one tbl-any job-cancels Bool.or_eq_true] at h)
  (simp only [cov-one reach-mem-cons tbl-any-app Bool.or_eq_true])
  (cases h)
  (case [inl h1] (exact (Or.inl (Or.inr h1))))
  (case [inr h2]
    (cases h2)
    (case [inl h3] (exact (Or.inl (Or.inl (Eq.trans (beq-comm y x) h3)))))
    (case [inr h4] (exact (Or.inr (Or.inl h4))))))

(a/theorem cov-other-one [kd0 :- (List Nat), j :- Job, hj :- (forall [y :- Nat] (= (job-cancels y j) false)), t :- (List Job), nx :- (List Job), y :- Nat]
  (=> (= (cov-one kd0 (List.cons Job j t) y) true) (= (cov-one kd0 (List.append Job t nx) y) true))
  (intro h)
  (simp only [cov-one tbl-any (hj y) Bool.false_or Bool.or_eq_true] at h)
  (simp only [cov-one tbl-any-app Bool.or_eq_true])
  (cases h)
  (case [inl h1] (exact (Or.inl h1)))
  (case [inr h2] (exact (Or.inr (Or.inl h2)))))

(a/theorem cov-nil [kd0 :- (List Nat), kl0 :- (List Nat), js :- (List Job)]
  (=> (= (jobs-empty js) true) (= (tbl-all (cov-one kd0 js) kl0) true) (= (tbl-all (cov-one kd0 (List.nil Job)) kl0) true))
  (intros he h) (cases js) (case [nil] (exact h)) (case [cons j t] (simp [jobs-empty] at he)))

(a/theorem casc-kill [kc0 :- Nat, kl0 :- (List Nat), fuel :- (List Nat)]
  (forall [w :- World, js :- (List Job), kd0 :- (List Nat)]
    (=> (= (kdb kc0 kl0 kd0 w) true) (= (tbl-all (cov-one kd0 js) kl0) true) (= (jobs-empty (:rest (cascade fuel w js))) true)
        (= (tbl-all (not-alive-of kc0) (:runs (:world (cascade fuel w js)))) true)))
  (induction fuel)
  (case [nil]
    (intros w js kd0 h hc he)
    (simp only [cascade] at he) (simp only [cascade])
    (exact (kd-final kc0 kl0 kd0 w h (cov-nil kd0 kl0 js he hc))))
  (case [cons u f ih]
    (intros w js kd0 h hc he)
    (cases js)
    (case [nil] (simp only [cascade]) (exact (kd-final kc0 kl0 kd0 w h hc)))
    (case [cons j t]
      (simp only [cascade] at he) (simp only [cascade])
      (cases j)
      (case [jcancel x rep]
        (exact (ih (job-apply w (Job.jcancel x rep)) _ (List.cons Nat x kd0) (kd-cancel kc0 kl0 kd0 w x rep h)
                 (tbl-all-mono Nat (cov-one kd0 (List.cons Job (Job.jcancel x rep) t)) (cov-one (List.cons Nat x kd0) (List.append Job t (job-next w (Job.jcancel x rep))))
                   (cov-cancel-one kd0 x rep t (job-next w (Job.jcancel x rep))) kl0 hc)
                 he)))
      (case [jretire x]
        (exact (ih (job-apply w (Job.jretire x)) _ kd0 (kdb-job-apply kc0 kl0 kd0 w (Job.jretire x) h)
                 (tbl-all-mono Nat (cov-one kd0 (List.cons Job (Job.jretire x) t)) (cov-one kd0 (List.append Job t (job-next w (Job.jretire x))))
                   (cov-other-one kd0 (Job.jretire x) (fn [y :- Nat] (Eq.refl false)) t (job-next w (Job.jretire x))) kl0 hc)
                 he)))
      (case [jclose s]
        (exact (ih (job-apply w (Job.jclose s)) _ kd0 (kdb-job-apply kc0 kl0 kd0 w (Job.jclose s) h)
                 (tbl-all-mono Nat (cov-one kd0 (List.cons Job (Job.jclose s) t)) (cov-one kd0 (List.append Job t (job-next w (Job.jclose s))))
                   (cov-other-one kd0 (Job.jclose s) (fn [y :- Nat] (Eq.refl false)) t (job-next w (Job.jclose s))) kl0 hc)
                 he))))))

(a/theorem all-of-mem-r [p :- (=> Nat Bool), xs :- (List Nat), h :- (forall [y :- Nat] (=> (= (reach-mem y xs) true) (= (p y) true)))]
  (= (tbl-all p xs) true)
  (induction xs)
  (case [nil] (simp [tbl-all]))
  (case [cons hd t ih]
    (have h1 (= (p hd) true)) (apply h) (simp only [reach-mem Nat.beq_refl])
    (have h2 (= (tbl-all p t) true))
    (apply ih) (intros y hy) (apply h) (simp only [reach-mem-cons hy Bool.or_true])
    (simp only [tbl-all h1 h2 Bool.and_self])))

;; ---- demote: its own cascade kills every alive run of C (casc-done needs acts-alive), its
;; dep edges are dropped, then C sleeps clean

(a/theorem cancel-jobs-cov [y :- Nat, xs :- (List Nat)]
  (=> (= (reach-mem y xs) true) (= (tbl-any (job-cancels y) (cancel-jobs xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp [reach-mem] at h))
  (case [cons hd t ih]
    (intro h)
    (cases hx (Nat.beq y hd))
    (case [true] (simp only [cancel-jobs tbl-any job-cancels (Eq.trans (beq-comm hd y) hx) Bool.true_or]))
    (case [false] (simp only [reach-mem hx] at h) (simp only [cancel-jobs tbl-any (ih h) Bool.or_true]))))

(a/theorem demote-dead [w :- World, c :- CompRow]
  (=> (= (inv-sample w) true) (= (acts-alive w) true)
      (= (tbl-all (not-alive-of (:id c)) (:runs (run-cascade w (cancel-jobs (demote-cancels w c))))) true))
  (intros h ha)
  (have k0 (= (kdb (:id c) (demote-cancels w c) (List.nil Nat) w) true))
  (apply (kdb-intro _ _ _ w h))
  (simp only [kdb-rest])
  (apply (all-of-mem RunRow (kd-one (:id c) (demote-cancels w c) (List.nil Nat)) (:runs w)))
  (intros q hm)
  (cases hl (run-alive q))
  (case [false] (simp only [kd-one hl reach-mem Bool.not_false Bool.true_or Bool.and_self]))
  (case [true]
    (cases ho (Nat.beq (:of q) (:id c)))
    (case [false] (simp only [kd-one hl ho reach-mem Bool.not_false Bool.not_true Bool.false_or Bool.true_or Bool.and_self]))
    (case [true]
      (have hp (= (run-alive-of (:id c) q) true)) (simp only [run-alive-of hl ho Bool.and_self])
      (have m1 := (scan-mem RunRow run-id (run-alive-of (:id c)) q (:runs w) hm hp))
      (have m2 (= (reach-mem (:id q) (demote-cancels w c)) true)) (simp only [demote-cancels]) (exact (rm-app-l _ _ _ m1))
      (simp only [kd-one hl ho m2 reach-mem Bool.not_false Bool.not_true Bool.false_or Bool.true_or Bool.and_self])))
  (have cv (= (tbl-all (cov-one (List.nil Nat) (cancel-jobs (demote-cancels w c))) (demote-cancels w c)) true))
  (apply (all-of-mem-r (cov-one (List.nil Nat) (cancel-jobs (demote-cancels w c))) (demote-cancels w c)))
  (intros y hy) (simp only [cov-one (cancel-jobs-cov y _ hy) Bool.or_true])
  (have cd := (casc-done-ok w (cancel-jobs (demote-cancels w c)) h ha))
  (simp only [casc-done cascade-run] at cd)
  (exact (casc-kill (:id c) (demote-cancels w c) _ w _ (List.nil Nat) k0 cv cd)))
(a/defn no-cred [x :- Nat, e :- EdgeRow] Bool
  (Bool.or (Bool.not (Bool.or (Nat.beq (:kind e) ek-dep) (:marked e))) (Bool.not (Nat.beq (:creditor e) x))))

;; the creditor of a non-dep edge is no computation (host 0 or an activation)
(a/theorem cred-not-comp [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (g7-rest w) true) (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) false)
      (= (tbl-has comp-id (:creditor e) (:comps w)) false))
  (intros h hr hm hk)
  (have p := (g7k-parts _ _ _ hr))
  (have ho := (tbl-all-mem EdgeRow obs-one e (:edges w) (And.right (And.right (And.right (And.right p)))) hm))
  (have hok := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                 (And.left (And.right (inv-parts w h))) hm))
  (simp only [edge-ok Bool.and_eq_true] at hok)
  (have hco := (And.left hok))
  (cases hh (host-cred e))
  (case [true]
    (have z (= (:creditor e) 0))
    (simp only [host-cred Bool.or_eq_true Bool.and_eq_true] at hh)
    (cases hh)
    (case [inl ho2] (simp only [obs-one ho2 Bool.not_true Bool.false_or] at ho) (exact (Nat.eq_of_beq_eq_true ho)))
    (case [inr hw] (exact (Nat.eq_of_beq_eq_true (And.right hw))))
    (rw [z]) (exact (comp-has-zero w h)))
  (case [false]
    (simp only [cred-ok hk hh] at hco)
    (exact (act-not-comp w (:creditor e) h hco))))

(a/theorem no-cred-of [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (g7-rest w) true) (= (tbl-has comp-id x (:comps w)) true)
      (= (tbl-all (not-dep-of x) (:edges w)) true) (= (tbl-all (no-cred x) (:edges w)) true))
  (intros h hr hx hd)
  (apply (all-of-mem EdgeRow (no-cred x) (:edges w)))
  (intros e hm)
  (have d := (tbl-all-mem EdgeRow (not-dep-of x) e (:edges w) hd hm))
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [true]
    (simp only [not-dep-of dep-of hk Bool.true_and] at d)
    (simp only [no-cred d Bool.or_true]))
  (case [false]
    (have nc := (cred-not-comp w e h hr hm hk))
    (cases he (Nat.beq (:creditor e) x))
    (case [false] (simp only [no-cred he Bool.not_false Bool.or_true]))
    (case [true]
      (have e2 (= (:creditor e) x)) (exact (Nat.eq_of_beq_eq_true he))
      (rw [e2] at nc) (rw [hx] at nc) (cases nc))))

(a/theorem awake-upd-ne [x :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                         cs :- (List CompRow), y :- Nat]
  (=> (= (Nat.beq y x) false) (= (awake cs y) true) (= (awake (tbl-upd comp-id x f cs) y) true))
  (intros hy h) (simp only [awake] at h) (simp only [awake])
  (apply (tbl-all-upd CompRow comp-id x f (not-idle-if-id y) (not-idle-if-id y) _ _ cs h))
  (intros c hc hx)
  (have e (= (:id (f c)) x)) (exact (Eq.trans (hid c) (Nat.eq_of_beq_eq_true hx)))
  (have hy2 (= (Nat.beq x y) false)) (exact (Eq.trans (beq-comm x y) hy))
  (simp only [not-idle-if-id e hy2 Bool.not_false Bool.true_or])
  (intros c hc hx) (exact hc))

(a/theorem sleep-a7 [x :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                     cs :- (List CompRow), q :- RunRow]
  (=> (= (a7-one cs q) true) (= (not-alive-of x q) true) (= (a7-one (tbl-upd comp-id x f cs) q) true))
  (intros a1 a2)
  (cases hl (run-alive q))
  (case [false] (simp only [a7-one hl Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [a7-one hl Bool.not_true Bool.false_or] at a1)
    (simp only [not-alive-of hl Bool.not_true Bool.false_or] at a2)
    (simp only [a7-one hl Bool.not_true Bool.false_or])
    (exact (awake-upd-ne x f hid cs (:of q) (bnot-true _ a2) a1))))

(a/theorem sleep-dm [x :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                     cs :- (List CompRow), e :- EdgeRow]
  (=> (= (dm-one cs e) true) (= (no-cred x e) true) (= (dm-one (tbl-upd comp-id x f cs) e) true))
  (intros a1 a2)
  (cases hd (Bool.or (Nat.beq (:kind e) ek-dep) (:marked e)))
  (case [false] (simp only [dm-one hd Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dm-one hd Bool.not_true Bool.false_or] at a1)
    (simp only [no-cred hd Bool.not_true Bool.false_or] at a2)
    (simp only [dm-one hd Bool.not_true Bool.false_or])
    (exact (awake-upd-ne x f hid cs (:creditor e) (bnot-true _ a2) a1))))

(a/theorem g7k-sleep [x :- Nat, f :- (=> CompRow CompRow),
                      hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                      hcl :- (forall [c :- CompRow] (= (clean-one (f c)) true)),
                      cs :- (List CompRow), rs :- (List RunRow), es :- (List EdgeRow)]
  (=> (= (tbl-all (not-alive-of x) rs) true) (= (tbl-all (no-cred x) es) true) (= (g7k cs rs es) true)
      (= (g7k (tbl-upd comp-id x f cs) rs es) true))
  (intros hna hnc h)
  (have p := (g7k-parts cs rs es h))
  (have h1 := (tbl-all-mono2 RunRow (a7-one cs) (not-alive-of x) (a7-one (tbl-upd comp-id x f cs))
                (fn [q :- RunRow, a1 :- (= (a7-one cs q) true), a2 :- (= (not-alive-of x q) true)] (sleep-a7 x f hid cs q a1 a2))
                rs (And.left p) hna))
  (have h2 := (tbl-all-mono2 EdgeRow (dm-one cs) (no-cred x) (dm-one (tbl-upd comp-id x f cs))
                (fn [e :- EdgeRow, a1 :- (= (dm-one cs e) true), a2 :- (= (no-cred x e) true)] (sleep-dm x f hid cs e a1 a2))
                es (And.left (And.right p)) hnc))
  (have h3 (= (tbl-all clean-one (tbl-upd comp-id x f cs)) true))
  (apply (tbl-all-upd CompRow comp-id x f clean-one clean-one _ _ cs (And.left (And.right (And.right p)))))
  (intros c hc hx) (exact (hcl c))
  (intros c hc hx) (exact hc)
  (exact (g7k-intro _ _ _ h1 h2 h3 (And.left (And.right (And.right (And.right p)))) (And.right (And.right (And.right (And.right p)))))))

(a/theorem comp-make-idle-clean [vs :- (List Valid), c :- CompRow] (= (clean-one (comp-make-idle vs c)) true)
  (simp [clean-one idle-clean comp-make-idle created-empty bases-empty]))

(a/theorem comp-find-has [w :- World, x :- Nat, c :- CompRow] (=> (= (comp-find w x) (Option.some CompRow c)) (= (tbl-has comp-id x (:comps w)) true))
  (intro hf) (exact (tbl-find-has CompRow comp-id x c (:comps w) hf)))

(override! G7 'inv-demote-finish '[inv-drop-edges inv-comp-del-unref]
  '(a/theorem g7-demote-finish [w :- World, cid :- Nat, vs :- (List Valid)]
     (=> (= (tbl-all (not-alive-of cid) (:runs w)) true) (= (tbl-all (not-dep-of cid) (:edges w)) true)
         (= (g7 w) true) (= (g7 (demote-finish w cid vs)) true))
     (intros hna hnd h)
     (cases hf (comp-find w cid)) (case' [some c]) (case' [none])
     (simp only [demote-finish hf]) (exact h)
     (cases hk (demote-keep w c))
     (simp only [demote-finish hf hk])
     (exact (g7-comp-del-unref _ cid (drop-edges-avoids w cid) (g7-drop-edges w (edge-avoids cid) h)))
     (simp only [demote-finish hf hk])
     (have hnc := (no-cred-of w cid (g7-sample w h) (g7-rest-of w h) (comp-find-has w cid c hf) hnd))
     (exact (g7-intro _ (inv-comp-upd w cid (comp-make-idle vs) (comp-make-idle-id vs) (comp-make-idle-pending vs) (g7-sample w h))
              (g7k-sleep cid (comp-make-idle vs) (comp-make-idle-id vs) (comp-make-idle-clean vs) (:comps w) (:runs w) (:edges w)
                hna hnc (g7-rest-of w h))))))

(a/theorem runs-demote-epoch [w :- World, cid :- Nat, b :- Bool] (= (:runs (demote-epoch w cid b)) (:runs w))
  (cases b) (all_goals (simp only [demote-epoch comp-upd set-comps])))

(override! G7 'inv-demote '[inv-run-cascade inv-demote-epoch inv-drop-edges inv-demote-finish]
  '(a/theorem g7-demote [w :- World, cid :- Nat]
     (=> (= (acts-alive w) true) (= (g7 w) true) (= (g7 (demote w cid)) true))
     (intros ha h)
     (cases hf (comp-find w cid)) (case' [some c]) (case' [none])
     (simp only [demote hf]) (exact h)
     (cases hi (:idle c))
     (simp only [demote hf hi demote-edges])
     (have e (= (:id c) cid)) (exact (tbl-find-id CompRow comp-id cid c (:comps w) hf))
     (have na := (demote-dead w c (g7-sample w h) ha))
     (rw [e] at na)
     (have g1 := (g7-run-cascade w (cancel-jobs (demote-cancels w c)) h))
     (have g2 := (g7-demote-epoch _ cid (demote-cur w c) g1))
     (have g3 := (g7-drop-edges _ (not-dep-of cid) g2))
     (have na3 (= (tbl-all (not-alive-of cid) (:runs (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) cid (demote-cur w c)) (not-dep-of cid)))) true))
     (simp only [drop-edges set-comps set-edges runs-demote-epoch]) (exact na)
     (have nd3 (= (tbl-all (not-dep-of cid) (:edges (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) cid (demote-cur w c)) (not-dep-of cid)))) true))
     (simp only [drop-edges set-comps set-edges]) (exact (tbl-all-filter-self EdgeRow (not-dep-of cid) _))
     (exact (g7-demote-finish _ cid _ na3 nd3 g3))
     (simp only [demote hf hi]) (exact h)))


;; ---- normalization with acts-alive (for demote's casc-done)

(lcopy! G7 'inv-demote)

(a/theorem g7-demote-fold [a :- Nat, k :- Nat, xs :- (List Nat)]
  (forall [w :- World] (=> (= (bn a k w) true) (= (g7 w) true) (= (g7 (nat-fold demote w xs)) true)))
  (induction xs)
  (case [nil] (intros w hb h) (simp only [nat-fold]) (exact h))
  (case [cons hd t ih]
    (intros w hb h) (simp only [nat-fold])
    (exact (ih (demote w hd) (bn-demote a k w hd hb) (g7-demote w hd (And.left (And.right (bn-parts a k w hb))) h)))))

(override! G7 'inv-norm-round '[inv-run-cascade inv-detach inv-demote]
  '(a/theorem g7-norm-round [w :- World]
     (=> (= (acts-alive w) true) (= (g7 w) true) (= (g7 (norm-round w)) true))
     (intros ha h)
     (simp only [norm-round norm-round-lv])
     (have b0 := (bn-intro (alive-cnt w) (act-cnt w) w (g7-sample w h) ha (Nat.le_refl _) (Nat.le_refl _)))
     (exact (g7-detach _ (g7-demote-fold (alive-cnt w) (act-cnt w) _ _
              (bn-run-cascade _ _ w _ b0) (g7-run-cascade w _ h))))))

(override! G7 'inv-norm-loop '[inv-norm-round]
  '(a/theorem g7-norm-loop [fuel :- (List Nat)]
     (forall [w :- World] (=> (= (acts-alive w) true) (= (g7 w) true) (= (g7 (norm-loop fuel w)) true)))
     (induction fuel)
     (case' [cons h f ih])
     (case' [nil])
     (intros w ha hw) (simp only [norm-loop]) (exact hw)
     (intros w ha hw)
     (cases hn (normalized w))
     (simp only [norm-loop hn])
     (exact (ih (norm-round w) (And.right (bn-round w (g7-sample w hw) ha)) (g7-norm-round w ha hw)))
     (simp only [norm-loop hn]) (exact hw)))

(override! G7 'inv-normalize '[inv-norm-loop inv-detach]
  '(a/theorem g7-normalize [w :- World]
     (=> (= (acts-alive w) true) (= (g7 w) true) (= (g7 (normalize w)) true))
     (intros ha h)
     (have b := (bn-detach (alive-cnt w) (act-cnt w) w (bn-intro (alive-cnt w) (act-cnt w) w (g7-sample w h) ha (Nat.le_refl _) (Nat.le_refl _))))
     (exact (g7-norm-loop (norm-fuel (detach w)) (detach w) (And.left (And.right (bn-parts _ _ _ b))) (g7-detach w h)))))

;; ===========================================================================
;; Part F. The copies
;; ===========================================================================

(doseq [r '[inv-cancel-pred inv-cut-suffix inv-consume-entry inv-react-add inv-await-step inv-await-pre inv-await-wire
            inv-fast-fill inv-fin-if-final]]
  (lcopy! AWO r))

(lcopy! G7 'raw-inv)
(lcopy! G7 'inv-normalize)

;; ===========================================================================
;; Part H. Rule R and the step
;; ===========================================================================

(a/theorem g7-rule-r-filter [w :- World]
  (=> (= (g7 w) true) (= (filter-safe w) true) (= (g7 (rule-r-filter w)) true))
  (intros h hf)
  (rw [rule-r-filter-eq])
  (exact (g7-filter-world w (keep-fn w) h hf)))

(a/theorem g7-rule-r-round [w :- World]
  (=> (= (acts-alive w) true) (= (g7 w) true) (= (filter-safe (normalize w)) true) (= (g7 (rule-r-round w)) true))
  (intros ha h hf)
  (simp only [rule-r-round])
  (exact (g7-rule-r-filter (normalize w) (g7-normalize w ha h) hf)))

(a/theorem g7-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (acts-alive w0) true) (= (g7 w0) true) (= (rr-safe fuel w0) true)
                            (= (g7 (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 ha h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (g7-rule-r-round w0 ha h hs)))
  (case [cons x f ih]
    (intros w0 ha h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (g7-rule-r-round w0 ha h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false]
      (simp only [ho] at hs) (simp only [rr-loop ho])
      (exact (ih (rule-r-round w0) (acts-alive-round w0 (g7-sample w0 h) ha) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))

(a/theorem g7-rule-r [w :- World]
  (=> (= (acts-alive w) true) (= (g7 w) true) (= (rule-r-safe w) true) (= (g7 (rule-r w)) true))
  (intros ha h hs)
  (simp only [rule-r-safe] at hs) (simp only [rule-r])
  (exact (g7-rr-loop (rr-fuel w) w ha h hs)))

;; Theorem: the bundle is preserved by every step (hypotheses of step-acts)
(a/theorem step-g7 [w :- World, it :- Item]
  (=> (= (ga w) true) (= (g7 w) true) (= (rule-r-safe (:world (raw w it))) true) (= (g7 (:world (world-step w it))) true))
  (intros hg h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true]
    (have e2 := (step-accepted w it ha)) (rw [e2])
    (exact (g7-rule-r (:world (raw w it)) (raw-acts-alive w it hg) (raw-g7 w it h) hs))))

(a/theorem g7-empty [] (= (g7 empty-world) true) (rfl))

;; ---- the literal I7 (idle shape) follows from the bundle

(a/theorem idle-not-awake [cs :- (List CompRow), c :- CompRow]
  (=> (List.Mem c cs) (= (:idle c) true) (= (awake cs (:id c)) false))
  (intros hm hi)
  (cases ha (awake cs (:id c)))
  (case [false] (rfl))
  (case [true]
    (simp only [awake] at ha)
    (have n := (tbl-all-mem CompRow (not-idle-if-id (:id c)) c cs ha hm))
    (simp [not-idle-if-id hi] at n)))

(a/theorem dm-no-cred [cs :- (List CompRow), x :- Nat, e :- EdgeRow]
  (=> (= (awake cs x) false) (= (dm-one cs e) true) (= (no-cred x e) true))
  (intros ha hd)
  (cases hk (Bool.or (Nat.beq (:kind e) ek-dep) (:marked e)))
  (case [false] (simp only [no-cred hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dm-one hk Bool.not_true Bool.false_or] at hd)
    (cases hc (Nat.beq (:creditor e) x))
    (case [false] (simp only [no-cred hc Bool.not_false Bool.or_true]))
    (case [true]
      (have e2 (= (:creditor e) x)) (exact (Nat.eq_of_beq_eq_true hc))
      (rw [e2] at hd) (rw [ha] at hd) (cases hd))))

(a/theorem marks-zero [x :- Nat, es :- (List EdgeRow)]
  (=> (= (tbl-all (no-cred x) es) true) (= (marked-in x es) 0))
  (induction es)
  (case [nil] (intro h) (simp only [marked-in tbl-count]))
  (case [cons hd t ih]
    (intro h)
    (simp only [tbl-all Bool.and_eq_true] at h)
    (have z := (ih (And.right h)))
    (simp only [marked-in] at z)
    (have m (= (marks x hd) false))
    (have n := (And.left h))
    (cases hm (:marked hd))
    (case [false] (simp only [marks hm Bool.and_false]))
    (case [true]
      (simp only [no-cred hm Bool.or_true Bool.not_true Bool.false_or] at n)
      (simp only [marks (bnot-true _ n) Bool.false_and]))
    (simp only [marked-in tbl-count m z])))

(a/theorem dep-none [x :- Nat, es :- (List EdgeRow)]
  (=> (= (tbl-all (no-cred x) es) true) (= (tbl-any (dep-of x) es) false))
  (induction es)
  (case [nil] (intro h) (simp only [tbl-any]))
  (case [cons hd t ih]
    (intro h)
    (simp only [tbl-all Bool.and_eq_true] at h)
    (have d (= (dep-of x hd) false))
    (have n := (And.left h))
    (cases hk (Nat.beq (:kind hd) ek-dep))
    (case [false] (simp only [dep-of hk Bool.false_and]))
    (case [true]
      (simp only [no-cred hk Bool.true_or Bool.not_true Bool.false_or] at n)
      (simp only [dep-of hk (bnot-true _ n) Bool.and_false]))
    (simp only [tbl-any d (ih (And.right h)) Bool.or_self])))

(a/theorem g7-i7 [w :- World] (=> (= (g7 w) true) (= (inv-i7 w) true))
  (intro h)
  (have hs := (g7-sample w h))
  (have p := (g7k-parts _ _ _ (g7-rest-of w h)))
  (have pe := (And.left (inv-parts w hs)))
  (simp only [pending-exact pending-exact-in] at pe)
  (simp only [inv-i7])
  (apply (all-of-mem CompRow (idle-shape w) (:comps w)))
  (intros c hm)
  (cases hi (:idle c))
  (case [false] (simp only [idle-shape hi Bool.not_false Bool.true_or]))
  (case [true]
    (have cl := (tbl-all-mem CompRow clean-one c (:comps w) (And.left (And.right (And.right p))) hm))
    (simp only [clean-one idle-clean hi Bool.not_true Bool.false_or Bool.and_eq_true] at cl)
    (have na := (idle-not-awake (:comps w) c hm hi))
    (have nc := (tbl-all-mono EdgeRow (dm-one (:comps w)) (no-cred (:id c)) (fn [e :- EdgeRow, he :- (= (dm-one (:comps w) e) true)] (dm-no-cred (:comps w) (:id c) e na he)) (:edges w) (And.left (And.right p))))
    (have ce := (tbl-all-mem CompRow (comp-exact (:edges w)) c (:comps w) pe hm))
    (simp only [comp-exact (marks-zero (:id c) (:edges w) nc)] at ce)
    (simp only [idle-shape hi (And.left cl) (And.left (And.right cl)) (And.right (And.right cl)) ce (dep-none (:id c) (:edges w) nc)
                Bool.not_true Bool.not_false Bool.false_or Bool.and_self])))

;; Theorem: I7 (idle shape) through the step (hypotheses as step-gl: ga and rule-r-safe of the raw world)
(a/theorem step-lit-i7 [w :- World, it :- Item]
  (=> (= (ga w) true) (= (g7 w) true) (= (rule-r-safe (:world (raw w it))) true) (= (inv-i7 (:world (world-step w it))) true))
  (intros hg h hs) (exact (g7-i7 _ (step-g7 w it hg h hs))))
