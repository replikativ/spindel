(ns spindel.v2.hm7
  "Bounded P11 reactivation preserves explicit H3 obligations. Arbitrary fuel
   proves safety of the returned world, without a queue-completion claim."
  (:require [ansatz.core :as a]
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
            [spindel.v2.hm :refer :all]
            [spindel.v2.hmk :refer :all]
            [spindel.v2.hm3 :refer :all]
            [spindel.v2.hm5 :refer :all]
            [spindel.v2.hm6 :refer :all]
            [spindel.v2.hm6-base :refer :all]))

;; Only a matching activation run is known alive. G7 then excludes the actual
;; idle computation as its owner; arbitrary run rows need not be alive.
(a/theorem h3-react-act-off [w :- World, c :- CompRow, b :- ActRow, r :- RunRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) true)
      (= (g7 w) true) (= (aha w) true)
      (List.Mem b (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run b))
      (= (Nat.beq (:of r) (:id c)) false))
  (intros mc hi hg ha mb mr ir)
  (have al := (aha-acts-alive w ha))
  (simp only [acts-alive] at al)
  (have ar := (tbl-all-mem RunRow _ r _ (tbl-all-mem ActRow _ b _ al mb) mr))
  (simp only [act-run-ok run-ok-for ir Nat.beq_refl Bool.not_true Bool.false_or] at ar)
  (have gp := (g7k-parts _ _ _ (g7-rest-of w hg)))
  (have aw := (tbl-all-mem RunRow _ r _ (And.left gp) mr))
  (simp only [a7-one ar Bool.not_true Bool.false_or] at aw)
  (cases he (Nat.beq (:of r) (:id c)))
  (case [false] (rfl))
  (case [true]
    (have oe := (Nat.eq_of_beq_eq_true he))
    (rw [oe (idle-not-awake (:comps w) c mc hi)] at aw)
    (cases aw)))

;; An idle row cannot satisfy an old strong-waiting obligation. Unique IDs
;; extend its idle flag to precisely the rows affected by the update.
(a/theorem h3-react-wif [w :- World, c :- CompRow, y :- Nat]
  (=> (= (inv-sample w) true) (List.Mem c (:comps w)) (= (:idle c) true)
      (= (tbl-all (hk-wif y) (:comps w)) true)
      (= (tbl-all (hk-wif y) (:comps (comp-upd w (:id c) comp-react-row))) true))
  (intros hs mc hi h)
  (have u := (uniq-all CompRow comp-id (fn [q :- CompRow] (:idle q)) c (:comps w) (comps-nodup w hs) mc hi))
  (simp only [comp-upd set-comps])
  (apply (all-upd2 CompRow comp-id (:id c) comp-react-row (hk-wif y)
           (same-id-then comp-id (:id c) (fn [q :- CompRow] (:idle q))) (hk-wif y) _ _ (:comps w) h u))
  (intros q hq uq eq)
  (simp only [same-id-then eq Bool.not_true Bool.false_or] at uq)
  (simp only [hk-wif hk-wt uq Bool.not_true Bool.false_and Bool.or_false] at hq)
  (simp only [hk-wif comp-react-row hq Bool.true_or])
  (intros q hq uq eq) (exact hq))

(a/theorem h3-react-cs-off [w :- World, c :- CompRow, k :- RK3]
  (=> (= (Nat.beq (:of k) (:id c)) false)
      (= (tbl-all (h3-cs k) (:comps w)) true)
      (= (tbl-all (h3-cs k) (:comps (comp-upd w (:id c) comp-react-row))) true))
  (intros hn h)
  (simp only [comp-upd set-comps])
  (apply (tbl-all-upd CompRow comp-id (:id c) comp-react-row (h3-cs k) (h3-cs k) _ _ (:comps w) h))
  (intros q hq eq)
  (have qi (= (:id q) (:id c))) (exact (Nat.eq_of_beq_eq_true eq))
  (have ne (= (Nat.beq (:id q) (:of k)) false))
  (rw [qi beq-comm]) (exact hn)
  (simp only [h3-cs comp-react-row ne Bool.not_false Bool.true_or])
  (intros q hq eq) (exact hq))

;; Direct per-run transfer keeps every exemption intact. The completion
;; obligation is transported only for the matching activation's owner.
(a/theorem h3-react-r [xm :- (List Nat), w :- World, c :- CompRow, b :- ActRow, r :- RunRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) true) (= (g7 w) true) (= (aha w) true)
      (= (h3 xm w) true) (List.Mem b (:acts w)) (List.Mem r (:runs w))
      (= (h3-rr xm (comp-upd w (:id c) comp-react-row) b r) true))
  (intros mc hi hg ha h mb mr)
  (have hs := (h3-sample xm w h))
  (have hb := (tbl-all-mem ActRow _ b _ (h3-rest-of xm w h) mb))
  (simp only [h3-a Bool.and_eq_true] at hb)
  (have hr := (tbl-all-mem RunRow _ r _ (And.right hb) mr))
  (simp only [h3-rr] at hr) (simp only [h3-rr])
  (cases hid (Nat.beq (:id (rk3 r)) (:run b)))
  (case [false] (simp only [h3-r hid Bool.not_false Bool.true_or]))
  (case [true]
    (have ir (= (:id r) (:run b))) (exact (Nat.eq_of_beq_eq_true hid))
    (have off := (h3-react-act-off w c b r mc hi hg ha mb mr ir))
    (simp only [h3-r hid Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
    (simp only [h3-r hid Bool.not_true Bool.false_or Bool.and_eq_true])
    (apply And.intro) (exact (And.left hr))
    (apply And.intro)
    (exact (h3-e1-upd (rk3 r) (:id c) comp-react-row comp-react-row-id
             (fn [q :- CompRow] (Nat.le_refl (:epoch q))) (:comps w) (And.left (And.right hr))))
    (have ob := (And.right (And.right hr)))
    (simp only [h3-ob Bool.or_eq_true Bool.and_eq_true] at ob)
    (simp only [h3-ob Bool.or_eq_true Bool.and_eq_true])
    (cases hx (reach-mem (:of (rk3 r)) xm))
    (case [true] (exact (Or.inl (rfl))))
    (case [false]
      (apply Or.inr)
      (cases hc (tbl-any (h3-cur (rk3 r)) (:comps (comp-upd w (:id c) comp-react-row))))
      (case [false] (exact (Or.inl (rfl))))
      (case [true]
        (apply Or.inr)
        (have cw := (h3-c3-upd w (:id c) comp-react-row comp-react-row-id
                     (fn [q :- CompRow] (Nat.le_refl (:epoch q))) (rk3 r) (gd-lt-of _ _ (And.left hr)) hc))
        (cases ob)
        (case [inl z] (rw [hx] at z) (cases z))
        (case [inr z]
          (cases z)
          (case [inl z1] (simp only [cw Bool.not_true] at z1) (cases z1))
          (case [inr z1]
            (apply And.intro) (exact (h3-react-cs-off w c (rk3 r) off (And.left z1)))
            (apply (tbl-all-mem-mono Nat (h3-x xm w b (rk3 r))
                     (h3-x xm (comp-upd w (:id c) comp-react-row) b (rk3 r)) (act-contrib b) _ (And.right z1)))
            (intros x mx px)
            (have nf (=> (= (reach-mem x xm) false) (= (h3-free xm w x) true) False))
            (intros hxx fr)
            (exact (h3-free-use xm w x b r fr mb mr ir hx cw (Iff.mpr (reach-mem-iff x (act-contrib b)) mx) hxx))
            (exact (h3-x-rel xm w (comp-upd w (:id c) comp-react-row) b (rk3 r) x
                     (h3-db-of w hs) (h3-c1-upd w (:id c) comp-react-row comp-react-row-id)
                     (fn [y :- Nat, hy :- (< y (:next-id w)), hyx :- (= (reach-mem y xm) false), py :- (= (tbl-all (hk-wif y) (:comps w)) true)]
                       (h3-react-wif w c y hs mc hi py))
                     (fn [y :- Nat, hy :- (< y (:next-id w)), py :- (= (tbl-all (h3-tk (:runs w) y) (:tasks w)) true)] py)
                     (rfl) (h3-hef-all xm w (:edges w) (fn [y :- Nat, py :- (= (tbl-has edge-id y (:edges w)) true)] py))
                     (h3-heb-of xm w (:edges w) (h3-heb-refl (:edges w)))
                     nf px))))))))

(a/theorem h3-comp-react [xm :- (List Nat), w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) true) (= (g7 w) true) (= (aha w) true)
      (= (h3 xm w) true) (= (h3 xm (comp-upd w (:id c) comp-react-row)) true))
  (intros mc hi hg ha h)
  (apply (h3-intro xm _ (inv-comp-upd w (:id c) comp-react-row comp-react-row-id comp-react-row-pending (h3-sample xm w h))))
  (simp only [h3-rest comp-upd set-comps])
  (apply all-of-mem) (intros b mb)
  (have hb := (tbl-all-mem ActRow _ b _ (h3-rest-of xm w h) mb))
  (simp only [h3-a Bool.and_eq_true] at hb)
  (simp only [h3-a Bool.and_eq_true])
  (apply And.intro) (exact (And.left hb))
  (apply all-of-mem) (intros r mr)
  (exact (h3-react-r xm w c b r mc hi hg ha h mb mr)))

;; Generate every frame in load order, including rank-only computation edits.
;; Fresh namespace loading must not depend on declarations from a prior REPL.
(lcopy! H3 'inv-insert-edge-checked)
(lcopy! H3 'inv-raise-for)
(lcopy! AHA 'inv-react-one)
(lcopy! G7 'inv-react-one)

(a/theorem h3-react-add [xm :- (List Nat), w :- World, c :- Nat, v :- Valid]
  (=> (= (h3 xm w) true) (= (h3 xm (react-add w c v)) true))
  (intro h)
  (cases hk (react-ok w c v))
  (case [false] (simp only [react-add hk]) (exact h))
  (case [true]
    (simp only [react-add hk])
    (exact (hm3-raise-for xm _ c (:debtor v) (hm3-insert-edge-checked xm w (valid-edge w c v) h)))))

(a/theorem h3-react-edges [xm :- (List Nat), vs :- (List Valid)]
  (forall [w :- World, c :- Nat]
    (=> (= (h3 xm w) true) (= (h3 xm (react-edges w c vs)) true)))
  (induction vs)
  (case [nil] (intros w c h) (simp only [react-edges]) (exact h))
  (case [cons v t ih]
    (intros w c h) (simp only [react-edges])
    (exact (ih _ c (h3-react-add xm w c v h)))))

(a/theorem h3-react-one [xm :- (List Nat), w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) true) (= (g7 w) true) (= (aha w) true)
      (= (h3 xm w) true) (= (h3 xm (react-one w c)) true))
  (intros mc hi hg ha h) (simp only [react-one])
  (exact (h3-react-edges xm (:validity c) _ (:id c) (h3-comp-react xm w c mc hi hg ha h))))

(a/theorem h3-react-loop [xm :- (List Nat), fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)]
    (=> (= (g7 w) true) (= (aha w) true) (= (h3 xm w) true) (= (h3 xm (react-loop fuel w q)) true)))
  (induction fuel)
  (case [nil] (intros w q hg ha h) (simp only [react-loop]) (exact h))
  (case [cons z f ih]
    (intros w q hg ha h)
    (cases q)
    (case [nil] (simp only [react-loop]) (exact h))
    (case [cons x t]
      (cases hf (comp-find w x))
      (case [none] (simp only [react-loop hf]) (exact (ih w t hg ha h)))
      (case [some c]
        (cases hi (:idle c))
        (case [false] (simp only [react-loop hf hi]) (exact (ih w t hg ha h)))
        (case [true]
          (simp only [react-loop hf hi])
          (exact (ih _ _ (g7-react-one w c hg) (aha-react-one w c ha)
                   (h3-react-one xm w c (tbl-find-mem CompRow comp-id x c (:comps w) hf) hi hg ha h))))))))

(a/theorem p3la-aha [w :- World]
  (=> (= (p3la w) true) (= (aha w) true))
  (intro h)
  (have pb := (p3b-parts w (p3la-p3b w h)))
  (have rp := (ri-parts w (And.right (And.right (And.right (And.right pb))))))
  (exact (And.right (And.right (And.right rp)))))

(a/theorem h3-react-loop-p3la [xm :- (List Nat), fuel :- (List Nat), w :- World, q :- (List Nat)]
  (=> (= (p3la w) true) (= (h3 xm w) true) (= (h3 xm (react-loop fuel w q)) true))
  (intros hp h)
  (exact (h3-react-loop xm fuel w q (p3la-g7 w hp) (p3la-aha w hp) h)))
