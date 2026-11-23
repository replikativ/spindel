(ns ^:ansatz/lean spindel.v2.inv.members.react
  "Bounded P11 reactivation preserves explicit H3 obligations. Arbitrary fuel
   proves safety of the returned world, without a queue-completion claim."
  (:require [ansatz.core :as a]
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
            [spindel.v2.inv.comp-facts :refer :all]
            [spindel.v2.inv.marks :refer :all]
            [spindel.v2.inv.members.bundle :refer :all]
            [spindel.v2.inv.members.track-take :refer :all]
            [spindel.v2.inv.members.cascade :refer :all]
            [spindel.v2.inv.members.base :refer :all]))

;; Only a matching activation run is known alive. G7 then excludes the actual
;; idle computation as its owner; arbitrary run rows need not be alive.
(a/theorem current-members-react-act-off [w :- World, c :- CompRow, b :- ActRow, r :- RunRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) true)
      (= (i7-idle w) true) (= (act-runs-alive w) true)
      (List.Mem b (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run b))
      (= (Nat.beq (:of r) (:id c)) false))
  (intros mc hi hg ha mb mr ir)
  (have al := (act-runs-alive-acts-alive w ha))
  (simp only [acts-alive] at al)
  (have ar := (tbl-all-mem RunRow _ r _ (tbl-all-mem ActRow _ b _ al mb) mr))
  (simp only [act-run-ok run-ok-for ir Nat.beq_refl Bool.not_true Bool.false_or] at ar)
  (have gp := (i7-idle-keys-ok-parts _ _ _ (i7-idle-rest-of w hg)))
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
(a/theorem current-members-react-wif [w :- World, c :- CompRow, y :- Nat]
  (=> (= (well-formed w) true) (List.Mem c (:comps w)) (= (:idle c) true)
      (= (tbl-all (hk-wif y) (:comps w)) true)
      (= (tbl-all (hk-wif y) (:comps (comp-upd w (:id c) comp-react-row))) true))
  (intros hs mc hi h)
  (have u := (uniq-all CompRow comp-id (fn [q :- CompRow] (:idle q)) c (:comps w) (comps-nodup w hs) mc hi))
  (simp only [comp-upd set-comps])
  (apply (all-upd2 CompRow comp-id (:id c) comp-react-row (hk-wif y)
           (same-id-then comp-id (:id c) (fn [q :- CompRow] (:idle q))) (hk-wif y) _ _ (:comps w) h u))
  (intros q hq uq eq)
  (simp only [same-id-then eq Bool.not_true Bool.false_or] at uq)
  (simp only [hk-wif waiting-strongly uq Bool.not_true Bool.false_and Bool.or_false] at hq)
  (simp only [hk-wif comp-react-row hq Bool.true_or])
  (intros q hq uq eq) (exact hq))

(a/theorem current-members-react-cs-off [w :- World, c :- CompRow, k :- CurrentMembersRunKey]
  (=> (= (Nat.beq (:of k) (:id c)) false)
      (= (tbl-all (current-members-cs k) (:comps w)) true)
      (= (tbl-all (current-members-cs k) (:comps (comp-upd w (:id c) comp-react-row))) true))
  (intros hn h)
  (simp only [comp-upd set-comps])
  (apply (tbl-all-upd CompRow comp-id (:id c) comp-react-row (current-members-cs k) (current-members-cs k) _ _ (:comps w) h))
  (intros q hq eq)
  (have qi (= (:id q) (:id c))) (exact (Nat.eq_of_beq_eq_true eq))
  (have ne (= (Nat.beq (:id q) (:of k)) false))
  (rw [qi beq-comm]) (exact hn)
  (simp only [current-members-cs comp-react-row ne Bool.not_false Bool.true_or])
  (intros q hq eq) (exact hq))

;; Direct per-run transfer keeps every exemption intact. The completion
;; obligation is transported only for the matching activation's owner.
(a/theorem current-members-react-r [xm :- (List Nat), w :- World, c :- CompRow, b :- ActRow, r :- RunRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) true) (= (i7-idle w) true) (= (act-runs-alive w) true)
      (= (current-members xm w) true) (List.Mem b (:acts w)) (List.Mem r (:runs w))
      (= (current-members-rr xm (comp-upd w (:id c) comp-react-row) b r) true))
  (intros mc hi hg ha h mb mr)
  (have hs := (current-members-well-formed xm w h))
  (have hb := (tbl-all-mem ActRow _ b _ (current-members-rest-of xm w h) mb))
  (simp only [current-members-a Bool.and_eq_true] at hb)
  (have hr := (tbl-all-mem RunRow _ r _ (And.right hb) mr))
  (simp only [current-members-rr] at hr) (simp only [current-members-rr])
  (cases hid (Nat.beq (:id (current-members-run-key r)) (:run b)))
  (case [false] (simp only [current-members-r hid Bool.not_false Bool.true_or]))
  (case [true]
    (have ir (= (:id r) (:run b))) (exact (Nat.eq_of_beq_eq_true hid))
    (have off := (current-members-react-act-off w c b r mc hi hg ha mb mr ir))
    (simp only [current-members-r hid Bool.not_true Bool.false_or Bool.and_eq_true] at hr)
    (simp only [current-members-r hid Bool.not_true Bool.false_or Bool.and_eq_true])
    (apply And.intro) (exact (And.left hr))
    (apply And.intro)
    (exact (current-members-e1-upd (current-members-run-key r) (:id c) comp-react-row comp-react-row-id
             (fn [q :- CompRow] (Nat.le_refl (:epoch q))) (:comps w) (And.left (And.right hr))))
    (have ob := (And.right (And.right hr)))
    (simp only [current-members-ob Bool.or_eq_true Bool.and_eq_true] at ob)
    (simp only [current-members-ob Bool.or_eq_true Bool.and_eq_true])
    (cases hx (reach-mem (:of (current-members-run-key r)) xm))
    (case [true] (exact (Or.inl (rfl))))
    (case [false]
      (apply Or.inr)
      (cases hc (tbl-any (current-members-cur (current-members-run-key r)) (:comps (comp-upd w (:id c) comp-react-row))))
      (case [false] (exact (Or.inl (rfl))))
      (case [true]
        (apply Or.inr)
        (have cw := (current-members-c3-upd w (:id c) comp-react-row comp-react-row-id
                     (fn [q :- CompRow] (Nat.le_refl (:epoch q))) (current-members-run-key r) (comp-facts-lt-of _ _ (And.left hr)) hc))
        (cases ob)
        (case [inl z] (simp only [current-members-run-key] at hx) (rw [hx] at z) (cases z))
        (case [inr z]
          (cases z)
          (case [inl z1] (simp only [cw Bool.not_true] at z1) (cases z1))
          (case [inr z1]
            (apply And.intro) (exact (current-members-react-cs-off w c (current-members-run-key r) off (And.left z1)))
            (apply (tbl-all-mem-mono Nat (current-members-x xm w b (current-members-run-key r))
                     (current-members-x xm (comp-upd w (:id c) comp-react-row) b (current-members-run-key r)) (act-contrib b) _ (And.right z1)))
            (intros x mx px)
            (have nf (=> (= (reach-mem x xm) false) (= (current-members-free xm w x) true) False))
            (intros hxx fr)
            (exact (current-members-free-use xm w x b r fr mb mr ir hx cw (Iff.mpr (reach-mem-iff x (act-contrib b)) mx) hxx))
            (exact (current-members-x-rel xm w (comp-upd w (:id c) comp-react-row) b (current-members-run-key r) x
                     (current-members-db-of w hs) (current-members-c1-upd w (:id c) comp-react-row comp-react-row-id)
                     (fn [y :- Nat, hy :- (< y (:next-id w)), hyx :- (= (reach-mem y xm) false), py :- (= (tbl-all (hk-wif y) (:comps w)) true)]
                       (current-members-react-wif w c y hs mc hi py))
                     (fn [y :- Nat, hy :- (< y (:next-id w)), py :- (= (tbl-all (current-members-tk (:runs w) y) (:tasks w)) true)] py)
                     (rfl) (current-members-hef-all xm w (:edges w) (fn [y :- Nat, py :- (= (tbl-has edge-id y (:edges w)) true)] py))
                     (current-members-heb-of xm w (:edges w) (current-members-heb-refl (:edges w)))
                     nf px))))))))

(a/theorem current-members-comp-react [xm :- (List Nat), w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) true) (= (i7-idle w) true) (= (act-runs-alive w) true)
      (= (current-members xm w) true) (= (current-members xm (comp-upd w (:id c) comp-react-row)) true))
  (intros mc hi hg ha h)
  (apply (current-members-intro xm _ (well-formed-comp-upd w (:id c) comp-react-row comp-react-row-id comp-react-row-pending (current-members-well-formed xm w h))))
  (simp only [current-members-rest comp-upd set-comps])
  (apply all-of-mem) (intros b mb)
  (have hb := (tbl-all-mem ActRow _ b _ (current-members-rest-of xm w h) mb))
  (simp only [current-members-a Bool.and_eq_true] at hb)
  (simp only [current-members-a Bool.and_eq_true])
  (apply And.intro) (exact (And.left hb))
  (apply all-of-mem) (intros r mr)
  (exact (current-members-react-r xm w c b r mc hi hg ha h mb mr)))

(tree/restate! H3 '[well-formed-raise-for])

(a/theorem current-members-react-add [xm :- (List Nat), w :- World, c :- Nat, v :- Valid]
  (=> (= (current-members xm w) true) (= (current-members xm (react-add w c v)) true))
  (intro h)
  (cases hk (react-ok w c v))
  (case [false] (simp only [react-add hk]) (exact h))
  (case [true]
    (simp only [react-add hk])
    (exact (current-members-raise-for xm _ c (:debtor v) (current-members-insert-edge-checked xm w (valid-edge w c v) h)))))

(a/theorem current-members-react-edges [xm :- (List Nat), vs :- (List Valid)]
  (forall [w :- World, c :- Nat]
    (=> (= (current-members xm w) true) (= (current-members xm (react-edges w c vs)) true)))
  (induction vs)
  (case [nil] (intros w c h) (simp only [react-edges]) (exact h))
  (case [cons v t ih]
    (intros w c h) (simp only [react-edges])
    (exact (ih _ c (current-members-react-add xm w c v h)))))

(a/theorem current-members-react-one [xm :- (List Nat), w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) true) (= (i7-idle w) true) (= (act-runs-alive w) true)
      (= (current-members xm w) true) (= (current-members xm (react-one w c)) true))
  (intros mc hi hg ha h) (simp only [react-one])
  (exact (current-members-react-edges xm (:validity c) _ (:id c) (current-members-comp-react xm w c mc hi hg ha h))))

(a/theorem current-members-react-loop [xm :- (List Nat), fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)]
    (=> (= (i7-idle w) true) (= (act-runs-alive w) true) (= (current-members xm w) true) (= (current-members xm (react-loop fuel w q)) true)))
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
          (exact (ih _ _ (i7-idle-react-one w c hg) (act-runs-alive-react-one w c ha)
                   (current-members-react-one xm w c (tbl-find-mem CompRow comp-id x c (:comps w) hf) hi hg ha h))))))))

(a/theorem chain-to-edge-kinds-act-runs-alive [w :- World]
  (=> (= (chain-to-edge-kinds w) true) (= (act-runs-alive w) true))
  (intro h)
  (have pb := (chain-start-parts w (chain-to-edge-kinds-implies-chain-start w h)))
  (have rp := (round-facts-parts w (And.right (And.right (And.right (And.right pb))))))
  (exact (And.left (And.right (And.right (And.right rp))))))

(a/theorem current-members-react-loop-chain-to-edge-kinds [xm :- (List Nat), fuel :- (List Nat), w :- World, q :- (List Nat)]
  (=> (= (chain-to-edge-kinds w) true) (= (current-members xm w) true) (= (current-members xm (react-loop fuel w q)) true))
  (intros hp h)
  (exact (current-members-react-loop xm fuel w q (chain-to-edge-kinds-i7-idle w hp) (chain-to-edge-kinds-act-runs-alive w hp) h)))
