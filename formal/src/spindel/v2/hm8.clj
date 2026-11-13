(ns spindel.v2.hm8
  "Bounded await preparation preserves H3 and exports its reachable supports.
   Wiring, post-processing and full T6/P11 remain separate obligations."
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
            [spindel.v2.i10 :refer :all]
            [spindel.v2.ar :refer :all]
            [spindel.v2.hmk2 :refer :all]
            [spindel.v2.hmk :refer :all]
            [spindel.v2.hm3 :refer :all]
            [spindel.v2.hm5 :refer :all]
            [spindel.v2.hm6 :refer :all]
            [spindel.v2.hm6-base :refer :all]
            [spindel.v2.hm7 :refer :all]))

;; Materialize support closure at namespace load, before any caller. H3's
;; generic activation insertion remains unavailable: its new obligation is below.
(lcopy! G7 'inv-demand-reactive)
(lcopy! AHA 'inv-demand-reactive)
(lcopy! G7 'inv-await-pre)
(lcopy! AHA 'inv-await-pre)
(lcopy! GD 'inv-await-pre)
(lcopy! AR 'inv-await-pre)
(lcopy! HMK 'inv-await-pre)
(lcopy! EKB 'inv-await-pre)

(a/theorem h3-demand-reactive [xm :- (List Nat), w :- World, d :- Nat]
  (=> (= (g7 w) true) (= (aha w) true) (= (h3 xm w) true)
      (= (h3 xm (demand-reactive w d)) true))
  (intros hg ha h)
  (cases hf (comp-find w d))
  (case [none] (simp only [demand-reactive hf]) (exact h))
  (case [some c]
    (cases hi (:idle c))
    (case [false] (simp only [demand-reactive hf hi]) (exact h))
    (case [true]
      (cases hv (valid-idle w c))
      (case [false]
        (simp only [demand-reactive hf hi hv])
        (exact (h3-comp-upd-m xm w d comp-demand-row comp-demand-row-id comp-demand-row-pending
                 comp-demand-row-h3ep comp-demand-row-hkm comp-demand-row-h3ds h)))
      (case [true]
        (simp only [demand-reactive hf hi hv])
        (exact (h3-react-loop xm (react-fuel w) w _ hg ha h))))))

(a/theorem h3-demand-fold [xm :- (List Nat), ds :- (List Nat)]
  (forall [w :- World]
    (=> (= (g7 w) true) (= (aha w) true) (= (h3 xm w) true)
        (= (h3 xm (nat-fold demand-reactive w ds)) true)))
  (induction ds)
  (case [nil] (intros w hg ha h) (simp only [nat-fold]) (exact h))
  (case [cons d t ih]
    (intros w hg ha h) (simp only [nat-fold])
    (exact (ih _ (g7-demand-reactive w d hg) (aha-demand-reactive w d ha)
             (h3-demand-reactive xm w d hg ha h)))))

;; Field/rest facts are used at the unbumped insertion. No inv-sample claim
;; is made there. Only original-world G10R/GD and actual run membership are used.
(a/theorem h3-await-empty-act [xm :- (List Nat), w :- World, r :- RunRow, b :- ActRow]
  (=> (= (g10r w) true) (= (gd w) true) (List.Mem r (:runs w)) (= (run-alive r) true)
      (= (:run b) (:id r)) (= (:members b) (List.nil Member))
      (= (h3-a xm (act-ins (run-upd w (:id r) run-tick) b) b) true))
  (intros hg hd mr al br bm)
  (have hs := (gd-sample w hd))
  (have g := (h3-g10-run w r hg mr))
  (have hu (forall [c :- CompRow, c2 :- CompRow]
             (=> (List.Mem c (:comps (act-ins (run-upd w (:id r) run-tick) b)))
                 (List.Mem c2 (:comps (act-ins (run-upd w (:id r) run-tick) b)))
                 (= (:id c2) (:id c)) (= (:epoch c2) (:epoch c)))))
  (intros c c2 mc mc2 ci) (exact (And.left (comp-same w c c2 hs mc mc2 ci)))
  (have hcs (forall [c :- CompRow]
              (=> (List.Mem c (:comps (act-ins (run-upd w (:id r) run-tick) b)))
                  (= (:id c) (:of r)) (= (:epoch r) (:epoch c))
                  (= (Nat.blt (:done-epoch c) (:epoch c)) true))))
  (intros c mc ci ce) (exact (h3-gd-cs w r c hd mr al mc ci ce))
  (have hm (forall [y :- Nat]
             (=> (List.Mem y (act-contrib b))
                 (= (h3-x xm (act-ins (run-upd w (:id r) run-tick) b) b (rk3 r) y) true))))
  (intros y my) (simp only [act-contrib bm member-edges] at my) (cases my)
  (have hr := (h3-r-new2 xm (act-ins (run-upd w (:id r) run-tick) b) b r (And.left g) (And.right g) hu hcs hm))
  (have rb := (runs-below w hs)) (rw [all-rk10s] at rb)
  (have bound := (tbl-all-mem RunRow _ r (:runs w) rb mr))
  (simp only [id-lt rk10] at bound)
  (simp only [h3-a Bool.and_eq_true])
  (apply And.intro) (rw [br]) (exact bound)
  (have old (= (tbl-all (h3-rr xm (act-ins (run-upd w (:id r) run-tick) b) b) (:runs w)) true))
  (apply all-of-mem) (intros q mq)
  (cases eq (Nat.beq (:id q) (:id r)))
  (case [false] (simp only [h3-rr h3-r rk3 br eq Bool.not_false Bool.true_or]))
  (case [true] (rw [(h3-run-uniq w r q hs mr mq eq)]) (exact hr))
  (apply (tbl-all-upd RunRow run-id (:id r) run-tick
           (h3-rr xm (act-ins (run-upd w (:id r) run-tick) b) b)
           (h3-rr xm (act-ins (run-upd w (:id r) run-tick) b) b) _ _ (:runs w) old))
  (intros q hq eq) (exact hq)
  (intros q hq eq) (exact hq))

(a/theorem h3-await-allocate [xm :- (List Nat), w :- World, r :- RunRow, b :- ActRow]
  (=> (= (g10r w) true) (= (gd w) true) (= (g7 w) true) (= (aha w) true) (= (h3 xm w) true)
      (List.Mem r (:runs w)) (= (run-alive r) true)
      (= (:id b) (:next-id w)) (= (:run b) (:id r)) (= (:members b) (List.nil Member))
      (And (= (h3 xm (bump (act-ins (run-upd w (:id r) run-tick) b))) true)
       (And (= (g7 (bump (act-ins (run-upd w (:id r) run-tick) b))) true)
            (= (aha (bump (act-ins (run-upd w (:id r) run-tick) b))) true))))
  (intros hg hd h7 ha h mr al bi br bm)
  (have hs := (h3-sample xm w h))
  (have h1 := (h3-run-upd-m xm w (:id r) run-tick run-tick-run-id
                (fn [q :- RunRow] (Eq.refl (:of q))) (fn [q :- RunRow] (Eq.refl (:epoch q)))
                (fn [q :- RunRow, aq :- (= (run-alive q) true)] aq) h))
  (have g1 := (g7-run-upd w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (rk7 q))) h7))
  (have a1 := (aha-run-upd w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (run-alive q))) ha))
  (have he (= (act-id b)
              (:next-id (run-upd w (:id r) run-tick)))) (exact bi)
  (have hy (forall [y :- Nat]
             (=> (= (mem-has y (:members b)) true)
                 (Or (= (reach-mem y xm) true) (= (tbl-has edge-id y (:edges w)) false)))))
  (intros y my) (simp only [bm mem-has] at my) (cases my)
  (have rest := (h3r-act-ins xm (run-upd w (:id r) run-tick) b hy
                  (h3-await-empty-act xm w r b hg hd mr al br bm) (h3-rest-of xm _ h1)))
  (have hb := (h3-intro xm _ (inv-act-ins-fresh (run-upd w (:id r) run-tick) b he (h3-sample xm _ h1))
                (h3r-bump xm (act-ins (run-upd w (:id r) run-tick) b) (h3-db-of w hs) rest)))
  (have gb := (g7-act-ins-fresh (run-upd w (:id r) run-tick) b he g1))
  (have o0 := (run-ok-of-mem w r hs mr al))
  (have o1 (= (tbl-all (run-ok-for (:id r)) (:runs (run-upd w (:id r) run-tick))) true))
  (apply (tbl-all-upd RunRow run-id (:id r) run-tick (run-ok-for (:id r)) (run-ok-for (:id r)) _ _ (:runs w) o0))
  (intros q hq eq) (exact hq)
  (intros q hq eq) (exact hq)
  (have hh (= (tbl-has run-id (:id r) (:runs (run-upd w (:id r) run-tick))) true))
  (simp only [run-upd set-runs (tbl-has-upd RunRow run-id (:id r) (:id r) run-tick run-tick-run-id (:runs w))])
  (exact (tbl-find-has-mem w r mr))
  (have ob (= (tbl-all (run-ok-for (:run b)) (:runs (run-upd w (:id r) run-tick))) true))
  (rw [br]) (exact o1)
  (have bh (= (tbl-has run-id (:run b) (:runs (run-upd w (:id r) run-tick))) true))
  (rw [br]) (exact hh)
  (have ab := (aha-act-ins-fresh (run-upd w (:id r) run-tick) b he ob bh a1))
  (exact (And.intro hb (And.intro gb ab))))

(a/theorem h3-await-pre [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (g10r w) true) (= (gd w) true) (= (g7 w) true) (= (aha w) true) (= (h3 xm w) true)
      (List.Mem r (:runs w)) (= (run-alive r) true)
      (= (h3 xm (await-pre w r ds mode k mine)) true))
  (intros hg hd h7 ha h mr al)
  (have base := (h3-await-allocate xm w r
                  (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine)
                  hg hd h7 ha h mr al (rfl) (rfl) (rfl)))
  (simp only [await-pre])
  (exact (h3-demand-fold xm (nat-distinct ds) _ (And.left (And.right base)) (And.right (And.right base)) (And.left base))))

(a/theorem p3la-g10r [w :- World]
  (=> (= (p3la w) true) (= (g10r w) true))
  (intro h) (exact (And.right (p3i-ctx w (p3la-p3i w h)))))
(a/theorem p3la-gd [w :- World]
  (=> (= (p3la w) true) (= (gd w) true))
  (intro h)
  (have pl := (p3l-parts w (p3la-p3l w h)))
  (have pk := (p3k-parts w (And.left pl)))
  (exact (And.right (p3j-parts w (And.left pk)))))
(a/theorem p3la-hmk [w :- World]
  (=> (= (p3la w) true) (= (hmk (List.nil Nat) w) true))
  (intro h) (exact (And.right (p3l-parts w (p3la-p3l w h)))))

(a/theorem h3-await-pre-p3la [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (p3la w) true) (= (h3 xm w) true) (List.Mem r (:runs w)) (= (run-alive r) true)
      (= (h3 xm (await-pre w r ds mode k mine)) true))
  (intros hp h mr al)
  (exact (h3-await-pre xm w r ds mode k mine (p3la-g10r w hp) (p3la-gd w hp)
           (p3la-g7 w hp) (p3la-aha w hp) h mr al)))

(a/theorem h3-await-pre-token [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat]
  (=> (= (p3la w) true) (= (h3 xm w) true) (= (tok-run w st) (Option.some RunRow r))
      (= (await-ok w r ds mode fresh) true) (= (h3 xm (await-pre w r ds mode k mine)) true))
  (intros hp h ht hok)
  (have mr := (And.left (tok-facts w st r ht)))
  (simp only [await-ok Bool.and_eq_true] at hok)
  (have al := (normal-alive r (And.left (And.right hok))))
  (exact (h3-await-pre-p3la xm w r ds mode k mine hp h mr al)))

(a/theorem g7-await-pre-p3la [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (p3la w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (g7 (await-pre w r ds mode k mine)) true))
  (intros hp mr al) (exact (g7-await-pre w r ds mode k mine (p3la-g7 w hp))))

(a/theorem aha-await-pre-p3la [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (p3la w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (aha (await-pre w r ds mode k mine)) true))
  (intros hp mr al) (exact (aha-await-pre w r ds mode k mine mr al (p3la-aha w hp))))

(a/theorem gd-await-pre-p3la [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (p3la w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (gd (await-pre w r ds mode k mine)) true))
  (intros hp mr al) (exact (gd-await-pre w r ds mode k mine (p3la-g7 w hp) (p3la-gd w hp))))

(a/theorem ar-await-pre-p3la [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (p3la w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (ar (await-pre w r ds mode k mine)) true))
  (intros hp mr al) (exact (ar-await-pre w r ds mode k mine (p3la-ar w hp))))

(a/theorem hmk-await-pre-p3la [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (p3la w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (hmk (List.nil Nat) (await-pre w r ds mode k mine)) true))
  (intros hp mr al) (exact (hmk-await-pre (List.nil Nat) w r ds mode k mine (p3la-hmk w hp))))

(a/theorem ekb-await-pre-p3la [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (p3la w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (ekb (await-pre w r ds mode k mine)) true))
  (intros hp mr al) (exact (ekb-await-pre w r ds mode k mine (p3la-ekb w hp))))
