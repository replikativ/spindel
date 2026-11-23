(ns ^:ansatz/lean spindel.v2.inv.members.await-prep
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
            [spindel.v2.inv.i10 :refer :all]
            [spindel.v2.inv.alive-runs :refer :all]
            [spindel.v2.inv.marks-step :refer :all]
            [spindel.v2.inv.marks :refer :all]
            [spindel.v2.inv.members.bundle :refer :all]
            [spindel.v2.inv.members.track-take :refer :all]
            [spindel.v2.inv.members.cascade :refer :all]
            [spindel.v2.inv.members.base :refer :all]
            [spindel.v2.inv.members.react :refer :all]))

;; H3's generic activation insertion is unavailable: its new obligation is below.

(a/theorem current-members-demand-reactive [xm :- (List Nat), w :- World, d :- Nat]
  (=> (= (i7-idle w) true) (= (act-runs-alive w) true) (= (current-members xm w) true)
      (= (current-members xm (demand-reactive w d)) true))
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
        (exact (current-members-comp-upd-m xm w d comp-demand-row comp-demand-row-id comp-demand-row-pending
                 comp-demand-row-h3ep comp-demand-row-hkm comp-demand-row-h3ds h)))
      (case [true]
        (simp only [demand-reactive hf hi hv])
        (exact (current-members-react-loop xm (react-fuel w) w _ hg ha h))))))

(a/theorem current-members-demand-fold [xm :- (List Nat), ds :- (List Nat)]
  (forall [w :- World]
    (=> (= (i7-idle w) true) (= (act-runs-alive w) true) (= (current-members xm w) true)
        (= (current-members xm (nat-fold demand-reactive w ds)) true)))
  (induction ds)
  (case [nil] (intros w hg ha h) (simp only [nat-fold]) (exact h))
  (case [cons d t ih]
    (intros w hg ha h) (simp only [nat-fold])
    (exact (ih _ (i7-idle-demand-reactive w d hg) (act-runs-alive-demand-reactive w d ha)
             (current-members-demand-reactive xm w d hg ha h)))))

;; Field/rest facts are used at the unbumped insertion. No well-formed claim
;; is made there. Only original-world G10R/GD and actual run membership are used.
(a/theorem current-members-await-empty-act [xm :- (List Nat), w :- World, r :- RunRow, b :- ActRow]
  (=> (= (i10-current w) true) (= (comp-facts w) true) (List.Mem r (:runs w)) (= (run-alive r) true)
      (= (:run b) (:id r)) (= (:members b) (List.nil Member))
      (= (current-members-a xm (act-ins (run-upd w (:id r) run-tick) b) b) true))
  (intros hg hd mr al br bm)
  (have hs := (comp-facts-well-formed w hd))
  (have g := (current-members-i10-current-run w r hg mr))
  (have hu (forall [c :- CompRow, c2 :- CompRow]
             (=> (List.Mem c (:comps (act-ins (run-upd w (:id r) run-tick) b)))
                 (List.Mem c2 (:comps (act-ins (run-upd w (:id r) run-tick) b)))
                 (= (:id c2) (:id c)) (= (:epoch c2) (:epoch c)))))
  (intros c c2 mc mc2 ci) (exact (And.left (comp-same w c c2 hs mc mc2 ci)))
  (have hcs (forall [c :- CompRow]
              (=> (List.Mem c (:comps (act-ins (run-upd w (:id r) run-tick) b)))
                  (= (:id c) (:of r)) (= (:epoch r) (:epoch c))
                  (= (Nat.blt (:done-epoch c) (:epoch c)) true))))
  (intros c mc ci ce) (exact (current-members-comp-facts-cs w r c hd mr al mc ci ce))
  (have hm (forall [y :- Nat]
             (=> (List.Mem y (act-contrib b))
                 (= (current-members-x xm (act-ins (run-upd w (:id r) run-tick) b) b (current-members-run-key r) y) true))))
  (intros y my) (simp only [act-contrib bm member-edges] at my) (cases my)
  (have hr := (current-members-r-new2 xm (act-ins (run-upd w (:id r) run-tick) b) b r (And.left g) (And.right g) hu hcs hm))
  (have rb := (runs-below w hs)) (rw [all-i10-current-run-keys] at rb)
  (have bound := (tbl-all-mem RunRow _ r (:runs w) rb mr))
  (simp only [id-lt i10-current-run-key] at bound)
  (simp only [current-members-a Bool.and_eq_true])
  (apply And.intro) (rw [br]) (exact bound)
  (have old (= (tbl-all (current-members-rr xm (act-ins (run-upd w (:id r) run-tick) b) b) (:runs w)) true))
  (apply all-of-mem) (intros q mq)
  (cases eq (Nat.beq (:id q) (:id r)))
  (case [false] (simp only [current-members-rr current-members-r current-members-run-key br eq Bool.not_false Bool.true_or]))
  (case [true] (rw [(current-members-run-uniq w r q hs mr mq eq)]) (exact hr))
  (apply (tbl-all-upd RunRow run-id (:id r) run-tick
           (current-members-rr xm (act-ins (run-upd w (:id r) run-tick) b) b)
           (current-members-rr xm (act-ins (run-upd w (:id r) run-tick) b) b) _ _ (:runs w) old))
  (intros q hq eq) (exact hq)
  (intros q hq eq) (exact hq))

(a/theorem current-members-await-allocate [xm :- (List Nat), w :- World, r :- RunRow, b :- ActRow]
  (=> (= (i10-current w) true) (= (comp-facts w) true) (= (i7-idle w) true) (= (act-runs-alive w) true) (= (current-members xm w) true)
      (List.Mem r (:runs w)) (= (run-alive r) true)
      (= (:id b) (:next-id w)) (= (:run b) (:id r)) (= (:members b) (List.nil Member))
      (And (= (current-members xm (bump (act-ins (run-upd w (:id r) run-tick) b))) true)
       (And (= (i7-idle (bump (act-ins (run-upd w (:id r) run-tick) b))) true)
            (= (act-runs-alive (bump (act-ins (run-upd w (:id r) run-tick) b))) true))))
  (intros hg hd h7 ha h mr al bi br bm)
  (have hs := (current-members-well-formed xm w h))
  (have h1 := (current-members-run-upd-m xm w (:id r) run-tick run-tick-run-id
                (fn [q :- RunRow] (Eq.refl (:of q))) (fn [q :- RunRow] (Eq.refl (:epoch q)))
                (fn [q :- RunRow, aq :- (= (run-alive q) true)] aq) h))
  (have g1 := (i7-idle-run-upd w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (i7-idle-run-key q))) h7))
  (have a1 := (act-runs-alive-run-upd w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (run-alive q))) ha))
  (have he (= (act-id b)
              (:next-id (run-upd w (:id r) run-tick)))) (exact bi)
  (have hy (forall [y :- Nat]
             (=> (= (mem-has y (:members b)) true)
                 (Or (= (reach-mem y xm) true) (= (tbl-has edge-id y (:edges w)) false)))))
  (intros y my) (simp only [bm mem-has] at my) (cases my)
  (have rest := (current-members-rest-act-ins xm (run-upd w (:id r) run-tick) b hy
                  (current-members-await-empty-act xm w r b hg hd mr al br bm) (current-members-rest-of xm _ h1)))
  (have hb := (current-members-intro xm _ (well-formed-act-ins-fresh (run-upd w (:id r) run-tick) b he (current-members-well-formed xm _ h1))
                (current-members-rest-bump xm (act-ins (run-upd w (:id r) run-tick) b) (current-members-db-of w hs) rest)))
  (have gb := (i7-idle-act-ins-fresh (run-upd w (:id r) run-tick) b he g1))
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
  (have ab := (act-runs-alive-act-ins-fresh (run-upd w (:id r) run-tick) b he ob bh a1))
  (exact (And.intro hb (And.intro gb ab))))

(a/theorem current-members-await-pre [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (i10-current w) true) (= (comp-facts w) true) (= (i7-idle w) true) (= (act-runs-alive w) true) (= (current-members xm w) true)
      (List.Mem r (:runs w)) (= (run-alive r) true)
      (= (current-members xm (await-pre w r ds mode k mine)) true))
  (intros hg hd h7 ha h mr al)
  (have base := (current-members-await-allocate xm w r
                  (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine)
                  hg hd h7 ha h mr al (rfl) (rfl) (rfl)))
  (simp only [await-pre])
  (exact (current-members-demand-fold xm (nat-distinct ds) _ (And.left (And.right base)) (And.right (And.right base)) (And.left base))))

(a/theorem chain-to-edge-kinds-i10-current [w :- World]
  (=> (= (chain-to-edge-kinds w) true) (= (i10-current w) true))
  (intro h) (exact (And.right (chain-to-i8-closed-ctx w (chain-to-edge-kinds-implies-chain-to-i8-closed w h)))))
(a/theorem chain-to-edge-kinds-comp-facts [w :- World]
  (=> (= (chain-to-edge-kinds w) true) (= (comp-facts w) true))
  (intro h)
  (have pl := (chain-to-marks-waiting-parts w (chain-to-edge-kinds-prev w h)))
  (have pk := (chain-to-i14-ordered-parts w (And.left pl)))
  (exact (And.right (chain-to-comp-facts-parts w (And.left pk)))))
(a/theorem chain-to-edge-kinds-marks-waiting [w :- World]
  (=> (= (chain-to-edge-kinds w) true) (= (marks-waiting (List.nil Nat) w) true))
  (intro h) (exact (And.right (chain-to-marks-waiting-parts w (chain-to-edge-kinds-prev w h)))))

(a/theorem current-members-await-pre-chain-to-edge-kinds [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (chain-to-edge-kinds w) true) (= (current-members xm w) true) (List.Mem r (:runs w)) (= (run-alive r) true)
      (= (current-members xm (await-pre w r ds mode k mine)) true))
  (intros hp h mr al)
  (exact (current-members-await-pre xm w r ds mode k mine (chain-to-edge-kinds-i10-current w hp) (chain-to-edge-kinds-comp-facts w hp)
           (chain-to-edge-kinds-i7-idle w hp) (chain-to-edge-kinds-act-runs-alive w hp) h mr al)))

(a/theorem current-members-await-pre-token [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat]
  (=> (= (chain-to-edge-kinds w) true) (= (current-members xm w) true) (= (tok-run w st) (Option.some RunRow r))
      (= (await-ok w r ds mode fresh) true) (= (current-members xm (await-pre w r ds mode k mine)) true))
  (intros hp h ht hok)
  (have mr := (And.left (tok-facts w st r ht)))
  (simp only [await-ok Bool.and_eq_true] at hok)
  (have al := (normal-alive r (And.left (And.right hok))))
  (exact (current-members-await-pre-chain-to-edge-kinds xm w r ds mode k mine hp h mr al)))

(a/theorem i7-idle-await-pre-chain-to-edge-kinds [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (chain-to-edge-kinds w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (i7-idle (await-pre w r ds mode k mine)) true))
  (intros hp mr al) (exact (i7-idle-await-pre w r ds mode k mine (chain-to-edge-kinds-i7-idle w hp))))

(a/theorem act-runs-alive-await-pre-chain-to-edge-kinds [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (chain-to-edge-kinds w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (act-runs-alive (await-pre w r ds mode k mine)) true))
  (intros hp mr al) (exact (act-runs-alive-await-pre w r ds mode k mine mr al (chain-to-edge-kinds-act-runs-alive w hp))))

(a/theorem comp-facts-await-pre-chain-to-edge-kinds [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (chain-to-edge-kinds w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (comp-facts (await-pre w r ds mode k mine)) true))
  (intros hp mr al) (exact (comp-facts-await-pre w r ds mode k mine (chain-to-edge-kinds-i7-idle w hp) (chain-to-edge-kinds-comp-facts w hp))))

(a/theorem alive-run-latest-await-pre-chain-to-edge-kinds [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (chain-to-edge-kinds w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (alive-run-latest (await-pre w r ds mode k mine)) true))
  (intros hp mr al) (exact (alive-run-latest-await-pre w r ds mode k mine (chain-to-edge-kinds-alive-run-latest w hp))))

(a/theorem marks-waiting-await-pre-chain-to-edge-kinds [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (chain-to-edge-kinds w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (marks-waiting (List.nil Nat) (await-pre w r ds mode k mine)) true))
  (intros hp mr al) (exact (marks-waiting-await-pre (List.nil Nat) w r ds mode k mine (chain-to-edge-kinds-marks-waiting w hp))))

(a/theorem edge-kinds-await-pre-chain-to-edge-kinds [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (chain-to-edge-kinds w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (edge-kinds (await-pre w r ds mode k mine)) true))
  (intros hp mr al) (exact (edge-kinds-await-pre w r ds mode k mine (chain-to-edge-kinds-edge-kinds w hp))))
