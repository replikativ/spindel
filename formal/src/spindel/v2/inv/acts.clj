(ns spindel.v2.inv.acts
  "The activation invariant behind P2/P4, preserved by every step, kernel-checked (Init only).

  `acts-parked w` = well-formed w and, for every activation A: every run row with id A.run is parked and
  holds no slice (`act-rows-good`), A.run < next-id (`act-below`), and A is its run's only
  activation (`act-sole`). It implies spindel.v2.progress.casc's `acts-alive` (`acts-parked-acts-alive`).

    step-acts            acts-parked w, rule-r-safe raw -> acts-parked (world-step w it)   (hypotheses of step-well-formed)
    acts-parked-empty             acts-parked empty-world
    raw-acts-alive       acts-parked w -> acts-alive (raw world)
    step-normalized-acts-parked   accepted, acts-parked w, rule-r-safe raw -> normalized (world-step w it)   (P2)
    step-i4-acts-parked           ... every non-done run of the step's world is live (I4)
    cascade-done-acts-parked         acts-parked w -> cascade-done w js                                            (P4)

  How: `acts-ok-with P w` is the invariant generic in the per-activation run predicate; `acts-parked` uses
  `act-rows-good`, `acts-parked-exempt ex` (inside T6/take, between the new activation and the park) exempts
  the activations of run (:x ex), which all have id (:a ex). Primitive edits (Part B, `prims!`);
  every composite well-formed lemma of `step-well-formed` is restated for the bundle from the generic step
  tree (spindel.v2.pres.tree; for acts-parked-exempt the 21 that T6 and take use). Own proofs (Part D, the tables'
  `:over`): resume and its callers (the resumed activation is its run's only one), T14's local
  part (the run's activations go with it), T12, the scheduling choice, finalize and finally regions
  (the run is not parked or holds the slice, so no activation names it: `no-act-bad`), T6 and take
  (`acts-parked-exempt-act-ins` ... `acts-parked-exempt-park`/`acts-parked-exempt-restore`)."
  (:require [ansatz.core :as a]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.progress.casc :refer :all]
            [spindel.v2.pres.part :refer [mk-bundle prim! inst]]
            [spindel.v2.pres.tree :as tree]))

;; ===========================================================================
;; Part A. The invariant
;; ===========================================================================

;; a run with an activation is parked and holds no slice
(a/defn good-row [r :- RunRow] Bool (Bool.and (Nat.beq (:act r) act-parked) (Bool.not (:slice r))))
(a/defn good-for [x :- Nat, r :- RunRow] Bool (Bool.or (Bool.not (Nat.beq (:id r) x)) (good-row r)))
(a/defn act-rows-good [rs :- (List RunRow), a :- ActRow] Bool (tbl-all (good-for (:run a)) rs))
;; an activation's run id is below the allocator (a run created later is never its run)
(a/defn act-below [n :- Nat, a :- ActRow] Bool (Nat.blt (:run a) n))
;; at most one activation per run
(a/defn same-run-id [a :- ActRow, b :- ActRow] Bool
  (Bool.or (Bool.not (Nat.beq (:run b) (:run a))) (Nat.beq (:id b) (:id a))))
(a/defn act-sole [as :- (List ActRow), a :- ActRow] Bool (tbl-all (same-run-id a) as))

(a/defn acts-ok-with [P :- (=> (List RunRow) ActRow Bool), w :- World] Bool
  (Bool.and (tbl-all (act-below (:next-id w)) (:acts w))
   (Bool.and (tbl-all (P (:runs w)) (:acts w)) (tbl-all (act-sole (:acts w)) (:acts w)))))
(a/defn acts-parked-rest [w :- World] Bool (acts-ok-with act-rows-good w))
(a/defn acts-parked [w :- World] Bool (Bool.and (well-formed w) (acts-parked-rest w)))

;; inside T6: the activations of run x (all with id a) are exempt from good rows
(a/structure Ex [] (x Nat) (a Nat))
(a/defn act-rows-good-x [e :- Ex, rs :- (List RunRow), c :- ActRow] Bool
  (if (Nat.beq (:run c) (:x e)) (Nat.beq (:id c) (:a e)) (act-rows-good rs c)))
(a/defn acts-parked-exempt-rest [e :- Ex, w :- World] Bool (acts-ok-with (act-rows-good-x e) w))
(a/defn acts-parked-exempt [e :- Ex, w :- World] Bool (Bool.and (well-formed w) (acts-parked-exempt-rest e w)))

(a/theorem acts-parked-well-formed [w :- World] (=> (= (acts-parked w) true) (= (well-formed w) true))
  (intro h) (simp only [acts-parked Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem acts-parked-rest-of [w :- World] (=> (= (acts-parked w) true) (= (acts-parked-rest w) true))
  (intro h) (simp only [acts-parked Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem acts-parked-intro [w :- World] (=> (= (well-formed w) true) (= (acts-parked-rest w) true) (= (acts-parked w) true))
  (intros h1 h2) (simp only [acts-parked h1 h2 Bool.and_self]))
(a/theorem acts-parked-parts [w :- World]
  (=> (= (acts-parked w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (acts-parked-well-formed w h))))
(a/theorem acts-parked-exempt-well-formed [e :- Ex, w :- World] (=> (= (acts-parked-exempt e w) true) (= (well-formed w) true))
  (intro h) (simp only [acts-parked-exempt Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem acts-parked-exempt-rest-of [e :- Ex, w :- World] (=> (= (acts-parked-exempt e w) true) (= (acts-parked-exempt-rest e w) true))
  (intro h) (simp only [acts-parked-exempt Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem acts-parked-exempt-intro [e :- Ex, w :- World] (=> (= (well-formed w) true) (= (acts-parked-exempt-rest e w) true) (= (acts-parked-exempt e w) true))
  (intros h1 h2) (simp only [acts-parked-exempt h1 h2 Bool.and_self]))
(a/theorem acts-parked-exempt-parts [e :- Ex, w :- World]
  (=> (= (acts-parked-exempt e w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (acts-parked-exempt-well-formed e w h))))

;; the invariant gives acts-alive (P2, P4)
(a/theorem good-for-alive [x :- Nat, r :- RunRow] (=> (= (good-for x r) true) (= (run-ok-for x r) true))
  (intro h)
  (cases hx (Nat.beq (:id r) x))
  (case [false] (simp [run-ok-for hx]))
  (case [true]
    (simp only [good-for hx Bool.not_true Bool.false_or good-row Bool.and_eq_true] at h)
    (have e (= (:act r) act-parked)) (exact (Nat.eq_of_beq_eq_true (And.left h)))
    (simp [run-ok-for run-alive e hx act-parked act-done])))

(a/theorem acts-parked-acts-alive [w :- World] (=> (= (acts-parked w) true) (= (acts-alive w) true))
  (intro h)
  (simp only [acts-parked acts-parked-rest acts-ok-with Bool.and_eq_true] at h)
  (simp only [acts-alive])
  (exact (tbl-all-mono ActRow (act-rows-good (:runs w)) (act-run-ok (:runs w))
           (fn [c :- ActRow, hc :- (= (act-rows-good (:runs w) c) true)]
             (tbl-all-mono RunRow (good-for (:run c)) (run-ok-for (:run c)) (good-for-alive (:run c)) (:runs w) hc))
           (:acts w) (And.left (And.right (And.right h))))))

;; ===========================================================================
;; Part B. The parts under the primitive edits
;; ===========================================================================

;; ---- run rows

(a/theorem arg-upd [x :- Nat, f :- (=> RunRow RunRow),
                    hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                    hg :- (forall [r :- RunRow] (= (good-row (f r)) (good-row r))), rs :- (List RunRow), c :- ActRow]
  (= (act-rows-good (tbl-upd run-id x f rs) c) (act-rows-good rs c))
  (have hy (forall [r :- RunRow] (= (good-for (:run c) (f r)) (good-for (:run c) r))))
  (intro r)
  (have e (= (:id (f r)) (:id r))) (exact (hid r))
  (simp only [good-for e (hg r)])
  (simp only [act-rows-good])
  (exact (tbl-all-upd-same RunRow run-id x f (good-for (:run c)) hy rs)))

(a/theorem arg-del [x :- Nat, rs :- (List RunRow), c :- ActRow]
  (=> (= (act-rows-good rs c) true) (= (act-rows-good (tbl-del run-id x rs) c) true))
  (intro h) (simp only [act-rows-good] at h) (simp only [act-rows-good])
  (exact (tbl-all-del RunRow run-id x (good-for (:run c)) (good-for (:run c))
           (fn [r :- RunRow, h1 :- (= (good-for (:run c) r) true), h2 :- (= (Nat.beq (run-id r) x) false)] h1) rs h)))

(a/theorem arg-keep [K :- (=> Nat Bool), rs :- (List RunRow), c :- ActRow]
  (=> (= (act-rows-good rs c) true) (= (act-rows-good (tbl-keep K run-id rs) c) true))
  (intro h) (simp only [act-rows-good] at h) (simp only [act-rows-good])
  (exact (tbl-all-keep-same RunRow K run-id (good-for (:run c)) rs h)))

;; a new run row whose id is above the activation's run
(a/theorem arg-ins [r :- RunRow, rs :- (List RunRow), c :- ActRow]
  (=> (= (Nat.beq (:id r) (:run c)) false) (= (act-rows-good rs c) true)
      (= (act-rows-good (tbl-ins r rs) c) true))
  (intros hne h) (simp only [act-rows-good] at h)
  (simp only [act-rows-good tbl-ins tbl-all good-for hne Bool.not_false Bool.true_or Bool.true_and])
  (exact h))

(a/theorem argx-upd [e :- Ex, x :- Nat, f :- (=> RunRow RunRow),
                     hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                     hg :- (forall [r :- RunRow] (= (good-row (f r)) (good-row r))), rs :- (List RunRow), c :- ActRow]
  (= (act-rows-good-x e (tbl-upd run-id x f rs) c) (act-rows-good-x e rs c))
  (simp only [act-rows-good-x (arg-upd x f hid hg rs c)]))

(a/theorem argx-mono [e :- Ex, rs :- (List RunRow), rs2 :- (List RunRow), c :- ActRow]
  (=> (=> (= (act-rows-good rs c) true) (= (act-rows-good rs2 c) true))
      (= (act-rows-good-x e rs c) true) (= (act-rows-good-x e rs2 c) true))
  (intros hm h)
  (cases hx (Nat.beq (:run c) (:x e)))
  (case [true] (simp only [act-rows-good-x hx] at h) (simp only [act-rows-good-x hx]) (exact h))
  (case [false] (simp only [act-rows-good-x hx] at h) (simp only [act-rows-good-x hx]) (exact (hm h))))

;; ---- activations: id- and run-preserving updates, removal

(a/theorem sole-upd [x :- Nat, f :- (=> ActRow ActRow),
                     hid :- (forall [c :- ActRow] (= (:id (f c)) (:id c))),
                     hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c))), as :- (List ActRow)]
  (= (tbl-all (act-sole (tbl-upd act-id x f as)) (tbl-upd act-id x f as)) (tbl-all (act-sole as) as))
  (have h1 (forall [c :- ActRow, b :- ActRow] (= (same-run-id c (f b)) (same-run-id c b))))
  (intros c b) (simp only [same-run-id (hid b) (hr b)])
  (have h2 (forall [c :- ActRow, b :- ActRow] (= (same-run-id (f c) b) (same-run-id c b))))
  (intros c b) (simp only [same-run-id (hid c) (hr c)])
  (have h3 (forall [c :- ActRow] (= (act-sole (tbl-upd act-id x f as) c) (act-sole as c))))
  (intro c) (simp only [act-sole]) (exact (tbl-all-upd-same ActRow act-id x f (same-run-id c) (h1 c) as))
  (have h4 (forall [c :- ActRow] (= (act-sole as (f c)) (act-sole as c))))
  (intro c) (simp only [act-sole]) (exact (tbl-all-congr ActRow _ _ (h2 c) as))
  (rw [(tbl-all-congr ActRow _ _ h3 (tbl-upd act-id x f as))])
  (exact (tbl-all-upd-same ActRow act-id x f (act-sole as) h4 as)))

(a/theorem sole-del [x :- Nat, as :- (List ActRow)]
  (=> (= (tbl-all (act-sole as) as) true) (= (tbl-all (act-sole (tbl-del act-id x as)) (tbl-del act-id x as)) true))
  (intro h)
  (have hin (forall [c :- ActRow] (=> (= (act-sole as c) true) (= (act-sole (tbl-del act-id x as) c) true))))
  (intros c hc) (simp only [act-sole] at hc) (simp only [act-sole])
  (exact (tbl-all-del ActRow act-id x (same-run-id c) (same-run-id c)
           (fn [b :- ActRow, h1 :- (= (same-run-id c b) true), h2 :- (= (Nat.beq (act-id b) x) false)] h1) as hc))
  (exact (tbl-all-del ActRow act-id x (act-sole as) (act-sole (tbl-del act-id x as))
           (fn [b :- ActRow, h1 :- (= (act-sole as b) true), h2 :- (= (Nat.beq (act-id b) x) false)] (hin b h1)) as h)))

(a/theorem sole-keep [K :- (=> Nat Bool), as :- (List ActRow)]
  (=> (= (tbl-all (act-sole as) as) true) (= (tbl-all (act-sole (tbl-keep K act-id as)) (tbl-keep K act-id as)) true))
  (intro h)
  (have hin (forall [c :- ActRow] (=> (= (act-sole as c) true) (= (act-sole (tbl-keep K act-id as) c) true))))
  (intros c hc) (simp only [act-sole] at hc) (simp only [act-sole])
  (exact (tbl-all-keep-same ActRow K act-id (same-run-id c) as hc))
  (exact (tbl-all-keep-same ActRow K act-id (act-sole (tbl-keep K act-id as)) as
           (tbl-all-mono ActRow (act-sole as) (act-sole (tbl-keep K act-id as)) hin as h))))

(a/theorem below-one [n :- Nat, m :- Nat, c :- ActRow]
  (=> (<= n m) (= (act-below n c) true) (= (act-below m c) true))
  (intros hn hc)
  (simp only [act-below Nat.blt_eq] at hc) (simp only [act-below Nat.blt_eq])
  (exact (Nat.lt_of_lt_of_le hc hn)))

(a/theorem below-mono [n :- Nat, m :- Nat, as :- (List ActRow)]
  (=> (<= n m) (= (tbl-all (act-below n) as) true) (= (tbl-all (act-below m) as) true))
  (intros hn h)
  (exact (tbl-all-mono ActRow (act-below n) (act-below m)
           (fn [c :- ActRow, hc :- (= (act-below n c) true)] (below-one n m c hn hc)) as h)))

;; ---- the parts, generic in the per-activation run predicate P

(a/theorem acts-ok-with-parts [P :- (=> (List RunRow) ActRow Bool), w :- World]
  (=> (= (acts-ok-with P w) true)
      (And (= (tbl-all (act-below (:next-id w)) (:acts w)) true)
           (And (= (tbl-all (P (:runs w)) (:acts w)) true) (= (tbl-all (act-sole (:acts w)) (:acts w)) true))))
  (intro h) (simp only [acts-ok-with Bool.and_eq_true] at h) (exact h))

(a/theorem acts-ok-with-mk [P :- (=> (List RunRow) ActRow Bool), w :- World]
  (=> (= (tbl-all (act-below (:next-id w)) (:acts w)) true) (= (tbl-all (P (:runs w)) (:acts w)) true)
      (= (tbl-all (act-sole (:acts w)) (:acts w)) true) (= (acts-ok-with P w) true))
  (intros h1 h2 h3) (simp only [acts-ok-with h1 h2 h3 Bool.and_self]))

(a/theorem acts-ok-with-bump [P :- (=> (List RunRow) ActRow Bool), w :- World]
  (=> (= (acts-ok-with P w) true) (= (acts-ok-with P (bump w)) true))
  (intro h)
  (have p := (acts-ok-with-parts P w h))
  (have hb (<= (:next-id w) (:next-id (bump w)))) (simp only [bump set-next-id]) (omega)
  (exact (acts-ok-with-mk P (bump w) (below-mono _ _ (:acts w) hb (And.left p)) (And.left (And.right p)) (And.right (And.right p)))))

(a/theorem acts-ok-with-run-upd [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hP :- (forall [rs :- (List RunRow), c :- ActRow] (= (P (tbl-upd run-id x f rs) c) (P rs c)))]
  (=> (= (acts-ok-with P w) true) (= (acts-ok-with P (run-upd w x f)) true))
  (intro h)
  (have p := (acts-ok-with-parts P w h))
  (have h2 (= (tbl-all (P (:runs (run-upd w x f))) (:acts (run-upd w x f))) true))
  (simp only [run-upd set-runs])
  (rw [(tbl-all-congr ActRow (P (tbl-upd run-id x f (:runs w))) (P (:runs w)) (hP (:runs w)) (:acts w))])
  (exact (And.left (And.right p)))
  (exact (acts-ok-with-mk P (run-upd w x f) (And.left p) h2 (And.right (And.right p)))))

(a/theorem acts-ok-with-run-del [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat,
                       hP :- (forall [rs :- (List RunRow), c :- ActRow] (=> (= (P rs c) true) (= (P (tbl-del run-id x rs) c) true)))]
  (=> (= (acts-ok-with P w) true) (= (acts-ok-with P (run-del w x)) true))
  (intro h)
  (have p := (acts-ok-with-parts P w h))
  (have h2 (= (tbl-all (P (:runs (run-del w x))) (:acts (run-del w x))) true))
  (simp only [run-del set-runs])
  (exact (tbl-all-mono ActRow (P (:runs w)) (P (tbl-del run-id x (:runs w))) (hP (:runs w)) (:acts w) (And.left (And.right p))))
  (exact (acts-ok-with-mk P (run-del w x) (And.left p) h2 (And.right (And.right p)))))

(a/theorem acts-ok-with-run-ins [P :- (=> (List RunRow) ActRow Bool), w :- World, r :- RunRow,
                       hP :- (forall [rs :- (List RunRow), c :- ActRow]
                               (=> (= (Nat.beq (:id r) (:run c)) false) (= (P rs c) true) (= (P (tbl-ins r rs) c) true)))]
  (=> (= (run-id r) (:next-id w)) (= (acts-ok-with P w) true) (= (acts-ok-with P (bump (run-ins w r))) true))
  (intros he h)
  (have p := (acts-ok-with-parts P w h))
  (have hin (forall [c :- ActRow] (=> (= (act-below (:next-id w) c) true) (= (P (:runs w) c) true)
                                      (= (P (tbl-ins r (:runs w)) c) true))))
  (intros c hc1 hc2)
  (simp only [act-below Nat.blt_eq] at hc1)
  (have hne (= (Nat.beq (:id r) (:run c)) false))
  (have e (= (:id r) (:next-id w))) (exact he)
  (rw [e]) (apply beq-false-of-ne) (omega)
  (exact (hP (:runs w) c hne hc2))
  (have h2 (= (tbl-all (P (:runs (run-ins w r))) (:acts (run-ins w r))) true))
  (simp only [run-ins set-runs])
  (exact (tbl-all-mono2 ActRow (act-below (:next-id w)) (P (:runs w)) (P (tbl-ins r (:runs w)))
           hin (:acts w) (And.left p) (And.left (And.right p))))
  (exact (acts-ok-with-bump P (run-ins w r) (acts-ok-with-mk P (run-ins w r) (And.left p) h2 (And.right (And.right p))))))

(a/theorem acts-ok-with-act-upd [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat, f :- (=> ActRow ActRow),
                       hid :- (forall [c :- ActRow] (= (:id (f c)) (:id c))),
                       hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c))),
                       hP :- (forall [rs :- (List RunRow), c :- ActRow] (= (P rs (f c)) (P rs c)))]
  (=> (= (acts-ok-with P w) true) (= (acts-ok-with P (act-upd w x f)) true))
  (intro h)
  (have p := (acts-ok-with-parts P w h))
  (have hb (forall [c :- ActRow] (= (act-below (:next-id w) (f c)) (act-below (:next-id w) c))))
  (intro c) (simp only [act-below (hr c)])
  (have h1 (= (tbl-all (act-below (:next-id (act-upd w x f))) (:acts (act-upd w x f))) true))
  (simp only [act-upd set-acts (tbl-all-upd-same ActRow act-id x f (act-below (:next-id w)) hb (:acts w))])
  (exact (And.left p))
  (have h2 (= (tbl-all (P (:runs (act-upd w x f))) (:acts (act-upd w x f))) true))
  (simp only [act-upd set-acts (tbl-all-upd-same ActRow act-id x f (P (:runs w)) (hP (:runs w)) (:acts w))])
  (exact (And.left (And.right p)))
  (have h3 (= (tbl-all (act-sole (:acts (act-upd w x f))) (:acts (act-upd w x f))) true))
  (simp only [act-upd set-acts (sole-upd x f hid hr (:acts w))])
  (exact (And.right (And.right p)))
  (exact (acts-ok-with-mk P (act-upd w x f) h1 h2 h3)))

(a/theorem acts-ok-with-act-del [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat]
  (=> (= (acts-ok-with P w) true) (= (acts-ok-with P (act-del w x)) true))
  (intro h)
  (have p := (acts-ok-with-parts P w h))
  (have h1 (= (tbl-all (act-below (:next-id (act-del w x))) (:acts (act-del w x))) true))
  (simp only [act-del set-acts])
  (exact (tbl-all-del ActRow act-id x (act-below (:next-id w)) (act-below (:next-id w))
           (fn [c :- ActRow, h1 :- (= (act-below (:next-id w) c) true), h2 :- (= (Nat.beq (act-id c) x) false)] h1)
           (:acts w) (And.left p)))
  (have h2 (= (tbl-all (P (:runs (act-del w x))) (:acts (act-del w x))) true))
  (simp only [act-del set-acts])
  (exact (tbl-all-del ActRow act-id x (P (:runs w)) (P (:runs w))
           (fn [c :- ActRow, h1 :- (= (P (:runs w) c) true), h2 :- (= (Nat.beq (act-id c) x) false)] h1)
           (:acts w) (And.left (And.right p))))
  (have h3 (= (tbl-all (act-sole (:acts (act-del w x))) (:acts (act-del w x))) true))
  (simp only [act-del set-acts]) (exact (sole-del x (:acts w) (And.right (And.right p))))
  (exact (acts-ok-with-mk P (act-del w x) h1 h2 h3)))

(a/theorem acts-ok-with-filter [P :- (=> (List RunRow) ActRow Bool), w :- World, K :- (=> Nat Bool),
                      hP :- (forall [rs :- (List RunRow), c :- ActRow] (=> (= (P rs c) true) (= (P (tbl-keep K run-id rs) c) true)))]
  (=> (= (acts-ok-with P w) true) (= (acts-ok-with P (filter-world K w)) true))
  (intro h)
  (have p := (acts-ok-with-parts P w h))
  (have h1 (= (tbl-all (act-below (:next-id (filter-world K w))) (:acts (filter-world K w))) true))
  (simp only [filter-world]) (exact (tbl-all-keep-same ActRow K act-id (act-below (:next-id w)) (:acts w) (And.left p)))
  (have h2 (= (tbl-all (P (:runs (filter-world K w))) (:acts (filter-world K w))) true))
  (simp only [filter-world])
  (exact (tbl-all-keep-same ActRow K act-id (P (tbl-keep K run-id (:runs w))) (:acts w)
           (tbl-all-mono ActRow (P (:runs w)) (P (tbl-keep K run-id (:runs w))) (hP (:runs w)) (:acts w) (And.left (And.right p)))))
  (have h3 (= (tbl-all (act-sole (:acts (filter-world K w))) (:acts (filter-world K w))) true))
  (simp only [filter-world]) (exact (sole-keep K (:acts w) (And.right (And.right p))))
  (exact (acts-ok-with-mk P (filter-world K w) h1 h2 h3)))

;; ---- instances: acts-parked-rest (P = act-rows-good) and acts-parked-exempt-rest (P = act-rows-good-x e)

(a/theorem argx-del [e :- Ex, x :- Nat, rs :- (List RunRow), c :- ActRow]
  (=> (= (act-rows-good-x e rs c) true) (= (act-rows-good-x e (tbl-del run-id x rs) c) true))
  (exact (argx-mono e rs (tbl-del run-id x rs) c (arg-del x rs c))))
(a/theorem argx-keep [e :- Ex, K :- (=> Nat Bool), rs :- (List RunRow), c :- ActRow]
  (=> (= (act-rows-good-x e rs c) true) (= (act-rows-good-x e (tbl-keep K run-id rs) c) true))
  (exact (argx-mono e rs (tbl-keep K run-id rs) c (arg-keep K rs c))))
(a/theorem argx-ins [e :- Ex, r :- RunRow, rs :- (List RunRow), c :- ActRow]
  (=> (= (Nat.beq (:id r) (:run c)) false) (= (act-rows-good-x e rs c) true) (= (act-rows-good-x e (tbl-ins r rs) c) true))
  (intro hne) (exact (argx-mono e rs (tbl-ins r rs) c (arg-ins r rs c hne))))
(a/theorem arg-act [rs :- (List RunRow), f :- (=> ActRow ActRow), hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c))), c :- ActRow]
  (= (act-rows-good rs (f c)) (act-rows-good rs c))
  (simp only [act-rows-good (hr c)]))
(a/theorem argx-act [e :- Ex, rs :- (List RunRow), f :- (=> ActRow ActRow),
                     hid :- (forall [c :- ActRow] (= (:id (f c)) (:id c))),
                     hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c))), c :- ActRow]
  (= (act-rows-good-x e rs (f c)) (act-rows-good-x e rs c))
  (simp only [act-rows-good-x act-rows-good (hr c) (hid c)]))

;; ===========================================================================
;; Part C. The two parts (`acts-parked` = the invariant, `acts-parked-exempt e` = the invariant inside T6 with run (:x e)
;; exempt), their cells and their tables in the generic tree
;; ===========================================================================

(defn- bsym [B suffix] (symbol (str (name (:pred B)) suffix)))

(def GA (mk-bundle 'acts-parked [] "acts-parked-"
          {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (good-row r))) 4]
           'well-formed-act-upd ['(fn [c :- ActRow] (Eq.refl (:run c))) 4]}))
(def GX (mk-bundle 'acts-parked-exempt '[ex :- Ex] "acts-parked-exempt-"
          {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (good-row r))) 4]
           'well-formed-act-upd ['(fn [c :- ActRow] (Eq.refl (:run c))) 4]}))

;; ---- the primitives

(a/theorem acts-ok-with-mark-edge [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat] (= (acts-ok-with P (mark-edge w x)) (acts-ok-with P w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem acts-ok-with-unmark-edge [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat] (= (acts-ok-with P (unmark-edge w x)) (acts-ok-with P w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem acts-ok-with-remove-edge [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat] (= (acts-ok-with P (remove-edge w x)) (acts-ok-with P w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))

(a/theorem acts-parked-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hg :- (forall [r :- RunRow] (= (good-row (f r)) (good-row r)))]
  (=> (= (acts-parked w) true) (= (acts-parked (run-upd w x f)) true))
  (intro h)
  (exact (acts-parked-intro _ (well-formed-run-upd w x f hf (acts-parked-well-formed w h))
           (acts-ok-with-run-upd act-rows-good w x f (arg-upd x f hf hg) (acts-parked-rest-of w h)))))
(a/theorem acts-parked-exempt-run-upd [e :- Ex, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hg :- (forall [r :- RunRow] (= (good-row (f r)) (good-row r)))]
  (=> (= (acts-parked-exempt e w) true) (= (acts-parked-exempt e (run-upd w x f)) true))
  (intro h)
  (exact (acts-parked-exempt-intro e _ (well-formed-run-upd w x f hf (acts-parked-exempt-well-formed e w h))
           (acts-ok-with-run-upd (act-rows-good-x e) w x f (argx-upd e x f hf hg) (acts-parked-exempt-rest-of e w h)))))

(a/theorem acts-parked-act-upd [w :- World, x :- Nat, f :- (=> ActRow ActRow),
                       hf :- (forall [r :- ActRow] (= (act-id (f r)) (act-id r))),
                       hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c)))]
  (=> (= (acts-parked w) true) (= (acts-parked (act-upd w x f)) true))
  (intro h)
  (exact (acts-parked-intro _ (well-formed-act-upd w x f hf (acts-parked-well-formed w h))
           (acts-ok-with-act-upd act-rows-good w x f hf hr (fn [rs :- (List RunRow), c :- ActRow] (arg-act rs f hr c)) (acts-parked-rest-of w h)))))
(a/theorem acts-parked-exempt-act-upd [e :- Ex, w :- World, x :- Nat, f :- (=> ActRow ActRow),
                       hf :- (forall [r :- ActRow] (= (act-id (f r)) (act-id r))),
                       hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c)))]
  (=> (= (acts-parked-exempt e w) true) (= (acts-parked-exempt e (act-upd w x f)) true))
  (intro h)
  (exact (acts-parked-exempt-intro e _ (well-formed-act-upd w x f hf (acts-parked-exempt-well-formed e w h))
           (acts-ok-with-act-upd (act-rows-good-x e) w x f hf hr (fn [rs :- (List RunRow), c :- ActRow] (argx-act e rs f hf hr c))
             (acts-parked-exempt-rest-of e w h)))))

(doseq [B [GA GX]]
  (swap! (:renames B) assoc 'well-formed-run-upd (bsym B "-run-upd") 'well-formed-act-upd (bsym B "-act-upd") 'well-formed-parts (bsym B "-parts")))

(defn- prims! [B P del-f keep-f ins-f]
  (doseq [o '[well-formed-scope-upd well-formed-pub-upd well-formed-source-upd well-formed-task-upd well-formed-resource-upd well-formed-cleanup-upd well-formed-cleanup-del
              well-formed-set-pins well-formed-resource-del well-formed-scope-del well-formed-cleanup-ins
              well-formed-edge-upd well-formed-drop-cred-edges well-formed-drop-edges well-formed-comp-del-unref well-formed-comp-upd well-formed-fork-del]]
    (prim! B o nil))
  (doseq [o '[well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-resource-ins-fresh well-formed-scope-ins-fresh well-formed-task-ins-fresh well-formed-comp-ins-fresh]]
    (prim! B o (list 'acts-ok-with-bump P (list (symbol (str/replace (subs (name o) 12) "-fresh" "")) 'w 'r)
                                     (list 'Eq.trans '(rfl) 'R))))
  (prim! B 'well-formed-bump (list 'acts-ok-with-bump P 'w 'R))
  (prim! B 'well-formed-mark-edge (list 'Eq.trans (list 'acts-ok-with-mark-edge P 'w 'x) 'R))
  (prim! B 'well-formed-unmark-edge (list 'Eq.trans (list 'acts-ok-with-unmark-edge P 'w 'x) 'R))
  (prim! B 'well-formed-remove-edge (list 'Eq.trans (list 'acts-ok-with-remove-edge P 'w 'x) 'R))
  (prim! B 'well-formed-insert-edge-fresh
         (list 'acts-ok-with-bump P '(insert-edge w (edge-set-id (:next-id w) e)) (list 'Eq.trans '(rfl) 'R)))
  (prim! B 'well-formed-run-del (list 'acts-ok-with-run-del P 'w 'x del-f 'R))
  (prim! B 'well-formed-run-ins-fresh (list 'acts-ok-with-run-ins P 'w 'r ins-f 'h0 'R))
  (prim! B 'well-formed-drop-act (list 'acts-ok-with-act-del P '(drop-cred-edges w a) 'a (list 'Eq.trans '(rfl) 'R)))
  (prim! B 'well-formed-filter-world (list 'acts-ok-with-filter P 'w 'K keep-f 'R)))

(prims! GA 'act-rows-good '(arg-del x) '(arg-keep K) '(arg-ins r))
(prims! GX '(act-rows-good-x ex) '(argx-del ex x) '(argx-keep ex K) '(argx-ins ex r))

;; acts-parked and acts-parked-exempt on the generic tree (spindel.v2.pres.tree): their own proofs are Part D
(tree/part! GA
  :over '{well-formed-resume acts-parked-resume
          well-formed-fill-slot acts-parked-fill-slot
          well-formed-fire-dep acts-parked-fire-dep
          well-formed-fire-wait-act acts-parked-fire-wait-act
          well-formed-cancel-run-local acts-parked-cancel-run-local
          well-formed-complete-raw acts-parked-complete-raw
          well-formed-t12-complete acts-parked-t12-complete
          well-formed-retire-pre acts-parked-retire-pre
          well-formed-retire-one acts-parked-retire-one
          well-formed-t-schedule acts-parked-t-schedule
          well-formed-t-finalize acts-parked-t-finalize
          well-formed-t-finally-enter acts-parked-t-finally-enter
          well-formed-t-finally-exit acts-parked-t-finally-exit
          well-formed-t-finally-leave acts-parked-t-finally-leave
          well-formed-t-slice-exit acts-parked-t-slice-exit
          well-formed-await-raw acts-parked-await-raw
          well-formed-t6-await acts-parked-t6-await
          well-formed-take-park acts-parked-take-park
          well-formed-t-take acts-parked-t-take
          well-formed-arm-park acts-parked-arm-park
          well-formed-t17-arm acts-parked-t17-arm})
(tree/part! GX
  :over '{well-formed-resume acts-parked-exempt-resume
          well-formed-fill-slot acts-parked-exempt-fill-slot
          well-formed-fire-dep acts-parked-exempt-fire-dep
          well-formed-fire-wait-act acts-parked-exempt-fire-wait-act})

;; ===========================================================================
;; Part D. The own proofs: where an edit changes a run row that has an activation
;; ===========================================================================

;; ---- a run row nobody's activation names may change freely

(a/theorem tbl-all-upd-on [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), p :- (=> A Bool),
                           hf :- (forall [r :- A] (=> (= (Nat.beq (idf r) x) true) (= (p (f r)) (p r)))), xs :- (List A)]
  (= (tbl-all p (tbl-upd idf x f xs)) (tbl-all p xs))
  (induction xs)
  (case [nil] (simp [tbl-all tbl-upd]))
  (case [cons h t ih]
    (cases hx (Nat.beq (idf h) x))
    (case [false] (simp only [tbl-upd hx tbl-all ih]))
    (case [true] (simp only [tbl-upd hx tbl-all ih (hf h hx)]))))

(a/theorem arg-upd-free [x :- Nat, f :- (=> RunRow RunRow),
                         hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))), rs :- (List RunRow), c :- ActRow]
  (=> (= (act-of-run x c) false) (= (act-rows-good (tbl-upd run-id x f rs) c) (act-rows-good rs c)))
  (intro hc)
  (have hy (forall [r :- RunRow] (=> (= (Nat.beq (run-id r) x) true) (= (good-for (:run c) (f r)) (good-for (:run c) r)))))
  (intros r h2)
  (have e1 (= (:id (f r)) x)) (exact (Eq.trans (hid r) (Nat.eq_of_beq_eq_true h2)))
  (have e2 (= (:id r) x)) (exact (Nat.eq_of_beq_eq_true h2))
  (have h3 (= (Nat.beq x (:run c)) false)) (rw [beq-comm]) (exact hc)
  (simp only [good-for e1 e2 h3 Bool.not_false Bool.true_or])
  (simp only [act-rows-good])
  (exact (tbl-all-upd-on RunRow run-id x f (good-for (:run c)) hy rs)))

(a/theorem argx-upd-free [e :- Ex, x :- Nat, f :- (=> RunRow RunRow),
                          hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))), rs :- (List RunRow), c :- ActRow]
  (=> (= (act-of-run x c) false) (= (act-rows-good-x e (tbl-upd run-id x f rs) c) (act-rows-good-x e rs c)))
  (intro hc) (simp only [act-rows-good-x (arg-upd-free x f hid rs c hc)]))

(a/defn bnot-of [A :- Type :implicit, p :- (=> A Bool), c :- A] Bool (Bool.not (p c)))

(a/theorem any-false-all [A :- Type, p :- (=> A Bool), xs :- (List A)]
  (=> (= (tbl-any p xs) false) (= (tbl-all (bnot-of p) xs) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-all]))
  (case [cons h t ih]
    (intro hn)
    (simp only [tbl-any Bool.or_eq_false_iff] at hn)
    (simp only [tbl-all bnot-of (And.left hn) Bool.not_false Bool.true_and])
    (exact (ih (And.right hn)))))

(a/theorem acts-ok-with-run-upd-free [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                            hP :- (forall [rs :- (List RunRow), c :- ActRow]
                                    (=> (= (act-of-run x c) false) (= (P (tbl-upd run-id x f rs) c) (P rs c))))]
  (=> (= (tbl-any (act-of-run x) (:acts w)) false) (= (acts-ok-with P w) true) (= (acts-ok-with P (run-upd w x f)) true))
  (intros hn h)
  (have p := (acts-ok-with-parts P w h))
  (have hin (forall [c :- ActRow] (=> (= (bnot-of (act-of-run x) c) true) (= (P (:runs w) c) true)
                                      (= (P (tbl-upd run-id x f (:runs w)) c) true))))
  (intros c h1 h2) (simp only [bnot-of] at h1) (rw [(hP (:runs w) c (bnot-true _ h1))]) (exact h2)
  (have h2 (= (tbl-all (P (:runs (run-upd w x f))) (:acts (run-upd w x f))) true))
  (simp only [run-upd set-runs])
  (exact (tbl-all-mono2 ActRow (bnot-of (act-of-run x)) (P (:runs w)) (P (tbl-upd run-id x f (:runs w)))
           hin (:acts w) (any-false-all ActRow (act-of-run x) (:acts w) hn) (And.left (And.right p))))
  (exact (acts-ok-with-mk P (run-upd w x f) (And.left p) h2 (And.right (And.right p)))))

;; ---- resume: the activation is its run's only one, so after it goes no activation names the run

(a/theorem sole-drop-free [a :- ActRow, as :- (List ActRow)]
  (=> (= (act-sole as a) true) (= (tbl-any (act-of-run (:run a)) (tbl-del act-id (:id a) as)) false))
  (induction as)
  (case [nil] (intro h) (simp [tbl-del tbl-any]))
  (case [cons h t ih]
    (intro hs)
    (simp only [act-sole tbl-all Bool.and_eq_true] at hs)
    (have ih2 := (ih (And.right hs)))
    (cases hx (Nat.beq (act-id h) (:id a)))
    (case [true] (simp only [tbl-del hx]) (exact ih2))
    (case [false]
      (have hx2 (= (Nat.beq (:id h) (:id a)) false)) (exact hx)
      (have h1 := (And.left hs))
      (simp only [same-run-id hx2 Bool.or_false] at h1)
      (have h2 := (bnot-true _ h1))
      (simp only [tbl-del hx tbl-any act-of-run h2 Bool.false_or])
      (exact ih2))))

(a/theorem acts-parked-sole [w :- World, a :- ActRow] (=> (= (acts-parked w) true) (List.Mem a (:acts w)) (= (act-sole (:acts w) a) true))
  (intros h hm) (exact (tbl-all-mem ActRow (act-sole (:acts w)) a (:acts w) (And.right (And.right (acts-ok-with-parts _ w (acts-parked-rest-of w h)))) hm)))
(a/theorem acts-parked-exempt-sole [e :- Ex, w :- World, a :- ActRow] (=> (= (acts-parked-exempt e w) true) (List.Mem a (:acts w)) (= (act-sole (:acts w) a) true))
  (intros h hm) (exact (tbl-all-mem ActRow (act-sole (:acts w)) a (:acts w) (And.right (And.right (acts-ok-with-parts _ w (acts-parked-exempt-rest-of e w h)))) hm)))

(a/theorem acts-parked-resume-hand [w :- World, a :- ActRow]
  (=> (= (act-sole (:acts w) a) true) (= (acts-parked w) true) (= (acts-parked (resume w a)) true))
  (intros hs h)
  (have h1 := (acts-parked-drop-act w (:id a) h))
  (have hn (= (tbl-any (act-of-run (:run a)) (:acts (drop-act w (:id a)))) false))
  (exact (sole-drop-free a (:acts w) hs))
  (exact (acts-parked-intro _ (well-formed-resume w a (acts-parked-well-formed w h))
           (acts-ok-with-run-upd-free act-rows-good _ (:run a) run-wake
             (fn [rs :- (List RunRow), c :- ActRow, hc :- (= (act-of-run (:run a) c) false)]
               (arg-upd-free (:run a) run-wake run-wake-run-id rs c hc))
             hn (acts-parked-rest-of _ h1)))))

(a/theorem acts-parked-exempt-resume-hand [e :- Ex, w :- World, a :- ActRow]
  (=> (= (act-sole (:acts w) a) true) (= (acts-parked-exempt e w) true) (= (acts-parked-exempt e (resume w a)) true))
  (intros hs h)
  (have h1 := (acts-parked-exempt-drop-act e w (:id a) h))
  (have hn (= (tbl-any (act-of-run (:run a)) (:acts (drop-act w (:id a)))) false))
  (exact (sole-drop-free a (:acts w) hs))
  (exact (acts-parked-exempt-intro e _ (well-formed-resume w a (acts-parked-exempt-well-formed e w h))
           (acts-ok-with-run-upd-free (act-rows-good-x e) _ (:run a) run-wake
             (fn [rs :- (List RunRow), c :- ActRow, hc :- (= (act-of-run (:run a) c) false)]
               (argx-upd-free e (:run a) run-wake run-wake-run-id rs c hc))
             hn (acts-parked-exempt-rest-of e _ h1)))))

;; a hand-written proof generic in the bundle (spindel.v2.pres.part/inst: `$name` is the bundle's
;; lemma <prefix>name applied to the bundle's parameters, `(%G w)` the bundle predicate of w),
;; checked for acts-parked and for acts-parked-exempt
(defn- both! [form] (doseq [B [GA GX]] (eval (inst B form))))

(doseq [B [GA GX]] (tree/restate! B '[well-formed-drop-act]))
(both!
  '(a/theorem $resume [w :- World, a :- ActRow]
     (=> (= (act-sole (:acts w) a) true) (= (%G w) true) (= (%G (resume w a)) true))
     (intros hs h) (exact ($resume-hand w a hs h))))

(doseq [B [GA GX]] (tree/restate! B '[well-formed-resume]))
(both!
  '(a/theorem $fill-slot [w :- World, a :- ActRow, x :- Nat, v :- RunResult]
     (=> (= (act-sole (:acts w) a) true) (= (%G w) true) (= (%G (fill-slot w a x v)) true))
     (intros hs h)
     (cases hm (act-ready (act-fill x v a)))
     (simp only [fill-slot hm])
     (exact ($act-upd w (:id a) (act-fill x v) (act-fill-act-id x v) (fn [c :- ActRow] (Eq.refl (:run c))) h))
     (simp only [fill-slot hm]) (exact ($resume w a hs h))))

(doseq [B [GA GX]] (tree/restate! B '[well-formed-invalidate well-formed-fill-slot well-formed-dep-consumed]))
(both!
  '(a/theorem $fire-dep [w :- World, e :- EdgeRow]
     (=> (= (%G w) true) (= (%G (fire-dep w e)) true))
     (intro h)
     (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
     (simp only [fire-dep ha]) (exact ($invalidate w e h))
     (have hs := ($sole w a h (act-with-member-mem (:id e) (:acts w) a ha)))
     (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
     (simp only [fire-dep ha hc]) (exact ($invalidate w e h))
     (simp only [fire-dep ha hc deliver-dep])
     (have hs2 (= (act-sole (:acts (dep-consumed w e)) a) true))
     (exact (Eq.trans (congrArg (fn [as :- (List ActRow)] (act-sole as a)) (dep-consumed-acts w e)) hs))
     (exact ($fill-slot _ a _ _ hs2 ($dep-consumed w e h)))))

(doseq [B [GA GX]] (tree/restate! B '[well-formed-edge-set-phase well-formed-fill-slot]))
(both!
  '(a/theorem $fire-wait-act [res :- RunResult, w :- World, e :- EdgeRow]
     (=> (= (%G w) true) (= (%G (fire-wait-act res w e)) true))
     (intro h)
     (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
     (simp only [fire-wait-act ha]) (exact ($edge-set-phase w (:id e) ph-fired h))
     (have hs := ($sole w a h (tbl-find-mem ActRow act-id (:creditor e) a (:acts w) ha)))
     (cases hc (run-current w (:run a)))
     (simp only [fire-wait-act ha hc]) (exact ($edge-set-phase w (:id e) ph-fired h))
     (have hs2 (= (act-sole (:acts (edge-upd w (:id e) (edge-set-phase ph-fired))) a) true)) (exact hs)
     (simp only [fire-wait-act ha hc]) (exact ($fill-slot _ a _ _ hs2 ($edge-set-phase w (:id e) ph-fired h)))))

(tree/restate! GX '[well-formed-fire-edge])

;; ---- T14's local part: the run is done and every activation of it is gone

(a/defn arg-or [x :- Nat, rs :- (List RunRow), c :- ActRow] Bool (Bool.or (act-of-run x c) (act-rows-good rs c)))

(a/theorem acts-ok-with-fold-drop [P :- (=> (List RunRow) ActRow Bool), ids :- (List Nat)]
  (forall [w :- World] (=> (= (acts-ok-with P w) true) (= (acts-ok-with P (nat-fold drop-act w ids)) true)))
  (induction ids)
  (case [nil] (intros w h) (simp only [nat-fold]) (exact h))
  (case [cons h t ih]
    (intros w hw) (simp only [nat-fold])
    (exact (ih (drop-act w h) (acts-ok-with-act-del P (drop-cred-edges w h) h hw)))))

(a/theorem fold-covers [x :- Nat, ids :- (List Nat)]
  (forall [w :- World]
    (=> (= (tbl-all (covers-ids act-id (act-of-run x) ids) (:acts w)) true)
        (= (tbl-all (covers-ids act-id (act-of-run x) (List.nil Nat)) (:acts (nat-fold drop-act w ids))) true)))
  (induction ids)
  (case [nil] (intros w h) (simp only [nat-fold]) (exact h))
  (case [cons h t ih]
    (intros w hw)
    (have hout (forall [r :- ActRow] (=> (= (covers-ids act-id (act-of-run x) (List.cons Nat h t) r) true)
                                         (= (Nat.beq (act-id r) h) false)
                                         (= (covers-ids act-id (act-of-run x) t r) true))))
    (intros r h1 h2)
    (simp only [covers-ids reach-mem-cons h2 Bool.false_or] at h1) (simp only [covers-ids]) (exact h1)
    (have h4 (= (tbl-all (covers-ids act-id (act-of-run x) t) (:acts (drop-act w h))) true))
    (simp only [drop-act act-del set-acts])
    (exact (tbl-all-del ActRow act-id h _ _ hout (:acts (drop-cred-edges w h)) hw))
    (simp only [nat-fold])
    (exact (ih (drop-act w h) h4))))

(a/theorem arg-or-cancel [w :- World, x :- Nat, c :- ActRow]
  (=> (= (act-rows-good (:runs w) c) true) (= (arg-or x (tbl-upd run-id x run-cancel-row (:runs w)) c) true))
  (intros hc)
  (cases hx (act-of-run x c))
  (case [true] (simp only [arg-or hx Bool.true_or]))
  (case [false] (simp only [arg-or hx Bool.false_or (arg-upd-free x run-cancel-row run-cancel-row-id (:runs w) c hx)]) (exact hc)))

(a/theorem arg-or-clean [x :- Nat, rs :- (List RunRow), c :- ActRow]
  (=> (= (covers-ids act-id (act-of-run x) (List.nil Nat) c) true) (= (arg-or x rs c) true) (= (act-rows-good rs c) true))
  (intros h1 h2)
  (simp only [covers-ids reach-mem Bool.or_false] at h1)
  (simp only [arg-or (bnot-true _ h1) Bool.false_or] at h2) (exact h2))

(a/theorem acts-parked-cancel-acts-hand [w :- World, x :- Nat]
  (=> (= (acts-parked w) true) (= (acts-parked (cancel-acts (run-upd w x run-cancel-row) x)) true))
  (intro h)
  (have p := (acts-ok-with-parts act-rows-good w (acts-parked-rest-of w h)))
  (have g1 (= (acts-ok-with (arg-or x) (run-upd w x run-cancel-row)) true))
  (exact (acts-ok-with-mk (arg-or x) (run-upd w x run-cancel-row) (And.left p)
           (tbl-all-mono ActRow (act-rows-good (:runs w)) (arg-or x (tbl-upd run-id x run-cancel-row (:runs w)))
             (arg-or-cancel w x) (:acts w) (And.left (And.right p)))
           (And.right (And.right p))))
  (have g2 (= (acts-ok-with (arg-or x) (cancel-acts (run-upd w x run-cancel-row) x)) true))
  (simp only [cancel-acts])
  (exact (acts-ok-with-fold-drop (arg-or x) (tbl-scan act-id (act-of-run x) (:acts w)) (run-upd w x run-cancel-row) g1))
  (have hc (= (tbl-all (covers-ids act-id (act-of-run x) (List.nil Nat)) (:acts (cancel-acts (run-upd w x run-cancel-row) x))) true))
  (simp only [cancel-acts])
  (exact (fold-covers x (tbl-scan act-id (act-of-run x) (:acts w)) (run-upd w x run-cancel-row)
           (scan-covers-ids ActRow act-id (act-of-run x) (:acts w))))
  (have p2 := (acts-ok-with-parts (arg-or x) (cancel-acts (run-upd w x run-cancel-row) x) g2))
  (have h2 (= (tbl-all (act-rows-good (:runs (cancel-acts (run-upd w x run-cancel-row) x))) (:acts (cancel-acts (run-upd w x run-cancel-row) x))) true))
  (exact (tbl-all-mono2 ActRow (covers-ids act-id (act-of-run x) (List.nil Nat))
           (arg-or x (:runs (cancel-acts (run-upd w x run-cancel-row) x)))
           (act-rows-good (:runs (cancel-acts (run-upd w x run-cancel-row) x)))
           (arg-or-clean x (:runs (cancel-acts (run-upd w x run-cancel-row) x)))
           (:acts (cancel-acts (run-upd w x run-cancel-row) x)) hc (And.left (And.right p2))))
  (exact (acts-parked-intro (cancel-acts (run-upd w x run-cancel-row) x)
           (well-formed-cancel-acts (run-upd w x run-cancel-row) x (well-formed-run-upd w x run-cancel-row run-cancel-row-id (acts-parked-well-formed w h)))
           (acts-ok-with-mk act-rows-good (cancel-acts (run-upd w x run-cancel-row) x) (And.left p2) h2 (And.right (And.right p2))))))

(tree/restate! GA '[well-formed-cancel-debtor well-formed-cleanup-set well-formed-cancel-res])
(a/theorem acts-parked-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
  (=> (= (acts-parked w) true) (= (acts-parked (cancel-run-local w r rep)) true))
  (intro h)
  (simp only [cancel-run-local])
  (exact (acts-parked-cancel-debtor rep _ r (acts-parked-cleanup-set _ (:id r) _ (acts-parked-cancel-res _ r (acts-parked-cancel-acts-hand w (:id r) h))))))

;; ---- a run that is not parked, or holds the slice, has no activation

(a/theorem tok-facts [w :- World, st :- Nat, r :- RunRow]
  (=> (= (tok-run w st) (Option.some RunRow r)) (And (List.Mem r (:runs w)) (= (:slice r) true)))
  (intro h)
  (cases hf (tbl-find run-stamp st (:runs w)))
  (case [none] (simp [tok-run hf] at h))
  (case [some r2]
    (cases hv (run-valid r2))
    (case [false] (simp [tok-run hf hv] at h))
    (case [true]
      (simp only [tok-run hf hv Option.some.injEq] at h)
      (simp only [run-valid Bool.and_eq_true] at hv)
      (have e (= (:slice r2) (:slice r))) (exact (congrArg (fn [q :- RunRow] (:slice q)) h))
      (have hm := (tbl-find-mem RunRow run-stamp st r2 (:runs w) hf))
      (rw [h] at hm)
      (exact (And.intro hm (Eq.trans (Eq.symm e) (And.left hv)))))))

(a/theorem slice-not-good [r :- RunRow] (=> (= (:slice r) true) (= (good-row r) false))
  (intro h) (simp only [good-row h Bool.not_true Bool.and_false]))

(a/theorem no-act-one [r :- RunRow, rs :- (List RunRow), c :- ActRow]
  (=> (List.Mem r rs) (= (good-row r) false) (= (act-rows-good rs c) true) (= (bnot-of (act-of-run (:id r)) c) true))
  (intros hm hg hc)
  (simp only [act-rows-good] at hc)
  (have h1 := (tbl-all-mem RunRow (good-for (:run c)) r rs hc hm))
  (simp only [good-for hg Bool.or_false] at h1)
  (have h2 := (bnot-true _ h1))
  (simp only [bnot-of act-of-run])
  (rw [beq-comm]) (rw [h2]))

(a/theorem all-bnot-any [A :- Type, p :- (=> A Bool), xs :- (List A)]
  (=> (= (tbl-all (bnot-of p) xs) true) (= (tbl-any p xs) false))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any]))
  (case [cons h t ih]
    (intro ha)
    (simp only [tbl-all Bool.and_eq_true bnot-of] at ha)
    (simp only [tbl-any (bnot-true _ (And.left ha)) Bool.false_or])
    (exact (ih (And.right ha)))))

(a/theorem no-act-bad [w :- World, r :- RunRow]
  (=> (= (acts-parked w) true) (List.Mem r (:runs w)) (= (good-row r) false) (= (tbl-any (act-of-run (:id r)) (:acts w)) false))
  (intros h hm hg)
  (have p := (acts-ok-with-parts act-rows-good w (acts-parked-rest-of w h)))
  (exact (all-bnot-any ActRow (act-of-run (:id r)) (:acts w)
           (tbl-all-mono ActRow (act-rows-good (:runs w)) (bnot-of (act-of-run (:id r)))
             (fn [c :- ActRow, hc :- (= (act-rows-good (:runs w) c) true)] (no-act-one r (:runs w) c hm hg hc))
             (:acts w) (And.left (And.right p))))))

(a/theorem acts-parked-run-upd-free [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                            hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r)))]
  (=> (= (tbl-any (act-of-run x) (:acts w)) false) (= (acts-parked w) true) (= (acts-parked (run-upd w x f)) true))
  (intros hn h)
  (exact (acts-parked-intro (run-upd w x f) (well-formed-run-upd w x f hid (acts-parked-well-formed w h))
           (acts-ok-with-run-upd-free act-rows-good w x f (arg-upd-free x f hid) hn (acts-parked-rest-of w h)))))

(a/theorem find-facts [w :- World, rid :- Nat, r :- RunRow]
  (=> (= (run-find w rid) (Option.some RunRow r)) (And (List.Mem r (:runs w)) (= (:id r) rid)))
  (intro h) (exact (And.intro (tbl-find-mem RunRow run-id rid r (:runs w) h) (tbl-find-id RunRow run-id rid r (:runs w) h))))

(a/theorem acts-parked-free-of-tok [w :- World, st :- Nat, r :- RunRow]
  (=> (= (acts-parked w) true) (= (tok-run w st) (Option.some RunRow r)) (= (tbl-any (act-of-run (:id r)) (:acts w)) false))
  (intros h ht)
  (have p := (tok-facts w st r ht))
  (exact (no-act-bad w r h (And.left p) (slice-not-good r (And.right p)))))

;; ---- T12, the scheduling choice, finalize, finally regions: the token or chosen run has no activation

(tree/restate! GA '[well-formed-finalize-if-final well-formed-run-cascade well-formed-retire-after well-formed-complete-body])
(a/theorem acts-parked-complete-raw [w :- World, r :- RunRow, res :- RunResult]
  (=> (= (tbl-any (act-of-run (:id r)) (:acts w)) false) (= (acts-parked w) true) (= (acts-parked (complete-raw w r res)) true))
  (intros hn h)
  (have h0 := (acts-parked-run-upd-free w (:id r) run-complete-row run-complete-row-id hn h))
  (simp only [complete-raw])
  (exact (acts-parked-finalize-if-final _ (:of r) (acts-parked-run-cascade _ _ (acts-parked-retire-after _ (:id r) (acts-parked-complete-body _ r res h0))))))

(tree/restate! GA '[well-formed-complete-raw])
(a/theorem acts-parked-t12-complete [w :- World, st :- Nat, tag :- Nat, v :- Nat]
  (=> (= (acts-parked w) true) (= (acts-parked (:world (t12-complete w st tag v))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t12-complete ht refuse]) (exact h)
  (cases hn (run-normal r))
  (simp only [t12-complete ht hn refuse]) (exact h)
  (simp only [t12-complete ht hn accept]) (exact (acts-parked-complete-raw w r _ (acts-parked-free-of-tok w st r h ht) h)))

;; ---- Z#77 T28: the retired run has no activation from `cancel-acts` on (the resource deletions and the
;; finalizer drop change no activation), so T12's override applies to its completion
(a/theorem covers-none-any [x :- Nat, as :- (List ActRow)]
  (=> (= (tbl-all (covers-ids act-id (act-of-run x) (List.nil Nat)) as) true) (= (tbl-any (act-of-run x) as) false))
  (induction as)
  (case [nil] (intro h) (simp only [tbl-any]))
  (case [cons a t ih]
    (intro h)
    (simp only [tbl-all covers-ids reach-mem Bool.or_false Bool.and_eq_true] at h)
    (simp only [tbl-any (bnot-true _ (And.left h)) (ih (And.right h)) Bool.false_or])))
(a/theorem cancel-acts-none [w :- World, x :- Nat] (= (tbl-any (act-of-run x) (:acts (cancel-acts w x))) false)
  (apply (covers-none-any x))
  (simp only [cancel-acts])
  (exact (fold-covers x (tbl-scan act-id (act-of-run x) (:acts w)) w (scan-covers-ids ActRow act-id (act-of-run x) (:acts w)))))
(a/theorem acts-ack-if [rid :- Nat, w :- World, z :- Nat] (= (:acts (ack-if rid w z)) (:acts w))
  (cases hu (tbl-all (no-debtor z) (:edges w)))
  (case [false] (simp only [ack-if hu]))
  (case [true] (simp only [ack-if hu ack-raw cleanup-upd run-upd resource-del set-cleanup set-runs set-res])))
(a/theorem acts-fold-ack [rid :- Nat, zs :- (List Nat)]
  (forall [w :- World] (= (:acts (nat-fold (ack-if rid) w zs)) (:acts w)))
  (induction zs)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons z t ih] (intro w) (simp only [nat-fold]) (exact (Eq.trans (ih (ack-if rid w z)) (acts-ack-if rid w z)))))
(a/theorem retire-mid-noact [w :- World, r :- RunRow]
  (= (tbl-any (act-of-run (:id r)) (:acts (nat-fold (ack-if (:id r)) (cancel-acts w (:id r)) (:resources r)))) false)
  (rw [(acts-fold-ack (:id r) (:resources r) (cancel-acts w (:id r)))])
  (exact (cancel-acts-none w (:id r))))
(a/theorem retire-pre-noact [w :- World, r :- RunRow] (= (tbl-any (act-of-run (:id r)) (:acts (retire-pre w r))) false)
  (simp only [retire-pre run-upd set-runs]) (exact (retire-mid-noact w r)))
(a/theorem retire-r1-id [w :- World, r :- RunRow, r1 :- RunRow, rid :- Nat]
  (=> (= (run-find w rid) (Option.some RunRow r)) (= (run-find (retire-pre w r) rid) (Option.some RunRow r1)) (= (:id r1) (:id r)))
  (intros h0 h1)
  (exact (Eq.trans (tbl-find-id RunRow run-id rid r1 (:runs (retire-pre w r)) h1)
                   (Eq.symm (tbl-find-id RunRow run-id rid r (:runs w) h0)))))
(a/theorem retire-r1-noact [w :- World, r :- RunRow, r1 :- RunRow, rid :- Nat]
  (=> (= (run-find w rid) (Option.some RunRow r)) (= (run-find (retire-pre w r) rid) (Option.some RunRow r1))
      (= (tbl-any (act-of-run (:id r1)) (:acts (retire-pre w r))) false))
  (intros h0 h1) (rw [(retire-r1-id w r r1 rid h0 h1)]) (exact (retire-pre-noact w r)))

(a/theorem nat-fold-pres2 [P :- (=> World Bool), Q :- (=> World Bool), f :- (=> World Nat World),
                           hp :- (forall [w :- World, x :- Nat] (=> (= (P w) true) (= (P (f w x)) true))),
                           hq :- (forall [w :- World, x :- Nat] (=> (= (P w) true) (= (Q w) true) (= (Q (f w x)) true))),
                           xs :- (List Nat)]
  (forall [w :- World] (=> (= (P w) true) (= (Q w) true) (= (Q (nat-fold f w xs)) true)))
  (induction xs)
  (case [nil] (intros w a b) (simp only [nat-fold]) (exact b))
  (case [cons x t ih] (intros w a b) (simp only [nat-fold]) (exact (ih (f w x) (hp w x a) (hq w x a b)))))
(a/theorem pres-and [P1 :- (=> World Bool), P2 :- (=> World Bool), f :- (=> World Nat World),
                     h1 :- (forall [w :- World, x :- Nat] (=> (= (P1 w) true) (= (P1 (f w x)) true))),
                     h2 :- (forall [w :- World, x :- Nat] (=> (= (P2 w) true) (= (P2 (f w x)) true)))]
  (forall [w :- World, x :- Nat] (=> (= (Bool.and (P1 w) (P2 w)) true) (= (Bool.and (P1 (f w x)) (P2 (f w x))) true)))
  (intros w x h)
  (simp only [Bool.and_eq_true] at h)
  (simp only [(h1 w x (And.left h)) (h2 w x (And.right h)) Bool.and_self]))
(a/theorem retire-r1-mem [w :- World, r :- RunRow, r1 :- RunRow, rid :- Nat]
  (=> (= (run-find (retire-pre w r) rid) (Option.some RunRow r1)) (List.Mem r1 (:runs (retire-pre w r))))
  (intro h1) (exact (tbl-find-mem RunRow run-id rid r1 (:runs (retire-pre w r)) h1)))

(tree/restate! GA '[well-formed-ack-if well-formed-cancel-acts])
(a/theorem acts-parked-retire-pre [w :- World, r :- RunRow]
  (=> (= (acts-parked w) true) (= (acts-parked (retire-pre w r)) true))
  (intro h)
  (simp only [retire-pre])
  (exact (acts-parked-run-upd-free _ (:id r) run-drop-fins run-drop-fins-id (retire-mid-noact w r)
           (acts-parked-nat-fold (ack-if (:id r)) (acts-parked-ack-if (:id r)) (:resources r) _ (acts-parked-cancel-acts w (:id r) h)))))
(tree/restate! GA '[well-formed-retire-pre well-formed-complete-raw well-formed-run-cascade])
(a/theorem acts-parked-retire-one [v :- Nat, w :- World, rid :- Nat]
  (=> (= (acts-parked w) true) (= (acts-parked (retire-one v w rid)) true))
  (intro h)
  (cases hf (run-find w rid))
  (case [none] (simp only [retire-one hf]) (exact h))
  (case [some r]
    (have hp := (acts-parked-retire-pre w r h))
    (cases hf1 (run-find (retire-pre w r) rid))
    (case [none] (simp only [retire-one hf hf1]) (exact hp))
    (case [some r1]
      (cases ha (Bool.and (run-alive r1) (run-of-local (retire-pre w r) r1)))
      (case [true] (simp only [retire-one hf hf1 ha]) (exact (acts-parked-complete-raw _ r1 _ (retire-r1-noact w r r1 rid hf hf1) hp)))
      (case [false] (simp only [retire-one hf hf1 ha t13-retire]) (exact (acts-parked-run-cascade _ _ hp))))))

(a/theorem active-not-good [r :- RunRow] (=> (= (Nat.beq (:act r) act-active) true) (= (good-row r) false))
  (intro h)
  (have e (= (:act r) act-active)) (exact (Nat.eq_of_beq_eq_true h))
  (simp [good-row e act-active act-parked]))
(a/theorem done-not-good [r :- RunRow] (=> (= (Nat.beq (:act r) act-done) true) (= (good-row r) false))
  (intro h)
  (have e (= (:act r) act-done)) (exact (Nat.eq_of_beq_eq_true h))
  (simp [good-row e act-done act-parked]))

(a/theorem acts-parked-t-schedule [w :- World, rid :- Nat]
  (=> (= (acts-parked w) true) (= (acts-parked (:world (t-schedule w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-schedule hf refuse]) (exact h)
  (cases hg (schedule-ok w r))
  (simp only [t-schedule hf hg refuse]) (exact h)
  (have p := (find-facts w rid r hf))
  (have hg2 := hg)
  (simp only [schedule-ok Bool.and_eq_true] at hg2)
  (have hn := (no-act-bad w r h (And.left p) (active-not-good r (And.left hg2))))
  (rw [(And.right p)] at hn)
  (simp only [t-schedule hf hg accept]) (exact (acts-parked-run-upd-free w rid run-enter-row run-enter-row-id hn h)))

(a/theorem acts-parked-t-finalize [w :- World, rid :- Nat]
  (=> (= (acts-parked w) true) (= (acts-parked (:world (t-finalize w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-finalize hf refuse]) (exact h)
  (cases hg (cleanup-ready w r))
  (simp only [t-finalize hf hg refuse]) (exact h)
  (have p := (find-facts w rid r hf))
  (have hg2 := hg)
  (simp only [cleanup-ready Bool.and_eq_true] at hg2)
  (have hn := (no-act-bad w r h (And.left p) (done-not-good r (And.left hg2))))
  (rw [(And.right p)] at hn)
  (simp only [t-finalize hf hg accept]) (exact (acts-parked-run-upd-free w rid run-enter-row run-enter-row-id hn h)))

(a/theorem acts-parked-t-finally-enter [w :- World, st :- Nat]
  (=> (= (acts-parked w) true) (= (acts-parked (:world (t-finally-enter w st))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-enter ht refuse]) (exact h)
  (cases hg (run-normal r))
  (simp only [t-finally-enter ht hg refuse]) (exact h)
  (simp only [t-finally-enter ht hg accept])
  (exact (acts-parked-run-upd-free w (:id r) (run-fin-push (Finalizer.mk 0 (:effect-index r) (List.nil Nat)))
           (run-fin-push-id _) (acts-parked-free-of-tok w st r h ht) h)))

(a/theorem acts-parked-t-finally-exit [w :- World, st :- Nat]
  (=> (= (acts-parked w) true) (= (acts-parked (:world (t-finally-exit w st))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-exit ht refuse]) (exact h)
  (have hn := (acts-parked-free-of-tok w st r h ht))
  (cases he (finally-exit-refused (:finalizers r)))
  (case [true] (simp only [t-finally-exit ht he refuse]) (exact h))
  (case [false] (simp only [t-finally-exit ht he accept]) (exact (acts-parked-run-upd-free w (:id r) run-fin-exit run-fin-exit-id hn h))))

(a/theorem acts-parked-t-finally-leave [w :- World, st :- Nat]
  (=> (= (acts-parked w) true) (= (acts-parked (:world (t-finally-leave w st))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-leave ht refuse]) (exact h)
  (have hn := (acts-parked-free-of-tok w st r h ht))
  (cases he (finally-leave-refused (:finalizers r)))
  (case [true] (simp only [t-finally-leave ht he refuse]) (exact h))
  (case [false] (simp only [t-finally-leave ht he accept]) (exact (acts-parked-run-upd-free w (:id r) run-fin-pop run-fin-pop-id hn h))))

(tree/restate! GA '[well-formed-run-cascade])
(a/theorem acts-parked-t-slice-exit [w :- World, rid :- Nat]
  (=> (= (acts-parked w) true) (= (acts-parked (:world (t-slice-exit w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-slice-exit hf refuse]) (exact h)
  (cases hg (exit-ready r))
  (simp only [t-slice-exit hf hg refuse]) (exact h)
  (have p := (find-facts w rid r hf))
  (have hg2 := hg)
  (simp only [exit-ready Bool.and_eq_true] at hg2)
  (have hn := (no-act-bad w r h (And.left p) (done-not-good r (And.left hg2))))
  (rw [(And.right p)] at hn)
  (simp only [t-slice-exit hf hg accept t13-retire])
  (exact (acts-parked-run-cascade _ _ (acts-parked-run-upd-free w rid run-fin-pop-end run-fin-pop-end-id hn h))))

;; ---- T6 and take: the new activation's run is exempt until it parks

(a/theorem all-ids-mem [A :- Type, idf :- (=> A Nat), p :- (=> Nat Bool), r :- A, xs :- (List A)]
  (=> (= (tbl-all p (tbl-ids idf xs)) true) (List.Mem r xs) (= (p (idf r)) true))
  (induction xs)
  (case [nil] (intros h hm) (cases hm))
  (case [cons h t ih]
    (intros hp hm)
    (simp only [tbl-ids tbl-all Bool.and_eq_true] at hp)
    (cases hm)
    (exact (And.left hp))
    (rename_i hm2)
    (exact (ih (And.right hp) hm2))))

(a/theorem run-below [w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (< (:id r) (:next-id w)))
  (intros h hm)
  (have hi := (And.right (And.right (well-formed-parts w h))))
  (simp only [ids-ok ids-below all-ids tbl-all-nat-app Bool.and_eq_true] at hi)
  (have hr := (all-ids-mem RunRow run-id (id-in-range (:next-id w)) r (:runs w)
                (And.left (And.right (And.right (And.right (And.right (And.right hi)))))) hm))
  (simp only [id-in-range run-id Bool.and_eq_true Nat.blt_eq] at hr)
  (exact (And.right hr)))

(a/theorem sole-ins [n :- Nat, a :- ActRow, as :- (List ActRow)]
  (=> (= (tbl-any (act-of-run (:run a)) as) false) (= (tbl-all (act-sole as) as) true)
      (= (tbl-all (act-sole (List.cons ActRow a as)) (List.cons ActRow a as)) true))
  (intros hn h)
  (have hb := (any-false-all ActRow (act-of-run (:run a)) as hn))
  (have h1 (forall [c :- ActRow] (=> (= (bnot-of (act-of-run (:run a)) c) true) (= (same-run-id a c) true))))
  (intros c hc) (simp only [bnot-of act-of-run] at hc) (simp only [same-run-id hc Bool.not_false Bool.true_or])
  (have h2 (forall [c :- ActRow] (=> (= (bnot-of (act-of-run (:run a)) c) true) (= (act-sole as c) true)
                                     (= (act-sole (List.cons ActRow a as) c) true))))
  (intros c hc hs)
  (simp only [bnot-of act-of-run] at hc)
  (have hc2 (= (Nat.beq (:run a) (:run c)) false)) (rw [beq-comm]) (exact (bnot-true _ hc))
  (simp only [act-sole tbl-all same-run-id hc2 Bool.not_false Bool.true_or Bool.true_and]) (exact hs)
  (simp only [tbl-all Bool.and_eq_true])
  (apply And.intro)
  (simp only [act-sole tbl-all Bool.and_eq_true same-run-id Nat.beq_refl Bool.or_true Bool.true_and])
  (exact (tbl-all-mono ActRow (bnot-of (act-of-run (:run a))) (same-run-id a) h1 as hb))
  (exact (tbl-all-mono2 ActRow (bnot-of (act-of-run (:run a))) (act-sole as) (act-sole (List.cons ActRow a as)) h2 as hb h)))

(a/theorem argx-other [x :- Nat, n :- Nat, rs :- (List RunRow), c :- ActRow]
  (=> (= (bnot-of (act-of-run x) c) true) (= (act-rows-good rs c) true)
      (= (act-rows-good-x (Ex.mk x n) rs c) true))
  (intros hc h)
  (simp only [bnot-of act-of-run] at hc)
  (simp only [act-rows-good-x (bnot-true _ hc)]) (exact h))

(a/theorem acts-parked-exempt-act-ins [w :- World, a :- ActRow]
  (=> (= (act-id a) (:next-id w)) (< (:run a) (:next-id w)) (= (tbl-any (act-of-run (:run a)) (:acts w)) false)
      (= (acts-parked w) true) (= (acts-parked-exempt (Ex.mk (:run a) (:next-id w)) (bump (act-ins w a))) true))
  (intros hid hlt hn h)
  (have p := (acts-ok-with-parts act-rows-good w (acts-parked-rest-of w h)))
  (have hb := (any-false-all ActRow (act-of-run (:run a)) (:acts w) hn))
  (have ha1 (= (act-below (:next-id w) a) true)) (simp only [act-below Nat.blt_eq]) (exact hlt)
  (have g1 (= (tbl-all (act-below (:next-id (act-ins w a))) (:acts (act-ins w a))) true))
  (simp only [act-ins set-acts tbl-ins tbl-all ha1 (And.left p) Bool.and_self])
  (have ha2 (= (act-rows-good-x (Ex.mk (:run a) (:next-id w)) (:runs w) a) true))
  (have e (= (:id a) (:next-id w))) (exact hid)
  (simp only [act-rows-good-x Nat.beq_refl e])
  (have g2 (= (tbl-all (act-rows-good-x (Ex.mk (:run a) (:next-id w)) (:runs (act-ins w a))) (:acts (act-ins w a))) true))
  (simp only [act-ins set-acts tbl-ins tbl-all ha2 Bool.true_and])
  (exact (tbl-all-mono2 ActRow (bnot-of (act-of-run (:run a))) (act-rows-good (:runs w))
           (act-rows-good-x (Ex.mk (:run a) (:next-id w)) (:runs w)) (argx-other (:run a) (:next-id w) (:runs w))
           (:acts w) hb (And.left (And.right p))))
  (have g3 (= (tbl-all (act-sole (:acts (act-ins w a))) (:acts (act-ins w a))) true))
  (simp only [act-ins set-acts tbl-ins])
  (exact (sole-ins 0 a (:acts w) hn (And.right (And.right p))))
  (exact (acts-parked-exempt-intro (Ex.mk (:run a) (:next-id w)) (bump (act-ins w a)) (well-formed-act-ins-fresh w a hid (acts-parked-well-formed w h))
           (acts-ok-with-bump (act-rows-good-x (Ex.mk (:run a) (:next-id w))) (act-ins w a)
             (acts-ok-with-mk (act-rows-good-x (Ex.mk (:run a) (:next-id w))) (act-ins w a) g1 g2 g3)))))

(a/theorem all-good-upd [x :- Nat, f :- (=> RunRow RunRow),
                         hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         hg :- (forall [r :- RunRow] (= (good-row (f r)) true)), rs :- (List RunRow)]
  (= (tbl-all (good-for x) (tbl-upd run-id x f rs)) true)
  (induction rs)
  (case [nil] (simp [tbl-all tbl-upd]))
  (case [cons h t ih]
    (cases hx (Nat.beq (run-id h) x))
    (case [false]
      (have hx2 (= (Nat.beq (:id h) x) false)) (exact hx)
      (simp only [tbl-upd hx tbl-all good-for hx2 Bool.not_false Bool.true_or ih Bool.and_self]))
    (case [true] (simp only [tbl-upd hx tbl-all good-for (hg h) Bool.or_true ih Bool.and_self]))))

(a/theorem arg-restore [ex :- Ex, f :- (=> RunRow RunRow),
                        hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hg :- (forall [r :- RunRow] (= (good-row (f r)) true)), rs :- (List RunRow), c :- ActRow]
  (=> (= (act-rows-good-x ex rs c) true) (= (act-rows-good (tbl-upd run-id (:x ex) f rs) c) true))
  (intro h)
  (cases hx (Nat.beq (:run c) (:x ex)))
  (case [true]
    (have e (= (:run c) (:x ex))) (exact (Nat.eq_of_beq_eq_true hx))
    (simp only [act-rows-good e]) (exact (all-good-upd (:x ex) f hid hg rs)))
  (case [false]
    (simp only [act-rows-good-x hx] at h)
    (rw [(arg-upd-free (:x ex) f hid rs c hx)]) (exact h)))

(a/theorem acts-parked-exempt-restore [ex :- Ex, w :- World, f :- (=> RunRow RunRow),
                       hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hg :- (forall [r :- RunRow] (= (good-row (f r)) true))]
  (=> (= (acts-parked-exempt ex w) true) (= (acts-parked (run-upd w (:x ex) f)) true))
  (intro h)
  (have p := (acts-ok-with-parts (act-rows-good-x ex) w (acts-parked-exempt-rest-of ex w h)))
  (have g2 (= (tbl-all (act-rows-good (:runs (run-upd w (:x ex) f))) (:acts (run-upd w (:x ex) f))) true))
  (simp only [run-upd set-runs])
  (exact (tbl-all-mono ActRow (act-rows-good-x ex (:runs w)) (act-rows-good (tbl-upd run-id (:x ex) f (:runs w)))
           (arg-restore ex f hid hg (:runs w)) (:acts w) (And.left (And.right p))))
  (exact (acts-parked-intro (run-upd w (:x ex) f) (well-formed-run-upd w (:x ex) f hid (acts-parked-exempt-well-formed ex w h))
           (acts-ok-with-mk act-rows-good (run-upd w (:x ex) f) (And.left p) g2 (And.right (And.right p))))))

(a/defn act-id-is [x :- Nat, c :- ActRow] Bool (Nat.beq (act-id c) x))
(a/theorem has-false-all [x :- Nat, as :- (List ActRow)]
  (=> (= (tbl-has act-id x as) false) (= (tbl-all (bnot-of (act-id-is x)) as) true))
  (induction as)
  (case [nil] (intro h) (simp [tbl-all]))
  (case [cons h t ih]
    (intro hn)
    (cases hx (Nat.beq (act-id h) x))
    (case [true] (simp [tbl-has hx] at hn))
    (case [false]
      (simp only [tbl-has hx] at hn)
      (simp only [tbl-all bnot-of act-id-is hx Bool.not_false Bool.true_and])
      (exact (ih hn)))))

(a/theorem arg-gone [ex :- Ex, rs :- (List RunRow), c :- ActRow]
  (=> (= (bnot-of (act-id-is (:a ex)) c) true) (= (act-rows-good-x ex rs c) true) (= (act-rows-good rs c) true))
  (intros h1 h2)
  (simp only [bnot-of act-id-is] at h1)
  (cases hx (Nat.beq (:run c) (:x ex)))
  (case [true]
    (simp only [act-rows-good-x hx] at h2)
    (have h3 (= (Nat.beq (act-id c) (:a ex)) true)) (exact h2)
    (rw [h3] at h1) (cases h1))
  (case [false] (simp only [act-rows-good-x hx] at h2) (exact h2)))

(a/theorem run-park-row-good [r :- RunRow] (= (good-row (run-park-row r)) true) (simp [good-row run-park-row act-parked]))
(a/theorem run-tick-park-good [r :- RunRow] (= (good-row (run-tick-park r)) true) (simp [good-row run-tick-park act-parked]))

(a/theorem acts-parked-exempt-park [ex :- Ex, w :- World]
  (=> (= (acts-parked-exempt ex w) true) (= (acts-parked (park-if w (:a ex) (:x ex))) true))
  (intro h)
  (cases ha (act-has w (:a ex)))
  (case [true] (simp only [park-if ha]) (exact (acts-parked-exempt-restore ex w run-park-row run-park-row-id run-park-row-good h)))
  (case [false]
    (simp only [park-if ha])
    (have p := (acts-ok-with-parts (act-rows-good-x ex) w (acts-parked-exempt-rest-of ex w h)))
    (have hb := (has-false-all (:a ex) (:acts w) ha))
    (exact (acts-parked-intro w (acts-parked-exempt-well-formed ex w h)
             (acts-ok-with-mk act-rows-good w (And.left p)
               (tbl-all-mono2 ActRow (bnot-of (act-id-is (:a ex))) (act-rows-good-x ex (:runs w)) (act-rows-good (:runs w))
                 (arg-gone ex (:runs w)) (:acts w) hb (And.left (And.right p)))
               (And.right (And.right p)))))))

(tree/restate! GX '[well-formed-nat-fold])
(tree/restate! GX '[well-formed-demand-reactive])
(tree/restate! GX '[well-formed-await-wire])
(tree/restate! GX '[well-formed-fast-fill])
(tree/restate! GX '[well-formed-insert-edge-checked])

(tree/restate! GA '[well-formed-finalize-if-final])
(tree/restate! GA '[well-formed-nat-fold])

(a/theorem acts-parked-await-raw-hand [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (List.Mem r (:runs w)) (= (:slice r) true) (= (acts-parked w) true) (= (acts-parked (await-raw w r ds mode k mine)) true))
  (intros hm hs h)
  (have hn := (no-act-bad w r h hm (slice-not-good r hs)))
  (have hlt := (run-below w r (acts-parked-well-formed w h) hm))
  (have h1 := (acts-parked-run-upd w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (good-row q))) h))
  (have h2 := (acts-parked-exempt-act-ins (run-upd w (:id r) run-tick)
                (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine)
                (rfl) hlt hn h1))
  (have h3 := (acts-parked-exempt-nat-fold (Ex.mk (:id r) (:next-id w)) demand-reactive (acts-parked-exempt-demand-reactive (Ex.mk (:id r) (:next-id w)))
                (nat-distinct ds) _ h2))
  (have h4 (= (acts-parked-exempt (Ex.mk (:id r) (:next-id w)) (:world (await-acc w r ds mode k mine))) true))
  (exact (acts-parked-exempt-await-wire (Ex.mk (:id r) (:next-id w)) r (:next-id w) mode k (nat-distinct ds)
           (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) h3))
  (have h5 := (acts-parked-exempt-act-upd (Ex.mk (:id r) (:next-id w)) (:world (await-acc w r ds mode k mine)) (:next-id w)
                (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds))
                (act-set-members-id (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds))
                (fn [c :- ActRow] (Eq.refl (:run c))) h4))
  (have h6 := (acts-parked-exempt-nat-fold (Ex.mk (:id r) (:next-id w)) (fast-fill (:pairs (await-acc w r ds mode k mine)))
                (acts-parked-exempt-fast-fill (Ex.mk (:id r) (:next-id w)) (:pairs (await-acc w r ds mode k mine))) (nat-distinct ds) _ h5))
  (have h7 := (acts-parked-exempt-park (Ex.mk (:id r) (:next-id w)) _ h6))
  (simp only [await-raw await-post])
  (exact (acts-parked-nat-fold finalize-if-final acts-parked-finalize-if-final (nat-distinct ds) _ h7)))

(a/theorem acts-parked-take-park-hand [w :- World, r :- RunRow, x :- Nat, k :- Nat]
  (=> (List.Mem r (:runs w)) (= (:slice r) true) (= (acts-parked w) true) (= (acts-parked (take-park w r x k)) true))
  (intros hm hs h)
  (have hn := (no-act-bad w r h hm (slice-not-good r hs)))
  (have hlt := (run-below w r (acts-parked-well-formed w h) hm))
  (have h2 := (acts-parked-exempt-act-ins w (take-act w r k) (rfl) hlt hn h))
  (have h3 := (acts-parked-exempt-insert-edge-checked (Ex.mk (:id r) (:next-id w)) _ (take-edge r (:next-id w) x) h2))
  (simp only [take-park])
  (exact (acts-parked-exempt-restore (Ex.mk (:id r) (:next-id w)) _ run-tick-park run-tick-park-id run-tick-park-good h3)))

(a/theorem acts-parked-await-raw [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (List.Mem r (:runs w)) (= (:slice r) true) (= (acts-parked w) true) (= (acts-parked (await-raw w r ds mode k mine)) true))
  (intros hm hs h) (exact (acts-parked-await-raw-hand w r ds mode k mine hm hs h)))

(tree/restate! GA '[well-formed-await-raw])
(a/theorem acts-parked-t6-await [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
  (=> (= (acts-parked w) true) (= (acts-parked (:world (t6-await w st ds mode k fresh mine))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t6-await ht refuse]) (exact h)
  (have p := (tok-facts w st r ht))
  (cases hg (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
  (simp only [t6-await ht hg refuse]) (exact h)
  (simp only [t6-await ht hg accept])
  (exact (acts-parked-await-raw w r ds mode k mine (And.left p) (And.right p) h)))

(a/theorem acts-parked-take-park [w :- World, r :- RunRow, x :- Nat, k :- Nat]
  (=> (List.Mem r (:runs w)) (= (:slice r) true) (= (acts-parked w) true) (= (acts-parked (take-park w r x k)) true))
  (intros hm hs h) (exact (acts-parked-take-park-hand w r x k hm hs h)))

(tree/restate! GA '[well-formed-take-park well-formed-take-now])
(a/theorem acts-parked-t-take [w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (acts-parked w) true) (= (acts-parked (:world (t-take w st x k fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-take ht refuse]) (exact h)
  (have p := (tok-facts w st r ht))
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-take ht hs refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (takeable s))))
  (simp only [t-take ht hs hg refuse]) (exact h)
  (cases hv (take-ready s))
  (simp only [t-take ht hs hg hv accept]) (exact (acts-parked-take-park w r x k (And.left p) (And.right p) h))
  (simp only [t-take ht hs hg hv accept]) (exact (acts-parked-take-now w r x h)))

;; Z#55: arm = arm-raw (frame for acts-parked) then take-park on the armed row (still the slice holder)
(tree/restate! GA '[well-formed-take-park well-formed-arm-raw])
(a/theorem acts-parked-arm-park [w :- World, r :- RunRow, kind :- Nat, k :- Nat]
  (=> (List.Mem r (:runs w)) (= (:slice r) true) (= (acts-parked w) true) (= (acts-parked (arm-park w r kind k)) true))
  (intros hm hs h)
  (simp only [arm-park])
  (exact (acts-parked-take-park _ (run-arm (:next-id w) r) (:next-id w) k (arm-raw-mem w r kind hm) hs (acts-parked-arm-raw w r kind h))))

(tree/restate! GA '[well-formed-arm-park])
(a/theorem acts-parked-t17-arm [w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (acts-parked w) true) (= (acts-parked (:world (t17-arm w st kind k fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t17-arm ht refuse]) (exact h)
  (have p := (tok-facts w st r ht))
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind))))
  (simp only [t17-arm ht hg refuse]) (exact h)
  (simp only [t17-arm ht hg accept]) (exact (acts-parked-arm-park w r kind k (And.left p) (And.right p) h)))

(tree/restate! GA '[step-well-formed])

;; ===========================================================================
;; Part E. The step
;; ===========================================================================

(a/theorem acts-parked-empty [] (= (acts-parked empty-world) true) (rfl))

;; every step keeps the activation invariant (the hypotheses of step-well-formed)
(a/theorem step-acts [w :- World, it :- Item]
  (=> (= (acts-parked w) true) (= (rule-r-safe (:world (raw w it))) true) (= (acts-parked (:world (world-step w it))) true))
  (intros h hs) (exact (step-acts-parked w it h hs)))

;; P2 and P4 hold in every world of the model: the raw world of a step has no activation of a
;; done run
(a/theorem raw-acts-alive [w :- World, it :- Item]
  (=> (= (acts-parked w) true) (= (acts-alive (:world (raw w it))) true))
  (intro h) (exact (acts-parked-acts-alive _ (acts-parked-raw w it h))))

;; Theorem: the step's world is normalized, with no normalized flag (hypotheses of step-well-formed)
(a/theorem step-normalized-acts-parked [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) true) (= (acts-parked w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (normalized (:world (world-step w it))) true))
  (intros ha h hs)
  (exact (step-normalized-ok w it ha (acts-parked-well-formed w h) (raw-acts-alive w it h) hs)))

;; I4 after every accepted step
(a/theorem step-i4-acts-parked [w :- World, it :- Item, r :- RunRow]
  (=> (= (:accepted (raw w it)) true) (= (acts-parked w) true) (= (rule-r-safe (:world (raw w it))) true)
      (List.Mem r (:runs (:world (world-step w it)))) (= (run-alive r) true)
      (= (in-live (:world (world-step w it)) (:id r)) true))
  (intros ha h hs hm hr)
  (exact (normalized-runs _ r (step-normalized-acts-parked w it ha h hs) hm hr)))

;; P4 in every world the step reaches: a cascade started there empties its worklist
(a/theorem cascade-done-acts-parked [w :- World, js :- (List Job)]
  (=> (= (acts-parked w) true) (= (cascade-done w js) true))
  (intro h) (exact (cascade-done-ok w js (acts-parked-well-formed w h) (acts-parked-acts-alive w h))))
