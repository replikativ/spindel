(ns spindel.v2.acts
  "The activation invariant behind P2/P4, preserved by every step, kernel-checked (Init only).

  `ga w` = inv-sample w and, for every activation A: every run row with id A.run is parked and
  holds no slice (`act-rows-good`), A.run < next-id (`act-below`), and A is its run's only
  activation (`act-sole`). It implies spindel.v2.casc's `acts-alive` (`ga-acts-alive`).

    step-acts            ga w, rule-r-safe raw -> ga (world-step w it)   (hypotheses of step-inv)
    ga-empty             ga empty-world
    raw-acts-alive       ga w -> acts-alive (raw world)
    step-normalized-ga   accepted, ga w, rule-r-safe raw -> normalized (world-step w it)   (P2)
    step-i4-ga           ... every non-done run of the step's world is live (I4)
    casc-done-ga         ga w -> casc-done w js                                            (P4)

  How: `gr P w` is the invariant generic in the per-activation run predicate; `ga` uses
  `act-rows-good`, `gx ex` (inside T6/take, between the new activation and the park) exempts
  the activations of run (:x ex), which all have id (:a ex). Primitive edits (Part B, `prims!`);
  every composite inv-sample lemma of `step-inv` re-checked for the bundle by `copy!` (138 for
  ga, 21 for gx). Overrides (Part D): resume and its callers (the resumed activation is its
  run's only one), T14's local part (the run's activations go with it), T12, the scheduling
  choice, finalize and finally regions (the run is not parked or holds the slice, so no
  activation names it: `no-act-bad`), T6 and take (`gx-act-ins` ... `gx-park`/`gx-restore`)."
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
            [spindel.v2.casc :refer :all]))

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

(a/defn gr [P :- (=> (List RunRow) ActRow Bool), w :- World] Bool
  (Bool.and (tbl-all (act-below (:next-id w)) (:acts w))
   (Bool.and (tbl-all (P (:runs w)) (:acts w)) (tbl-all (act-sole (:acts w)) (:acts w)))))
(a/defn ga-rest [w :- World] Bool (gr act-rows-good w))
(a/defn ga [w :- World] Bool (Bool.and (inv-sample w) (ga-rest w)))

;; inside T6: the activations of run x (all with id a) are exempt from good rows
(a/structure Ex [] (x Nat) (a Nat))
(a/defn act-rows-good-x [e :- Ex, rs :- (List RunRow), c :- ActRow] Bool
  (if (Nat.beq (:run c) (:x e)) (Nat.beq (:id c) (:a e)) (act-rows-good rs c)))
(a/defn gx-rest [e :- Ex, w :- World] Bool (gr (act-rows-good-x e) w))
(a/defn gx [e :- Ex, w :- World] Bool (Bool.and (inv-sample w) (gx-rest e w)))

(a/theorem ga-sample [w :- World] (=> (= (ga w) true) (= (inv-sample w) true))
  (intro h) (simp only [ga Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem ga-rest-of [w :- World] (=> (= (ga w) true) (= (ga-rest w) true))
  (intro h) (simp only [ga Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem ga-intro [w :- World] (=> (= (inv-sample w) true) (= (ga-rest w) true) (= (ga w) true))
  (intros h1 h2) (simp only [ga h1 h2 Bool.and_self]))
(a/theorem ga-parts [w :- World]
  (=> (= (ga w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (ga-sample w h))))
(a/theorem gx-sample [e :- Ex, w :- World] (=> (= (gx e w) true) (= (inv-sample w) true))
  (intro h) (simp only [gx Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem gx-rest-of [e :- Ex, w :- World] (=> (= (gx e w) true) (= (gx-rest e w) true))
  (intro h) (simp only [gx Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem gx-intro [e :- Ex, w :- World] (=> (= (inv-sample w) true) (= (gx-rest e w) true) (= (gx e w) true))
  (intros h1 h2) (simp only [gx h1 h2 Bool.and_self]))
(a/theorem gx-parts [e :- Ex, w :- World]
  (=> (= (gx e w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (gx-sample e w h))))

;; the invariant gives acts-alive (P2, P4)
(a/theorem good-for-alive [x :- Nat, r :- RunRow] (=> (= (good-for x r) true) (= (run-ok-for x r) true))
  (intro h)
  (cases hx (Nat.beq (:id r) x))
  (case [false] (simp [run-ok-for hx]))
  (case [true]
    (simp only [good-for hx Bool.not_true Bool.false_or good-row Bool.and_eq_true] at h)
    (have e (= (:act r) act-parked)) (exact (Nat.eq_of_beq_eq_true (And.left h)))
    (simp [run-ok-for run-alive e hx act-parked act-done])))

(a/theorem ga-acts-alive [w :- World] (=> (= (ga w) true) (= (acts-alive w) true))
  (intro h)
  (simp only [ga ga-rest gr Bool.and_eq_true] at h)
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

(a/theorem gr-parts [P :- (=> (List RunRow) ActRow Bool), w :- World]
  (=> (= (gr P w) true)
      (And (= (tbl-all (act-below (:next-id w)) (:acts w)) true)
           (And (= (tbl-all (P (:runs w)) (:acts w)) true) (= (tbl-all (act-sole (:acts w)) (:acts w)) true))))
  (intro h) (simp only [gr Bool.and_eq_true] at h) (exact h))

(a/theorem gr-mk [P :- (=> (List RunRow) ActRow Bool), w :- World]
  (=> (= (tbl-all (act-below (:next-id w)) (:acts w)) true) (= (tbl-all (P (:runs w)) (:acts w)) true)
      (= (tbl-all (act-sole (:acts w)) (:acts w)) true) (= (gr P w) true))
  (intros h1 h2 h3) (simp only [gr h1 h2 h3 Bool.and_self]))

(a/theorem gr-bump [P :- (=> (List RunRow) ActRow Bool), w :- World]
  (=> (= (gr P w) true) (= (gr P (bump w)) true))
  (intro h)
  (have p := (gr-parts P w h))
  (have hb (<= (:next-id w) (:next-id (bump w)))) (simp only [bump set-next-id]) (omega)
  (exact (gr-mk P (bump w) (below-mono _ _ (:acts w) hb (And.left p)) (And.left (And.right p)) (And.right (And.right p)))))

(a/theorem gr-run-upd [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hP :- (forall [rs :- (List RunRow), c :- ActRow] (= (P (tbl-upd run-id x f rs) c) (P rs c)))]
  (=> (= (gr P w) true) (= (gr P (run-upd w x f)) true))
  (intro h)
  (have p := (gr-parts P w h))
  (have h2 (= (tbl-all (P (:runs (run-upd w x f))) (:acts (run-upd w x f))) true))
  (simp only [run-upd set-runs])
  (rw [(tbl-all-congr ActRow (P (tbl-upd run-id x f (:runs w))) (P (:runs w)) (hP (:runs w)) (:acts w))])
  (exact (And.left (And.right p)))
  (exact (gr-mk P (run-upd w x f) (And.left p) h2 (And.right (And.right p)))))

(a/theorem gr-run-del [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat,
                       hP :- (forall [rs :- (List RunRow), c :- ActRow] (=> (= (P rs c) true) (= (P (tbl-del run-id x rs) c) true)))]
  (=> (= (gr P w) true) (= (gr P (run-del w x)) true))
  (intro h)
  (have p := (gr-parts P w h))
  (have h2 (= (tbl-all (P (:runs (run-del w x))) (:acts (run-del w x))) true))
  (simp only [run-del set-runs])
  (exact (tbl-all-mono ActRow (P (:runs w)) (P (tbl-del run-id x (:runs w))) (hP (:runs w)) (:acts w) (And.left (And.right p))))
  (exact (gr-mk P (run-del w x) (And.left p) h2 (And.right (And.right p)))))

(a/theorem gr-run-ins [P :- (=> (List RunRow) ActRow Bool), w :- World, r :- RunRow,
                       hP :- (forall [rs :- (List RunRow), c :- ActRow]
                               (=> (= (Nat.beq (:id r) (:run c)) false) (= (P rs c) true) (= (P (tbl-ins r rs) c) true)))]
  (=> (= (run-id r) (:next-id w)) (= (gr P w) true) (= (gr P (bump (run-ins w r))) true))
  (intros he h)
  (have p := (gr-parts P w h))
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
  (exact (gr-bump P (run-ins w r) (gr-mk P (run-ins w r) (And.left p) h2 (And.right (And.right p))))))

(a/theorem gr-act-upd [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat, f :- (=> ActRow ActRow),
                       hid :- (forall [c :- ActRow] (= (:id (f c)) (:id c))),
                       hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c))),
                       hP :- (forall [rs :- (List RunRow), c :- ActRow] (= (P rs (f c)) (P rs c)))]
  (=> (= (gr P w) true) (= (gr P (act-upd w x f)) true))
  (intro h)
  (have p := (gr-parts P w h))
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
  (exact (gr-mk P (act-upd w x f) h1 h2 h3)))

(a/theorem gr-act-del [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat]
  (=> (= (gr P w) true) (= (gr P (act-del w x)) true))
  (intro h)
  (have p := (gr-parts P w h))
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
  (exact (gr-mk P (act-del w x) h1 h2 h3)))

(a/theorem gr-filter [P :- (=> (List RunRow) ActRow Bool), w :- World, K :- (=> Nat Bool),
                      hP :- (forall [rs :- (List RunRow), c :- ActRow] (=> (= (P rs c) true) (= (P (tbl-keep K run-id rs) c) true)))]
  (=> (= (gr P w) true) (= (gr P (filter-world K w)) true))
  (intro h)
  (have p := (gr-parts P w h))
  (have h1 (= (tbl-all (act-below (:next-id (filter-world K w))) (:acts (filter-world K w))) true))
  (simp only [filter-world]) (exact (tbl-all-keep-same ActRow K act-id (act-below (:next-id w)) (:acts w) (And.left p)))
  (have h2 (= (tbl-all (P (:runs (filter-world K w))) (:acts (filter-world K w))) true))
  (simp only [filter-world])
  (exact (tbl-all-keep-same ActRow K act-id (P (tbl-keep K run-id (:runs w))) (:acts w)
           (tbl-all-mono ActRow (P (:runs w)) (P (tbl-keep K run-id (:runs w))) (hP (:runs w)) (:acts w) (And.left (And.right p)))))
  (have h3 (= (tbl-all (act-sole (:acts (filter-world K w))) (:acts (filter-world K w))) true))
  (simp only [filter-world]) (exact (sole-keep K (:acts w) (And.right (And.right p))))
  (exact (gr-mk P (filter-world K w) h1 h2 h3)))

;; ---- instances: ga-rest (P = act-rows-good) and gx-rest (P = act-rows-good-x e)

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
;; Part C. The copy of the inv-sample lemmas (as spindel.v2.casc's bc-copy!, here generic in
;; the bundle: `ga` = the invariant, `gx e` = the invariant inside T6 with run (:x e) exempt)
;; ===========================================================================

(def ^:private acts-ns *ns*)

(defn- ns-source-forms [ns-sym]
  (let [path (str (-> (name ns-sym) (str/replace "." "/") (str/replace "-" "_")) ".clj")]
    (binding [*ns* (the-ns ns-sym)]
      (with-open [r (java.io.PushbackReader. (io/reader (io/resource path)))]
        (loop [acc []]
          (let [f (read {:eof ::eof} r)]
            (if (= f ::eof) acc (recur (conj acc f)))))))))

(defn- theorem-form? [f] (and (seq? f) (contains? #{'a/theorem 'ansatz.core/theorem} (first f))))

(defn- expand-top [ns-sym f]
  (cond
    (and (seq? f) (= 'do (first f))) (mapcat #(expand-top ns-sym %) (rest f))
    (and (seq? f) (symbol? (first f)) (not (theorem-form? f)))
    (let [v (binding [*ns* (the-ns ns-sym)] (resolve (first f)))]
      (if (and (var? v) (:macro (meta v)) (= (the-ns ns-sym) (:ns (meta v))))
        (expand-top ns-sym (binding [*ns* (the-ns ns-sym)] (macroexpand-1 f)))
        [f]))
    :else [f]))

(def copy-source-nss '[spindel.v2.edits spindel.v2.step spindel.v2.rule spindel.v2.engine])

(def ^:private source-theorems
  (delay (vec (for [nsym copy-source-nss, f (ns-source-forms nsym), g (expand-top nsym f) :when (theorem-form? g)]
                [(second g) g]))))

(defn- theorem-source [nm]
  (or (some (fn [[n g]] (when (= n nm) g)) @source-theorems)
      (throw (ex-info (str "no source for theorem " nm) {:name nm}))))

(defn- binder-names [binders] (vec (take-nth 3 binders)))
(defn- inv-premise? [p] (and (seq? p) (= '= (first p)) (seq? (second p)) (= 'inv-sample (first (second p)))))

;; REPL iteration only: skip a generated theorem whose name is already in the env
(defonce ^:dynamic *acts-dev-skip* false)
(defn- declared? [s] (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str s)))))

(defn- eval-theorem! [form]
  (try (when-not (and *acts-dev-skip* (declared? (second form))) (binding [*ns* acts-ns] (eval form)))
       (catch Throwable t
         (throw (ex-info (str "acts: theorem " (second form) " failed: " (ex-message t)) {:form form} t)))))

;; a bundle: :pred (applied to the params, then the world), :params [sym type ...], :prefix,
;; :renames/:overrides/:copied atoms, :extra-args {lemma [form position]}
(defn- mk-bundle [pred params prefix extra]
  {:pred pred :params params :prefix prefix :extra-args extra
   :renames (atom {}) :overrides (atom {}) :copied (atom [])})

(defn- pargs [B] (binder-names (:params B)))
(defn- papp [B head & args] (apply list head (concat (pargs B) args)))
(defn- bsym [B suffix] (symbol (str (name (:pred B)) suffix)))

(defn- pred-subst [B x]
  (walk/postwalk (fn [y] (if (and (seq? y) (= 'inv-sample (first y))) (papp B (:pred B) (second y)) y)) x))

;; a primitive: the inv-sample lemma plus a proof of the bundle's rest part; `rest-f` is a form
;; over the binder names, premise names h0..hn and R = the rest part of the input world; nil = frame
(defn- prim-form [B orig nm rest-f]
  (let [[_ _ binders stmt] (theorem-source orig)
        prems (butlast (rest stmt))
        concl (last stmt)
        hs (vec (map-indexed (fn [i _] (symbol (str "h" i))) prems))
        i (first (keep-indexed (fn [i p] (when (inv-premise? p) i)) prems))
        w (second (second (nth prems i)))
        w2 (second (second concl))
        hi (nth hs i)
        args (concat (binder-names binders) (assoc hs i (papp B (bsym B "-sample") w hi)))
        R (papp B (bsym B "-rest-of") w hi)
        rest-term (if rest-f (walk/postwalk-replace {'R R} rest-f) (list 'Eq.trans 'e-frame R))]
    (concat
     (list 'a/theorem nm (into (vec (:params B)) binders) (pred-subst B stmt) (cons 'intros hs))
     (when-not rest-f [(list 'have 'e-frame (list '= (papp B (bsym B "-rest") w2) (papp B (bsym B "-rest") w))) '(rfl)])
     [(list 'exact (papp B (bsym B "-intro") w2 (cons orig args) rest-term))])))

(defn- prim! [B orig nm rest-f]
  (eval-theorem! (apply list (prim-form B orig nm rest-f)))
  (swap! (:renames B) assoc orig nm))

(defn- copy-name [B sym]
  (let [s (name sym) p (:prefix B)]
    (symbol (cond (str/starts-with? s "inv-") (str p (subs s 4))
                  (str/ends-with? s "-inv-sample") (str (subs s 0 (- (count s) 11)) "-" (name (:pred B)))
                  (str/ends-with? s "-inv") (str (subs s 0 (- (count s) 4)) "-" (name (:pred B)))
                  :else (str s "-" (name (:pred B)))))))

(defn- copy-subst [B x rn]
  (cond
    (and (seq? x) (= 'inv-sample (first x))) (papp B (:pred B) (copy-subst B (second x) rn))
    (and (seq? x) (symbol? (first x)) (contains? rn (first x)))
    (let [h (first x)
          args (map #(copy-subst B % rn) (rest x))
          args (if-let [[e k] ((:extra-args B) h)]
                 (do (assert (>= (count args) k) (str h " applied to too few arguments: " (pr-str x)))
                     (concat (take k args) [e] (drop k args)))
                 args)]
      (apply papp B (rn h) args))
    (seq? x) (apply list (map #(copy-subst B % rn) x))
    (vector? x) (mapv #(copy-subst B % rn) x)
    (symbol? x) (cond (contains? (:extra-args B) x) (throw (ex-info (str x " used as a value") {}))
                      (contains? rn x) (papp B (rn x))
                      :else x)
    :else x))

(defn- copy-form [B form nm rn]
  (let [[head _ binders stmt & proof] form]
    (apply list head nm (into (vec (:params B)) (copy-subst B binders rn)) (copy-subst B stmt rn)
           (map #(copy-subst B % rn) proof))))

(defn- statement-mentions-inv? [form]
  (let [[_ _ binders stmt] form] (boolean (some #{'inv-sample} (flatten (list (seq binders) stmt))))))

(defn- closure [B root]
  (let [thms @source-theorems
        S (set (keep (fn [[n g]] (when (statement-mentions-inv? g) n)) thms))
        deps (fn [n]
               (cond (contains? @(:renames B) n) []
                     (contains? @(:overrides B) n) (:deps (get @(:overrides B) n))
                     :else (let [[_ _ _ _ & proof] (theorem-source n)]
                             (filter S (filter symbol? (flatten proof))))))]
    (loop [todo [root] seen #{}]
      (if-let [n (first todo)]
        (if (seen n) (recur (rest todo) seen) (recur (concat (rest todo) (deps n)) (conj seen n)))
        (filterv seen (map first thms))))))

(defn copy!
  "Check the bundle version of every inv-sample lemma `root` depends on, in load order."
  [B root]
  (doseq [n (closure B root) :when (not (contains? @(:renames B) n))]
    (let [form (if-let [o (get @(:overrides B) n)]
                 (:form o)
                 (copy-form B (theorem-source n) (copy-name B n) @(:renames B)))]
      (eval-theorem! form)
      (swap! (:renames B) assoc n (second form))
      (swap! (:copied B) conj (second form)))))

(defn- override! [B orig deps form] (swap! (:overrides B) assoc orig {:deps deps :form form}))

(def GA (mk-bundle 'ga [] "ga-"
          {'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (good-row r))) 4]
           'inv-act-upd ['(fn [c :- ActRow] (Eq.refl (:run c))) 4]}))
(def GX (mk-bundle 'gx '[ex :- Ex] "gx-"
          {'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (good-row r))) 4]
           'inv-act-upd ['(fn [c :- ActRow] (Eq.refl (:run c))) 4]}))

;; ---- the primitives

(a/theorem gr-mark-edge [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat] (= (gr P (mark-edge w x)) (gr P w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem gr-unmark-edge [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat] (= (gr P (unmark-edge w x)) (gr P w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem gr-remove-edge [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat] (= (gr P (remove-edge w x)) (gr P w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))

(a/theorem ga-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hg :- (forall [r :- RunRow] (= (good-row (f r)) (good-row r)))]
  (=> (= (ga w) true) (= (ga (run-upd w x f)) true))
  (intro h)
  (exact (ga-intro _ (inv-run-upd w x f hf (ga-sample w h))
           (gr-run-upd act-rows-good w x f (arg-upd x f hf hg) (ga-rest-of w h)))))
(a/theorem gx-run-upd [e :- Ex, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hg :- (forall [r :- RunRow] (= (good-row (f r)) (good-row r)))]
  (=> (= (gx e w) true) (= (gx e (run-upd w x f)) true))
  (intro h)
  (exact (gx-intro e _ (inv-run-upd w x f hf (gx-sample e w h))
           (gr-run-upd (act-rows-good-x e) w x f (argx-upd e x f hf hg) (gx-rest-of e w h)))))

(a/theorem ga-act-upd [w :- World, x :- Nat, f :- (=> ActRow ActRow),
                       hf :- (forall [r :- ActRow] (= (act-id (f r)) (act-id r))),
                       hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c)))]
  (=> (= (ga w) true) (= (ga (act-upd w x f)) true))
  (intro h)
  (exact (ga-intro _ (inv-act-upd w x f hf (ga-sample w h))
           (gr-act-upd act-rows-good w x f hf hr (fn [rs :- (List RunRow), c :- ActRow] (arg-act rs f hr c)) (ga-rest-of w h)))))
(a/theorem gx-act-upd [e :- Ex, w :- World, x :- Nat, f :- (=> ActRow ActRow),
                       hf :- (forall [r :- ActRow] (= (act-id (f r)) (act-id r))),
                       hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c)))]
  (=> (= (gx e w) true) (= (gx e (act-upd w x f)) true))
  (intro h)
  (exact (gx-intro e _ (inv-act-upd w x f hf (gx-sample e w h))
           (gr-act-upd (act-rows-good-x e) w x f hf hr (fn [rs :- (List RunRow), c :- ActRow] (argx-act e rs f hf hr c))
             (gx-rest-of e w h)))))

(doseq [B [GA GX]]
  (swap! (:renames B) assoc 'inv-run-upd (bsym B "-run-upd") 'inv-act-upd (bsym B "-act-upd") 'inv-parts (bsym B "-parts")))

(defn- prims! [B P del-f keep-f ins-f]
  (doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-task-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del
              inv-set-pins inv-resource-del inv-scope-del inv-cleanup-ins
              inv-edge-upd inv-drop-cred inv-drop-edges inv-comp-del-unref inv-comp-upd]]
    (prim! B o (copy-name B o) nil))
  (doseq [o '[inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-task-ins-fresh inv-comp-ins-fresh]]
    (prim! B o (copy-name B o) (list 'gr-bump P (list (symbol (str/replace (subs (name o) 4) "-fresh" "")) 'w 'r)
                                     (list 'Eq.trans '(rfl) 'R))))
  (prim! B 'inv-bump (copy-name B 'inv-bump) (list 'gr-bump P 'w 'R))
  (prim! B 'mark-edge-inv-sample (copy-name B 'mark-edge-inv-sample) (list 'Eq.trans (list 'gr-mark-edge P 'w 'x) 'R))
  (prim! B 'unmark-edge-inv-sample (copy-name B 'unmark-edge-inv-sample) (list 'Eq.trans (list 'gr-unmark-edge P 'w 'x) 'R))
  (prim! B 'inv-remove-edge (copy-name B 'inv-remove-edge) (list 'Eq.trans (list 'gr-remove-edge P 'w 'x) 'R))
  (prim! B 'insert-edge-fresh-inv-sample (copy-name B 'insert-edge-fresh-inv-sample)
         (list 'gr-bump P '(insert-edge w (edge-set-id (:next-id w) e)) (list 'Eq.trans '(rfl) 'R)))
  (prim! B 'inv-run-del (copy-name B 'inv-run-del) (list 'gr-run-del P 'w 'x del-f 'R))
  (prim! B 'inv-run-ins-fresh (copy-name B 'inv-run-ins-fresh) (list 'gr-run-ins P 'w 'r ins-f 'h0 'R))
  (prim! B 'inv-drop-act (copy-name B 'inv-drop-act) (list 'gr-act-del P '(drop-cred-edges w a) 'a (list 'Eq.trans '(rfl) 'R)))
  (prim! B 'inv-filter-world (copy-name B 'inv-filter-world) (list 'gr-filter P 'w 'K keep-f 'R)))

(prims! GA 'act-rows-good '(arg-del x) '(arg-keep K) '(arg-ins r))
(prims! GX '(act-rows-good-x ex) '(argx-del ex x) '(argx-keep ex K) '(argx-ins ex r))

;; ===========================================================================
;; Part D. The overrides: where an edit changes a run row that has an activation
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

(a/theorem gr-run-upd-free [P :- (=> (List RunRow) ActRow Bool), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                            hP :- (forall [rs :- (List RunRow), c :- ActRow]
                                    (=> (= (act-of-run x c) false) (= (P (tbl-upd run-id x f rs) c) (P rs c))))]
  (=> (= (tbl-any (act-of-run x) (:acts w)) false) (= (gr P w) true) (= (gr P (run-upd w x f)) true))
  (intros hn h)
  (have p := (gr-parts P w h))
  (have hin (forall [c :- ActRow] (=> (= (bnot-of (act-of-run x) c) true) (= (P (:runs w) c) true)
                                      (= (P (tbl-upd run-id x f (:runs w)) c) true))))
  (intros c h1 h2) (simp only [bnot-of] at h1) (rw [(hP (:runs w) c (bnot-true _ h1))]) (exact h2)
  (have h2 (= (tbl-all (P (:runs (run-upd w x f))) (:acts (run-upd w x f))) true))
  (simp only [run-upd set-runs])
  (exact (tbl-all-mono2 ActRow (bnot-of (act-of-run x)) (P (:runs w)) (P (tbl-upd run-id x f (:runs w)))
           hin (:acts w) (any-false-all ActRow (act-of-run x) (:acts w) hn) (And.left (And.right p))))
  (exact (gr-mk P (run-upd w x f) (And.left p) h2 (And.right (And.right p)))))

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

(a/theorem ga-sole [w :- World, a :- ActRow] (=> (= (ga w) true) (List.Mem a (:acts w)) (= (act-sole (:acts w) a) true))
  (intros h hm) (exact (tbl-all-mem ActRow (act-sole (:acts w)) a (:acts w) (And.right (And.right (gr-parts _ w (ga-rest-of w h)))) hm)))
(a/theorem gx-sole [e :- Ex, w :- World, a :- ActRow] (=> (= (gx e w) true) (List.Mem a (:acts w)) (= (act-sole (:acts w) a) true))
  (intros h hm) (exact (tbl-all-mem ActRow (act-sole (:acts w)) a (:acts w) (And.right (And.right (gr-parts _ w (gx-rest-of e w h)))) hm)))

(a/theorem ga-resume-o [w :- World, a :- ActRow]
  (=> (= (act-sole (:acts w) a) true) (= (ga w) true) (= (ga (resume w a)) true))
  (intros hs h)
  (have h1 := (ga-drop-act w (:id a) h))
  (have hn (= (tbl-any (act-of-run (:run a)) (:acts (drop-act w (:id a)))) false))
  (exact (sole-drop-free a (:acts w) hs))
  (exact (ga-intro _ (inv-resume w a (ga-sample w h))
           (gr-run-upd-free act-rows-good _ (:run a) run-wake
             (fn [rs :- (List RunRow), c :- ActRow, hc :- (= (act-of-run (:run a) c) false)]
               (arg-upd-free (:run a) run-wake run-wake-run-id rs c hc))
             hn (ga-rest-of _ h1)))))

(a/theorem gx-resume-o [e :- Ex, w :- World, a :- ActRow]
  (=> (= (act-sole (:acts w) a) true) (= (gx e w) true) (= (gx e (resume w a)) true))
  (intros hs h)
  (have h1 := (gx-drop-act e w (:id a) h))
  (have hn (= (tbl-any (act-of-run (:run a)) (:acts (drop-act w (:id a)))) false))
  (exact (sole-drop-free a (:acts w) hs))
  (exact (gx-intro e _ (inv-resume w a (gx-sample e w h))
           (gr-run-upd-free (act-rows-good-x e) _ (:run a) run-wake
             (fn [rs :- (List RunRow), c :- ActRow, hc :- (= (act-of-run (:run a) c) false)]
               (argx-upd-free e (:run a) run-wake run-wake-run-id rs c hc))
             hn (gx-rest-of e _ h1)))))

;; a hand-written bundle proof, generic in the bundle: `$name` is the bundle's lemma
;; <prefix>name applied to the bundle's parameters (in head position or as a value), `(%G w)` is
;; the bundle predicate of w; the theorem gets the parameters as its first binders
(defn- inst [B form]
  (letfn [(dsym? [x] (and (symbol? x) (str/starts-with? (name x) "$")))
          (dname [x] (symbol (str (:prefix B) (subs (name x) 1))))
          (walk [x]
            (cond
              (and (seq? x) (= '%G (first x))) (papp B (:pred B) (walk (second x)))
              (and (seq? x) (dsym? (first x))) (apply papp B (dname (first x)) (map walk (rest x)))
              (seq? x) (apply list (map walk x))
              (vector? x) (mapv walk x)
              (dsym? x) (papp B (dname x))
              :else x))]
    (let [[head nm binders & more] form]
      (apply list head (if (dsym? nm) (dname nm) nm) (into (vec (:params B)) (walk binders)) (map walk more)))))

(defn- override-both! [orig deps form]
  (doseq [B [GA GX]] (override! B orig deps (inst B form))))

(override-both! 'inv-resume '[inv-drop-act]
  '(a/theorem $resume [w :- World, a :- ActRow]
     (=> (= (act-sole (:acts w) a) true) (= (%G w) true) (= (%G (resume w a)) true))
     (intros hs h) (exact ($resume-o w a hs h))))

(override-both! 'inv-fill-slot '[inv-resume]
  '(a/theorem $fill-slot [w :- World, a :- ActRow, x :- Nat, v :- RunResult]
     (=> (= (act-sole (:acts w) a) true) (= (%G w) true) (= (%G (fill-slot w a x v)) true))
     (intros hs h)
     (cases hm (act-ready (act-fill x v a)))
     (simp only [fill-slot hm])
     (exact ($act-upd w (:id a) (act-fill x v) (act-fill-act-id x v) (fn [c :- ActRow] (Eq.refl (:run c))) h))
     (simp only [fill-slot hm]) (exact ($resume w a hs h))))

(override-both! 'inv-fire-dep '[inv-invalidate inv-fill-slot inv-dep-consumed]
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

(override-both! 'inv-fire-wait-act '[inv-edge-set-phase inv-fill-slot]
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

(copy! GX 'inv-fire-edge)

;; ---- T14's local part: the run is done and every activation of it is gone

(a/defn arg-or [x :- Nat, rs :- (List RunRow), c :- ActRow] Bool (Bool.or (act-of-run x c) (act-rows-good rs c)))

(a/theorem gr-fold-drop [P :- (=> (List RunRow) ActRow Bool), ids :- (List Nat)]
  (forall [w :- World] (=> (= (gr P w) true) (= (gr P (nat-fold drop-act w ids)) true)))
  (induction ids)
  (case [nil] (intros w h) (simp only [nat-fold]) (exact h))
  (case [cons h t ih]
    (intros w hw) (simp only [nat-fold])
    (exact (ih (drop-act w h) (gr-act-del P (drop-cred-edges w h) h hw)))))

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

(a/theorem ga-cancel-acts-o [w :- World, x :- Nat]
  (=> (= (ga w) true) (= (ga (cancel-acts (run-upd w x run-cancel-row) x)) true))
  (intro h)
  (have p := (gr-parts act-rows-good w (ga-rest-of w h)))
  (have g1 (= (gr (arg-or x) (run-upd w x run-cancel-row)) true))
  (exact (gr-mk (arg-or x) (run-upd w x run-cancel-row) (And.left p)
           (tbl-all-mono ActRow (act-rows-good (:runs w)) (arg-or x (tbl-upd run-id x run-cancel-row (:runs w)))
             (arg-or-cancel w x) (:acts w) (And.left (And.right p)))
           (And.right (And.right p))))
  (have g2 (= (gr (arg-or x) (cancel-acts (run-upd w x run-cancel-row) x)) true))
  (simp only [cancel-acts])
  (exact (gr-fold-drop (arg-or x) (tbl-scan act-id (act-of-run x) (:acts w)) (run-upd w x run-cancel-row) g1))
  (have hc (= (tbl-all (covers-ids act-id (act-of-run x) (List.nil Nat)) (:acts (cancel-acts (run-upd w x run-cancel-row) x))) true))
  (simp only [cancel-acts])
  (exact (fold-covers x (tbl-scan act-id (act-of-run x) (:acts w)) (run-upd w x run-cancel-row)
           (scan-covers-ids ActRow act-id (act-of-run x) (:acts w))))
  (have p2 := (gr-parts (arg-or x) (cancel-acts (run-upd w x run-cancel-row) x) g2))
  (have h2 (= (tbl-all (act-rows-good (:runs (cancel-acts (run-upd w x run-cancel-row) x))) (:acts (cancel-acts (run-upd w x run-cancel-row) x))) true))
  (exact (tbl-all-mono2 ActRow (covers-ids act-id (act-of-run x) (List.nil Nat))
           (arg-or x (:runs (cancel-acts (run-upd w x run-cancel-row) x)))
           (act-rows-good (:runs (cancel-acts (run-upd w x run-cancel-row) x)))
           (arg-or-clean x (:runs (cancel-acts (run-upd w x run-cancel-row) x)))
           (:acts (cancel-acts (run-upd w x run-cancel-row) x)) hc (And.left (And.right p2))))
  (exact (ga-intro (cancel-acts (run-upd w x run-cancel-row) x)
           (inv-cancel-acts (run-upd w x run-cancel-row) x (inv-run-upd w x run-cancel-row run-cancel-row-id (ga-sample w h)))
           (gr-mk act-rows-good (cancel-acts (run-upd w x run-cancel-row) x) (And.left p2) h2 (And.right (And.right p2))))))

(override! GA 'inv-cancel-run-local '[inv-cancel-debtor inv-cleanup-set inv-cancel-res]
  '(a/theorem ga-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
     (=> (= (ga w) true) (= (ga (cancel-run-local w r rep)) true))
     (intro h)
     (simp only [cancel-run-local])
     (exact (ga-cancel-debtor rep _ r (ga-cleanup-set _ (:id r) _ (ga-cancel-res _ r (ga-cancel-acts-o w (:id r) h)))))))

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
  (=> (= (ga w) true) (List.Mem r (:runs w)) (= (good-row r) false) (= (tbl-any (act-of-run (:id r)) (:acts w)) false))
  (intros h hm hg)
  (have p := (gr-parts act-rows-good w (ga-rest-of w h)))
  (exact (all-bnot-any ActRow (act-of-run (:id r)) (:acts w)
           (tbl-all-mono ActRow (act-rows-good (:runs w)) (bnot-of (act-of-run (:id r)))
             (fn [c :- ActRow, hc :- (= (act-rows-good (:runs w) c) true)] (no-act-one r (:runs w) c hm hg hc))
             (:acts w) (And.left (And.right p))))))

(a/theorem ga-run-upd-free [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                            hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r)))]
  (=> (= (tbl-any (act-of-run x) (:acts w)) false) (= (ga w) true) (= (ga (run-upd w x f)) true))
  (intros hn h)
  (exact (ga-intro (run-upd w x f) (inv-run-upd w x f hid (ga-sample w h))
           (gr-run-upd-free act-rows-good w x f (arg-upd-free x f hid) hn (ga-rest-of w h)))))

(a/theorem find-facts [w :- World, rid :- Nat, r :- RunRow]
  (=> (= (run-find w rid) (Option.some RunRow r)) (And (List.Mem r (:runs w)) (= (:id r) rid)))
  (intro h) (exact (And.intro (tbl-find-mem RunRow run-id rid r (:runs w) h) (tbl-find-id RunRow run-id rid r (:runs w) h))))

(a/theorem ga-free-of-tok [w :- World, st :- Nat, r :- RunRow]
  (=> (= (ga w) true) (= (tok-run w st) (Option.some RunRow r)) (= (tbl-any (act-of-run (:id r)) (:acts w)) false))
  (intros h ht)
  (have p := (tok-facts w st r ht))
  (exact (no-act-bad w r h (And.left p) (slice-not-good r (And.right p)))))

;; ---- T12, the scheduling choice, finalize, finally regions: the token or chosen run has no activation

(override! GA 'inv-complete-raw '[inv-fin-if-final inv-run-cascade inv-retire-after inv-complete-body]
  '(a/theorem ga-complete-raw [w :- World, r :- RunRow, res :- RunResult]
     (=> (= (tbl-any (act-of-run (:id r)) (:acts w)) false) (= (ga w) true) (= (ga (complete-raw w r res)) true))
     (intros hn h)
     (have h0 := (ga-run-upd-free w (:id r) run-complete-row run-complete-row-id hn h))
     (simp only [complete-raw])
     (exact (ga-fin-if-final _ (:of r) (ga-run-cascade _ _ (ga-retire-after _ (:id r) (ga-complete-body _ r res h0)))))))

(override! GA 't12-inv '[inv-complete-raw]
  '(a/theorem t12-ga [w :- World, st :- Nat, tag :- Nat, v :- Nat]
     (=> (= (ga w) true) (= (ga (:world (t12-complete w st tag v))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t12-complete ht refuse]) (exact h)
     (cases hn (run-normal r))
     (simp only [t12-complete ht hn refuse]) (exact h)
     (simp only [t12-complete ht hn accept]) (exact (ga-complete-raw w r _ (ga-free-of-tok w st r h ht) h))))

(a/theorem active-not-good [r :- RunRow] (=> (= (Nat.beq (:act r) act-active) true) (= (good-row r) false))
  (intro h)
  (have e (= (:act r) act-active)) (exact (Nat.eq_of_beq_eq_true h))
  (simp [good-row e act-active act-parked]))
(a/theorem done-not-good [r :- RunRow] (=> (= (Nat.beq (:act r) act-done) true) (= (good-row r) false))
  (intro h)
  (have e (= (:act r) act-done)) (exact (Nat.eq_of_beq_eq_true h))
  (simp [good-row e act-done act-parked]))

(override! GA 'sched-inv '[]
  '(a/theorem sched-ga [w :- World, rid :- Nat]
     (=> (= (ga w) true) (= (ga (:world (t-schedule w rid))) true))
     (intro h)
     (cases hf (run-find w rid)) (case' [some r]) (case' [none])
     (simp only [t-schedule hf refuse]) (exact h)
     (cases hg (sched-ok w r))
     (simp only [t-schedule hf hg refuse]) (exact h)
     (have p := (find-facts w rid r hf))
     (have hg2 := hg)
     (simp only [sched-ok Bool.and_eq_true] at hg2)
     (have hn := (no-act-bad w r h (And.left p) (active-not-good r (And.left hg2))))
     (rw [(And.right p)] at hn)
     (simp only [t-schedule hf hg accept]) (exact (ga-run-upd-free w rid run-enter-row run-enter-row-id hn h))))

(override! GA 't-finalize-inv '[]
  '(a/theorem t-finalize-ga [w :- World, rid :- Nat]
     (=> (= (ga w) true) (= (ga (:world (t-finalize w rid))) true))
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
     (simp only [t-finalize hf hg accept]) (exact (ga-run-upd-free w rid run-enter-row run-enter-row-id hn h))))

(override! GA 't-finally-enter-inv '[]
  '(a/theorem t-finally-enter-ga [w :- World, st :- Nat]
     (=> (= (ga w) true) (= (ga (:world (t-finally-enter w st))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t-finally-enter ht refuse]) (exact h)
     (cases hg (run-normal r))
     (simp only [t-finally-enter ht hg refuse]) (exact h)
     (simp only [t-finally-enter ht hg accept])
     (exact (ga-run-upd-free w (:id r) (run-fin-push (Finalizer.mk 0 (:effect-index r) (List.nil Nat)))
              (run-fin-push-id _) (ga-free-of-tok w st r h ht) h))))

(override! GA 't-finally-exit-inv '[]
  '(a/theorem t-finally-exit-ga [w :- World, st :- Nat]
     (=> (= (ga w) true) (= (ga (:world (t-finally-exit w st))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t-finally-exit ht refuse]) (exact h)
     (have hn := (ga-free-of-tok w st r h ht))
     (cases he (fins-empty (:finalizers r)))
     (case [true] (simp only [t-finally-exit ht he refuse]) (exact h))
     (case [false] (simp only [t-finally-exit ht he accept]) (exact (ga-run-upd-free w (:id r) run-fin-pop run-fin-pop-id hn h)))))

(override! GA 't-slice-exit-inv '[inv-run-cascade]
  '(a/theorem t-slice-exit-ga [w :- World, rid :- Nat]
     (=> (= (ga w) true) (= (ga (:world (t-slice-exit w rid))) true))
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
     (simp only [t-slice-exit hf hg accept retire-full])
     (exact (ga-run-cascade _ _ (ga-run-upd-free w rid run-fin-pop-end run-fin-pop-end-id hn h)))))

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
  (=> (= (inv-sample w) true) (List.Mem r (:runs w)) (< (:id r) (:next-id w)))
  (intros h hm)
  (have hi := (And.right (And.right (inv-parts w h))))
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

(a/theorem gx-act-ins [w :- World, a :- ActRow]
  (=> (= (act-id a) (:next-id w)) (< (:run a) (:next-id w)) (= (tbl-any (act-of-run (:run a)) (:acts w)) false)
      (= (ga w) true) (= (gx (Ex.mk (:run a) (:next-id w)) (bump (act-ins w a))) true))
  (intros hid hlt hn h)
  (have p := (gr-parts act-rows-good w (ga-rest-of w h)))
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
  (exact (gx-intro (Ex.mk (:run a) (:next-id w)) (bump (act-ins w a)) (inv-act-ins-fresh w a hid (ga-sample w h))
           (gr-bump (act-rows-good-x (Ex.mk (:run a) (:next-id w))) (act-ins w a)
             (gr-mk (act-rows-good-x (Ex.mk (:run a) (:next-id w))) (act-ins w a) g1 g2 g3)))))

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

(a/theorem gx-restore [ex :- Ex, w :- World, f :- (=> RunRow RunRow),
                       hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hg :- (forall [r :- RunRow] (= (good-row (f r)) true))]
  (=> (= (gx ex w) true) (= (ga (run-upd w (:x ex) f)) true))
  (intro h)
  (have p := (gr-parts (act-rows-good-x ex) w (gx-rest-of ex w h)))
  (have g2 (= (tbl-all (act-rows-good (:runs (run-upd w (:x ex) f))) (:acts (run-upd w (:x ex) f))) true))
  (simp only [run-upd set-runs])
  (exact (tbl-all-mono ActRow (act-rows-good-x ex (:runs w)) (act-rows-good (tbl-upd run-id (:x ex) f (:runs w)))
           (arg-restore ex f hid hg (:runs w)) (:acts w) (And.left (And.right p))))
  (exact (ga-intro (run-upd w (:x ex) f) (inv-run-upd w (:x ex) f hid (gx-sample ex w h))
           (gr-mk act-rows-good (run-upd w (:x ex) f) (And.left p) g2 (And.right (And.right p))))))

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

(a/theorem gx-park [ex :- Ex, w :- World]
  (=> (= (gx ex w) true) (= (ga (park-if w (:a ex) (:x ex))) true))
  (intro h)
  (cases ha (act-has w (:a ex)))
  (case [true] (simp only [park-if ha]) (exact (gx-restore ex w run-park-row run-park-row-id run-park-row-good h)))
  (case [false]
    (simp only [park-if ha])
    (have p := (gr-parts (act-rows-good-x ex) w (gx-rest-of ex w h)))
    (have hb := (has-false-all (:a ex) (:acts w) ha))
    (exact (ga-intro w (gx-sample ex w h)
             (gr-mk act-rows-good w (And.left p)
               (tbl-all-mono2 ActRow (bnot-of (act-id-is (:a ex))) (act-rows-good-x ex (:runs w)) (act-rows-good (:runs w))
                 (arg-gone ex (:runs w)) (:acts w) hb (And.left (And.right p)))
               (And.right (And.right p)))))))

(copy! GX 'nat-fold-inv)
(copy! GX 'inv-demand-reactive)
(copy! GX 'inv-await-wire)
(copy! GX 'inv-fast-fill)
(copy! GX 'inv-insert-edge-checked)

(copy! GA 'inv-fin-if-final)
(copy! GA 'nat-fold-inv)

(a/theorem ga-await-raw-o [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (List.Mem r (:runs w)) (= (:slice r) true) (= (ga w) true) (= (ga (await-raw w r ds mode k mine)) true))
  (intros hm hs h)
  (have hn := (no-act-bad w r h hm (slice-not-good r hs)))
  (have hlt := (run-below w r (ga-sample w h) hm))
  (have h1 := (ga-run-upd w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (good-row q))) h))
  (have h2 := (gx-act-ins (run-upd w (:id r) run-tick)
                (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine)
                (rfl) hlt hn h1))
  (have h3 := (nat-fold-gx (Ex.mk (:id r) (:next-id w)) demand-reactive (gx-demand-reactive (Ex.mk (:id r) (:next-id w)))
                (nat-distinct ds) _ h2))
  (have h4 (= (gx (Ex.mk (:id r) (:next-id w)) (:world (await-acc w r ds mode k mine))) true))
  (exact (gx-await-wire (Ex.mk (:id r) (:next-id w)) r (:next-id w) mode k (nat-distinct ds)
           (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) h3))
  (have h5 := (gx-act-upd (Ex.mk (:id r) (:next-id w)) (:world (await-acc w r ds mode k mine)) (:next-id w)
                (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds))
                (act-set-members-id (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds))
                (fn [c :- ActRow] (Eq.refl (:run c))) h4))
  (have h6 := (nat-fold-gx (Ex.mk (:id r) (:next-id w)) (fast-fill (:pairs (await-acc w r ds mode k mine)))
                (gx-fast-fill (Ex.mk (:id r) (:next-id w)) (:pairs (await-acc w r ds mode k mine))) (nat-distinct ds) _ h5))
  (have h7 := (gx-park (Ex.mk (:id r) (:next-id w)) _ h6))
  (simp only [await-raw await-post])
  (exact (nat-fold-ga fin-if-final ga-fin-if-final (nat-distinct ds) _ h7)))

(a/theorem ga-take-park-o [w :- World, r :- RunRow, x :- Nat, k :- Nat]
  (=> (List.Mem r (:runs w)) (= (:slice r) true) (= (ga w) true) (= (ga (take-park w r x k)) true))
  (intros hm hs h)
  (have hn := (no-act-bad w r h hm (slice-not-good r hs)))
  (have hlt := (run-below w r (ga-sample w h) hm))
  (have h2 := (gx-act-ins w (take-act w r k) (rfl) hlt hn h))
  (have h3 := (gx-insert-edge-checked (Ex.mk (:id r) (:next-id w)) _ (take-edge r (:next-id w) x) h2))
  (simp only [take-park])
  (exact (gx-restore (Ex.mk (:id r) (:next-id w)) _ run-tick-park run-tick-park-id run-tick-park-good h3)))

(override! GA 'inv-await-raw '[]
  '(a/theorem ga-await-raw [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
     (=> (List.Mem r (:runs w)) (= (:slice r) true) (= (ga w) true) (= (ga (await-raw w r ds mode k mine)) true))
     (intros hm hs h) (exact (ga-await-raw-o w r ds mode k mine hm hs h))))

(override! GA 't6-inv '[inv-await-raw]
  '(a/theorem t6-ga [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
     (=> (= (ga w) true) (= (ga (:world (t6-await w st ds mode k fresh mine))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t6-await ht refuse]) (exact h)
     (have p := (tok-facts w st r ht))
     (cases hg (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
     (simp only [t6-await ht hg refuse]) (exact h)
     (simp only [t6-await ht hg accept])
     (exact (ga-await-raw w r ds mode k mine (And.left p) (And.right p) h))))

(override! GA 'inv-take-park '[]
  '(a/theorem ga-take-park [w :- World, r :- RunRow, x :- Nat, k :- Nat]
     (=> (List.Mem r (:runs w)) (= (:slice r) true) (= (ga w) true) (= (ga (take-park w r x k)) true))
     (intros hm hs h) (exact (ga-take-park-o w r x k hm hs h))))

(override! GA 't-take-inv '[inv-take-park inv-take-now]
  '(a/theorem t-take-ga [w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
     (=> (= (ga w) true) (= (ga (:world (t-take w st x k fresh))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t-take ht refuse]) (exact h)
     (have p := (tok-facts w st r ht))
     (cases hs (source-find w x)) (case' [some s]) (case' [none])
     (simp only [t-take ht hs refuse]) (exact h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (takeable s))))
     (simp only [t-take ht hs hg refuse]) (exact h)
     (cases hv (take-ready s))
     (simp only [t-take ht hs hg hv accept]) (exact (ga-take-park w r x k (And.left p) (And.right p) h))
     (simp only [t-take ht hs hg hv accept]) (exact (ga-take-now w r x h))))

;; Z#55: arm = arm-raw (frame for ga) then take-park on the armed row (still the slice holder)
(override! GA 'inv-arm-park '[inv-take-park inv-arm-raw]
  '(a/theorem ga-arm-park [w :- World, r :- RunRow, kind :- Nat, k :- Nat]
     (=> (List.Mem r (:runs w)) (= (:slice r) true) (= (ga w) true) (= (ga (arm-park w r kind k)) true))
     (intros hm hs h)
     (simp only [arm-park])
     (exact (ga-take-park _ (run-arm (:next-id w) r) (:next-id w) k (arm-raw-mem w r kind hm) hs (ga-arm-raw w r kind h)))))

(override! GA 't17-inv '[inv-arm-park]
  '(a/theorem t17-ga [w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
     (=> (= (ga w) true) (= (ga (:world (t17-arm w st kind k fresh))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t17-arm ht refuse]) (exact h)
     (have p := (tok-facts w st r ht))
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind))))
     (simp only [t17-arm ht hg refuse]) (exact h)
     (simp only [t17-arm ht hg accept]) (exact (ga-arm-park w r kind k (And.left p) (And.right p) h))))

(copy! GA 'step-inv)

;; ===========================================================================
;; Part E. The step
;; ===========================================================================

(a/theorem ga-empty [] (= (ga empty-world) true) (rfl))

;; every step keeps the activation invariant (the hypotheses of step-inv)
(a/theorem step-acts [w :- World, it :- Item]
  (=> (= (ga w) true) (= (rule-r-safe (:world (raw w it))) true) (= (ga (:world (world-step w it))) true))
  (intros h hs) (exact (step-ga w it h hs)))

;; P2 and P4 hold in every world of the model: the raw world of a step has no activation of a
;; done run
(a/theorem raw-acts-alive [w :- World, it :- Item]
  (=> (= (ga w) true) (= (acts-alive (:world (raw w it))) true))
  (intro h) (exact (ga-acts-alive _ (raw-ga w it h))))

;; Theorem: the step's world is normalized, with no normalized flag (hypotheses of step-inv)
(a/theorem step-normalized-ga [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) true) (= (ga w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (normalized (:world (world-step w it))) true))
  (intros ha h hs)
  (exact (step-normalized-ok w it ha (ga-sample w h) (raw-acts-alive w it h) hs)))

;; I4 after every accepted step
(a/theorem step-i4-ga [w :- World, it :- Item, r :- RunRow]
  (=> (= (:accepted (raw w it)) true) (= (ga w) true) (= (rule-r-safe (:world (raw w it))) true)
      (List.Mem r (:runs (:world (world-step w it)))) (= (run-alive r) true)
      (= (in-live (:world (world-step w it)) (:id r)) true))
  (intros ha h hs hm hr)
  (exact (normalized-runs _ r (step-normalized-ga w it ha h hs) hm hr)))

;; P4 in every world the step reaches: a cascade started there empties its worklist
(a/theorem casc-done-ga [w :- World, js :- (List Job)]
  (=> (= (ga w) true) (= (casc-done w js) true))
  (intro h) (exact (casc-done-ok w js (ga-sample w h) (ga-acts-alive w h))))
