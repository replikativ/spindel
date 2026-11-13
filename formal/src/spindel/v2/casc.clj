(ns spindel.v2.casc
  "Obligations P4 (cascade completion) and P2 (normalization terminates), kernel-checked (Init only).

  Hypothesis of both: `acts-alive w` (every run row whose id is an activation's run is not done).
  inv-sample does not imply it: `resume` sets its run active, so a done run that kept an
  activation would be revived. spindel.v2.acts proves it for every world the step reaches.

    casc-done-ok         inv-sample w, acts-alive w -> casc-done w js                      (P4)
    normalized-ok        inv-sample w, acts-alive w -> normalized (normalize w)             (P2)
    rule-r-normalized-ok ... and rule-r-safe w -> normalized (normalize (rule-r-pre w))
    step-normalized-ok, step-i4-ok   the step theorems without the `normalized` flag

  P4 (Part D): potential `casc-pot n w js` = jobs (a jclose weighs n+1) + (n+1) #alive runs +
  n #run rows; with n the initial #run rows, every pop lowers it by >= 1 (`casc-step-pot`: an
  acting cancel lowers #alive and queues <= #alive + 1 jobs, an acting retire lowers #rows and
  queues <= #alive, an acting close queues <= #alive <= n; nothing ever raises #alive or #rows),
  and it starts below `casc-fuel` (`casc-fuel-above`).
  Monotonicity: the bundle `bc b w` = inv-sample, acts-alive, #alive <= (:alive b), #rows <=
  (:rows b), the ids of the non-idle computations = (:active b), proved per primitive edit
  (Part B) and copied for the 38 composite cascade lemmas by `bc-copy!` (the inv-sample proof
  re-checked with the bundle; overrides: resume and its callers, T14's local part).
  P2 (Part E): `round-lt` (a round of a non-normalized world lowers `norm-measure`: the first
  stray run's cancel acts, else the first stray computation is demoted (idle or removed); unique
  ids pick the stray row), `bn-round-lv` (no count grows: bundle `bn`), `norm-loop-ok`."
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
            [spindel.v2.engine :refer :all]))

;; ===========================================================================
;; Part A. The cascade bundle
;; ===========================================================================

;; every run row whose id is an activation's run is alive (no activation of a done run)
(a/defn run-ok-for [x :- Nat, r :- RunRow] Bool (Bool.or (Bool.not (Nat.beq (:id r) x)) (run-alive r)))
(a/defn act-run-ok [rs :- (List RunRow), a :- ActRow] Bool (tbl-all (run-ok-for (:run a)) rs))
(a/defn acts-alive [w :- World] Bool (tbl-all (act-run-ok (:runs w)) (:acts w)))

(a/defn run-any [r :- RunRow] Bool true)
(a/defn alive-cnt [w :- World] Nat (tbl-count run-alive (:runs w)))
(a/defn row-cnt [w :- World] Nat (tbl-count run-any (:runs w)))
(a/defn active-ids [w :- World] (List Nat) (tbl-scan comp-id comp-active (:comps w)))

;; bounds: #alive runs <= alive, #run rows <= rows, the non-idle computations' ids = active
(a/structure Bnd [] (alive Nat) (rows Nat) (active (List Nat)))
(a/defn bc-rest [b :- Bnd, w :- World] Bool
  (Bool.and (acts-alive w)
   (Bool.and (Nat.ble (alive-cnt w) (:alive b))
    (Bool.and (Nat.ble (row-cnt w) (:rows b)) (nat-list-eq (active-ids w) (:active b))))))
(a/defn bc [b :- Bnd, w :- World] Bool (Bool.and (inv-sample w) (bc-rest b w)))
(a/defn bnd-of [w :- World] Bnd (Bnd.mk (alive-cnt w) (row-cnt w) (active-ids w)))

(a/theorem nat-list-eq-eq [xs :- (List Nat)]
  (forall [ys :- (List Nat)] (=> (= (nat-list-eq xs ys) true) (= xs ys)))
  (induction xs)
  (case [nil] (intros ys h) (cases ys) (rfl) (simp [nat-list-eq] at h))
  (case [cons x t ih]
    (intros ys h)
    (cases ys)
    (simp [nat-list-eq] at h)
    (rename_i y t2)
    (simp only [nat-list-eq Bool.and_eq_true] at h)
    (have e1 (= x y)) (exact (Nat.eq_of_beq_eq_true (And.left h)))
    (have e2 (= t t2)) (exact (ih t2 (And.right h)))
    (rw [e1 e2])))

(a/theorem nat-list-eq-refl [xs :- (List Nat)] (= (nat-list-eq xs xs) true)
  (induction xs)
  (case [nil] (simp [nat-list-eq]))
  (case [cons x t ih] (simp [nat-list-eq Nat.beq_refl ih])))

(a/theorem bc-sample [b :- Bnd, w :- World] (=> (= (bc b w) true) (= (inv-sample w) true))
  (intro h) (simp only [bc Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem bc-rest-of [b :- Bnd, w :- World] (=> (= (bc b w) true) (= (bc-rest b w) true))
  (intro h) (simp only [bc Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem bc-intro [b :- Bnd, w :- World] (=> (= (inv-sample w) true) (= (bc-rest b w) true) (= (bc b w) true))
  (intros h1 h2) (simp only [bc h1 h2 Bool.and_self]))
(a/theorem bc-parts [b :- Bnd, w :- World]
  (=> (= (bc b w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (bc-sample b w h))))

(a/theorem bc-rest-parts [b :- Bnd, w :- World]
  (=> (= (bc-rest b w) true)
      (And (= (acts-alive w) true)
           (And (<= (alive-cnt w) (:alive b))
                (And (<= (row-cnt w) (:rows b)) (= (active-ids w) (:active b))))))
  (intro h)
  (simp only [bc-rest Bool.and_eq_true] at h)
  (exact (And.intro (And.left h)
           (And.intro (Nat.le_of_ble_eq_true (And.left (And.right h)))
             (And.intro (Nat.le_of_ble_eq_true (And.left (And.right (And.right h))))
                        (nat-list-eq-eq _ _ (And.right (And.right (And.right h)))))))))

(a/theorem bc-rest-intro [b :- Bnd, w :- World]
  (=> (= (acts-alive w) true) (<= (alive-cnt w) (:alive b)) (<= (row-cnt w) (:rows b))
      (= (active-ids w) (:active b)) (= (bc-rest b w) true))
  (intros h1 h2 h3 h4)
  (simp only [bc-rest Bool.and_eq_true h1 h4 nat-list-eq-refl (Nat.ble_eq_true_of_le h2) (Nat.ble_eq_true_of_le h3)]))

;; the frame: acts-alive kept, both counts down, the active ids unchanged
(a/theorem bc-rest-mono [b :- Bnd, w :- World, w2 :- World]
  (=> (=> (= (acts-alive w) true) (= (acts-alive w2) true))
      (<= (alive-cnt w2) (alive-cnt w)) (<= (row-cnt w2) (row-cnt w)) (= (active-ids w2) (active-ids w))
      (= (bc-rest b w) true) (= (bc-rest b w2) true))
  (intros ha hl hr he h)
  (have p := (bc-rest-parts b w h))
  (exact (bc-rest-intro b w2 (ha (And.left p)) (Nat.le_trans hl (And.left (And.right p)))
           (Nat.le_trans hr (And.left (And.right (And.right p))))
           (Eq.trans he (And.right (And.right (And.right p)))))))

(a/theorem ble-refl [n :- Nat] (= (Nat.ble n n) true) (exact (Nat.ble_eq_true_of_le (Nat.le_refl n))))

(a/theorem bc-of-bnd [w :- World] (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (bc (bnd-of w) w) true))
  (intros h1 h2)
  (have h3 (= (bc-rest (bnd-of w) w) true))
  (simp only [bc-rest bnd-of h2 ble-refl nat-list-eq-refl Bool.and_self])
  (exact (bc-intro (bnd-of w) w h1 h3)))

;; ===========================================================================
;; Part B. bc-rest under the primitive edits
;; ===========================================================================

(a/theorem bc-rest-same [b :- Bnd, w :- World, w2 :- World]
  (=> (= (acts-alive w2) (acts-alive w)) (= (alive-cnt w2) (alive-cnt w)) (= (row-cnt w2) (row-cnt w))
      (= (active-ids w2) (active-ids w)) (= (bc-rest b w2) (bc-rest b w)))
  (intros h1 h2 h3 h4) (simp only [bc-rest h1 h2 h3 h4]))

(a/theorem tbl-all-upd-same [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), p :- (=> A Bool),
                             hf :- (forall [r :- A] (= (p (f r)) (p r))), xs :- (List A)]
  (= (tbl-all p (tbl-upd idf x f xs)) (tbl-all p xs))
  (induction xs)
  (case [nil] (simp [tbl-all tbl-upd]))
  (case [cons h t ih]
    (cases hx (Nat.beq (idf h) x))
    (all_goals (simp only [tbl-upd hx tbl-all hf ih]))))

(a/theorem tbl-scan-upd-same [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), p :- (=> A Bool),
                              hid :- (forall [r :- A] (= (idf (f r)) (idf r))),
                              hf :- (forall [r :- A] (= (p (f r)) (p r))), xs :- (List A)]
  (= (tbl-scan idf p (tbl-upd idf x f xs)) (tbl-scan idf p xs))
  (induction xs)
  (case [nil] (simp [tbl-scan tbl-upd]))
  (case [cons h t ih]
    (cases hx (Nat.beq (idf h) x))
    (all_goals (simp only [tbl-upd hx tbl-scan hf hid ih]))))

(a/theorem tbl-count-del-le [A :- Type, idf :- (=> A Nat), x :- Nat, p :- (=> A Bool), xs :- (List A)]
  (<= (tbl-count p (tbl-del idf x xs)) (tbl-count p xs))
  (induction xs)
  (case [nil] (simp [tbl-count tbl-del]))
  (case [cons h t ih]
    (cases hx (Nat.beq (idf h) x))
    (all_goals (simp only [tbl-del hx tbl-count-cons]))
    (omega)
    (omega)))

(a/theorem tbl-count-filter-le [A :- Type, q :- (=> A Bool), p :- (=> A Bool), xs :- (List A)]
  (<= (tbl-count p (tbl-filter q xs)) (tbl-count p xs))
  (induction xs)
  (case [nil] (simp [tbl-count tbl-filter]))
  (case [cons h t ih]
    (cases hx (q h))
    (all_goals (simp only [tbl-filter hx tbl-count-cons]))
    (omega)
    (omega)))

;; ---- runs

(a/theorem acts-alive-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                               hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                               hal :- (forall [r :- RunRow] (= (run-alive (f r)) (run-alive r)))]
  (= (acts-alive (run-upd w x f)) (acts-alive w))
  (have hy (forall [y :- Nat, r :- RunRow] (= (run-ok-for y (f r)) (run-ok-for y r))))
  (intros y r)
  (have e (= (:id (f r)) (:id r))) (exact (hid r))
  (simp only [run-ok-for e (hal r)])
  (have ha (forall [a :- ActRow] (= (act-run-ok (tbl-upd run-id x f (:runs w)) a) (act-run-ok (:runs w) a))))
  (intro a)
  (simp only [act-run-ok])
  (exact (tbl-all-upd-same RunRow run-id x f (run-ok-for (:run a)) (hy (:run a)) (:runs w)))
  (simp only [acts-alive run-upd set-runs])
  (exact (tbl-all-congr ActRow _ _ ha (:acts w))))

(a/theorem bc-rest-run-upd [b :- Bnd, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                            hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                            hal :- (forall [r :- RunRow] (= (run-alive (f r)) (run-alive r)))]
  (= (bc-rest b (run-upd w x f)) (bc-rest b w))
  (have e2 (= (alive-cnt (run-upd w x f)) (alive-cnt w)))
  (simp only [alive-cnt run-upd set-runs]) (exact (tbl-count-upd-same RunRow run-id x f run-alive hal (:runs w)))
  (have e3 (= (row-cnt (run-upd w x f)) (row-cnt w)))
  (simp only [row-cnt run-upd set-runs])
  (exact (tbl-count-upd-same RunRow run-id x f run-any (fn [r :- RunRow] (Eq.refl true)) (:runs w)))
  (exact (bc-rest-same b w (run-upd w x f) (acts-alive-run-upd w x f hid hal) e2 e3 (rfl))))

(a/theorem act-run-ok-del [rs :- (List RunRow), x :- Nat, a :- ActRow]
  (=> (= (act-run-ok rs a) true) (= (act-run-ok (tbl-del run-id x rs) a) true))
  (intro h)
  (simp only [act-run-ok] at h) (simp only [act-run-ok])
  (exact (tbl-all-del RunRow run-id x (run-ok-for (:run a)) (run-ok-for (:run a))
           (fn [r :- RunRow, h1 :- (= (run-ok-for (:run a) r) true), h2 :- (= (Nat.beq (run-id r) x) false)] h1)
           rs h)))

(a/theorem bc-rest-run-del [b :- Bnd, w :- World, x :- Nat]
  (=> (= (bc-rest b w) true) (= (bc-rest b (run-del w x)) true))
  (intro h)
  (have ha (=> (= (acts-alive w) true) (= (acts-alive (run-del w x)) true)))
  (intro h1)
  (simp only [acts-alive run-del set-runs])
  (exact (tbl-all-mono ActRow (act-run-ok (:runs w)) (act-run-ok (tbl-del run-id x (:runs w)))
           (act-run-ok-del (:runs w) x) (:acts w) h1))
  (have hl (<= (alive-cnt (run-del w x)) (alive-cnt w)))
  (simp only [alive-cnt run-del set-runs]) (exact (tbl-count-del-le RunRow run-id x run-alive (:runs w)))
  (have hr (<= (row-cnt (run-del w x)) (row-cnt w)))
  (simp only [row-cnt run-del set-runs]) (exact (tbl-count-del-le RunRow run-id x run-any (:runs w)))
  (exact (bc-rest-mono b w (run-del w x) ha hl hr (rfl) h)))

;; ---- activations

(a/theorem bc-rest-act-upd [b :- Bnd, w :- World, x :- Nat, f :- (=> ActRow ActRow),
                            hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c)))]
  (= (bc-rest b (act-upd w x f)) (bc-rest b w))
  (have hp (forall [c :- ActRow] (= (act-run-ok (:runs w) (f c)) (act-run-ok (:runs w) c))))
  (intro c) (simp only [act-run-ok (hr c)])
  (have e1 (= (acts-alive (act-upd w x f)) (acts-alive w)))
  (simp only [acts-alive act-upd set-acts])
  (exact (tbl-all-upd-same ActRow act-id x f (act-run-ok (:runs w)) hp (:acts w)))
  (exact (bc-rest-same b w (act-upd w x f) e1 (rfl) (rfl) (rfl))))

(a/theorem bc-rest-act-del [b :- Bnd, w :- World, x :- Nat]
  (=> (= (bc-rest b w) true) (= (bc-rest b (act-del w x)) true))
  (intro h)
  (have ha (=> (= (acts-alive w) true) (= (acts-alive (act-del w x)) true)))
  (intro h1)
  (simp only [acts-alive act-del set-acts])
  (exact (tbl-all-del ActRow act-id x (act-run-ok (:runs w)) (act-run-ok (:runs w))
           (fn [r :- ActRow, h1 :- (= (act-run-ok (:runs w) r) true), h2 :- (= (Nat.beq (act-id r) x) false)] h1)
           (:acts w) h1))
  (exact (bc-rest-mono b w (act-del w x) ha (Nat.le_refl _) (Nat.le_refl _) (rfl) h)))

;; ---- computations

(a/theorem bc-rest-comp-upd [b :- Bnd, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                             hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                             hac :- (forall [c :- CompRow] (= (comp-active (f c)) (comp-active c)))]
  (= (bc-rest b (comp-upd w x f)) (bc-rest b w))
  (have e (= (active-ids (comp-upd w x f)) (active-ids w)))
  (simp only [active-ids comp-upd set-comps])
  (exact (tbl-scan-upd-same CompRow comp-id x f comp-active hid hac (:comps w)))
  (exact (bc-rest-same b w (comp-upd w x f) (rfl) (rfl) (rfl) e)))

(a/theorem scan-resync [es :- (List EdgeRow), cs :- (List CompRow)]
  (= (tbl-scan comp-id comp-active (comps-resync es cs)) (tbl-scan comp-id comp-active cs))
  (induction cs)
  (case [nil] (simp [comps-resync tbl-scan]))
  (case [cons h t ih]
    (have e1 (= (comp-active (comp-resync es h)) (comp-active h))) (rfl)
    (have e2 (= (comp-id (comp-resync es h)) (comp-id h))) (rfl)
    (simp only [comps-resync tbl-scan e1 e2 ih])))

(a/theorem bc-rest-drop-edges [b :- Bnd, w :- World, p :- (=> EdgeRow Bool)]
  (= (bc-rest b (drop-edges w p)) (bc-rest b w))
  (have e (= (active-ids (drop-edges w p)) (active-ids w)))
  (simp only [active-ids drop-edges set-comps set-edges])
  (exact (scan-resync (tbl-filter p (:edges w)) (:comps w)))
  (exact (bc-rest-same b w (drop-edges w p) (rfl) (rfl) (rfl) e)))

(a/theorem bc-rest-drop-cred [b :- Bnd, w :- World, a :- Nat]
  (= (bc-rest b (drop-cred-edges w a)) (bc-rest b w))
  (simp only [drop-cred-edges])
  (rw [(bc-rest-comp-upd b _ a (comp-set-pending 0) (comp-set-pending-id 0) (fn [c :- CompRow] (Eq.refl (comp-active c))))]))

(a/theorem bc-rest-drop-act [b :- Bnd, w :- World, a :- Nat]
  (=> (= (bc-rest b w) true) (= (bc-rest b (drop-act w a)) true))
  (intro h)
  (simp only [drop-act])
  (exact (bc-rest-act-del b _ a (Eq.trans (bc-rest-drop-cred b w a) h))))

(a/theorem bc-rest-remove-edge [b :- Bnd, w :- World, x :- Nat]
  (= (bc-rest b (remove-edge w x)) (bc-rest b w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]))
    (case [true]
      (simp only [remove-edge hf hm])
      (rw [(bc-rest-comp-upd b _ (:creditor e) comp-dec-pending comp-dec-pending-id (fn [c :- CompRow] (Eq.refl (comp-active c))))]))))

;; ---- generic count lemmas

(a/theorem count-upd-false-le [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), p :- (=> A Bool),
                               hf :- (forall [r :- A] (= (p (f r)) false)), xs :- (List A)]
  (<= (tbl-count p (tbl-upd idf x f xs)) (tbl-count p xs))
  (induction xs)
  (case [nil] (simp [tbl-count tbl-upd]))
  (case [cons h t ih]
    (cases hx (Nat.beq (idf h) x))
    (all_goals (simp only [tbl-upd hx tbl-count-cons hf b2n]))
    (omega)
    (omega)))

;; a found row with p that f makes false: the count drops
(a/theorem count-upd-false-lt [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), p :- (=> A Bool),
                               hf :- (forall [r :- A] (= (p (f r)) false)), e :- A, xs :- (List A)]
  (=> (= (tbl-find idf x xs) (Option.some A e)) (= (p e) true)
      (<= (+ (tbl-count p (tbl-upd idf x f xs)) 1) (tbl-count p xs)))
  (induction xs)
  (case [nil] (intros h1 h2) (simp [tbl-find] at h1))
  (case [cons h t ih]
    (intros h1 h2)
    (cases hx (Nat.beq (idf h) x))
    (case [false]
      (simp only [tbl-find hx] at h1)
      (have ih2 := (ih h1 h2))
      (simp only [tbl-upd hx tbl-count-cons])
      (omega))
    (case [true]
      (simp only [tbl-find hx Option.some.injEq] at h1)
      (have le := (count-upd-false-le A idf x f p hf t))
      (rw [← h1] at h2)
      (simp only [tbl-upd hx tbl-count-cons hf h2 b2n])
      (omega))))

(a/theorem count-del-lt [A :- Type, idf :- (=> A Nat), x :- Nat, p :- (=> A Bool), e :- A, xs :- (List A)]
  (=> (= (tbl-find idf x xs) (Option.some A e)) (= (p e) true)
      (<= (+ (tbl-count p (tbl-del idf x xs)) 1) (tbl-count p xs)))
  (induction xs)
  (case [nil] (intros h1 h2) (simp [tbl-find] at h1))
  (case [cons h t ih]
    (intros h1 h2)
    (cases hx (Nat.beq (idf h) x))
    (case [false]
      (simp only [tbl-find hx] at h1)
      (have ih2 := (ih h1 h2))
      (simp only [tbl-del hx tbl-count-cons])
      (omega))
    (case [true]
      (simp only [tbl-find hx Option.some.injEq] at h1)
      (have le := (tbl-count-del-le A idf x p t))
      (rw [← h1] at h2)
      (simp only [tbl-del hx tbl-count-cons h2 b2n])
      (omega))))

;; ===========================================================================
;; Part C. The bundle under the primitive edits, and the copy of the composite lemmas
;; ===========================================================================

(a/theorem bc-run-upd [bnd :- Bnd, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hal :- (forall [r :- RunRow] (= (run-alive (f r)) (run-alive r)))]
  (=> (= (bc bnd w) true) (= (bc bnd (run-upd w x f)) true))
  (intro h)
  (exact (bc-intro bnd _ (inv-run-upd w x f hf (bc-sample bnd w h))
           (Eq.trans (bc-rest-run-upd bnd w x f hf hal) (bc-rest-of bnd w h)))))

(a/theorem bc-act-upd [bnd :- Bnd, w :- World, x :- Nat, f :- (=> ActRow ActRow),
                       hf :- (forall [r :- ActRow] (= (act-id (f r)) (act-id r))),
                       hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c)))]
  (=> (= (bc bnd w) true) (= (bc bnd (act-upd w x f)) true))
  (intro h)
  (exact (bc-intro bnd _ (inv-act-upd w x f hf (bc-sample bnd w h))
           (Eq.trans (bc-rest-act-upd bnd w x f hr) (bc-rest-of bnd w h)))))

(a/theorem bc-comp-upd [bnd :- Bnd, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hac :- (forall [c :- CompRow] (= (comp-active (f c)) (comp-active c)))]
  (=> (= (bc bnd w) true) (= (bc bnd (comp-upd w x f)) true))
  (intro h)
  (exact (bc-intro bnd _ (inv-comp-upd w x f hid hp (bc-sample bnd w h))
           (Eq.trans (bc-rest-comp-upd bnd w x f hid hac) (bc-rest-of bnd w h)))))

(def ^:private casc-ns *ns*)

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

(def source-nss '[spindel.v2.edits spindel.v2.step spindel.v2.rule])

(def ^:private source-theorems
  (delay (vec (for [nsym source-nss, f (ns-source-forms nsym), g (expand-top nsym f) :when (theorem-form? g)]
                [(second g) g]))))

(defn- theorem-source [nm]
  (or (some (fn [[n g]] (when (= n nm) g)) @source-theorems)
      (throw (ex-info (str "no source for theorem " nm) {:name nm}))))

(defn- binder-names [binders] (vec (take-nth 3 binders)))
(defn- inv-premise? [p] (and (seq? p) (= '= (first p)) (seq? (second p)) (= 'inv-sample (first (second p)))))

(def ^:private renames "inv-sample lemma -> its bundle version" (atom {}))
(def bc-copied "the theorems checked by bc-copy!, in order" (atom []))

;; REPL iteration only: skip a generated theorem whose name is already in the env
(defonce ^:dynamic *dev-skip-declared* false)

(defn- declared? [s] (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str s)))))

(defn- eval-theorem! [form]
  (try (when-not (and *dev-skip-declared* (declared? (second form))) (binding [*ns* casc-ns] (eval form)))
       (catch Throwable t
         (throw (ex-info (str "casc: theorem " (second form) " failed: " (ex-message t)) {:form form} t)))))

;; a primitive: the inv-sample lemma plus a bc-rest proof; `rest` is a form over the binder
;; names, the premise names h0..hn and R = bc-rest of the input world; nil = rfl frame
(defn- prim-form [orig bcn rest-f]
  (let [[_ _ binders stmt] (theorem-source orig)
        prems (butlast (rest stmt))
        concl (last stmt)
        hs (vec (map-indexed (fn [i _] (symbol (str "h" i))) prems))
        i (first (keep-indexed (fn [i p] (when (inv-premise? p) i)) prems))
        w (second (second (nth prems i)))
        w2 (second (second concl))
        hi (nth hs i)
        args (concat (binder-names binders) (assoc hs i (list 'bc-sample 'bnd w hi)))
        R (list 'bc-rest-of 'bnd w hi)
        rest-term (if rest-f (walk/postwalk-replace {'R R} rest-f) (list 'Eq.trans 'e-frame R))
        sub (fn [x] (walk/postwalk (fn [y] (if (and (seq? y) (= 'inv-sample (first y))) (list 'bc 'bnd (second y)) y)) x))]
    (concat
     (list 'a/theorem bcn (into '[bnd :- Bnd] binders) (sub stmt) (cons 'intros hs))
     (when-not rest-f [(list 'have 'e-frame (list '= (list 'bc-rest 'bnd w2) (list 'bc-rest 'bnd w))) '(rfl)])
     [(list 'exact (list 'bc-intro 'bnd w2 (cons orig args) rest-term))])))

(defn- bc-prim! [orig bcn rest]
  (eval-theorem! (apply list (prim-form orig bcn rest)))
  (swap! renames assoc orig bcn))

(defmacro ^:private defbc-prims [& specs]
  `(do ~@(for [[orig bcn rest] (partition 3 specs)] `(bc-prim! '~orig '~bcn '~rest))))

(swap! renames assoc 'inv-run-upd 'bc-run-upd 'inv-act-upd 'bc-act-upd 'inv-comp-upd 'bc-comp-upd
       'inv-parts 'bc-parts)

(defbc-prims
  ;; edits that touch neither runs, activations nor computations (rfl frame)
  inv-scope-upd bc-scope-upd nil
  inv-source-upd bc-source-upd nil
  inv-task-upd bc-task-upd nil
  inv-resource-upd bc-resource-upd nil
  inv-cleanup-del bc-cleanup-del nil
  inv-cleanup-ins bc-cleanup-ins nil
  inv-edge-upd bc-edge-upd nil
  inv-scope-del bc-scope-del nil
  ;; runs, activations, computations
  inv-run-del bc-run-del (bc-rest-run-del bnd w x R)
  inv-remove-edge bc-remove-edge (Eq.trans (bc-rest-remove-edge bnd w x) R)
  inv-drop-cred bc-drop-cred (Eq.trans (bc-rest-drop-cred bnd w a) R)
  inv-drop-act bc-drop-act (bc-rest-drop-act bnd w a R)
  inv-drop-edges bc-drop-edges (Eq.trans (bc-rest-drop-edges bnd w p) R))

(defn- statement-mentions-inv? [form]
  (let [[_ _ binders stmt] form] (boolean (some #{'inv-sample} (flatten (list (seq binders) stmt))))))

(defn- bc-name [sym]
  (let [s (name sym)]
    (symbol (cond (str/starts-with? s "inv-") (str "bc-" (subs s 4))
                  (str/ends-with? s "-inv") (str (subs s 0 (- (count s) 4)) "-bc")
                  :else (str s "-bc")))))

;; the row-function lemmas of the bundle take one more argument than their inv-sample versions
(def ^:private extra-args
  {'inv-comp-upd ['(fn [c :- CompRow] (Eq.refl (comp-active c))) 5]
   'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (run-alive r))) 4]
   'inv-act-upd ['(fn [c :- ActRow] (Eq.refl (:run c))) 4]})

(defn- bc-subst [x rn]
  (cond
    (and (seq? x) (= 'inv-sample (first x))) (list 'bc 'bnd (bc-subst (second x) rn))
    (and (seq? x) (symbol? (first x)) (contains? rn (first x)))
    (let [h (first x)
          args (map #(bc-subst % rn) (rest x))
          args (if-let [[e k] (extra-args h)]
                 (do (assert (>= (count args) k) (str h " applied to too few arguments: " (pr-str x)))
                     (concat (take k args) [e] (drop k args)))
                 args)]
      (apply list (rn h) 'bnd args))
    (seq? x) (apply list (map #(bc-subst % rn) x))
    (vector? x) (mapv #(bc-subst % rn) x)
    (symbol? x) (cond (contains? extra-args x) (throw (ex-info (str x " used as a value") {}))
                      (contains? rn x) (list (rn x) 'bnd)
                      :else x)
    :else x))

(defn- bc-form [form bcn rn]
  (let [[head _ binders stmt & proof] form]
    (apply list head bcn (into '[bnd :- Bnd] (bc-subst binders rn)) (bc-subst stmt rn)
           (map #(bc-subst % rn) proof))))

(def ^:private bc-overrides
  "Bundle proofs written by hand, keyed by the inv-sample lemma they replace" (atom {}))

(defmacro ^:private defbc-override [orig deps form]
  `(swap! bc-overrides assoc '~orig {:deps '~deps :form '~form}))

(defn- bc-closure [root]
  (let [thms @source-theorems
        S (set (keep (fn [[n g]] (when (statement-mentions-inv? g) n)) thms))
        deps (fn [n]
               (cond (contains? @renames n) []
                     (contains? @bc-overrides n) (:deps (get @bc-overrides n))
                     :else (let [[_ _ _ _ & proof] (theorem-source n)]
                             (filter S (filter symbol? (flatten proof))))))]
    (loop [todo [root] seen #{}]
      (if-let [n (first todo)]
        (if (seen n) (recur (rest todo) seen) (recur (concat (rest todo) (deps n)) (conj seen n)))
        (filterv seen (map first thms))))))

(defn bc-copy!
  "Check the bundle version of every inv-sample lemma `root` depends on, in load order."
  [root]
  (doseq [n (bc-closure root) :when (not (contains? @renames n))]
    (let [form (if-let [o (get @bc-overrides n)]
                 (:form o)
                 (bc-form (theorem-source n) (bc-name n) @renames))]
      (eval-theorem! form)
      (swap! renames assoc n (second form))
      (swap! bc-copied conj (second form)))))

;; ---- resume: a run with an activation is alive, so resuming it revives nothing

(a/theorem act-with-member-mem [x :- Nat, as :- (List ActRow), a :- ActRow]
  (=> (= (act-with-member x as) (Option.some ActRow a)) (List.Mem a as))
  (induction as)
  (case [nil] (intro h) (simp [act-with-member] at h))
  (case [cons h t ih]
    (intro hf)
    (cases hm (mem-has x (:members h)))
    (case [false] (simp [act-with-member hm] at hf) (exact (List.Mem.tail h (ih hf))))
    (case [true] (simp [act-with-member hm] at hf) (rw [hf]) (exact (List.Mem.head t)))))

(a/theorem acts-alive-mem [w :- World, a :- ActRow]
  (=> (= (acts-alive w) true) (List.Mem a (:acts w)) (= (act-run-ok (:runs w) a) true))
  (intros h hm) (simp only [acts-alive] at h) (exact (tbl-all-mem ActRow (act-run-ok (:runs w)) a (:acts w) h hm)))

(a/theorem bc-acts-alive [bnd :- Bnd, w :- World] (=> (= (bc bnd w) true) (= (acts-alive w) true))
  (intro h) (exact (And.left (bc-rest-parts bnd w (bc-rest-of bnd w h)))))

(a/theorem count-revive [x :- Nat, f :- (=> RunRow RunRow),
                         hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                         hal :- (forall [r :- RunRow] (= (run-alive (f r)) true)), rs :- (List RunRow)]
  (=> (= (tbl-all (run-ok-for x) rs) true)
      (= (tbl-count run-alive (tbl-upd run-id x f rs)) (tbl-count run-alive rs)))
  (induction rs)
  (case [nil] (intro h) (simp [tbl-count tbl-upd]))
  (case [cons h t ih]
    (intro hp)
    (simp only [tbl-all Bool.and_eq_true] at hp)
    (have ih2 := (ih (And.right hp)))
    (cases hx (Nat.beq (run-id h) x))
    (case [false] (simp only [tbl-upd hx tbl-count-cons ih2]))
    (case [true]
      (have hx2 (= (Nat.beq (:id h) x) true)) (exact hx)
      (have ha (= (run-alive h) true))
      (have hp1 := (And.left hp))
      (simp only [run-ok-for hx2 Bool.not_true Bool.false_or] at hp1)
      (exact hp1)
      (simp only [tbl-upd hx tbl-count-cons ih2 (hal h) ha]))))

(a/theorem bc-rest-revive [b :- Bnd, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                           hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                           hal :- (forall [r :- RunRow] (= (run-alive (f r)) true))]
  (=> (= (tbl-all (run-ok-for x) (:runs w)) true) (= (bc-rest b w) true) (= (bc-rest b (run-upd w x f)) true))
  (intros hx h)
  (have hin (forall [y :- Nat, r :- RunRow] (=> (= (run-ok-for y r) true) (= (Nat.beq (run-id r) x) true)
                                                (= (run-ok-for y (f r)) true))))
  (intros y r h1 h2) (simp only [run-ok-for (hal r) Bool.or_true])
  (have hout (forall [y :- Nat, r :- RunRow] (=> (= (run-ok-for y r) true) (= (Nat.beq (run-id r) x) false)
                                                 (= (run-ok-for y r) true))))
  (intros y r h1 h2) (exact h1)
  (have ha (=> (= (acts-alive w) true) (= (acts-alive (run-upd w x f)) true)))
  (intro h1)
  (simp only [acts-alive run-upd set-runs])
  (exact (tbl-all-mono ActRow (act-run-ok (:runs w)) (act-run-ok (tbl-upd run-id x f (:runs w)))
           (fn [c :- ActRow, hc :- (= (act-run-ok (:runs w) c) true)]
             (tbl-all-upd RunRow run-id x f (run-ok-for (:run c)) (run-ok-for (:run c)) (hin (:run c)) (hout (:run c))
               (:runs w) hc))
           (:acts w) h1))
  (have hl (<= (alive-cnt (run-upd w x f)) (alive-cnt w)))
  (simp only [alive-cnt run-upd set-runs (count-revive x f hid hal (:runs w) hx)]) (exact (Nat.le_refl _))
  (have hr (<= (row-cnt (run-upd w x f)) (row-cnt w)))
  (simp only [row-cnt run-upd set-runs (tbl-count-upd-same RunRow run-id x f run-any (fn [r :- RunRow] (Eq.refl true)) (:runs w))])
  (exact (Nat.le_refl _))
  (exact (bc-rest-mono b w (run-upd w x f) ha hl hr (rfl) h)))

(a/theorem run-set-act-active-alive [r :- RunRow] (= (run-alive (run-set-act act-active r)) true) (rfl))

;; Z#50: resume wakes only a parked run, so it keeps every run's aliveness (a frame)
(a/theorem run-wake-alive [r :- RunRow] (= (run-alive (run-wake r)) (run-alive r))
  (cases h (Nat.beq (:act r) act-parked))
  (case [false] (simp only [run-alive run-wake wake-act h]))
  (case [true]
    (have e (= (:act r) act-parked)) (exact (Nat.eq_of_beq_eq_true h))
    (simp only [run-alive run-wake wake-act h e])))

(defbc-override inv-resume [inv-drop-act]
  (a/theorem bc-resume [bnd :- Bnd, w :- World, a :- ActRow]
    (=> (= (act-run-ok (:runs w) a) true) (= (bc bnd w) true) (= (bc bnd (resume w a)) true))
    (intros ha h)
    (exact (bc-run-upd bnd _ (:run a) run-wake run-wake-run-id run-wake-alive (bc-drop-act bnd w (:id a) h)))))

(defbc-override inv-fill-slot [inv-resume]
  (a/theorem bc-fill-slot [bnd :- Bnd, w :- World, a :- ActRow, x :- Nat, v :- RunResult]
    (=> (= (act-run-ok (:runs w) a) true) (= (bc bnd w) true) (= (bc bnd (fill-slot w a x v)) true))
    (intros ha h)
    (cases hm (act-ready (act-fill x v a)))
    (simp only [fill-slot hm])
    (exact (bc-act-upd bnd w (:id a) (act-fill x v) (act-fill-act-id x v) (fn [c :- ActRow] (Eq.refl (:run c))) h))
    (simp only [fill-slot hm]) (exact (bc-resume bnd w a ha h))))

(defbc-override inv-fire-dep [inv-invalidate inv-fill-slot inv-dep-consumed]
  (a/theorem bc-fire-dep [bnd :- Bnd, w :- World, e :- EdgeRow]
    (=> (= (bc bnd w) true) (= (bc bnd (fire-dep w e)) true))
    (intro h)
    (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
    (simp only [fire-dep ha]) (exact (bc-invalidate bnd w e h))
    (have hok := (acts-alive-mem w a (bc-acts-alive bnd w h) (act-with-member-mem (:id e) (:acts w) a ha)))
    (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
    (simp only [fire-dep ha hc]) (exact (bc-invalidate bnd w e h))
    (simp only [fire-dep ha hc deliver-dep])
    (have hok2 (= (act-run-ok (:runs (dep-consumed w e)) a) true))
    (exact (Eq.trans (congrArg (fn [rs :- (List RunRow)] (act-run-ok rs a)) (dep-consumed-runs w e)) hok))
    (exact (bc-fill-slot bnd _ a _ _ hok2 (bc-dep-consumed bnd w e h)))))

(defbc-override inv-fire-wait-act [inv-edge-set-phase inv-fill-slot]
  (a/theorem bc-fire-wait-act [bnd :- Bnd, res :- RunResult, w :- World, e :- EdgeRow]
    (=> (= (bc bnd w) true) (= (bc bnd (fire-wait-act res w e)) true))
    (intro h)
    (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
    (simp only [fire-wait-act ha]) (exact (bc-edge-set-phase bnd w (:id e) ph-fired h))
    (have hok := (acts-alive-mem w a (bc-acts-alive bnd w h) (tbl-find-mem ActRow act-id (:creditor e) a (:acts w) ha)))
    (cases hc (run-current w (:run a)))
    (simp only [fire-wait-act ha hc]) (exact (bc-edge-set-phase bnd w (:id e) ph-fired h))
    (have hok2 (= (act-run-ok (:runs (edge-upd w (:id e) (edge-set-phase ph-fired))) a) true)) (exact hok)
    (simp only [fire-wait-act ha hc]) (exact (bc-fill-slot bnd _ a _ _ hok2 (bc-edge-set-phase bnd w (:id e) ph-fired h)))))

(bc-copy! 'inv-fire-edge)

;; ---- T14's local part: the run is done and its activations are gone

(a/theorem bc-weaken [b :- Bnd, b2 :- Bnd, w :- World]
  (=> (= (bc b w) true) (<= (:alive b) (:alive b2)) (<= (:rows b) (:rows b2)) (= (:active b) (:active b2))
      (= (bc b2 w) true))
  (intros h h1 h2 h3)
  (have p := (bc-rest-parts b w (bc-rest-of b w h)))
  (exact (bc-intro b2 w (bc-sample b w h)
           (bc-rest-intro b2 w (And.left p) (Nat.le_trans (And.left (And.right p)) h1)
             (Nat.le_trans (And.left (And.right (And.right p))) h2) (Eq.trans (And.right (And.right (And.right p))) h3)))))

(a/defn runs-of [w :- World] (List RunRow) (:runs w))

(a/theorem nat-fold-frame [T :- Type, g :- (=> World T), f :- (=> World Nat World),
                           hf :- (forall [w :- World, y :- Nat] (= (g (f w y)) (g w))), ys :- (List Nat)]
  (forall [w :- World] (= (g (nat-fold f w ys)) (g w)))
  (induction ys)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons h t ih] (intro w) (simp only [nat-fold]) (exact (Eq.trans (ih (f w h)) (hf w h)))))

(a/theorem drop-act-runs [w :- World, y :- Nat] (= (runs-of (drop-act w y)) (runs-of w)) (rfl))
(a/theorem drop-act-active [w :- World, y :- Nat] (= (active-ids (drop-act w y)) (active-ids w))
  (simp only [active-ids drop-act act-del set-acts drop-cred-edges comp-upd set-comps set-edges])
  (exact (tbl-scan-upd-same CompRow comp-id y (comp-set-pending 0) comp-active (comp-set-pending-id 0)
           (fn [c :- CompRow] (Eq.refl (comp-active c))) (:comps w))))

(a/defn covers-ids [A :- Type :implicit, idf :- (=> A Nat), p :- (=> A Bool), ids :- (List Nat), a :- A] Bool
  (Bool.or (Bool.not (p a)) (reach-mem (idf a) ids)))

(a/theorem scan-covers-ids [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), xs :- (List A)]
  (= (tbl-all (covers-ids idf p (tbl-scan idf p xs)) xs) true)
  (induction xs)
  (case [nil] (simp [tbl-all]))
  (case [cons h t ih]
    (have hm (forall [a :- A] (=> (= (covers-ids idf p (tbl-scan idf p t) a) true)
                                  (= (covers-ids idf p (tbl-scan idf p (List.cons A h t)) a) true))))
    (intros a ha)
    (cases hp (p h))
    (case [false] (simp only [tbl-scan hp]) (exact ha))
    (case [true]
      (cases hr (reach-mem (idf a) (tbl-scan idf p t)))
      (case [true] (simp [tbl-scan hp covers-ids reach-mem-cons hr]))
      (case [false]
        (simp only [covers-ids hr Bool.or_false] at ha)
        (simp only [tbl-scan hp covers-ids ha Bool.true_or])))
    (have hh (= (covers-ids idf p (tbl-scan idf p (List.cons A h t)) h) true))
    (cases hp (p h))
    (case [false] (simp only [covers-ids hp Bool.not_false Bool.true_or]))
    (case [true] (simp only [tbl-scan hp covers-ids reach-mem-cons Nat.beq_refl Bool.true_or Bool.or_true]))
    (simp only [tbl-all Bool.and_eq_true])
    (exact (And.intro hh (tbl-all-mono A _ _ hm t ih)))))

(a/defn act-covered-run [x :- Nat, ids :- (List Nat), rs :- (List RunRow), a :- ActRow] Bool
  (if (act-of-run x a) (reach-mem (:id a) ids) (act-run-ok rs a)))

(a/theorem fold-drop-covered [x :- Nat, rs :- (List RunRow), ids :- (List Nat)]
  (forall [w :- World]
    (=> (= (tbl-all (act-covered-run x ids rs) (:acts w)) true)
        (= (tbl-all (act-covered-run x (List.nil Nat) rs) (:acts (nat-fold drop-act w ids))) true)))
  (induction ids)
  (case [nil] (intros w h) (simp only [nat-fold]) (exact h))
  (case [cons h t ih]
    (intros w hw)
    (have hout (forall [r :- ActRow] (=> (= (act-covered-run x (List.cons Nat h t) rs r) true)
                                         (= (Nat.beq (act-id r) h) false)
                                         (= (act-covered-run x t rs r) true))))
    (intros r h1 h2)
    (have h3 (= (Nat.beq (:id r) h) false)) (exact h2)
    (cases hk (act-of-run x r))
    (case [false] (simp only [act-covered-run hk] at h1) (simp only [act-covered-run hk]) (exact h1))
    (case [true] (simp only [act-covered-run hk reach-mem-cons h3 Bool.false_or] at h1) (simp only [act-covered-run hk]) (exact h1))
    (have h4 (= (tbl-all (act-covered-run x t rs) (:acts (drop-act w h))) true))
    (simp only [drop-act act-del set-acts])
    (exact (tbl-all-del ActRow act-id h _ _ hout (:acts (drop-cred-edges w h)) hw))
    (simp only [nat-fold])
    (exact (ih (drop-act w h) h4))))

(a/theorem act-run-ok-cancel [x :- Nat, rs :- (List RunRow), a :- ActRow]
  (=> (= (act-of-run x a) false) (= (act-run-ok rs a) true)
      (= (act-run-ok (tbl-upd run-id x run-cancel-row rs) a) true))
  (intros hx h)
  (have hin (forall [r :- RunRow] (=> (= (run-ok-for (:run a) r) true) (= (Nat.beq (run-id r) x) true)
                                      (= (run-ok-for (:run a) (run-cancel-row r)) true))))
  (intros r h1 h2)
  (have e (= (run-id r) x)) (exact (Nat.eq_of_beq_eq_true h2))
  (have h5 (= (Nat.beq (:run a) x) false)) (exact hx)
  (have h6 (= (Nat.beq (:id r) (:run a)) false))
  (have e2 (= (:id r) x)) (exact e)
  (rw [e2]) (rw [beq-comm]) (exact h5)
  (simp only [run-ok-for run-cancel-row h6 Bool.not_false Bool.true_or])
  (simp only [act-run-ok] at h) (simp only [act-run-ok])
  (exact (tbl-all-upd RunRow run-id x run-cancel-row (run-ok-for (:run a)) (run-ok-for (:run a)) hin
           (fn [r :- RunRow, h1 :- (= (run-ok-for (:run a) r) true), h2 :- (= (Nat.beq (run-id r) x) false)] h1) rs h)))

(a/theorem cancel-covered-one [w :- World, x :- Nat, a :- ActRow]
  (=> (= (covers-ids act-id (act-of-run x) (tbl-scan act-id (act-of-run x) (:acts w)) a) true)
      (= (act-run-ok (:runs w) a) true)
      (= (act-covered-run x (tbl-scan act-id (act-of-run x) (:acts w)) (tbl-upd run-id x run-cancel-row (:runs w)) a) true))
  (intros h1 h2)
  (cases hk (act-of-run x a))
  (case [false] (simp only [act-covered-run hk]) (exact (act-run-ok-cancel x (:runs w) a hk h2)))
  (case [true] (simp only [covers-ids hk Bool.not_true Bool.false_or] at h1) (simp only [act-covered-run hk]) (exact h1)))

(a/theorem covered-init [w :- World, x :- Nat]
  (=> (= (acts-alive w) true)
      (= (tbl-all (act-covered-run x (tbl-scan act-id (act-of-run x) (:acts w)) (tbl-upd run-id x run-cancel-row (:runs w))) (:acts w)) true))
  (intro h)
  (have hc := (scan-covers-ids ActRow act-id (act-of-run x) (:acts w)))
  (simp only [acts-alive] at h)
  (exact (tbl-all-mono2 ActRow _ _ _
           (fn [a :- ActRow, h1 :- (= (covers-ids act-id (act-of-run x) (tbl-scan act-id (act-of-run x) (:acts w)) a) true),
                h2 :- (= (act-run-ok (:runs w) a) true)]
             (cancel-covered-one w x a h1 h2))
           (:acts w) hc h)))

(a/theorem covered-nil [x :- Nat, rs :- (List RunRow), a :- ActRow]
  (=> (= (act-covered-run x (List.nil Nat) rs a) true) (= (act-run-ok rs a) true))
  (intro h)
  (cases hk (act-of-run x a))
  (case [false] (simp only [act-covered-run hk] at h) (exact h))
  (case [true] (simp [act-covered-run hk reach-mem] at h)))

(a/theorem cancel-acts-bc [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (acts-alive w) true)
      (= (bc (Bnd.mk (alive-cnt (run-upd w x run-cancel-row)) (row-cnt w) (active-ids w))
             (cancel-acts (run-upd w x run-cancel-row) x)) true))
  (intros h ha)
  (have hrun (= (runs-of (cancel-acts (run-upd w x run-cancel-row) x)) (runs-of (run-upd w x run-cancel-row))))
  (simp only [cancel-acts])
  (exact (nat-fold-frame (List RunRow) runs-of drop-act drop-act-runs _ _))
  (simp only [runs-of] at hrun)
  (have hact (= (active-ids (cancel-acts (run-upd w x run-cancel-row) x)) (active-ids (run-upd w x run-cancel-row))))
  (simp only [cancel-acts])
  (exact (nat-fold-frame (List Nat) active-ids drop-act drop-act-active _ _))
  (have h1 (= (acts-alive (cancel-acts (run-upd w x run-cancel-row) x)) true))
  (have hc := (fold-drop-covered x (tbl-upd run-id x run-cancel-row (:runs w))
                (tbl-scan act-id (act-of-run x) (:acts w)) (run-upd w x run-cancel-row) (covered-init w x ha)))
  (simp only [acts-alive hrun])
  (simp only [cancel-acts])
  (exact (tbl-all-mono ActRow _ _ (covered-nil x (tbl-upd run-id x run-cancel-row (:runs w))) _ hc))
  (have h2 (<= (alive-cnt (cancel-acts (run-upd w x run-cancel-row) x)) (alive-cnt (run-upd w x run-cancel-row))))
  (simp only [alive-cnt hrun]) (exact (Nat.le_refl _))
  (have h3 (<= (row-cnt (cancel-acts (run-upd w x run-cancel-row) x)) (row-cnt w)))
  (simp only [row-cnt hrun run-upd set-runs (tbl-count-upd-same RunRow run-id x run-cancel-row run-any (fn [r :- RunRow] (Eq.refl true)) (:runs w))])
  (exact (Nat.le_refl _))
  (have hact2 (= (active-ids (cancel-acts (run-upd w x run-cancel-row) x)) (active-ids w))) (exact hact)
  (exact (bc-intro (Bnd.mk (alive-cnt (run-upd w x run-cancel-row)) (row-cnt w) (active-ids w))
           (cancel-acts (run-upd w x run-cancel-row) x)
           (inv-cancel-acts (run-upd w x run-cancel-row) x (inv-run-upd w x run-cancel-row run-cancel-row-id h))
           (bc-rest-intro (Bnd.mk (alive-cnt (run-upd w x run-cancel-row)) (row-cnt w) (active-ids w))
             (cancel-acts (run-upd w x run-cancel-row) x) h1 h2 h3 hact2))))

(a/theorem run-cancel-row-alive [r :- RunRow] (= (run-alive (run-cancel-row r)) false) (rfl))

(a/theorem alive-cancel-le [w :- World, x :- Nat]
  (<= (alive-cnt (run-upd w x run-cancel-row)) (alive-cnt w))
  (simp only [alive-cnt run-upd set-runs])
  (exact (count-upd-false-le RunRow run-id x run-cancel-row run-alive run-cancel-row-alive (:runs w))))

(a/theorem alive-cancel-lt [w :- World, x :- Nat, r :- RunRow]
  (=> (= (run-find w x) (Option.some RunRow r)) (= (run-alive r) true)
      (<= (+ (alive-cnt (run-upd w x run-cancel-row)) 1) (alive-cnt w)))
  (intros hf ha)
  (simp only [alive-cnt run-upd set-runs])
  (exact (count-upd-false-lt RunRow run-id x run-cancel-row run-alive run-cancel-row-alive r (:runs w) hf ha)))

(bc-copy! 'inv-cancel-debtor)
(bc-copy! 'inv-cleanup-set)
(bc-copy! 'inv-cancel-res)

(a/theorem bc-cancel-tail [bnd :- Bnd, w :- World, r :- RunRow, rep :- Bool]
  (=> (= (bc bnd (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r))) true)
      (= (bc bnd (cancel-run-local w r rep)) true))
  (intro h)
  (simp only [cancel-run-local])
  (exact (bc-cancel-debtor bnd rep _ r (bc-cleanup-set bnd _ (:id r) _ (bc-cancel-res bnd _ r h)))))

(defbc-override inv-cancel-run-local [inv-cancel-debtor inv-cleanup-set inv-cancel-res]
  (a/theorem bc-cancel-run-local [bnd :- Bnd, w :- World, r :- RunRow, rep :- Bool]
    (=> (= (bc bnd w) true) (= (bc bnd (cancel-run-local w r rep)) true))
    (intro h)
    (have p := (bc-rest-parts bnd w (bc-rest-of bnd w h)))
    (have h1 := (cancel-acts-bc w (:id r) (bc-sample bnd w h) (And.left p)))
    (exact (bc-cancel-tail bnd w r rep
             (bc-weaken _ bnd _ h1 (Nat.le_trans (alive-cancel-le w (:id r)) (And.left (And.right p)))
               (And.left (And.right (And.right p))) (And.right (And.right (And.right p))))))))

(bc-copy! 'inv-run-cascade)

;; ===========================================================================
;; Part D. P4: the cascade empties its worklist within casc-fuel
;; ===========================================================================

;; ---- an acting cancel lowers #alive runs, an acting retire lowers #run rows

(a/theorem cancel-alive-lt [w :- World, rid :- Nat, r :- RunRow, rep :- Bool]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (run-find w rid) (Option.some RunRow r))
      (= (run-alive r) true)
      (<= (+ (alive-cnt (cancel-run-local w r rep)) 1) (alive-cnt w)))
  (intros h ha hf hr)
  (have e (= (run-id r) rid)) (exact (tbl-find-id RunRow run-id rid r (:runs w) hf))
  (have e2 (= (:id r) rid)) (exact e)
  (have hf2 (= (run-find w (:id r)) (Option.some RunRow r))) (rw [e2]) (exact hf)
  (have h1 := (bc-cancel-tail _ w r rep (cancel-acts-bc w (:id r) h ha)))
  (have p := (bc-rest-parts _ _ (bc-rest-of _ _ h1)))
  (have l1 (<= (alive-cnt (cancel-run-local w r rep)) (alive-cnt (run-upd w (:id r) run-cancel-row))))
  (exact (And.left (And.right p)))
  (have l2 := (alive-cancel-lt w (:id r) r hf2 hr))
  (omega))

(a/theorem fin-loop-runs [fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat)] (= (runs-of (:world (fin-loop fuel w ds))) (runs-of w)))
  (induction fuel)
  (case [nil] (intros w ds) (simp only [fin-loop]))
  (case [cons h f ih]
    (intros w ds)
    (cases ds)
    (simp only [fin-loop])
    (rename_i d t)
    (simp only [fin-loop])
    (exact (ih _ _))))

;; Z#53: closing a source wakes its waiters (T9 fills resume parked runs), so the run rows change
;; (act parked -> active) but keep their ids
(a/defn run-ids [w :- World] (List Nat) (tbl-ids run-id (:runs w)))
(a/theorem ri-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r)))]
  (= (run-ids (run-upd w x f)) (run-ids w))
  (exact (tbl-ids-upd RunRow run-id x f hf (:runs w))))
(a/theorem ri-resume [w :- World, a :- ActRow] (= (run-ids (resume w a)) (run-ids w))
  (simp only [resume])
  (exact (ri-run-upd _ (:run a) run-wake (fn [r :- RunRow] (Eq.refl (run-id r))))))
(a/theorem ri-fill-slot [w :- World, a :- ActRow, y :- Nat, v :- RunResult]
  (= (run-ids (fill-slot w a y v)) (run-ids w))
  (cases hm (act-ready (act-fill y v a)))
  (simp only [fill-slot hm])
  (simp only [fill-slot hm]) (exact (ri-resume w a)))
(a/theorem ri-remove-edge [w :- World, y :- Nat] (= (run-ids (remove-edge w y)) (run-ids w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf])
  (cases hm (:marked e))
  (all_goals (simp only [remove-edge hf hm])))
(a/theorem ri-dep-consumed [w :- World, e :- EdgeRow] (= (run-ids (dep-consumed w e)) (run-ids w))
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf])
  (simp only [dep-consumed hf]) (exact (ri-remove-edge w (:id e))))
(a/theorem ri-fire-dep [w :- World, e :- EdgeRow] (= (run-ids (fire-dep w e)) (run-ids w))
  (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha invalidate])
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc invalidate])
  (simp only [fire-dep ha hc deliver-dep])
  (exact (Eq.trans (ri-fill-slot _ a _ _) (ri-dep-consumed w e))))
(a/theorem ri-fire-wait [res :- RunResult, w :- World, e :- EdgeRow] (= (run-ids (fire-wait res w e)) (run-ids w))
  (cases hc (Nat.beq (:creditor e) 0))
  (case [true] (simp only [fire-wait hc]) (exact (ri-remove-edge w (:id e))))
  (case [false]
    (simp only [fire-wait hc])
    (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
    (simp only [fire-wait-act ha])
    (cases hr (run-current w (:run a)))
    (simp only [fire-wait-act ha hr])
    (simp only [fire-wait-act ha hr]) (exact (ri-fill-slot _ a _ _))))
(a/theorem ri-fire-edge [res :- RunResult, w :- World, y :- Nat] (= (run-ids (fire-edge res w y)) (run-ids w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [fire-edge hf])
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [fire-edge hf hp])
  (cases hk1 (Nat.beq (:kind e) ek-dep))
  (cases hk2 (Nat.beq (:kind e) ek-wait))
  (cases hk3 (Nat.beq (:kind e) ek-observe))
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-savepoint-todo])
  (cases ho (observe-new e (deb-version w (:debtor e))))
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-observe ho])
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-observe ho])
  (simp only [fire-edge hf hp hk1 hk2]) (exact (ri-fire-wait res w e))
  (simp only [fire-edge hf hp hk1]) (exact (ri-fire-dep w e)))
(a/theorem ri-close-source [w :- World, x :- Nat] (= (run-ids (close-source w x)) (run-ids w))
  (simp only [close-source finalize-debtor wake-closed])
  (have e1 := (fin-loop-runs (fin-fuel (nat-fold (fire-edge (deb-result (source-upd w x source-close-row) x)) (source-upd w x source-close-row)
                                             (tbl-scan edge-id (close-wakes (:acts (source-upd w x source-close-row)) x) (:edges (source-upd w x source-close-row)))))
                             (nat-fold (fire-edge (deb-result (source-upd w x source-close-row) x)) (source-upd w x source-close-row)
                               (tbl-scan edge-id (close-wakes (:acts (source-upd w x source-close-row)) x) (:edges (source-upd w x source-close-row))))
                             (List.cons Nat x (List.nil Nat))))
  (simp only [runs-of] at e1)
  (simp only [run-ids e1])
  (exact (nat-fold-frame (List Nat) run-ids (fire-edge (deb-result (source-upd w x source-close-row) x))
           (ri-fire-edge (deb-result (source-upd w x source-close-row) x)) _ _)))
(a/theorem close-scope-id-runs [w :- World, x :- Nat] (= (runs-of (close-scope-id w x)) (runs-of w)) (rfl))
(a/theorem scope-del-runs [w :- World, x :- Nat] (= (runs-of (scope-del w x)) (runs-of w)) (rfl))
(a/theorem ri-close-scope-id [w :- World, x :- Nat] (= (run-ids (close-scope-id w x)) (run-ids w)) (rfl))

(a/theorem ri-close-local [w :- World, sub :- (List Nat)] (= (run-ids (close-local w sub)) (run-ids w))
  (simp only [close-local])
  (exact (Eq.trans (nat-fold-frame (List Nat) run-ids close-source ri-close-source _ _)
                   (nat-fold-frame (List Nat) run-ids close-scope-id ri-close-scope-id _ _))))

;; a table with the same ids has the same row count; deleting a present id lowers it
(a/theorem count-any-ids [xs :- (List RunRow)] (= (tbl-count run-any xs) (List.length (tbl-ids run-id xs)))
  (induction xs)
  (case [nil] (simp [tbl-count tbl-ids]))
  (case [cons hd t ih] (simp only [tbl-count tbl-ids run-any List.length ih])))
(a/theorem count-any-del-le [x :- Nat, xs :- (List RunRow)]
  (<= (tbl-count run-any (tbl-del run-id x xs)) (tbl-count run-any xs))
  (induction xs)
  (case [nil] (simp [tbl-del tbl-count]))
  (case [cons hd t ih]
    (cases hx (Nat.beq (run-id hd) x))
    (case [true] (simp [tbl-del hx tbl-count run-any]) (omega))
    (case [false] (simp [tbl-del hx tbl-count run-any]) (omega))))
(a/theorem count-any-del-lt [x :- Nat, xs :- (List RunRow)]
  (=> (= (nat-mem x (tbl-ids run-id xs)) true)
      (<= (+ (tbl-count run-any (tbl-del run-id x xs)) 1) (tbl-count run-any xs)))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-ids nat-mem] at h))
  (case [cons hd t ih]
    (intro h)
    (have l2 := (count-any-del-le x t))
    (cases hx (Nat.beq (run-id hd) x))
    (case [true] (simp [tbl-del hx tbl-count run-any]) (omega))
    (case [false]
      (simp only [tbl-ids nat-mem hx] at h)
      (have l := (ih h))
      (simp [tbl-del hx tbl-count run-any])
      (omega))))

(a/theorem clear-comp-run-runs [w :- World, r :- RunRow] (= (runs-of (clear-comp-run w r)) (runs-of w))
  (cases hc (comp-find w (:of r)))
  (case [some c]
    (cases he (Nat.beq (:run c) (:id r)))
    (all_goals (simp only [clear-comp-run hc he])))
  (case [none]
    (simp only [clear-comp-run hc])
    (cases ht (task-find w (:of r)))
    (case [none] (simp only [clear-task-run ht]))
    (case [some t]
      (cases he (Nat.beq (:run t) (:id r)))
      (all_goals (simp only [clear-task-run ht he])))))

(a/theorem remove-if-empty-runs [w :- World, sub :- (List Nat)] (= (runs-of (remove-if-empty w sub)) (runs-of w))
  (cases he (subtree-empty w sub))
  (case [false] (simp only [remove-if-empty he]))
  (case [true] (simp only [remove-if-empty he]) (exact (nat-fold-frame (List RunRow) runs-of scope-del scope-del-runs _ _))))

(a/theorem retire-rows-lt [w :- World, rid :- Nat, r :- RunRow]
  (=> (= (run-find w rid) (Option.some RunRow r))
      (<= (+ (row-cnt (retire-local w r)) 1) (row-cnt w)))
  (intro hf)
  (have e (= (run-id r) rid)) (exact (tbl-find-id RunRow run-id rid r (:runs w) hf))
  (have e2 (= (:id r) rid)) (exact e)
  (have hr (= (runs-of (retire-local w r))
              (tbl-del run-id (:id r) (runs-of (close-local (clear-comp-run w r) (scope-subtree w (:scope r)))))))
  (simp only [retire-local retire-with])
  (exact (remove-if-empty-runs _ _))
  (have hi (= (run-ids (close-local (clear-comp-run w r) (scope-subtree w (:scope r)))) (run-ids w)))
  (have hc (= (run-ids (clear-comp-run w r)) (run-ids w)))
  (exact (congrArg (tbl-ids run-id) (clear-comp-run-runs w r)))
  (exact (Eq.trans (ri-close-local _ _) hc))
  (simp only [runs-of] at hr)
  (simp only [run-ids] at hi)
  (have hf2 (= (tbl-find run-id (:id r) (:runs w)) (Option.some RunRow r))) (rw [e2]) (exact hf)
  (have hm (= (nat-mem (:id r) (tbl-ids run-id (:runs (close-local (clear-comp-run w r) (scope-subtree w (:scope r)))))) true))
  (rw [hi nat-mem-ids]) (exact (tbl-find-has RunRow run-id (:id r) r (:runs w) hf2))
  (have l1 := (count-any-del-lt (:id r) _ hm))
  (have l2 (= (tbl-count run-any (:runs (close-local (clear-comp-run w r) (scope-subtree w (:scope r))))) (tbl-count run-any (:runs w))))
  (rw [count-any-ids count-any-ids hi])
  (simp only [row-cnt hr])
  (omega))

;; ---- follow-up jobs: at most #alive runs + 1

(a/defn job-wt [n :- Nat, j :- Job] Nat (match j [(jcancel r rep) 1] [(jretire r) 1] [(jclose s) (+ n 1)]))
(a/defn jobs-wt [n :- Nat, js :- (List Job)] Nat (match js [nil 0] [(cons h t) (+ (job-wt n h) (jobs-wt n t))]))
;; the potential: |jobs| + n #jclose + (n+1) #alive runs + n #run rows
(a/defn casc-pot [n :- Nat, w :- World, js :- (List Job)] Nat
  (+ (jobs-wt n js) (+ (* (+ n 1) (alive-cnt w)) (* n (row-cnt w)))))

(a/theorem jobs-wt-append [n :- Nat, xs :- (List Job), ys :- (List Job)]
  (= (jobs-wt n (List.append Job xs ys)) (+ (jobs-wt n xs) (jobs-wt n ys)))
  (induction xs)
  (case [nil] (simp [List.append jobs-wt]))
  (case [cons h t ih] (simp only [List.append jobs-wt ih]) (omega)))

(a/theorem jobs-wt-cancel [n :- Nat, xs :- (List Nat)] (= (jobs-wt n (cancel-jobs xs)) (List.length xs))
  (induction xs)
  (case [nil] (simp [cancel-jobs jobs-wt]))
  (case [cons h t ih] (simp only [cancel-jobs jobs-wt job-wt List.length ih]) (omega)))

(a/theorem scan-length-le [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), q :- (=> A Bool),
                           h :- (forall [r :- A] (=> (= (p r) true) (= (q r) true))), xs :- (List A)]
  (<= (List.length (tbl-scan idf p xs)) (tbl-count q xs))
  (induction xs)
  (case [nil] (simp [tbl-scan tbl-count]))
  (case [cons hd t ih]
    (cases hp (p hd))
    (case [false] (simp only [tbl-scan hp tbl-count-cons]) (omega))
    (case [true] (simp only [tbl-scan hp tbl-count-cons List.length (h hd hp) b2n]) (omega))))

(a/theorem count-le-any [p :- (=> RunRow Bool), xs :- (List RunRow)] (<= (tbl-count p xs) (tbl-count run-any xs))
  (induction xs)
  (case [nil] (simp [tbl-count]))
  (case [cons hd t ih]
    (cases hp (p hd))
    (all_goals (simp only [tbl-count-cons hp run-any b2n]))
    (all_goals (omega))))

(a/theorem alive-le-rows [w :- World] (<= (alive-cnt w) (row-cnt w))
  (exact (count-le-any run-alive (:runs w))))

(a/theorem owned-runs-le [w :- World, sub :- (List Nat)] (<= (List.length (owned-runs w sub)) (alive-cnt w))
  (have h (forall [r :- RunRow] (=> (= (run-owned-by w sub r) true) (= (run-alive r) true))))
  (intros r hr) (simp only [run-owned-by Bool.and_eq_true] at hr) (exact (And.left hr))
  (exact (scan-length-le RunRow run-id (run-owned-by w sub) run-alive h (:runs w))))

;; ---- one pop lowers the potential by at least 1 (n bounds the run rows)

(a/theorem bc-of-job [w :- World, j :- Job]
  (=> (= (inv-sample w) true) (= (acts-alive w) true)
      (And (= (inv-sample (job-apply w j)) true)
           (And (= (acts-alive (job-apply w j)) true)
                (And (<= (alive-cnt (job-apply w j)) (alive-cnt w)) (<= (row-cnt (job-apply w j)) (row-cnt w))))))
  (intros h ha)
  (have h1 := (bc-job-apply (bnd-of w) w j (bc-of-bnd w h ha)))
  (have p := (bc-rest-parts _ _ (bc-rest-of _ _ h1)))
  (exact (And.intro (bc-sample _ _ h1) (And.intro (And.left p) (And.intro (And.left (And.right p)) (And.left (And.right (And.right p))))))))

(a/theorem mul-lt-step [n :- Nat, a :- Nat, b :- Nat]
  (=> (<= (+ b 1) a) (<= (+ (* (+ n 1) b) (+ n 1)) (* (+ n 1) a)))
  (intro h)
  (have h2 := (Nat.mul_le_mul_left (+ n 1) h))
  (rw [Nat.mul_add Nat.mul_one] at h2)
  (exact h2))

(a/theorem casc-step-pot [n :- Nat, w :- World, j :- Job, t :- (List Job)]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (<= (row-cnt w) n)
      (<= (+ (casc-pot n (job-apply w j) (List.append Job t (job-next w j))) 1) (casc-pot n w (List.cons Job j t))))
  (intros h ha hn)
  (have p := (bc-of-job w j h ha))
  (have la (<= (alive-cnt (job-apply w j)) (alive-cnt w))) (exact (And.left (And.right (And.right p))))
  (have lr (<= (row-cnt (job-apply w j)) (row-cnt w))) (exact (And.right (And.right (And.right p))))
  (have ma := (Nat.mul_le_mul_left (+ n 1) la))
  (have mr := (Nat.mul_le_mul_left n lr))
  (have ar := (alive-le-rows w))
  (simp only [casc-pot jobs-wt jobs-wt-append])
  (cases j)
  ;; jcancel
  (case [jcancel rid rep]
    (cases hf (run-find w rid))
    (case [none] (simp only [job-next hf jobs-wt]) (simp only [job-apply hf] at ma mr) (simp only [job-apply hf job-wt]) (omega))
    (case [some r]
      (cases hl (run-alive r))
      (case [false] (simp only [job-next hf hl jobs-wt]) (simp only [job-apply hf hl] at ma mr) (simp only [job-apply hf hl job-wt]) (omega))
      (case [true]
        (have lt := (cancel-alive-lt w rid r rep h ha hf hl))
        (have m1 := (mul-lt-step n _ _ lt))
        (have m2 (<= (* n (row-cnt (cancel-run-local w r rep))) (* n (row-cnt w))))
        (simp only [job-apply hf hl] at mr) (exact mr)
        (have ow := (owned-runs-le w (scope-subtree w (:scope r))))
        (simp only [job-next hf hl job-apply job-wt jobs-wt-append jobs-wt-cancel jobs-wt])
        (omega))))
  ;; jretire
  (case [jretire rid]
    (cases hf (run-find w rid))
    (case [none] (simp only [job-next hf jobs-wt]) (simp only [job-apply hf] at ma mr) (simp only [job-apply hf job-wt]) (omega))
    (case [some r]
      (cases hl (retirable r))
      (case [false] (simp only [job-next hf hl jobs-wt]) (simp only [job-apply hf hl] at ma mr) (simp only [job-apply hf hl job-wt]) (omega))
      (case [true]
        (have lt := (retire-rows-lt w rid r hf))
        (have m1 := (Nat.mul_le_mul_left n lt))
        (rw [Nat.mul_add Nat.mul_one] at m1)
        (have m2 (<= (* (+ n 1) (alive-cnt (retire-local w r))) (* (+ n 1) (alive-cnt w))))
        (simp only [job-apply hf hl] at ma) (exact ma)
        (have ow := (owned-runs-le w (scope-subtree w (:scope r))))
        (simp only [job-next hf hl job-apply job-wt jobs-wt-cancel])
        (omega))))
  ;; jclose
  (case [jclose s]
    (cases hs (scope-has w s))
    (case [false] (simp only [job-next hs jobs-wt]) (simp only [job-apply hs] at ma mr) (simp only [job-apply hs job-wt]) (omega))
    (case [true]
      (have ow := (owned-runs-le w (scope-subtree w s)))
      (simp only [job-apply hs] at ma mr)
      (simp only [job-next hs job-apply job-wt jobs-wt-cancel])
      (omega))))

;; ---- the induction over the fuel

(a/theorem casc-empties [n :- Nat, fuel :- (List Nat)]
  (forall [w :- World, js :- (List Job)]
    (=> (= (inv-sample w) true) (= (acts-alive w) true) (<= (row-cnt w) n)
        (< (casc-pot n w js) (List.length fuel))
        (= (jobs-empty (:rest (cascade fuel w js))) true)))
  (induction fuel)
  (case [nil] (intros w js h ha hn hp) (simp only [List.length] at hp) (omega))
  (case [cons x f ih]
    (intros w js h ha hn hp)
    (cases js)
    (case [nil] (simp [cascade jobs-empty]))
    (case [cons j t]
      (have p := (bc-of-job w j h ha))
      (have st := (casc-step-pot n w j t h ha hn))
      (have hn2 (<= (row-cnt (job-apply w j)) n))
      (exact (Nat.le_trans (And.right (And.right (And.right p))) hn))
      (have hp2 (< (casc-pot n (job-apply w j) (List.append Job t (job-next w j))) (List.length f)))
      (simp only [List.length] at hp) (omega)
      (simp only [cascade])
      (exact (ih (job-apply w j) (List.append Job t (job-next w j)) (And.left p) (And.left (And.right p)) hn2 hp2)))))

;; ---- casc-fuel is above the initial potential (n = #run rows)

(a/theorem rep-list-length [xs :- (List Nat), u :- (List Nat)]
  (= (List.length (rep-list xs u)) (* (List.length xs) (List.length u)))
  (induction xs)
  (case [nil] (simp [rep-list List.length]))
  (case [cons h t ih] (simp only [rep-list list-length-append ih List.length Nat.succ_mul Nat.add_mul Nat.one_mul]) (omega)))

(a/theorem job-zeros-length [js :- (List Job)] (= (List.length (job-zeros js)) (List.length js))
  (induction js)
  (case [nil] (simp [job-zeros List.length]))
  (case [cons h t ih] (simp only [job-zeros List.length ih])))

(a/theorem ids-length-rows [rs :- (List RunRow)] (= (List.length (tbl-ids run-id rs)) (tbl-count run-any rs))
  (induction rs)
  (case [nil] (simp [tbl-ids tbl-count]))
  (case [cons h t ih] (simp only [tbl-ids List.length ih tbl-count-cons run-any b2n])))

(a/theorem jobs-wt-le [n :- Nat, js :- (List Job)] (<= (jobs-wt n js) (* (List.length js) (+ n 1)))
  (induction js)
  (case [nil] (simp [jobs-wt List.length]))
  (case [cons h t ih]
    (have hj (<= (job-wt n h) (+ n 1)))
    (cases h)
    (all_goals (simp only [job-wt]))
    (all_goals (try (omega)))
    (simp only [jobs-wt List.length Nat.add_mul Nat.one_mul])
    (omega)))

(a/theorem casc-fuel-above [w :- World, js :- (List Job)]
  (< (casc-pot (row-cnt w) w js) (List.length (casc-fuel w js)))
  (have h1 := (jobs-wt-le (row-cnt w) js))
  (have h2 := (Nat.mul_le_mul_left (+ (row-cnt w) 1) (alive-le-rows w)))
  (simp only [casc-pot casc-fuel List.length list-length-append rep-list-length job-zeros-length ids-length-rows])
  (simp only [row-cnt] at h1 h2)
  (simp only [row-cnt])
  (simp only [Nat.mul_add Nat.add_mul Nat.mul_one Nat.one_mul] at h1 h2)
  (simp only [Nat.mul_add Nat.add_mul Nat.mul_one Nat.one_mul])
  (omega))

;; Theorem (P4): on a world with unique ids (inv-sample) where no activation belongs to a done
;; run (acts-alive), every cascade empties its worklist within casc-fuel
(a/theorem casc-done-ok [w :- World, js :- (List Job)]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (casc-done w js) true))
  (intros h ha)
  (simp only [casc-done cascade-run])
  (exact (casc-empties (row-cnt w) (casc-fuel w js) w js h ha (Nat.le_refl _) (casc-fuel-above w js))))

;; ===========================================================================
;; Part E. P2: every round lowers norm-measure; normalize ends normalized
;; ===========================================================================

;; ---- unique run and computation ids (from ids-ok)

(a/theorem runs-nodup [w :- World] (=> (= (inv-sample w) true) (= (nat-nodup (tbl-ids run-id (:runs w))) true))
  (intro h)
  (have hi := (And.right (And.right (inv-parts w h))))
  (simp only [ids-ok ids-unique all-ids Bool.and_eq_true] at hi)
  (exact (nat-nodup-app-left _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (And.left hi)))))))

(a/theorem comps-nodup [w :- World] (=> (= (inv-sample w) true) (= (nat-nodup (tbl-ids comp-id (:comps w))) true))
  (intro h)
  (have hi := (And.right (And.right (inv-parts w h))))
  (simp only [ids-ok ids-unique all-ids Bool.and_eq_true] at hi)
  (exact (nat-nodup-app-left _ _ (nat-nodup-app-right _ _ (And.left hi)))))

;; an id in the scan of p names, by unique ids, a row with p
(a/theorem scan-ids-mem [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), x :- Nat, xs :- (List A)]
  (=> (= (reach-mem x (tbl-scan idf p xs)) true) (= (nat-mem x (tbl-ids idf xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-scan reach-mem] at h))
  (case [cons h t ih]
    (intro hm)
    (cases hx (Nat.beq (idf h) x))
    (case [true] (simp [tbl-ids nat-mem hx]))
    (case [false]
      (have hm2 (= (reach-mem x (tbl-scan idf p t)) true))
      (cases hp (p h))
      (case [false] (simp only [tbl-scan hp] at hm) (exact hm))
      (case [true]
        (have hx2 (= (Nat.beq x (idf h)) false)) (rw [beq-comm]) (exact hx)
        (simp only [tbl-scan hp reach-mem-cons hx2 Bool.false_or] at hm) (exact hm))
      (simp only [tbl-ids nat-mem hx]) (exact (ih hm2)))))

(a/theorem scan-mem-find [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), x :- Nat, xs :- (List A)]
  (=> (= (reach-mem x (tbl-scan idf p xs)) true) (= (nat-nodup (tbl-ids idf xs)) true)
      (= (opt-test p (tbl-find idf x xs)) true))
  (induction xs)
  (case [nil] (intros h hn) (simp [tbl-scan reach-mem] at h))
  (case [cons h t ih]
    (intros hm hn)
    (simp only [tbl-ids nat-nodup Bool.and_eq_true] at hn)
    (cases hx (Nat.beq (idf h) x))
    (case [false]
      (have hm2 (= (reach-mem x (tbl-scan idf p t)) true))
      (cases hp (p h))
      (case [false] (simp only [tbl-scan hp] at hm) (exact hm))
      (case [true]
        (have hx2 (= (Nat.beq x (idf h)) false)) (rw [beq-comm]) (exact hx)
        (simp only [tbl-scan hp reach-mem-cons hx2 Bool.false_or] at hm) (exact hm))
      (simp only [tbl-find hx]) (exact (ih hm2 (And.right hn))))
    (case [true]
      (have e (= (idf h) x)) (exact (Nat.eq_of_beq_eq_true hx))
      (simp only [tbl-find hx opt-test])
      (cases hp (p h))
      (case [true] (rfl))
      (case [false]
        (simp only [tbl-scan hp] at hm)
        (have hin := (scan-ids-mem A idf p x t hm))
        (have hout (= (nat-mem (idf h) (tbl-ids idf t)) false)) (exact (bnot-true _ (And.left hn)))
        (rw [e] at hout)
        (rw [hin] at hout)
        (cases hout)))))

;; ---- counts

(a/defn act-cnt [w :- World] Nat (tbl-count comp-active (:comps w)))

(a/theorem scan-length-eq [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), xs :- (List A)]
  (= (List.length (tbl-scan idf p xs)) (tbl-count p xs))
  (induction xs)
  (case [nil] (simp [tbl-scan tbl-count]))
  (case [cons hd t ih]
    (cases hp (p hd))
    (all_goals (simp only [tbl-scan hp tbl-count-cons List.length b2n ih]))))

(a/theorem act-cnt-ids [w :- World] (= (act-cnt w) (List.length (active-ids w)))
  (simp only [act-cnt active-ids scan-length-eq]))

;; the round bundle: inv-sample, acts-alive, #alive runs <= a, #non-idle computations <= k
(a/defn bn [a :- Nat, k :- Nat, w :- World] Bool
  (Bool.and (inv-sample w) (Bool.and (acts-alive w) (Bool.and (Nat.ble (alive-cnt w) a) (Nat.ble (act-cnt w) k)))))

(a/theorem bn-parts [a :- Nat, k :- Nat, w :- World]
  (=> (= (bn a k w) true)
      (And (= (inv-sample w) true) (And (= (acts-alive w) true) (And (<= (alive-cnt w) a) (<= (act-cnt w) k)))))
  (intro h)
  (simp only [bn Bool.and_eq_true] at h)
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (And.intro (Nat.le_of_ble_eq_true (And.left (And.right (And.right h))))
                      (Nat.le_of_ble_eq_true (And.right (And.right (And.right h)))))))))

(a/theorem bn-intro [a :- Nat, k :- Nat, w :- World]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (<= (alive-cnt w) a) (<= (act-cnt w) k) (= (bn a k w) true))
  (intros h1 h2 h3 h4)
  (simp only [bn h1 h2 (Nat.ble_eq_true_of_le h3) (Nat.ble_eq_true_of_le h4) Bool.and_self]))

;; from the cascade bundle with the bounds of w
(a/theorem bn-lift [a :- Nat, k :- Nat, w :- World, w2 :- World]
  (=> (= (bc (bnd-of w) w2) true) (= (bn a k w) true) (= (bn a k w2) true))
  (intros h hb)
  (have p := (bn-parts a k w hb))
  (have q := (bc-rest-parts _ _ (bc-rest-of _ _ h)))
  (have e (= (act-cnt w2) (act-cnt w)))
  (have e2 (= (active-ids w2) (active-ids w))) (exact (And.right (And.right (And.right q))))
  (simp only [act-cnt-ids e2])
  (exact (bn-intro a k w2 (bc-sample _ _ h) (And.left q)
           (Nat.le_trans (And.left (And.right q)) (And.left (And.right (And.right p))))
           (Nat.le_trans (Nat.le_of_eq e) (And.right (And.right (And.right p)))))))

(a/theorem bn-bc [a :- Nat, k :- Nat, w :- World] (=> (= (bn a k w) true) (= (bc (bnd-of w) w) true))
  (intro h) (have p := (bn-parts a k w h)) (exact (bc-of-bnd w (And.left p) (And.left (And.right p)))))

(bc-copy! 'inv-detach-source)
(bc-copy! 'inv-detach-task)
(bc-copy! 'inv-detach-comp)

(bc-copy! 'inv-detach)

;; ---- the round keeps the bundle (both counts never grow)

(a/theorem bn-run-cascade [a :- Nat, k :- Nat, w :- World, js :- (List Job)]
  (=> (= (bn a k w) true) (= (bn a k (run-cascade w js)) true))
  (intro h) (exact (bn-lift a k w _ (bc-run-cascade (bnd-of w) w js (bn-bc a k w h)) h)))

(a/theorem bn-drop-edges [a :- Nat, k :- Nat, w :- World, p :- (=> EdgeRow Bool)]
  (=> (= (bn a k w) true) (= (bn a k (drop-edges w p)) true))
  (intro h) (exact (bn-lift a k w _ (bc-drop-edges (bnd-of w) w p (bn-bc a k w h)) h)))

(a/theorem bn-detach [a :- Nat, k :- Nat, w :- World]
  (=> (= (bn a k w) true) (= (bn a k (detach w)) true))
  (intro h) (exact (bn-lift a k w _ (bc-detach (bnd-of w) w (bn-bc a k w h)) h)))

(a/theorem act-cnt-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (= (act-cnt (drop-edges w p)) (act-cnt w))
  (simp only [act-cnt drop-edges set-comps set-edges])
  (have e := (scan-resync (tbl-filter p (:edges w)) (:comps w)))
  (rw [← (scan-length-eq CompRow comp-id comp-active (comps-resync (tbl-filter p (:edges w)) (:comps w)))])
  (rw [← (scan-length-eq CompRow comp-id comp-active (:comps w))])
  (rw [e]))

(a/theorem comp-make-idle-inactive [vs :- (List Valid), c :- CompRow] (= (comp-active (comp-make-idle vs c)) false) (rfl))

(a/theorem bn-demote-finish [a :- Nat, k :- Nat, w :- World, cid :- Nat, vs :- (List Valid)]
  (=> (= (bn a k w) true) (= (bn a k (demote-finish w cid vs)) true))
  (intro h)
  (have p := (bn-parts a k w h))
  (cases hf (comp-find w cid))
  (case [none] (simp only [demote-finish hf]) (exact h))
  (case [some c]
    (cases hk (demote-keep w c))
    (case [true]
      (simp only [demote-finish hf hk])
      (have l (<= (act-cnt (comp-upd w cid (comp-make-idle vs))) (act-cnt w)))
      (simp only [act-cnt comp-upd set-comps])
      (exact (count-upd-false-le CompRow comp-id cid (comp-make-idle vs) comp-active (comp-make-idle-inactive vs) (:comps w)))
      (exact (bn-intro a k _
               (inv-comp-upd w cid (comp-make-idle vs) (comp-make-idle-id vs) (comp-make-idle-pending vs) (And.left p))
               (And.left (And.right p)) (And.left (And.right (And.right p)))
               (Nat.le_trans l (And.right (And.right (And.right p)))))))
    (case [false]
      (simp only [demote-finish hf hk])
      (have h2 := (bn-drop-edges a k w (edge-avoids cid) h))
      (have p2 := (bn-parts a k _ h2))
      (have l (<= (act-cnt (comp-del (drop-edges w (edge-avoids cid)) cid)) (act-cnt (drop-edges w (edge-avoids cid)))))
      (simp only [act-cnt comp-del set-comps])
      (exact (tbl-count-del-le CompRow comp-id cid comp-active _))
      (have ha (= (acts-alive (comp-del (drop-edges w (edge-avoids cid)) cid)) (acts-alive (drop-edges w (edge-avoids cid))))) (rfl)
      (have hl (= (alive-cnt (comp-del (drop-edges w (edge-avoids cid)) cid)) (alive-cnt (drop-edges w (edge-avoids cid))))) (rfl)
      (rw [← ha] at p2) (rw [← hl] at p2)
      (exact (bn-intro a k _
               (inv-comp-del-unref _ cid (drop-edges-avoids w cid) (And.left p2))
               (And.left (And.right p2)) (And.left (And.right (And.right p2)))
               (Nat.le_trans l (And.right (And.right (And.right p2)))))))))

(a/theorem comp-inc-epoch-active [c :- CompRow] (= (comp-active (comp-inc-epoch c)) (comp-active c)) (rfl))
(a/theorem bc-demote-epoch [bnd :- Bnd, w :- World, cid :- Nat, b :- Bool]
  (=> (= (bc bnd w) true) (= (bc bnd (demote-epoch w cid b)) true))
  (intro h)
  (cases b)
  (simp only [demote-epoch]) (exact h)
  (simp only [demote-epoch])
  (exact (bc-comp-upd bnd w cid comp-inc-epoch comp-inc-epoch-comp-id comp-inc-epoch-pending comp-inc-epoch-active h)))
(a/theorem bn-demote-epoch [a :- Nat, k :- Nat, w :- World, cid :- Nat, b :- Bool]
  (=> (= (bn a k w) true) (= (bn a k (demote-epoch w cid b)) true))
  (intro h) (exact (bn-lift a k w _ (bc-demote-epoch (bnd-of w) w cid b (bn-bc a k w h)) h)))

(a/theorem bn-demote [a :- Nat, k :- Nat, w :- World, cid :- Nat]
  (=> (= (bn a k w) true) (= (bn a k (demote w cid)) true))
  (intro h)
  (cases hf (comp-find w cid))
  (case [none] (simp only [demote hf]) (exact h))
  (case [some c]
    (cases hi (:idle c))
    (case [true] (simp only [demote hf hi]) (exact h))
    (case [false]
      (simp only [demote hf hi demote-edges])
      (exact (bn-demote-finish a k _ cid _ (bn-drop-edges a k _ (not-dep-of cid) (bn-demote-epoch a k _ cid _ (bn-run-cascade a k w _ h))))))))

(a/theorem bn-nat-fold [a :- Nat, k :- Nat, f :- (=> World Nat World),
                        hf :- (forall [w :- World, x :- Nat] (=> (= (bn a k w) true) (= (bn a k (f w x)) true))),
                        xs :- (List Nat)]
  (forall [w :- World] (=> (= (bn a k w) true) (= (bn a k (nat-fold f w xs)) true)))
  (induction xs)
  (case [nil] (intros w hw) (simp only [nat-fold]) (exact hw))
  (case [cons h t ih] (intros w hw) (simp only [nat-fold]) (exact (ih (f w h) (hf w h hw)))))

(a/theorem bn-round-lv [a :- Nat, k :- Nat, w :- World, lv :- (List Nat)]
  (=> (= (bn a k w) true) (= (bn a k (norm-round-lv w lv)) true))
  (intro h)
  (simp only [norm-round-lv])
  (exact (bn-detach a k _ (bn-nat-fold a k demote (bn-demote a k) _ _ (bn-run-cascade a k w _ h)))))

;; ---- strict decrease

(a/theorem stray-scan-nil [lv :- (List Nat), rs :- (List RunRow)]
  (=> (= (tbl-all (run-norm lv) rs) true) (= (tbl-scan run-id (run-stray lv) rs) (List.nil Nat)))
  (induction rs)
  (case [nil] (intro h) (simp [tbl-scan]))
  (case [cons h t ih]
    (intro hp)
    (simp only [tbl-all Bool.and_eq_true] at hp)
    (simp only [tbl-scan run-stray (And.left hp) Bool.not_true])
    (exact (ih (And.right hp)))))

(a/theorem stray-scan-cons [lv :- (List Nat), rs :- (List RunRow)]
  (=> (= (tbl-scan run-id (run-stray lv) rs) (List.nil Nat)) (= (tbl-all (run-norm lv) rs) true))
  (induction rs)
  (case [nil] (intro h) (simp [tbl-all]))
  (case [cons h t ih]
    (intro hs)
    (cases hn (run-norm lv h))
    (case [false] (simp [tbl-scan run-stray hn] at hs))
    (case [true]
      (simp only [tbl-scan run-stray hn Bool.not_true] at hs)
      (simp only [tbl-all hn (ih hs) Bool.and_self]))))

(a/theorem comp-stray-nil [lv :- (List Nat), cs :- (List CompRow)]
  (=> (= (tbl-scan comp-id (comp-stray lv) cs) (List.nil Nat)) (= (tbl-all (comp-norm lv) cs) true))
  (induction cs)
  (case [nil] (intro h) (simp [tbl-all]))
  (case [cons h t ih]
    (intro hs)
    (cases hn (comp-norm lv h))
    (case [false] (simp [tbl-scan comp-stray hn] at hs))
    (case [true]
      (simp only [tbl-scan comp-stray hn Bool.not_true] at hs)
      (simp only [tbl-all hn (ih hs) Bool.and_self]))))

(a/theorem run-cascade-nil [w :- World] (= (run-cascade w (List.nil Job)) w)
  (simp only [run-cascade cascade-run casc-fuel cascade]))

(a/defn casc-tail [w :- World, js :- (List Job)] (List Nat)
  (List.append Nat (rep-list (job-zeros js) (List.cons Nat 0 (tbl-ids run-id (:runs w))))
    (rep-list (tbl-ids run-id (:runs w))
              (List.cons Nat 0 (List.cons Nat 0 (List.append Nat (tbl-ids run-id (:runs w)) (tbl-ids run-id (:runs w))))))))

(a/theorem run-cascade-cons [w :- World, j :- Job, t :- (List Job)]
  (= (run-cascade w (List.cons Job j t))
     (:world (cascade (casc-tail w (List.cons Job j t)) (job-apply w j) (List.append Job t (job-next w j)))))
  (simp only [run-cascade cascade-run casc-fuel cascade casc-tail]))

;; a stray run: the first cancel acts, #alive runs drops
(a/theorem cascade-first-lt [w :- World, x :- Nat, t :- (List Nat), r :- RunRow]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (run-find w x) (Option.some RunRow r)) (= (run-alive r) true)
      (And (<= (+ (alive-cnt (run-cascade w (cancel-jobs (List.cons Nat x t)))) 1) (alive-cnt w))
           (= (act-cnt (run-cascade w (cancel-jobs (List.cons Nat x t)))) (act-cnt w))))
  (intros h ha hf hr)
  (have lt := (cancel-alive-lt w x r false h ha hf hr))
  (have hj (= (job-apply w (Job.jcancel x false)) (cancel-run-local w r false))) (simp only [job-apply hf hr])
  (have p := (bc-of-job w (Job.jcancel x false) h ha))
  (have h1 := (bc-of-bnd _ (And.left p) (And.left (And.right p))))
  (have h2 := (bc-cascade (bnd-of (job-apply w (Job.jcancel x false))) (casc-tail w (cancel-jobs (List.cons Nat x t)))
                (job-apply w (Job.jcancel x false))
                (List.append Job (cancel-jobs t) (job-next w (Job.jcancel x false))) h1))
  (have q := (bc-rest-parts _ _ (bc-rest-of _ _ h2)))
  (have l1 := (And.left (And.right q)))
  (simp only [bnd-of hj] at l1)
  (have h3 := (bc-run-cascade (bnd-of w) w (cancel-jobs (List.cons Nat x t)) (bc-of-bnd w h ha)))
  (have q3 := (bc-rest-parts _ _ (bc-rest-of _ _ h3)))
  (have e3 (= (active-ids (run-cascade w (cancel-jobs (List.cons Nat x t)))) (active-ids w)))
  (exact (And.right (And.right (And.right q3))))
  (have lt2 (<= (+ (alive-cnt (job-apply w (Job.jcancel x false))) 1) (alive-cnt w))) (rw [hj]) (exact lt)
  (simp only [cancel-jobs run-cascade-cons] at e3)
  (simp only [cancel-jobs] at l1)
  (simp only [cancel-jobs run-cascade-cons])
  (apply And.intro)
  (omega)
  (simp only [act-cnt-ids e3]))

;; a stray computation: its demotion makes it idle or removes it
(a/theorem demote-finish-lt [w :- World, x :- Nat, vs :- (List Valid)]
  (=> (= (inv-sample w) true) (= (reach-mem x (active-ids w)) true)
      (<= (+ (act-cnt (demote-finish w x vs)) 1) (act-cnt w)))
  (intros h hm)
  (have hfind (= (opt-test comp-active (comp-find w x)) true))
  (exact (scan-mem-find CompRow comp-id comp-active x (:comps w) hm (comps-nodup w h)))
  (cases hf (comp-find w x))
  (case [none] (simp [opt-test hf] at hfind))
  (case [some c]
    (simp only [opt-test hf] at hfind)
    (cases hk (demote-keep w c))
    (case [true]
      (simp only [demote-finish hf hk act-cnt comp-upd set-comps])
      (exact (count-upd-false-lt CompRow comp-id x (comp-make-idle vs) comp-active (comp-make-idle-inactive vs) c (:comps w) hf hfind)))
    (case [false]
      (simp only [demote-finish hf hk])
      (have h2 := (inv-drop-edges w (edge-avoids x) h))
      (have hm2 (= (reach-mem x (active-ids (drop-edges w (edge-avoids x)))) true))
      (simp only [active-ids drop-edges set-comps set-edges scan-resync]) (exact hm)
      (have hfind2 (= (opt-test comp-active (comp-find (drop-edges w (edge-avoids x)) x)) true))
      (exact (scan-mem-find CompRow comp-id comp-active x _ hm2 (comps-nodup _ h2)))
      (have e := (act-cnt-drop-edges w (edge-avoids x)))
      (cases hf2 (comp-find (drop-edges w (edge-avoids x)) x))
      (case [none] (simp [opt-test hf2] at hfind2))
      (case [some c3]
        (simp only [opt-test hf2] at hfind2)
        (have l := (count-del-lt CompRow comp-id x comp-active c3 (:comps (drop-edges w (edge-avoids x))) hf2 hfind2))
        (have e2 (= (act-cnt (comp-del (drop-edges w (edge-avoids x)) x))
                    (tbl-count comp-active (tbl-del comp-id x (:comps (drop-edges w (edge-avoids x))))))) (rfl)
        (have e3 (= (act-cnt (drop-edges w (edge-avoids x))) (tbl-count comp-active (:comps (drop-edges w (edge-avoids x)))))) (rfl)
        (omega)))))

(a/theorem demote-lt [w :- World, x :- Nat, c :- CompRow]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (comp-find w x) (Option.some CompRow c)) (= (:idle c) false)
      (And (<= (+ (act-cnt (demote w x)) 1) (act-cnt w)) (<= (alive-cnt (demote w x)) (alive-cnt w))))
  (intros h ha hf hi)
  (have h1 := (bc-demote-epoch (bnd-of w) _ x (demote-cur w c) (bc-run-cascade (bnd-of w) w (cancel-jobs (demote-cancels w c)) (bc-of-bnd w h ha))))
  (have q := (bc-rest-parts _ _ (bc-rest-of _ _ h1)))
  (have hx (= (reach-mem x (active-ids w)) true))
  (have e (= (comp-id c) x)) (exact (tbl-find-id CompRow comp-id x c (:comps w) hf))
  (have hac (= (comp-active c) true)) (simp only [comp-active hi Bool.not_false])
  (have hm := (scan-mem CompRow comp-id comp-active c (:comps w) (tbl-find-mem CompRow comp-id x c (:comps w) hf) hac))
  (rw [e] at hm) (exact hm)
  (have hx2 (= (reach-mem x (active-ids (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) (not-dep-of x)))) true))
  (have e1 (= (active-ids (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c))) (active-ids w)))
  (exact (And.right (And.right (And.right q))))
  (simp only [active-ids drop-edges set-comps set-edges scan-resync])
  (simp only [active-ids] at e1)
  (rw [e1]) (exact hx)
  (have hs2 := (inv-drop-edges _ (not-dep-of x) (bc-sample _ _ h1)))
  (have l1 := (demote-finish-lt _ x (validity-of (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) x) hs2 hx2))
  (have l2 := (act-cnt-drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) (not-dep-of x)))
  (have l3 (= (act-cnt (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c))) (act-cnt w)))
  (simp only [act-cnt-ids]) (rw [(And.right (And.right (And.right q)))])
  (have b1 := (bn-demote-finish (alive-cnt w) (act-cnt w) (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) (not-dep-of x)) x
                (validity-of (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) x)
                (bn-drop-edges (alive-cnt w) (act-cnt w) _ (not-dep-of x)
                  (bn-demote-epoch (alive-cnt w) (act-cnt w) _ x (demote-cur w c)
                    (bn-run-cascade (alive-cnt w) (act-cnt w) w (cancel-jobs (demote-cancels w c))
                      (bn-intro _ _ w h ha (Nat.le_refl _) (Nat.le_refl _)))))))
  (have pb := (bn-parts _ _ _ b1))
  (simp only [demote hf hi demote-edges])
  (apply And.intro)
  (omega)
  (exact (And.left (And.right (And.right pb)))))

(a/theorem norm-measure-eq [w :- World] (= (norm-measure w) (+ (alive-cnt w) (act-cnt w))) (rfl))

(a/theorem stray-run-alive [lv :- (List Nat), r :- RunRow] (=> (= (run-stray lv r) true) (= (run-alive r) true))
  (intro h)
  (cases ha (run-alive r))
  (case [false] (simp [run-stray run-norm ha] at h))
  (case [true] (rfl)))

(a/theorem stray-comp-busy [lv :- (List Nat), c :- CompRow] (=> (= (comp-stray lv c) true) (= (:idle c) false))
  (intro h)
  (cases hi (:idle c))
  (case [false] (rfl))
  (case [true] (simp [comp-stray comp-norm hi] at h)))

;; one round of a world that is not normalized lowers #non-done runs + #non-idle computations
(a/theorem round-lt [w :- World, lv :- (List Nat)]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (normalized-with w lv) false)
      (< (norm-measure (norm-round-lv w lv)) (norm-measure w)))
  (intros h ha hn)
  (simp only [norm-measure-eq])
  (cases hs (tbl-scan run-id (run-stray lv) (:runs w)))
  (case [cons x t]
    (have hm (= (reach-mem x (List.cons Nat x t)) true)) (simp [reach-mem-cons Nat.beq_refl])
    (rw [← hs] at hm)
    (have hfind (= (opt-test (run-stray lv) (run-find w x)) true))
    (exact (scan-mem-find RunRow run-id (run-stray lv) x (:runs w) hm (runs-nodup w h)))
    (cases hf (run-find w x))
    (case [none] (simp [opt-test hf] at hfind))
    (case [some r]
      (simp only [opt-test hf] at hfind)
      (have c1 := (cascade-first-lt w x t r h ha hf (stray-run-alive lv r hfind)))
      (have h1 := (bc-run-cascade (bnd-of w) w (cancel-jobs (List.cons Nat x t)) (bc-of-bnd w h ha)))
      (have b1 := (bn-intro (alive-cnt (run-cascade w (cancel-jobs (List.cons Nat x t))))
                            (act-cnt (run-cascade w (cancel-jobs (List.cons Nat x t)))) _
                    (bc-sample _ _ h1) (bc-acts-alive _ _ h1) (Nat.le_refl _) (Nat.le_refl _)))
      (have b2 := (bn-detach _ _ _ (bn-nat-fold _ _ demote (bn-demote _ _) (tbl-scan comp-id (comp-stray lv) (:comps w)) _ b1)))
      (have p2 := (bn-parts _ _ _ b2))
      (simp only [norm-round-lv hs])
      (have l1 := (And.left (And.right (And.right p2))))
      (have l2 := (And.right (And.right (And.right p2))))
      (have c1a := (And.left c1))
      (have c1b := (And.right c1))
      (omega)))
  (case [nil]
    (have hr := (stray-scan-cons lv (:runs w) hs))
    (have hc (= (tbl-all (comp-norm lv) (:comps w)) false))
    (simp only [normalized-with hr Bool.true_and] at hn) (exact hn)
    (cases hcs (tbl-scan comp-id (comp-stray lv) (:comps w)))
    (case [nil] (have hc2 := (comp-stray-nil lv (:comps w) hcs)) (rw [hc2] at hc) (cases hc))
    (case [cons x t]
      (have hm (= (reach-mem x (List.cons Nat x t)) true)) (simp [reach-mem-cons Nat.beq_refl])
      (rw [← hcs] at hm)
      (have hfind (= (opt-test (comp-stray lv) (comp-find w x)) true))
      (exact (scan-mem-find CompRow comp-id (comp-stray lv) x (:comps w) hm (comps-nodup w h)))
      (cases hf (comp-find w x))
      (case [none] (simp [opt-test hf] at hfind))
      (case [some c]
        (simp only [opt-test hf] at hfind)
        (have d := (demote-lt w x c h ha hf (stray-comp-busy lv c hfind)))
        (have bd := (bn-demote (alive-cnt w) (act-cnt w) w x (bn-intro _ _ w h ha (Nat.le_refl _) (Nat.le_refl _))))
        (have pd := (bn-parts _ _ _ bd))
        (have b1 := (bn-intro (alive-cnt (demote w x)) (act-cnt (demote w x)) _
                      (And.left pd) (And.left (And.right pd)) (Nat.le_refl _) (Nat.le_refl _)))
        (have b2 := (bn-detach _ _ _ (bn-nat-fold _ _ demote (bn-demote _ _) t _ b1)))
        (have p2 := (bn-parts _ _ _ b2))
        (simp only [norm-round-lv hs hcs cancel-jobs run-cascade-nil nat-fold])
        (have l1 := (And.left (And.right (And.right p2))))
        (have l2 := (And.right (And.right (And.right p2))))
        (have d1 := (And.left d))
        (have d2 := (And.right d))
        (omega)))))

(a/theorem bn-round [w :- World]
  (=> (= (inv-sample w) true) (= (acts-alive w) true)
      (And (= (inv-sample (norm-round w)) true) (= (acts-alive (norm-round w)) true)))
  (intros h ha)
  (have b := (bn-round-lv (alive-cnt w) (act-cnt w) w (live-list w) (bn-intro _ _ w h ha (Nat.le_refl _) (Nat.le_refl _))))
  (have p := (bn-parts _ _ _ b))
  (exact (And.intro (And.left p) (And.left (And.right p)))))

(a/theorem norm-loop-ok [fuel :- (List Nat)]
  (forall [w :- World]
    (=> (= (inv-sample w) true) (= (acts-alive w) true) (< (norm-measure w) (List.length fuel))
        (= (normalized (norm-loop fuel w)) true)))
  (induction fuel)
  (case [nil] (intros w h ha hm) (simp only [List.length] at hm) (omega))
  (case [cons x f ih]
    (intros w h ha hm)
    (cases hn (normalized w))
    (case [true] (simp only [norm-loop hn]))
    (case [false]
      (have lt := (round-lt w (live-list w) h ha hn))
      (have p := (bn-round w h ha))
      (have hm2 (< (norm-measure (norm-round w)) (List.length f)))
      (simp only [List.length] at hm)
      (simp only [norm-round])
      (omega)
      (simp only [norm-loop hn])
      (exact (ih (norm-round w) (And.left p) (And.right p) hm2)))))

(a/theorem norm-fuel-length [w :- World] (= (List.length (norm-fuel w)) (+ (norm-measure w) 1))
  (simp only [norm-fuel norm-measure List.length list-length-append scan-length-eq]))

;; Theorem (P2): on a world with unique ids where no activation belongs to a done run,
;; normalization ends normalized (the loop's flag always holds)
(a/theorem normalized-ok [w :- World]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (normalized (normalize w)) true))
  (intros h ha)
  (have hd := (inv-detach w h))
  (have b := (bn-detach (alive-cnt w) (act-cnt w) w (bn-intro _ _ w h ha (Nat.le_refl _) (Nat.le_refl _))))
  (have p := (bn-parts _ _ _ b))
  (have hm (< (norm-measure (detach w)) (List.length (norm-fuel (detach w)))))
  (rw [norm-fuel-length]) (omega)
  (simp only [normalize])
  (exact (norm-loop-ok (norm-fuel (detach w)) (detach w) hd (And.left (And.right p)) hm)))

;; ---- through the Rule R rounds

(a/theorem acts-alive-norm-loop [fuel :- (List Nat)]
  (forall [w :- World] (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (acts-alive (norm-loop fuel w)) true)))
  (induction fuel)
  (case [nil] (intros w h ha) (simp only [norm-loop]) (exact ha))
  (case [cons x f ih]
    (intros w h ha)
    (cases hn (normalized w))
    (case [true] (simp only [norm-loop hn]) (exact ha))
    (case [false]
      (have p := (bn-round w h ha))
      (simp only [norm-loop hn])
      (exact (ih (norm-round w) (And.left p) (And.right p))))))

(a/theorem acts-alive-normalize [w :- World]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (acts-alive (normalize w)) true))
  (intros h ha)
  (have p := (bn-parts _ _ _ (bn-detach (alive-cnt w) (act-cnt w) w (bn-intro _ _ w h ha (Nat.le_refl _) (Nat.le_refl _)))))
  (simp only [normalize])
  (exact (acts-alive-norm-loop _ (detach w) (inv-detach w h) (And.left (And.right p)))))

(a/theorem act-run-ok-keep [K :- (=> Nat Bool), rs :- (List RunRow), a :- ActRow]
  (=> (= (act-run-ok rs a) true) (= (act-run-ok (tbl-keep K run-id rs) a) true))
  (intro h) (simp only [act-run-ok] at h) (simp only [act-run-ok])
  (exact (tbl-all-keep-same RunRow K run-id (run-ok-for (:run a)) rs h)))

(a/theorem acts-alive-filter [K :- (=> Nat Bool), w :- World]
  (=> (= (acts-alive w) true) (= (acts-alive (filter-world K w)) true))
  (intro h)
  (simp only [acts-alive filter-world])
  (simp only [acts-alive] at h)
  (exact (tbl-all-keep-same ActRow K act-id (act-run-ok (tbl-keep K run-id (:runs w))) (:acts w)
           (tbl-all-mono ActRow (act-run-ok (:runs w)) (act-run-ok (tbl-keep K run-id (:runs w)))
             (act-run-ok-keep K (:runs w)) (:acts w) h))))

(a/theorem acts-alive-round [w :- World]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (acts-alive (rule-r-round w)) true))
  (intros h ha)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (acts-alive-filter _ _ (acts-alive-normalize w h ha))))

(a/theorem rr-pre-ok [fuel :- (List Nat)]
  (forall [w0 :- World]
    (=> (= (inv-sample w0) true) (= (acts-alive w0) true) (= (rr-safe fuel w0) true)
        (And (= (inv-sample (rr-pre fuel w0)) true) (= (acts-alive (rr-pre fuel w0)) true))))
  (induction fuel)
  (case [nil] (intros w0 h ha hs) (simp only [rr-pre]) (exact (And.intro h ha)))
  (case [cons x f ih]
    (intros w0 h ha hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (cases ho (no-orphans (rule-r-round w0)))
    (case [true] (simp only [rr-pre ho]) (exact (And.intro h ha)))
    (case [false]
      (simp only [ho] at hs)
      (simp only [rr-pre ho])
      (exact (ih (rule-r-round w0) (inv-rule-r-round w0 h (And.left hs)) (acts-alive-round w0 h ha) (And.right hs))))))

;; P2 for Rule R: with filter-safe in every round, the last round's normalization is normalized
(a/theorem rule-r-normalized-ok [w :- World]
  (=> (= (inv-sample w) true) (= (acts-alive w) true) (= (rule-r-safe w) true)
      (= (normalized (normalize (rule-r-pre w))) true))
  (intros h ha hs)
  (simp only [rule-r-safe] at hs)
  (have p := (rr-pre-ok (rr-fuel w) w h ha hs))
  (simp only [rule-r-pre])
  (exact (normalized-ok _ (And.left p) (And.right p))))

;; ===========================================================================
;; Part F. The step
;; ===========================================================================

;; the step's world is normalized: no normalized hypothesis, only acts-alive of the raw world
;; (and rule-r-safe, as step-inv)
(a/theorem step-normalized-ok [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) true) (= (inv-sample w) true) (= (acts-alive (:world (raw w it))) true)
      (= (rule-r-safe (:world (raw w it))) true)
      (= (normalized (:world (world-step w it))) true))
  (intros ha h haa hs)
  (exact (step-normalized-total w it ha (rule-r-normalized-ok _ (raw-inv w it h) haa hs))))

(a/theorem step-i4-ok [w :- World, it :- Item, r :- RunRow]
  (=> (= (:accepted (raw w it)) true) (= (inv-sample w) true) (= (acts-alive (:world (raw w it))) true)
      (= (rule-r-safe (:world (raw w it))) true)
      (List.Mem r (:runs (:world (world-step w it)))) (= (run-alive r) true)
      (= (in-live (:world (world-step w it)) (:id r)) true))
  (intros ha h haa hs hm hr)
  (exact (normalized-runs _ r (step-normalized-ok w it ha h haa hs) hm hr)))
