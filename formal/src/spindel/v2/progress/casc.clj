(ns ^:ansatz/lean spindel.v2.progress.casc
  "Obligations P4 (cascade completion) and P2 (normalization terminates), kernel-checked (Init only).

  Hypothesis of both: `acts-alive w` (every run row whose id is an activation's run is not done).
  well-formed does not imply it: `resume` sets its run active, so a done run that kept an
  activation would be revived. spindel.v2.inv.acts proves it for every world the step reaches.

    cascade-done-ok         well-formed w, acts-alive w -> cascade-done w js                      (P4)
    normalized-ok        well-formed w, acts-alive w -> normalized (normalize w)             (P2)
    rule-r-normalized-ok ... and rule-r-safe w -> normalized (normalize (rule-r-last-input w))
    step-normalized-ok, step-i4-ok   the step theorems without the `normalized` flag

  P4 (Part D): potential `cascade-pot n w js` = jobs (a jclose weighs n+1) + (n+1) #alive runs +
  n #run rows; with n the initial #run rows, every pop lowers it by >= 1 (`cascade-step-pot`: an
  acting cancel lowers #alive and queues <= #alive + 1 jobs, an acting retire lowers #rows and
  queues <= #alive, an acting close queues <= #alive <= n; nothing ever raises #alive or #rows),
  and it starts below `cascade-fuel` (`cascade-fuel-above`).
  Monotonicity: the bundle `cascade-bound b w` = well-formed, acts-alive, #alive <= (:alive b), #rows <=
  (:rows b), the ids of the non-idle computations = (:active b), proved per primitive edit
  (Part B) and restated for the 38 composite cascade lemmas from the generic step tree (Part C:
  the bundle is the part `BC`; its own proofs: resume and its callers, T14's local part).
  P2 (Part E): `round-lt` (a round of a non-normalized world lowers `normalize-measure`: the first
  stray run's cancel acts, else the first stray computation is demoted (idle or removed); unique
  ids pick the stray row), `round-bound-round-lv` (no count grows: bundle `round-bound`), `normalize-loop-ok`."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.pres.part :refer [mk-bundle prim!]]
            [spindel.v2.pres.tree :as tree]))

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
(a/structure Bound [] (alive Nat) (rows Nat) (active (List Nat)))
(a/defn cascade-bound-rest [b :- Bound, w :- World] Bool
  (Bool.and (acts-alive w)
   (Bool.and (Nat.ble (alive-cnt w) (:alive b))
    (Bool.and (Nat.ble (row-cnt w) (:rows b)) (nat-list-eq (active-ids w) (:active b))))))
(a/defn cascade-bound [b :- Bound, w :- World] Bool (Bool.and (well-formed w) (cascade-bound-rest b w)))
(a/defn bound-of [w :- World] Bound (Bound.mk (alive-cnt w) (row-cnt w) (active-ids w)))

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

(a/theorem cascade-bound-well-formed [b :- Bound, w :- World] (=> (= (cascade-bound b w) true) (= (well-formed w) true))
  (intro h) (simp only [cascade-bound Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem cascade-bound-rest-of [b :- Bound, w :- World] (=> (= (cascade-bound b w) true) (= (cascade-bound-rest b w) true))
  (intro h) (simp only [cascade-bound Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem cascade-bound-intro [b :- Bound, w :- World] (=> (= (well-formed w) true) (= (cascade-bound-rest b w) true) (= (cascade-bound b w) true))
  (intros h1 h2) (simp only [cascade-bound h1 h2 Bool.and_self]))
(a/theorem cascade-bound-parts [b :- Bound, w :- World]
  (=> (= (cascade-bound b w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (cascade-bound-well-formed b w h))))

(a/theorem cascade-bound-rest-parts [b :- Bound, w :- World]
  (=> (= (cascade-bound-rest b w) true)
      (And (= (acts-alive w) true)
           (And (<= (alive-cnt w) (:alive b))
                (And (<= (row-cnt w) (:rows b)) (= (active-ids w) (:active b))))))
  (intro h)
  (simp only [cascade-bound-rest Bool.and_eq_true] at h)
  (exact (And.intro (And.left h)
           (And.intro (Nat.le_of_ble_eq_true (And.left (And.right h)))
             (And.intro (Nat.le_of_ble_eq_true (And.left (And.right (And.right h))))
                        (nat-list-eq-eq _ _ (And.right (And.right (And.right h)))))))))

(a/theorem cascade-bound-rest-intro [b :- Bound, w :- World]
  (=> (= (acts-alive w) true) (<= (alive-cnt w) (:alive b)) (<= (row-cnt w) (:rows b))
      (= (active-ids w) (:active b)) (= (cascade-bound-rest b w) true))
  (intros h1 h2 h3 h4)
  (simp only [cascade-bound-rest Bool.and_eq_true h1 h4 nat-list-eq-refl (Nat.ble_eq_true_of_le h2) (Nat.ble_eq_true_of_le h3)]))

;; the frame: acts-alive kept, both counts down, the active ids unchanged
(a/theorem cascade-bound-rest-mono [b :- Bound, w :- World, w2 :- World]
  (=> (=> (= (acts-alive w) true) (= (acts-alive w2) true))
      (<= (alive-cnt w2) (alive-cnt w)) (<= (row-cnt w2) (row-cnt w)) (= (active-ids w2) (active-ids w))
      (= (cascade-bound-rest b w) true) (= (cascade-bound-rest b w2) true))
  (intros ha hl hr he h)
  (have p := (cascade-bound-rest-parts b w h))
  (exact (cascade-bound-rest-intro b w2 (ha (And.left p)) (Nat.le_trans hl (And.left (And.right p)))
           (Nat.le_trans hr (And.left (And.right (And.right p))))
           (Eq.trans he (And.right (And.right (And.right p)))))))

(a/theorem ble-refl [n :- Nat] (= (Nat.ble n n) true) (exact (Nat.ble_eq_true_of_le (Nat.le_refl n))))

(a/theorem cascade-bound-of-bnd [w :- World] (=> (= (well-formed w) true) (= (acts-alive w) true) (= (cascade-bound (bound-of w) w) true))
  (intros h1 h2)
  (have h3 (= (cascade-bound-rest (bound-of w) w) true))
  (simp only [cascade-bound-rest bound-of h2 ble-refl nat-list-eq-refl Bool.and_self])
  (exact (cascade-bound-intro (bound-of w) w h1 h3)))

;; ===========================================================================
;; Part B. cascade-bound-rest under the primitive edits
;; ===========================================================================

(a/theorem cascade-bound-rest-same [b :- Bound, w :- World, w2 :- World]
  (=> (= (acts-alive w2) (acts-alive w)) (= (alive-cnt w2) (alive-cnt w)) (= (row-cnt w2) (row-cnt w))
      (= (active-ids w2) (active-ids w)) (= (cascade-bound-rest b w2) (cascade-bound-rest b w)))
  (intros h1 h2 h3 h4) (simp only [cascade-bound-rest h1 h2 h3 h4]))

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

(a/theorem cascade-bound-rest-run-upd [b :- Bound, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                            hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                            hal :- (forall [r :- RunRow] (= (run-alive (f r)) (run-alive r)))]
  (= (cascade-bound-rest b (run-upd w x f)) (cascade-bound-rest b w))
  (have e2 (= (alive-cnt (run-upd w x f)) (alive-cnt w)))
  (simp only [alive-cnt run-upd set-runs]) (exact (tbl-count-upd-same RunRow run-id x f run-alive hal (:runs w)))
  (have e3 (= (row-cnt (run-upd w x f)) (row-cnt w)))
  (simp only [row-cnt run-upd set-runs])
  (exact (tbl-count-upd-same RunRow run-id x f run-any (fn [r :- RunRow] (Eq.refl true)) (:runs w)))
  (exact (cascade-bound-rest-same b w (run-upd w x f) (acts-alive-run-upd w x f hid hal) e2 e3 (rfl))))

(a/theorem act-run-ok-del [rs :- (List RunRow), x :- Nat, a :- ActRow]
  (=> (= (act-run-ok rs a) true) (= (act-run-ok (tbl-del run-id x rs) a) true))
  (intro h)
  (simp only [act-run-ok] at h) (simp only [act-run-ok])
  (exact (tbl-all-del RunRow run-id x (run-ok-for (:run a)) (run-ok-for (:run a))
           (fn [r :- RunRow, h1 :- (= (run-ok-for (:run a) r) true), h2 :- (= (Nat.beq (run-id r) x) false)] h1)
           rs h)))

(a/theorem cascade-bound-rest-run-del [b :- Bound, w :- World, x :- Nat]
  (=> (= (cascade-bound-rest b w) true) (= (cascade-bound-rest b (run-del w x)) true))
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
  (exact (cascade-bound-rest-mono b w (run-del w x) ha hl hr (rfl) h)))

;; ---- activations

(a/theorem cascade-bound-rest-act-upd [b :- Bound, w :- World, x :- Nat, f :- (=> ActRow ActRow),
                            hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c)))]
  (= (cascade-bound-rest b (act-upd w x f)) (cascade-bound-rest b w))
  (have hp (forall [c :- ActRow] (= (act-run-ok (:runs w) (f c)) (act-run-ok (:runs w) c))))
  (intro c) (simp only [act-run-ok (hr c)])
  (have e1 (= (acts-alive (act-upd w x f)) (acts-alive w)))
  (simp only [acts-alive act-upd set-acts])
  (exact (tbl-all-upd-same ActRow act-id x f (act-run-ok (:runs w)) hp (:acts w)))
  (exact (cascade-bound-rest-same b w (act-upd w x f) e1 (rfl) (rfl) (rfl))))

(a/theorem cascade-bound-rest-act-del [b :- Bound, w :- World, x :- Nat]
  (=> (= (cascade-bound-rest b w) true) (= (cascade-bound-rest b (act-del w x)) true))
  (intro h)
  (have ha (=> (= (acts-alive w) true) (= (acts-alive (act-del w x)) true)))
  (intro h1)
  (simp only [acts-alive act-del set-acts])
  (exact (tbl-all-del ActRow act-id x (act-run-ok (:runs w)) (act-run-ok (:runs w))
           (fn [r :- ActRow, h1 :- (= (act-run-ok (:runs w) r) true), h2 :- (= (Nat.beq (act-id r) x) false)] h1)
           (:acts w) h1))
  (exact (cascade-bound-rest-mono b w (act-del w x) ha (Nat.le_refl _) (Nat.le_refl _) (rfl) h)))

;; ---- computations

(a/theorem cascade-bound-rest-comp-upd [b :- Bound, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                             hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                             hac :- (forall [c :- CompRow] (= (comp-active (f c)) (comp-active c)))]
  (= (cascade-bound-rest b (comp-upd w x f)) (cascade-bound-rest b w))
  (have e (= (active-ids (comp-upd w x f)) (active-ids w)))
  (simp only [active-ids comp-upd set-comps])
  (exact (tbl-scan-upd-same CompRow comp-id x f comp-active hid hac (:comps w)))
  (exact (cascade-bound-rest-same b w (comp-upd w x f) (rfl) (rfl) (rfl) e)))

(a/theorem scan-resync [es :- (List EdgeRow), cs :- (List CompRow)]
  (= (tbl-scan comp-id comp-active (comps-resync es cs)) (tbl-scan comp-id comp-active cs))
  (induction cs)
  (case [nil] (simp [comps-resync tbl-scan]))
  (case [cons h t ih]
    (have e1 (= (comp-active (comp-resync es h)) (comp-active h))) (rfl)
    (have e2 (= (comp-id (comp-resync es h)) (comp-id h))) (rfl)
    (simp only [comps-resync tbl-scan e1 e2 ih])))

(a/theorem cascade-bound-rest-drop-edges [b :- Bound, w :- World, p :- (=> EdgeRow Bool)]
  (= (cascade-bound-rest b (drop-edges w p)) (cascade-bound-rest b w))
  (have e (= (active-ids (drop-edges w p)) (active-ids w)))
  (simp only [active-ids drop-edges set-comps set-edges])
  (exact (scan-resync (tbl-filter p (:edges w)) (:comps w)))
  (exact (cascade-bound-rest-same b w (drop-edges w p) (rfl) (rfl) (rfl) e)))

(a/theorem cascade-bound-rest-drop-cred [b :- Bound, w :- World, a :- Nat]
  (= (cascade-bound-rest b (drop-cred-edges w a)) (cascade-bound-rest b w))
  (simp only [drop-cred-edges])
  (rw [(cascade-bound-rest-comp-upd b _ a (comp-set-pending 0) (comp-set-pending-id 0) (fn [c :- CompRow] (Eq.refl (comp-active c))))]))

(a/theorem cascade-bound-rest-drop-act [b :- Bound, w :- World, a :- Nat]
  (=> (= (cascade-bound-rest b w) true) (= (cascade-bound-rest b (drop-act w a)) true))
  (intro h)
  (simp only [drop-act])
  (exact (cascade-bound-rest-act-del b _ a (Eq.trans (cascade-bound-rest-drop-cred b w a) h))))

(a/theorem cascade-bound-rest-remove-edge [b :- Bound, w :- World, x :- Nat]
  (= (cascade-bound-rest b (remove-edge w x)) (cascade-bound-rest b w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]))
    (case [true]
      (simp only [remove-edge hf hm])
      (rw [(cascade-bound-rest-comp-upd b _ (:creditor e) comp-dec-pending comp-dec-pending-id (fn [c :- CompRow] (Eq.refl (comp-active c))))]))))

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
;; Part C. The bundle under the primitive edits and through the composite lemmas
;; ===========================================================================

(a/theorem cascade-bound-run-upd [bnd :- Bound, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hal :- (forall [r :- RunRow] (= (run-alive (f r)) (run-alive r)))]
  (=> (= (cascade-bound bnd w) true) (= (cascade-bound bnd (run-upd w x f)) true))
  (intro h)
  (exact (cascade-bound-intro bnd _ (well-formed-run-upd w x f hf (cascade-bound-well-formed bnd w h))
           (Eq.trans (cascade-bound-rest-run-upd bnd w x f hf hal) (cascade-bound-rest-of bnd w h)))))

(a/theorem cascade-bound-act-upd [bnd :- Bound, w :- World, x :- Nat, f :- (=> ActRow ActRow),
                       hf :- (forall [r :- ActRow] (= (act-id (f r)) (act-id r))),
                       hr :- (forall [c :- ActRow] (= (:run (f c)) (:run c)))]
  (=> (= (cascade-bound bnd w) true) (= (cascade-bound bnd (act-upd w x f)) true))
  (intro h)
  (exact (cascade-bound-intro bnd _ (well-formed-act-upd w x f hf (cascade-bound-well-formed bnd w h))
           (Eq.trans (cascade-bound-rest-act-upd bnd w x f hr) (cascade-bound-rest-of bnd w h)))))

(a/theorem cascade-bound-comp-upd [bnd :- Bound, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hac :- (forall [c :- CompRow] (= (comp-active (f c)) (comp-active c)))]
  (=> (= (cascade-bound bnd w) true) (= (cascade-bound bnd (comp-upd w x f)) true))
  (intro h)
  (exact (cascade-bound-intro bnd _ (well-formed-comp-upd w x f hid hp (cascade-bound-well-formed bnd w h))
           (Eq.trans (cascade-bound-rest-comp-upd bnd w x f hid hac) (cascade-bound-rest-of bnd w h)))))

;; The bundle as a part (spindel.v2.pres.part). Its cell for a primitive edit is the well-formed lemma and
;; a cascade-bound-rest proof (`prim!`): a form over the lemma's binders, its premises `h0 ... hn` and `R` =
;; cascade-bound-rest of the input world; nil = the edit leaves cascade-bound-rest definitionally unchanged.
;; The composite lemmas are restated from the generic step tree (spindel.v2.pres.tree, `restate!`), each
;; where it is first used; the lemmas that revive or cancel a run have proofs written here (:over).

(def BC (mk-bundle 'cascade-bound '[bnd :- Bound] "cascade-bound-"
                   ;; the row-function lemmas of the bundle take one more argument than their well-formed versions
                   {'well-formed-comp-upd ['(fn [c :- CompRow] (Eq.refl (comp-active c))) 5]
                    'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (run-alive r))) 4]
                    'well-formed-act-upd ['(fn [c :- ActRow] (Eq.refl (:run c))) 4]}))
(swap! (:renames BC) assoc 'well-formed-run-upd 'cascade-bound-run-upd 'well-formed-act-upd 'cascade-bound-act-upd
       'well-formed-comp-upd 'cascade-bound-comp-upd 'well-formed-parts 'cascade-bound-parts)

;; edits that touch neither runs, activations nor computations (rfl frame)
(doseq [o '[well-formed-scope-upd well-formed-source-upd well-formed-task-upd well-formed-resource-upd
            well-formed-cleanup-del well-formed-cleanup-ins well-formed-edge-upd well-formed-scope-del]]
  (prim! BC o nil))
;; runs, activations, computations
(doseq [[o rest-f] '[[well-formed-run-del (cascade-bound-rest-run-del bnd w x R)]
                     [well-formed-remove-edge (Eq.trans (cascade-bound-rest-remove-edge bnd w x) R)]
                     [well-formed-drop-cred-edges (Eq.trans (cascade-bound-rest-drop-cred bnd w a) R)]
                     [well-formed-drop-act (cascade-bound-rest-drop-act bnd w a R)]
                     [well-formed-drop-edges (Eq.trans (cascade-bound-rest-drop-edges bnd w p) R)]]]
  (prim! BC o rest-f))

(tree/part! BC
  :over '{well-formed-resume           cascade-bound-resume             ; a run with an activation is alive: nothing revives
          well-formed-fill-slot        cascade-bound-fill-slot
          well-formed-fire-dep         cascade-bound-fire-dep
          well-formed-fire-wait-act    cascade-bound-fire-wait-act
          well-formed-cancel-run-local cascade-bound-cancel-run-local}) ; the cancelled run is no longer alive

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

(a/theorem cascade-bound-acts-alive [bnd :- Bound, w :- World] (=> (= (cascade-bound bnd w) true) (= (acts-alive w) true))
  (intro h) (exact (And.left (cascade-bound-rest-parts bnd w (cascade-bound-rest-of bnd w h)))))

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

(a/theorem cascade-bound-rest-revive [b :- Bound, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                           hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                           hal :- (forall [r :- RunRow] (= (run-alive (f r)) true))]
  (=> (= (tbl-all (run-ok-for x) (:runs w)) true) (= (cascade-bound-rest b w) true) (= (cascade-bound-rest b (run-upd w x f)) true))
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
  (exact (cascade-bound-rest-mono b w (run-upd w x f) ha hl hr (rfl) h)))

(a/theorem run-set-act-active-alive [r :- RunRow] (= (run-alive (run-set-act act-active r)) true) (rfl))

;; Z#50: resume wakes only a parked run, so it keeps every run's aliveness (a frame)
(a/theorem run-wake-alive [r :- RunRow] (= (run-alive (run-wake r)) (run-alive r))
  (cases h (Nat.beq (:act r) act-parked))
  (case [false] (simp only [run-alive run-wake wake-act h]))
  (case [true]
    (have e (= (:act r) act-parked)) (exact (Nat.eq_of_beq_eq_true h))
    (simp only [run-alive run-wake wake-act h e])))

(a/theorem cascade-bound-resume [bnd :- Bound, w :- World, a :- ActRow]
  (=> (= (act-run-ok (:runs w) a) true) (= (cascade-bound bnd w) true) (= (cascade-bound bnd (resume w a)) true))
  (intros ha h)
  (exact (cascade-bound-run-upd bnd _ (:run a) run-wake run-wake-run-id run-wake-alive (cascade-bound-drop-act bnd w (:id a) h))))

(a/theorem cascade-bound-fill-slot [bnd :- Bound, w :- World, a :- ActRow, x :- Nat, v :- RunResult]
  (=> (= (act-run-ok (:runs w) a) true) (= (cascade-bound bnd w) true) (= (cascade-bound bnd (fill-slot w a x v)) true))
  (intros ha h)
  (cases hm (act-ready (act-fill x v a)))
  (simp only [fill-slot hm])
  (exact (cascade-bound-act-upd bnd w (:id a) (act-fill x v) (act-fill-act-id x v) (fn [c :- ActRow] (Eq.refl (:run c))) h))
  (simp only [fill-slot hm]) (exact (cascade-bound-resume bnd w a ha h)))

(tree/restate! BC '[well-formed-invalidate well-formed-dep-consumed])
(a/theorem cascade-bound-fire-dep [bnd :- Bound, w :- World, e :- EdgeRow]
  (=> (= (cascade-bound bnd w) true) (= (cascade-bound bnd (fire-dep w e)) true))
  (intro h)
  (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha]) (exact (cascade-bound-invalidate bnd w e h))
  (have hok := (acts-alive-mem w a (cascade-bound-acts-alive bnd w h) (act-with-member-mem (:id e) (:acts w) a ha)))
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc]) (exact (cascade-bound-invalidate bnd w e h))
  (simp only [fire-dep ha hc deliver-dep])
  (have hok2 (= (act-run-ok (:runs (dep-consumed w e)) a) true))
  (exact (Eq.trans (congrArg (fn [rs :- (List RunRow)] (act-run-ok rs a)) (dep-consumed-runs w e)) hok))
  (exact (cascade-bound-fill-slot bnd _ a _ _ hok2 (cascade-bound-dep-consumed bnd w e h))))

(tree/restate! BC '[well-formed-edge-set-phase])
(a/theorem cascade-bound-fire-wait-act [bnd :- Bound, res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (cascade-bound bnd w) true) (= (cascade-bound bnd (fire-wait-act res w e)) true))
  (intro h)
  (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
  (simp only [fire-wait-act ha]) (exact (cascade-bound-edge-set-phase bnd w (:id e) ph-fired h))
  (have hok := (acts-alive-mem w a (cascade-bound-acts-alive bnd w h) (tbl-find-mem ActRow act-id (:creditor e) a (:acts w) ha)))
  (cases hc (run-current w (:run a)))
  (simp only [fire-wait-act ha hc]) (exact (cascade-bound-edge-set-phase bnd w (:id e) ph-fired h))
  (have hok2 (= (act-run-ok (:runs (edge-upd w (:id e) (edge-set-phase ph-fired))) a) true)) (exact hok)
  (simp only [fire-wait-act ha hc]) (exact (cascade-bound-fill-slot bnd _ a _ _ hok2 (cascade-bound-edge-set-phase bnd w (:id e) ph-fired h))))

(tree/restate! BC '[well-formed-fire-edge])

;; ---- T14's local part: the run is done and its activations are gone

(a/theorem cascade-bound-weaken [b :- Bound, b2 :- Bound, w :- World]
  (=> (= (cascade-bound b w) true) (<= (:alive b) (:alive b2)) (<= (:rows b) (:rows b2)) (= (:active b) (:active b2))
      (= (cascade-bound b2 w) true))
  (intros h h1 h2 h3)
  (have p := (cascade-bound-rest-parts b w (cascade-bound-rest-of b w h)))
  (exact (cascade-bound-intro b2 w (cascade-bound-well-formed b w h)
           (cascade-bound-rest-intro b2 w (And.left p) (Nat.le_trans (And.left (And.right p)) h1)
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

(a/theorem cancel-acts-cascade-bound [w :- World, x :- Nat]
  (=> (= (well-formed w) true) (= (acts-alive w) true)
      (= (cascade-bound (Bound.mk (alive-cnt (run-upd w x run-cancel-row)) (row-cnt w) (active-ids w))
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
  (exact (cascade-bound-intro (Bound.mk (alive-cnt (run-upd w x run-cancel-row)) (row-cnt w) (active-ids w))
           (cancel-acts (run-upd w x run-cancel-row) x)
           (well-formed-cancel-acts (run-upd w x run-cancel-row) x (well-formed-run-upd w x run-cancel-row run-cancel-row-id h))
           (cascade-bound-rest-intro (Bound.mk (alive-cnt (run-upd w x run-cancel-row)) (row-cnt w) (active-ids w))
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

(tree/restate! BC '[well-formed-cancel-debtor])
(tree/restate! BC '[well-formed-cleanup-set])
(tree/restate! BC '[well-formed-cancel-res])

(a/theorem cascade-bound-cancel-tail [bnd :- Bound, w :- World, r :- RunRow, rep :- Bool]
  (=> (= (cascade-bound bnd (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r))) true)
      (= (cascade-bound bnd (cancel-run-local w r rep)) true))
  (intro h)
  (simp only [cancel-run-local])
  (exact (cascade-bound-cancel-debtor bnd rep _ r (cascade-bound-cleanup-set bnd _ (:id r) _ (cascade-bound-cancel-res bnd _ r h)))))

(a/theorem cascade-bound-cancel-run-local [bnd :- Bound, w :- World, r :- RunRow, rep :- Bool]
  (=> (= (cascade-bound bnd w) true) (= (cascade-bound bnd (cancel-run-local w r rep)) true))
  (intro h)
  (have p := (cascade-bound-rest-parts bnd w (cascade-bound-rest-of bnd w h)))
  (have h1 := (cancel-acts-cascade-bound w (:id r) (cascade-bound-well-formed bnd w h) (And.left p)))
  (exact (cascade-bound-cancel-tail bnd w r rep
           (cascade-bound-weaken _ bnd _ h1 (Nat.le_trans (alive-cancel-le w (:id r)) (And.left (And.right p)))
             (And.left (And.right (And.right p))) (And.right (And.right (And.right p)))))))

(tree/restate! BC '[well-formed-run-cascade])

;; ===========================================================================
;; Part D. P4: the cascade empties its worklist within cascade-fuel
;; ===========================================================================

;; ---- an acting cancel lowers #alive runs, an acting retire lowers #run rows

(a/theorem cancel-alive-lt [w :- World, rid :- Nat, r :- RunRow, rep :- Bool]
  (=> (= (well-formed w) true) (= (acts-alive w) true) (= (run-find w rid) (Option.some RunRow r))
      (= (run-alive r) true)
      (<= (+ (alive-cnt (cancel-run-local w r rep)) 1) (alive-cnt w)))
  (intros h ha hf hr)
  (have e (= (run-id r) rid)) (exact (tbl-find-id RunRow run-id rid r (:runs w) hf))
  (have e2 (= (:id r) rid)) (exact e)
  (have hf2 (= (run-find w (:id r)) (Option.some RunRow r))) (rw [e2]) (exact hf)
  (have h1 := (cascade-bound-cancel-tail _ w r rep (cancel-acts-cascade-bound w (:id r) h ha)))
  (have p := (cascade-bound-rest-parts _ _ (cascade-bound-rest-of _ _ h1)))
  (have l1 (<= (alive-cnt (cancel-run-local w r rep)) (alive-cnt (run-upd w (:id r) run-cancel-row))))
  (exact (And.left (And.right p)))
  (have l2 := (alive-cancel-lt w (:id r) r hf2 hr))
  (omega))

(a/theorem finalize-loop-runs [fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat)] (= (runs-of (:world (finalize-loop fuel w ds))) (runs-of w)))
  (induction fuel)
  (case [nil] (intros w ds) (simp only [finalize-loop]))
  (case [cons h f ih]
    (intros w ds)
    (cases ds)
    (simp only [finalize-loop])
    (rename_i d t)
    (simp only [finalize-loop])
    (exact (ih _ _))))

;; Z#53: closing a source wakes its waiters (T9 fills resume parked runs), so the run rows change
;; (act parked -> active) but keep their ids
(a/defn run-ids [w :- World] (List Nat) (tbl-ids run-id (:runs w)))
(a/theorem round-facts-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r)))]
  (= (run-ids (run-upd w x f)) (run-ids w))
  (exact (tbl-ids-upd RunRow run-id x f hf (:runs w))))
(a/theorem round-facts-resume [w :- World, a :- ActRow] (= (run-ids (resume w a)) (run-ids w))
  (simp only [resume])
  (exact (round-facts-run-upd _ (:run a) run-wake (fn [r :- RunRow] (Eq.refl (run-id r))))))
(a/theorem round-facts-fill-slot [w :- World, a :- ActRow, y :- Nat, v :- RunResult]
  (= (run-ids (fill-slot w a y v)) (run-ids w))
  (cases hm (act-ready (act-fill y v a)))
  (simp only [fill-slot hm])
  (simp only [fill-slot hm]) (exact (round-facts-resume w a)))
(a/theorem round-facts-remove-edge [w :- World, y :- Nat] (= (run-ids (remove-edge w y)) (run-ids w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf])
  (cases hm (:marked e))
  (all_goals (simp only [remove-edge hf hm])))
(a/theorem round-facts-dep-consumed [w :- World, e :- EdgeRow] (= (run-ids (dep-consumed w e)) (run-ids w))
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf])
  (simp only [dep-consumed hf]) (exact (round-facts-remove-edge w (:id e))))
(a/theorem round-facts-fire-dep [w :- World, e :- EdgeRow] (= (run-ids (fire-dep w e)) (run-ids w))
  (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha invalidate])
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc invalidate])
  (simp only [fire-dep ha hc deliver-dep])
  (exact (Eq.trans (round-facts-fill-slot _ a _ _) (round-facts-dep-consumed w e))))
(a/theorem round-facts-fire-wait [res :- RunResult, w :- World, e :- EdgeRow] (= (run-ids (fire-wait res w e)) (run-ids w))
  (cases hc (Nat.beq (:creditor e) 0))
  (case [true] (simp only [fire-wait hc]) (exact (round-facts-remove-edge w (:id e))))
  (case [false]
    (simp only [fire-wait hc])
    (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
    (simp only [fire-wait-act ha])
    (cases hr (run-current w (:run a)))
    (simp only [fire-wait-act ha hr])
    (simp only [fire-wait-act ha hr]) (exact (round-facts-fill-slot _ a _ _))))
(a/theorem round-facts-fire-edge [res :- RunResult, w :- World, y :- Nat] (= (run-ids (fire-edge res w y)) (run-ids w))
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
  (simp only [fire-edge hf hp hk1 hk2]) (exact (round-facts-fire-wait res w e))
  (simp only [fire-edge hf hp hk1]) (exact (round-facts-fire-dep w e)))
(a/theorem round-facts-t10-finalize-debtor [w :- World, d :- Nat] (= (run-ids (t10-finalize-debtor w d)) (run-ids w))
  (simp only [t10-finalize-debtor])
  (have e1 := (finalize-loop-runs (finalize-fuel w) w (List.cons Nat d (List.nil Nat))))
  (simp only [runs-of] at e1)
  (simp only [run-ids e1]))
(a/theorem round-facts-source-upd [w :- World, x :- Nat, f :- (=> SourceRow SourceRow)] (= (run-ids (source-upd w x f)) (run-ids w)) (rfl))
(a/theorem round-facts-deliver-res [w :- World, x :- Nat, v :- Nat, res :- RunResult] (= (run-ids (deliver-res w x v res)) (run-ids w))
  (simp only [deliver-res])
  (exact (Eq.trans (round-facts-t10-finalize-debtor _ x)
           (Eq.trans (nat-fold-frame (List Nat) run-ids (fire-edge res) (round-facts-fire-edge res) _ _)
             (Eq.trans (nat-fold-frame (List Nat) run-ids (fire-edge res) (round-facts-fire-edge res) _ _) (round-facts-source-upd w x _))))))
(a/theorem round-facts-realize-link [w :- World, x :- Nat, v :- Nat, fl :- Bool, n :- Nat] (= (run-ids (realize-link w x v fl n)) (run-ids w))
  (simp only [realize-link]) (exact (Eq.trans (round-facts-deliver-res _ x v _) (round-facts-source-upd w x _))))
(a/theorem round-facts-end-link [w :- World, x :- Nat, fl :- Bool, v :- Nat] (= (run-ids (end-link w x fl v)) (run-ids w))
  (cases hp (link-pending w x))
  (simp only [end-link hp])
  (simp only [end-link hp]) (exact (round-facts-realize-link w x _ fl 0)))
(a/theorem round-facts-end-stream [w :- World, x :- Nat] (= (run-ids (end-stream w x)) (run-ids w))
  (cases hf (source-find w x)) (case' [some s]) (case' [none])
  (simp only [end-stream hf])
  (cases hk (Nat.beq (:kind s) sk-stream))
  (simp only [end-stream hf hk])
  (simp only [end-stream hf hk]) (exact (round-facts-end-link w _ false 0)))
(a/theorem round-facts-close-source-ended [w :- World, x :- Nat] (= (run-ids (close-source-ended w x)) (run-ids w))
  (simp only [close-source-ended t10-finalize-debtor wake-closed])
  (have e1 := (finalize-loop-runs (finalize-fuel (nat-fold (fire-edge (deb-result (source-upd w x source-close-row) x)) (source-upd w x source-close-row)
                                             (tbl-scan edge-id (close-wakes (:acts (source-upd w x source-close-row)) x) (:edges (source-upd w x source-close-row)))))
                             (nat-fold (fire-edge (deb-result (source-upd w x source-close-row) x)) (source-upd w x source-close-row)
                               (tbl-scan edge-id (close-wakes (:acts (source-upd w x source-close-row)) x) (:edges (source-upd w x source-close-row))))
                             (List.cons Nat x (List.nil Nat))))
  (simp only [runs-of] at e1)
  (simp only [run-ids e1])
  (exact (nat-fold-frame (List Nat) run-ids (fire-edge (deb-result (source-upd w x source-close-row) x))
           (round-facts-fire-edge (deb-result (source-upd w x source-close-row) x)) _ _)))
(a/theorem round-facts-close-source [w :- World, x :- Nat] (= (run-ids (close-source w x)) (run-ids w))
  (simp only [close-source]) (exact (Eq.trans (round-facts-close-source-ended _ x) (round-facts-end-stream w x))))
(a/theorem close-scope-id-runs [w :- World, x :- Nat] (= (runs-of (close-scope-id w x)) (runs-of w)) (rfl))
(a/theorem scope-del-runs [w :- World, x :- Nat] (= (runs-of (scope-del w x)) (runs-of w)) (rfl))
(a/theorem round-facts-close-scope-id [w :- World, x :- Nat] (= (run-ids (close-scope-id w x)) (run-ids w)) (rfl))

(a/theorem round-facts-close-local [w :- World, sub :- (List Nat)] (= (run-ids (close-local w sub)) (run-ids w))
  (simp only [close-local])
  (exact (Eq.trans (nat-fold-frame (List Nat) run-ids close-source round-facts-close-source _ _)
                   (nat-fold-frame (List Nat) run-ids close-scope-id round-facts-close-scope-id _ _))))

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
      (<= (+ (row-cnt (retire-run w r)) 1) (row-cnt w)))
  (intro hf)
  (have e (= (run-id r) rid)) (exact (tbl-find-id RunRow run-id rid r (:runs w) hf))
  (have e2 (= (:id r) rid)) (exact e)
  (have hr (= (runs-of (retire-run w r))
              (tbl-del run-id (:id r) (runs-of (close-local (clear-comp-run w r) (scope-subtree w (:scope r)))))))
  (simp only [retire-run t13-retire-with-subtree])
  (exact (remove-if-empty-runs _ _))
  (have hi (= (run-ids (close-local (clear-comp-run w r) (scope-subtree w (:scope r)))) (run-ids w)))
  (have hc (= (run-ids (clear-comp-run w r)) (run-ids w)))
  (exact (congrArg (tbl-ids run-id) (clear-comp-run-runs w r)))
  (exact (Eq.trans (round-facts-close-local _ _) hc))
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

(a/defn job-wt [n :- Nat, j :- Job] Nat (match j (jcancel r rep) 1 (jretire r) 1 (jclose s) (+ n 1)))
(a/defn jobs-wt [n :- Nat, js :- (List Job)] Nat (match js nil 0 (cons h t) (+ (job-wt n h) (jobs-wt n t))))
;; the potential: |jobs| + n #jclose + (n+1) #alive runs + n #run rows
(a/defn cascade-pot [n :- Nat, w :- World, js :- (List Job)] Nat
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

(a/theorem cascade-bound-of-job [w :- World, j :- Job]
  (=> (= (well-formed w) true) (= (acts-alive w) true)
      (And (= (well-formed (job-apply w j)) true)
           (And (= (acts-alive (job-apply w j)) true)
                (And (<= (alive-cnt (job-apply w j)) (alive-cnt w)) (<= (row-cnt (job-apply w j)) (row-cnt w))))))
  (intros h ha)
  (have h1 := (cascade-bound-job-apply (bound-of w) w j (cascade-bound-of-bnd w h ha)))
  (have p := (cascade-bound-rest-parts _ _ (cascade-bound-rest-of _ _ h1)))
  (exact (And.intro (cascade-bound-well-formed _ _ h1) (And.intro (And.left p) (And.intro (And.left (And.right p)) (And.left (And.right (And.right p))))))))

(a/theorem mul-lt-step [n :- Nat, a :- Nat, b :- Nat]
  (=> (<= (+ b 1) a) (<= (+ (* (+ n 1) b) (+ n 1)) (* (+ n 1) a)))
  (intro h)
  (have h2 := (Nat.mul_le_mul_left (+ n 1) h))
  (rw [Nat.mul_add Nat.mul_one] at h2)
  (exact h2))

(a/theorem cascade-step-pot [n :- Nat, w :- World, j :- Job, t :- (List Job)]
  (=> (= (well-formed w) true) (= (acts-alive w) true) (<= (row-cnt w) n)
      (<= (+ (cascade-pot n (job-apply w j) (List.append Job t (job-next w j))) 1) (cascade-pot n w (List.cons Job j t))))
  (intros h ha hn)
  (have p := (cascade-bound-of-job w j h ha))
  (have la (<= (alive-cnt (job-apply w j)) (alive-cnt w))) (exact (And.left (And.right (And.right p))))
  (have lr (<= (row-cnt (job-apply w j)) (row-cnt w))) (exact (And.right (And.right (And.right p))))
  (have ma := (Nat.mul_le_mul_left (+ n 1) la))
  (have mr := (Nat.mul_le_mul_left n lr))
  (have ar := (alive-le-rows w))
  (simp only [cascade-pot jobs-wt jobs-wt-append])
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
        (have m2 (<= (* (+ n 1) (alive-cnt (retire-run w r))) (* (+ n 1) (alive-cnt w))))
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

(a/theorem cascade-empties [n :- Nat, fuel :- (List Nat)]
  (forall [w :- World, js :- (List Job)]
    (=> (= (well-formed w) true) (= (acts-alive w) true) (<= (row-cnt w) n)
        (< (cascade-pot n w js) (List.length fuel))
        (= (jobs-empty (:rest (cascade fuel w js))) true)))
  (induction fuel)
  (case [nil] (intros w js h ha hn hp) (simp only [List.length] at hp) (omega))
  (case [cons x f ih]
    (intros w js h ha hn hp)
    (cases js)
    (case [nil] (simp [cascade jobs-empty]))
    (case [cons j t]
      (have p := (cascade-bound-of-job w j h ha))
      (have st := (cascade-step-pot n w j t h ha hn))
      (have hn2 (<= (row-cnt (job-apply w j)) n))
      (exact (Nat.le_trans (And.right (And.right (And.right p))) hn))
      (have hp2 (< (cascade-pot n (job-apply w j) (List.append Job t (job-next w j))) (List.length f)))
      (simp only [List.length] at hp) (omega)
      (simp only [cascade])
      (exact (ih (job-apply w j) (List.append Job t (job-next w j)) (And.left p) (And.left (And.right p)) hn2 hp2)))))

;; ---- cascade-fuel is above the initial potential (n = #run rows)

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

(a/theorem cascade-fuel-above [w :- World, js :- (List Job)]
  (< (cascade-pot (row-cnt w) w js) (List.length (cascade-fuel w js)))
  (have h1 := (jobs-wt-le (row-cnt w) js))
  (have h2 := (Nat.mul_le_mul_left (+ (row-cnt w) 1) (alive-le-rows w)))
  (simp only [cascade-pot cascade-fuel List.length list-length-append rep-list-length job-zeros-length ids-length-rows])
  (simp only [row-cnt] at h1 h2)
  (simp only [row-cnt])
  (simp only [Nat.mul_add Nat.add_mul Nat.mul_one Nat.one_mul] at h1 h2)
  (simp only [Nat.mul_add Nat.add_mul Nat.mul_one Nat.one_mul])
  (omega))

;; Theorem (P4): on a world with unique ids (well-formed) where no activation belongs to a done
;; run (acts-alive), every cascade empties its worklist within cascade-fuel
(a/theorem cascade-done-ok [w :- World, js :- (List Job)]
  (=> (= (well-formed w) true) (= (acts-alive w) true) (= (cascade-done w js) true))
  (intros h ha)
  (simp only [cascade-done cascade-run])
  (exact (cascade-empties (row-cnt w) (cascade-fuel w js) w js h ha (Nat.le_refl _) (cascade-fuel-above w js))))

;; ===========================================================================
;; Part E. P2: every round lowers normalize-measure; normalize ends normalized
;; ===========================================================================

;; ---- unique run and computation ids (from ids-ok)

(a/theorem runs-nodup [w :- World] (=> (= (well-formed w) true) (= (nat-nodup (tbl-ids run-id (:runs w))) true))
  (intro h)
  (have hi := (And.right (And.right (well-formed-parts w h))))
  (simp only [ids-ok ids-unique all-ids Bool.and_eq_true] at hi)
  (exact (nat-nodup-app-left _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (And.left hi)))))))

(a/theorem comps-nodup [w :- World] (=> (= (well-formed w) true) (= (nat-nodup (tbl-ids comp-id (:comps w))) true))
  (intro h)
  (have hi := (And.right (And.right (well-formed-parts w h))))
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

;; the round bundle: well-formed, acts-alive, #alive runs <= a, #non-idle computations <= k
(a/defn round-bound [a :- Nat, k :- Nat, w :- World] Bool
  (Bool.and (well-formed w) (Bool.and (acts-alive w) (Bool.and (Nat.ble (alive-cnt w) a) (Nat.ble (act-cnt w) k)))))

(a/theorem round-bound-parts [a :- Nat, k :- Nat, w :- World]
  (=> (= (round-bound a k w) true)
      (And (= (well-formed w) true) (And (= (acts-alive w) true) (And (<= (alive-cnt w) a) (<= (act-cnt w) k)))))
  (intro h)
  (simp only [round-bound Bool.and_eq_true] at h)
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (And.intro (Nat.le_of_ble_eq_true (And.left (And.right (And.right h))))
                      (Nat.le_of_ble_eq_true (And.right (And.right (And.right h)))))))))

(a/theorem round-bound-intro [a :- Nat, k :- Nat, w :- World]
  (=> (= (well-formed w) true) (= (acts-alive w) true) (<= (alive-cnt w) a) (<= (act-cnt w) k) (= (round-bound a k w) true))
  (intros h1 h2 h3 h4)
  (simp only [round-bound h1 h2 (Nat.ble_eq_true_of_le h3) (Nat.ble_eq_true_of_le h4) Bool.and_self]))

;; from the cascade bundle with the bounds of w
(a/theorem round-bound-lift [a :- Nat, k :- Nat, w :- World, w2 :- World]
  (=> (= (cascade-bound (bound-of w) w2) true) (= (round-bound a k w) true) (= (round-bound a k w2) true))
  (intros h hb)
  (have p := (round-bound-parts a k w hb))
  (have q := (cascade-bound-rest-parts _ _ (cascade-bound-rest-of _ _ h)))
  (have e (= (act-cnt w2) (act-cnt w)))
  (have e2 (= (active-ids w2) (active-ids w))) (exact (And.right (And.right (And.right q))))
  (simp only [act-cnt-ids e2])
  (exact (round-bound-intro a k w2 (cascade-bound-well-formed _ _ h) (And.left q)
           (Nat.le_trans (And.left (And.right q)) (And.left (And.right (And.right p))))
           (Nat.le_trans (Nat.le_of_eq e) (And.right (And.right (And.right p)))))))

(a/theorem round-bound-cascade-bound [a :- Nat, k :- Nat, w :- World] (=> (= (round-bound a k w) true) (= (cascade-bound (bound-of w) w) true))
  (intro h) (have p := (round-bound-parts a k w h)) (exact (cascade-bound-of-bnd w (And.left p) (And.left (And.right p)))))

(tree/restate! BC '[well-formed-detach-source])
(tree/restate! BC '[well-formed-detach-task])
(tree/restate! BC '[well-formed-detach-comp])

(tree/restate! BC '[well-formed-detach])
(tree/restate! BC '[well-formed-end-basis])

;; ---- the round keeps the bundle (both counts never grow)

(a/theorem round-bound-run-cascade [a :- Nat, k :- Nat, w :- World, js :- (List Job)]
  (=> (= (round-bound a k w) true) (= (round-bound a k (run-cascade w js)) true))
  (intro h) (exact (round-bound-lift a k w _ (cascade-bound-run-cascade (bound-of w) w js (round-bound-cascade-bound a k w h)) h)))

(a/theorem round-bound-drop-edges [a :- Nat, k :- Nat, w :- World, p :- (=> EdgeRow Bool)]
  (=> (= (round-bound a k w) true) (= (round-bound a k (drop-edges w p)) true))
  (intro h) (exact (round-bound-lift a k w _ (cascade-bound-drop-edges (bound-of w) w p (round-bound-cascade-bound a k w h)) h)))

(a/theorem round-bound-detach [a :- Nat, k :- Nat, w :- World]
  (=> (= (round-bound a k w) true) (= (round-bound a k (detach w)) true))
  (intro h) (exact (round-bound-lift a k w _ (cascade-bound-detach (bound-of w) w (round-bound-cascade-bound a k w h)) h)))

(a/theorem act-cnt-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (= (act-cnt (drop-edges w p)) (act-cnt w))
  (simp only [act-cnt drop-edges set-comps set-edges])
  (have e := (scan-resync (tbl-filter p (:edges w)) (:comps w)))
  (rw [← (scan-length-eq CompRow comp-id comp-active (comps-resync (tbl-filter p (:edges w)) (:comps w)))])
  (rw [← (scan-length-eq CompRow comp-id comp-active (:comps w))])
  (rw [e]))

(a/theorem comp-make-idle-inactive [vs :- (List Valid), c :- CompRow] (= (comp-active (comp-make-idle vs c)) false) (rfl))
(a/theorem comp-demote-row-inactive [vs :- (List Valid), c :- CompRow] (= (comp-active (comp-demote-row vs c)) false)
  (cases h (demote-idle c)) (all_goals (simp only [comp-demote-row h comp-active Bool.or_true Bool.true_or Bool.not_true Bool.not_false Bool.or_false Bool.false_or])))

(a/theorem round-bound-demote-finish [a :- Nat, k :- Nat, w :- World, cid :- Nat, vs :- (List Valid)]
  (=> (= (round-bound a k w) true) (= (round-bound a k (demote-finish w cid vs)) true))
  (intro h)
  (have p := (round-bound-parts a k w h))
  (cases hf (comp-find w cid))
  (case [none] (simp only [demote-finish hf]) (exact h))
  (case [some c]
    (cases hk (demote-keep w c))
    (case [true]
      (simp only [demote-finish hf hk])
      (have l (<= (act-cnt (comp-upd w cid (comp-demote-row vs))) (act-cnt w)))
      (simp only [act-cnt comp-upd set-comps])
      (exact (count-upd-false-le CompRow comp-id cid (comp-demote-row vs) comp-active (comp-demote-row-inactive vs) (:comps w)))
      (exact (round-bound-intro a k _
               (well-formed-comp-upd w cid (comp-demote-row vs) (comp-demote-row-id vs) (comp-demote-row-pending vs) (And.left p))
               (And.left (And.right p)) (And.left (And.right (And.right p)))
               (Nat.le_trans l (And.right (And.right (And.right p)))))))
    (case [false]
      (simp only [demote-finish hf hk])
      (have h2 := (round-bound-drop-edges a k w (edge-avoids cid) h))
      (have p2 := (round-bound-parts a k _ h2))
      (have l (<= (act-cnt (comp-del (drop-edges w (edge-avoids cid)) cid)) (act-cnt (drop-edges w (edge-avoids cid)))))
      (simp only [act-cnt comp-del set-comps])
      (exact (tbl-count-del-le CompRow comp-id cid comp-active _))
      (have ha (= (acts-alive (comp-del (drop-edges w (edge-avoids cid)) cid)) (acts-alive (drop-edges w (edge-avoids cid))))) (rfl)
      (have hl (= (alive-cnt (comp-del (drop-edges w (edge-avoids cid)) cid)) (alive-cnt (drop-edges w (edge-avoids cid))))) (rfl)
      (rw [← ha] at p2) (rw [← hl] at p2)
      (exact (round-bound-intro a k _
               (well-formed-comp-del-unref _ cid (drop-edges-avoids w cid) (And.left p2))
               (And.left (And.right p2)) (And.left (And.right (And.right p2)))
               (Nat.le_trans l (And.right (And.right (And.right p2)))))))))

(a/theorem comp-inc-epoch-active [c :- CompRow] (= (comp-active (comp-inc-epoch c)) (comp-active c)) (rfl))
(a/theorem cascade-bound-demote-epoch [bnd :- Bound, w :- World, cid :- Nat, b :- Bool]
  (=> (= (cascade-bound bnd w) true) (= (cascade-bound bnd (demote-epoch w cid b)) true))
  (intro h)
  (cases b)
  (simp only [demote-epoch]) (exact h)
  (simp only [demote-epoch])
  (exact (cascade-bound-comp-upd bnd w cid comp-inc-epoch comp-inc-epoch-comp-id comp-inc-epoch-pending comp-inc-epoch-active h)))
(a/theorem round-bound-demote-epoch [a :- Nat, k :- Nat, w :- World, cid :- Nat, b :- Bool]
  (=> (= (round-bound a k w) true) (= (round-bound a k (demote-epoch w cid b)) true))
  (intro h) (exact (round-bound-lift a k w _ (cascade-bound-demote-epoch (bound-of w) w cid b (round-bound-cascade-bound a k w h)) h)))

(a/theorem round-bound-end-basis [a :- Nat, k :- Nat, w :- World, cid :- Nat]
  (=> (= (round-bound a k w) true) (= (round-bound a k (end-basis w cid)) true))
  (intro h) (exact (round-bound-lift a k w _ (cascade-bound-end-basis (bound-of w) w cid (round-bound-cascade-bound a k w h)) h)))

(a/theorem round-bound-demote [a :- Nat, k :- Nat, w :- World, cid :- Nat]
  (=> (= (round-bound a k w) true) (= (round-bound a k (demote w cid)) true))
  (intro h)
  (cases hf (comp-find w cid))
  (case [none] (simp only [demote hf]) (exact h))
  (case [some c]
    (cases hi (:idle c))
    (case [true] (simp only [demote hf hi]) (exact h))
    (case [false]
      (simp only [demote hf hi demote-edges])
      (exact (round-bound-demote-finish a k _ cid _ (round-bound-end-basis a k _ cid (round-bound-drop-edges a k _ (not-dep-of cid) (round-bound-demote-epoch a k _ cid _ (round-bound-run-cascade a k w _ h)))))))))

(a/theorem round-bound-nat-fold [a :- Nat, k :- Nat, f :- (=> World Nat World),
                        hf :- (forall [w :- World, x :- Nat] (=> (= (round-bound a k w) true) (= (round-bound a k (f w x)) true))),
                        xs :- (List Nat)]
  (forall [w :- World] (=> (= (round-bound a k w) true) (= (round-bound a k (nat-fold f w xs)) true)))
  (induction xs)
  (case [nil] (intros w hw) (simp only [nat-fold]) (exact hw))
  (case [cons h t ih] (intros w hw) (simp only [nat-fold]) (exact (ih (f w h) (hf w h hw)))))

(a/theorem round-bound-round-lv [a :- Nat, k :- Nat, w :- World, lv :- (List Nat)]
  (=> (= (round-bound a k w) true) (= (round-bound a k (normalize-round-with-live w lv)) true))
  (intro h)
  (simp only [normalize-round-with-live])
  (exact (round-bound-detach a k _ (round-bound-nat-fold a k demote (round-bound-demote a k) _ _ (round-bound-run-cascade a k w _ h)))))

;; ---- strict decrease

(a/theorem stray-scan-nil [lv :- (List Nat), rs :- (List RunRow)]
  (=> (= (tbl-all (run-normalized lv) rs) true) (= (tbl-scan run-id (run-stray lv) rs) (List.nil Nat)))
  (induction rs)
  (case [nil] (intro h) (simp [tbl-scan]))
  (case [cons h t ih]
    (intro hp)
    (simp only [tbl-all Bool.and_eq_true] at hp)
    (simp only [tbl-scan run-stray (And.left hp) Bool.not_true])
    (exact (ih (And.right hp)))))

(a/theorem stray-scan-cons [lv :- (List Nat), rs :- (List RunRow)]
  (=> (= (tbl-scan run-id (run-stray lv) rs) (List.nil Nat)) (= (tbl-all (run-normalized lv) rs) true))
  (induction rs)
  (case [nil] (intro h) (simp [tbl-all]))
  (case [cons h t ih]
    (intro hs)
    (cases hn (run-normalized lv h))
    (case [false] (simp [tbl-scan run-stray hn] at hs))
    (case [true]
      (simp only [tbl-scan run-stray hn Bool.not_true] at hs)
      (simp only [tbl-all hn (ih hs) Bool.and_self]))))

(a/theorem comp-stray-nil [lv :- (List Nat), cs :- (List CompRow)]
  (=> (= (tbl-scan comp-id (comp-stray lv) cs) (List.nil Nat)) (= (tbl-all (comp-normalized lv) cs) true))
  (induction cs)
  (case [nil] (intro h) (simp [tbl-all]))
  (case [cons h t ih]
    (intro hs)
    (cases hn (comp-normalized lv h))
    (case [false] (simp [tbl-scan comp-stray hn] at hs))
    (case [true]
      (simp only [tbl-scan comp-stray hn Bool.not_true] at hs)
      (simp only [tbl-all hn (ih hs) Bool.and_self]))))

(a/theorem run-cascade-nil [w :- World] (= (run-cascade w (List.nil Job)) w)
  (simp only [run-cascade cascade-run cascade-fuel cascade]))

(a/defn cascade-tail [w :- World, js :- (List Job)] (List Nat)
  (List.append Nat (rep-list (job-zeros js) (List.cons Nat 0 (tbl-ids run-id (:runs w))))
    (rep-list (tbl-ids run-id (:runs w))
              (List.cons Nat 0 (List.cons Nat 0 (List.append Nat (tbl-ids run-id (:runs w)) (tbl-ids run-id (:runs w))))))))

(a/theorem run-cascade-cons [w :- World, j :- Job, t :- (List Job)]
  (= (run-cascade w (List.cons Job j t))
     (:world (cascade (cascade-tail w (List.cons Job j t)) (job-apply w j) (List.append Job t (job-next w j)))))
  (simp only [run-cascade cascade-run cascade-fuel cascade cascade-tail]))

;; a stray run: the first cancel acts, #alive runs drops
(a/theorem cascade-first-lt [w :- World, x :- Nat, t :- (List Nat), r :- RunRow]
  (=> (= (well-formed w) true) (= (acts-alive w) true) (= (run-find w x) (Option.some RunRow r)) (= (run-alive r) true)
      (And (<= (+ (alive-cnt (run-cascade w (cancel-jobs (List.cons Nat x t)))) 1) (alive-cnt w))
           (= (act-cnt (run-cascade w (cancel-jobs (List.cons Nat x t)))) (act-cnt w))))
  (intros h ha hf hr)
  (have lt := (cancel-alive-lt w x r false h ha hf hr))
  (have hj (= (job-apply w (Job.jcancel x false)) (cancel-run-local w r false))) (simp only [job-apply hf hr])
  (have p := (cascade-bound-of-job w (Job.jcancel x false) h ha))
  (have h1 := (cascade-bound-of-bnd _ (And.left p) (And.left (And.right p))))
  (have h2 := (cascade-bound-cascade (bound-of (job-apply w (Job.jcancel x false))) (cascade-tail w (cancel-jobs (List.cons Nat x t)))
                (job-apply w (Job.jcancel x false))
                (List.append Job (cancel-jobs t) (job-next w (Job.jcancel x false))) h1))
  (have q := (cascade-bound-rest-parts _ _ (cascade-bound-rest-of _ _ h2)))
  (have l1 := (And.left (And.right q)))
  (simp only [bound-of hj] at l1)
  (have h3 := (cascade-bound-run-cascade (bound-of w) w (cancel-jobs (List.cons Nat x t)) (cascade-bound-of-bnd w h ha)))
  (have q3 := (cascade-bound-rest-parts _ _ (cascade-bound-rest-of _ _ h3)))
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
  (=> (= (well-formed w) true) (= (reach-mem x (active-ids w)) true)
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
      (exact (count-upd-false-lt CompRow comp-id x (comp-demote-row vs) comp-active (comp-demote-row-inactive vs) c (:comps w) hf hfind)))
    (case [false]
      (simp only [demote-finish hf hk])
      (have h2 := (well-formed-drop-edges w (edge-avoids x) h))
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
  (=> (= (well-formed w) true) (= (acts-alive w) true) (= (comp-find w x) (Option.some CompRow c)) (= (:idle c) false)
      (= (:tomb c) false)
      (And (<= (+ (act-cnt (demote w x)) 1) (act-cnt w)) (<= (alive-cnt (demote w x)) (alive-cnt w))))
  (intros h ha hf hi ht)
  (have h1 := (cascade-bound-demote-epoch (bound-of w) _ x (demote-cur w c) (cascade-bound-run-cascade (bound-of w) w (cancel-jobs (demote-cancels w c)) (cascade-bound-of-bnd w h ha))))
  (have q := (cascade-bound-rest-parts _ _ (cascade-bound-rest-of _ _ h1)))
  (have hx (= (reach-mem x (active-ids w)) true))
  (have e (= (comp-id c) x)) (exact (tbl-find-id CompRow comp-id x c (:comps w) hf))
  (have hac (= (comp-active c) true)) (simp only [comp-active hi ht Bool.or_false Bool.not_false])
  (have hm := (scan-mem CompRow comp-id comp-active c (:comps w) (tbl-find-mem CompRow comp-id x c (:comps w) hf) hac))
  (rw [e] at hm) (exact hm)
  (have hx2 (= (reach-mem x (active-ids (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) (not-dep-of x)))) true))
  (have e1 (= (active-ids (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c))) (active-ids w)))
  (exact (And.right (And.right (And.right q))))
  (simp only [active-ids drop-edges set-comps set-edges scan-resync])
  (simp only [active-ids] at e1)
  (rw [e1]) (exact hx)
  (have bd := (round-bound-drop-edges (alive-cnt w) (act-cnt w) _ (not-dep-of x)
                (round-bound-demote-epoch (alive-cnt w) (act-cnt w) _ x (demote-cur w c)
                  (round-bound-run-cascade (alive-cnt w) (act-cnt w) w (cancel-jobs (demote-cancels w c))
                    (round-bound-intro _ _ w h ha (Nat.le_refl _) (Nat.le_refl _))))))
  (have pd := (round-bound-parts _ _ _ bd))
  (have hE := (cascade-bound-end-basis _ _ x (cascade-bound-of-bnd (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) (not-dep-of x))
                                   (And.left pd) (And.left (And.right pd)))))
  (have qE := (cascade-bound-rest-parts _ _ (cascade-bound-rest-of _ _ hE)))
  (have eE := (And.right (And.right (And.right qE))))
  (simp only [bound-of] at eE)
  (have hx3 (= (reach-mem x (active-ids (end-basis (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) (not-dep-of x)) x))) true))
  (rw [eE]) (exact hx2)
  (have hs2 := (cascade-bound-well-formed _ _ hE))
  (have l1 := (demote-finish-lt _ x (validity-of (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) x) hs2 hx3))
  (have l0 (= (act-cnt (end-basis (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) (not-dep-of x)) x))
              (act-cnt (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) (not-dep-of x)))))
  (simp only [act-cnt-ids]) (rw [eE])
  (have l2 := (act-cnt-drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) (not-dep-of x)))
  (have l3 (= (act-cnt (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c))) (act-cnt w)))
  (simp only [act-cnt-ids]) (rw [(And.right (And.right (And.right q)))])
  (have b1 := (round-bound-demote-finish (alive-cnt w) (act-cnt w) (end-basis (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) (not-dep-of x)) x) x
                (validity-of (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) x)
                (round-bound-end-basis (alive-cnt w) (act-cnt w) _ x bd)))
  (have pb := (round-bound-parts _ _ _ b1))
  (simp only [demote hf hi demote-edges])
  (apply And.intro)
  (omega)
  (exact (And.left (And.right (And.right pb)))))

(a/theorem normalize-measure-eq [w :- World] (= (normalize-measure w) (+ (alive-cnt w) (act-cnt w))) (rfl))

(a/theorem stray-run-alive [lv :- (List Nat), r :- RunRow] (=> (= (run-stray lv r) true) (= (run-alive r) true))
  (intro h)
  (cases ha (run-alive r))
  (case [false] (simp [run-stray run-normalized ha] at h))
  (case [true] (rfl)))

(a/theorem stray-comp-busy [lv :- (List Nat), c :- CompRow] (=> (= (comp-stray lv c) true) (= (:idle c) false))
  (intro h)
  (cases hi (:idle c))
  (case [false] (rfl))
  (case [true] (simp [comp-stray comp-normalized hi] at h)))
(a/theorem stray-comp-tomb [lv :- (List Nat), c :- CompRow] (=> (= (comp-stray lv c) true) (= (:tomb c) false))
  (intro h)
  (cases hi (:tomb c))
  (case [false] (rfl))
  (case [true] (simp [comp-stray comp-normalized hi] at h)))

;; one round of a world that is not normalized lowers #non-done runs + #non-idle computations
(a/theorem round-lt [w :- World, lv :- (List Nat)]
  (=> (= (well-formed w) true) (= (acts-alive w) true) (= (normalized-with w lv) false)
      (< (normalize-measure (normalize-round-with-live w lv)) (normalize-measure w)))
  (intros h ha hn)
  (simp only [normalize-measure-eq])
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
      (have h1 := (cascade-bound-run-cascade (bound-of w) w (cancel-jobs (List.cons Nat x t)) (cascade-bound-of-bnd w h ha)))
      (have b1 := (round-bound-intro (alive-cnt (run-cascade w (cancel-jobs (List.cons Nat x t))))
                            (act-cnt (run-cascade w (cancel-jobs (List.cons Nat x t)))) _
                    (cascade-bound-well-formed _ _ h1) (cascade-bound-acts-alive _ _ h1) (Nat.le_refl _) (Nat.le_refl _)))
      (have b2 := (round-bound-detach _ _ _ (round-bound-nat-fold _ _ demote (round-bound-demote _ _) (tbl-scan comp-id (comp-stray lv) (:comps w)) _ b1)))
      (have p2 := (round-bound-parts _ _ _ b2))
      (simp only [normalize-round-with-live hs])
      (have l1 := (And.left (And.right (And.right p2))))
      (have l2 := (And.right (And.right (And.right p2))))
      (have c1a := (And.left c1))
      (have c1b := (And.right c1))
      (omega)))
  (case [nil]
    (have hr := (stray-scan-cons lv (:runs w) hs))
    (have hc (= (tbl-all (comp-normalized lv) (:comps w)) false))
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
        (have d := (demote-lt w x c h ha hf (stray-comp-busy lv c hfind) (stray-comp-tomb lv c hfind)))
        (have bd := (round-bound-demote (alive-cnt w) (act-cnt w) w x (round-bound-intro _ _ w h ha (Nat.le_refl _) (Nat.le_refl _))))
        (have pd := (round-bound-parts _ _ _ bd))
        (have b1 := (round-bound-intro (alive-cnt (demote w x)) (act-cnt (demote w x)) _
                      (And.left pd) (And.left (And.right pd)) (Nat.le_refl _) (Nat.le_refl _)))
        (have b2 := (round-bound-detach _ _ _ (round-bound-nat-fold _ _ demote (round-bound-demote _ _) t _ b1)))
        (have p2 := (round-bound-parts _ _ _ b2))
        (simp only [normalize-round-with-live hs hcs cancel-jobs run-cascade-nil nat-fold])
        (have l1 := (And.left (And.right (And.right p2))))
        (have l2 := (And.right (And.right (And.right p2))))
        (have d1 := (And.left d))
        (have d2 := (And.right d))
        (omega)))))

(a/theorem round-bound-round [w :- World]
  (=> (= (well-formed w) true) (= (acts-alive w) true)
      (And (= (well-formed (normalize-round w)) true) (= (acts-alive (normalize-round w)) true)))
  (intros h ha)
  (have b := (round-bound-round-lv (alive-cnt w) (act-cnt w) w (live-list w) (round-bound-intro _ _ w h ha (Nat.le_refl _) (Nat.le_refl _))))
  (have p := (round-bound-parts _ _ _ b))
  (exact (And.intro (And.left p) (And.left (And.right p)))))

(a/theorem normalize-loop-ok [fuel :- (List Nat)]
  (forall [w :- World]
    (=> (= (well-formed w) true) (= (acts-alive w) true) (< (normalize-measure w) (List.length fuel))
        (= (normalized (normalize-loop fuel w)) true)))
  (induction fuel)
  (case [nil] (intros w h ha hm) (simp only [List.length] at hm) (omega))
  (case [cons x f ih]
    (intros w h ha hm)
    (cases hn (normalized w))
    (case [true] (simp only [normalize-loop hn]))
    (case [false]
      (have lt := (round-lt w (live-list w) h ha hn))
      (have p := (round-bound-round w h ha))
      (have hm2 (< (normalize-measure (normalize-round w)) (List.length f)))
      (simp only [List.length] at hm)
      (simp only [normalize-round])
      (omega)
      (simp only [normalize-loop hn])
      (exact (ih (normalize-round w) (And.left p) (And.right p) hm2)))))

(a/theorem normalize-fuel-length [w :- World] (= (List.length (normalize-fuel w)) (+ (normalize-measure w) 1))
  (simp only [normalize-fuel normalize-measure List.length list-length-append scan-length-eq]))

;; Theorem (P2): on a world with unique ids where no activation belongs to a done run,
;; normalization ends normalized (the loop's flag always holds)
(a/theorem normalized-ok [w :- World]
  (=> (= (well-formed w) true) (= (acts-alive w) true) (= (normalized (normalize w)) true))
  (intros h ha)
  (have hd := (well-formed-detach w h))
  (have b := (round-bound-detach (alive-cnt w) (act-cnt w) w (round-bound-intro _ _ w h ha (Nat.le_refl _) (Nat.le_refl _))))
  (have p := (round-bound-parts _ _ _ b))
  (have hm (< (normalize-measure (detach w)) (List.length (normalize-fuel (detach w)))))
  (rw [normalize-fuel-length]) (omega)
  (simp only [normalize])
  (exact (normalize-loop-ok (normalize-fuel (detach w)) (detach w) hd (And.left (And.right p)) hm)))

;; ---- through the Rule R rounds

(a/theorem acts-alive-normalize-loop [fuel :- (List Nat)]
  (forall [w :- World] (=> (= (well-formed w) true) (= (acts-alive w) true) (= (acts-alive (normalize-loop fuel w)) true)))
  (induction fuel)
  (case [nil] (intros w h ha) (simp only [normalize-loop]) (exact ha))
  (case [cons x f ih]
    (intros w h ha)
    (cases hn (normalized w))
    (case [true] (simp only [normalize-loop hn]) (exact ha))
    (case [false]
      (have p := (round-bound-round w h ha))
      (simp only [normalize-loop hn])
      (exact (ih (normalize-round w) (And.left p) (And.right p))))))

(a/theorem acts-alive-normalize [w :- World]
  (=> (= (well-formed w) true) (= (acts-alive w) true) (= (acts-alive (normalize w)) true))
  (intros h ha)
  (have p := (round-bound-parts _ _ _ (round-bound-detach (alive-cnt w) (act-cnt w) w (round-bound-intro _ _ w h ha (Nat.le_refl _) (Nat.le_refl _)))))
  (simp only [normalize])
  (exact (acts-alive-normalize-loop _ (detach w) (well-formed-detach w h) (And.left (And.right p)))))

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
  (=> (= (well-formed w) true) (= (acts-alive w) true) (= (acts-alive (rule-r-round w)) true))
  (intros h ha)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (acts-alive-filter _ _ (acts-alive-normalize w h ha))))

(a/theorem last-input-loop-ok [fuel :- (List Nat)]
  (forall [w0 :- World]
    (=> (= (well-formed w0) true) (= (acts-alive w0) true) (= (rounds-safe-loop fuel w0) true)
        (And (= (well-formed (last-input-loop fuel w0)) true) (= (acts-alive (last-input-loop fuel w0)) true))))
  (induction fuel)
  (case [nil] (intros w0 h ha hs) (simp only [last-input-loop]) (exact (And.intro h ha)))
  (case [cons x f ih]
    (intros w0 h ha hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (cases ho (no-orphans (rule-r-round w0)))
    (case [true] (simp only [last-input-loop ho]) (exact (And.intro h ha)))
    (case [false]
      (simp only [ho] at hs)
      (simp only [last-input-loop ho])
      (exact (ih (rule-r-round w0) (well-formed-rule-r-round w0 h (And.left hs)) (acts-alive-round w0 h ha) (And.right hs))))))

;; P2 for Rule R: with filter-safe in every round, the last round's normalization is normalized
(a/theorem rule-r-normalized-ok [w :- World]
  (=> (= (well-formed w) true) (= (acts-alive w) true) (= (rule-r-safe w) true)
      (= (normalized (normalize (rule-r-last-input w))) true))
  (intros h ha hs)
  (simp only [rule-r-safe] at hs)
  (have p := (last-input-loop-ok (rule-r-fuel w) w h ha hs))
  (simp only [rule-r-last-input])
  (exact (normalized-ok _ (And.left p) (And.right p))))

;; ===========================================================================
;; Part F. The step
;; ===========================================================================

;; the step's world is normalized: no normalized hypothesis, only acts-alive of the raw world
;; (and rule-r-safe, as step-well-formed)
(a/theorem step-normalized-ok [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) true) (= (well-formed w) true) (= (acts-alive (:world (raw w it))) true)
      (= (rule-r-safe (:world (raw w it))) true)
      (= (normalized (:world (world-step w it))) true))
  (intros ha h haa hs)
  (exact (step-normalized-total w it ha (rule-r-normalized-ok _ (well-formed-raw w it h) haa hs))))

(a/theorem step-i4-ok [w :- World, it :- Item, r :- RunRow]
  (=> (= (:accepted (raw w it)) true) (= (well-formed w) true) (= (acts-alive (:world (raw w it))) true)
      (= (rule-r-safe (:world (raw w it))) true)
      (List.Mem r (:runs (:world (world-step w it)))) (= (run-alive r) true)
      (= (in-live (:world (world-step w it)) (:id r)) true))
  (intros ha h haa hs hm hr)
  (exact (normalized-runs _ r (step-normalized-ok w it ha h haa hs) hm hr)))
