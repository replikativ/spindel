(ns spindel.v2.z59
  "Z#59 (§4.5.1, T11, L5) as theorems, kernel-checked (Init only).

  Z#59 settles the former h-mark counterexample (l5_test `h-mark-fired-sibling-resolved`):
    (b) T11's entry E is the earliest fired dep edge of C in CREATION order (the least id: one
        allocator, an edge keeps its id) and every dep edge of C created after E is cut, the
        siblings at E's own site included; E is consumed (re-armed, or removed on a final debtor).
        `z59-t11-no-fired`: after the cut and the consumption of E, C has NO fired dep edge left:
        every fired one was created after E (E is the least) and is cut, E itself is armed or gone.
        So no fired edge outlives a re-entry, and a later write can no longer reach C through a
        leftover fired edge.
    (a) a write marks only from the computations whose dep edge on the written source fires, i.e.
        was armed (`armed-creditors`): a fired edge starts no marking (`z59-fired-starts-none`).
  The full step invariants h-mark / h-mem2 (and so L5 without hypotheses) are open: see
  notes/PLAN.md, branch z59, for the plan and the auxiliary facts it needs (tripwired in l5_test)."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]))

;; ===========================================================================
;; Part A. T11 (Z#59 b): no fired dep edge survives a re-entry
;; ===========================================================================

(a/defn z59-nf [c :- Nat, e :- EdgeRow] Bool (Bool.not (fired-dep-of c e)))
(a/defn z59-ge [i :- Nat, q :- EdgeRow] Bool (Nat.ble i (:id q)))
(a/defn z59-ble-opt [i :- Nat, o :- (Option EdgeRow)] Bool
  (match o [none true] [(some b) (Nat.ble i (:id b))]))

;; Nat comparisons
(a/theorem z59-blt-false [a :- Nat, b :- Nat] (=> (= (Nat.blt a b) false) (<= b a))
  (intro h) (have q := (Nat.lt_or_ge a b)) (cases q)
  (case [inl z] (have z2 (= (Nat.blt a b) true)) (simp only [Nat.blt_eq]) (exact z) (rw [h] at z2) (simp at z2))
  (case [inr z] (exact z)))
(a/theorem z59-blt-true [a :- Nat, b :- Nat] (=> (= (Nat.blt a b) true) (< a b))
  (intro h) (simp only [Nat.blt_eq] at h) (exact h))
(a/theorem z59-ble-of [a :- Nat, b :- Nat] (=> (<= a b) (= (Nat.ble a b) true))
  (intro h) (simp only [Nat.ble_eq]) (exact h))
(a/theorem z59-le-of-ble [a :- Nat, b :- Nat] (=> (= (Nat.ble a b) true) (<= a b))
  (intro h) (simp only [Nat.ble_eq] at h) (exact h))
(a/theorem z59-ble-self [e :- EdgeRow] (= (z59-ble-opt (:id e) (Option.some EdgeRow e)) true)
  (simp only [z59-ble-opt Nat.ble_eq Nat.le_refl]))

;; `earliest` returns the least id: below its start value and below every row it scans
(a/theorem z59-earliest-min [es :- (List EdgeRow)]
  (forall [best :- (Option EdgeRow), e :- EdgeRow]
    (=> (= (earliest best es) (Option.some EdgeRow e))
        (And (= (z59-ble-opt (:id e) best) true) (= (tbl-all (z59-ge (:id e)) es) true))))
  (induction es)
  (case [nil]
    (intros best e h)
    (simp only [earliest] at h)
    (rw [h])
    (exact (And.intro (z59-ble-self e) (rfl))))
  (case [cons hd t ih]
    (intros best e h)
    (simp only [earliest] at h)
    (have r := (ih _ e h))
    (have r1 := (And.left r))
    (have r2 := (And.right r))
    (cases best)
    (case [none]
      (simp only [z59-ble-opt] at r1)
      (have g2 (= (tbl-all (z59-ge (:id e)) (List.cons EdgeRow hd t)) true)) (simp only [tbl-all z59-ge r1 r2 Bool.and_self])
      (exact (And.intro (rfl) g2)))
    (case [some b]
      (cases hb (Nat.blt (:id hd) (:id b)))
      (case [true]
        (simp only [hb z59-ble-opt] at r1)
        (have l0 := (z59-le-of-ble _ _ r1))
        (have l1 := (z59-blt-true _ _ hb))
        (have l2 (<= (:id e) (:id b))) (omega)
        (have g1 (= (z59-ble-opt (:id e) (Option.some EdgeRow b)) true)) (exact (z59-ble-of _ _ l2))
        (have g2 (= (tbl-all (z59-ge (:id e)) (List.cons EdgeRow hd t)) true)) (simp only [tbl-all z59-ge r1 r2 Bool.and_self])
        (exact (And.intro g1 g2)))
      (case [false]
        (simp only [hb z59-ble-opt] at r1)
        (have l0 := (z59-le-of-ble _ _ r1))
        (have l1 := (z59-blt-false _ _ hb))
        (have l2 (<= (:id e) (:id hd))) (omega)
        (have g1 (= (z59-ble-opt (:id e) (Option.some EdgeRow b)) true)) (exact r1)
        (have g3 (= (Nat.ble (:id e) (:id hd)) true)) (exact (z59-ble-of _ _ l2))
        (have g2 (= (tbl-all (z59-ge (:id e)) (List.cons EdgeRow hd t)) true)) (simp only [tbl-all z59-ge g3 r2 Bool.and_self])
        (exact (And.intro g1 g2))))))

(a/defn z59-or-not [q :- (=> EdgeRow Bool), P :- (=> EdgeRow Bool), r :- EdgeRow] Bool
  (Bool.or (Bool.not (q r)) (P r)))

(a/theorem z59-all-of-filter [P :- (=> EdgeRow Bool), q :- (=> EdgeRow Bool), xs :- (List EdgeRow)]
  (=> (= (tbl-all P (tbl-filter q xs)) true) (= (tbl-all (z59-or-not q P) xs) true))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (cases hq (q hd))
    (case [false]
      (simp only [tbl-filter hq] at h)
      (simp only [tbl-all z59-or-not hq Bool.not_false Bool.true_or (ih h) Bool.and_self]))
    (case [true]
      (simp only [tbl-filter hq tbl-all Bool.and_eq_true] at h)
      (simp only [tbl-all z59-or-not hq Bool.not_true Bool.false_or (And.left h) (ih (And.right h)) Bool.and_self]))))

(a/theorem z59-all-filter-imp [P :- (=> EdgeRow Bool), Q :- (=> EdgeRow Bool), q :- (=> EdgeRow Bool),
                               h :- (forall [x :- EdgeRow] (=> (= (P x) true) (= (q x) true) (= (Q x) true))), xs :- (List EdgeRow)]
  (=> (= (tbl-all P xs) true) (= (tbl-all Q (tbl-filter q xs)) true))
  (induction xs)
  (case [nil] (intro hp) (simp only [tbl-filter tbl-all]))
  (case [cons hd t ih]
    (intro hp)
    (simp only [tbl-all Bool.and_eq_true] at hp)
    (cases hq (q hd))
    (case [false] (simp only [tbl-filter hq]) (exact (ih (And.right hp))))
    (case [true] (simp only [tbl-filter hq tbl-all (h hd (And.left hp) hq) (ih (And.right hp)) Bool.and_self]))))

;; every fired dep edge of c has an id >= E's
(a/theorem z59-entry-least [w :- World, c :- Nat, e :- EdgeRow]
  (=> (= (entry-edge w c) (Option.some EdgeRow e))
      (= (tbl-all (z59-or-not (fired-dep-of c) (z59-ge (:id e))) (:edges w)) true))
  (intro h)
  (simp only [entry-edge] at h)
  (exact (z59-all-of-filter (z59-ge (:id e)) (fired-dep-of c) (:edges w) (And.right (z59-earliest-min _ (Option.none EdgeRow) e h)))))

;; after the cut, a fired dep edge of c is E's id
(a/defn z59-p1 [c :- Nat, i :- Nat, r :- EdgeRow] Bool (Bool.or (z59-nf c r) (Nat.beq (:id r) i)))

(a/theorem z59-cut-p1 [c :- Nat, i :- Nat, r :- EdgeRow]
  (=> (= (z59-or-not (fired-dep-of c) (z59-ge i) r) true) (= (keep-prefix c true i r) true) (= (z59-p1 c i r) true))
  (intros h hk)
  (cases hf (fired-dep-of c r))
  (case [false] (simp only [z59-p1 z59-nf hf Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [z59-or-not hf Bool.not_true Bool.false_or z59-ge] at h)
    (have hd := hf)
    (simp only [fired-dep-of Bool.and_eq_true] at hd)
    (have l0 := (z59-le-of-ble _ _ h))
    (cases hlt (Nat.blt i (:id r)))
    (case [true] (simp only [keep-prefix suffix-edge after-cut (And.left hd) hlt] at hk) (simp at hk))
    (case' [false])
    (have l1 := (z59-blt-false _ _ hlt))
    (have eq (= (:id r) i)) (omega)
    (simp only [z59-p1 eq Nat.beq_refl Bool.or_true])))

(a/theorem z59-cut-edges [w :- World, c :- Nat, k :- Nat, i :- Nat]
  (= (:edges (cut-suffix w c true k i)) (tbl-filter (keep-prefix c true i) (:edges w)))
  (simp only [cut-suffix drop-edges comp-upd set-comps set-edges]))

(a/theorem z59-armed-nf [c :- Nat, r :- EdgeRow] (=> (= (:phase r) ph-armed) (= (z59-nf c r) true))
  (intro h) (have hb (= (Nat.beq ph-armed ph-fired) false)) (rfl)
  (simp only [z59-nf fired-dep-of h hb Bool.and_false Bool.not_false]))

;; no row with E's id: p1 is nf
(a/theorem z59-p1-nf [c :- Nat, i :- Nat, es :- (List EdgeRow)]
  (=> (= (tbl-find edge-id i es) (Option.none EdgeRow)) (= (tbl-all (z59-p1 c i) es) true) (= (tbl-all (z59-nf c) es) true))
  (induction es)
  (case [nil] (intros h1 h2) (simp only [tbl-all]))
  (case [cons hd t ih]
    (intros h1 h2)
    (cases hx (Nat.beq (edge-id hd) i))
    (case [true] (simp only [tbl-find hx] at h1) (cases h1))
    (case [false]
      (simp only [tbl-find hx] at h1)
      (simp only [tbl-all Bool.and_eq_true] at h2)
      (have a1 := (And.left h2))
      (simp only [edge-id] at hx)
      (simp only [z59-p1 hx Bool.or_false] at a1)
      (simp only [tbl-all a1 (ih h1 (And.right h2)) Bool.and_self]))))

;; Z#59 (b): after T11's cut and the consumption of E, the computation has no fired dep edge
(a/theorem z59-t11-no-fired [w :- World, c :- Nat, k :- Nat, e :- EdgeRow]
  (=> (= (entry-edge w c) (Option.some EdgeRow e))
      (= (tbl-all (z59-nf c) (:edges (consume-entry (cut-suffix w c true k (:id e)) e))) true))
  (intro h)
  (have h0 := (z59-entry-least w c e h))
  (have h1 (= (tbl-all (z59-p1 c (:id e)) (:edges (cut-suffix w c true k (:id e)))) true))
  (rw [(z59-cut-edges w c k (:id e))])
  (exact (z59-all-filter-imp _ _ _ (z59-cut-p1 c (:id e)) (:edges w) h0))
  (have hout (forall [r :- EdgeRow] (=> (= (z59-p1 c (:id e) r) true) (= (Nat.beq (edge-id r) (:id e)) false) (= (z59-nf c r) true))))
  (intros r p q)
  (simp only [edge-id] at q)
  (simp only [z59-p1 q Bool.or_false] at p)
  (exact p)
  (cases hf (deb-final (cut-suffix w c true k (:id e)) (:debtor e)))
  (case [true]
    (cases he (edge-find (cut-suffix w c true k (:id e)) (:id e)))
    (case [none] (simp only [consume-entry hf remove-edge he]) (exact (z59-p1-nf c (:id e) _ he h1)))
    (case [some e2]
      (cases hm (:marked e2))
      (case [false] (simp only [consume-entry hf remove-edge he hm edge-del])
        (exact (tbl-all-del EdgeRow edge-id (:id e) _ _ hout _ h1)))
      (case [true] (simp only [consume-entry hf remove-edge he hm edge-del])
        (exact (tbl-all-del EdgeRow edge-id (:id e) _ _ hout _ h1)))))
  (case [false]
    (have hin (forall [f :- (=> EdgeRow EdgeRow)]
                (=> (forall [r :- EdgeRow] (= (:phase (f r)) ph-armed))
                    (forall [r :- EdgeRow] (=> (= (z59-p1 c (:id e) r) true) (= (Nat.beq (edge-id r) (:id e)) true) (= (z59-nf c (f r)) true))))))
    (intros f hfa r p q) (exact (z59-armed-nf c (f r) (hfa r)))
    (cases hr (Nat.beq (:cont e) cont-restart))
    (case [true]
      (simp only [consume-entry hf hr edge-upd])
      (exact (tbl-all-upd EdgeRow edge-id (:id e) _ _ _ (hin (edge-set-phase ph-armed) (fn [r :- EdgeRow] (Eq.refl ph-armed))) hout _ h1)))
    (case [false]
      (simp only [consume-entry hf hr edge-upd])
      (exact (tbl-all-upd EdgeRow edge-id (:id e) _ _ _
               (hin (edge-rearm (deb-value (cut-suffix w c true k (:id e)) (:debtor e)) (deb-version (cut-suffix w c true k (:id e)) (:debtor e)))
                    (fn [r :- EdgeRow] (Eq.refl ph-armed)))
               hout _ h1)))))

;; ===========================================================================
;; Part B. T2 (Z#59 a): a fired edge on the written source starts no marking
;; ===========================================================================

;; the creditor of a non-armed dep edge on x is a root of the write's marking only through another,
;; armed, dep edge on x
(a/theorem z59-armed-creditors-mem [es :- (List EdgeRow), x :- Nat, y :- Nat]
  (=> (= (reach-mem y (armed-creditors es x)) true)
      (= (tbl-any (fn [e :- EdgeRow] (Bool.and (Bool.and (Nat.beq (:debtor e) x) (Nat.beq (:kind e) ek-dep))
                                               (Bool.and (Nat.beq (:phase e) ph-armed) (Nat.beq (:creditor e) y)))) es) true))
  (induction es)
  (case [nil] (intro h) (simp [armed-creditors reach-mem] at h))
  (case [cons hd t ih]
    (intro h)
    (cases ha (Bool.and (Bool.and (Nat.beq (:debtor hd) x) (Nat.beq (:kind hd) ek-dep)) (Nat.beq (:phase hd) ph-armed)))
    (case [false]
      (simp only [armed-creditors ha] at h)
      (simp only [tbl-any (ih h) Bool.or_true]))
    (case [true]
      (simp only [armed-creditors ha reach-mem] at h)
      (cases hy (Nat.beq y (:creditor hd)))
      (case [false] (simp only [hy] at h) (simp only [tbl-any (ih h) Bool.or_true]))
      (case [true]
        (simp only [Bool.and_eq_true] at ha)
        (have hy2 := (Nat.eq_of_beq_eq_true hy))
        (have hc (= (Nat.beq (:creditor hd) y) true)) (rw [hy2]) (exact (Nat.beq_refl _))
        (simp only [tbl-any (And.left (And.left ha)) (And.right (And.left ha)) (And.right ha) hc Bool.and_self Bool.true_or])))))

(a/defn z59-armed-on [x :- Nat, y :- Nat, e :- EdgeRow] Bool
  (Bool.and (Bool.and (Nat.beq (:debtor e) x) (Nat.beq (:kind e) ek-dep))
            (Bool.and (Nat.beq (:phase e) ph-armed) (Nat.beq (:creditor e) y))))

;; Z#59 (a): a computation none of whose dep edges on x is armed is no root of the write's marking
(a/theorem z59-fired-starts-none [w :- World, x :- Nat, y :- Nat]
  (=> (= (tbl-any (z59-armed-on x y) (:edges w)) false)
      (= (reach-mem y (armed-creditors (:edges w) x)) false))
  (intro h)
  (cases hr (reach-mem y (armed-creditors (:edges w) x)))
  (case [false] (rfl))
  (case [true]
    (have q := (z59-armed-creditors-mem (:edges w) x y hr))
    (have q2 (= (tbl-any (z59-armed-on x y) (:edges w)) true)) (exact q)
    (rw [h] at q2) (simp at q2)))
