(ns spindel.v2.react
  "Obligations P8 and P6. P8: the reactivation worklist (§3.4 step 3, `react-loop` in spindel.v2.engine) empties within
  its fuel `react-fuel` (2 + the number of validity entries), kernel-checked (Init only).

  `react-run8` is `react-loop` with the leftover queue (`react-run8-world`: same world); `react-done w d`
  says the queue emptied. Potential |queue| + vm w, vm = the validity entries of the idle computations: a
  pop of an absent or awake id lowers |queue|; a pop of an idle computation c reactivates it (awake, no
  validity: `comp-react-row`) and queues one id per validity entry, while the edges and rank raises of the
  reactivation (`react-edges`, `raise-run`) keep every computation's (id, idle, #validity) key
  (`ck-react-edges`), so vm drops by exactly #validity c (unique ids). The fuel starts above the potential
  (`vm-le-all`).

  P6: the §3.4 validation walk (`valid-loop`) never runs out of its fuel `valid-fuel` (2 + the number of
  validity entries). `valid-ex` follows the walk and says whether the fuel ran out; potential |entries| +
  the entries of the idle computations not yet expanded (`useen8`): a pop either drops an entry or expands
  an idle computation once (`seen`), which queues exactly the entries it removes from the potential
  (`useen-add`, unique ids). Before branch z57 the walk had no `seen` and followed every path of the
  validity DAG: it ran out of the fuel on reachable worlds (react_test `p6-validity-chain`).

  Theorems: react-done-ok   inv-sample w -> react-done w d = true
            valid-done-ok   inv-sample w -> comp-find w x = some c -> valid-done w c = true"
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.casc :refer :all]
            [spindel.v2.lit :refer :all]))

;; ---- the loop with its leftover queue
(a/defn react-run8 [fuel :- (List Nat), w :- World, q :- (List Nat)] FinRes
  (match fuel
    [nil (FinRes.mk w q)]
    [(cons h f) (match q
                  [nil (FinRes.mk w (List.nil Nat))]
                  [(cons x t) (match (comp-find w x)
                                [none (react-run8 f w t)]
                                [(some c) (if (:idle c)
                                              (react-run8 f (react-one w c) (List.append Nat t (valid-debtors (:validity c))))
                                              (react-run8 f w t))])])]))
(a/defn react-done [w :- World, d :- Nat] Bool
  (match (:rest (react-run8 (react-fuel w) w (List.cons Nat d (List.nil Nat)))) [nil true] [(cons h t) false]))

(a/theorem react-run8-world [fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)] (= (:world (react-run8 fuel w q)) (react-loop fuel w q)))
  (induction fuel)
  (case [nil] (intros w q) (simp only [react-run8 react-loop]))
  (case [cons h f ih]
    (intros w q)
    (cases q)
    (case [nil] (simp only [react-run8 react-loop]))
    (case [cons x t]
      (cases hc (comp-find w x))
      (case [none] (simp only [react-run8 react-loop hc]) (exact (ih w t)))
      (case [some c]
        (cases hi (:idle c))
        (case [false] (simp only [react-run8 react-loop hc hi]) (exact (ih w t)))
        (case [true] (simp only [react-run8 react-loop hc hi]) (exact (ih _ _)))))))

;; ---- computation keys: (id, idle, #validity)
(a/structure CK8 [] (id Nat) (idle Bool) (nv Nat))
(a/defn ck8 [c :- CompRow] CK8 (CK8.mk (:id c) (:idle c) (List.length Valid (:validity c))))
(a/defn ck8-id [k :- CK8] Nat (:id k))
(a/defn ck8s [cs :- (List CompRow)] (List CK8)
  (match cs [nil (List.nil CK8)] [(cons h t) (List.cons CK8 (ck8 h) (ck8s t))]))
(a/defn ck8-v [k :- CK8] Nat (if (:idle k) (:nv k) 0))
(a/defn ck8-sum [ks :- (List CK8)] Nat (match ks [nil 0] [(cons h t) (+ (ck8-v h) (ck8-sum t))]))
(a/defn vm8 [w :- World] Nat (ck8-sum (ck8s (:comps w))))

(a/theorem ck8s-upd [x :- Nat, f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (ck8 (f c)) (ck8 c))), cs :- (List CompRow)]
  (= (ck8s (tbl-upd comp-id x f cs)) (ck8s cs))
  (induction cs)
  (case [nil] (simp only [tbl-upd ck8s]))
  (case [cons h t ih] (cases hx (Nat.beq (comp-id h) x)) (all_goals (simp only [tbl-upd hx ck8s ih (hk h)]))))

;; the rank raise only sets ranks
(a/theorem ck8-raise-loop [fuel :- (List Nat)]
  (forall [d :- Nat, w :- World, todo :- (List RJ)] (= (ck8s (:comps (:world (raise-loop fuel d w todo)))) (ck8s (:comps w))))
  (induction fuel)
  (case [nil] (intros d w todo) (cases todo) (all_goals (simp only [raise-loop])))
  (case [cons u f ih]
    (intros d w todo)
    (cases todo)
    (case [nil] (simp only [raise-loop]))
    (case [cons j t]
      (cases hn (Nat.beq (:node j) d))
      (case [true] (simp only [raise-loop hn]))
      (case [false]
        (cases hb (Nat.ble (:need j) (comp-rank w (:node j))))
        (case [true] (simp only [raise-loop hn hb]) (exact (ih d w t)))
        (case [false]
          (simp only [raise-loop hn hb])
          (rw [(ih _ _ _)])
          (simp only [comp-upd set-comps (ck8s-upd (:node j) (comp-set-rank (:need j)) (fn [c :- CompRow] (Eq.refl (ck8 c))) (:comps w))]))))))
(a/theorem ck8-raise-run [w :- World, c :- Nat, d :- Nat] (= (ck8s (:comps (:world (raise-run w c d)))) (ck8s (:comps w)))
  (cases hc (comp-has w d))
  (case [false] (simp only [raise-run hc]))
  (case [true] (simp only [raise-run hc]) (exact (ck8-raise-loop _ d w _))))
(a/theorem ck8-iec [w :- World, e :- EdgeRow] (= (:comps (insert-edge-checked w e)) (:comps w))
  (cases hc (edge-ok-in w e)) (all_goals (simp only [insert-edge-checked hc insert-edge-fresh insert-edge edge-ins set-edges bump set-next-id])))
(a/theorem ck8-react-add [w :- World, c :- Nat, v :- Valid] (= (ck8s (:comps (react-add w c v))) (ck8s (:comps w)))
  (cases hk (react-ok w c v))
  (case [false] (simp only [react-add hk]))
  (case [true]
    (simp only [react-add hk])
    (rw [(ck8-raise-run (insert-edge-checked w (valid-edge w c v)) c (:debtor v))])
    (rw [(ck8-iec w (valid-edge w c v))])))
(a/theorem ck8-react-edges [vs :- (List Valid)]
  (forall [w :- World, c :- Nat] (= (ck8s (:comps (react-edges w c vs))) (ck8s (:comps w))))
  (induction vs)
  (case [nil] (intros w c) (simp only [react-edges]))
  (case [cons v t ih] (intros w c) (simp only [react-edges]) (exact (Eq.trans (ih _ c) (ck8-react-add w c v)))))

;; reactivating c (idle, unique id) removes exactly #validity c from the potential
(a/defn ck8-react [k :- CK8] CK8 (CK8.mk (:id k) false 0))
(a/theorem ck8-react-row [c :- CompRow] (= (ck8 (comp-react-row c)) (ck8-react (ck8 c))) (rfl))
(a/theorem ck8s-upd-g [x :- Nat, f :- (=> CompRow CompRow), g :- (=> CK8 CK8),
                       hc :- (forall [c :- CompRow] (= (ck8 (f c)) (g (ck8 c)))), cs :- (List CompRow)]
  (= (ck8s (tbl-upd comp-id x f cs)) (tbl-upd ck8-id x g (ck8s cs)))
  (induction cs)
  (case [nil] (simp only [tbl-upd ck8s]))
  (case [cons h t ih]
    (cases hx (Nat.beq (comp-id h) x))
    (case [false] (have hx2 (= (Nat.beq (ck8-id (ck8 h)) x) false)) (exact hx) (simp only [tbl-upd hx ck8s hx2 ih]))
    (case [true] (have hx2 (= (Nat.beq (ck8-id (ck8 h)) x) true)) (exact hx) (simp only [tbl-upd hx ck8s hx2 ih (hc h)]))))
(a/defn ck8-other [x :- Nat, k :- CK8] Bool (Bool.not (Nat.beq (:id k) x)))
(a/theorem ck8-sum-upd-out [x :- Nat, ks :- (List CK8)]
  (=> (= (tbl-all (ck8-other x) ks) true) (= (ck8-sum (tbl-upd ck8-id x ck8-react ks)) (ck8-sum ks)))
  (induction ks)
  (case [nil] (intro h) (simp only [tbl-upd]))
  (case [cons k t ih]
    (intro h)
    (simp only [tbl-all Bool.and_eq_true] at h)
    (have hx (= (Nat.beq (ck8-id k) x) false)) (have q := (And.left h)) (simp only [ck8-other] at q) (exact (bnot-true _ q))
    (simp only [tbl-upd hx ck8-sum (ih (And.right h))])))
;; the found row: its key is the only one with that id (unique ids), so the sum loses exactly its #validity
(a/theorem ck8-other-of [x :- Nat, cs :- (List CompRow)]
  (=> (= (nat-mem x (tbl-ids comp-id cs)) false) (= (tbl-all (ck8-other x) (ck8s cs)) true))
  (induction cs)
  (case [nil] (intro h) (simp only [ck8s tbl-all]))
  (case [cons h t ih]
    (intro hm)
    (cases hb (Nat.beq (comp-id h) x))
    (case [true] (simp [tbl-ids nat-mem hb] at hm))
    (case [false]
      (simp only [tbl-ids nat-mem hb] at hm)
      (have hb2 (= (Nat.beq (:id h) x) false)) (exact hb)
      (simp only [ck8s tbl-all ck8-other ck8 hb2 Bool.not_false (ih hm) Bool.and_self]))))
(a/theorem vm-react [x :- Nat, c :- CompRow, cs :- (List CompRow)]
  (=> (= (nat-nodup (tbl-ids comp-id cs)) true) (= (tbl-find comp-id x cs) (Option.some CompRow c)) (= (:idle c) true)
      (= (+ (ck8-sum (tbl-upd ck8-id x ck8-react (ck8s cs))) (List.length Valid (:validity c))) (ck8-sum (ck8s cs))))
  (induction cs)
  (case [nil] (intros hn hf hi) (simp only [tbl-find] at hf) (cases hf))
  (case [cons h t ih]
    (intros hn hf hi)
    (simp only [tbl-ids nat-nodup Bool.and_eq_true] at hn)
    (cases hx (Nat.beq (comp-id h) x))
    (case [true]
      (simp only [tbl-find hx] at hf)
      (have e := (Option.some.inj hf))
      (have hx2 (= (Nat.beq (ck8-id (ck8 h)) x) true)) (exact hx)
      (have ex (= (comp-id h) x)) (exact (Nat.eq_of_beq_eq_true hx))
      (have nm := (bnot-true _ (And.left hn)))
      (rw [ex] at nm)
      (have ho := (ck8-other-of x t nm))
      (rw [e] at hx2)
      (rw [e])
      (have hx3 (= (Nat.beq (ck8-id (ck8 c)) x) true)) (exact hx2)
      (simp only [ck8s tbl-upd hx3])
      (simp only [ck8-sum (ck8-sum-upd-out x (ck8s t) ho) ck8-v ck8-react ck8 hi ite_true ite_false])
      (omega))
    (case [false]
      (simp only [tbl-find hx] at hf)
      (have hx2 (= (Nat.beq (ck8-id (ck8 h)) x) false)) (exact hx)
      (have q := (ih (And.right hn) hf hi))
      (simp only [ck8s tbl-upd hx2 ck8-sum])
      (omega))))

(a/theorem nlen-app [a :- (List Nat), b :- (List Nat)] (= (List.length Nat (List.append Nat a b)) (+ (List.length Nat a) (List.length Nat b)))
  (induction a)
  (case [nil] (simp only [List.length List.append]) (omega))
  (case [cons h t ih]
    (change (= (+ (List.length Nat (List.append Nat t b)) 1) (+ (+ (List.length Nat t) 1) (List.length Nat b))))
    (rw [ih]) (omega)))
(a/theorem nlen-cons [x :- Nat, t :- (List Nat)] (= (List.length Nat (List.cons Nat x t)) (+ (List.length Nat t) 1)) (rfl))
(a/theorem nlen-nil [] (= (List.length Nat (List.nil Nat)) 0) (rfl))
(a/theorem vd-len [vs :- (List Valid)] (= (List.length Nat (valid-debtors vs)) (List.length Valid vs))
  (induction vs)
  (case [nil] (simp only [valid-debtors List.length]))
  (case [cons h t ih] (simp only [valid-debtors List.length ih])))
(a/theorem vm8-react-one [w :- World, x :- Nat, c :- CompRow]
  (=> (= (inv-sample w) true) (= (comp-find w x) (Option.some CompRow c)) (= (:idle c) true)
      (= (+ (vm8 (react-one w c)) (List.length Valid (:validity c))) (vm8 w)))
  (intros hs hf hi)
  (have i (= (:id c) x)) (exact (tbl-find-id CompRow comp-id x c (:comps w) hf))
  (have e1 := (ck8-react-edges (:validity c) (comp-upd w (:id c) comp-react-row) (:id c)))
  (have e2 (= (ck8s (:comps (comp-upd w (:id c) comp-react-row))) (tbl-upd ck8-id (:id c) ck8-react (ck8s (:comps w)))))
  (simp only [comp-upd set-comps (ck8s-upd-g (:id c) comp-react-row ck8-react ck8-react-row (:comps w))])
  (have e3 (= (vm8 (react-one w c)) (ck8-sum (tbl-upd ck8-id (:id c) ck8-react (ck8s (:comps w))))))
  (simp only [vm8 react-one]) (rw [e1, e2])
  (rw [e3, i])
  (exact (vm-react x c (:comps w) (comps-nodup w hs) hf hi)))

(a/theorem react-run8-done [fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)]
    (=> (= (inv-sample w) true) (< (+ (List.length Nat q) (vm8 w)) (List.length Nat fuel))
        (= (:rest (react-run8 fuel w q)) (List.nil Nat))))
  (induction fuel)
  (case [nil] (intros w q hs hl) (rw [nlen-nil] at hl) (omega))
  (case [cons u f ih]
    (intros w q hs hl)
    (cases q)
    (case [nil] (simp only [react-run8]))
    (case [cons x t]
      (rw [nlen-cons, nlen-cons] at hl)
      (cases hc (comp-find w x))
      (case [none] (simp only [react-run8 hc]) (apply (ih w t hs)) (omega))
      (case [some c]
        (cases hi (:idle c))
        (case [false] (simp only [react-run8 hc hi]) (apply (ih w t hs)) (omega))
        (case [true]
          (simp only [react-run8 hc hi])
          (apply (ih (react-one w c) _ (inv-react-one w c hs)))
          (have v := (vm8-react-one w x c hs hc hi))
          (rw [nlen-app, vd-len])
          (omega))))))

;; the fuel starts above the potential: vm8 <= the number of validity entries
(a/theorem vm-le-all [cs :- (List CompRow)]
  (<= (ck8-sum (ck8s cs)) (List.length Nat (tbl-gather (fn [c :- CompRow] true) (fn [c :- CompRow] (valid-debtors (:validity c))) cs)))
  (induction cs)
  (case [nil] (simp only [ck8s ck8-sum tbl-gather List.length]) (exact (Nat.le_refl 0)))
  (case [cons h t ih]
    (simp only [ck8s ck8-sum tbl-gather ite_true nlen-app vd-len ck8-v ck8])
    (cases hi (:idle h))
    (all_goals (simp only [hi ite_true ite_false]))
    (all_goals (omega))))

;; Theorem (P8): the reactivation worklist empties within react-fuel
(a/theorem react-done-ok [w :- World, d :- Nat] (=> (= (inv-sample w) true) (= (react-done w d) true))
  (intro hs)
  (have le := (vm-le-all (:comps w)))
  (have hl (< (+ (List.length Nat (List.cons Nat d (List.nil Nat))) (vm8 w)) (List.length Nat (react-fuel w))))
  (simp only [react-fuel nlen-cons nlen-nil vm8])
  (omega)
  (simp only [react-done (react-run8-done (react-fuel w) w (List.cons Nat d (List.nil Nat)) hs hl)]))

;; ===========================================================================
;; P6: the §3.4 validation walk ends within its fuel (each idle computation's entries expanded once)
;; ===========================================================================

;; `valid-ex` follows `valid-loop` and says whether it ran out of fuel
(a/defn valid-ex [fuel :- (List Nat), w :- World, seen :- (List Nat), vs :- (List Valid)] Bool
  (match fuel
    [nil true]
    [(cons h f) (match vs
                  [nil false]
                  [(cons v t) (match (comp-find w (:debtor v))
                                [none (if (Bool.or (source-has w (:debtor v)) (task-has w (:debtor v)))
                                          (if (Nat.beq (deb-version w (:debtor v)) (:version v)) (valid-ex f w seen t) false)
                                          false)]
                                [(some c) (if (comp-clean w c v)
                                              (if (Bool.and (:idle c) (Bool.not (reach-mem (:id c) seen)))
                                                  (valid-ex f w (List.cons Nat (:id c) seen) (List.append Valid (:validity c) t))
                                                  (valid-ex f w seen t))
                                              false)])])]))
(a/defn valid-done [w :- World, c :- CompRow] Bool
  (Bool.not (valid-ex (valid-fuel w) w (List.cons Nat (:id c) (List.nil Nat)) (:validity c))))

;; potential: |entries| + the entries of the idle computations not yet expanded
(a/defn ck8-u [seen :- (List Nat), k :- CK8] Nat (if (Bool.and (:idle k) (Bool.not (reach-mem (:id k) seen))) (:nv k) 0))
(a/defn useen8 [seen :- (List Nat), ks :- (List CK8)] Nat (match ks [nil 0] [(cons h t) (+ (ck8-u seen h) (useen8 seen t))]))
(a/theorem vlen-app [a :- (List Valid), b :- (List Valid)] (= (List.length Valid (List.append Valid a b)) (+ (List.length Valid a) (List.length Valid b)))
  (induction a)
  (case [nil] (simp only [List.length List.append]) (omega))
  (case [cons h t ih]
    (change (= (+ (List.length Valid (List.append Valid t b)) 1) (+ (+ (List.length Valid t) 1) (List.length Valid b))))
    (rw [ih]) (omega)))
(a/theorem vlen-cons [x :- Valid, t :- (List Valid)] (= (List.length Valid (List.cons Valid x t)) (+ (List.length Valid t) 1)) (rfl))

;; expanding x (idle, not seen, the only row with id x) lowers the potential by its entries
(a/theorem useen-out [x :- Nat, seen :- (List Nat), ks :- (List CK8)]
  (=> (= (tbl-all (ck8-other x) ks) true) (= (useen8 (List.cons Nat x seen) ks) (useen8 seen ks)))
  (induction ks)
  (case [nil] (intro h) (simp only [useen8]))
  (case [cons k t ih]
    (intro h)
    (simp only [tbl-all Bool.and_eq_true] at h)
    (have hx (= (Nat.beq (:id k) x) false)) (have q := (And.left h)) (simp only [ck8-other] at q) (exact (bnot-true _ q))
    (simp only [useen8 ck8-u reach-mem-cons hx Bool.false_or (ih (And.right h))])))
(a/theorem useen-add [x :- Nat, c :- CompRow, seen :- (List Nat), cs :- (List CompRow)]
  (=> (= (nat-nodup (tbl-ids comp-id cs)) true) (= (tbl-find comp-id x cs) (Option.some CompRow c)) (= (:idle c) true)
      (= (reach-mem x seen) false)
      (= (+ (useen8 (List.cons Nat x seen) (ck8s cs)) (List.length Valid (:validity c))) (useen8 seen (ck8s cs))))
  (induction cs)
  (case [nil] (intros hn hf hi hs) (simp only [tbl-find] at hf) (cases hf))
  (case [cons h t ih]
    (intros hn hf hi hs)
    (simp only [tbl-ids nat-nodup Bool.and_eq_true] at hn)
    (cases hx (Nat.beq (comp-id h) x))
    (case [true]
      (simp only [tbl-find hx] at hf)
      (have e := (Option.some.inj hf))
      (have ex (= (comp-id h) x)) (exact (Nat.eq_of_beq_eq_true hx))
      (have nm := (bnot-true _ (And.left hn)))
      (rw [ex] at nm)
      (have ho := (ck8-other-of x t nm))
      (have hx2 (= (Nat.beq (:id h) x) true)) (exact hx)
      (rw [e] at hx2)
      (rw [e])
      (have ec (= (:id c) x)) (exact (Nat.eq_of_beq_eq_true hx2))
      (simp only [ck8s useen8 (useen-out x seen (ck8s t) ho) ck8-u ck8 hi ec reach-mem-cons Nat.beq_refl hs Bool.true_or Bool.not_true Bool.not_false Bool.and_false Bool.and_true ite_true ite_false Bool.false_or])
      (omega))
    (case [false]
      (simp only [tbl-find hx] at hf)
      (have q := (ih (And.right hn) hf hi hs))
      (have hx2 (= (Nat.beq (:id h) x) false)) (exact hx)
      (simp only [ck8s useen8 ck8-u ck8 reach-mem-cons hx2 Bool.false_or])
      (omega))))

(a/theorem valid-ex-done [w :- World, fuel :- (List Nat)]
  (forall [seen :- (List Nat), vs :- (List Valid)]
    (=> (= (nat-nodup (tbl-ids comp-id (:comps w))) true)
        (< (+ (List.length Valid vs) (useen8 seen (ck8s (:comps w)))) (List.length Nat fuel))
        (= (valid-ex fuel w seen vs) false)))
  (induction fuel)
  (case [nil] (intros seen vs hn hl) (rw [nlen-nil] at hl) (omega))
  (case [cons u f ih]
    (intros seen vs hn hl)
    (rw [nlen-cons] at hl)
    (cases vs)
    (case [nil] (simp only [valid-ex]))
    (case [cons v t]
      (rw [vlen-cons] at hl)
      (cases hc (comp-find w (:debtor v)))
      (case [none]
        (cases hs (Bool.or (source-has w (:debtor v)) (task-has w (:debtor v))))
        (case [false] (simp only [valid-ex hc hs]))
        (case [true]
          (cases hv (Nat.beq (deb-version w (:debtor v)) (:version v)))
          (case [false] (simp only [valid-ex hc hs hv]))
          (case [true] (simp only [valid-ex hc hs hv]) (apply (ih seen t hn)) (omega))))
      (case [some c]
        (cases hk (comp-clean w c v))
        (case [false] (simp only [valid-ex hc hk]))
        (case [true]
          (cases he (Bool.and (:idle c) (Bool.not (reach-mem (:id c) seen))))
          (case [false] (simp only [valid-ex hc hk he]) (apply (ih seen t hn)) (omega))
          (case [true]
            (simp only [valid-ex hc hk he])
            (simp only [Bool.and_eq_true] at he)
            (have i (= (:id c) (:debtor v))) (exact (tbl-find-id CompRow comp-id (:debtor v) c (:comps w) hc))
            (have hc2 (= (tbl-find comp-id (:id c) (:comps w)) (Option.some CompRow c))) (rw [i]) (exact hc)
            (have q := (useen-add (:id c) c seen (:comps w) hn hc2 (And.left he) (bnot-true _ (And.right he))))
            (apply (ih (List.cons Nat (:id c) seen) (List.append Valid (:validity c) t) hn))
            (rw [vlen-app])
            (omega)))))))

;; the fuel starts above the potential: a row's own entries plus the others' are all entries
(a/theorem vz-len [vs :- (List Valid)] (= (List.length Nat (valid-zeros vs)) (List.length Valid vs))
  (induction vs)
  (case [nil] (simp only [valid-zeros List.length]))
  (case [cons h t ih] (simp only [valid-zeros List.length ih])))
(a/theorem useen-le [seen :- (List Nat), cs :- (List CompRow)]
  (<= (useen8 seen (ck8s cs)) (List.length Nat (all-valid-zeros cs)))
  (induction cs)
  (case [nil] (simp only [ck8s useen8 all-valid-zeros nlen-nil]) (exact (Nat.le_refl 0)))
  (case [cons h t ih]
    (simp only [ck8s useen8 all-valid-zeros nlen-app vz-len ck8-u ck8])
    (cases hi (Bool.and (:idle h) (Bool.not (reach-mem (:id h) seen))))
    (all_goals (simp only [hi ite_true ite_false]))
    (all_goals (omega))))
(a/theorem init-bound [x :- Nat, c :- CompRow, cs :- (List CompRow)]
  (=> (= (nat-nodup (tbl-ids comp-id cs)) true) (= (tbl-find comp-id x cs) (Option.some CompRow c))
      (<= (+ (useen8 (List.cons Nat x (List.nil Nat)) (ck8s cs)) (List.length Valid (:validity c))) (List.length Nat (all-valid-zeros cs))))
  (induction cs)
  (case [nil] (intros hn hf) (simp only [tbl-find] at hf) (cases hf))
  (case [cons h t ih]
    (intros hn hf)
    (simp only [tbl-ids nat-nodup Bool.and_eq_true] at hn)
    (cases hx (Nat.beq (comp-id h) x))
    (case [true]
      (simp only [tbl-find hx] at hf)
      (have e := (Option.some.inj hf))
      (have hx2 (= (Nat.beq (:id h) x) true)) (exact hx)
      (have le := (useen-le (List.cons Nat x (List.nil Nat)) t))
      (rw [e] at hx2)
      (rw [e])
      (simp only [ck8s useen8 all-valid-zeros nlen-app vz-len ck8-u ck8 reach-mem-cons hx2 Bool.true_or Bool.not_true Bool.and_false ite_false])
      (omega))
    (case [false]
      (simp only [tbl-find hx] at hf)
      (have q := (ih (And.right hn) hf))
      (simp only [ck8s useen8 all-valid-zeros nlen-app vz-len ck8-u ck8])
      (cases hi (Bool.and (:idle h) (Bool.not (reach-mem (:id h) (List.cons Nat x (List.nil Nat))))))
      (all_goals (simp only [hi ite_true ite_false]))
      (all_goals (omega)))))

;; Theorem (P6): validation of a computation of the world never runs out of fuel
(a/theorem valid-done-ok [w :- World, x :- Nat, c :- CompRow]
  (=> (= (inv-sample w) true) (= (comp-find w x) (Option.some CompRow c)) (= (valid-done w c) true))
  (intros hs hf)
  (have hn := (comps-nodup w hs))
  (have i (= (:id c) x)) (exact (tbl-find-id CompRow comp-id x c (:comps w) hf))
  (have b := (init-bound x c (:comps w) hn hf))
  (have hl (< (+ (List.length Valid (:validity c)) (useen8 (List.cons Nat (:id c) (List.nil Nat)) (ck8s (:comps w)))) (List.length Nat (valid-fuel w))))
  (rw [i]) (simp only [valid-fuel nlen-cons]) (omega)
  (simp only [valid-done (valid-ex-done w (valid-fuel w) _ _ hn hl) Bool.not_false]))
