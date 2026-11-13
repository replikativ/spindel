(ns spindel.v2.rank
  "I12 (A#6) ranks, kernel-checked (Init only): the height adjustment of spindel.v2.engine
  (`raise-loop`) establishes `ranks-ok` (rank(creditor) > rank(debtor) on every dep edge between
  computations) whenever it reports `ok`.

  The worklist invariant `raise-inv w todo`: every edge is rank-ok, or a pending job (n, k) for
  its creditor n has k > rank(debtor) (`covers`). It holds initially for a ranks-ok world plus
  a new edge c -> d with the job (c, rank d + 1) (`raise-inv-start`), every pop keeps it
  (`raise-inv-skip`, `raise-inv-raise`), and an empty worklist is ranks-ok (`raise-inv-done`).
  Hence:
    raise-loop-ranks    raise-inv w todo, (:ok (raise-loop fuel d w todo)) -> ranks-ok of its world
    raise-run-ranks     ranks-ok w, e = c -> d is the only edge of w' = w + e not checked,
                        (:ok (raise-run w' c d)) -> ranks-ok (:world (raise-run w' c d))
  T6 inserts a dep edge on a computation and then raises (`await-new-dep`), and refuses when
  the raise is not ok (::cycle); a reactivation edge is kept only when its raise is ok
  (`react-add`). So these are exactly the steps that add rank constraints."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]))

;; ---------------------------------------------------------------------------
;; Generic list lemmas

(a/theorem tbl-all-mem-mono [A :- Type, P :- (=> A Bool), Q :- (=> A Bool), xs :- (List A)]
  (=> (forall [x :- A] (=> (List.Mem x xs) (= (P x) true) (= (Q x) true)))
      (= (tbl-all P xs) true) (= (tbl-all Q xs) true))
  (induction xs)
  (case [nil] (intros hpq hp) (simp [tbl-all]))
  (case [cons h t ih]
    (intros hpq hp)
    (simp only [tbl-all Bool.and_eq_true] at hp)
    (simp only [tbl-all Bool.and_eq_true])
    (apply And.intro)
    (exact (hpq h (List.Mem.head t) (And.left hp)))
    (apply (ih _ (And.right hp)))
    (intros x hx hpx)
    (exact (hpq x (List.Mem.tail h hx) hpx))))

(a/theorem tbl-any-app [A :- Type, p :- (=> A Bool), xs :- (List A), ys :- (List A)]
  (= (tbl-any p (List.append A xs ys)) (Bool.or (tbl-any p xs) (tbl-any p ys)))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [tbl-any List.append])
  (simp only [List.append tbl-any]) (rw [ih]) (rw [Bool.or_assoc]))

(a/theorem tbl-any-mono [A :- Type, p :- (=> A Bool), q :- (=> A Bool),
                         hpq :- (forall [x :- A] (=> (= (p x) true) (= (q x) true))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-any q xs) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro hp)
    (simp only [tbl-any Bool.or_eq_true] at hp)
    (simp only [tbl-any Bool.or_eq_true])
    (cases hp)
    (case [inl h1] (exact (Or.inl (hpq h h1))))
    (case [inr h1] (exact (Or.inr (ih h1))))))

;; ---------------------------------------------------------------------------
;; comp-rank and comp-has under a rank update

(a/theorem tbl-find-upd-ne [A :- Type, idf :- (=> A Nat), x :- Nat, y :- Nat, f :- (=> A A),
                            hf :- (forall [r :- A] (= (idf (f r)) (idf r))), xs :- (List A)]
  (=> (= (Nat.beq y x) false) (= (tbl-find idf y (tbl-upd idf x f xs)) (tbl-find idf y xs)))
  (intro hne)
  (induction xs)
  (case [nil] (simp [tbl-find tbl-upd]))
  (case [cons h t ih]
    (cases hx (Nat.beq (idf h) x))
    (case [false] (simp only [tbl-upd hx tbl-find ih]))
    (case [true]
      (have hxe (= (idf h) x)) (exact (Nat.eq_of_beq_eq_true hx))
      (have hy (= (Nat.beq (idf h) y) false)) (rw [hxe]) (rw [beq-comm]) (exact hne)
      (have hy2 (= (Nat.beq (idf (f h)) y) false)) (rw [hf]) (exact hy)
      (simp only [tbl-upd hx tbl-find hy hy2 ih]))))

(a/theorem comp-rank-set-ne [w :- World, n :- Nat, k :- Nat, y :- Nat]
  (=> (= (Nat.beq y n) false) (= (comp-rank (comp-upd w n (comp-set-rank k)) y) (comp-rank w y)))
  (intro hne)
  (simp only [comp-rank comp-find comp-upd set-comps]
    )
  (rw [(tbl-find-upd-ne CompRow comp-id n y (comp-set-rank k) (comp-set-rank-id k) (:comps w) hne)]))

(a/defn crank [cs :- (List CompRow), x :- Nat] Nat (match (tbl-find comp-id x cs) [none 0] [(some c) (:rank c)]))

(a/theorem crank-upd-eq [n :- Nat, k :- Nat, cs :- (List CompRow)]
  (=> (= (tbl-has comp-id n cs) true) (= (crank (tbl-upd comp-id n (comp-set-rank k) cs) n) k))
  (induction cs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hh) (simp [tbl-has] at hh)
  (intro hh)
  (cases hx (Nat.beq (comp-id h) n))
  (simp only [tbl-has hx] at hh)
  (simp only [crank tbl-upd hx tbl-find])
  (exact (ih hh))
  (have hx2 (= (Nat.beq (comp-id (comp-set-rank k h)) n) true)) (rw [comp-set-rank-id]) (exact hx)
  (simp only [crank tbl-upd hx tbl-find hx2]))

(a/theorem comp-rank-set-eq [w :- World, n :- Nat, k :- Nat]
  (=> (= (comp-has w n) true) (= (comp-rank (comp-upd w n (comp-set-rank k)) n) k))
  (intro h)
  (simp only [comp-has] at h)
  (exact (crank-upd-eq n k (:comps w) h)))

(a/theorem comp-has-set-rank [w :- World, n :- Nat, k :- Nat, y :- Nat]
  (= (comp-has (comp-upd w n (comp-set-rank k)) y) (comp-has w y))
  (simp only [comp-has comp-upd set-comps])
  (exact (tbl-has-upd CompRow comp-id n y (comp-set-rank k) (comp-set-rank-id k) (:comps w))))

;; ---------------------------------------------------------------------------
;; The worklist invariant

(a/defn covers [w :- World, e :- EdgeRow, j :- RJ] Bool
  (Bool.and (Nat.beq (:node j) (:creditor e)) (Nat.blt (comp-rank w (:debtor e)) (:need j))))
(a/defn pend-ok [w :- World, todo :- (List RJ), e :- EdgeRow] Bool
  (Bool.or (rank-edge-ok w e) (tbl-any (covers w e) todo)))
(a/defn raise-inv [w :- World, todo :- (List RJ)] Bool (tbl-all (pend-ok w todo) (:edges w)))

(a/theorem raise-inv-done [w :- World]
  (=> (= (raise-inv w (List.nil RJ)) true) (= (ranks-ok w) true))
  (intro h)
  (simp only [raise-inv] at h)
  (simp only [ranks-ok])
  (exact (tbl-all-mono EdgeRow (pend-ok w (List.nil RJ)) (rank-edge-ok w)
           (fn [e :- EdgeRow, he :- (= (pend-ok w (List.nil RJ) e) true)]
             (Eq.trans (Eq.symm (Bool.or_false (rank-edge-ok w e))) he))
           (:edges w) h)))

;; rank-edge-ok from the rank comparison
(a/theorem rank-edge-ok-of-lt [w :- World, e :- EdgeRow]
  (=> (= (Nat.blt (comp-rank w (:debtor e)) (comp-rank w (:creditor e))) true) (= (rank-edge-ok w e) true))
  (intro h) (simp [rank-edge-ok h]))

;; a skipped job (its node already ranks high enough): its covered edges are rank-ok
(a/theorem pend-skip [w :- World, j :- RJ, t :- (List RJ), e :- EdgeRow]
  (=> (= (Nat.ble (:need j) (comp-rank w (:node j))) true)
      (= (pend-ok w (List.cons RJ j t) e) true) (= (pend-ok w t e) true))
  (intros hs he)
  (simp only [pend-ok tbl-any Bool.or_eq_true] at he)
  (simp only [pend-ok Bool.or_eq_true])
  (rcases he (or h1 (or h2 h3)))
  (exact (Or.inl h1))
  (simp only [covers Bool.and_eq_true] at h2)
  (have hn (= (:node j) (:creditor e))) (exact (Nat.eq_of_beq_eq_true (And.left h2)))
  (have hl (= (Nat.blt (comp-rank w (:debtor e)) (comp-rank w (:creditor e))) true))
  (have h4 := (And.right h2))
  (rw [← hn])
  (simp only [Nat.blt_eq] at h4)
  (simp only [Nat.ble_eq] at hs)
  (simp only [Nat.blt_eq])
  (omega)
  (exact (Or.inl (rank-edge-ok-of-lt w e hl)))
  (exact (Or.inr h3)))

(a/theorem raise-inv-skip [w :- World, j :- RJ, t :- (List RJ)]
  (=> (= (Nat.ble (:need j) (comp-rank w (:node j))) true)
      (= (raise-inv w (List.cons RJ j t)) true) (= (raise-inv w t) true))
  (intros hs h)
  (simp only [raise-inv] at h)
  (simp only [raise-inv])
  (exact (tbl-all-mono EdgeRow (pend-ok w (List.cons RJ j t)) (pend-ok w t)
           (fn [e :- EdgeRow, he :- (= (pend-ok w (List.cons RJ j t) e) true)] (pend-skip w j t e hs he))
           (:edges w) h)))

;; ---- the raise step

(a/theorem dep-cred-mem [e :- EdgeRow, n :- Nat, es :- (List EdgeRow)]
  (=> (List.Mem e es) (= (Nat.beq (:kind e) ek-dep) true) (= (Nat.beq (:debtor e) n) true)
      (= (reach-mem (:creditor e) (dep-creditors es n)) true))
  (induction es)
  (case' [cons h t ih])
  (case' [nil])
  (intros hm hk hd) (cases hm)
  (intros hm hk hd)
  (cases hm)
  (simp [dep-creditors hk hd reach-mem])
  (rename_i hm2)
  (have h2 := (ih hm2 hk hd))
  (cases hc (Bool.and (Nat.beq (:debtor h) n) (Nat.beq (:kind h) ek-dep)))
  (simp only [dep-creditors hc]) (exact h2)
  (simp only [dep-creditors hc reach-mem-cons h2 Bool.or_true]))

(a/theorem rjobs-covers [w :- World, e :- EdgeRow, m :- Nat, ys :- (List Nat)]
  (=> (= (reach-mem (:creditor e) ys) true) (= (Nat.blt (comp-rank w (:debtor e)) m) true)
      (= (tbl-any (covers w e) (rjobs m ys)) true))
  (induction ys)
  (case' [cons y t ih])
  (case' [nil])
  (intros hm hb) (simp [reach-mem] at hm)
  (intros hm hb)
  (simp only [reach-mem-cons Bool.or_eq_true] at hm)
  (simp only [rjobs tbl-any Bool.or_eq_true covers Bool.and_eq_true])
  (cases hm)
  (rename_i h1)
  (exact (Or.inl (And.intro (Eq.trans (beq-comm y (:creditor e)) h1) hb)))
  (rename_i h1)
  (have h2 := (ih h1 hb))
  (exact (Or.inr h2)))

(a/theorem covers-transfer [w :- World, w2 :- World, e :- EdgeRow, t :- (List RJ)]
  (=> (= (comp-rank w2 (:debtor e)) (comp-rank w (:debtor e)))
      (= (tbl-any (covers w e) t) true) (= (tbl-any (covers w2 e) t) true))
  (intros hr h)
  (exact (tbl-any-mono RJ (covers w e) (covers w2 e)
           (fn [j :- RJ, hj :- (= (covers w e j) true)]
             (Eq.trans (congrArg (fn [r :- Nat] (Bool.and (Nat.beq (:node j) (:creditor e)) (Nat.blt r (:need j)))) hr) hj))
           t h)))

(a/theorem lt-of-ble-false [a :- Nat, b :- Nat] (=> (= (Nat.ble a b) false) (< b a))
  (intro h) (have h2 (Not (<= a b))) (intro hab) (have h3 := (Nat.ble_eq_true_of_le hab))
  (rw [h] at h3) (cases h3) (omega))

(a/defn raise-todo [w :- World, j :- RJ, t :- (List RJ)] (List RJ)
  (List.append RJ t (rjobs (+ (:need j) 1) (dep-creditors (:edges w) (:node j)))))

(a/theorem pend-raise [w :- World, j :- RJ, t :- (List RJ), e :- EdgeRow]
  (=> (= (Nat.ble (:need j) (comp-rank w (:node j))) false)
      (List.Mem e (:edges w))
      (= (pend-ok w (List.cons RJ j t) e) true)
      (= (pend-ok (comp-upd w (:node j) (comp-set-rank (:need j))) (raise-todo w j t) e) true))
  (intros hk hm he)
  (have hhas (forall [y :- Nat] (= (comp-has (comp-upd w (:node j) (comp-set-rank (:need j))) y) (comp-has w y))))
  (intro y) (exact (comp-has-set-rank w (:node j) (:need j) y))
  (cases hkd (Nat.beq (:kind e) ek-dep))
  (case [false] (simp [pend-ok rank-edge-ok hkd]))
  (case [true]
    (cases hhd (comp-has w (:debtor e)))
    (case [false] (simp [pend-ok rank-edge-ok hkd hhas hhd]))
    (case [true]
      (cases hhc (comp-has w (:creditor e)))
      (case [false] (simp [pend-ok rank-edge-ok hkd hhas hhd hhc]))
      (case [true]
        (have hk2 := (lt-of-ble-false _ _ hk))
        (cases hdn (Nat.beq (:debtor e) (:node j)))
        (case [true]
          ;; the debtor was raised: its creditor gets a job with need + 1
          (have hdeq (= (:debtor e) (:node j))) (exact (Nat.eq_of_beq_eq_true hdn))
          (have hhn (= (comp-has w (:node j)) true)) (rw [← hdeq]) (exact hhd)
          (have hr (= (comp-rank (comp-upd w (:node j) (comp-set-rank (:need j))) (:debtor e)) (:need j)))
          (rw [hdeq]) (exact (comp-rank-set-eq w (:node j) (:need j) hhn))
          (have hb (= (Nat.blt (comp-rank (comp-upd w (:node j) (comp-set-rank (:need j))) (:debtor e)) (+ (:need j) 1)) true))
          (rw [hr]) (simp only [Nat.blt_eq]) (omega)
          (have hc := (rjobs-covers (comp-upd w (:node j) (comp-set-rank (:need j))) e (+ (:need j) 1)
                        (dep-creditors (:edges w) (:node j)) (dep-cred-mem e (:node j) (:edges w) hm hkd hdn) hb))
          (simp only [pend-ok raise-todo tbl-any-app Bool.or_eq_true])
          (exact (Or.inr (Or.inr hc))))
        (case [false]
          (have hrd (= (comp-rank (comp-upd w (:node j) (comp-set-rank (:need j))) (:debtor e)) (comp-rank w (:debtor e))))
          (exact (comp-rank-set-ne w (:node j) (:need j) (:debtor e) hdn))
          (simp only [pend-ok tbl-any Bool.or_eq_true] at he)
          (cases hcn (Nat.beq (:creditor e) (:node j)))
          (case [true]
            ;; the creditor was raised to need > its old rank
            (have hceq (= (:creditor e) (:node j))) (exact (Nat.eq_of_beq_eq_true hcn))
            (have hhn (= (comp-has w (:node j)) true)) (rw [← hceq]) (exact hhc)
            (have hrc (= (comp-rank (comp-upd w (:node j) (comp-set-rank (:need j))) (:creditor e)) (:need j)))
            (rw [hceq]) (exact (comp-rank-set-eq w (:node j) (:need j) hhn))
            (rcases he (or h1 (or h2 h3)))
            (simp only [rank-edge-ok hkd hhd hhc Bool.not_true Bool.false_or] at h1)
            (have hl (= (Nat.blt (comp-rank (comp-upd w (:node j) (comp-set-rank (:need j))) (:debtor e))
                                 (comp-rank (comp-upd w (:node j) (comp-set-rank (:need j))) (:creditor e))) true))
            (rw [hrd hrc]) (rw [hceq] at h1) (simp only [Nat.blt_eq] at h1) (simp only [Nat.blt_eq]) (omega)
            (simp only [pend-ok Bool.or_eq_true]) (exact (Or.inl (rank-edge-ok-of-lt _ e hl)))
            (simp only [covers Bool.and_eq_true] at h2)
            (have hl (= (Nat.blt (comp-rank (comp-upd w (:node j) (comp-set-rank (:need j))) (:debtor e))
                                 (comp-rank (comp-upd w (:node j) (comp-set-rank (:need j))) (:creditor e))) true))
            (rw [hrd hrc]) (exact (And.right h2))
            (simp only [pend-ok Bool.or_eq_true]) (exact (Or.inl (rank-edge-ok-of-lt _ e hl)))
            (simp only [pend-ok raise-todo tbl-any-app Bool.or_eq_true])
            (exact (Or.inr (Or.inl (covers-transfer w _ e t hrd h3)))))
          (case [false]
            (have hrc (= (comp-rank (comp-upd w (:node j) (comp-set-rank (:need j))) (:creditor e)) (comp-rank w (:creditor e))))
            (exact (comp-rank-set-ne w (:node j) (:need j) (:creditor e) hcn))
            (rcases he (or h1 (or h2 h3)))
            (simp only [pend-ok rank-edge-ok hhas hrd hrc Bool.or_eq_true])
            (simp only [rank-edge-ok Bool.or_eq_true] at h1)
            (exact (Or.inl h1))
            (simp only [covers Bool.and_eq_true] at h2)
            (have hne (= (:node j) (:creditor e))) (exact (Nat.eq_of_beq_eq_true (And.left h2)))
            (rw [← hne] at hcn) (simp [Nat.beq_refl] at hcn)
            (simp only [pend-ok raise-todo tbl-any-app Bool.or_eq_true])
            (exact (Or.inr (Or.inl (covers-transfer w _ e t hrd h3))))))))))

(a/theorem raise-inv-raise [w :- World, j :- RJ, t :- (List RJ)]
  (=> (= (Nat.ble (:need j) (comp-rank w (:node j))) false)
      (= (raise-inv w (List.cons RJ j t)) true)
      (= (raise-inv (comp-upd w (:node j) (comp-set-rank (:need j))) (raise-todo w j t)) true))
  (intros hk h)
  (simp only [raise-inv] at h)
  (simp only [raise-inv comp-upd set-comps])
  (exact (tbl-all-mem-mono EdgeRow (pend-ok w (List.cons RJ j t))
           (pend-ok (comp-upd w (:node j) (comp-set-rank (:need j))) (raise-todo w j t)) (:edges w)
           (fn [e :- EdgeRow, hm :- (List.Mem e (:edges w)), he :- (= (pend-ok w (List.cons RJ j t) e) true)]
             (pend-raise w j t e hk hm he))
           h)))

;; ---- the loop

(a/theorem raise-loop-ranks [fuel :- (List Nat)]
  (forall [d :- Nat, w :- World, todo :- (List RJ)]
    (=> (= (raise-inv w todo) true) (= (:ok (raise-loop fuel d w todo)) true)
        (= (ranks-ok (:world (raise-loop fuel d w todo))) true)))
  (induction fuel)
  (case' [cons u f ih])
  (case' [nil])
  (intros d w todo h hok)
  (cases todo)
  (simp only [raise-loop]) (exact (raise-inv-done w h))
  (simp [raise-loop] at hok)
  (intros d w todo h hok)
  (cases todo)
  (simp only [raise-loop]) (exact (raise-inv-done w h))
  (rename_i j t)
  (cases hd (Nat.beq (:node j) d))
  (case [true] (simp [raise-loop hd] at hok))
  (case [false]
    (cases hn (Nat.ble (:need j) (comp-rank w (:node j))))
    (case [true]
      (simp only [raise-loop hd hn] at hok)
      (simp only [raise-loop hd hn])
      (exact (ih d w t (raise-inv-skip w j t hn h) hok)))
    (case [false]
      (have h2 := (raise-inv-raise w j t hn h))
      (simp only [raise-todo] at h2)
      (simp only [raise-loop hd hn] at hok)
      (simp only [raise-loop hd hn])
      (exact (ih d _ _ h2 hok)))))

;; inserting an edge changes no computation
(a/theorem edges-ins-fresh [w :- World, e :- EdgeRow]
  (= (:edges (insert-edge-fresh w e))
     (List.cons EdgeRow (edge-set-marked false (edge-set-id (:next-id w) e)) (:edges w)))
  (rfl))
(a/theorem pend-ok-ins [w :- World, e :- EdgeRow, todo :- (List RJ), x :- EdgeRow]
  (= (pend-ok (insert-edge-fresh w e) todo x) (pend-ok w todo x)) (rfl))
(a/theorem rank-edge-ok-ins [w :- World, e :- EdgeRow, x :- EdgeRow]
  (= (rank-edge-ok (insert-edge-fresh w e) x) (rank-edge-ok w x)) (rfl))

(a/theorem pend-of-edge [w :- World, todo :- (List RJ), x :- EdgeRow]
  (=> (= (rank-edge-ok w x) true) (= (pend-ok w todo x) true))
  (intro hx) (simp [pend-ok hx]))

(a/theorem pend-of-ranks [w :- World, todo :- (List RJ)]
  (=> (= (ranks-ok w) true) (= (tbl-all (pend-ok w todo) (:edges w)) true))
  (intro h)
  (simp only [ranks-ok] at h)
  (exact (tbl-all-mono EdgeRow (rank-edge-ok w) (pend-ok w todo) (pend-of-edge w todo) (:edges w) h)))

;; the start: a ranks-ok world plus the edge c -> d, with the job (c, rank d + 1)
(a/theorem raise-inv-start [w :- World, e :- EdgeRow, c :- Nat, d :- Nat]
  (=> (= (ranks-ok w) true) (= (:creditor e) c) (= (:debtor e) d)
      (= (raise-inv (insert-edge-checked w e)
                    (List.cons RJ (RJ.mk c (+ (comp-rank (insert-edge-checked w e) d) 1)) (List.nil RJ))) true))
  (intros h hc hd)
  (cases hk (edge-ok-in w e))
  (case [false]
    (simp only [raise-inv insert-edge-checked hk])
    (exact (pend-of-ranks w _ h)))
  (case [true]
    (simp only [raise-inv insert-edge-checked hk edges-ins-fresh tbl-all pend-ok-ins Bool.and_eq_true])
    (apply And.intro)
    (simp only [pend-ok tbl-any covers Bool.or_eq_true Bool.and_eq_true])
    (apply Or.inr) (apply Or.inl)
    (apply And.intro)
    (simp [edge-set-marked edge-set-id hc])
    (have hr (= (comp-rank (insert-edge-fresh w e) d) (comp-rank w d))) (rfl)
    (simp [edge-set-marked edge-set-id hd hr Nat.blt_eq])
    (exact (pend-of-ranks w _ h))))

(a/theorem ranks-ins-noncomp [w :- World, e :- EdgeRow]
  (=> (= (ranks-ok w) true) (= (comp-has (insert-edge-checked w e) (:debtor e)) false)
      (= (ranks-ok (insert-edge-checked w e)) true))
  (intros h hh)
  (cases hk (edge-ok-in w e))
  (case [false] (simp only [insert-edge-checked hk]) (exact h))
  (case [true]
    (simp only [insert-edge-checked hk] at hh)
    (have hh2 (= (comp-has w (:debtor e)) false)) (exact hh)
    (simp only [ranks-ok insert-edge-checked hk edges-ins-fresh tbl-all rank-edge-ok-ins Bool.and_eq_true])
    (apply And.intro)
    (simp [rank-edge-ok edge-set-marked edge-set-id hh2])
    (simp only [ranks-ok] at h) (exact h)))

;; Theorem: a raise that reports ok leaves the world ranks-ok, the new edge included
(a/theorem raise-run-ranks [w :- World, e :- EdgeRow, c :- Nat, d :- Nat]
  (=> (= (ranks-ok w) true) (= (:creditor e) c) (= (:debtor e) d)
      (= (:ok (raise-run (insert-edge-checked w e) c d)) true)
      (= (ranks-ok (:world (raise-run (insert-edge-checked w e) c d))) true))
  (intros h hc hd hok)
  (have hs := (raise-inv-start w e c d h hc hd))
  (cases hh (comp-has (insert-edge-checked w e) d))
  (case [true]
    (simp only [raise-run hh] at hok)
    (simp only [raise-run hh])
    (exact (raise-loop-ranks (raise-fuel (insert-edge-checked w e)) d _ _ hs hok)))
  (case [false]
    (simp only [raise-run hh])
    (rw [← hd] at hh)
    (exact (ranks-ins-noncomp w e h hh))))

;; ---- the two places that add rank constraints

;; T6: a new dep edge of the run's computation on d, then the raise (T6 refuses when not ok)
(a/theorem await-new-dep-ranks [w :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat]
  (=> (= (ranks-ok w) true) (= (as-dep w r d) true) (= (:ok (await-new-dep w r a mode k d)) true)
      (= (ranks-ok (:world (await-new-dep w r a mode k d))) true))
  (intros h hd hok)
  (have hc (= (:creditor (await-edge w r a mode k d)) (:of r))) (simp [await-edge hd])
  (have hdb (= (:debtor (await-edge w r a mode k d)) d)) (simp [await-edge hd])
  (simp only [await-new-dep] at hok)
  (simp only [await-new-dep])
  (exact (raise-run-ranks w (await-edge w r a mode k d) (:of r) d h hc hdb hok)))

(a/theorem react-ok-raise [w :- World, c :- Nat, v :- Valid]
  (=> (= (react-ok w c v) true) (= (:ok (raise-run (insert-edge-checked w (valid-edge w c v)) c (:debtor v))) true))
  (intro h) (simp only [react-ok Bool.and_eq_true] at h) (exact (And.right h)))
;; a reactivation edge is kept only with an ok raise: unconditionally ranks-ok
(a/theorem react-add-ranks [w :- World, c :- Nat, v :- Valid]
  (=> (= (ranks-ok w) true) (= (ranks-ok (react-add w c v)) true))
  (intro h)
  (cases hk (react-ok w c v))
  (simp only [react-add hk]) (exact h)
  (simp only [react-add hk])
  (exact (raise-run-ranks w (valid-edge w c v) c (:debtor v) h (rfl) (rfl) (react-ok-raise w c v hk))))
