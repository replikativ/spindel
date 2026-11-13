(ns spindel.v2.hmk2
  "h-mark through `world-step` (P11), continued from spindel.v2.hmk: T2 write, T12 complete + settle,
  Rule R's demote, and the step. Kernel-checked, Init only.

  Part A: edge keys backward (`hk-ek es es2`: every edge of es2 has an edge of es with the same id,
  kind, creditor and debtor, marked when it is), copied through every fire and settle edit (`ek-*`,
  generated from l5's es-nm lemmas). Part B: an edge whose creditor is a computation survives a fire
  of another id (`hk-sv-*`). Part C: a computation row property kept by epoch steps and pending
  changes survives every fire (`hk-cs-*`). Part D: T2: a root (creditor of an armed dep edge on the
  written source) is strong after its edge's fire (an invalidation steps the epoch; a delivery needs
  a current alive run, so done-epoch /= epoch by gd's cde); the cone's creditors keep their in-edge,
  which is marked by the fold; `hmk-write-raw-x`, `t2-hmk`. Part E: T12: the completed computation is
  exempt until it settles; a settle exempts the creditors of the unmarked edges until they are queued
  (a live creditor is settle-ready by gd) or found waiting; the loop empties (P7);
  `hmk-complete-raw-x`, `t12-hmk`. Part F: Rule R's demote: the round's strays are the exemption list;
  i14's pass bundle `vr S R` (a dep edge on a stray has a stray creditor not yet demoted) supplies the
  safe creditors of the edges a demotion drops and, at the end of the pass, that no dep edge has a stray
  debtor (`hmk-norm-round`, `hmk-rule-r`). Part G: raw0/raw0g/raw with gd, g7, ga, g10r premises,
  `step-hmk`, `p3l` = p3k && hmk [] with `step-p3l`, `p3l-empty`, and `step-h-mark-total` (h-mark after
  every step from a p3l world, no honest hypothesis)."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [clojure.walk :as walk]
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
            [spindel.v2.i10 :refer :all]
            [spindel.v2.i11 :refer :all]
            [spindel.v2.i1 :refer :all]
            [spindel.v2.i8 :refer :all]
            [spindel.v2.hm :refer :all]
            [spindel.v2.progress :refer :all]
            [spindel.v2.l5 :refer :all]
            [spindel.v2.hmk :refer :all]
            [spindel.v2.i14 :refer :all]))

;; ===========================================================================
;; Part A. Edge keys backward
;; ===========================================================================

;; ---- edge keys backward: every edge of the later list has an edge of the earlier list with the
;; same id, kind, creditor and debtor that is marked when it is
(a/defn hk-kk [r2 :- EdgeRow, r :- EdgeRow] Bool
  (Bool.and (Nat.beq (:id r) (:id r2))
   (Bool.and (Nat.beq (:kind r) (:kind r2))
    (Bool.and (Nat.beq (:creditor r) (:creditor r2))
     (Bool.and (Nat.beq (:debtor r) (:debtor r2)) (Bool.or (Bool.not (:marked r2)) (:marked r)))))))
(a/defn hk-back [es :- (List EdgeRow), r2 :- EdgeRow] Bool (tbl-any (hk-kk r2) es))
(a/defn hk-ek [es :- (List EdgeRow), es2 :- (List EdgeRow)] Bool (tbl-all (hk-back es) es2))

(a/theorem hk-kk-refl [r :- EdgeRow] (= (hk-kk r r) true)
  (cases hm (:marked r))
  (all_goals (simp only [hk-kk hm Nat.beq_refl Bool.not_false Bool.not_true Bool.true_or Bool.or_true Bool.and_self])))
(a/theorem hk-kk-trans [r3 :- EdgeRow, r2 :- EdgeRow, r1 :- EdgeRow]
  (=> (= (hk-kk r3 r2) true) (= (hk-kk r2 r1) true) (= (hk-kk r3 r1) true))
  (intros a b)
  (simp only [hk-kk Bool.and_eq_true] at a b)
  (have a1 := (Nat.eq_of_beq_eq_true (And.left a)))
  (have a2 := (Nat.eq_of_beq_eq_true (And.left (And.right a))))
  (have a3 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right a)))))
  (have a4 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right (And.right a))))))
  (have a5 := (And.right (And.right (And.right (And.right a)))))
  (have b1 := (Nat.eq_of_beq_eq_true (And.left b)))
  (have b2 := (Nat.eq_of_beq_eq_true (And.left (And.right b))))
  (have b3 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right b)))))
  (have b4 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right (And.right b))))))
  (have b5 := (And.right (And.right (And.right (And.right b)))))
  (have m (= (Bool.or (Bool.not (:marked r3)) (:marked r1)) true))
  (cases h3 (:marked r3))
  (simp only [Bool.not_false Bool.true_or])
  (simp only [h3 Bool.not_true Bool.false_or] at a5)
  (simp only [a5 Bool.not_true Bool.false_or] at b5)
  (simp only [b5 Bool.or_true])
  (simp only [hk-kk b1 a1 b2 a2 b3 a3 b4 a4 Nat.beq_refl m Bool.and_self]))

(a/theorem hk-ek-refl [es :- (List EdgeRow)] (= (hk-ek es es) true)
  (simp only [hk-ek])
  (apply (all-of-mem EdgeRow _ es))
  (intros r m)
  (simp only [hk-back])
  (exact (any-elim-of EdgeRow (hk-kk r) r es m (hk-kk-refl r))))
(a/theorem hk-back-trans [es1 :- (List EdgeRow), es2 :- (List EdgeRow), r3 :- EdgeRow]
  (=> (= (hk-ek es1 es2) true) (= (hk-back es2 r3) true) (= (hk-back es1 r3) true))
  (intros h1 h2)
  (simp only [hk-back] at h2)
  (apply (any-elim EdgeRow (hk-kk r3) _ es2 h2))
  (intros r2 m2 k2)
  (simp only [hk-ek] at h1)
  (have b := (tbl-all-mem EdgeRow (hk-back es1) r2 es2 h1 m2))
  (simp only [hk-back] at b)
  (apply (any-elim EdgeRow (hk-kk r2) _ es1 b))
  (intros r1 m1 k1)
  (simp only [hk-back])
  (exact (any-elim-of EdgeRow (hk-kk r3) r1 es1 m1 (hk-kk-trans r3 r2 r1 k2 k1))))
(a/theorem hk-ek-trans [es1 :- (List EdgeRow), es2 :- (List EdgeRow), es3 :- (List EdgeRow)]
  (=> (= (hk-ek es1 es2) true) (= (hk-ek es2 es3) true) (= (hk-ek es1 es3) true))
  (intros h1 h2)
  (simp only [hk-ek] at h2)
  (simp only [hk-ek])
  (apply (tbl-all-mono EdgeRow (hk-back es2) (hk-back es1) _ es3 h2))
  (intros r hr)
  (exact (hk-back-trans es1 es2 r h1 hr)))
(a/theorem hk-ek-upd [x :- Nat, f :- (=> EdgeRow EdgeRow), hf :- (forall [e :- EdgeRow] (= (hk-kk (f e) e) true)), es :- (List EdgeRow)]
  (= (hk-ek es (tbl-upd edge-id x f es)) true)
  (have r0 := (hk-ek-refl es)) (simp only [hk-ek] at r0)
  (simp only [hk-ek])
  (apply (tbl-all-upd EdgeRow edge-id x f (hk-back es) (hk-back es) _ _ es r0))
  (intros r hr hx)
  (simp only [hk-back] at hr)
  (apply (any-elim EdgeRow (hk-kk r) _ es hr))
  (intros r1 m1 k1)
  (simp only [hk-back])
  (exact (any-elim-of EdgeRow (hk-kk (f r)) r1 es m1 (hk-kk-trans (f r) r r1 (hf r) k1)))
  (intros r hr hx) (exact hr))
(a/theorem hk-ek-del [x :- Nat, es :- (List EdgeRow)] (= (hk-ek es (tbl-del edge-id x es)) true)
  (have r0 := (hk-ek-refl es)) (simp only [hk-ek] at r0)
  (simp only [hk-ek])
  (exact (tbl-all-del EdgeRow edge-id x (hk-back es) (hk-back es)
           (fn [r :- EdgeRow, p :- (= (hk-back es r) true), q :- (= (Nat.beq (edge-id r) x) false)] p) es r0)))
(a/theorem hk-ek-filter [q :- (=> EdgeRow Bool), es :- (List EdgeRow)] (= (hk-ek es (tbl-filter q es)) true)
  (have r0 := (hk-ek-refl es)) (simp only [hk-ek] at r0)
  (simp only [hk-ek])
  (exact (tbl-all-filter EdgeRow (hk-back es) q es r0)))

(a/theorem hk-kk-phase [p :- Nat] (forall [e :- EdgeRow] (= (hk-kk (edge-set-phase p e) e) true))
  (intro e) (cases hm (:marked e)) (all_goals (simp [hk-kk edge-set-phase hm Nat.beq_refl])))
(a/theorem hk-kk-rearm [v :- Nat, ver :- Nat] (forall [e :- EdgeRow] (= (hk-kk (edge-rearm v ver e) e) true))
  (intro e) (cases hm (:marked e)) (all_goals (simp [hk-kk edge-rearm hm Nat.beq_refl])))
(a/theorem hk-kk-seen [n :- Nat] (forall [e :- EdgeRow] (= (hk-kk (edge-set-seen n e) e) true))
  (intro e) (cases hm (:marked e)) (all_goals (simp [hk-kk edge-set-seen hm Nat.beq_refl])))
(a/theorem hk-kk-unmark [] (forall [e :- EdgeRow] (= (hk-kk (edge-set-marked false e) e) true))
  (intro e) (simp [hk-kk edge-set-marked Nat.beq_refl]))

;; the es-nm lemmas of spindel.v2.l5 restated for hk-ek (same proofs, renamed)
(def ^:private ek-names '[nm-edge-upd nm-remove-edge nm-unmark-edge nm-invalidate nm-dep-consumed nm-drop-act nm-resume nm-fill-slot
                          nm-deliver-dep nm-fire-dep nm-fire-wait nm-fire-observe nm-fire-edge nm-nat-fold nm-settle-host nm-settle-fire nm-settle-edge])
(def ^:private ek-ren (merge '{es-nm-refl hk-ek-refl es-nm-trans hk-ek-trans es-nm-upd hk-ek-upd es-nm-del hk-ek-del es-nm-filter hk-ek-filter
                               ekeep-phase hk-kk-phase ekeep-rearm hk-kk-rearm ekeep-seen hk-kk-seen ekeep-unmark hk-kk-unmark}
                             (into {} (map (fn [n] [n (symbol (str "ek-" (subs (name n) 3)))]) ek-names))))
(defn- ek-tr [f]
  (walk/prewalk (fn [y] (cond (and (seq? y) (= 'es-nm (first y))) (list '= (apply list 'hk-ek (rest y)) 'true)
                              (and (seq? y) (= 'ekeep (first y))) (list 'hk-kk (list (nth y 1) (nth y 2)) (nth y 2))
                              (symbol? y) (get ek-ren y y)
                              :else y)) f))
(let [l5-forms (@#'spindel.v2.lit/ns-source-forms 'spindel.v2.l5)]
  (doseq [n ek-names]
    (eval (ek-tr (first (filter #(and (seq? %) (= 'a/theorem (first %)) (= n (second %))) l5-forms))))))

;; ===========================================================================
;; Part B. Survival of an edge through fires of other ids
;; ===========================================================================

;; ---- an edge survives a fire of another id when its creditor is a computation
(a/theorem hk-mem-upd-ne [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), r :- A, xs :- (List A)]
  (=> (List.Mem r xs) (= (Nat.beq (idf r) x) false) (List.Mem r (tbl-upd idf x f xs)))
  (induction xs)
  (case [nil] (intros m hx) (cases m))
  (case [cons h t ih]
    (intros m hx)
    (cases m)
    (case [head] (simp only [tbl-upd hx]) (exact (List.Mem.head _)))
    (case [tail m2]
      (cases hh (Nat.beq (idf h) x))
      (case [false] (simp only [tbl-upd hh]) (exact (List.Mem.tail h (ih m2 hx))))
      (case [true] (simp only [tbl-upd hh]) (exact (List.Mem.tail (f h) (ih m2 hx)))))))
(a/theorem hk-mem-del-ne [A :- Type, idf :- (=> A Nat), x :- Nat, r :- A, xs :- (List A)]
  (=> (List.Mem r xs) (= (Nat.beq (idf r) x) false) (List.Mem r (tbl-del idf x xs)))
  (induction xs)
  (case [nil] (intros m hx) (cases m))
  (case [cons h t ih]
    (intros m hx)
    (cases m)
    (case [head] (simp only [tbl-del hx]) (exact (List.Mem.head _)))
    (case [tail m2]
      (cases hh (Nat.beq (idf h) x))
      (case [false] (simp only [tbl-del hh]) (exact (List.Mem.tail h (ih m2 hx))))
      (case [true] (simp only [tbl-del hh]) (exact (ih m2 hx))))))
(a/theorem hk-mem-filter [A :- Type, q :- (=> A Bool), r :- A, xs :- (List A)]
  (=> (List.Mem r xs) (= (q r) true) (List.Mem r (tbl-filter q xs)))
  (induction xs)
  (case [nil] (intros m hx) (cases m))
  (case [cons h t ih]
    (intros m hx)
    (cases m)
    (case [head] (simp only [tbl-filter hx]) (exact (List.Mem.head _)))
    (case [tail m2]
      (cases hh (q h))
      (case [false] (simp only [tbl-filter hh]) (exact (ih m2 hx)))
      (case [true] (simp only [tbl-filter hh]) (exact (List.Mem.tail h (ih m2 hx)))))))

(a/theorem hk-sv-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow), r :- EdgeRow]
  (=> (List.Mem r (:edges w)) (= (Nat.beq (:id r) x) false) (List.Mem r (:edges (edge-upd w x f))))
  (intros m hx) (simp only [edge-upd set-edges]) (exact (hk-mem-upd-ne EdgeRow edge-id x f r (:edges w) m hx)))
(a/theorem hk-sv-remove [w :- World, x :- Nat, r :- EdgeRow]
  (=> (List.Mem r (:edges w)) (= (Nat.beq (:id r) x) false) (List.Mem r (:edges (remove-edge w x))))
  (intros m hx)
  (have d := (hk-mem-del-ne EdgeRow edge-id x r (:edges w) m hx))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact m))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm edge-del set-edges]) (exact d))
    (case [true] (simp only [remove-edge hf hm edge-del comp-upd set-edges set-comps]) (exact d))))
(a/theorem hk-sv-drop-act [w :- World, a :- Nat, r :- EdgeRow]
  (=> (List.Mem r (:edges w)) (= (tbl-has comp-id (:creditor r) (:comps w)) true) (= (tbl-has comp-id a (:comps w)) false)
      (List.Mem r (:edges (drop-act w a))))
  (intros m hc ha)
  (have q (= (cred-ne a r) true))
  (cases he (Nat.beq (:creditor r) a))
  (case [false] (simp only [cred-ne he Bool.not_false]))
  (case [true] (have e := (Nat.eq_of_beq_eq_true he)) (rw [e] at hc) (rw [hc] at ha) (cases ha))
  (simp only [drop-act act-del drop-cred-edges comp-upd set-acts set-comps set-edges])
  (exact (hk-mem-filter EdgeRow (cred-ne a) r (:edges w) m q)))
(a/theorem hk-sv-fill-slot [w :- World, a :- ActRow, x :- Nat, v :- RunResult, r :- EdgeRow]
  (=> (List.Mem r (:edges w)) (= (tbl-has comp-id (:creditor r) (:comps w)) true) (= (tbl-has comp-id (:id a) (:comps w)) false)
      (List.Mem r (:edges (fill-slot w a x v))))
  (intros m hc ha)
  (cases hr (act-ready (act-fill x v a)))
  (case [false] (simp only [fill-slot hr act-upd set-acts]) (exact m))
  (case [true] (simp only [fill-slot hr resume run-upd set-runs]) (exact (hk-sv-drop-act w (:id a) r m hc ha))))
(a/theorem hk-sv-dep-consumed [w :- World, e :- EdgeRow, r :- EdgeRow]
  (=> (List.Mem r (:edges w)) (= (Nat.beq (:id r) (:id e)) false) (List.Mem r (:edges (dep-consumed w e))))
  (intros m hx)
  (cases hd (deb-final w (:debtor e)))
  (case [false] (simp only [dep-consumed hd]) (exact (hk-sv-upd w (:id e) _ r m hx)))
  (case [true] (simp only [dep-consumed hd]) (exact (hk-sv-remove w (:id e) r m hx))))
(a/theorem hk-sv-fire-dep [w :- World, e :- EdgeRow, r :- EdgeRow]
  (=> (= (inv-sample w) true) (List.Mem r (:edges w)) (= (tbl-has comp-id (:creditor r) (:comps w)) true) (= (Nat.beq (:id r) (:id e)) false)
      (List.Mem r (:edges (fire-dep w e))))
  (intros hs m hc hx)
  (have iv (List.Mem r (:edges (invalidate w e))))
  (simp only [invalidate comp-upd set-comps]) (exact (hk-sv-upd w (:id e) _ r m hx))
  (cases ha (act-with-member (:id e) (:acts w)))
  (case [none] (simp only [fire-dep ha]) (exact iv))
  (case [some a]
    (cases hk (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
    (case [false] (simp only [fire-dep ha hk]) (exact iv))
    (case [true]
      (simp only [fire-dep ha hk deliver-dep])
      (have na := (act-not-comp w (:id a) hs (has-of-mem ActRow act-id a (:acts w) (act-with-member-mem (:id e) (:acts w) a ha))))
      (have na2 (= (tbl-has comp-id (:id a) (:comps (dep-consumed w e))) false)) (rw [hk-has-dep-consumed]) (exact na)
      (have hc2 (= (tbl-has comp-id (:creditor r) (:comps (dep-consumed w e))) true)) (rw [hk-has-dep-consumed]) (exact hc)
      (exact (hk-sv-fill-slot (dep-consumed w e) a (:id e) _ r (hk-sv-dep-consumed w e r m hx) hc2 na2)))))
(a/theorem hk-sv-fire-wait [res :- RunResult, w :- World, e :- EdgeRow, r :- EdgeRow]
  (=> (= (inv-sample w) true) (List.Mem r (:edges w)) (= (tbl-has comp-id (:creditor r) (:comps w)) true) (= (Nat.beq (:id r) (:id e)) false)
      (List.Mem r (:edges (fire-wait res w e))))
  (intros hs m hc hx)
  (have u := (hk-sv-upd w (:id e) (edge-set-phase ph-fired) r m hx))
  (cases hz (Nat.beq (:creditor e) 0))
  (case [true] (simp only [fire-wait hz]) (exact (hk-sv-remove w (:id e) r m hx)))
  (case [false]
    (simp only [fire-wait hz])
    (cases ha (act-find w (:creditor e)))
    (case [none] (simp only [fire-wait-act ha]) (exact u))
    (case [some a]
      (cases hk (run-current w (:run a)))
      (case [false] (simp only [fire-wait-act ha hk]) (exact u))
      (case [true]
        (simp only [fire-wait-act ha hk])
        (have na := (act-not-comp w (:id a) hs (has-of-mem ActRow act-id a (:acts w) (tbl-find-mem ActRow act-id (:creditor e) a (:acts w) ha))))
        (exact (hk-sv-fill-slot (edge-upd w (:id e) (edge-set-phase ph-fired)) a (:id e) res r u hc na))))))
(a/theorem hk-sv-fire-edge [res :- RunResult, w :- World, y :- Nat, r :- EdgeRow]
  (=> (= (inv-sample w) true) (List.Mem r (:edges w)) (= (tbl-has comp-id (:creditor r) (:comps w)) true) (= (Nat.beq (:id r) y) false)
      (List.Mem r (:edges (fire-edge res w y))))
  (intros hs m hc hy)
  (cases hf (edge-find w y))
  (case [none] (simp only [fire-edge hf]) (exact m))
  (case [some e]
    (have ie (= (:id e) y)) (exact (tbl-find-id EdgeRow edge-id y e (:edges w) hf))
    (have hx (= (Nat.beq (:id r) (:id e)) false)) (rw [ie]) (exact hy)
    (cases hp (Nat.beq (:phase e) ph-armed))
    (case [false] (simp only [fire-edge hf hp]) (exact m))
    (case [true]
      (cases k1 (Nat.beq (:kind e) ek-dep))
      (case [true] (simp only [fire-edge hf hp k1]) (exact (hk-sv-fire-dep w e r hs m hc hx)))
      (case [false]
        (cases k2 (Nat.beq (:kind e) ek-wait))
        (case [true] (simp only [fire-edge hf hp k1 k2]) (exact (hk-sv-fire-wait res w e r hs m hc hx)))
        (case [false]
          (cases k3 (Nat.beq (:kind e) ek-observe))
          (case [false] (simp only [fire-edge hf hp k1 k2 k3 fire-savepoint-todo]) (exact m))
          (case [true]
            (cases hn (observe-new e (deb-version w (:debtor e))))
            (case [false] (simp only [fire-edge hf hp k1 k2 k3 fire-observe hn]) (exact m))
            (case [true] (simp only [fire-edge hf hp k1 k2 k3 fire-observe hn]) (exact (hk-sv-upd w (:id e) _ r m hx)))))))))
(a/theorem hk-sv-fold [res :- RunResult, r :- EdgeRow, ys :- (List Nat)]
  (forall [w :- World] (=> (= (inv-sample w) true) (List.Mem r (:edges w)) (= (tbl-has comp-id (:creditor r) (:comps w)) true)
                           (= (reach-mem (:id r) ys) false)
                           (List.Mem r (:edges (nat-fold (fire-edge res) w ys)))))
  (induction ys)
  (case [nil] (intros w hs m hc hy) (simp only [nat-fold]) (exact m))
  (case [cons y t ih]
    (intros w hs m hc hy)
    (simp only [reach-mem-cons Bool.or_eq_false_iff] at hy)
    (have hc2 (= (tbl-has comp-id (:creditor r) (:comps (fire-edge res w y))) true)) (rw [hk-has-fire-edge]) (exact hc)
    (simp only [nat-fold])
    (exact (ih (fire-edge res w y) (inv-fire-edge res w y hs) (hk-sv-fire-edge res w y r hs m hc (And.left hy)) hc2 (And.right hy)))))

;; ===========================================================================
;; Part C. Computation row properties through fires
;; ===========================================================================

;; ---- a row property of the computations kept by every fire: fires only step epochs and change pendings
(a/theorem hk-cs-upd [R :- (=> CompRow Bool), f :- (=> CompRow CompRow), hf :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (f c)) true))),
                      x :- Nat, cs :- (List CompRow)]
  (=> (= (tbl-all R cs) true) (= (tbl-all R (tbl-upd comp-id x f cs)) true))
  (intro h)
  (exact (tbl-all-upd CompRow comp-id x f R R (fn [c :- CompRow, p :- (= (R c) true), q :- (= (Nat.beq (comp-id c) x) true)] (hf c p))
           (fn [c :- CompRow, p :- (= (R c) true), q :- (= (Nat.beq (comp-id c) x) false)] p) cs h)))
(a/theorem hk-cs-remove [R :- (=> CompRow Bool), h2 :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-dec-pending c)) true))),
                         w :- World, x :- Nat]
  (=> (= (tbl-all R (:comps w)) true) (= (tbl-all R (:comps (remove-edge w x))) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm edge-del set-edges]) (exact h))
    (case [true] (simp only [remove-edge hf hm edge-del comp-upd set-edges set-comps]) (exact (hk-cs-upd R comp-dec-pending h2 (:creditor e) (:comps w) h)))))
(a/theorem hk-cs-fill-slot [R :- (=> CompRow Bool), h3 :- (forall [c :- CompRow, n :- Nat] (=> (= (R c) true) (= (R (comp-set-pending n c)) true))),
                            w :- World, a :- ActRow, x :- Nat, v :- RunResult]
  (=> (= (tbl-all R (:comps w)) true) (= (tbl-all R (:comps (fill-slot w a x v))) true))
  (intro h)
  (cases hr (act-ready (act-fill x v a)))
  (case [false] (simp only [fill-slot hr act-upd set-acts]) (exact h))
  (case [true]
    (simp only [fill-slot hr resume run-upd set-runs drop-act act-del drop-cred-edges comp-upd set-acts set-comps set-edges])
    (exact (hk-cs-upd R (comp-set-pending 0) (fn [c :- CompRow, p :- (= (R c) true)] (h3 c 0 p)) (:id a) (:comps w) h))))
(a/theorem hk-cs-dep-consumed [R :- (=> CompRow Bool), h2 :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-dec-pending c)) true))),
                               w :- World, e :- EdgeRow]
  (=> (= (tbl-all R (:comps w)) true) (= (tbl-all R (:comps (dep-consumed w e))) true))
  (intro h)
  (cases hd (deb-final w (:debtor e)))
  (case [false] (simp only [dep-consumed hd edge-upd set-edges]) (exact h))
  (case [true] (simp only [dep-consumed hd]) (exact (hk-cs-remove R h2 w (:id e) h))))
(a/theorem hk-cs-fire-dep [R :- (=> CompRow Bool),
                           h1 :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-inc-epoch c)) true))),
                           h2 :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-dec-pending c)) true))),
                           h3 :- (forall [c :- CompRow, n :- Nat] (=> (= (R c) true) (= (R (comp-set-pending n c)) true))),
                           w :- World, e :- EdgeRow]
  (=> (= (tbl-all R (:comps w)) true) (= (tbl-all R (:comps (fire-dep w e))) true))
  (intro h)
  (have iv (= (tbl-all R (:comps (invalidate w e))) true))
  (simp only [invalidate comp-upd edge-upd set-comps set-edges]) (exact (hk-cs-upd R comp-inc-epoch h1 (:creditor e) (:comps w) h))
  (cases ha (act-with-member (:id e) (:acts w)))
  (case [none] (simp only [fire-dep ha]) (exact iv))
  (case [some a]
    (cases hk (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
    (case [false] (simp only [fire-dep ha hk]) (exact iv))
    (case [true]
      (simp only [fire-dep ha hk deliver-dep])
      (exact (hk-cs-fill-slot R h3 (dep-consumed w e) a (:id e) _ (hk-cs-dep-consumed R h2 w e h))))))
(a/theorem hk-cs-fire-edge [R :- (=> CompRow Bool),
                            h1 :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-inc-epoch c)) true))),
                            h2 :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-dec-pending c)) true))),
                            h3 :- (forall [c :- CompRow, n :- Nat] (=> (= (R c) true) (= (R (comp-set-pending n c)) true))),
                            res :- RunResult, w :- World, y :- Nat]
  (=> (= (tbl-all R (:comps w)) true) (= (tbl-all R (:comps (fire-edge res w y))) true))
  (intro h)
  (cases hf (edge-find w y))
  (case [none] (simp only [fire-edge hf]) (exact h))
  (case [some e]
    (have u (= (tbl-all R (:comps (edge-upd w (:id e) (edge-set-phase ph-fired)))) true)) (exact h)
    (cases hp (Nat.beq (:phase e) ph-armed))
    (case [false] (simp only [fire-edge hf hp]) (exact h))
    (case [true]
      (cases k1 (Nat.beq (:kind e) ek-dep))
      (case [true] (simp only [fire-edge hf hp k1]) (exact (hk-cs-fire-dep R h1 h2 h3 w e h)))
      (case [false]
        (cases k2 (Nat.beq (:kind e) ek-wait))
        (case [true]
          (simp only [fire-edge hf hp k1 k2])
          (cases hz (Nat.beq (:creditor e) 0))
          (case [true] (simp only [fire-wait hz]) (exact (hk-cs-remove R h2 w (:id e) h)))
          (case [false]
            (simp only [fire-wait hz])
            (cases ha (act-find w (:creditor e)))
            (case [none] (simp only [fire-wait-act ha]) (exact u))
            (case [some a]
              (cases hk (run-current w (:run a)))
              (case [false] (simp only [fire-wait-act ha hk]) (exact u))
              (case [true] (simp only [fire-wait-act ha hk]) (exact (hk-cs-fill-slot R h3 _ a (:id e) res u))))))
        (case [false]
          (cases k3 (Nat.beq (:kind e) ek-observe))
          (case [false] (simp only [fire-edge hf hp k1 k2 k3 fire-savepoint-todo]) (exact h))
          (case [true]
            (cases hn (observe-new e (deb-version w (:debtor e))))
            (case [false] (simp only [fire-edge hf hp k1 k2 k3 fire-observe hn]) (exact h))
            (case [true] (simp only [fire-edge hf hp k1 k2 k3 fire-observe hn edge-upd set-edges]) (exact h))))))))
(a/theorem hk-cs-fold [R :- (=> CompRow Bool),
                       h1 :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-inc-epoch c)) true))),
                       h2 :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-dec-pending c)) true))),
                       h3 :- (forall [c :- CompRow, n :- Nat] (=> (= (R c) true) (= (R (comp-set-pending n c)) true))),
                       res :- RunResult, ys :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all R (:comps w)) true) (= (tbl-all R (:comps (nat-fold (fire-edge res) w ys))) true)))
  (induction ys)
  (case [nil] (intros w h) (simp only [nat-fold]) (exact h))
  (case [cons y t ih] (intros w h) (simp only [nat-fold]) (exact (ih (fire-edge res w y) (hk-cs-fire-edge R h1 h2 h3 res w y h)))))

;; the two row properties: strong (hk-rc) and awake
(a/theorem hk-rc-inc [d :- Nat, c :- CompRow] (=> (= (hk-rc d c) true) (= (hk-rc d (comp-inc-epoch c)) true))
  (intro h)
  (cases hx (Nat.beq (:id c) d))
  (case [false] (simp only [hk-rc comp-inc-epoch hx Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [hk-rc hx Bool.not_true Bool.false_or Bool.and_eq_true] at h)
    (have l := (gd-lt-of _ _ (And.right h)))
    (have z (= (Nat.blt (:done-epoch c) (+ (:epoch c) 1)) true)) (apply gd-blt-of) (omega)
    (simp only [hk-rc comp-inc-epoch hx (And.left h) z Bool.not_true Bool.not_false Bool.false_or Bool.and_self])))
(a/theorem hk-rc-dec [d :- Nat, c :- CompRow] (=> (= (hk-rc d c) true) (= (hk-rc d (comp-dec-pending c)) true))
  (intro h) (exact h))
(a/theorem hk-rc-setp [d :- Nat, c :- CompRow, n :- Nat] (=> (= (hk-rc d c) true) (= (hk-rc d (comp-set-pending n c)) true))
  (intro h) (exact h))
(a/theorem hk-aw-inc [d :- Nat, c :- CompRow] (=> (= (not-idle-if-id d c) true) (= (not-idle-if-id d (comp-inc-epoch c)) true))
  (intro h) (exact h))
(a/theorem hk-aw-dec [d :- Nat, c :- CompRow] (=> (= (not-idle-if-id d c) true) (= (not-idle-if-id d (comp-dec-pending c)) true))
  (intro h) (exact h))
(a/theorem hk-aw-setp [d :- Nat, c :- CompRow, n :- Nat] (=> (= (not-idle-if-id d c) true) (= (not-idle-if-id d (comp-set-pending n c)) true))
  (intro h) (exact h))

;; ===========================================================================
;; Part D. T2 write
;; ===========================================================================

;; ---- a root: the fire of its armed dep edge on the written source leaves it strong
(a/theorem hk-rc-ne [d :- Nat, c :- CompRow] (=> (= (Nat.beq (:id c) d) false) (= (hk-rc d c) true))
  (intro h) (simp only [hk-rc h Bool.not_false Bool.true_or]))
(a/theorem hk-rc-same [w :- World, c :- CompRow, d :- Nat]
  (=> (= (inv-sample w) true) (List.Mem c (:comps w)) (= (:id c) d) (= (hk-rc d c) true) (= (tbl-all (hk-rc d) (:comps w)) true))
  (intros hs mc ic h)
  (have u := (gd-same-id w c (hk-rc d) hs mc h))
  (apply (tbl-all-mono CompRow _ (hk-rc d) _ (:comps w) u))
  (intros r hr)
  (cases hx (Nat.beq (:id r) d))
  (case [false] (exact (hk-rc-ne d r hx)))
  (case [true]
    (have hx2 (= (Nat.beq (comp-id r) (:id c)) true)) (rw [ic]) (exact hx)
    (simp only [same-id-then hx2 Bool.not_true Bool.false_or] at hr) (exact hr)))
;; a computation with a current alive run at its epoch is strong
(a/theorem hk-rc-cur [w :- World, rid :- Nat, d :- Nat, q :- RunRow]
  (=> (= (gd w) true) (= (awake (:comps w) d) true) (= (run-find w rid) (Option.some RunRow q)) (= (run-alive q) true)
      (= (run-current-of w rid d) true) (= (tbl-all (hk-rc d) (:comps w)) true))
  (intros hg ha hq hal hc)
  (have hs := (gd-sample w hg))
  (simp only [run-current-of hq run-current Bool.and_eq_true] at hc)
  (have od := (Nat.eq_of_beq_eq_true (And.left hc)))
  (have hc2 := (And.right hc))
  (cases hf (comp-find w (:of q)))
  (case [none]
    (apply (all-of-mem CompRow _ (:comps w)))
    (intros r mr)
    (cases hx (Nat.beq (:id r) d))
    (case [false] (exact (hk-rc-ne d r hx)))
    (case [true]
      (have e := (Nat.eq_of_beq_eq_true hx))
      (have z := (tbl-find-none-has CompRow comp-id (:of q) (:comps w) hf))
      (have z2 := (has-of-mem CompRow comp-id r (:comps w) mr))
      (have e2 (= (comp-id r) (:of q))) (exact (Eq.trans e (Eq.symm od)))
      (rw [e2] at z2) (rw [z2] at z) (cases z)))
  (case [some c]
    (have hc3 (= (Nat.beq (:epoch q) (:epoch c)) true)) (rw [hf] at hc2) (exact hc2)
    (have mc := (tbl-find-mem CompRow comp-id (:of q) c (:comps w) hf))
    (have ic (= (:id c) d)) (exact (Eq.trans (tbl-find-id CompRow comp-id (:of q) c (:comps w) hf) od))
    (have p := (gdk-parts _ _ _ (gd-rest-of w hg)))
    (have qa := (And.right p)) (rw [all-gdkeys] at qa)
    (have pc := (gd-c-parts _ _ _ (tbl-all-mem CompRow (fn [x :- CompRow] (gd-c (:runs w) (:next-id w) (gdkey x))) c (:comps w) qa mc)))
    (have dl := (And.left pc)) (simp only [gd-dle gdkey Bool.and_eq_true] at dl)
    (have l1 := (gd-le-of _ _ (And.left dl)))
    (have cd := (And.right (And.right (And.right pc))))
    (have mq := (tbl-find-mem RunRow run-id rid q (:runs w) hq))
    (have ne (= (Nat.beq (:done-epoch c) (:epoch c)) false))
    (cases hde (Nat.beq (:done-epoch c) (:epoch c)))
    (case [false] (rfl))
    (case [true]
      (simp only [gd-cde gdkey hde Bool.not_true Bool.false_or] at cd)
      (have nq := (tbl-all-mem RunRow _ q (:runs w) cd mq))
      (have o2 (= (Nat.beq (:of q) (:id c)) true)) (rw [ic]) (rw [od]) (exact (Nat.beq_refl d))
      (simp only [gd-ncur gdkey o2 hc3 hal Bool.and_self Bool.not_true] at nq) (cases nq))
    (have ne2 := (Nat.ne_of_beq_eq_false ne))
    (have lt (= (Nat.blt (:done-epoch c) (:epoch c)) true)) (apply gd-blt-of) (omega)
    (have aw := (tbl-all-mem CompRow (not-idle-if-id d) c (:comps w) ha mc))
    (have ic2 (= (Nat.beq (:id c) d) true)) (rw [ic]) (exact (Nat.beq_refl d))
    (simp only [not-idle-if-id ic2 Bool.not_true Bool.false_or] at aw)
    (have rc (= (hk-rc d c) true)) (simp only [hk-rc ic2 aw lt Bool.not_true Bool.false_or Bool.and_self])
    (exact (hk-rc-same w c d hs mc ic rc))))
;; an invalidation of a dep edge whose creditor is awake leaves the creditor strong
(a/theorem hk-rc-inv [w :- World, e :- EdgeRow]
  (=> (= (gd w) true) (= (awake (:comps w) (:creditor e)) true) (= (tbl-all (hk-rc (:creditor e)) (:comps (invalidate w e))) true))
  (intros hg ha)
  (have p := (gdk-parts _ _ _ (gd-rest-of w hg)))
  (have qa := (And.right p)) (rw [all-gdkeys] at qa)
  (simp only [invalidate comp-upd edge-upd set-comps set-edges])
  (apply (hk-all-upd-mem CompRow comp-id (:creditor e) comp-inc-epoch _ (hk-rc (:creditor e)) (:comps w) _ _ qa))
  (intros r mr hr hx)
  (have dl := (And.left (gd-c-parts _ _ _ hr))) (simp only [gd-dle gdkey Bool.and_eq_true] at dl)
  (have l1 := (gd-le-of _ _ (And.left dl)))
  (have aw := (tbl-all-mem CompRow (not-idle-if-id (:creditor e)) r (:comps w) ha mr))
  (have hx2 (= (Nat.beq (:id r) (:creditor e)) true)) (exact hx)
  (simp only [not-idle-if-id hx2 Bool.not_true Bool.false_or] at aw)
  (have z (= (Nat.blt (:done-epoch r) (+ (:epoch r) 1)) true)) (apply gd-blt-of) (omega)
  (simp only [hk-rc comp-inc-epoch hx2 aw z Bool.not_true Bool.false_or Bool.and_self])
  (intros r mr hr hx) (exact (hk-rc-ne (:creditor e) r hx)))
(a/theorem hk-root-fire [res :- RunResult, w :- World, e0 :- EdgeRow]
  (=> (= (gd w) true) (= (ga w) true) (List.Mem e0 (:edges w)) (= (Nat.beq (:phase e0) ph-armed) true) (= (Nat.beq (:kind e0) ek-dep) true)
      (= (awake (:comps w) (:creditor e0)) true)
      (= (tbl-all (hk-rc (:creditor e0)) (:comps (fire-edge res w (:id e0)))) true))
  (intros hg hga m hp hk ha)
  (have hs := (gd-sample w hg))
  (have hf := (find-self EdgeRow edge-id e0 (:edges w) (l5-edge-nodup w hs) m))
  (have hf2 (= (edge-find w (:id e0)) (Option.some EdgeRow e0))) (exact hf)
  (simp only [fire-edge hf2 hp hk])
  (cases hm (act-with-member (:id e0) (:acts w)))
  (case [none] (simp only [fire-dep hm]) (exact (hk-rc-inv w e0 hg ha)))
  (case [some a]
    (cases hc (Bool.and (run-current-of w (:run a) (:creditor e0)) (deb-avail w (:debtor e0))))
    (case [false] (simp only [fire-dep hm hc]) (exact (hk-rc-inv w e0 hg ha)))
    (case [true]
      (simp only [fire-dep hm hc deliver-dep])
      (simp only [Bool.and_eq_true] at hc)
      (have rc := (And.left hc))
      (cases hq (run-find w (:run a)))
      (case [none] (simp only [run-current-of hq] at rc) (cases rc))
      (case [some q]
        (have ma := (act-with-member-mem (:id e0) (:acts w) a hm))
        (have ok := (tbl-all-mem ActRow (act-run-ok (:runs w)) a (:acts w) (ga-acts-alive w hga) ma))
        (simp only [act-run-ok] at ok)
        (have mq := (tbl-find-mem RunRow run-id (:run a) q (:runs w) hq))
        (have rq := (tbl-all-mem RunRow (run-ok-for (:run a)) q (:runs w) ok mq))
        (have iq0 (= (:id q) (:run a))) (exact (tbl-find-id RunRow run-id (:run a) q (:runs w) hq))
        (have iq (= (Nat.beq (:id q) (:run a)) true)) (rw [iq0]) (exact (Nat.beq_refl _))
        (simp only [run-ok-for iq Bool.not_true Bool.false_or] at rq)
        (have r0 := (hk-rc-cur w (:run a) (:creditor e0) q hg ha hq rq rc))
        (exact (hk-cs-fill-slot (hk-rc (:creditor e0)) (hk-rc-setp (:creditor e0)) (dep-consumed w e0) a (:id e0) _
                 (hk-cs-dep-consumed (hk-rc (:creditor e0)) (hk-rc-dec (:creditor e0)) w e0 r0)))))))
;; ---- the root through the whole fire fold
(a/theorem hk-root-fold [res :- RunResult, e0 :- EdgeRow, ys :- (List Nat)]
  (forall [w :- World]
    (=> (= (gd w) true) (= (ga w) true) (= (Nat.beq (:phase e0) ph-armed) true) (= (Nat.beq (:kind e0) ek-dep) true)
        (= (awake (:comps w) (:creditor e0)) true)
        (Or (= (tbl-all (hk-rc (:creditor e0)) (:comps w)) true) (And (List.Mem e0 (:edges w)) (= (reach-mem (:id e0) ys) true)))
        (= (tbl-all (hk-rc (:creditor e0)) (:comps (nat-fold (fire-edge res) w ys))) true)))
  (induction ys)
  (case [nil]
    (intros w hg hga hp hk ha ho)
    (simp only [nat-fold])
    (cases ho)
    (case [inl z] (exact z))
    (case [inr z] (have z2 := (And.right z)) (simp [reach-mem] at z2)))
  (case [cons y t ih]
    (intros w hg hga hp hk ha ho)
    (have hs := (gd-sample w hg))
    (have g1 := (gd-fire-edge res w y hg))
    (have a1 := (ga-fire-edge res w y hga))
    (have aw1 := (hk-cs-fire-edge (not-idle-if-id (:creditor e0)) (hk-aw-inc (:creditor e0)) (hk-aw-dec (:creditor e0)) (hk-aw-setp (:creditor e0)) res w y ha))
    (simp only [nat-fold])
    (apply (ih (fire-edge res w y) g1 a1 hp hk aw1))
    (cases ho)
    (case [inl z]
      (exact (Or.inl (hk-cs-fire-edge (hk-rc (:creditor e0)) (hk-rc-inc (:creditor e0)) (hk-rc-dec (:creditor e0)) (hk-rc-setp (:creditor e0)) res w y z))))
    (case [inr z]
      (have m := (And.left z))
      (have r := (And.right z))
      (simp only [reach-mem-cons Bool.or_eq_true] at r)
      (cases hy (Nat.beq (:id e0) y))
      (case [true]
        (have ey := (Nat.eq_of_beq_eq_true hy))
        (have r1 := (hk-root-fire res w e0 hg hga m hp hk ha))
        (rw [ey] at r1)
        (exact (Or.inl r1)))
      (case [false]
        (have r2 (= (reach-mem (:id e0) t) true))
        (cases r)
        (case [inl q] (rw [hy] at q) (cases q))
        (case [inr q] (exact q))
        (have hc := (hk-dep-cred-has w e0 hs m hk))
        (exact (Or.inr (And.intro (hk-sv-fire-edge res w y e0 hs m hc hy) r2)))))))

;; ---- the written source's edges
(a/defn hk-ar [x :- Nat, d :- Nat, e :- EdgeRow] Bool
  (Bool.and (Bool.and (Nat.beq (:debtor e) x) (Nat.beq (:kind e) ek-dep)) (Bool.and (Nat.beq (:phase e) ph-armed) (Nat.beq (:creditor e) d))))
(a/theorem hk-armed-any [x :- Nat, d :- Nat, es :- (List EdgeRow)]
  (=> (= (reach-mem d (armed-creditors es x)) true) (= (tbl-any (hk-ar x d) es) true))
  (induction es)
  (case [nil] (intro hx) (simp [armed-creditors reach-mem] at hx))
  (case [cons h t ih]
    (intro hx)
    (cases hc (Bool.and (Bool.and (Nat.beq (:debtor h) x) (Nat.beq (:kind h) ek-dep)) (Nat.beq (:phase h) ph-armed)))
    (case [false] (simp only [armed-creditors hc] at hx) (simp only [tbl-any (ih hx) Bool.or_true]))
    (case [true]
      (simp only [armed-creditors hc reach-mem] at hx)
      (cases hd (Nat.beq d (:creditor h)))
      (case [false] (simp only [hd] at hx) (simp only [tbl-any (ih hx) Bool.or_true]))
      (case [true]
        (simp only [Bool.and_eq_true] at hc)
        (have hd2 (= (Nat.beq (:creditor h) d) true)) (rw [beq-comm]) (exact hd)
        (simp only [tbl-any hk-ar (And.left hc) (And.right hc) hd2 Bool.and_self Bool.true_or])))))
(a/theorem hk-onto-mem [x :- Nat, es :- (List EdgeRow), e :- EdgeRow]
  (=> (List.Mem e es) (= (Nat.beq (:debtor e) x) true) (= (Nat.beq (:kind e) ek-dep) true) (= (reach-mem (:id e) (edges-onto x es)) true))
  (induction es)
  (case [nil] (intros m h1 h2) (cases m))
  (case [cons h t ih]
    (intros m h1 h2)
    (cases m)
    (case [head] (simp only [edges-onto h1 h2 Bool.true_or Bool.and_self reach-mem Nat.beq_refl]))
    (case [tail m2]
      (have z := (ih m2 h1 h2))
      (cases hc (Bool.and (Nat.beq (:debtor h) x) (Bool.or (Nat.beq (:kind h) ek-dep) (Nat.beq (:kind h) ek-observe))))
      (case [false] (simp only [edges-onto hc]) (exact z))
      (case [true] (simp only [edges-onto hc]) (exact (hk-rm-cons (:id e) (:id h) _ z))))))
(a/defn hk-oq [i :- Nat, x :- Nat, e :- EdgeRow] Bool (Bool.and (Nat.beq (:id e) i) (Nat.beq (:debtor e) x)))
(a/theorem hk-onto-any [x :- Nat, i :- Nat, es :- (List EdgeRow)]
  (=> (= (reach-mem i (edges-onto x es)) true) (= (tbl-any (hk-oq i x) es) true))
  (induction es)
  (case [nil] (intro hx) (simp [edges-onto reach-mem] at hx))
  (case [cons h t ih]
    (intro hx)
    (cases hc (Bool.and (Nat.beq (:debtor h) x) (Bool.or (Nat.beq (:kind h) ek-dep) (Nat.beq (:kind h) ek-observe))))
    (case [false] (simp only [edges-onto hc] at hx) (simp only [tbl-any (ih hx) Bool.or_true]))
    (case [true]
      (simp only [edges-onto hc reach-mem] at hx)
      (cases hd (Nat.beq i (:id h)))
      (case [false] (simp only [hd] at hx) (simp only [tbl-any (ih hx) Bool.or_true]))
      (case [true]
        (simp only [Bool.and_eq_true] at hc)
        (have hd2 (= (Nat.beq (:id h) i) true)) (rw [beq-comm]) (exact hd)
        (simp only [tbl-any hk-oq (And.left hc) hd2 Bool.and_self Bool.true_or])))))
(a/defn hk-debx [x :- Nat, e :- EdgeRow] Bool (Nat.beq (:debtor e) x))
;; an edge whose debtor is no source x is not among the edges onto x
(a/theorem hk-not-onto [w :- World, x :- Nat, r :- EdgeRow]
  (=> (= (inv-sample w) true) (List.Mem r (:edges w)) (= (Nat.beq (:debtor r) x) false)
      (= (reach-mem (:id r) (edges-onto x (:edges w))) false))
  (intros hs m hd)
  (cases hi (reach-mem (:id r) (edges-onto x (:edges w))))
  (case [false] (rfl))
  (case [true]
    (have a := (hk-onto-any x (:id r) (:edges w) hi))
    (apply (any-elim EdgeRow (hk-oq (:id r) x) _ (:edges w) a))
    (intros e me he)
    (simp only [hk-oq Bool.and_eq_true] at he)
    (have u := (uniq-all EdgeRow edge-id (hk-debx x) e (:edges w) (l5-edge-nodup w hs) me (And.right he)))
    (have ur := (tbl-all-mem EdgeRow _ r (:edges w) u m))
    (have i2 (= (Nat.beq (edge-id r) (edge-id e)) true)) (rw [beq-comm]) (exact (And.left he))
    (simp only [same-id-then i2 Bool.not_true Bool.false_or hk-debx hd] at ur)
    (cases ur)))
;; ---- the mark targets keep their kind and debtor through the fires (edge keys backward)
(a/theorem hk-tg-ek [hxm :- (List Nat), S :- (List Nat), es0 :- (List EdgeRow), W1 :- World]
  (=> (= (nat-nodup (tbl-ids edge-id es0)) true) (= (hk-ek es0 (:edges W1)) true)
      (forall [d :- Nat] (=> (= (reach-mem d S) true) (= (tbl-has comp-id d (:comps W1)) true)))
      (= (tbl-all (hk-tg (List.append Nat S hxm) (mark-targets S es0) (:comps W1)) (:edges W1)) true))
  (intros hn hek hS)
  (simp only [hk-ek] at hek)
  (apply (all-of-mem EdgeRow _ (:edges W1)))
  (intros r mr)
  (cases ht (reach-mem (:id r) (mark-targets S es0)))
  (case [false] (simp only [hk-tg ht Bool.not_false Bool.true_or]))
  (case [true]
    (have a := (hk-mt-any S (:id r) es0 ht))
    (apply (any-elim EdgeRow (hk-tq S (:id r)) _ es0 a))
    (intros r0 m0 h0)
    (simp only [hk-tq Bool.and_eq_true] at h0)
    (have q0 (= (hk-dS S r0) true)) (simp only [hk-dS (And.left (And.right h0)) (And.right (And.right h0)) Bool.and_self])
    (have u := (uniq-all EdgeRow edge-id (hk-dS S) r0 es0 hn m0 q0))
    (have b := (tbl-all-mem EdgeRow (hk-back es0) r (:edges W1) hek mr))
    (simp only [hk-back] at b)
    (apply (any-elim EdgeRow (hk-kk r) _ es0 b))
    (intros r1 m1 k1)
    (simp only [hk-kk Bool.and_eq_true] at k1)
    (have e1 := (Nat.eq_of_beq_eq_true (And.left k1)))
    (have e2 := (Nat.eq_of_beq_eq_true (And.left (And.right k1))))
    (have e4 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right (And.right k1))))))
    (have e0 := (Nat.eq_of_beq_eq_true (And.left h0)))
    (have ur := (tbl-all-mem EdgeRow (same-id-then edge-id (edge-id r0) (hk-dS S)) r1 es0 u m1))
    (have i0 (= (Nat.beq (edge-id r1) (edge-id r0)) true))
    (show (= (Nat.beq (:id r1) (:id r0)) true)) (rw [e1]) (rw [e0]) (exact (Nat.beq_refl _))
    (simp only [same-id-then i0 Bool.not_true Bool.false_or hk-dS Bool.and_eq_true] at ur)
    (have kd (= (Nat.beq (:kind r) ek-dep) true)) (rw [← e2]) (exact (And.left ur))
    (have dS (= (reach-mem (:debtor r) S) true)) (rw [← e4]) (exact (And.right ur))
    (simp only [hk-tg ht Bool.not_true Bool.false_or])
    (exact (hk-e-intro (List.append Nat S hxm) (:comps W1) (edge-set-marked true r) kd (hS (:debtor r) dS)
             (Or.inl (rm-app-l (:debtor r) S hxm dS))))))

;; ---- the dirty set: computations, not the written source
(a/theorem hk-dirty-comp [w :- World, x :- Nat, d :- Nat]
  (=> (= (inv-sample w) true) (= (reach-mem d (dirty-set w x)) true) (= (tbl-has comp-id d (:comps w)) true))
  (intros hs hd)
  (have q := (hm-dirty-back w x d hd))
  (simp only [rinv-q Bool.or_eq_true] at q)
  (cases q)
  (case [inl z]
    (have a := (hk-armed-any x d (:edges w) z))
    (apply (any-elim EdgeRow (hk-ar x d) _ (:edges w) a))
    (intros e me he)
    (simp only [hk-ar Bool.and_eq_true] at he)
    (have c := (hk-dep-cred-has w e hs me (And.right (And.left he))))
    (have ec := (Nat.eq_of_beq_eq_true (And.right (And.right he))))
    (rw [ec] at c) (exact c))
  (case [inr z]
    (apply (any-elim Nat (rinv-par (dep-creditors (:edges w)) d) _ _ z))
    (intros m mm hp)
    (simp only [rinv-par] at hp)
    (have a := (hk-dc-any d m (:edges w) hp))
    (apply (any-elim EdgeRow (hk-dcr d m) _ (:edges w) a))
    (intros e me he)
    (simp only [hk-dcr Bool.and_eq_true] at he)
    (have c := (hk-dep-cred-has w e hs me (And.left he)))
    (have ec := (Nat.eq_of_beq_eq_true (And.left (And.right he))))
    (rw [ec] at c) (exact c)))
(a/theorem hk-dirty-nx [w :- World, x :- Nat, s :- SourceRow, d :- Nat]
  (=> (= (inv-sample w) true) (= (source-find w x) (Option.some SourceRow s)) (= (reach-mem d (dirty-set w x)) true) (= (Nat.beq d x) false))
  (intros hs hf hd)
  (have c := (hk-dirty-comp w x d hs hd))
  (have nx := (hk-src-not-comp w x hs (tbl-find-has SourceRow source-id x s (:sources w) hf)))
  (cases he (Nat.beq d x))
  (case [false] (rfl))
  (case [true] (have e := (Nat.eq_of_beq_eq_true he)) (rw [e] at c) (rw [c] at nx) (cases nx)))
;; ---- every dirty computation is waiting after the write
(a/theorem hk-write-wif [w :- World, x :- Nat, v :- Nat, s :- SourceRow, d :- Nat]
  (=> (= (source-find w x) (Option.some SourceRow s)) (= (gd w) true) (= (g7 w) true) (= (ga w) true)
      (= (reach-mem d (dirty-set w x)) true)
      (= (tbl-all (hk-wif d) (:comps (write-raw w x v))) true))
  (intros hf hg h7 hga hd)
  (have hs := (gd-sample w hg))
  (have g0 := (gd-source-upd w x (source-write v) (source-write-source-id v) hg))
  (have a0 := (ga-source-upd w x (source-write v) (source-write-source-id v) hga))
  (have s0 := (inv-source-upd w x (source-write v) (source-write-source-id v) hs))
  (have s1 := (nat-fold-inv (fire-edge (RunResult.mk res-ok v)) (inv-fire-edge (RunResult.mk res-ok v)) (edges-onto x (:edges w)) _ s0))
  (simp only [write-raw])
  (have q := (hm-dirty-back w x d hd))
  (simp only [rinv-q Bool.or_eq_true] at q)
  (cases q)
  (case [inl z]
    (have a := (hk-armed-any x d (:edges w) z))
    (apply (any-elim EdgeRow (hk-ar x d) _ (:edges w) a))
    (intros e0 me he)
    (simp only [hk-ar Bool.and_eq_true] at he)
    (have ec := (Nat.eq_of_beq_eq_true (And.right (And.right he))))
    (have aw := (cred-awake-mem w e0 hs (g7-rest-of w h7) me))
    (simp only [cred-awake] at aw)
    (have aw0 (= (awake (:comps (source-upd w x (source-write v))) (:creditor e0)) true)) (exact aw)
    (have me0 (List.Mem e0 (:edges (source-upd w x (source-write v))))) (exact me)
    (have on := (hk-onto-mem x (:edges w) e0 me (And.left (And.left he)) (And.right (And.left he))))
    (have rf := (hk-root-fold (RunResult.mk res-ok v) e0 (edges-onto x (:edges w)) (source-upd w x (source-write v)) g0 a0
                  (And.left (And.right he)) (And.right (And.left he)) aw0 (Or.inr (And.intro me0 on))))
    (have rc := (hk-fold-mark-q (fn [q :- World] (tbl-all (hk-rc (:creditor e0)) (:comps q)))
                  (fn [w2 :- World, y :- Nat, a1 :- (= (inv-sample w2) true), a2 :- (= (tbl-all (hk-rc (:creditor e0)) (:comps w2)) true)]
                    (hk-cs-mark (hk-rc (:creditor e0)) (fn [q :- CompRow, hq :- (= (hk-rc (:creditor e0) q) true)] hq) w2 y a2))
                  (mark-targets (dirty-set w x) (:edges w)) _ s1 rf))
    (have r2 := (hk-wif-rc (:creditor e0) _ rc))
    (rw [ec] at r2) (exact r2))
  (case [inr z]
    (apply (any-elim Nat (rinv-par (dep-creditors (:edges w)) d) _ _ z))
    (intros m mm hp)
    (simp only [rinv-par] at hp)
    (have a := (hk-dc-any d m (:edges w) hp))
    (apply (any-elim EdgeRow (hk-dcr d m) _ (:edges w) a))
    (intros r mr hr)
    (simp only [hk-dcr Bool.and_eq_true] at hr)
    (have ec := (Nat.eq_of_beq_eq_true (And.left (And.right hr))))
    (have em := (Nat.eq_of_beq_eq_true (And.right (And.right hr))))
    (have mS (= (reach-mem m (dirty-set w x)) true)) (exact (Iff.mpr (reach-mem-iff m _) mm))
    (have dS (= (reach-mem (:debtor r) (dirty-set w x)) true)) (rw [em]) (exact mS)
    (have tm := (hk-tgt-mem (dirty-set w x) (:edges w) r mr (And.left hr) dS))
    (have nx := (hk-dirty-nx w x s (:debtor r) hs hf dS))
    (have no := (hk-not-onto w x r hs mr nx))
    (have hc := (hk-dep-cred-has w r hs mr (And.left hr)))
    (have sv := (hk-sv-fold (RunResult.mk res-ok v) r (edges-onto x (:edges w)) (source-upd w x (source-write v)) s0 mr hc no))
    (have ck (= (hk-ck d (mark-targets (dirty-set w x) (:edges w)) r) true)) (simp only [hk-ck (And.left (And.right hr)) tm Bool.and_self])
    (have k1 := (any-elim-of EdgeRow _ r _ sv ck))
    (have aw := (cred-awake-mem w r hs (g7-rest-of w h7) mr))
    (simp only [cred-awake awake] at aw) (rw [ec] at aw)
    (have aw1 := (hk-cs-fold (not-idle-if-id d) (hk-aw-inc d) (hk-aw-dec d) (hk-aw-setp d) (RunResult.mk res-ok v) (edges-onto x (:edges w))
                   (source-upd w x (source-write v)) aw))
    (have aw2 (= (awake (:comps (nat-fold (fire-edge (RunResult.mk res-ok v)) (source-upd w x (source-write v)) (edges-onto x (:edges w)))) d) true))
    (simp only [awake]) (exact aw1)
    (exact (hk-fold-wif _ _ d s1 aw2 k1))))

(a/theorem hmk-write-raw-x [hxm :- (List Nat), w :- World, x :- Nat, v :- Nat, s :- SourceRow]
  (=> (= (source-find w x) (Option.some SourceRow s)) (= (gd w) true) (= (g7 w) true) (= (ga w) true) (= (hmk hxm w) true)
      (= (hmk hxm (write-raw w x v)) true))
  (intros hf hg h7 hga h)
  (have hs := (gd-sample w hg))
  (have h0 := (hmk-source-upd hxm w x (source-write v) (source-write-source-id v) h))
  (have h1 := (nat-fold-hmk hxm (fire-edge (RunResult.mk res-ok v)) (hmk-fire-edge hxm (RunResult.mk res-ok v)) (edges-onto x (:edges w)) _ h0))
  (have s1 := (hmk-sample hxm _ h1))
  (have hx1 := (hmk-intro (List.append Nat (dirty-set w x) hxm) _ s1
                 (hmk-rest-xm hxm _ _ (fn [d :- Nat, hd :- (= (reach-mem d hxm) true)] (rm-app-r d (dirty-set w x) hxm hd)) (hmk-rest-of hxm _ h1))))
  (have ek1 := (ek-nat-fold (fire-edge (RunResult.mk res-ok v)) (fn [w1 :- World, y :- Nat] (ek-fire-edge (RunResult.mk res-ok v) w1 y))
                 (edges-onto x (:edges w)) (source-upd w x (source-write v))))
  (have ek2 (= (hk-ek (:edges w) (:edges (nat-fold (fire-edge (RunResult.mk res-ok v)) (source-upd w x (source-write v)) (edges-onto x (:edges w))))) true))
  (exact ek1)
  (have hS (forall [d :- Nat] (=> (= (reach-mem d (dirty-set w x)) true)
                                  (= (tbl-has comp-id d (:comps (nat-fold (fire-edge (RunResult.mk res-ok v)) (source-upd w x (source-write v)) (edges-onto x (:edges w))))) true))))
  (intros d hd)
  (rw [hk-fold-fire-has]) (exact (hk-dirty-comp w x d hs hd))
  (have tg1 := (hk-tg-ek hxm (dirty-set w x) (:edges w) _ (l5-edge-nodup w hs) ek2 hS))
  (have h2 := (hmk-fold-mark-x (List.append Nat (dirty-set w x) hxm) (mark-targets (dirty-set w x) (:edges w)) (mark-targets (dirty-set w x) (:edges w))
                _ (hk-all-self _) tg1 hx1))
  (have h2b (= (hmk (List.append Nat (dirty-set w x) hxm) (write-raw w x v)) true)) (simp only [write-raw]) (exact h2)
  (apply (hmk-discharge hxm (dirty-set w x) (write-raw w x v) h2b))
  (intros d hd hh)
  (exact (hk-write-wif w x v s d hf hg h7 hga hd)))
(swap! (:renames HMK) assoc 'inv-write-raw 'hmk-write-raw-x)
(override! HMK 't2-inv '[]
  '(a/theorem t2-hmk [hxm :- (List Nat), w :- World, x :- Nat, v :- Nat]
     (=> (= (gd w) true) (= (g7 w) true) (= (ga w) true) (= (hmk hxm w) true) (= (hmk hxm (:world (t2-write w x v))) true))
     (intros hg h7 hga h)
     (cases hs (source-find w x)) (case' [some s]) (case' [none])
     (simp only [t2-write hs refuse]) (exact h)
     (cases hw (writable s))
     (simp only [t2-write hs hw refuse]) (exact h)
     (simp only [t2-write hs hw accept]) (exact (hmk-write-raw-x hxm w x v s hs hg h7 hga h))))
(lcopy! HMK 't2-inv)

;; ===========================================================================
;; Part E. T12 complete + settle
;; ===========================================================================

;; ---- discharge: an exempt id leaves the list when it stays listed, is waiting, or has no marked in-edge
(a/defn hk-nmd [d :- Nat, e :- EdgeRow] Bool (Bool.or (Bool.not (:marked e)) (Bool.not (Nat.beq (:debtor e) d))))
(a/theorem hmk-dis [hxm :- (List Nat), S :- (List Nat), L :- (List Nat), w :- World]
  (=> (= (hmk (List.append Nat S hxm) w) true)
      (forall [d :- Nat] (=> (= (reach-mem d S) true)
                             (Or (= (reach-mem d L) true) (Or (= (tbl-all (hk-wif d) (:comps w)) true) (= (tbl-all (hk-nmd d) (:edges w)) true)))))
      (forall [d :- Nat] (=> (= (reach-mem d hxm) true) (= (reach-mem d L) true)))
      (= (hmk L w) true))
  (intros h hd hx)
  (have r := (hmk-rest-of _ w h)) (simp only [hmk-rest] at r)
  (have r2 (= (hmk-rest L w) true))
  (simp only [hmk-rest])
  (apply (all-of-mem EdgeRow _ (:edges w)))
  (intros e me)
  (have he := (tbl-all-mem EdgeRow _ e (:edges w) r me))
  (cases hm (:marked e))
  (case [false] (exact (hk-e-unm L _ e hm)))
  (case [true]
    (have p := (hk-e-marked _ (:comps w) e he hm))
    (apply (hk-e-intro L _ e (And.left p) (And.left (And.right p))))
    (have q := (And.right (And.right p)))
    (cases q)
    (case [inr z] (exact (Or.inr z)))
    (case [inl z]
      (rw [reach-mem-append] at z) (simp only [Bool.or_eq_true] at z)
      (cases z)
      (case [inr z1] (exact (Or.inl (hx (:debtor e) z1))))
      (case [inl z1]
        (have o := (hd (:debtor e) z1))
        (cases o)
        (case [inl o1] (exact (Or.inl o1)))
        (case [inr o1]
          (cases o1)
          (case [inl o2] (exact (Or.inr o2)))
          (case [inr o2]
            (have n := (tbl-all-mem EdgeRow _ e (:edges w) o2 me))
            (simp only [hk-nmd hm Nat.beq_refl Bool.not_true Bool.false_or] at n)
            (cases n))))))
  (exact (hmk-intro L w (hmk-sample _ w h) r2)))

;; ---- scans
(a/theorem hk-scan-mem [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), r :- A, xs :- (List A)]
  (=> (List.Mem r xs) (= (p r) true) (= (reach-mem (idf r) (tbl-scan idf p xs)) true))
  (induction xs)
  (case [nil] (intros m h) (cases m))
  (case [cons h t ih]
    (intros m hp)
    (cases m)
    (case [head] (simp only [tbl-scan hp reach-mem Nat.beq_refl]))
    (case [tail m2]
      (have z := (ih m2 hp))
      (cases hc (p h))
      (case [false] (simp only [tbl-scan hc]) (exact z))
      (case [true] (simp only [tbl-scan hc]) (exact (hk-rm-cons (idf r) (idf h) _ z))))))
(a/defn hk-sq [A :- Type :implicit, idf :- (=> A Nat), p :- (=> A Bool), y :- Nat, r :- A] Bool (Bool.and (Nat.beq (idf r) y) (p r)))
(a/theorem hk-scan-any [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), y :- Nat, xs :- (List A)]
  (=> (= (reach-mem y (tbl-scan idf p xs)) true) (= (tbl-any (hk-sq idf p y) xs) true))
  (induction xs)
  (case [nil] (intro hx) (simp [tbl-scan reach-mem] at hx))
  (case [cons h t ih]
    (intro hx)
    (cases hc (p h))
    (case [false] (simp only [tbl-scan hc] at hx) (simp only [tbl-any (ih hx) Bool.or_true]))
    (case [true]
      (simp only [tbl-scan hc reach-mem] at hx)
      (cases hd (Nat.beq y (idf h)))
      (case [false] (simp only [hd] at hx) (simp only [tbl-any (ih hx) Bool.or_true]))
      (case [true]
        (have hd2 (= (Nat.beq (idf h) y) true)) (rw [beq-comm]) (exact hd)
        (simp only [tbl-any hk-sq hd2 hc Bool.and_self Bool.true_or])))))
(a/theorem hk-rm-filter [q :- (=> Nat Bool), y :- Nat, xs :- (List Nat)]
  (=> (= (reach-mem y xs) true) (= (q y) true) (= (reach-mem y (tbl-filter q xs)) true))
  (induction xs)
  (case [nil] (intros h hq) (simp [reach-mem] at h))
  (case [cons h t ih]
    (intros hm hq)
    (simp only [reach-mem-cons Bool.or_eq_true] at hm)
    (cases hc (q h))
    (case [false]
      (simp only [tbl-filter hc])
      (cases hm)
      (case [inl z] (have e := (Nat.eq_of_beq_eq_true z)) (rw [e] at hq) (rw [hq] at hc) (cases hc))
      (case [inr z] (exact (ih z hq))))
    (case [true]
      (simp only [tbl-filter hc reach-mem-cons Bool.or_eq_true])
      (cases hm)
      (case [inl z] (exact (Or.inl z)))
      (case [inr z] (exact (Or.inr (ih z hq)))))))

;; ---- the comps frame through a settle (fires and unmarks)
(a/theorem hk-cs-unmark [R :- (=> CompRow Bool), h2 :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-dec-pending c)) true))),
                         w :- World, x :- Nat]
  (=> (= (tbl-all R (:comps w)) true) (= (tbl-all R (:comps (unmark-edge w x))) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true] (simp only [unmark-edge hf hm comp-upd edge-upd set-edges set-comps]) (exact (hk-cs-upd R comp-dec-pending h2 (:creditor e) (:comps w) h)))))
(a/theorem hk-cs-settle-edge [R :- (=> CompRow Bool),
                              h1 :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-inc-epoch c)) true))),
                              h2 :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-dec-pending c)) true))),
                              h3 :- (forall [c :- CompRow, n :- Nat] (=> (= (R c) true) (= (R (comp-set-pending n c)) true))),
                              ch :- Bool, ver :- Nat, w :- World, x :- Nat]
  (=> (= (tbl-all R (:comps w)) true) (= (tbl-all R (:comps (settle-edge ch ver w x))) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [settle-edge hf]) (exact h))
  (case [some e]
    (have se := (settle-edge-eq ch ver w x e hf)) (simp only [se])
    (apply (hk-cs-unmark R h2 (settle-fire ver w e) x))
    (cases hp (Nat.beq (:phase e) ph-armed))
    (case [false] (simp only [settle-fire hp]) (exact h))
    (case [true]
      (cases hc (Bool.or (edge-behind ver e) (member-current w e)))
      (case [false] (simp only [settle-fire hp hc]) (exact h))
      (case [true] (simp only [settle-fire hp hc]) (exact (hk-cs-fire-dep R h1 h2 h3 w e h))))))
(a/theorem hk-cs-settle-one [R :- (=> CompRow Bool),
                             h1 :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-inc-epoch c)) true))),
                             h2 :- (forall [c :- CompRow] (=> (= (R c) true) (= (R (comp-dec-pending c)) true))),
                             h3 :- (forall [c :- CompRow, n :- Nat] (=> (= (R c) true) (= (R (comp-set-pending n c)) true))),
                             w :- World, d :- Nat, ch :- Bool]
  (=> (= (tbl-all R (:comps w)) true) (= (tbl-all R (:comps (settle-one w d ch))) true))
  (intro h)
  (have f1 (forall [xs :- (List Nat), w1 :- World] (=> (= (tbl-all R (:comps w1)) true) (= (tbl-all R (:comps (nat-fold (settle-edge ch (deb-version w d)) w1 xs))) true))))
  (intro xs)
  (induction xs)
  (case [nil] (intros w1 h0) (simp only [nat-fold]) (exact h0))
  (case [cons y t ih] (intros w1 h0) (simp only [nat-fold]) (exact (ih _ (hk-cs-settle-edge R h1 h2 h3 ch (deb-version w d) w1 y h0))))
  (simp only [settle-one settle-host])
  (exact (hk-cs-fold R h1 h2 h3 _ _ _ (f1 _ w h))))

;; ---- a computation that is not settle-ready is waiting (gd: a live one is ready)
(a/theorem hk-wt-nready [w :- World, c :- CompRow]
  (=> (= (gd w) true) (List.Mem c (:comps w)) (= (:idle c) false) (= (settle-ready w c) false) (= (hk-wt c) true))
  (intros hg mc hi hr)
  (have p := (gdk-parts _ _ _ (gd-rest-of w hg)))
  (have qa := (And.right p)) (rw [all-gdkeys] at qa)
  (have pc := (gd-c-parts _ _ _ (tbl-all-mem CompRow (fn [x :- CompRow] (gd-c (:runs w) (:next-id w) (gdkey x))) c (:comps w) qa mc)))
  (have dl := (And.left pc)) (simp only [gd-dle gdkey Bool.and_eq_true] at dl)
  (have l1 := (gd-le-of _ _ (And.left dl)))
  (cases hl (comp-live c))
  (case [false]
    (cases hde (Nat.beq (:done-epoch c) (:epoch c)))
    (case [false]
      (have ne := (Nat.ne_of_beq_eq_false hde))
      (have lt (= (Nat.blt (:done-epoch c) (:epoch c)) true)) (apply gd-blt-of) (omega)
      (simp only [hk-wt hi lt Bool.not_false Bool.true_or Bool.and_self]))
    (case [true]
      (cases hp0 (Nat.beq (:pending c) 0))
      (case [false] (simp only [hk-wt hi hp0 Bool.not_false Bool.or_true Bool.and_self]))
      (case [true] (simp only [comp-live hi hde hp0 Bool.not_false Bool.and_self] at hl) (cases hl))))
  (case [true]
    (simp only [settle-ready hl Bool.true_and] at hr)
    (have hrb := (bnot-false _ hr))
    (simp only [Bool.and_eq_true] at hrb)
    (have hr1 := (And.left hrb))
    (have hr2 := (And.right hrb))
    (simp only [comp-live Bool.and_eq_true] at hl)
    (have de := (And.left (And.right hl)))
    (cases hq (run-find w (:run c)))
    (case [none] (simp only [run-busy hq] at hr2) (cases hr2))
    (case [some q]
      (simp only [run-busy hq] at hr2)
      (simp only [run-current-of-comp hq] at hr1)
      (have mq := (tbl-find-mem RunRow run-id (:run c) q (:runs w) hq))
      (have iq (= (:id q) (:run c))) (exact (tbl-find-id RunRow run-id (:run c) q (:runs w) hq))
      (have rof := (tbl-all-mem RunRow _ q (:runs w) (And.left (And.right (And.right pc))) mq))
      (have iq2 (= (Nat.beq (:id q) (:run c)) true)) (rw [iq]) (exact (Nat.beq_refl _))
      (simp only [gd-rof gdkey iq2 Bool.not_true Bool.false_or] at rof)
      (have cd := (And.right (And.right (And.right pc))))
      (simp only [gd-cde gdkey de Bool.not_true Bool.false_or] at cd)
      (have nq := (tbl-all-mem RunRow _ q (:runs w) cd mq))
      (simp only [gd-ncur gdkey rof hr1 hr2 Bool.and_self Bool.not_true] at nq)
      (cases nq))))
(a/theorem hk-wif-same [w :- World, c :- CompRow, d :- Nat]
  (=> (= (inv-sample w) true) (List.Mem c (:comps w)) (= (:id c) d) (= (hk-wt c) true) (= (tbl-all (hk-wif d) (:comps w)) true))
  (intros hs mc ic h)
  (have u := (gd-same-id w c hk-wt hs mc h))
  (apply (tbl-all-mono CompRow _ (hk-wif d) _ (:comps w) u))
  (intros r hr)
  (cases hx (Nat.beq (:id r) d))
  (case [false] (simp only [hk-wif hx Bool.not_false Bool.true_or]))
  (case [true]
    (have hx2 (= (Nat.beq (comp-id r) (:id c)) true)) (rw [ic]) (exact hx)
    (simp only [same-id-then hx2 Bool.not_true Bool.false_or] at hr)
    (simp only [hk-wif hx hr Bool.not_true Bool.false_or])))
(a/theorem hk-wif-none [w :- World, d :- Nat]
  (=> (= (comp-find w d) (Option.none CompRow)) (= (tbl-all (hk-wif d) (:comps w)) true))
  (intro hf)
  (have z := (tbl-find-none-has CompRow comp-id d (:comps w) hf))
  (apply (all-of-mem CompRow _ (:comps w)))
  (intros r mr)
  (cases hx (Nat.beq (:id r) d))
  (case [false] (simp only [hk-wif hx Bool.not_false Bool.true_or]))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true hx))
    (have z2 := (has-of-mem CompRow comp-id r (:comps w) mr))
    (have e2 (= (comp-id r) d)) (exact e)
    (rw [e2] at z2) (rw [z2] at z) (cases z)))
;; not ready, awake: waiting
(a/theorem hk-wif-nready [w :- World, d :- Nat]
  (=> (= (gd w) true) (= (awake (:comps w) d) true) (= (ready-id w d) false) (= (tbl-all (hk-wif d) (:comps w)) true))
  (intros hg ha hr)
  (cases hf (comp-find w d))
  (case [none] (exact (hk-wif-none w d hf)))
  (case [some c]
    (simp only [ready-id hf opt-test] at hr)
    (have mc := (tbl-find-mem CompRow comp-id d c (:comps w) hf))
    (have ic (= (:id c) d)) (exact (tbl-find-id CompRow comp-id d c (:comps w) hf))
    (have aw := (tbl-all-mem CompRow (not-idle-if-id d) c (:comps w) ha mc))
    (have ic2 (= (Nat.beq (:id c) d) true)) (rw [ic]) (exact (Nat.beq_refl d))
    (simp only [not-idle-if-id ic2 Bool.not_true Bool.false_or] at aw)
    (have hi := (bnot-true _ aw))
    (exact (hk-wif-same w c d (gd-sample w hg) mc ic (hk-wt-nready w c hg mc hi hr)))))
(a/theorem rm-app-cons [y :- Nat, d :- Nat, S :- (List Nat), L :- (List Nat)]
  (=> (= (reach-mem y (List.cons Nat d L)) true) (= (reach-mem y (List.append Nat (List.cons Nat d S) L)) true))
  (intro hy)
  (show (= (reach-mem y (List.cons Nat d (List.append Nat S L))) true))
  (simp only [reach-mem-cons Bool.or_eq_true] at hy)
  (simp only [reach-mem-cons Bool.or_eq_true])
  (cases hy)
  (case [inl z] (exact (Or.inl z)))
  (case [inr z] (exact (Or.inr (rm-app-r y S L z)))))
;; ---- one settle: the settled debtor's out-edges are unmarked; their creditors are exempt until they
;; are queued (ready) or found waiting
(a/defn hk-xin [d :- Nat, es :- (List EdgeRow), x :- Nat] Bool (tbl-any (hk-sq edge-id (out-dep d) x) es))
(a/theorem hk-scan-xin [d :- Nat, es :- (List EdgeRow)] (= (tbl-all (hk-xin d es) (tbl-scan edge-id (out-dep d) es)) true)
  (apply (all-of-mem Nat _ (tbl-scan edge-id (out-dep d) es)))
  (intros y my)
  (simp only [hk-xin])
  (exact (hk-scan-any EdgeRow edge-id (out-dep d) y es (Iff.mpr (reach-mem-iff y _) my))))
(a/theorem hk-unm-safe [L :- (List Nat), W :- World, Wk :- World, x :- Nat, d :- Nat, e :- EdgeRow]
  (=> (= (nat-nodup (tbl-ids edge-id (:edges W))) true) (= (hk-ek (:edges W) (:edges Wk)) true) (= (hk-xin d (:edges W) x) true)
      (= (edge-find Wk x) (Option.some EdgeRow e)) (= (:marked e) true)
      (= (hk-safe (List.append Nat (List.cons Nat d (tbl-scan edge-cred (out-marked d) (:edges W))) L) (:comps Wk) (:creditor e)) true))
  (intros hn hek hx hf hm)
  (have me := (tbl-find-mem EdgeRow edge-id x e (:edges Wk) hf))
  (have ie (= (:id e) x)) (exact (tbl-find-id EdgeRow edge-id x e (:edges Wk) hf))
  (simp only [hk-ek] at hek)
  (have b := (tbl-all-mem EdgeRow (hk-back (:edges W)) e (:edges Wk) hek me))
  (simp only [hk-back] at b)
  (apply (any-elim EdgeRow (hk-kk e) _ (:edges W) b))
  (intros e1 m1 k1)
  (simp only [hk-kk hm Bool.not_true Bool.false_or Bool.and_eq_true] at k1)
  (have i1 := (Nat.eq_of_beq_eq_true (And.left k1)))
  (have c1 := (Nat.eq_of_beq_eq_true (And.left (And.right (And.right k1)))))
  (have mk1 := (And.right (And.right (And.right (And.right k1)))))
  (simp only [hk-xin] at hx)
  (apply (any-elim EdgeRow (hk-sq edge-id (out-dep d) x) _ (:edges W) hx))
  (intros e2 m2 h2)
  (simp only [hk-sq Bool.and_eq_true] at h2)
  (have u := (uniq-all EdgeRow edge-id (out-dep d) e2 (:edges W) hn m2 (And.right h2)))
  (have ur := (tbl-all-mem EdgeRow _ e1 (:edges W) u m1))
  (have i2 (= (:id e2) x)) (exact (Nat.eq_of_beq_eq_true (And.left h2)))
  (have i3 (= (Nat.beq (edge-id e1) (edge-id e2)) true))
  (show (= (Nat.beq (:id e1) (:id e2)) true)) (rw [i1]) (rw [ie]) (rw [i2]) (exact (Nat.beq_refl _))
  (simp only [same-id-then i3 Bool.not_true Bool.false_or] at ur)
  (have om (= (out-marked d e1) true)) (simp only [out-marked ur mk1 Bool.and_self])
  (have sc := (hk-scan-mem EdgeRow edge-cred (out-marked d) e1 (:edges W) m1 om))
  (have sc2 (= (reach-mem (:creditor e) (tbl-scan edge-cred (out-marked d) (:edges W))) true)) (rw [← c1]) (exact sc)
  (simp only [hk-safe (rm-app-l (:creditor e) _ L (hk-rm-cons (:creditor e) d _ sc2)) Bool.true_or]))
(a/theorem hmk-settle-fire [hxm :- (List Nat), ver :- Nat, w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e)) (= (hmk hxm w) true) (= (hmk hxm (settle-fire ver w e)) true))
  (intros hf h)
  (cases hp (Nat.beq (:phase e) ph-armed))
  (case [false] (simp only [settle-fire hp]) (exact h))
  (case [true]
    (cases hc (Bool.or (edge-behind ver e) (member-current w e)))
    (case [false] (simp only [settle-fire hp hc]) (exact h))
    (case [true] (simp only [settle-fire hp hc]) (exact (hmk-fire-dep hxm w e hf h)))))
(a/theorem hk-se-fold [ch :- Bool, ver :- Nat, d :- Nat, L :- (List Nat), W :- World, xs :- (List Nat)]
  (forall [Wk :- World]
    (=> (= (inv-sample Wk) true) (= (nat-nodup (tbl-ids edge-id (:edges W))) true) (= (hk-ek (:edges W) (:edges Wk)) true)
        (= (tbl-all (hk-xin d (:edges W)) xs) true)
        (= (hmk (List.append Nat (List.cons Nat d (tbl-scan edge-cred (out-marked d) (:edges W))) L) Wk) true)
        (= (hmk (List.append Nat (List.cons Nat d (tbl-scan edge-cred (out-marked d) (:edges W))) L) (nat-fold (settle-edge ch ver) Wk xs)) true)))
  (induction xs)
  (case [nil] (intros Wk hs hn hek hx h) (simp only [nat-fold]) (exact h))
  (case [cons y t ih]
    (intros Wk hs hn hek hx h)
    (simp only [tbl-all Bool.and_eq_true] at hx)
    (have ek2 := (hk-ek-trans _ _ _ hek (ek-settle-edge ch ver Wk y)))
    (have h3 (= (hmk (List.append Nat (List.cons Nat d (tbl-scan edge-cred (out-marked d) (:edges W))) L) (settle-edge ch ver Wk y)) true))
    (cases hf (edge-find Wk y))
    (case [none] (simp only [settle-edge hf]) (exact h))
    (case [some e0]
      (have se := (settle-edge-eq ch ver Wk y e0 hf)) (simp only [se])
      (have ie (= (:id e0) y)) (exact (tbl-find-id EdgeRow edge-id y e0 (:edges Wk) hf))
      (have hf2 (= (edge-find Wk (:id e0)) (Option.some EdgeRow e0))) (rw [ie]) (exact hf)
      (have h1 := (hmk-settle-fire _ ver Wk e0 hf2 h))
      (have ek1 := (hk-ek-trans _ _ _ hek (ek-settle-fire ver Wk e0)))
      (apply (hmk-unmark-edge _ (settle-fire ver Wk e0) y _ h1))
      (intros e hf3 hm)
      (exact (hk-unm-safe L W (settle-fire ver Wk e0) y d e hn ek1 (And.left hx) hf3 hm)))
    (simp only [nat-fold])
    (exact (ih (settle-edge ch ver Wk y) (inv-settle-edge ch ver Wk y hs) hn ek2 (And.right hx) h3))))
(a/theorem hk-nmd-of-sd [hxm :- (List Nat), w :- World, d :- Nat]
  (=> (= (hmk hxm w) true) (= (tbl-all (sd-row d (List.nil Nat)) (:edges w)) true) (= (tbl-all (hk-nmd d) (:edges w)) true))
  (intros h hsd)
  (have r := (hmk-rest-of _ w h)) (simp only [hmk-rest] at r)
  (apply (all-of-mem EdgeRow _ (:edges w)))
  (intros e me)
  (cases hm (:marked e))
  (case [false] (simp only [hk-nmd hm Bool.not_false Bool.true_or]))
  (case [true]
    (have p := (hk-e-marked _ (:comps w) e (tbl-all-mem EdgeRow _ e (:edges w) r me) hm))
    (have s := (tbl-all-mem EdgeRow _ e (:edges w) hsd me))
    (cases hd (Nat.beq (:debtor e) d))
    (case [false] (simp only [hk-nmd hd Bool.not_false Bool.or_true]))
    (case [true] (simp only [sd-row out-marked out-dep (And.left p) hd hm reach-mem Bool.and_self Bool.not_true Bool.or_false] at s) (cases s))))
(a/theorem hk-settle-step [L :- (List Nat), W :- World, d :- Nat, ch :- Bool]
  (=> (= (gd W) true) (= (g7 W) true) (= (hmk (List.cons Nat d L) W) true)
      (= (hmk (List.append Nat (settle-next W (settle-one W d ch) d) L) (settle-one W d ch)) true))
  (intros hg h7 h)
  (have hs := (gd-sample W hg))
  (have hn := (l5-edge-nodup W hs))
  (have h0 := (hmk-intro (List.append Nat (List.cons Nat d (tbl-scan edge-cred (out-marked d) (:edges W))) L) W hs
                (hmk-rest-xm _ _ W (fn [y :- Nat, hy :- (= (reach-mem y (List.cons Nat d L)) true)]
                                     (rm-app-cons y d (tbl-scan edge-cred (out-marked d) (:edges W)) L hy)) (hmk-rest-of _ W h))))
  (have hf := (hk-se-fold ch (deb-version W d) d L W (tbl-scan edge-id (out-dep d) (:edges W)) W hs hn (hk-ek-refl _) (hk-scan-xin d (:edges W)) h0))
  (have h2 (= (hmk (List.append Nat (List.cons Nat d (tbl-scan edge-cred (out-marked d) (:edges W))) L) (settle-one W d ch)) true))
  (simp only [settle-one settle-host])
  (exact (nat-fold-hmk _ _ (hmk-fire-edge _ _) _ _ hf))
  (have s1 := (sd-fold ch (deb-version W d) d (tbl-scan edge-id (out-dep d) (:edges W)) W hs (sd-init d (:edges W))))
  (have n2 := (nm-settle-host (nat-fold (settle-edge ch (deb-version W d)) W (tbl-scan edge-id (out-dep d) (:edges W))) d))
  (simp only [es-nm] at n2)
  (have s2 := ((And.left (n2 d (List.nil Nat))) s1))
  (have s3 (= (tbl-all (sd-row d (List.nil Nat)) (:edges (settle-one W d ch))) true)) (simp only [settle-one]) (exact s2)
  (have nm := (hk-nmd-of-sd _ _ d h2 s3))
  (have g2 := (gd-settle-one W d ch hg))
  (apply (hmk-dis L (List.cons Nat d (tbl-scan edge-cred (out-marked d) (:edges W))) _ _ h2))
  (intros y hy)
  (simp only [reach-mem-cons Bool.or_eq_true] at hy)
  (cases hy)
  (case [inl z] (have e := (Nat.eq_of_beq_eq_true z)) (rw [e]) (exact (Or.inr (Or.inr nm))))
  (case [inr z]
    (cases hr (ready-id (settle-one W d ch) y))
    (case [true]
      (have f := (hk-rm-filter (ready-id (settle-one W d ch)) y _ z hr))
      (exact (Or.inl (rm-app-l y _ L f))))
    (case [false]
      (have a := (hk-scan-any EdgeRow edge-cred (out-marked d) y (:edges W) z))
      (apply (any-elim EdgeRow (hk-sq edge-cred (out-marked d) y) _ (:edges W) a))
      (intros e me he)
      (simp only [hk-sq out-marked out-dep Bool.and_eq_true] at he)
      (have ec := (Nat.eq_of_beq_eq_true (And.left he)))
      (have aw := (cred-awake-mem W e hs (g7-rest-of W h7) me))
      (simp only [cred-awake awake] at aw)
      (have ec2 (= (:creditor e) y)) (exact ec)
      (rw [ec2] at aw)
      (have aw1 := (hk-cs-settle-one (not-idle-if-id y) (hk-aw-inc y) (hk-aw-dec y) (hk-aw-setp y) W d ch aw))
      (have aw2 (= (awake (:comps (settle-one W d ch)) y) true)) (simp only [awake]) (exact aw1)
      (exact (Or.inr (Or.inl (hk-wif-nready _ y g2 aw2 hr))))))
  (intros y hy) (exact (rm-app-r y _ L hy)))
;; ---- the settle loop: the queue is the exemption list; it empties (P7)
(a/theorem rm-swap3 [y :- Nat, n :- (List Nat), t :- (List Nat), h :- (List Nat)]
  (=> (= (reach-mem y (List.append Nat n (List.append Nat t h))) true) (= (reach-mem y (List.append Nat (List.append Nat t n) h)) true))
  (intro hy)
  (simp only [reach-mem-append Bool.or_eq_true] at hy)
  (simp only [reach-mem-append Bool.or_eq_true])
  (cases hy)
  (case [inl z] (exact (Or.inl (Or.inr z))))
  (case [inr z]
    (cases z)
    (case [inl z1] (exact (Or.inl (Or.inl z1))))
    (case [inr z1] (exact (Or.inr z1)))))
(a/theorem hk-settle-loop [hxm :- (List Nat), fuel :- (List Nat)]
  (forall [W :- World, q :- (List Nat)]
    (=> (= (gd W) true) (= (g7 W) true) (= (hmk (List.append Nat q hxm) W) true) (= (:rest (settle-loop fuel W q)) (List.nil Nat))
        (= (hmk hxm (:world (settle-loop fuel W q))) true)))
  (induction fuel)
  (case [nil]
    (intros W q hg h7 h hr)
    (simp only [settle-loop] at hr)
    (simp only [settle-loop])
    (rw [hr] at h) (exact h))
  (case [cons f0 f ih]
    (intros W q hg h7 h hr)
    (cases q)
    (case [nil] (simp only [settle-loop]) (exact h))
    (case [cons d t]
      (simp only [settle-loop] at hr)
      (simp only [settle-loop])
      (have s := (hk-settle-step (List.append Nat t hxm) W d false hg h7 h))
      (apply (ih (settle-one W d false) (List.append Nat t (settle-next W (settle-one W d false) d)) (gd-settle-one W d false hg) (g7-settle-one W d false h7) _ hr))
      (exact (hmk-intro _ _ (hmk-sample _ _ s)
               (hmk-rest-xm _ _ _ (fn [y :- Nat, hy :- (= (reach-mem y (List.append Nat (settle-next W (settle-one W d false) d) (List.append Nat t hxm))) true)]
                                    (rm-swap3 y _ t hxm hy)) (hmk-rest-of _ _ s)))))))
(a/theorem hk-rest-nil [w :- World, d :- Nat, ch :- Bool]
  (=> (= (settle-done w d ch) true) (= (:rest (settle-res w d ch)) (List.nil Nat)))
  (intro h)
  (cases hr (:rest (settle-res w d ch)))
  (case [nil] (rfl))
  (case [cons a t] (simp only [settle-done hr] at h) (cases h)))
(a/theorem hmk-settle-x [hxm :- (List Nat), W :- World, C :- Nat, ch :- Bool]
  (=> (= (gd W) true) (= (g7 W) true) (= (awake (:comps W) C) true) (= (hmk (List.cons Nat C hxm) W) true)
      (= (hmk hxm (settle W C ch)) true))
  (intros hg h7 ha h)
  (have hs := (gd-sample W hg))
  (cases hr (ready-id W C))
  (case [false]
    (simp only [settle hr])
    (apply (hmk-dis hxm (List.cons Nat C (List.nil Nat)) hxm W h))
    (intros y hy)
    (simp only [reach-mem-cons reach-mem Bool.or_false] at hy)
    (have e := (Nat.eq_of_beq_eq_true hy)) (rw [e])
    (exact (Or.inr (Or.inl (hk-wif-nready W C hg ha hr))))
    (intros y hy) (exact hy))
  (case [true]
    (simp only [settle hr settle-res])
    (have s := (hk-settle-step hxm W C ch hg h7 h))
    (have rn := (hk-rest-nil W C ch (settle-done-ok W C ch hs)))
    (simp only [settle-res] at rn)
    (exact (hk-settle-loop hxm (settle-fuel W) _ _ (gd-settle-one W C ch hg) (g7-settle-one W C ch h7) s rn))))

;; ---- T12's result row: the completed computation is exempt until it settles
(a/theorem hmk-comp-upd-x [hxm :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                           hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                           hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c)))]
  (=> (= (hmk hxm w) true) (= (hmk (List.cons Nat x hxm) (comp-upd w x f)) true))
  (intro h)
  (have r0 := (hmk-rest-xm hxm (List.cons Nat x hxm) w (fn [d :- Nat, hd :- (= (reach-mem d hxm) true)] (hk-rm-cons d x hxm hd)) (hmk-rest-of hxm w h)))
  (have r (= (hmk-rest (List.cons Nat x hxm) (comp-upd w x f)) true))
  (simp only [hmk-rest comp-upd set-comps]) (simp only [hmk-rest] at r0)
  (apply (hk-all-cs _ (:comps w) (tbl-upd comp-id x f (:comps w)) (:edges w) _ _ r0))
  (intros d hd) (rw [(tbl-has-upd CompRow comp-id x d f hid (:comps w))]) (exact hd)
  (intros d hx hd)
  (simp only [reach-mem-cons Bool.or_eq_false_iff] at hx)
  (have q (= (Nat.beq x d) false)) (rw [beq-comm]) (exact (And.left hx))
  (exact (hk-wif-pend-ne d x f hid (:comps w) q hd))
  (exact (hmk-intro _ _ (inv-comp-upd w x f hid hp (hmk-sample hxm w h)) r)))
(a/theorem hk-comps-cancel-res [w :- World, r :- RunRow] (= (:comps (cancel-res w r)) (:comps w))
  (simp only [cancel-res])
  (have f (forall [xs :- (List Nat), w1 :- World] (= (:comps (nat-fold res-cancel w1 xs)) (:comps w1))))
  (intro xs) (induction xs)
  (case [nil] (intro w1) (simp only [nat-fold]))
  (case [cons y t ih] (intro w1) (simp only [nat-fold]) (exact (Eq.trans (ih (res-cancel w1 y)) (Eq.refl _))))
  (exact (f (:resources r) w)))
;; gd after T12's result row (the inner step of gd-complete-body)
(a/theorem hk-gd-result [w :- World, r :- RunRow, c :- CompRow, res :- RunResult]
  (=> (= (Bool.or (Bool.not (gd-cce w r)) (tbl-all (gd-noal (:of r) (:epoch r)) (:runs w))) true) (= (gd w) true)
      (= (comp-find w (:of r)) (Option.some CompRow c)) (= (Nat.beq (:epoch r) (:epoch c)) true)
      (= (gd (comp-upd w (:id c) (comp-result-row res (:epoch r)))) true))
  (intros hpre h hc he)
  (have hs := (gd-sample w h))
  (have mc := (tbl-find-mem CompRow comp-id (:of r) c (:comps w) hc))
  (have ic (= (:id c) (:of r))) (exact (tbl-find-id CompRow comp-id (:of r) c (:comps w) hc))
  (have ee := (Nat.eq_of_beq_eq_true he))
  (simp only [gd-cce hc he Bool.not_true Bool.false_or] at hpre)
  (have hn (= (tbl-all (gd-noal (:id c) (:epoch c)) (:runs w)) true)) (rw [ic]) (rw [← ee]) (exact hpre)
  (have p := (gdk-parts _ _ _ (gd-rest-of w h)))
  (have q := (And.right p)) (rw [all-gdkeys] at q)
  (have hc0 := (tbl-all-mem CompRow (fn [x :- CompRow] (gd-c (:runs w) (:next-id w) (gdkey x))) c (:comps w) q mc))
  (have u := (gd-same-id w c (fn [x :- CompRow] (gd-c (:runs w) (:next-id w) (gdkey (comp-result-row res (:epoch r) x)))) hs mc
               (gd-result-c (:runs w) (:next-id w) c (:epoch r) res hc0 ee hn)))
  (have r1 (= (gd-rest (comp-upd w (:id c) (comp-result-row res (:epoch r)))) true))
  (show (= (gdk (gdkeys (tbl-upd comp-id (:id c) (comp-result-row res (:epoch r)) (:comps w))) (:runs w) (:next-id w)) true))
  (simp only [gdk (And.left p) Bool.true_and])
  (rw [all-gdkeys])
  (exact (gd-upd-same (:id c) (comp-result-row res (:epoch r)) _ _
           (fn [x :- CompRow, hx :- (= (gd-c (:runs w) (:next-id w) (gdkey x)) true)] hx) (:comps w) q u))
  (exact (gd-intro _ (inv-comp-upd w (:id c) (comp-result-row res (:epoch r)) (comp-result-row-id res (:epoch r))
                       (comp-result-row-pending res (:epoch r)) hs) r1)))
(a/theorem hk-aw-result [d :- Nat, res :- RunResult, ep :- Nat, c :- CompRow]
  (=> (= (not-idle-if-id d c) true) (= (not-idle-if-id d (comp-result-row res ep c)) true))
  (intro h) (exact h))

(a/theorem hmk-complete-body-x [hxm :- (List Nat), w :- World, r :- RunRow, res :- RunResult]
  (=> (= (Bool.or (Bool.not (gd-cce w r)) (tbl-all (gd-noal (:of r) (:epoch r)) (:runs w))) true) (= (gd w) true) (= (g7 w) true)
      (= (awake (:comps w) (:of r)) true) (= (hmk hxm w) true)
      (= (hmk hxm (:world (complete-body w r res))) true))
  (intros hpre hg h7 ha h)
  (cases hc (comp-find w (:of r)))
  (case [none]
    (cases hk (task-find w (:of r)))
    (case [none] (simp only [complete-body hc hk]) (exact h))
    (case [some k]
      (simp only [complete-body hc hk complete-task])
      (exact (nat-fold-hmk hxm (fire-edge res) (hmk-fire-edge hxm res) _ _
               (hmk-cancel-res hxm _ r (hmk-task-upd hxm w (:id k) (task-result-row res) (task-result-row-id res) h))))))
  (case [some c]
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [complete-body hc he]) (exact h))
    (case [true]
      (have ic (= (:id c) (:of r))) (exact (tbl-find-id CompRow comp-id (:of r) c (:comps w) hc))
      (have g1 := (gd-cancel-res _ r (hk-gd-result w r c res hpre hg hc he)))
      (have s1 := (g7-cancel-res _ r (g7-comp-upd-m w (:id c) (comp-result-row res (:epoch r)) (comp-result-row-id res (:epoch r))
                                     (comp-result-row-pending res (:epoch r)) (comp-result-row-nsl res (:epoch r)) (comp-result-row-kcl res (:epoch r)) h7)))
      (have h1 := (hmk-cancel-res _ _ r (hmk-comp-upd-x hxm w (:id c) (comp-result-row res (:epoch r)) (comp-result-row-id res (:epoch r))
                                          (comp-result-row-pending res (:epoch r)) h)))
      (have a1 (= (awake (:comps (cancel-res (comp-upd w (:id c) (comp-result-row res (:epoch r))) r)) (:id c)) true))
      (rw [hk-comps-cancel-res]) (simp only [awake comp-upd set-comps]) (simp only [awake] at ha) (rw [ic])
      (exact (hk-cs-upd (not-idle-if-id (:of r)) (comp-result-row res (:epoch r)) (hk-aw-result (:of r) res (:epoch r)) (:of r) (:comps w) ha))
      (simp only [complete-body hc he complete-comp])
      (exact (hmk-settle-x hxm _ (:id c) _ g1 s1 a1 h1)))))
(lcopy! HMK 'inv-retire-after)
(a/theorem hmk-complete-raw-x [hxm :- (List Nat), w :- World, r :- RunRow, res :- RunResult]
  (=> (= (Bool.or (Bool.not (gd-cce w r)) (tbl-all (gd-u1 r) (:runs w))) true) (= (gd w) true) (= (g7 w) true)
      (List.Mem r (:runs w)) (= (run-alive r) true) (= (hmk hxm w) true) (= (hmk hxm (complete-raw w r res)) true))
  (intros hpre hg h7 mr hal h)
  (have h0 := (gd-run-upd-m w (:id r) run-complete-row run-complete-row-id run-complete-row-grm hg))
  (have ce (= (gd-cce (run-upd w (:id r) run-complete-row) r) (gd-cce w r))) (rfl)
  (have p2 (= (Bool.or (Bool.not (gd-cce (run-upd w (:id r) run-complete-row) r))
                       (tbl-all (gd-noal (:of r) (:epoch r)) (:runs (run-upd w (:id r) run-complete-row)))) true))
  (cases hc (gd-cce w r))
  (case [false] (simp only [ce hc Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [hc Bool.not_true Bool.false_or] at hpre)
    (simp only [ce hc Bool.not_true Bool.false_or])
    (exact (gd-noal-upd r (:runs w) hpre)))
  (have s0 := (g7-run-upd-m w (:id r) run-complete-row run-complete-row-id run-complete-row-dwn run-complete-row-snk h7))
  (have p := (g7k-parts _ _ _ (g7-rest-of w h7)))
  (have a := (tbl-all-mem RunRow _ r (:runs w) (And.left p) mr))
  (simp only [a7-one hal Bool.not_true Bool.false_or] at a)
  (have a0 (= (awake (:comps (run-upd w (:id r) run-complete-row)) (:of r)) true)) (exact a)
  (have h1 := (hmk-run-upd hxm w (:id r) run-complete-row run-complete-row-id h))
  (simp only [complete-raw])
  (exact (hmk-fin-if-final hxm _ (:of r) (hmk-run-cascade hxm _ _ (hmk-retire-after hxm _ (:id r) (hmk-complete-body-x hxm _ r res p2 h0 s0 a0 h1))))))
(swap! (:renames HMK) assoc 'inv-complete-raw 'hmk-complete-raw-x 'inv-complete-body 'hmk-complete-body-x)
(override! HMK 't12-inv '[]
  '(a/theorem t12-hmk [hxm :- (List Nat), w :- World, st :- Nat, tag :- Nat, v :- Nat]
     (=> (= (g10r w) true) (= (gd w) true) (= (g7 w) true) (= (hmk hxm w) true) (= (hmk hxm (:world (t12-complete w st tag v))) true))
     (intros hg10 hg h7 h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t12-complete ht refuse]) (exact h)
     (cases hn (run-normal r))
     (simp only [t12-complete ht hn refuse]) (exact h)
     (have mr := (And.left (tok-facts w st r ht)))
     (simp only [t12-complete ht hn accept])
     (exact (hmk-complete-raw-x hxm w r _ (gd-u1-of-g10r w r hg10 mr) hg h7 mr (normal-alive r hn) h))))
(lcopy! HMK 't12-inv)

;; ===========================================================================
;; Part F. Rule R: demote (the round's strays are exempt; i14's vr gives their creditors)
;; ===========================================================================

(a/theorem hk-cons-sub [d :- Nat, x :- Nat, hxm :- (List Nat)]
  (=> (= (reach-mem x hxm) true) (= (reach-mem d (List.cons Nat x hxm)) true) (= (reach-mem d hxm) true))
  (intros hx hd)
  (simp only [reach-mem-cons Bool.or_eq_true] at hd)
  (cases hd)
  (case [inl z] (have e := (Nat.eq_of_beq_eq_true z)) (rw [e]) (exact hx))
  (case [inr z] (exact z)))
;; ---- an exempt computation's row may change freely (keeping id and pending)
(a/theorem hmk-comp-upd-xm [hxm :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                            hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                            hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c)))]
  (=> (= (reach-mem x hxm) true) (= (hmk hxm w) true) (= (hmk hxm (comp-upd w x f)) true))
  (intros hx h)
  (have h1 := (hmk-comp-upd-x hxm w x f hid hp h))
  (exact (hmk-intro hxm _ (hmk-sample _ _ h1)
           (hmk-rest-xm _ hxm _ (fn [d :- Nat, hd :- (= (reach-mem d (List.cons Nat x hxm)) true)]
                                  (hk-cons-sub d x hxm hx hd)) (hmk-rest-of _ _ h1)))))

;; ---- one demotion of a stray x: x and the creditors of dep edges on x are strays (i14's vr)
(a/theorem hk-dok-own [X :- (List Nat), cs :- (List CompRow), x :- Nat, e :- EdgeRow]
  (=> (= (reach-mem x X) true) (= (hk-dok X cs (not-dep-of x) e) true))
  (intro hx)
  (cases hn (not-dep-of x e))
  (case [true] (simp only [hk-dok hn Bool.true_or]))
  (case [false]
    (simp only [not-dep-of dep-of Bool.and_eq_true] at hn)
    (have hn2 := (bnot-false _ hn))
    (simp only [Bool.and_eq_true] at hn2)
    (have ec := (Nat.eq_of_beq_eq_true (And.right hn2)))
    (simp only [hk-dok hk-safe ec hx Bool.true_or Bool.or_true])))
(a/theorem hk-dok-avoid [S :- (List Nat), R :- (List Nat), hxm :- (List Nat), W :- World, x :- Nat]
  (=> (= (reach-mem x S) true) (= (tbl-all (rm-in S) R) true) (= (vr S R W) true) (= (tbl-all (ncd14 x) (:edges W)) true)
      (= (hmk (List.append Nat S hxm) W) true)
      (= (tbl-all (hk-dok (List.append Nat S hxm) (:comps W) (edge-avoids x)) (:edges W)) true))
  (intros hx hR hv hn h)
  (have p := (vrk-parts _ _ _ _ _ (vr-rest-of _ _ W hv)))
  (have r := (hmk-rest-of _ W h)) (simp only [hmk-rest] at r)
  (apply (all-of-mem EdgeRow _ (:edges W)))
  (intros e me)
  (cases ha (edge-avoids x e))
  (case [true] (simp only [hk-dok ha Bool.true_or]))
  (case [false]
    (cases hm (:marked e))
    (case [false] (simp only [hk-dok ha hm Bool.not_false Bool.true_or Bool.false_or]))
    (case [true]
      (have pk := (hk-e-marked _ (:comps W) e (tbl-all-mem EdgeRow _ e (:edges W) r me) hm))
      (have kd := (And.left pk))
      (have nc := (tbl-all-mem EdgeRow _ e (:edges W) hn me))
      (simp only [ncd14 kd Bool.not_true Bool.false_or] at nc)
      (simp only [edge-avoids nc Bool.true_and] at ha)
      (have hd := (bnot-false _ ha))
      (have ed := (Nat.eq_of_beq_eq_true hd))
      (have db := (tbl-all-mem EdgeRow _ e (:edges W) (And.left (And.right p)) me))
      (have dS (= (reach-mem (:debtor e) S) true)) (rw [ed]) (exact hx)
      (simp only [dnb14 kd dS Bool.not_true Bool.false_or Bool.true_or Bool.true_and] at db)
      (have cS := (all-reach-mem (rm-in S) (:creditor e) R hR db))
      (simp only [rm-in] at cS)
      (simp only [hk-dok hk-safe ha hm (rm-app-l (:creditor e) S hxm cS) Bool.true_or Bool.or_true Bool.false_or Bool.not_true]))))
(lcopy! HMK 'inv-demote-epoch)
(a/theorem hmk-demote-x [S :- (List Nat), R :- (List Nat), hxm :- (List Nat), W :- World, x :- Nat]
  (=> (= (reach-mem x S) true) (= (tbl-all (rm-in S) R) true) (= (inv-rank W) true) (= (vr S (List.cons Nat x R) W) true)
      (= (hmk (List.append Nat S hxm) W) true) (= (hmk (List.append Nat S hxm) (demote W x)) true))
  (intros hx hR hk hv h)
  (have hX := (rm-app-l x S hxm hx))
  (cases hf (comp-find W x)) (case' [some c]) (case' [none])
  (simp only [demote hf]) (exact h)
  (cases hi (:idle c))
  (case' [true])
  (simp only [demote hf hi]) (exact h)
  (simp only [demote hf hi demote-edges])
  (have h1 := (hmk-run-cascade _ W (cancel-jobs (demote-cancels W c)) h))
  (have v1 := (vr-run-cascade S (List.cons Nat x R) W (cancel-jobs (demote-cancels W c)) hv))
  (have h2 := (hmk-demote-epoch _ (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c) h1))
  (have v2 := (vr-demote-epoch S (List.cons Nat x R) (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c) v1))
  (have dk (= (tbl-all (hk-dok (List.append Nat S hxm) (:comps (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c))) (not-dep-of x)) (:edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)))) true))
  (apply (all-of-mem EdgeRow _ (:edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c))))) (intros e me) (exact (hk-dok-own _ _ x e hX))
  (have h3 := (hmk-drop-edges _ (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) dk h2))
  (have v3 := (vr-drop-r S R (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x
                (ncd-drop (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) x)
                (vr-drop-edges S (List.cons Nat x R) (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x) v2)))
  (have nc := (ncd-drop (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) x))
  (cases hf3 (comp-find (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) x))
  (case' [some c3]) (case' [none])
  (simp only [demote-finish hf3]) (exact h3)
  (cases hkp (demote-keep (drop-edges (demote-epoch (run-cascade W (cancel-jobs (demote-cancels W c))) x (demote-cur W c)) (not-dep-of x)) c3))
  (simp only [demote-finish hf3 hkp])
  (exact (hmk-comp-del-unref _ _ x (drop-edges-avoids _ x)
           (hmk-drop-edges _ _ (edge-avoids x) (hk-dok-avoid S R hxm _ x hx hR v3 nc h3) h3)))
  (simp only [demote-finish hf3 hkp])
  (exact (hmk-comp-upd-xm _ _ x _ (comp-make-idle-id _) (comp-make-idle-pending _) hX h3)))
(a/theorem hmk-demote-fold [S :- (List Nat), hxm :- (List Nat), R :- (List Nat)]
  (forall [W :- World] (=> (= (tbl-all (rm-in S) R) true) (= (inv-rank W) true) (= (vr S R W) true)
                           (= (hmk (List.append Nat S hxm) W) true) (= (hmk (List.append Nat S hxm) (nat-fold demote W R)) true)))
  (induction R)
  (case [nil] (intros W hR hk hv h) (simp only [nat-fold]) (exact h))
  (case [cons x t ih]
    (intros W hR hk hv h)
    (simp only [tbl-all Bool.and_eq_true] at hR)
    (have hx (= (reach-mem x S) true)) (exact (And.left hR))
    (simp only [nat-fold])
    (exact (ih (demote W x) (And.right hR) (rk-demote W x hk) (vr-demote S t W x hx hk hv) (hmk-demote-x S t hxm W x hx (And.right hR) hk hv h)))))
;; at the end of the pass no dep edge has a stray debtor
(a/theorem hk-nmd-pass [S :- (List Nat), hxm :- (List Nat), W :- World, d :- Nat]
  (=> (= (vr S (List.nil Nat) W) true) (= (hmk (List.append Nat S hxm) W) true) (= (reach-mem d S) true)
      (= (tbl-all (hk-nmd d) (:edges W)) true))
  (intros hv h hd)
  (have p := (vrk-parts _ _ _ _ _ (vr-rest-of _ _ W hv)))
  (have r := (hmk-rest-of _ W h)) (simp only [hmk-rest] at r)
  (apply (all-of-mem EdgeRow _ (:edges W)))
  (intros e me)
  (cases hm (:marked e))
  (case [false] (simp only [hk-nmd hm Bool.not_false Bool.true_or]))
  (case [true]
    (have kd := (And.left (hk-e-marked _ (:comps W) e (tbl-all-mem EdgeRow _ e (:edges W) r me) hm)))
    (cases he (Nat.beq (:debtor e) d))
    (case [false] (simp only [hk-nmd he Bool.not_false Bool.or_true]))
    (case [true]
      (have ed := (Nat.eq_of_beq_eq_true he))
      (have db := (tbl-all-mem EdgeRow _ e (:edges W) (And.left (And.right p)) me))
      (have dS (= (reach-mem (:debtor e) S) true)) (rw [ed]) (exact hd)
      (simp only [dnb14 kd dS reach-mem Bool.not_true Bool.false_or Bool.true_or Bool.true_and] at db)
      (cases db))))
(a/theorem hmk-norm-round [hxm :- (List Nat), w :- World]
  (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (hmk hxm w) true) (= (hmk hxm (norm-round w)) true))
  (intros hk hv h)
  (have h0 := (vr-pass-start w hv))
  (have h1 := (hmk-run-cascade hxm w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) h))
  (have h1x := (hmk-intro (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) hxm) (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (hmk-sample hxm (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) h1)
                 (hmk-rest-xm hxm (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) hxm) (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (fn [d :- Nat, hd :- (= (reach-mem d hxm) true)] (rm-app-r d (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) hxm hd)) (hmk-rest-of hxm (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) h1))))
  (have v1 := (vr-run-cascade _ _ w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) h0))
  (have k1 := (rk-run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) hk))
  (have f := (hmk-demote-fold (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) hxm (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))
               _ (rm-in-scan CompRow comp-id (comp-stray (live-list w)) (:comps w)) k1 v1 h1x))
  (have vf := (vr-fold (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))
                (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (rm-in-scan CompRow comp-id (comp-stray (live-list w)) (:comps w)) k1 v1))
  (have h2 (= (hmk hxm (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)))) true))
  (apply (hmk-dis hxm (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) hxm (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) f))
  (intros d hd) (exact (Or.inr (Or.inr (hk-nmd-pass (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) hxm (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))) d (And.left vf) f hd))))
  (intros d hd) (exact hd)
  (simp only [norm-round norm-round-lv])
  (exact (hmk-detach hxm _ h2)))
(a/theorem hmk-norm-loop [hxm :- (List Nat), fuel :- (List Nat)]
  (forall [w :- World] (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (hmk hxm w) true) (= (hmk hxm (norm-loop fuel w)) true)))
  (induction fuel)
  (case [nil] (intros w hk hv h) (simp only [norm-loop]) (exact h))
  (case [cons u f ih]
    (intros w hk hv h)
    (cases hn (normalized w))
    (case [false] (simp only [norm-loop hn]) (exact (ih (norm-round w) (rk-norm-round w hk) (vr-norm-round w hk hv) (hmk-norm-round hxm w hk hv h))))
    (case [true] (simp only [norm-loop hn]) (exact h))))
(a/theorem hmk-normalize-x [hxm :- (List Nat), w :- World]
  (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (hmk hxm w) true) (= (hmk hxm (normalize w)) true))
  (intros hk hv h)
  (simp only [normalize])
  (exact (hmk-norm-loop hxm (norm-fuel (detach w)) (detach w) (rk-detach w hk) (vr-detach (List.nil Nat) (List.nil Nat) w hv) (hmk-detach hxm w h))))
(a/theorem hmk-rule-r-round [hxm :- (List Nat), w :- World]
  (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (hmk hxm w) true) (= (filter-safe (normalize w)) true)
      (= (hmk hxm (rule-r-round w)) true))
  (intros hk hv h hf)
  (simp only [rule-r-round]) (rw [rule-r-filter-eq])
  (exact (hmk-filter-world hxm _ (keep-fn (normalize w)) (hmk-normalize-x hxm w hk hv h) hf)))
(a/theorem hmk-rr-loop [hxm :- (List Nat), fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (inv-rank w0) true) (= (vr (List.nil Nat) (List.nil Nat) w0) true) (= (hmk hxm w0) true) (= (rr-safe fuel w0) true)
                            (= (hmk hxm (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 hk hv h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (hmk-rule-r-round hxm w0 hk hv h hs)))
  (case [cons x f ih]
    (intros w0 hk hv h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (hmk-rule-r-round hxm w0 hk hv h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho])
      (exact (ih (rule-r-round w0) (rk-rule-r-round w0 hk (And.left hs)) (vr-rule-r-round w0 hk hv (And.left hs)) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))
(a/theorem hmk-rule-r [hxm :- (List Nat), w :- World]
  (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (hmk hxm w) true) (= (rule-r-safe w) true) (= (hmk hxm (rule-r w)) true))
  (intros hk hv h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (hmk-rr-loop hxm (rr-fuel w) w hk hv h hs)))

;; ===========================================================================
;; Part G. The step
;; ===========================================================================

;; ---- raw0 / raw0g / raw: gd, g7, ga, g10r threaded from the step's input (T2, T3, T11, T12)
(def ^:private hmk-calls
  '{(t2-inv w _ _ h) (t2-inv w _ _ hg hg7 hga h)
    (t3-inv w _ _ _ _ h) (t3-inv w _ _ _ _ hg hg7 h)
    (t3-top-inv w _ _ _ _ h) (t3-top-inv w _ _ _ _ hg hg7 h)
    (t11-inv w _ _ h) (t11-inv w _ _ hg h)
    (t12-inv w _ _ _ h) (t12-inv w _ _ _ hg10 hg hg7 h)})
(defn- hmk-add-hyps [form calls]
  (let [[hd nm binders stmt & proof] form
        stmt2 (apply list '=> '(= (gd w) true) '(= (g7 w) true) '(= (ga w) true) '(= (g10r w) true) (rest stmt))
        proof2 (map (fn [t] (if (= t '(intro h)) '(intros hg hg7 hga hg10 h) t)) proof)]
    (subst-forms #(contains? calls %) calls (apply list hd nm binders stmt2 proof2))))
(patch! HMK 'raw0-inv (fn [form] (hmk-add-hyps (hmk-patch form) hmk-calls)))
(patch! HMK 'raw0g-inv (fn [form] (hmk-add-hyps (hmk-patch form) '{(raw0-inv w it h) (raw0-inv w it hg hg7 hga hg10 h)})))
(patch! HMK 'raw-inv (fn [form] (hmk-add-hyps (hmk-patch form) '{(raw0g-inv w it h) (raw0g-inv w it hg hg7 hga hg10 h)})))
(lcopy! HMK 'raw-inv)

;; Theorem (h-mark bundle through the step)
(a/theorem step-hmk [w :- World, it :- Item]
  (=> (= (gd w) true) (= (g7 w) true) (= (ga w) true) (= (g10r w) true) (= (inv-rank w) true) (= (v14 w) true)
      (= (rule-r-safe (:world (raw w it))) true) (= (hmk (List.nil Nat) w) true)
      (= (hmk (List.nil Nat) (:world (world-step w it))) true))
  (intros hg h7 hga hg10 hk hv hs h)
  (simp only [v14] at hv)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true]
    (have e2 := (step-accepted w it ha)) (rw [e2])
    (have r0 := (raw-vq (List.nil Nat) (List.nil Nat) false w it hv))
    (exact (hmk-rule-r _ _ (raw-rk w it hk) (vr-of-vq (List.nil Nat) false _ r0 (dep-active-of-g7 _ (raw-g7 w it h7)))
             (raw-hmk _ w it hg h7 hga hg10 h) hs))))

;; the combined bundle: p3l = p3k && hmk [] (no honest hypothesis)
(a/defn p3l [w :- World] Bool (Bool.and (p3k w) (hmk (List.nil Nat) w)))
(a/theorem p3l-parts [w :- World] (=> (= (p3l w) true) (And (= (p3k w) true) (= (hmk (List.nil Nat) w) true)))
  (intro h) (simp only [p3l Bool.and_eq_true] at h) (exact h))
(a/theorem p3l-empty [] (= (p3l empty-world) true) (rfl))
(a/theorem step-p3l [w :- World, it :- Item] (=> (= (p3l w) true) (= (p3l (:world (world-step w it))) true))
  (intro h)
  (have p := (p3l-parts w h))
  (have pk := (p3k-parts w (And.left p)))
  (have pj := (p3j-parts w (And.left pk)))
  (have pc := (p3i-ctx w (And.left pj)))
  (have pb := (p3b-parts w (And.left pc)))
  (have a1 := (step-p3k w it (And.left p)))
  (have a2 := (step-hmk w it (And.right pj) (p3i-g7 w (And.left pj)) (And.left pb) (And.right pc) (And.left (And.right pb)) (And.right pk)
                (step-rule-r-safe w it (And.left pc)) (And.right p)))
  (simp only [p3l a1 a2 Bool.and_self]))

;; Theorem (h-mark, P11 first half): after every step from a p3l world, every marked edge's debtor is waiting
(a/theorem step-h-mark-total [w :- World, it :- Item] (=> (= (p3l w) true) (= (h-mark (:world (world-step w it))) true))
  (intro h)
  (exact (hk-h-mark _ (And.right (p3l-parts _ (step-p3l w it h))))))
(a/theorem p3l-h-mark [w :- World] (=> (= (p3l w) true) (= (h-mark w) true))
  (intro h) (exact (hk-h-mark w (And.right (p3l-parts w h)))))
