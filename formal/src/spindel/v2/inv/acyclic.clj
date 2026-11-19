(ns spindel.v2.inv.acyclic
  "Z#69 (engine PR #272): scope parents are acyclic, through every step, kernel-checked (Init only).

  detach k s re-parents k's run scope rs under s. Without the guard (`detach-ok`: rs is neither s
  nor on s's parent chain, `scope-within`, engine `within?`) detaching k into a scope of its own
  run-scope subtree closes a cycle (rs.parent = s, s below rs) and neither scope is ever removed.

    scopes-acyclic w   no scope is on its own `scope-ancestors` (executable); equivalently no scope
                       reaches itself through the parent fields (`cy-acyc-of`, `cy-acyc-intro`:
                       forall y, Reach (scope-up w) (scope-up w y) y -> False)
    gcy w              inv-sample w and `gcy-rest`: every scope's parent is below the allocator
                       (`cy-par-below`: a fresh scope is nobody's parent yet) and scopes-acyclic.

  The graph lemmas are generic over the parent function (Part A): a sub-graph keeps acyclicity
  (deletion, Rule R's filter), a fresh node no edge points to keeps it (scope creation: the id is
  next-id, the parent 0 or an existing scope, so below next-id), and re-parenting x under p keeps
  it when x is neither p nor above p (detach under the guard). The copy over the raw transition and
  normalization is spindel.v2.inv.copier's (`mk-bundle`, `prim!`, `lcopy!`), as spindel.v2.inv.i1-scopes's G1:
  overrides at run creation (`gcy-add-run-scope`: the parent is 0 or the owner scope), open-scope
  (the current scope exists, `open-ok`) and detach (`t-detach-gcy`: the guard).

  Theorems: step-gcy (Rule R's honest hypothesis), step-acyc / acyc-empty (from p3b, no hypothesis),
  step-acyclic, step-acyclic-reach."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.inv.rank :refer :all]
            [spindel.v2.progress.casc :refer :all]
            [spindel.v2.inv.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.base :refer :all]))

;; ===========================================================================
;; Part A. Acyclic parent graphs (generic over the parent function u : Nat -> List Nat)
;; ===========================================================================

(a/theorem cy-reach-nil [u :- (=> Nat (List Nat)), x :- Nat]
  (=> (Reach u (List.nil Nat) x) False)
  (intro h)
  (induction h)
  (case [root r hr] (cases hr))
  (case [step p q hp hq ihp] (exact ihp)))

(a/theorem cy-reach-sub [u :- (=> Nat (List Nat)), v :- (=> Nat (List Nat)), R :- (List Nat), S :- (List Nat), x :- Nat]
  (=> (forall [z :- Nat] (=> (List.Mem z S) (List.Mem z R)))
      (forall [y :- Nat, z :- Nat] (=> (List.Mem z (v y)) (List.Mem z (u y))))
      (Reach v S x) (Reach u R x))
  (intros hr hs h)
  (induction h)
  (case [root r hm] (exact (Reach.root r (hr r hm))))
  (case [step p q hp hq ihp] (exact (Reach.step p q ihp (hs p q hq)))))

(a/theorem cy-acyc-sub [u :- (=> Nat (List Nat)), v :- (=> Nat (List Nat))]
  (=> (forall [y :- Nat, z :- Nat] (=> (List.Mem z (v y)) (List.Mem z (u y))))
      (forall [y :- Nat] (=> (Reach u (u y) y) False))
      (forall [y :- Nat] (=> (Reach v (v y) y) False)))
  (intros hs ha y h)
  (exact (ha y (cy-reach-sub u v (u y) (v y) y (hs y) hs h))))

(a/theorem cy-reach-avoid [v :- (=> Nat (List Nat)), R :- (List Nat), x :- Nat, z :- Nat]
  (=> (forall [q :- Nat] (=> (List.Mem q R) (= (Nat.beq q x) false)))
      (forall [y :- Nat, q :- Nat] (=> (List.Mem q (v y)) (= (Nat.beq q x) false)))
      (Reach v R z) (= (Nat.beq z x) false))
  (intros hr ht h)
  (induction h)
  (case [root r hm] (exact (hr r hm)))
  (case [step p q hp hq ihp] (exact (ht p q hq))))

(a/theorem cy-acyc-fresh [u :- (=> Nat (List Nat)), v :- (=> Nat (List Nat)), x :- Nat]
  (=> (forall [y :- Nat] (=> (= (Nat.beq y x) false) (= (v y) (u y))))
      (forall [y :- Nat, q :- Nat] (=> (List.Mem q (v y)) (= (Nat.beq q x) false)))
      (forall [y :- Nat] (=> (Reach u (u y) y) False))
      (forall [y :- Nat] (=> (Reach v (v y) y) False)))
  (intros he ht ha y h)
  (have hy := (cy-reach-avoid v (v y) x y (ht y) ht h))
  (have e := (he y hy))
  (have fr (forall [z :- Nat] (=> (Reach v (v y) z) (= (u z) (v z)))))
  (intros z hz) (exact (Eq.symm (he z (cy-reach-avoid v (v y) x z (ht y) ht hz))))
  (have h2 := (Iff.mpr (reach-frame v u (v y) y fr) h))
  (rw [e] at h2)
  (exact (ha y h2)))

;; A z: z is p or above p (the new parent's chain, s included)
(a/theorem cy-anc-closed [u :- (=> Nat (List Nat)), p :- Nat, z :- Nat, q :- Nat]
  (=> (Or (= z p) (Reach u (u p) z)) (List.Mem q (u z)) (Reach u (u p) q))
  (intros ha hq)
  (cases ha)
  (case [inl e] (rw [e] at hq) (exact (Reach.root q hq)))
  (case [inr r] (exact (Reach.step z q r hq))))

(a/theorem cy-anc-ne [u :- (=> Nat (List Nat)), x :- Nat, p :- Nat, z :- Nat]
  (=> (= (Nat.beq x p) false) (=> (Reach u (u p) x) False) (Or (= z p) (Reach u (u p) z))
      (= (Nat.beq z x) false))
  (intros hxp hg ha)
  (cases hb (Nat.beq z x))
  (case [false] (rfl))
  (case [true]
    (have ez (= z x)) (exact (Nat.eq_of_beq_eq_true hb))
    (cases ha)
    (case [inl e]
      (have exp (= x p)) (exact (Eq.trans (Eq.symm ez) e))
      (rw [exp] at hxp) (simp [Nat.beq_refl] at hxp))
    (case [inr r] (rw [ez] at r) (exact (False.elim (hg r))))))

(a/theorem cy-anc-trans [u :- (=> Nat (List Nat)), p :- Nat, y :- Nat, q :- Nat]
  (=> (Or (= y p) (Reach u (u p) y)) (Reach u (u y) q) (Or (= q p) (Reach u (u p) q)))
  (intros ha h)
  (induction h)
  (case [root r hm] (exact (Or.inr (cy-anc-closed u p y r ha hm))))
  (case [step a b hab hb ih] (exact (Or.inr (cy-anc-closed u p a b ih hb)))))

(a/theorem cy-reparent-out [u :- (=> Nat (List Nat)), v :- (=> Nat (List Nat)), x :- Nat, p :- Nat, y :- Nat, z :- Nat]
  (=> (forall [y2 :- Nat] (=> (= (Nat.beq y2 x) false) (= (v y2) (u y2))))
      (forall [z2 :- Nat] (=> (List.Mem z2 (v x)) (= z2 p)))
      (= (Nat.beq x p) false) (=> (Reach u (u p) x) False)
      (Reach v (v y) z)
      (Or (Reach u (u y) z) (Or (= z p) (Reach u (u p) z))))
  (intros he hp hxp hg h)
  (induction h)
  (case [root r hm]
    (cases hy (Nat.beq y x))
    (case [false] (rw [(he y hy)] at hm) (exact (Or.inl (Reach.root r hm))))
    (case [true]
      (have ey (= y x)) (exact (Nat.eq_of_beq_eq_true hy))
      (rw [ey] at hm) (exact (Or.inr (Or.inl (hp r hm))))))
  (case [step a b hab hb ih]
    (cases ih)
    (case [inl ra]
      (cases hq (Nat.beq a x))
      (case [false] (rw [(he a hq)] at hb) (exact (Or.inl (Reach.step a b ra hb))))
      (case [true]
        (have ea (= a x)) (exact (Nat.eq_of_beq_eq_true hq))
        (rw [ea] at hb) (exact (Or.inr (Or.inl (hp b hb))))))
    (case [inr aa]
      (rw [(he a (cy-anc-ne u x p a hxp hg aa))] at hb)
      (exact (Or.inr (Or.inr (cy-anc-closed u p a b aa hb)))))))

(a/theorem cy-reparent-in [u :- (=> Nat (List Nat)), v :- (=> Nat (List Nat)), x :- Nat, p :- Nat, y :- Nat, z :- Nat]
  (=> (forall [y2 :- Nat] (=> (= (Nat.beq y2 x) false) (= (v y2) (u y2))))
      (= (Nat.beq x p) false) (=> (Reach u (u p) x) False)
      (Or (= y p) (Reach u (u p) y))
      (Reach v (v y) z)
      (Reach u (u y) z))
  (intros he hxp hg hay h)
  (induction h)
  (case [root r hm]
    (rw [(he y (cy-anc-ne u x p y hxp hg hay))] at hm) (exact (Reach.root r hm)))
  (case [step a b hab hb ih]
    (have aa := (cy-anc-trans u p y a hay ih))
    (rw [(he a (cy-anc-ne u x p a hxp hg aa))] at hb)
    (exact (Reach.step a b ih hb))))

;; re-parenting x under p keeps the parent graph acyclic when x is neither p nor above p
(a/theorem cy-acyc-reparent [u :- (=> Nat (List Nat)), v :- (=> Nat (List Nat)), x :- Nat, p :- Nat]
  (=> (forall [y :- Nat] (=> (= (Nat.beq y x) false) (= (v y) (u y))))
      (forall [z :- Nat] (=> (List.Mem z (v x)) (= z p)))
      (= (Nat.beq x p) false) (=> (Reach u (u p) x) False)
      (forall [y :- Nat] (=> (Reach u (u y) y) False))
      (forall [y :- Nat] (=> (Reach v (v y) y) False)))
  (intros he hp hxp hg ha y h)
  (have o := (cy-reparent-out u v x p y y he hp hxp hg h))
  (cases o)
  (case [inl r] (exact (ha y r)))
  (case [inr ay] (exact (ha y (cy-reparent-in u v x p y y he hxp hg ay h)))))

;; ===========================================================================
;; Part B. The scope tables: parents of edited tables; Bool <-> Prop
;; ===========================================================================

;; the parent list of a found scope row (scope-up, unfolded)
(a/defn cy-par [o :- (Option ScopeRow)] (List Nat) (match o [none (List.nil Nat)] [(some s) (nz (:parent s))]))
(a/theorem cy-up [w :- World, y :- Nat] (= (scope-up w y) (cy-par (tbl-find scope-id y (:scopes w))))
  (cases hf (scope-find w y))
  (case [none] (simp only [scope-find] at hf) (simp only [scope-up scope-find hf cy-par]))
  (case [some s] (simp only [scope-find] at hf) (simp only [scope-up scope-find hf cy-par])))

(a/theorem cy-mem-nz [p :- Nat, y :- Nat] (=> (List.Mem y (nz p)) (= y p))
  (intro hm)
  (cases hz (Nat.beq p 0))
  (case [true] (simp only [nz hz] at hm) (cases hm))
  (case [false] (simp only [nz hz] at hm) (cases hm) (rfl) (rename_i hm2) (cases hm2)))

;; ---- the parent of y in edited scope tables

(a/theorem cy-par-upd [x :- Nat, f :- (=> ScopeRow ScopeRow), hf :- (forall [s :- ScopeRow] (= (scope-id (f s)) (scope-id s))),
                       hk :- (forall [s :- ScopeRow] (= (:parent (f s)) (:parent s))), y :- Nat, xs :- (List ScopeRow)]
  (= (cy-par (tbl-find scope-id y (tbl-upd scope-id x f xs))) (cy-par (tbl-find scope-id y xs)))
  (induction xs)
  (case [nil] (simp only [tbl-upd]))
  (case [cons h t ih]
    (cases hy (Nat.beq (scope-id h) y))
    (case [false]
      (cases hx (Nat.beq (scope-id h) x))
      (all_goals (simp only [tbl-upd tbl-find hx hy (hf h) ih])))
    (case [true]
      (cases hx (Nat.beq (scope-id h) x))
      (all_goals (simp only [tbl-upd tbl-find hx hy (hf h) cy-par (hk h)])))))

(a/theorem cy-par-set [x :- Nat, p :- Nat, z :- Nat, xs :- (List ScopeRow)]
  (=> (List.Mem z (cy-par (tbl-find scope-id x (tbl-upd scope-id x (scope-set-parent p) xs)))) (= z p))
  (induction xs)
  (case [nil] (intro hm) (simp only [tbl-upd tbl-find cy-par] at hm) (cases hm))
  (case [cons h t ih]
    (intro hm)
    (cases hx (Nat.beq (scope-id h) x))
    (case [false] (simp only [tbl-upd tbl-find hx] at hm) (exact (ih hm)))
    (case [true]
      (simp only [tbl-upd tbl-find scope-set-parent-id hx cy-par] at hm)
      (exact (cy-mem-nz p z hm)))))

(a/theorem cy-find-del-self [x :- Nat, xs :- (List ScopeRow)]
  (= (tbl-find scope-id x (tbl-del scope-id x xs)) (Option.none ScopeRow))
  (induction xs)
  (case [nil] (simp only [tbl-del tbl-find]))
  (case [cons h t ih] (cases hx (Nat.beq (scope-id h) x)) (all_goals (simp only [tbl-del tbl-find hx ih]))))

(a/theorem cy-par-del [x :- Nat, y :- Nat, z :- Nat, xs :- (List ScopeRow)]
  (=> (List.Mem z (cy-par (tbl-find scope-id y (tbl-del scope-id x xs)))) (List.Mem z (cy-par (tbl-find scope-id y xs))))
  (induction xs)
  (case [nil] (intro hm) (simp only [tbl-del tbl-find cy-par] at hm) (cases hm))
  (case [cons h t ih]
    (intro hm)
    (cases hx (Nat.beq (scope-id h) x))
    (case [false]
      (cases hy (Nat.beq (scope-id h) y))
      (case [false] (simp only [tbl-del tbl-find hx hy] at hm) (simp only [tbl-find hy]) (exact (ih hm)))
      (case [true] (simp only [tbl-del tbl-find hx hy] at hm) (simp only [tbl-find hy]) (exact hm)))
    (case [true]
      (simp only [tbl-del hx] at hm)
      (cases hy (Nat.beq (scope-id h) y))
      (case [false] (simp only [tbl-find hy]) (exact (ih hm)))
      (case [true]
        (have e1 (= (scope-id h) x)) (exact (Nat.eq_of_beq_eq_true hx))
        (have e2 (= (scope-id h) y)) (exact (Nat.eq_of_beq_eq_true hy))
        (have e (= y x)) (exact (Eq.trans (Eq.symm e2) e1))
        (rw [e cy-find-del-self] at hm)
        (simp only [cy-par] at hm) (cases hm)))))

(a/theorem cy-par-keep [K :- (=> Nat Bool), y :- Nat, z :- Nat, xs :- (List ScopeRow)]
  (=> (List.Mem z (cy-par (tbl-find scope-id y (tbl-keep K scope-id xs)))) (List.Mem z (cy-par (tbl-find scope-id y xs))))
  (intro hm)
  (cases hk (K y))
  (case [false] (rw [(keep-find-out ScopeRow K scope-id y xs hk)] at hm) (simp only [cy-par] at hm) (cases hm))
  (case [true] (rw [(keep-find-in ScopeRow K scope-id y xs hk)] at hm) (exact hm)))

;; every parent below n: the parent of anything is below n
(a/defn cy-par-below [n :- Nat, s :- ScopeRow] Bool (Nat.blt (:parent s) n))
(a/theorem cy-par-lt [n :- Nat, y :- Nat, z :- Nat, xs :- (List ScopeRow)]
  (=> (= (tbl-all (cy-par-below n) xs) true) (List.Mem z (cy-par (tbl-find scope-id y xs))) (< z n))
  (intros ha hm)
  (cases hf (tbl-find scope-id y xs))
  (case [none] (rw [hf] at hm) (simp only [cy-par] at hm) (cases hm))
  (case [some s]
    (rw [hf] at hm) (simp only [cy-par] at hm)
    (have e := (cy-mem-nz (:parent s) z hm))
    (have b := (tbl-all-mem ScopeRow (cy-par-below n) s xs ha (tbl-find-mem ScopeRow scope-id y s xs hf)))
    (simp only [cy-par-below Nat.blt_eq] at b)
    (rw [e]) (exact b)))

(a/theorem cy-anc-iff [w :- World, s :- Nat, a :- Nat]
  (Iff (= (reach-mem a (scope-ancestors w s)) true) (Reach (scope-up w) (scope-up w s) a))
  (have c := (scope-anc-conv w s))
  (rw [reach-run-l-eq] at c)
  (simp only [scope-ancestors])
  (rw [reach-run-l-eq])
  (exact (reach-run-iff _ (scope-up w) (scope-up w s) a c)))

;; the invariant (executable): no scope is on its own ancestor chain
(a/defn scope-acyc-at [w :- World, s :- ScopeRow] Bool (Bool.not (reach-mem (:id s) (scope-ancestors w (:id s)))))
(a/defn scopes-acyclic [w :- World] Bool (tbl-all (scope-acyc-at w) (:scopes w)))

(a/theorem cy-acyc-of [w :- World]
  (=> (= (scopes-acyclic w) true) (forall [y :- Nat] (=> (Reach (scope-up w) (scope-up w y) y) False)))
  (intros h y r)
  (cases hf (tbl-find scope-id y (:scopes w)))
  (case [none]
    (have e (= (scope-up w y) (List.nil Nat))) (rw [(cy-up w y) hf])
    (rw [e] at r) (exact (cy-reach-nil _ y r)))
  (case [some s]
    (have m := (tbl-find-mem ScopeRow scope-id y s (:scopes w) hf))
    (have i := (tbl-find-id ScopeRow scope-id y s (:scopes w) hf))
    (have b := (tbl-all-mem ScopeRow (scope-acyc-at w) s (:scopes w) h m))
    (simp only [scope-acyc-at] at b)
    (have e (= (:id s) y)) (exact i)
    (rw [e] at b)
    (have r2 := (Iff.mpr (cy-anc-iff w y y) r))
    (rw [r2] at b) (simp at b)))

(a/theorem cy-acyc-intro [w :- World]
  (=> (forall [y :- Nat] (=> (Reach (scope-up w) (scope-up w y) y) False)) (= (scopes-acyclic w) true))
  (intro ha)
  (simp only [scopes-acyclic])
  (apply (all-of-mem ScopeRow (scope-acyc-at w) (:scopes w)))
  (intros s m)
  (simp only [scope-acyc-at])
  (cases hr (reach-mem (:id s) (scope-ancestors w (:id s))))
  (case [false] (simp only [hr Bool.not_false]))
  (case [true] (exact (False.elim (ha (:id s) (Iff.mp (cy-anc-iff w (:id s) (:id s)) hr))))))

;; ===========================================================================
;; Part C. The bundle gcy and its primitives
;; ===========================================================================

(a/defn gcy-rest [w :- World] Bool
  (Bool.and (tbl-all (cy-par-below (:next-id w)) (:scopes w)) (scopes-acyclic w)))
(a/defn gcy [w :- World] Bool (Bool.and (inv-sample w) (gcy-rest w)))

(a/theorem gcy-sample [w :- World] (=> (= (gcy w) true) (= (inv-sample w) true))
  (intro h) (simp only [gcy Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem gcy-rest-of [w :- World] (=> (= (gcy w) true) (= (gcy-rest w) true))
  (intro h) (simp only [gcy Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem gcy-intro [w :- World] (=> (= (inv-sample w) true) (= (gcy-rest w) true) (= (gcy w) true))
  (intros h1 h2) (simp only [gcy h1 h2 Bool.and_self]))
(a/theorem gcy-parts [w :- World]
  (=> (= (gcy w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (gcy-sample w h))))
(a/theorem gcy-rest-parts [w :- World]
  (=> (= (gcy-rest w) true)
      (And (= (tbl-all (cy-par-below (:next-id w)) (:scopes w)) true) (= (scopes-acyclic w) true)))
  (intro h) (simp only [gcy-rest Bool.and_eq_true] at h) (exact h))
(a/theorem gcy-rest-intro [w :- World]
  (=> (= (tbl-all (cy-par-below (:next-id w)) (:scopes w)) true) (= (scopes-acyclic w) true) (= (gcy-rest w) true))
  (intros h1 h2) (simp only [gcy-rest h1 h2 Bool.and_self]))
(a/theorem gcy-acyc [w :- World]
  (=> (= (gcy w) true) (forall [y :- Nat] (=> (Reach (scope-up w) (scope-up w y) y) False)))
  (intro h) (exact (cy-acyc-of w (And.right (gcy-rest-parts w (gcy-rest-of w h))))))

(a/theorem cy-lt-beq [q :- Nat, n :- Nat] (=> (< q n) (= (Nat.beq q n) false))
  (intro h) (cases hb (Nat.beq q n)) (rfl) (have e := (Nat.eq_of_beq_eq_true hb)) (omega))

;; a scope id is below the allocator
(a/theorem cy-scope-below [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (scope-has w x) true) (< x (:next-id w)))
  (intros h hc)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (have hm (= (nat-mem x (tbl-ids scope-id (:scopes w))) true)) (rw [nat-mem-ids]) (exact hc)
  (have r := (all-nat-mem (id-in-range (:next-id w)) x _ (And.left hb) hm))
  (simp only [id-in-range Bool.and_eq_true Nat.blt_eq] at r)
  (exact (And.right r)))

;; ---- the allocator

(a/theorem gcy-rest-next [w :- World, v :- Nat]
  (=> (= (gcy-rest w) true) (<= (:next-id w) v) (= (gcy-rest (set-next-id w v)) true))
  (intros h hv)
  (have p := (gcy-rest-parts w h))
  (have m (forall [s :- ScopeRow] (=> (= (cy-par-below (:next-id w) s) true) (= (cy-par-below v s) true))))
  (intros s hs) (simp only [cy-par-below Nat.blt_eq] at hs) (simp only [cy-par-below Nat.blt_eq]) (omega)
  (have a1 (= (tbl-all (cy-par-below (:next-id (set-next-id w v))) (:scopes (set-next-id w v))) true))
  (exact (tbl-all-mono ScopeRow (cy-par-below (:next-id w)) (cy-par-below v) m (:scopes w) (And.left p)))
  (have a2 (= (scopes-acyclic (set-next-id w v)) true)) (exact (And.right p))
  (exact (gcy-rest-intro _ a1 a2)))
(a/theorem gcy-rest-bump [w :- World] (=> (= (gcy-rest w) true) (= (gcy-rest (bump w)) true))
  (intro h) (simp only [bump]) (exact (gcy-rest-next w (+ (:next-id w) 1) h (Nat.le_succ (:next-id w)))))

;; ---- scope edits that keep every parent

(a/theorem gcy-scope-upd [w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow),
                          hf :- (forall [s :- ScopeRow] (= (scope-id (f s)) (scope-id s))),
                          hk :- (forall [s :- ScopeRow] (= (:parent (f s)) (:parent s)))]
  (=> (= (gcy w) true) (= (gcy (scope-upd w x f)) true))
  (intro h)
  (have p := (gcy-rest-parts w (gcy-rest-of w h)))
  (have es (= (:scopes (scope-upd w x f)) (tbl-upd scope-id x f (:scopes w)))) (rfl)
  (have a1 (= (tbl-all (cy-par-below (:next-id (scope-upd w x f))) (:scopes (scope-upd w x f))) true))
  (rw [es])
  (apply (tbl-all-upd ScopeRow scope-id x f (cy-par-below (:next-id w)) (cy-par-below (:next-id w)) _ _ (:scopes w) (And.left p)))
  (intros s q e) (simp only [cy-par-below (hk s)]) (simp only [cy-par-below] at q) (exact q)
  (intros s q e) (exact q)
  (have hs (forall [y :- Nat, z :- Nat] (=> (List.Mem z (scope-up (scope-upd w x f) y)) (List.Mem z (scope-up w y)))))
  (intros y z hm) (rw [(cy-up (scope-upd w x f) y) es (cy-par-upd x f hf hk y (:scopes w))] at hm) (rw [(cy-up w y)]) (exact hm)
  (have a2 := (cy-acyc-intro (scope-upd w x f) (cy-acyc-sub (scope-up w) (scope-up (scope-upd w x f)) hs (cy-acyc-of w (And.right p)))))
  (exact (gcy-intro _ (inv-scope-upd w x f hf (gcy-sample w h)) (gcy-rest-intro _ a1 a2))))

(a/theorem gcy-rest-scope-del [w :- World, x :- Nat] (=> (= (gcy-rest w) true) (= (gcy-rest (scope-del w x)) true))
  (intro h)
  (have p := (gcy-rest-parts w h))
  (have es (= (:scopes (scope-del w x)) (tbl-del scope-id x (:scopes w)))) (rfl)
  (have a1 (= (tbl-all (cy-par-below (:next-id (scope-del w x))) (:scopes (scope-del w x))) true))
  (rw [es])
  (exact (tbl-all-del ScopeRow scope-id x _ _ (fn [s :- ScopeRow, q :- (= (cy-par-below (:next-id w) s) true), e :- (= (Nat.beq (scope-id s) x) false)] q) _ (And.left p)))
  (have hs (forall [y :- Nat, z :- Nat] (=> (List.Mem z (scope-up (scope-del w x) y)) (List.Mem z (scope-up w y)))))
  (intros y z hm) (rw [(cy-up (scope-del w x) y) es] at hm) (rw [(cy-up w y)]) (exact (cy-par-del x y z (:scopes w) hm))
  (exact (gcy-rest-intro _ a1 (cy-acyc-intro (scope-del w x) (cy-acyc-sub (scope-up w) (scope-up (scope-del w x)) hs (cy-acyc-of w (And.right p)))))))

(a/theorem gcy-rest-filter [w :- World, K :- (=> Nat Bool)] (=> (= (gcy-rest w) true) (= (gcy-rest (filter-world K w)) true))
  (intro h)
  (have p := (gcy-rest-parts w h))
  (have es (= (:scopes (filter-world K w)) (tbl-keep K scope-id (:scopes w)))) (rfl)
  (have a1 (= (tbl-all (cy-par-below (:next-id (filter-world K w))) (:scopes (filter-world K w))) true))
  (rw [es]) (exact (tbl-all-keep-same ScopeRow K scope-id _ _ (And.left p)))
  (have hs (forall [y :- Nat, z :- Nat] (=> (List.Mem z (scope-up (filter-world K w) y)) (List.Mem z (scope-up w y)))))
  (intros y z hm) (rw [(cy-up (filter-world K w) y) es] at hm) (rw [(cy-up w y)]) (exact (cy-par-keep K y z (:scopes w) hm))
  (exact (gcy-rest-intro _ a1 (cy-acyc-intro (filter-world K w) (cy-acyc-sub (scope-up w) (scope-up (filter-world K w)) hs (cy-acyc-of w (And.right p)))))))

;; ---- a fresh scope (id next-id) whose parent is 0 or an existing scope: no parent field names
;; the fresh id, so no cycle passes through it
(a/theorem cy-hp-lt [w :- World, p :- Nat, z :- Nat]
  (=> (= (inv-sample w) true) (= (Bool.or (Nat.beq p 0) (scope-has w p)) true) (List.Mem z (nz p)) (< z (:next-id w)))
  (intros h hp hm)
  (have e := (cy-mem-nz p z hm))
  (cases hz (Nat.beq p 0))
  (case [true] (simp only [nz hz] at hm) (cases hm))
  (case [false]
    (simp only [hz Bool.false_or] at hp)
    (rw [e]) (exact (cy-scope-below w p h hp))))
(a/theorem cy-hp-le [w :- World, p :- Nat]
  (=> (= (inv-sample w) true) (= (Bool.or (Nat.beq p 0) (scope-has w p)) true) (< p (+ (:next-id w) 1)))
  (intros h hp)
  (cases hz (Nat.beq p 0))
  (case [true] (have e := (Nat.eq_of_beq_eq_true hz)) (omega))
  (case [false]
    (simp only [hz Bool.false_or] at hp)
    (have b := (cy-scope-below w p h hp)) (omega)))

(a/theorem cy-ins-same [w :- World, r :- ScopeRow, y :- Nat]
  (=> (= (scope-id r) (:next-id w)) (= (Nat.beq y (:next-id w)) false) (= (scope-up (bump (scope-ins w r)) y) (scope-up w y)))
  (intros hr hy)
  (have es (= (:scopes (bump (scope-ins w r))) (List.cons ScopeRow r (:scopes w)))) (rfl)
  (have hb (= (Nat.beq (scope-id r) y) false)) (rw [hr]) (exact (beq-symm-false y _ hy))
  (rw [(cy-up (bump (scope-ins w r)) y) (cy-up w y) es])
  (simp only [tbl-find hb]))
(a/theorem cy-ins-avoid [w :- World, r :- ScopeRow, y :- Nat, q :- Nat]
  (=> (= (Bool.or (Nat.beq (:parent r) 0) (scope-has w (:parent r))) true) (= (gcy w) true)
     (List.Mem q (scope-up (bump (scope-ins w r)) y)) (= (Nat.beq q (:next-id w)) false))
  (intros hp h hm)
  (have hs := (gcy-sample w h))
  (have p := (gcy-rest-parts w (gcy-rest-of w h)))
  (have es (= (:scopes (bump (scope-ins w r))) (List.cons ScopeRow r (:scopes w)))) (rfl)
  (rw [(cy-up (bump (scope-ins w r)) y) es] at hm)
  (apply (cy-lt-beq q (:next-id w)))
  (cases hb (Nat.beq (scope-id r) y))
  (case [false] (simp only [tbl-find hb] at hm) (exact (cy-par-lt (:next-id w) y q (:scopes w) (And.left p) hm)))
  (case [true] (simp only [tbl-find hb cy-par] at hm) (exact (cy-hp-lt w (:parent r) q hs hp hm))))
(a/theorem gcy-scope-ins-fresh [w :- World, r :- ScopeRow]
  (=> (= (scope-id r) (:next-id w)) (= (Bool.or (Nat.beq (:parent r) 0) (scope-has w (:parent r))) true)
      (= (gcy w) true) (= (gcy (bump (scope-ins w r))) true))
  (intros hr hp h)
  (have hs := (gcy-sample w h))
  (have p := (gcy-rest-parts w (gcy-rest-of w h)))
  (have es (= (:scopes (bump (scope-ins w r))) (List.cons ScopeRow r (:scopes w)))) (rfl)
  (have en (= (:next-id (bump (scope-ins w r))) (+ (:next-id w) 1))) (rfl)
  (have m (forall [s :- ScopeRow] (=> (= (cy-par-below (:next-id w) s) true) (= (cy-par-below (+ (:next-id w) 1) s) true))))
  (intros s q) (simp only [cy-par-below Nat.blt_eq] at q) (simp only [cy-par-below Nat.blt_eq]) (omega)
  (have hr0 (= (cy-par-below (+ (:next-id w) 1) r) true))
  (simp only [cy-par-below Nat.blt_eq]) (exact (cy-hp-le w (:parent r) hs hp))
  (have a1 (= (tbl-all (cy-par-below (:next-id (bump (scope-ins w r)))) (:scopes (bump (scope-ins w r)))) true))
  (have t (= (tbl-all (cy-par-below (+ (:next-id w) 1)) (:scopes w)) true))
  (exact (tbl-all-mono ScopeRow (cy-par-below (:next-id w)) (cy-par-below (+ (:next-id w) 1)) m (:scopes w) (And.left p)))
  (rw [es en])
  (simp only [tbl-all hr0 t Bool.and_self])
  (have a2 := (cy-acyc-intro _ (cy-acyc-fresh (scope-up w) (scope-up (bump (scope-ins w r))) (:next-id w)
                                 (fn [y :- Nat, hy :- (= (Nat.beq y (:next-id w)) false)] (cy-ins-same w r y hr hy))
                                 (fn [y :- Nat, q :- Nat, hm :- (List.Mem q (scope-up (bump (scope-ins w r)) y))] (cy-ins-avoid w r y q hp h hm))
                                 (cy-acyc-of w (And.right p)))))
  (exact (gcy-intro _ (inv-scope-ins-fresh w r hr hs) (gcy-rest-intro _ a1 a2))))

;; ---- detach: the run scope x gets the parent p, which is neither x nor below x
(a/theorem gcy-set-parent [w :- World, x :- Nat, p :- Nat]
  (=> (= (scope-within w p x) false) (= (scope-has w p) true) (= (gcy w) true)
      (= (gcy (scope-upd w x (scope-set-parent p))) true))
  (intros hg hp h)
  (have hs := (gcy-sample w h))
  (have pp := (gcy-rest-parts w (gcy-rest-of w h)))
  (simp only [scope-within Bool.or_eq_false_iff] at hg)
  (have hxp (= (Nat.beq x p) false)) (exact (beq-symm-false p x (And.left hg)))
  (have hr (=> (Reach (scope-up w) (scope-up w p) x) False))
  (intro r) (have r2 := (Iff.mpr (cy-anc-iff w p x) r)) (rw [(And.right hg)] at r2) (cases r2)
  (have pb := (cy-scope-below w p hs hp))
  (have es (= (:scopes (scope-upd w x (scope-set-parent p))) (tbl-upd scope-id x (scope-set-parent p) (:scopes w)))) (rfl)
  (have a1 (= (tbl-all (cy-par-below (:next-id (scope-upd w x (scope-set-parent p)))) (:scopes (scope-upd w x (scope-set-parent p)))) true))
  (rw [es])
  (apply (tbl-all-upd ScopeRow scope-id x (scope-set-parent p) (cy-par-below (:next-id w)) (cy-par-below (:next-id w)) _ _ (:scopes w) (And.left pp)))
  (intros s q e) (simp only [cy-par-below scope-set-parent Nat.blt_eq]) (exact pb)
  (intros s q e) (exact q)
  (have he (forall [y :- Nat] (=> (= (Nat.beq y x) false) (= (scope-up (scope-upd w x (scope-set-parent p)) y) (scope-up w y)))))
  (intros y hy)
  (rw [(cy-up (scope-upd w x (scope-set-parent p)) y) (cy-up w y) es (tbl-find-upd-ne ScopeRow scope-id x y (scope-set-parent p) (scope-set-parent-id p) (:scopes w) hy)])
  (have hpx (forall [z :- Nat] (=> (List.Mem z (scope-up (scope-upd w x (scope-set-parent p)) x)) (= z p))))
  (intros z hm) (rw [(cy-up (scope-upd w x (scope-set-parent p)) x) es] at hm) (exact (cy-par-set x p z (:scopes w) hm))
  (have a2 := (cy-acyc-intro _ (cy-acyc-reparent (scope-up w) (scope-up (scope-upd w x (scope-set-parent p))) x p he hpx hxp hr (cy-acyc-of w (And.right pp)))))
  (exact (gcy-intro _ (inv-scope-upd w x (scope-set-parent p) (scope-set-parent-id p) hs) (gcy-rest-intro _ a1 a2))))

;; ---- run + run scope (T4 / T5 / T11), the parent given (0 or an existing scope)
(a/theorem gcy-add-run-scope [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (Bool.or (Nat.beq parent 0) (scope-has w parent)) true) (= (gcy w) true)
      (= (gcy (add-run-scope w of epoch parent ei)) true))
  (intros hp h)
  (simp only [add-run-scope])
  (have h1 (= (gcy (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))) true))
  (exact (gcy-intro _ (inv-run-ins-fresh w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) (rfl) (gcy-sample w h))
           (gcy-rest-bump _ (gcy-rest-of w h))))
  (have he (= (scope-id (new-scope-row (+ (:next-id w) 1) parent))
              (:next-id (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei))))))
  (rfl)
  (exact (gcy-scope-ins-fresh _ (new-scope-row (+ (:next-id w) 1) parent) he hp h1)))

(a/theorem cy-open-has [w :- World, s :- Nat] (=> (= (scope-open-at w s) true) (= (scope-has w s) true))
  (intro h)
  (cases hf (scope-find w s))
  (case [none] (simp only [scope-open-at hf] at h) (cases h))
  (case [some sc] (exact (tbl-find-has ScopeRow scope-id s sc (:scopes w) hf))))

(a/theorem cy-tsp-has [w :- World, owner :- Nat]
  (= (Bool.or (Nat.beq (task-scope-parent w owner) 0) (scope-has w (task-scope-parent w owner))) true)
  (cases hs (scope-has w owner))
  (case [true] (simp only [task-scope-parent hs Bool.or_true]))
  (case [false] (simp only [task-scope-parent hs Nat.beq_refl Bool.true_or])))

;; ===========================================================================
;; Part D. The copy
;; ===========================================================================

(def GCY (mk-bundle 'gcy [] "gcy-" {'inv-scope-upd ['(fn [s :- ScopeRow] (Eq.refl (:parent s))) 4]}))
(swap! (:renames GCY) assoc 'inv-parts 'gcy-parts 'inv-scope-upd 'gcy-scope-upd 'inv-scope-ins-fresh 'gcy-scope-ins-fresh
       'inv-add-run-scope 'gcy-add-run-scope)
(doseq [o '[inv-run-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-task-upd inv-comp-upd
            inv-set-pins inv-resource-del inv-cleanup-ins inv-act-upd inv-edge-upd inv-drop-cred inv-drop-edges inv-drop-act
            inv-comp-del-unref inv-run-del inv-fork-del]]
  (prim! GCY o nil))
(a/theorem gcy-rest-mark-edge [w :- World, x :- Nat] (= (gcy-rest (mark-edge w x)) (gcy-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem gcy-rest-unmark-edge [w :- World, x :- Nat] (= (gcy-rest (unmark-edge w x)) (gcy-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem gcy-rest-remove-edge [w :- World, x :- Nat] (= (gcy-rest (remove-edge w x)) (gcy-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))
(prim! GCY 'mark-edge-inv-sample '(Eq.trans (gcy-rest-mark-edge w x) R))
(prim! GCY 'unmark-edge-inv-sample '(Eq.trans (gcy-rest-unmark-edge w x) R))
(prim! GCY 'inv-remove-edge '(Eq.trans (gcy-rest-remove-edge w x) R))
(doseq [o '[inv-source-ins-fresh inv-fork-ins-fresh inv-resource-ins-fresh inv-act-ins-fresh inv-comp-ins-fresh inv-task-ins-fresh]]
  (prim! GCY o (list 'gcy-rest-bump (list (symbol (str/replace (subs (name o) 4) "-fresh" "")) 'w 'r) (list 'Eq.trans '(rfl) 'R))))
(prim! GCY 'inv-bump '(gcy-rest-bump w R))
(prim! GCY 'insert-edge-fresh-inv-sample '(gcy-rest-bump (insert-edge w (edge-set-id (:next-id w) e)) (Eq.trans (rfl) R)))
(prim! GCY 'inv-scope-del '(gcy-rest-scope-del w x R))
(prim! GCY 'inv-filter-world '(gcy-rest-filter w K R))

;; callers of add-run-scope: a computation run scope has parent 0 (Z#26), a task run scope its owner
;; scope when that exists (task-scope-parent)
(defn- add-hp [form] (subst-forms (app-of? 'inv-add-run-scope) (fn [y] (concat (take 6 y) ['(Eq.refl true)] (drop 6 y))) form))
(patch! GCY 'inv-start-raw add-hp)
(patch! GCY 'inv-new-run-of add-hp)
(override! GCY 'inv-spawn-rows '[]
  '(a/theorem gcy-spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat), loc :- Bool]
     (=> (= (gcy w) true) (= (gcy (spawn-rows w owner inputs loc)) true))
     (intro h)
     (simp only [spawn-rows])
     (have h1 (= (gcy (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc)))) true))
     (exact (gcy-task-ins-fresh w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc) (rfl) h))
     (exact (gcy-add-run-scope (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc)))
              (:next-id w) 0 (task-scope-parent w owner) 0 (cy-tsp-has w owner) h1))))
;; open-scope: the new explicit scope's parent is the run's current scope, which exists (open-ok)
(override! GCY 't-open-scope-inv '[]
  '(a/theorem t-open-scope-gcy [w :- World, st :- Nat, s :- Nat]
     (=> (= (gcy w) true) (= (gcy (:world (t-open-scope w st s))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t-open-scope ht refuse]) (exact h)
     (cases hg (Bool.and (Nat.beq s (:next-id w)) (open-ok w r)))
     (simp only [t-open-scope ht hg refuse]) (exact h)
     (have hs (= s (:next-id w))) (simp only [Bool.and_eq_true Nat.beq_eq] at hg) (exact (And.left hg))
     (have hc (= (Bool.or (Nat.beq (cur-scope w r) 0) (scope-has w (cur-scope w r))) true))
     (simp only [open-ok Bool.and_eq_true] at hg) (simp only [(And.right (And.right hg)) Bool.or_true])
     (simp only [t-open-scope ht hg accept])
     (exact (gcy-scope-ins-fresh w (ScopeRow.mk s (cur-scope w r) scope-explicit true) hs hc h))))
(lcopy! GCY 'inv-remove-if-empty)
(a/theorem cy-not-true [b :- Bool] (=> (= (Bool.not b) true) (= b false))
  (intro h) (cases b) (rfl) (simp at h))
;; detach (Z#69): the run scope is re-parented under the open scope s, which the guard keeps out of
;; the run scope's subtree (`scope-within w s rs = false`): no cycle
(override! GCY 't-detach-inv '[inv-remove-if-empty]
  '(a/theorem t-detach-gcy [w :- World, k :- Nat, s :- Nat]
     (=> (= (gcy w) true) (= (gcy (:world (t-detach w k s))) true))
     (intro h)
     (cases hf (task-find w k))
     (case [none] (simp only [t-detach hf refuse]) (exact h))
     (case [some t]
       (cases hg (detach-ok w t s))
       (case [false] (simp only [t-detach hf hg refuse]) (exact h))
       (case [true]
         (have hg2 := hg)
         (simp only [detach-ok Bool.and_eq_true] at hg2)
         (have hs2 (= (scope-has w s) true)) (exact (cy-open-has w s (And.left (And.right (And.right hg2)))))
         (have hw (= (scope-within w s (task-run-scope w t)) false)) (exact (cy-not-true _ (And.right (And.right (And.right hg2)))))
         (simp only [t-detach hf hg accept remove-empty-at detach-move])
         (have h1 := (gcy-task-upd w k (task-set-owner s) (task-set-owner-id s) h))
         (exact (gcy-remove-if-empty _ _ (gcy-set-parent (task-upd w k (task-set-owner s)) (task-run-scope w t) s hw hs2 h1)))))))

(lcopy! GCY 'raw-inv)
(lcopy! GCY 'inv-normalize)

;; ===========================================================================
;; Part E. Rule R and the step
;; ===========================================================================

(a/theorem gcy-rule-r-round [w :- World]
  (=> (= (gcy w) true) (= (filter-safe (normalize w)) true) (= (gcy (rule-r-round w)) true))
  (intros h hf) (simp only [rule-r-round]) (rw [rule-r-filter-eq])
  (exact (gcy-filter-world (normalize w) (keep-fn (normalize w)) (gcy-normalize w h) hf)))
(a/theorem gcy-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (gcy w0) true) (= (rr-safe fuel w0) true) (= (gcy (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (gcy-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (gcy-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))
(a/theorem gcy-rule-r [w :- World] (=> (= (gcy w) true) (= (rule-r-safe w) true) (= (gcy (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (gcy-rr-loop (rr-fuel w) w h hs)))

;; the bundle through every step (Rule R's honest hypothesis as in step-inv)
(a/theorem step-gcy [w :- World, it :- Item]
  (=> (= (gcy w) true) (= (rule-r-safe (:world (raw w it))) true) (= (gcy (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (gcy-rule-r (:world (raw w it)) (raw-gcy w it h) hs))))
(a/theorem gcy-empty [] (= (gcy empty-world) true) (rfl))

;; ---- the invariant through every step from a p3b world (no hypothesis); the empty world has it
(a/theorem step-acyc [w :- World, it :- Item]
  (=> (= (p3b w) true) (= (gcy-rest w) true) (= (gcy-rest (:world (world-step w it))) true))
  (intros h hk)
  (exact (gcy-rest-of _ (step-gcy w it (gcy-intro w (ga-sample w (And.left (p3b-parts w h))) hk) (step-rule-r-safe w it h)))))
(a/theorem acyc-empty [] (= (gcy-rest empty-world) true) (rfl))
(a/theorem step-acyclic [w :- World, it :- Item]
  (=> (= (p3b w) true) (= (gcy-rest w) true) (= (scopes-acyclic (:world (world-step w it))) true))
  (intros h hk) (exact (And.right (gcy-rest-parts _ (step-acyc w it h hk)))))
;; no scope reaches itself through the parent fields
(a/theorem step-acyclic-reach [w :- World, it :- Item, y :- Nat]
  (=> (= (p3b w) true) (= (gcy-rest w) true)
      (Reach (scope-up (:world (world-step w it))) (scope-up (:world (world-step w it)) y) y) False)
  (intros h hk r)
  (exact (cy-acyc-of _ (step-acyclic w it h hk) y r)))
