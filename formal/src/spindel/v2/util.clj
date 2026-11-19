(ns spindel.v2.util
  "Small generic definitions shared by layer 2 (kernel-checked, Init only).

    fupd f k v    function update at a Nat key: (fupd f k v) x = v if x = k, else f x
    fupd-same     (fupd f k v) k = v
    fupd-other    x /= k -> (fupd f k v) x = f x
    nbeq-ne       a /= b -> Nat.beq a b = false

  Used by spindel.v2.sys (a system's cells and publications are functions Nat -> Cell / Pub). These
  were part of spindel.v2.cow, the forward-map physical model that spindel.v2.mvcc superseded; cow is
  retired (see git history before this namespace) and only these four are kept, with unchanged names
  and statements. spindel.v2.mvcc has its own copies (`mv-upd`, `mv-nbeq-ne`) and needs nothing here."
  (:require [ansatz.core :as a]))

(a/load-init!)

;; function update at a Nat key
(a/defn fupd [A :- Type :implicit, f :- (=> Nat A), k :- Nat, v :- A] (=> Nat A)
  (fn [x :- Nat] (if (Nat.beq x k) v (f x))))

(a/theorem nbeq-ne [a :- Nat, b :- Nat] (=> (Not (= a b)) (= (Nat.beq a b) false))
  (intro hne)
  (cases hab (Nat.beq a b))
  (rfl)
  (exact (absurd (Nat.eq_of_beq_eq_true hab) hne)))

(a/theorem fupd-same [A :- Type :implicit, f :- (=> Nat A), k :- Nat, v :- A]
  (= (fupd f k v k) v)
  (simp only [fupd Nat.beq_refl]))

(a/theorem fupd-other [A :- Type :implicit, f :- (=> Nat A), k :- Nat, v :- A, x :- Nat]
  (=> (Not (= x k)) (= (fupd f k v x) (f x)))
  (intro h) (simp only [fupd (nbeq-ne x k h)]))
