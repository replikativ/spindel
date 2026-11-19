(ns spindel.v2.local
  "Z#77 fork-local tasks: the closure invariants of `.internal/fork-local-design.md` §7 as executable predicates.

    loc1  LOC1, fork-local closure: every task owned by a fork-local scope is fork-local (`loc1-task`), and every run
          of a fork-local task has a fork-local run scope (`loc1-run`)
    loc2  LOC2: no fork marker is owned by a fork-local scope

  Theorem: `loc1-runs`, the run half of LOC1 holds in every world (a run of a fork-local task makes its own run scope
  fork-local, `scope-local` reading the scope itself first). The task half and LOC2 are invariants of the step (T4's
  inheritance, the detach guard, the refused `(fork)` effect), not proved here: their preservation through every
  item is the open part of the Z#77 model stage (notes/history/PLAN.md); the oracle evaluates both on every replayed world of
  the fork-local samples (oracle_test `fork-local-closure`)."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.lit]))

(a/load-init!)

(a/defn loc1-task [w :- World, t :- TaskRow] Bool (Bool.or (Bool.not (scope-local w (:owner t))) (:local t)))
(a/defn loc1-run [w :- World, r :- RunRow] Bool (Bool.or (Bool.not (run-of-local w r)) (scope-local w (:scope r))))
(a/defn loc1 [w :- World] Bool (Bool.and (tbl-all (loc1-task w) (:tasks w)) (tbl-all (loc1-run w) (:runs w))))
(a/defn loc2-fork [w :- World, f :- ForkRow] Bool (Bool.not (scope-local w (:owner f))))
(a/defn loc2 [w :- World] Bool (tbl-all (loc2-fork w) (:forks w)))

(a/theorem any-of-mem [A :- Type, p :- (=> A Bool), x :- A, xs :- (List A)]
  (=> (List.Mem x xs) (= (p x) true) (= (tbl-any p xs) true))
  (induction xs)
  (case [nil] (intros m hp) (cases m))
  (case [cons h t ih]
    (intros m hp)
    (cases m)
    (case [head] (simp only [tbl-any hp Bool.true_or]))
    (case [tail m2] (simp only [tbl-any (ih m2 hp) Bool.or_true]))))
;; Theorem (LOC1, run half): every run of a fork-local task has a fork-local run scope, in every world
(a/theorem loc1-runs [w :- World] (= (tbl-all (loc1-run w) (:runs w)) true)
  (apply (all-of-mem RunRow (loc1-run w) (:runs w)))
  (intros r m)
  (cases hl (run-of-local w r))
  (case [false] (simp only [loc1-run hl Bool.not_false Bool.true_or]))
  (case [true]
    (have hr (= (run-scope-of-local w (:scope r) r) true))
    (simp only [run-scope-of-local Nat.beq_refl Bool.true_and]) (exact hl)
    (have hs (= (local-run-scope w (:scope r)) true))
    (simp only [local-run-scope]) (exact (any-of-mem RunRow (run-scope-of-local w (:scope r)) r (:runs w) m hr))
    (simp only [loc1-run scope-local tbl-any hs Bool.true_or Bool.or_true])))
