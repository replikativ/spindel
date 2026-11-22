(ns spindel.v2.ledger
  "C1c stage A (spec Z#70, engine 1aac850): the task/scope completion ledger, derived from the scope tree.

  A task is complete when it is done, its run has retired (T13) and its run scope was removed (Z#18) or never
  materialized; a scope is complete when its row is removed. The engine keeps the flags K-COMPLETE / S-COMPLETE
  (set once) and the pairing K-SROW / S-TASK; the model derives all of them:
    - the run scope of task k is the scope k + 2 (T4's allocation order: task K, run K + 1, run scope K + 2;
      `spawn-rows`), created eagerly. The engine materializes it on first use; one never materialized owns
      nothing, and T13 (`t13-retire-with-subtree`'s `remove-if-empty`) removes the model's row in the retiring step, which is
      exactly when the engine completes a task with no K-SROW. So no separate clause is needed;
    - held = the task row's result is none or its run is unretired (rule.clj `task-held-in` without the scope
      test). A task id with no row is not held: the model keeps no kind for a removed id, so the caller knows k is a
      task id (layer 2's host joins record the id they were admitted for; the oracle remembers the ids it saw);
    - the root scope is never removed (Z#56), so it is never complete.
  Theorems (proof stage, notes/history/PLAN.md): stability, spindel.v2.completion.stable (`task-complete-stable`,
  `scope-complete-stable`); a quiet world has every task (id /= 0) and every non-root scope complete,
  spindel.v2.completion.quiet-world (`quiet-task-complete`, `quiet-scope-complete`, from spindel.v2.completion.open-scopes); layer 2, layer2/sys.clj
  (`complete-born-ledger`, `born-complete-delivered`)."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]))

;; the run scope of task k (T4: task K, run K + 1, run scope K + 2)
(a/defn task-srow [k :- Nat] Nat (+ k 2))

;; task k holds its owner: not done, or its run not yet retired (Z#56; rule.clj `task-held-in`)
(a/defn task-held [w :- World, k :- Nat] Bool
  (match (task-find w k)
    [none false]
    [(some t) (Bool.or (Nat.beq (:tag (:result t)) res-none) (Bool.not (Nat.beq (:run t) 0)))]))

;; Z#70: done, run retired, run scope removed (or never materialized: removed at the retirement)
(a/defn task-complete [w :- World, k :- Nat] Bool
  (Bool.and (Bool.not (task-held w k)) (Bool.not (scope-has w (task-srow k)))))

;; Z#70: a scope is complete when its row is removed
(a/defn scope-complete [w :- World, s :- Nat] Bool (Bool.not (scope-has w s)))
