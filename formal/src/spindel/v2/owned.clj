(ns spindel.v2.owned
  "C1c stage B (c1c design v4 L2, questions 15-18): owned forks, as layer-1 world operations.

  The count. Engine `W-OWNED-N` {scope -> n}: +1 in own-child!'s counting branch of the `(fork)` effect
  (the world is not released and the owner, `current-scope!`, is open; question 18a: a host fork and an
  activated instance are owned weakly by the root and never counted), -1 by the internal item
  `[:owned-done s child]` when the child completes or is collected. In the model the count is the
  layer-1 fork markers (`ForkRow`, state.clj, empty before stage B): one row per counted child, `id` the
  child world's id (the parent's fresh id, `alloc-id!` in fork-world*, question 18d), `child` the
  child's cell, `owner` the scope. So `W-OWNED-N[s]` = the number of markers owned by s.

  Normalization. A fork is a value copy of its parent's world, so it holds the parent's markers: the
  parent's counted ones and its own still undrained inherited ones, which is v4's union (the source's
  pending `W-NORMALIZE` and its scopes with a non-zero count). In the child they are inherited markers
  (spindel.v2.sys `Cell.norm`), keep reasons until drained (question 17: `s ∉ W-NORMALIZE` is a
  condition of remove-scope-if-empty!). `[:normalize]` drains them, once, at the first turn or the
  activation; a host item may come first (the fast path, question 15).

  Keep reason. A marker keeps itself and its owner scope's ancestor chain (spindel.v2.retain
  `fork-keep`, storage): Z#18's `subtree-empty` already refuses a subtree that owns a marker
  (`fork-owned-in`), and Rule R's filter (a model encoding: the engine has no filter over scope rows,
  question 17) keeps the owner while it has one.

  Completion (questions 15, 16): a world completes only without markers (`no-markers`, spindel.v2.sys
  `complete-ready`): W-OWNED-N all zero and W-NORMALIZE empty. The drain and owned-done both end with
  maybe-complete! (the system operation `sys-complete` after them)."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.engine :refer :all]))

;; the counting branch of own-child! at the `(fork)` effect: not released, the owner scope open
(a/defn own-ok [w :- World, s :- Nat] Bool (Bool.and (Bool.not (:released w)) (scope-open-at w s)))

;; +1: the marker of the child cell m owned by s, with the parent's fresh id (the child world's id). The
;; early branch (released, or the owner closed) releases the child at once and never counts it.
(a/defn own-world [w :- World, s :- Nat, m :- Nat] World
  (if (own-ok w s) (bump (fork-ins w (ForkRow.mk (:next-id w) m s))) w))

(a/defn marker-ids [w :- World] (List Nat) (tbl-ids fork-id (:forks w)))
(a/defn no-markers [w :- World] Bool (match (:forks w) [nil true] [(cons h t) false]))

;; `[:owned-done s child]`: the marker `child` of s goes, then remove-scope-if-empty! at s (Z#18) and Rule R
;; (the parents of a removed scope: the filter). Without that marker the world is unchanged (the engine
;; posts the item for a counted child only, question 18b).
(a/defn marker-of [s :- Nat, c :- Nat, f :- ForkRow] Bool (Bool.and (Nat.beq (:id f) c) (Nat.beq (:owner f) s)))
(a/defn owned-done-world [w :- World, s :- Nat, c :- Nat] World
  (if (tbl-any (marker-of s c) (:forks w)) (rule-r (remove-empty-at (fork-del w c) s)) w))

;; `[:normalize]`: the inherited markers `ids` go, then Z#18 at each of their owners and Rule R
(a/defn owners-in [ids :- (List Nat), fs :- (List ForkRow)] (List Nat)
  (match fs [nil (List.nil Nat)]
         [(cons h t) (if (reach-mem (:id h) ids) (List.cons Nat (:owner h) (owners-in ids t)) (owners-in ids t))]))
(a/defn drain-world [w :- World, ids :- (List Nat)] World
  (rule-r (nat-fold remove-empty-at (nat-fold fork-del w ids) (owners-in ids (:forks w)))))
