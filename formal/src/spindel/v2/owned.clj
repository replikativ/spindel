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


;; The three are layer-1 items (spindel.v2.step 45-47, engine.clj `t-own`, `t-owned-done`, `t-drain`): world-step
;; runs them, then Rule R. Each is refused (world unchanged) when it has nothing to do.
;; +1: the marker of the child cell m owned by s, with the parent's fresh id. The early branch (released, or the
;; owner closed) never counts.
(a/defn own-world [w :- World, s :- Nat, m :- Nat] World (:world (world-step w (Item.own s m))))
;; `[:owned-done s child]`: the marker `child` of s goes, then remove-scope-if-empty! at s (Z#18) and Rule R. Without
;; that marker the world is unchanged (the engine posts the item for a counted child only, question 18b).
(a/defn owned-done-world [w :- World, s :- Nat, c :- Nat] World (:world (world-step w (Item.owned-done s c))))
;; `[:normalize]`: the inherited markers `ids` go, then Z#18 at each of their owners and Rule R. Without any of them
;; the world is unchanged (the engine logs it only with W-NORMALIZE non-empty)
(a/defn drain-world [w :- World, ids :- (List Nat)] World (:world (world-step w (Item.drain ids))))

(a/defn marker-ids [w :- World] (List Nat) (tbl-ids fork-id (:forks w)))
(a/defn no-markers [w :- World] Bool (forks-nil (:forks w)))
(a/theorem no-markers-nil [w :- World] (=> (= (no-markers w) true) (= (forks-nil (:forks w)) true)) (intro h) (exact h))
(a/theorem nil-no-markers [w :- World] (=> (= (forks-nil (:forks w)) true) (= (no-markers w) true)) (intro h) (exact h))

;; a refused internal item leaves the world as it is
(a/theorem internal-refused [w :- World, it :- Item]
  (=> (= (host-item it) false) (= (:accepted (raw0 w it)) false) (= (:world (world-step w it)) w))
  (intros hh ha)
  (have r (= (:accepted (raw w it)) false))
  (simp only [raw post raw0g host-shut hh Bool.false_and Bool.and_false ha])
  (rw [(step-refuse w it r)]))

;; a world without markers is left as it is by owned-done and the drain; a released one by own
(a/theorem owned-done-none [w :- World, s :- Nat, c :- Nat] (=> (= (forks-nil (:forks w)) true) (= (owned-done-world w s c) w))
  (intro h)
  (have hf (= (:forks w) (List.nil ForkRow)))
  (cases e (:forks w)) (case [nil] (rfl)) (case [cons a t] (rw [e] at h) (simp [forks-nil] at h))
  (simp only [owned-done-world])
  (apply (internal-refused w (Item.owned-done s c) (rfl)))
  (simp only [raw0 t-owned-done hf tbl-any refuse]))
(a/theorem drain-none [w :- World, ids :- (List Nat)] (=> (= (forks-nil (:forks w)) true) (= (drain-world w ids) w))
  (intro h)
  (have hf (= (:forks w) (List.nil ForkRow)))
  (cases e (:forks w)) (case [nil] (rfl)) (case [cons a t] (rw [e] at h) (simp [forks-nil] at h))
  (simp only [drain-world])
  (apply (internal-refused w (Item.drain ids) (rfl)))
  (simp only [raw0 t-drain hf tbl-any refuse]))
(a/theorem own-released [w :- World, s :- Nat, m :- Nat] (=> (= (:released w) true) (= (own-world w s m) w))
  (intro h)
  (simp only [own-world])
  (apply (internal-refused w (Item.own s m) (rfl)))
  (simp only [raw0 t-own own-ok h Bool.not_true Bool.false_and refuse]))
