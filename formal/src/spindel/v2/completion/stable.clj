(ns ^:ansatz/lean spindel.v2.completion.stable
  "C1c stage A (Z#70), the proof stage, layer 1: completion is stable. Once task k is complete
  (spindel.v2.ledger `task-complete`: not held, no scope row k + 2) or scope s is (`scope-complete`:
  no row), it stays so through every step, kernel-checked (Init only).

    task-unheld-scope-absent k s w   well-formed w and `task-unheld-scope-absent-rest`: k is below the allocator and task k is not held (no
                task row k, or its result is not none and its run is 0), s is below the allocator and
                there is no scope row s. Parametric bundle (parameters `tk9`, `sc9`), restated over the
                raw transition and normalization by the generic step tree (spindel.v2.pres.tree):
                  - ids are never re-inserted: a task or scope row is only ever inserted at the
                    allocator (`*-ins-fresh`), which is above k and s;
                  - a task row update keeps \"not held\" (the extra argument of `task-unheld-scope-absent-task-upd`): every
                    update but three keeps the result and the run (by rfl); T14's `task-cancel-result`
                    writes a result only over none (`task-unheld-scope-absent-task-tcr`), T13's `task-clear-run` writes run 0
                    (`task-unheld-scope-absent-task-tcl`), and T12's `task-result-row res` keeps run 0 and writes a result
                    whose tag is ok or err (`complete-refused`; overrides `task-unheld-scope-absent-complete-body`,
                    `task-unheld-scope-absent-complete-raw`, `task-unheld-scope-absent-t12-complete`, patch of transition's complete arm, as spindel.v2.inv.copier's GL);
                  - scope rows are updated id-preservingly, deleted (Z#18) or filtered (Rule R): the
                    filter only removes rows.

  Theorems:
    step-task-unheld-scope-absent               task-unheld-scope-absent k s w, rule-r-safe raw -> task-unheld-scope-absent k s (world-step w it)
    task-complete-stable   chain-start w, k + 2 < next-id, task-complete w k -> task-complete (world-step w it) k
    scope-complete-stable  chain-start w, s < next-id, scope-complete w s -> scope-complete (world-step w it) s
  A task row collected while its run scope is still present reads not held, so its completion is then
  just \"no scope row k + 2\" (the second clause), as in the engine (K-SROW still present)."
  (:require [ansatz.core :as a]
            [spindel.v2.pres.frames :as frames]
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
            [spindel.v2.pres.tree :as tree]
            [spindel.v2.pres.part :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.ledger :refer :all]))

;; ===========================================================================
;; Part A. The bundle
;; ===========================================================================

;; a task row holds its owner (ledger `task-held`, per row)
(a/defn th-row [t :- TaskRow] Bool (Bool.or (Nat.beq (:tag (:result t)) res-none) (Bool.not (Nat.beq (:run t) 0))))
(a/defn th-opt [o :- (Option TaskRow)] Bool (match o none false (some t) (th-row t)))

(a/defn task-unheld-scope-absent-rest [tk9 :- Nat, sc9 :- Nat, w :- World] Bool
  (Bool.and (Nat.blt tk9 (:next-id w))
   (Bool.and (Bool.not (th-opt (task-find w tk9)))
    (Bool.and (Nat.blt sc9 (:next-id w)) (Bool.not (scope-has w sc9))))))
(a/defn task-unheld-scope-absent [tk9 :- Nat, sc9 :- Nat, w :- World] Bool (Bool.and (well-formed w) (task-unheld-scope-absent-rest tk9 sc9 w)))

(a/theorem task-unheld-scope-absent-well-formed [tk9 :- Nat, sc9 :- Nat, w :- World] (=> (= (task-unheld-scope-absent tk9 sc9 w) true) (= (well-formed w) true))
  (intro h) (simp only [task-unheld-scope-absent Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem task-unheld-scope-absent-rest-of [tk9 :- Nat, sc9 :- Nat, w :- World] (=> (= (task-unheld-scope-absent tk9 sc9 w) true) (= (task-unheld-scope-absent-rest tk9 sc9 w) true))
  (intro h) (simp only [task-unheld-scope-absent Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem task-unheld-scope-absent-intro [tk9 :- Nat, sc9 :- Nat, w :- World]
  (=> (= (well-formed w) true) (= (task-unheld-scope-absent-rest tk9 sc9 w) true) (= (task-unheld-scope-absent tk9 sc9 w) true))
  (intros h1 h2) (simp only [task-unheld-scope-absent h1 h2 Bool.and_self]))
(a/theorem task-unheld-scope-absent-parts [tk9 :- Nat, sc9 :- Nat, w :- World]
  (=> (= (task-unheld-scope-absent tk9 sc9 w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (task-unheld-scope-absent-well-formed tk9 sc9 w h))))

(a/theorem st-not-of [b :- Bool] (=> (= (Bool.not b) true) (= b false))
  (intro h) (cases b) (rfl) (simp at h))
(a/theorem st-not-intro [b :- Bool] (=> (= b false) (= (Bool.not b) true))
  (intro h) (rw [h]))

(a/theorem task-unheld-scope-absent-rest-parts [tk9 :- Nat, sc9 :- Nat, w :- World]
  (=> (= (task-unheld-scope-absent-rest tk9 sc9 w) true)
      (And (< tk9 (:next-id w)) (And (= (th-opt (task-find w tk9)) false)
       (And (< sc9 (:next-id w)) (= (scope-has w sc9) false)))))
  (intro h)
  (simp only [task-unheld-scope-absent-rest Bool.and_eq_true Nat.blt_eq] at h)
  (exact (And.intro (And.left h) (And.intro (st-not-of _ (And.left (And.right h)))
           (And.intro (And.left (And.right (And.right h))) (st-not-of _ (And.right (And.right (And.right h)))))))))
(a/theorem task-unheld-scope-absent-rest-mk [tk9 :- Nat, sc9 :- Nat, w :- World]
  (=> (< tk9 (:next-id w)) (= (th-opt (task-find w tk9)) false) (< sc9 (:next-id w)) (= (scope-has w sc9) false)
      (= (task-unheld-scope-absent-rest tk9 sc9 w) true))
  (intros h1 h2 h3 h4)
  (have b1 (= (Nat.blt tk9 (:next-id w)) true)) (simp only [Nat.blt_eq]) (exact h1)
  (have b3 (= (Nat.blt sc9 (:next-id w)) true)) (simp only [Nat.blt_eq]) (exact h3)
  (simp only [task-unheld-scope-absent-rest b1 b3 (st-not-intro _ h2) (st-not-intro _ h4) Bool.and_self]))

;; the transport: the allocator grows, \"not held\" and \"no row\" stay
(a/theorem task-unheld-scope-absent-rest-tr [tk9 :- Nat, sc9 :- Nat, w :- World, w2 :- World]
  (=> (<= (:next-id w) (:next-id w2))
      (=> (= (th-opt (task-find w tk9)) false) (= (th-opt (task-find w2 tk9)) false))
      (=> (= (scope-has w sc9) false) (= (scope-has w2 sc9) false))
      (= (task-unheld-scope-absent-rest tk9 sc9 w) true) (= (task-unheld-scope-absent-rest tk9 sc9 w2) true))
  (intros hn ht hs h)
  (have p := (task-unheld-scope-absent-rest-parts tk9 sc9 w h))
  (have a1 (< tk9 (:next-id w2))) (have q := (And.left p)) (omega)
  (have a3 (< sc9 (:next-id w2))) (have q := (And.left (And.right (And.right p)))) (omega)
  (exact (task-unheld-scope-absent-rest-mk tk9 sc9 w2 a1 (ht (And.left (And.right p))) a3 (hs (And.right (And.right (And.right p)))))))

;; ---- the allocator
(a/theorem task-unheld-scope-absent-rest-bump [tk9 :- Nat, sc9 :- Nat, w :- World] (=> (= (task-unheld-scope-absent-rest tk9 sc9 w) true) (= (task-unheld-scope-absent-rest tk9 sc9 (bump w)) true))
  (intro h)
  (have hn (<= (:next-id w) (:next-id (bump w)))) (simp only [bump set-next-id]) (omega)
  (exact (task-unheld-scope-absent-rest-tr tk9 sc9 w (bump w) hn (fn [q :- (= (th-opt (task-find w tk9)) false)] q)
           (fn [q :- (= (scope-has w sc9) false)] q) h)))

;; ---- tasks: a fresh row (id next-id, not tk9) and a row update that keeps \"not held\"
(a/theorem st-lt-ne [a :- Nat, n :- Nat] (=> (< a n) (= (Nat.beq n a) false))
  (intro h) (cases hb (Nat.beq n a)) (rfl) (have e := (Nat.eq_of_beq_eq_true hb)) (omega))

(a/theorem task-unheld-scope-absent-rest-task-ins [tk9 :- Nat, sc9 :- Nat, w :- World, r :- TaskRow]
  (=> (= (task-id r) (:next-id w)) (= (task-unheld-scope-absent-rest tk9 sc9 w) true) (= (task-unheld-scope-absent-rest tk9 sc9 (bump (task-ins w r))) true))
  (intros hr h)
  (have p := (task-unheld-scope-absent-rest-parts tk9 sc9 w h))
  (have hb (= (Nat.beq (task-id r) tk9) false)) (rw [hr]) (exact (st-lt-ne tk9 (:next-id w) (And.left p)))
  (have hn (<= (:next-id w) (:next-id (bump (task-ins w r))))) (simp only [bump set-next-id]) (omega)
  (apply (task-unheld-scope-absent-rest-tr tk9 sc9 w (bump (task-ins w r)) hn _ _ h))
  (intro q) (simp only [task-find bump set-next-id task-ins set-tasks tbl-ins tbl-find hb]) (simp only [task-find] at q) (exact q)
  (intro q) (exact q))

(a/theorem th-find-upd [x :- Nat, f :- (=> TaskRow TaskRow), hf :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                        hk :- (forall [t :- TaskRow] (=> (= (th-row t) false) (= (th-row (f t)) false))), y :- Nat, xs :- (List TaskRow)]
  (=> (= (th-opt (tbl-find task-id y xs)) false) (= (th-opt (tbl-find task-id y (tbl-upd task-id x f xs))) false))
  (induction xs)
  (case [nil] (intro q) (simp only [tbl-upd tbl-find th-opt]))
  (case [cons h t ih]
    (intro q)
    (cases hy (Nat.beq (task-id h) y))
    (case [false]
      (simp only [tbl-find hy] at q)
      (cases hx (Nat.beq (task-id h) x))
      (all_goals (simp only [tbl-upd hx tbl-find (hf h) hy]))
      (all_goals (exact (ih q))))
    (case [true]
      (simp only [tbl-find hy th-opt] at q)
      (cases hx (Nat.beq (task-id h) x))
      (case [false] (simp only [tbl-upd hx tbl-find hy th-opt]) (exact q))
      (case [true] (simp only [tbl-upd hx tbl-find (hf h) hy th-opt]) (exact (hk h q))))))

(a/theorem task-unheld-scope-absent-task-upd [tk9 :- Nat, sc9 :- Nat, w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                         hf :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                         hk :- (forall [t :- TaskRow] (=> (= (th-row t) false) (= (th-row (f t)) false)))]
  (=> (= (task-unheld-scope-absent tk9 sc9 w) true) (= (task-unheld-scope-absent tk9 sc9 (task-upd w x f)) true))
  (intro h)
  (have r := (task-unheld-scope-absent-rest-of tk9 sc9 w h))
  (have hn (<= (:next-id w) (:next-id (task-upd w x f)))) (simp only [task-upd set-tasks]) (omega)
  (have r2 (= (task-unheld-scope-absent-rest tk9 sc9 (task-upd w x f)) true))
  (apply (task-unheld-scope-absent-rest-tr tk9 sc9 w (task-upd w x f) hn _ _ r))
  (intro q) (simp only [task-find task-upd set-tasks]) (simp only [task-find] at q) (exact (th-find-upd x f hf hk tk9 (:tasks w) q))
  (intro q) (exact q)
  (exact (task-unheld-scope-absent-intro tk9 sc9 _ (well-formed-task-upd w x f hf (task-unheld-scope-absent-well-formed tk9 sc9 w h)) r2)))

;; the three updates that write the result or the run
(a/theorem th-tcr [t :- TaskRow] (=> (= (th-row t) false) (= (th-row (task-cancel-result t)) false))
  (intro q)
  (cases hn (Nat.beq (:tag (:result t)) res-none))
  (case [true] (simp only [th-row hn Bool.true_or] at q) (cases q))
  (case [false] (simp only [task-cancel-result hn]) (exact q)))
(a/theorem th-tcl [t :- TaskRow] (=> (= (th-row t) false) (= (th-row (task-clear-run t)) false))
  (intro q)
  (simp only [th-row Bool.or_eq_false_iff] at q)
  (simp only [th-row task-clear-run (And.left q) Nat.beq_refl Bool.not_true Bool.or_self]))
(a/theorem th-trr [res :- RunResult] (=> (= (Nat.beq (:tag res) res-none) false)
                                         (forall [t :- TaskRow] (=> (= (th-row t) false) (= (th-row (task-result-row res t)) false))))
  (intros hr t q)
  (simp only [th-row Bool.or_eq_false_iff] at q)
  (simp only [th-row task-result-row hr (And.right q) Bool.or_self]))

(a/theorem task-unheld-scope-absent-task-tcr [tk9 :- Nat, sc9 :- Nat, w :- World, x :- Nat]
  (=> (= (task-unheld-scope-absent tk9 sc9 w) true) (= (task-unheld-scope-absent tk9 sc9 (task-upd w x task-cancel-result)) true))
  (intro h) (exact (task-unheld-scope-absent-task-upd tk9 sc9 w x task-cancel-result task-cancel-result-id th-tcr h)))
(a/theorem task-unheld-scope-absent-task-tcl [tk9 :- Nat, sc9 :- Nat, w :- World, x :- Nat]
  (=> (= (task-unheld-scope-absent tk9 sc9 w) true) (= (task-unheld-scope-absent tk9 sc9 (task-upd w x task-clear-run)) true))
  (intro h) (exact (task-unheld-scope-absent-task-upd tk9 sc9 w x task-clear-run task-clear-run-id th-tcl h)))

;; ---- scopes: id-preserving update, deletion, a fresh row, the filter
(a/theorem task-unheld-scope-absent-rest-scope-upd [tk9 :- Nat, sc9 :- Nat, w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow),
                               hf :- (forall [s :- ScopeRow] (= (scope-id (f s)) (scope-id s)))]
  (=> (= (task-unheld-scope-absent-rest tk9 sc9 w) true) (= (task-unheld-scope-absent-rest tk9 sc9 (scope-upd w x f)) true))
  (intro h)
  (have hn (<= (:next-id w) (:next-id (scope-upd w x f)))) (simp only [scope-upd set-scopes]) (omega)
  (apply (task-unheld-scope-absent-rest-tr tk9 sc9 w (scope-upd w x f) hn _ _ h))
  (intro q) (exact q)
  (intro q) (simp only [scope-has scope-upd set-scopes (tbl-has-upd ScopeRow scope-id x sc9 f hf (:scopes w))]) (simp only [scope-has] at q) (exact q))

(a/theorem st-has-del [A :- Type, idf :- (=> A Nat), x :- Nat, y :- Nat, xs :- (List A)]
  (=> (= (tbl-has idf y xs) false) (= (tbl-has idf y (tbl-del idf x xs)) false))
  (induction xs)
  (case [nil] (intro q) (simp only [tbl-del tbl-has]))
  (case [cons h t ih]
    (intro q)
    (cases hy (Nat.beq (idf h) y))
    (case [true] (simp only [tbl-has hy] at q) (cases q))
    (case [false]
      (simp only [tbl-has hy] at q)
      (cases hx (Nat.beq (idf h) x))
      (all_goals (simp only [tbl-del hx tbl-has hy]))
      (all_goals (exact (ih q))))))

(a/theorem task-unheld-scope-absent-rest-scope-del [tk9 :- Nat, sc9 :- Nat, w :- World, x :- Nat]
  (=> (= (task-unheld-scope-absent-rest tk9 sc9 w) true) (= (task-unheld-scope-absent-rest tk9 sc9 (scope-del w x)) true))
  (intro h)
  (have hn (<= (:next-id w) (:next-id (scope-del w x)))) (simp only [scope-del set-scopes]) (omega)
  (apply (task-unheld-scope-absent-rest-tr tk9 sc9 w (scope-del w x) hn _ _ h))
  (intro q) (exact q)
  (intro q) (simp only [scope-has scope-del set-scopes]) (simp only [scope-has] at q) (exact (st-has-del ScopeRow scope-id x sc9 (:scopes w) q)))

(a/theorem task-unheld-scope-absent-rest-scope-ins [tk9 :- Nat, sc9 :- Nat, w :- World, r :- ScopeRow]
  (=> (= (scope-id r) (:next-id w)) (= (task-unheld-scope-absent-rest tk9 sc9 w) true) (= (task-unheld-scope-absent-rest tk9 sc9 (bump (scope-ins w r))) true))
  (intros hr h)
  (have p := (task-unheld-scope-absent-rest-parts tk9 sc9 w h))
  (have hb (= (Nat.beq (scope-id r) sc9) false)) (rw [hr]) (exact (st-lt-ne sc9 (:next-id w) (And.left (And.right (And.right p)))))
  (have hn (<= (:next-id w) (:next-id (bump (scope-ins w r))))) (simp only [bump set-next-id]) (omega)
  (apply (task-unheld-scope-absent-rest-tr tk9 sc9 w (bump (scope-ins w r)) hn _ _ h))
  (intro q) (exact q)
  (intro q) (simp only [scope-has bump set-next-id scope-ins set-scopes tbl-ins tbl-has hb]) (simp only [scope-has] at q) (exact q))

(a/theorem task-unheld-scope-absent-rest-filter [tk9 :- Nat, sc9 :- Nat, w :- World, K :- (=> Nat Bool)]
  (=> (= (task-unheld-scope-absent-rest tk9 sc9 w) true) (= (task-unheld-scope-absent-rest tk9 sc9 (filter-world K w)) true))
  (intro h)
  (have hn (<= (:next-id w) (:next-id (filter-world K w)))) (simp only [filter-world]) (omega)
  (apply (task-unheld-scope-absent-rest-tr tk9 sc9 w (filter-world K w) hn _ _ h))
  (intro q)
  (cases hk (K tk9))
  (case [false] (simp only [task-find filter-world (keep-find-out TaskRow K task-id tk9 (:tasks w) hk) th-opt]))
  (case [true] (simp only [task-find filter-world (keep-find-in TaskRow K task-id tk9 (:tasks w) hk)]) (simp only [task-find] at q) (exact q))
  (intro q) (simp only [scope-has filter-world tbl-has-keep]) (simp only [scope-has] at q) (simp only [q Bool.and_false]))

;; ---- edge marks (match on the edge row): frames

;; ===========================================================================
;; Part B. The copy
;; ===========================================================================

(def GST (mk-bundle 'task-unheld-scope-absent '[tk9 :- Nat, sc9 :- Nat] "task-unheld-scope-absent-"
           {'well-formed-task-upd ['(fn [t :- TaskRow, q :- (= (th-row t) false)] q) 4]}))
(swap! (:renames GST) assoc 'well-formed-parts 'task-unheld-scope-absent-parts 'well-formed-task-upd 'task-unheld-scope-absent-task-upd)

(defpart GST :reads '[next-id scopes tasks])
(frames/frame-theorem! 'task-unheld-scope-absent-rest-mark-edge 'task-unheld-scope-absent-rest 'well-formed-mark-edge)
(frames/frame-theorem! 'task-unheld-scope-absent-rest-unmark-edge 'task-unheld-scope-absent-rest 'well-formed-unmark-edge)
(frames/frame-theorem! 'task-unheld-scope-absent-rest-remove-edge 'task-unheld-scope-absent-rest 'well-formed-remove-edge)
(doseq [o '[well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-resource-ins-fresh well-formed-act-ins-fresh well-formed-comp-ins-fresh well-formed-run-ins-fresh]]
  (prim! GST o (list 'task-unheld-scope-absent-rest-bump 'tk9 'sc9 (list (symbol (str/replace (subs (name o) 12) "-fresh" "")) 'w 'r) (list 'Eq.trans '(rfl) 'R))))
(prim! GST 'well-formed-task-ins-fresh '(task-unheld-scope-absent-rest-task-ins tk9 sc9 w r h0 R))
(prim! GST 'well-formed-scope-ins-fresh '(task-unheld-scope-absent-rest-scope-ins tk9 sc9 w r h0 R))
(prim! GST 'well-formed-scope-upd '(task-unheld-scope-absent-rest-scope-upd tk9 sc9 w x f hf R))
(prim! GST 'well-formed-bump '(task-unheld-scope-absent-rest-bump tk9 sc9 w R))
(prim! GST 'well-formed-insert-edge-fresh '(task-unheld-scope-absent-rest-bump tk9 sc9 (insert-edge w (edge-set-id (:next-id w) e)) (Eq.trans (rfl) R)))
(prim! GST 'well-formed-scope-del '(task-unheld-scope-absent-rest-scope-del tk9 sc9 w x R))
(prim! GST 'well-formed-filter-world '(task-unheld-scope-absent-rest-filter tk9 sc9 w K R))

;; task-unheld-scope-absent on the generic tree (spindel.v2.pres.tree): its table. Its own proofs follow.
(tree/part! GST
  :over '{well-formed-complete-body task-unheld-scope-absent-complete-body
          well-formed-complete-raw  task-unheld-scope-absent-complete-raw
          well-formed-t12-complete           task-unheld-scope-absent-t12-complete
          well-formed-retire-one    task-unheld-scope-absent-retire-one}
  ;; ---- sites: T14's debtor side writes ::cancelled over a result none only; T13 clears the run
  :sites '{[well-formed-task-upd task-cancel-result] (task-unheld-scope-absent-task-tcr tk9 sc9 w x h0)
           [well-formed-task-upd task-clear-run]     (task-unheld-scope-absent-task-tcl tk9 sc9 w x h0)}
  ;; ---- facts from the path: T12 writes a result (ok or err, never none)
  :ctx '{well-formed-complete-body [(= (Nat.beq (:tag res) res-none) false)]
         well-formed-complete-raw  [(= (Nat.beq (:tag res) res-none) false)]
         well-formed-t12-complete           [(= (res-tag-ok tag) true)]}
  :pass '{well-formed-transition-complete {well-formed-t12-complete [(refused-tag-ok w st tag hc)]}})   ; complete not refused

;; T12: the result written is ok or err (complete-refused), so run 0 with a result stays not held
(tree/restate! GST '[well-formed-nat-fold well-formed-fire-edge well-formed-cancel-res well-formed-settle well-formed-comp-upd])
(a/theorem task-unheld-scope-absent-complete-body [tk9 :- Nat, sc9 :- Nat, w :- World, r :- RunRow, res :- RunResult]
  (=> (= (Nat.beq (:tag res) res-none) false) (= (task-unheld-scope-absent tk9 sc9 w) true) (= (task-unheld-scope-absent tk9 sc9 (:world (complete-body w r res))) true))
  (intros ht h)
  (cases hc (comp-find w (:of r)))
  (case [none]
    (cases hk (task-find w (:of r)))
    (case [none] (simp only [complete-body hc hk]) (exact h))
    (case [some kt]
      (simp only [complete-body hc hk complete-task])
      (exact (task-unheld-scope-absent-nat-fold tk9 sc9 (fire-edge res) (task-unheld-scope-absent-fire-edge tk9 sc9 res) _ _
               (task-unheld-scope-absent-cancel-res tk9 sc9 _ r (task-unheld-scope-absent-task-upd tk9 sc9 w (:id kt) (task-result-row res) (task-result-row-id res)
                                             (th-trr res ht) h))))))
  (case [some c]
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [complete-body hc he]) (exact h))
    (case [true]
      (simp only [complete-body hc he complete-comp])
      (exact (task-unheld-scope-absent-settle tk9 sc9 _ (:id c) _ (task-unheld-scope-absent-cancel-res tk9 sc9 _ r
               (task-unheld-scope-absent-comp-upd tk9 sc9 w (:id c) (comp-result-row res (:epoch r)) (comp-result-row-id res (:epoch r))
                 (comp-result-row-pending res (:epoch r)) h)))))))
(tree/restate! GST '[well-formed-finalize-if-final well-formed-run-cascade well-formed-retire-after well-formed-run-upd])
(a/theorem task-unheld-scope-absent-complete-raw [tk9 :- Nat, sc9 :- Nat, w :- World, r :- RunRow, res :- RunResult]
  (=> (= (Nat.beq (:tag res) res-none) false) (= (task-unheld-scope-absent tk9 sc9 w) true) (= (task-unheld-scope-absent tk9 sc9 (complete-raw w r res)) true))
  (intros ht h)
  (have h0 (= (task-unheld-scope-absent tk9 sc9 (run-upd w (:id r) run-complete-row)) true))
  (exact (task-unheld-scope-absent-run-upd tk9 sc9 w (:id r) run-complete-row run-complete-row-id h))
  (simp only [complete-raw])
  (exact (task-unheld-scope-absent-finalize-if-final tk9 sc9 _ (:of r) (task-unheld-scope-absent-run-cascade tk9 sc9 _ _ (task-unheld-scope-absent-retire-after tk9 sc9 _ (:id r)
           (task-unheld-scope-absent-complete-body tk9 sc9 _ r res ht h0))))))
(a/theorem task-unheld-scope-absent-t12-complete [tk9 :- Nat, sc9 :- Nat, w :- World, st :- Nat, tag :- Nat, v :- Nat]
  (=> (= (res-tag-ok tag) true) (= (task-unheld-scope-absent tk9 sc9 w) true) (= (task-unheld-scope-absent tk9 sc9 (:world (t12-complete w st tag v))) true))
  (intros hg h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t12-complete ht refuse]) (exact h)
  (cases hn (run-normal r))
  (simp only [t12-complete ht hn refuse]) (exact h)
  (simp only [t12-complete ht hn accept])
  (exact (task-unheld-scope-absent-complete-raw tk9 sc9 w r (RunResult.mk tag v) (tag-ok-none tag hg) h)))
(tree/restate! GST '[well-formed-retire-pre well-formed-run-cascade])
(a/theorem task-unheld-scope-absent-retire-one [tk9 :- Nat, sc9 :- Nat, v :- Nat, w :- World, rid :- Nat]
  (=> (= (task-unheld-scope-absent tk9 sc9 w) true) (= (task-unheld-scope-absent tk9 sc9 (retire-one v w rid)) true))
  (intro h)
  (cases hf (run-find w rid))
  (case [none] (simp only [retire-one hf]) (exact h))
  (case [some r]
    (have hp := (task-unheld-scope-absent-retire-pre tk9 sc9 w r h))
    
    (cases hf1 (run-find (retire-pre w r) rid))
    (case [none] (simp only [retire-one hf hf1]) (exact hp))
    (case [some r1]
      (have hm1 := (retire-r1-mem w r r1 rid hf1))
      (have hn1 := (retire-r1-noact w r r1 rid hf hf1))
      (have ht1 := (task-final-res-tag (retire-pre w r) (:of r1) v))
      (cases ha (Bool.and (run-alive r1) (run-of-local (retire-pre w r) r1)))
      (case [true] (simp only [retire-one hf hf1 ha]) (exact (task-unheld-scope-absent-complete-raw tk9 sc9 _ r1 _ ht1 hp)))
      (case [false] (simp only [retire-one hf hf1 ha t13-retire]) (exact (task-unheld-scope-absent-run-cascade tk9 sc9 _ _ hp))))))

(tree/restate! GST '[well-formed-raw well-formed-normalize])

;; ===========================================================================
;; Part C. Rule R and the step
;; ===========================================================================

(a/theorem task-unheld-scope-absent-rule-r-round [tk9 :- Nat, sc9 :- Nat, w :- World]
  (=> (= (task-unheld-scope-absent tk9 sc9 w) true) (= (filter-safe (normalize w)) true) (= (task-unheld-scope-absent tk9 sc9 (rule-r-round w)) true))
  (intros h hf) (simp only [rule-r-round]) (rw [rule-r-filter-eq])
  (exact (task-unheld-scope-absent-filter-world tk9 sc9 (normalize w) (keep-fn (normalize w)) (task-unheld-scope-absent-normalize tk9 sc9 w h) hf)))
(a/theorem task-unheld-scope-absent-rule-r-loop [tk9 :- Nat, sc9 :- Nat, fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (task-unheld-scope-absent tk9 sc9 w0) true) (= (rounds-safe-loop fuel w0) true) (= (task-unheld-scope-absent tk9 sc9 (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (task-unheld-scope-absent-rule-r-round tk9 sc9 w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (task-unheld-scope-absent-rule-r-round tk9 sc9 w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))
(a/theorem task-unheld-scope-absent-rule-r [tk9 :- Nat, sc9 :- Nat, w :- World]
  (=> (= (task-unheld-scope-absent tk9 sc9 w) true) (= (rule-r-safe w) true) (= (task-unheld-scope-absent tk9 sc9 (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (task-unheld-scope-absent-rule-r-loop tk9 sc9 (rule-r-fuel w) w h hs)))

(a/theorem step-task-unheld-scope-absent [tk9 :- Nat, sc9 :- Nat, w :- World, it :- Item]
  (=> (= (task-unheld-scope-absent tk9 sc9 w) true) (= (rule-r-safe (:world (raw w it))) true) (= (task-unheld-scope-absent tk9 sc9 (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (task-unheld-scope-absent-rule-r tk9 sc9 (:world (raw w it)) (task-unheld-scope-absent-raw tk9 sc9 w it h) hs))))

;; ===========================================================================
;; Part D. Stability of the ledger
;; ===========================================================================

(a/theorem th-opt-held [w :- World, k :- Nat] (= (task-held w k) (th-opt (task-find w k)))
  (cases hf (task-find w k))
  (case [none] (simp only [task-held hf th-opt]))
  (case [some t] (simp only [task-held hf th-opt th-row])))

;; id 0 is no row (ids are positive), so task 0 is not held
(a/theorem st-held0 [w :- World] (=> (= (well-formed w) true) (= (th-opt (task-find w 0)) false))
  (intro h)
  (cases hf (task-find w 0))
  (case [none] (simp only [th-opt]))
  (case [some t]
    (have hh := (tbl-find-has TaskRow task-id 0 t (:tasks w) hf))
    (have hm (= (nat-mem 0 (tbl-ids task-id (:tasks w))) true)) (rw [nat-mem-ids]) (exact hh)
    (have m2 (= (nat-mem 0 (all-ids w)) true))
    (simp only [all-ids nat-mem-app hm Bool.true_or Bool.or_true])
    (have r := (all-nat-mem (id-in-range (:next-id w)) 0 (all-ids w) (ids-below-of w h) m2))
    (simp only [id-in-range Bool.and_eq_true Nat.blt_eq] at r)
    (have l := (And.left r)) (omega)))

;; Theorem: a complete task (k a task id: its run scope k + 2 was allocated) stays complete
(a/theorem task-complete-stable [w :- World, it :- Item, k :- Nat]
  (=> (= (chain-start w) true) (< (+ k 2) (:next-id w)) (= (task-complete w k) true)
      (= (task-complete (:world (world-step w it)) k) true))
  (intros h hk hc)
  (have hs := (acts-parked-well-formed w (And.left (chain-start-parts w h))))
  (simp only [task-complete Bool.and_eq_true] at hc)
  (have a1 (< k (:next-id w))) (omega)
  (have a2 (= (th-opt (task-find w k)) false)) (rw [← (th-opt-held w k)]) (exact (st-not-of _ (And.left hc)))
  (have r := (task-unheld-scope-absent-rest-mk k (+ k 2) w a1 a2 hk (st-not-of _ (And.right hc))))
  (have g := (step-task-unheld-scope-absent k (+ k 2) w it (task-unheld-scope-absent-intro k (+ k 2) w hs r) (step-rule-r-safe w it h)))
  (have p := (task-unheld-scope-absent-rest-parts k (+ k 2) _ (task-unheld-scope-absent-rest-of k (+ k 2) _ g)))
  (simp only [task-complete task-srow (th-opt-held _ k) (And.left (And.right p)) (And.right (And.right (And.right p))) Bool.not_false Bool.and_self]))

;; Theorem: a complete scope (s allocated) stays complete
(a/theorem scope-complete-stable [w :- World, it :- Item, s :- Nat]
  (=> (= (chain-start w) true) (< s (:next-id w)) (= (scope-complete w s) true)
      (= (scope-complete (:world (world-step w it)) s) true))
  (intros h hs hc)
  (have hi := (acts-parked-well-formed w (And.left (chain-start-parts w h))))
  (simp only [scope-complete] at hc)
  (have a1 (< 0 (:next-id w))) (omega)
  (have r := (task-unheld-scope-absent-rest-mk 0 s w a1 (st-held0 w hi) hs (st-not-of _ hc)))
  (have g := (step-task-unheld-scope-absent 0 s w it (task-unheld-scope-absent-intro 0 s w hi r) (step-rule-r-safe w it h)))
  (have p := (task-unheld-scope-absent-rest-parts 0 s _ (task-unheld-scope-absent-rest-of 0 s _ g)))
  (simp only [scope-complete (And.right (And.right (And.right p))) Bool.not_false]))
