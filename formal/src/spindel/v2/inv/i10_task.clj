(ns spindel.v2.inv.i10-task
  "The part gl, I10 task part (spec §6 I10), through the step on the generic tree
  (spindel.v2.pres.tree; formal/notes/proof-layout.md §4.5, §5c), kernel-checked (Init only).

  Theorems:
    step-gl            ga w, gl w, rule-r-safe raw -> gl (world-step w it)
    step-lit-i10-task  ... -> inv-i10-task (world-step w it)   (literal I10, task part)

  The part's predicate, view, cells and break/repair lemmas are in spindel.v2.inv.copier (Parts A
  and C); this namespace is its table in the tree and its step."
  (:require [ansatz.core :as a]
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
            [spindel.v2.pres.tree :as tree]))

;; ---------------------------------------------------------------------------
;; The part gl: I10, task part
;;
;; 1. In words: (a) every run's `of` is below the allocator; (b) a run R of a task K is K.run; (c) a
;;    task without a result has an alive run. `gl-rest` is `l10k` over the run keys, the task keys
;;    and the allocator (copier, Part A).
;; 2. View: runs, tasks, next-id (`defpart GL` in the copier). Finer, column level: the key lists
;;    `kw` (run key id/of/alive, task key id/run/done, next-id), frame `gl-rest-kw`.
;; 3. Exempt form: `glx k`, (c) may fail for task k. Break `glx-kill` (a run made done); repairs
;;    `gl-task-done-x` (the task gets its result), `gl-of-glx-comp` (k is a computation),
;;    `gl-of-glx-find` (no task k); transport `glx-kw`. Uniform names `gl-exempt-<role>`.
;; 4. Cells: a run or task update that keeps the keys (the bundle's extra argument: `rfl` at every
;;    site not listed below), fresh inserts and `bump` (`gl-rest-bump`), frames from the view
;;    (`defpart GL`). Sites, below: the run updates whose row function changes the run key.
;; 5. Deferred within a step, and content (:over below): T14's local part (break at the run's
;;    cancel, repair in `cancel-debtor`), T12 (break at the run's completion, repair at
;;    `complete-task`), T13 (`retire-rest`), new runs (T4 with its task, T5 and T11 of a computation).
;;    The facts these need from the path (the run is a row, it is dead, the result is not none, the
;;    computation exists) are contexts of the tree (`tree/contexts`), passed at the call sites.
;; 6. Companions: `ga` (`step-gl`: acts-alive for Rule R's filter).

(tree/part! GL
  :sites '{[inv-run-upd run-wake]      (gl-run-upd w x run-wake hf run-wake-rkey h0)        ; resume (Z#50): key kept, by lemma
           [inv-run-upd run-park-row]  (gl-run-upd-up w x run-park-row hf                  ; park: alive goes up,
                                         (fn [r :- RunRow] (Eq.refl (RKey.mk (:id r) (:of r) true))) h0)  ;   (c) gains a witness
           [inv-run-upd run-tick-park] (gl-run-upd-up w x run-tick-park hf                 ; take, parked: same
                                         (fn [r :- RunRow] (Eq.refl (RKey.mk (:id r) (:of r) true))) h0)}
  :over '{inv-cancel-run-local gl-cancel-run-local-o   ; T14 local: break glx-kill, repair in debtor-side
          inv-complete-raw     gl-complete-raw-o       ; T12: break glx-kill, repair at complete-task
          inv-retire-local     gl-retire-local-o       ; T13: clear the task's run, delete the dead run (retire-rest)
          inv-spawn-rows       gl-spawn-rows-o         ; T4: a task and its alive run, inserted together
          inv-start-raw        gl-start-raw            ; T5: a new run of an existing computation (gl-comp-run-o)
          inv-new-run-of       gl-new-run-of})         ; T11: same

;; ---- T14's local part (cancel): the run is done, its task gets err ::cancelled

(tree/restate! GL '[inv-fire-task-cancelled inv-clear-rtasks inv-invalidate-dependents inv-fire-waits-cancelled])

(a/theorem gl-cancel-run-local-o [w :- World, r :- RunRow, rep :- Bool]
  (=> (List.Mem r (:runs w)) (= (gl w) true) (= (gl (cancel-run-local w r rep)) true))
  (intros hm h)
  (have hs := (gl-sample w h))
  (have hms := (cancel-mid-sample w r hs))
  (have hx (= (glx (:of r) (cancel-mid w r)) true))
  (rw [(glx-kw (:of r) _ _ (cancel-mid-kw w r))])
  (exact (glx-kill w r run-cancel-row (fn [q :- RunRow] (Eq.refl (rk-down (rkey q)))) hs hm h))
  (have e (= (cancel-run-local w r rep) (cancel-debtor rep (cancel-mid w r) r))) (rfl)
  (rw [e])
  (cases hc (Bool.and rep (comp-has (cancel-mid w r) (:of r))))
  (case [true]
    (simp only [cancel-debtor hc])
    (simp only [Bool.and_eq_true] at hc)
    (exact (gl-of-glx-comp _ (:of r) hms hx (And.right hc))))
  (case [false]
    (simp only [cancel-debtor hc])
    (cases hf (comp-find (cancel-mid w r) (:of r)))
    (case [none]
      (simp only [debtor-side hf])
      (exact (gl-clear-rtasks _ (:of r) (gl-fire-task-cancelled _ (:of r)
               (gl-task-done-x _ (:of r) task-cancel-result task-cancel-result-id tkey-cancel-result hms hx)))))
    (case [some c]
      (have hg := (gl-of-glx-comp _ (:of r) hms hx (tbl-find-has CompRow comp-id (:of r) c _ hf)))
      (cases he (Nat.beq (:epoch r) (:epoch c)))
      (case [false] (simp only [debtor-side hf he]) (exact hg))
      (case [true]
        (simp only [debtor-side hf he])
        (exact (gl-invalidate-dependents _ (:of r) (gl-fire-waits-cancelled _ (:of r) hg)))))))

;; ---- T12 (complete): the run is done, its task gets the result (ok/err, never none)

(tree/restate! GL '[inv-settle inv-cancel-res inv-fire-edge nat-fold-inv])

(a/theorem gl-complete-body-mid [w :- World, r :- RunRow, res :- RunResult]
  (=> (List.Mem r (:runs w)) (= (Nat.beq (:tag res) res-none) false) (= (gl w) true)
      (= (gl (:world (complete-body (run-upd w (:id r) run-complete-row) r res))) true))
  (intros hm ht h)
  (have hs := (gl-sample w h))
  (have hs1 := (inv-run-upd w (:id r) run-complete-row run-complete-row-id hs))
  (have hx := (glx-kill w r run-complete-row (fn [q :- RunRow] (Eq.refl (rk-down (rkey q)))) hs hm h))
  (cases hc (comp-find (run-upd w (:id r) run-complete-row) (:of r)))
  (case [none]
    (cases hk (task-find (run-upd w (:id r) run-complete-row) (:of r)))
    (case [none] (simp only [complete-body hc hk]) (exact (gl-of-glx-find _ (:of r) hs1 hx hk)))
    (case [some k]
      (simp only [complete-body hc hk complete-task])
      (have ek (= (task-id k) (:of r))) (exact (tbl-find-id TaskRow task-id (:of r) k _ hk))
      (have hx2 (= (glx (:id k) (run-upd w (:id r) run-complete-row)) true))
      (have ek2 (= (:id k) (:of r))) (exact ek)
      (rw [ek2]) (exact hx)
      (exact (nat-fold-gl (fire-edge res) (gl-fire-edge res) _ _
               (gl-cancel-res _ r (gl-task-done-x _ (:id k) (task-result-row res) (task-result-row-id res)
                                    (fn [q :- TaskRow] (tkey-result-row res q ht)) hs1 hx2))))))
  (case [some c]
    (have hg := (gl-of-glx-comp _ (:of r) hs1 hx (tbl-find-has CompRow comp-id (:of r) c _ hc)))
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [complete-body hc he]) (exact hg))
    (case [true]
      (simp only [complete-body hc he complete-comp])
      (exact (gl-settle _ (:id c) _ (gl-cancel-res _ r
               (gl-comp-upd _ (:id c) (comp-result-row res (:epoch r)) (comp-result-row-id res (:epoch r))
                 (comp-result-row-pending res (:epoch r)) hg)))))))

(tree/restate! GL '[inv-retire-after inv-run-cascade inv-fin-if-final])

(a/theorem gl-complete-raw-o [w :- World, r :- RunRow, res :- RunResult]
  (=> (List.Mem r (:runs w)) (= (Nat.beq (:tag res) res-none) false) (= (gl w) true) (= (gl (complete-raw w r res)) true))
  (intros hm ht h)
  (simp only [complete-raw])
  (exact (gl-fin-if-final _ (:of r) (gl-run-cascade _ _ (gl-retire-after _ (:id r) (gl-complete-body-mid w r res hm ht h))))))

;; ---- the raw step, and Rule R (the filter keeps every run that is not done: normalized, they are live)

(tree/restate! GL '[raw-inv inv-normalize])

(a/theorem gl-rule-r-round [w :- World]
  (=> (= (acts-alive w) true) (= (gl w) true) (= (filter-safe (normalize w)) true) (= (gl (rule-r-round w)) true))
  (intros ha h hf)
  (simp only [rule-r-round])
  (exact (gl-rule-r-filter-o (normalize w) (normalized-ok w (gl-sample w h) ha) (gl-normalize w h) hf)))

(a/theorem gl-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (acts-alive w0) true) (= (gl w0) true) (= (rr-safe fuel w0) true)
                            (= (gl (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 ha h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (gl-rule-r-round w0 ha h hs)))
  (case [cons x f ih]
    (intros w0 ha h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (gl-rule-r-round w0 ha h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false]
      (simp only [ho] at hs) (simp only [rr-loop ho])
      (exact (ih (rule-r-round w0) (acts-alive-round w0 (gl-sample w0 h) ha) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))

(a/theorem gl-rule-r [w :- World]
  (=> (= (acts-alive w) true) (= (gl w) true) (= (rule-r-safe w) true) (= (gl (rule-r w)) true))
  (intros ha h hs)
  (simp only [rule-r-safe] at hs) (simp only [rule-r])
  (exact (gl-rr-loop (rr-fuel w) w ha h hs)))

;; the bundle is preserved by every step (hypotheses of step-acts)
(a/theorem step-gl [w :- World, it :- Item]
  (=> (= (ga w) true) (= (gl w) true) (= (rule-r-safe (:world (raw w it))) true) (= (gl (:world (world-step w it))) true))
  (intros hg h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true]
    (have e2 := (step-accepted w it ha)) (rw [e2])
    (exact (gl-rule-r (:world (raw w it)) (raw-acts-alive w it hg) (raw-gl w it h) hs))))

(a/theorem gl-empty [] (= (gl empty-world) true) (rfl))

;; Theorem: literal I10, task part (every run of a task K is K.run; a task without result has
;; its run, not done), through every step
(a/theorem step-lit-i10-task [w :- World, it :- Item]
  (=> (= (ga w) true) (= (gl w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (inv-i10-task (:world (world-step w it))) true))
  (intros hg h hs) (exact (gl-i10-task _ (step-gl w it hg h hs))))
