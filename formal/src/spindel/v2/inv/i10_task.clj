(ns spindel.v2.inv.i10-task
  "The part i10-task, I10 task part (spec §6 I10), through the step on the generic tree
  (spindel.v2.pres.tree; formal/notes/proof-layout.md §4.5, §5c), kernel-checked (Init only).

  Theorems:
    step-i10-task            acts-parked w, i10-task w, rule-r-safe raw -> i10-task (world-step w it)
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
            [spindel.v2.pres.part :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.pres.tree :as tree]))

;; ---------------------------------------------------------------------------
;; The part i10-task: I10, task part
;;
;; 1. In words: (a) every run's `of` is below the allocator; (b) a run R of a task K is K.run; (c) a
;;    task without a result has an alive run. `i10-task-rest` is `i10-task-keys-ok` over the run keys, the task keys
;;    and the allocator (copier, Part A).
;; 2. View: runs, tasks, next-id (`defpart GL` in the copier). Finer, column level: the key lists
;;    `i10-task-view` (run key id/of/alive, task key id/run/done, next-id), frame `i10-task-rest-frame`.
;; 3. Exempt form: `i10-task-exempt k`, (c) may fail for task k. Break `i10-task-exempt-kill` (a run made done); repairs
;;    `i10-task-task-done-x` (the task gets its result), `i10-task-of-i10-task-exempt-comp` (k is a computation),
;;    `i10-task-of-i10-task-exempt-find` (no task k); transport `i10-task-exempt-frame`. Uniform names `gl-exempt-<role>`.
;; 4. Cells: a run or task update that keeps the keys (the bundle's extra argument: `rfl` at every
;;    site not listed below), fresh inserts and `bump` (`i10-task-rest-bump`), frames from the view
;;    (`defpart GL`). Sites, below: the run updates whose row function changes the run key.
;; 5. Deferred within a step, and content (:over below): T14's local part (break at the run's
;;    cancel, repair in `cancel-debtor`), T12 (break at the run's completion, repair at
;;    `complete-task`), T13 (`retire-rest`), new runs (T4 with its task, T5 and T11 of a computation).
;;    The facts these take from the path (:ctx, :own, :pass below): the run is a row, it is dead,
;;    the result is not none (transition's refusal guard), the computation exists (carried through T11's
;;    cancel and cut by the bundle `comp-exists`).
;; 6. Companions: `acts-parked` (`step-i10-task`: acts-alive for Rule R's filter).

(tree/part! GL
  :sites '{[well-formed-run-upd run-wake]      (i10-task-run-upd w x run-wake hf run-wake-run-key h0)        ; resume (Z#50): key kept, by lemma
           [well-formed-run-upd run-park-row]  (i10-task-run-upd-up w x run-park-row hf                  ; park: alive goes up,
                                         (fn [r :- RunRow] (Eq.refl (RunKey.mk (:id r) (:of r) true))) h0)  ;   (c) gains a witness
           [well-formed-run-upd run-tick-park] (i10-task-run-upd-up w x run-tick-park hf                 ; take, parked: same
                                         (fn [r :- RunRow] (Eq.refl (RunKey.mk (:id r) (:of r) true))) h0)}
  :over '{well-formed-cancel-run-local i10-task-cancel-run-local-hand   ; T14 local: break i10-task-exempt-kill, repair in debtor-side
          well-formed-complete-raw     i10-task-complete-raw-hand       ; T12: break i10-task-exempt-kill, repair at complete-task
          well-formed-retire-run     i10-task-retire-run-hand       ; T13: clear the task's run, delete the dead run (retire-rest)
          well-formed-spawn-rows       i10-task-spawn-rows-hand         ; T4: a task and its alive run, inserted together
          well-formed-start-raw        i10-task-start-raw            ; T5: a new run of an existing computation (i10-task-comp-run-hand)
          well-formed-new-run-of       i10-task-new-run-of}          ; T11: same
  :ctx '{well-formed-cancel-run-local [(List.Mem r (:runs w))]                         ; the cancelled run is a row
         well-formed-retire-run     [(List.Mem r (:runs w)) (= (run-alive r) false)] ; the retired run is a dead row
         well-formed-complete-raw     [(List.Mem r (:runs w))                          ; the completed run is a row,
                               (= (Nat.beq (:tag res) res-none) false)]        ;   its result is not none
         well-formed-start-raw        [(= (comp-has w (:id c)) true)]                  ; the new run's `of` is a computation
         well-formed-new-run-of       [(= (comp-has w (:id c)) true)]}                 ; same
  :own '{well-formed-t12-complete          [hg (= (res-tag-ok tag) true)]                       ; transition's refusal guard: an ok or err tag
         well-formed-dispatch-raw [hc (= (comp-has w (:id c)) true)]}                  ; T11's computation exists
  :pass '{well-formed-job-apply  {well-formed-cancel-run-local [(tbl-find-mem RunRow run-id rid r (:runs w) hf)]     ; run-find found it
                          well-formed-retire-run     [(tbl-find-mem RunRow run-id rid r (:runs w) hf)
                                                (retirable-dead r ha)]}                              ; retirable: done
          well-formed-transition-complete {well-formed-t12-complete [(refused-tag-ok w st tag hc)]}                                  ; complete not refused
          well-formed-t12-complete        {well-formed-complete-raw [(And.left (tok-facts w st r ht)) (tag-ok-res tag v hg)]}  ; the token's run
          well-formed-retire-one {well-formed-complete-raw [(retire-r1-mem w r r1 rid hf1) (task-final-res-tag _ _ v)]} ; found; err result
          well-formed-t5-start         {well-formed-start-raw [(find-comp-has w cid c hc)]}                                 ; comp-find found it
          well-formed-t11-dispatch        {well-formed-dispatch-raw [(find-comp-has w cid c hc)]}}                             ; same
  ;; T11: comp-has (:id c) survives cancel-pred, cut-suffix and consume-entry, which keep the
  ;; computation ids (the bundle `comp-exists` of the copier: a frame of the comps table at column level)
  :src '{well-formed-dispatch-raw
         (a/theorem well-formed-dispatch-raw [w :- World, c :- CompRow]
           (=> (= (comp-has w (:id c)) true) (= (well-formed w) true) (= (well-formed (dispatch-raw w c)) true))
           (intros hc h)
           (have h1 := (well-formed-cancel-pred w c h))
           (have k1 := (comp-exists-cancel-pred (:id c) w c (comp-exists-intro (:id c) w (base-of w h) hc)))
           (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
           (simp only [dispatch-raw he])
           (exact (well-formed-new-run-of _ c 0 (comp-exists-rest-of (:id c) _ (comp-exists-cut-suffix (:id c) _ (:id c) false 0 0 k1))
                    (well-formed-cut-suffix _ (:id c) false 0 0 h1)))
           (simp only [dispatch-raw he])
           (exact (well-formed-new-run-of _ c _
                    (comp-exists-rest-of (:id c) _ (comp-exists-consume-entry (:id c) _ e (comp-exists-cut-suffix (:id c) _ (:id c) true (:at e) (:id e) k1)))
                    (well-formed-consume-entry _ e (well-formed-cut-suffix _ (:id c) true (:at e) (:id e) h1)))))})

;; ---- T14's local part (cancel): the run is done, its task gets err ::cancelled

(tree/restate! GL '[well-formed-fire-task-cancelled well-formed-clear-rtasks well-formed-invalidate-dependents well-formed-fire-waits-cancelled])

(a/theorem i10-task-cancel-run-local-hand [w :- World, r :- RunRow, rep :- Bool]
  (=> (List.Mem r (:runs w)) (= (i10-task w) true) (= (i10-task (cancel-run-local w r rep)) true))
  (intros hm h)
  (have hs := (i10-task-well-formed w h))
  (have hms := (cancel-mid-well-formed w r hs))
  (have hx (= (i10-task-exempt (:of r) (cancel-mid w r)) true))
  (rw [(i10-task-exempt-frame (:of r) _ _ (cancel-mid-frame w r))])
  (exact (i10-task-exempt-kill w r run-cancel-row (fn [q :- RunRow] (Eq.refl (run-key-down (run-key q)))) hs hm h))
  (have e (= (cancel-run-local w r rep) (cancel-debtor rep (cancel-mid w r) r))) (rfl)
  (rw [e])
  (cases hc (Bool.and rep (comp-has (cancel-mid w r) (:of r))))
  (case [true]
    (simp only [cancel-debtor hc])
    (simp only [Bool.and_eq_true] at hc)
    (exact (i10-task-of-i10-task-exempt-comp _ (:of r) hms hx (And.right hc))))
  (case [false]
    (simp only [cancel-debtor hc])
    (cases hf (comp-find (cancel-mid w r) (:of r)))
    (case [none]
      (simp only [debtor-side hf])
      (exact (i10-task-clear-rtasks _ (:of r) (i10-task-fire-task-cancelled _ (:of r)
               (i10-task-task-done-x _ (:of r) task-cancel-result task-cancel-result-id task-key-cancel-result hms hx)))))
    (case [some c]
      (have hg := (i10-task-of-i10-task-exempt-comp _ (:of r) hms hx (tbl-find-has CompRow comp-id (:of r) c _ hf)))
      (cases he (Nat.beq (:epoch r) (:epoch c)))
      (case [false] (simp only [debtor-side hf he]) (exact hg))
      (case [true]
        (simp only [debtor-side hf he])
        (exact (i10-task-invalidate-dependents _ (:of r) (i10-task-fire-waits-cancelled _ (:of r) hg)))))))

;; ---- T12 (complete): the run is done, its task gets the result (ok/err, never none)

(tree/restate! GL '[well-formed-settle well-formed-cancel-res well-formed-fire-edge well-formed-nat-fold])

(a/theorem i10-task-complete-body-mid [w :- World, r :- RunRow, res :- RunResult]
  (=> (List.Mem r (:runs w)) (= (Nat.beq (:tag res) res-none) false) (= (i10-task w) true)
      (= (i10-task (:world (complete-body (run-upd w (:id r) run-complete-row) r res))) true))
  (intros hm ht h)
  (have hs := (i10-task-well-formed w h))
  (have hs1 := (well-formed-run-upd w (:id r) run-complete-row run-complete-row-id hs))
  (have hx := (i10-task-exempt-kill w r run-complete-row (fn [q :- RunRow] (Eq.refl (run-key-down (run-key q)))) hs hm h))
  (cases hc (comp-find (run-upd w (:id r) run-complete-row) (:of r)))
  (case [none]
    (cases hk (task-find (run-upd w (:id r) run-complete-row) (:of r)))
    (case [none] (simp only [complete-body hc hk]) (exact (i10-task-of-i10-task-exempt-find _ (:of r) hs1 hx hk)))
    (case [some k]
      (simp only [complete-body hc hk complete-task])
      (have ek (= (task-id k) (:of r))) (exact (tbl-find-id TaskRow task-id (:of r) k _ hk))
      (have hx2 (= (i10-task-exempt (:id k) (run-upd w (:id r) run-complete-row)) true))
      (have ek2 (= (:id k) (:of r))) (exact ek)
      (rw [ek2]) (exact hx)
      (exact (i10-task-nat-fold (fire-edge res) (i10-task-fire-edge res) _ _
               (i10-task-cancel-res _ r (i10-task-task-done-x _ (:id k) (task-result-row res) (task-result-row-id res)
                                    (fn [q :- TaskRow] (task-key-result-row res q ht)) hs1 hx2))))))
  (case [some c]
    (have hg := (i10-task-of-i10-task-exempt-comp _ (:of r) hs1 hx (tbl-find-has CompRow comp-id (:of r) c _ hc)))
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [complete-body hc he]) (exact hg))
    (case [true]
      (simp only [complete-body hc he complete-comp])
      (exact (i10-task-settle _ (:id c) _ (i10-task-cancel-res _ r
               (i10-task-comp-upd _ (:id c) (comp-result-row res (:epoch r)) (comp-result-row-id res (:epoch r))
                 (comp-result-row-pending res (:epoch r)) hg)))))))

(tree/restate! GL '[well-formed-retire-after well-formed-run-cascade well-formed-finalize-if-final])

(a/theorem i10-task-complete-raw-hand [w :- World, r :- RunRow, res :- RunResult]
  (=> (List.Mem r (:runs w)) (= (Nat.beq (:tag res) res-none) false) (= (i10-task w) true) (= (i10-task (complete-raw w r res)) true))
  (intros hm ht h)
  (simp only [complete-raw])
  (exact (i10-task-finalize-if-final _ (:of r) (i10-task-run-cascade _ _ (i10-task-retire-after _ (:id r) (i10-task-complete-body-mid w r res hm ht h))))))

;; ---- the raw step, and Rule R (the filter keeps every run that is not done: normalized, they are live)

(tree/restate! GL '[well-formed-raw well-formed-normalize])

(a/theorem i10-task-rule-r-round [w :- World]
  (=> (= (acts-alive w) true) (= (i10-task w) true) (= (filter-safe (normalize w)) true) (= (i10-task (rule-r-round w)) true))
  (intros ha h hf)
  (simp only [rule-r-round])
  (exact (i10-task-rule-r-filter-hand (normalize w) (normalized-ok w (i10-task-well-formed w h) ha) (i10-task-normalize w h) hf)))

(a/theorem i10-task-rule-r-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (acts-alive w0) true) (= (i10-task w0) true) (= (rounds-safe-loop fuel w0) true)
                            (= (i10-task (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 ha h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (i10-task-rule-r-round w0 ha h hs)))
  (case [cons x f ih]
    (intros w0 ha h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (i10-task-rule-r-round w0 ha h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false]
      (simp only [ho] at hs) (simp only [rule-r-loop ho])
      (exact (ih (rule-r-round w0) (acts-alive-round w0 (i10-task-well-formed w0 h) ha) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))

(a/theorem i10-task-rule-r [w :- World]
  (=> (= (acts-alive w) true) (= (i10-task w) true) (= (rule-r-safe w) true) (= (i10-task (rule-r w)) true))
  (intros ha h hs)
  (simp only [rule-r-safe] at hs) (simp only [rule-r])
  (exact (i10-task-rule-r-loop (rule-r-fuel w) w ha h hs)))

;; the bundle is preserved by every step (hypotheses of step-acts)
(a/theorem step-i10-task [w :- World, it :- Item]
  (=> (= (acts-parked w) true) (= (i10-task w) true) (= (rule-r-safe (:world (raw w it))) true) (= (i10-task (:world (world-step w it))) true))
  (intros hg h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true]
    (have e2 := (step-accepted w it ha)) (rw [e2])
    (exact (i10-task-rule-r (:world (raw w it)) (raw-acts-alive w it hg) (i10-task-raw w it h) hs))))

(a/theorem i10-task-empty [] (= (i10-task empty-world) true) (rfl))

;; Theorem: literal I10, task part (every run of a task K is K.run; a task without result has
;; its run, not done), through every step
(a/theorem step-lit-i10-task [w :- World, it :- Item]
  (=> (= (acts-parked w) true) (= (i10-task w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (inv-i10-task (:world (world-step w it))) true))
  (intros hg h hs) (exact (inv-i10-task-of _ (step-i10-task w it hg h hs))))
