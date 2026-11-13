(ns spindel.v2.rule
  "Rule R normalization and the cancel family (spec v1.5.1 §3.3, T13 with Z#18, T14, T15 with
  Z#6, T16, T10 one level), and the model's step `world-step w item = Rule R ∘ raw`,
  kernel-checked (Init only).

  Edits (Parts A-D): `drop-edges w p` keeps the edges with p and resyncs every computation's
  pending (exact pending without per-edge bookkeeping; `inv-drop-edges`). T14's local part
  `cancel-run-local w r rep`: act := done, mode := unwinding; R's activations are removed with
  every edge they are the creditor of (wait and savepoint members, wait edges on resources too,
  Z#6; dep members stay with C) by `drop-act`; armed resources -> cancelling; cleanup[R]
  (re)created; unless `rep` (cancel(R, replace), Y#2) the debtor side: wait creditors of R.of get
  err ::cancelled through T9 (`fire-edge`), a task without result completes with err ::cancelled,
  and for a computation's current run every armed dep edge on it is an invalidation (epoch step).
  T13 `retire-local` (Z#18): (1) C.run := none when R is C.run, (2) T16 local part on R.scope's
  subtree (every scope closed, every source owned there closed and finalized by T10), (3) run
  row and cleanup[R] removed, (4) the subtree's scopes removed when it is empty.

  Cascade (Part E): a worklist of `Job`s (jcancel r rep | jretire r | jclose s) with list fuel
  (`casc-fuel`: initial jobs x (1 + #runs) + #runs x (2 + 2 #runs) + 1; acting jobs are guarded:
  a cancel acts on a non-done run, a retire on a retirable one). A cancel queues the cancels of
  the work owned by R.scope's subtree and then T13 on R; T13 and T16 queue the cancels of the
  subtree's remaining work. `casc-done` says the worklist emptied (not proved; tests check it).

  Transitions (Part F): `t14-cancel w r rep`, `t16-close-scope w s`, `retire-full w r` (T13),
  `t15-full w z` (T15 with the Z#6 token `ack-tok-ok`: resource row and no edge with debtor z).
  step.clj's `dispatch` keeps its shallow T13 (`close-scope-shallow`) for its own lemmas; the
  model's step uses `raw` = dispatch with T15 := t15-full.

  The model's step `world-step` (raw part + Rule R) and its theorems live in
  spindel.v2.engine, after the transitions that create runs.

  Rule R (Part G): `normalize w` = `norm-loop (norm-fuel w') w'` with w' = `detach w`; a round
  (`norm-round`) recomputes live, cancels (T14, cascading) every non-done run outside live,
  demotes every non-idle computation outside live (the live list of the round's start), and
  detaches orphans. `demote`: cancel C's non-done runs and the runs of the tasks in its basis,
  remove its dep edges (validity from them), then idle (I7 shape) if it has a result, handles > 0
  or is the body entity of a cleanup entry (tombstone), else removed with every edge naming it.
  `detach`: a source or task whose owner (/= 0) is no existing scope or computation gets owner
  0; a detached source is closed and finalized (T10). The loop stops when `normalized` holds;
  fuel = #non-done runs + #non-idle computations + 1 (`norm-measure` + 1). `rule-r w` =
  `rule-r-filter (normalize w)`; `world-step w it` = accept (rule-r raw-world) when raw accepts,
  else the raw refusal.

  Theorems:
    inv-drop-edges, inv-cancel-run-local, inv-retire-local, inv-close-scope-local,
    inv-job-apply, inv-cascade (fuel induction), t14-inv/-refuse, t16-inv/-refuse,
    t15-full-inv/-refuse/-l4, inv-demote, inv-detach, inv-norm-round, inv-norm-loop,
    inv-normalize                inv-sample is preserved by every edit and by the loop
    normalized-runs              normalized w, r in runs, r not done -> in-live w r.id
    normalized-comps             normalized w, c in comps, c not idle -> in-live w c.id
    inv-filter-world             inv-sample w, filter-safe-k K w -> inv-sample (filter-world K w)
    inv-rule-r-filter, inv-rule-r, step-inv
                                 inv-sample w, filter-safe (normalize raw-world) ->
                                 inv-sample (:world (world-step w it))
    rule-r-filter-normalized     converged before/after -> the filter keeps `normalized`
    step-i3                      accepted, converged before/after the filter -> I3
    step-normalized, step-i4     ... and normalized (normalize raw-world) -> the step's world is
                                 normalized; every run that is not done is in its live set (I4)
    raw-inv, raw-refuse, raw-l4  the raw part (raw-l4: invalid token -> not accepted, Z#10)
    step-refuse, step-l4, step-accepted
                                 refusal -> (refuse w); invalid token -> (refuse w) (L4)
  Honest hypotheses (Bool flags the tests check after every step): `live-converged` before and
  after the filter (fuel sufficiency of live is not proved), `normalized` of the normalized
  world (the loop's flag: its termination measure is not proved; tests check that every round
  strictly decreases `norm-measure`), and `filter-safe` (a kept edge keeps its endpoints, a
  marked edge with a kept creditor is kept: it follows from I7 and the §3.2 edges in the worlds
  the transitions build, but inv-sample does not carry I7).

  Readings (spec ambiguities, see the report):
    1. Work owned by S: the non-done runs of the tasks owned by a scope of S's subtree
       (descendants by parent links). Computations owned there are not cancelled (demand only).
    2. T14's children: the work owned by R.scope's whole subtree (explicit scopes R opened and
       the child run scopes included), not only R.scope's direct tasks.
    3. T16 closes every scope of the subtree, run scopes included.
    4. A cancelled task without result completes with err ::cancelled (`cancelled-code`, the
       reserved Nat 1) and is final (Z#39): its wait creditors and the dep edges on it fire
       (T9), then T10. Computation, current run: wait creditors also get err ::cancelled, dep creditors an
       epoch step (`invalidate`, never a delivery). Stale run: nothing.
    5. The head finalizer's cleanup slice is not represented: `slice` is unchanged by cancel; a
       cancelled run without finalizers, resources and slice retires at once.
    6. Subtree empty: all its scopes closed, and no task, fork marker or run scope in it.
       Closed sources and computations owned there do not hold it; sources are detached by
       normalization.
    7. Validity entry of a removed dep edge (Z#24): (debtor, seen), the version the edge last
       consumed; an edge that never consumed one gives (0, 0), and debtor 0 never exists, so
       the validity fails.
    8. Detach is state-based and runs before the loop and in every round; owners removed by
       the final filter (step 3) are detached by the next Rule R.
    9. T10 cascades (Z#25): `finalize-debtor` = worklist `fin-loop` with list fuel. Z#32:
       computations are never final (`comp-final` is false), so the cascade never adds a
       computation and T10 applies to tasks, deferreds and closed sources only.
   10. Only armed resources go to cancelling; fired ones wait for their acknowledgement (I9).
   11. Demotion and normalization cancel with an ordinary cancel (debtor side included).
       Demotion steps C.epoch when C.run is current (Z#42), so a run kept in cleanup is stale.
   15. cleanup[R] retains the run scope's current ancestors as storage (Z#38, Z#52: recomputed
       by every Rule R pass, `scope-ancestors` in retain's `cleanup-contrib`).
   12. T13 step 1 clears C.run or K.run (Z#25).
   13. Detach (Z#23) also gives a computation whose owner is removed owner := 0 (not cancelled).
   14. Rule R (Z#25): rounds of normalize + filter until a round leaves no orphan (`rr-loop`,
       list fuel 1 + #ids); `rule-r w = rule-r-round (rule-r-pre w)` (`rule-r-eq`); the step
       theorems take their hypotheses about the last round (`rule-r-pre`), and `rule-r-safe`
       is filter-safe for every round.
   16. Z#53: closing a source (T16/T13 `close-local`) or detaching it (Rule R step 3) first wakes
       its armed wait edges and its armed dep edges that are activation members (`wake-closed`,
       T9 with the closed source's `deb-result`: its value, or err ::closed = `closed-code` 2
       for a mailbox, semaphore or undelivered deferred), then T10 removes the remaining armed
       dep edges. Tracks (non-member dep edges) are not invalidated by a close."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]))


;; ===========================================================================
;; Part A. Generic edits: an edge filter that keeps pending exact
;; ===========================================================================

(a/defn comp-resync [es :- (List EdgeRow), c :- CompRow] CompRow
  (comp-set-pending (marked-in (:id c) es) c))
(a/defn comps-resync [es :- (List EdgeRow), cs :- (List CompRow)] (List CompRow)
  (match cs [nil (List.nil CompRow)]
         [(cons h t) (List.cons CompRow (comp-resync es h) (comps-resync es t))]))

;; keep the edges with p; every computation's pending is the count of its marked in-edges
;; that remain (= the old count minus the removed marked ones, under pending-exact)
(a/defn drop-edges [w :- World, p :- (=> EdgeRow Bool)] World
  (set-comps (set-edges w (tbl-filter p (:edges w))) (comps-resync (tbl-filter p (:edges w)) (:comps w))))

(a/theorem resync-exact [es :- (List EdgeRow), cs :- (List CompRow)]
  (= (tbl-all (comp-exact es) (comps-resync es cs)) true)
  (induction cs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [comps-resync tbl-all])
  (simp [comps-resync tbl-all ih comp-exact comp-resync comp-set-pending Nat.beq_refl]))

(a/theorem resync-ids [es :- (List EdgeRow), cs :- (List CompRow)]
  (= (tbl-ids comp-id (comps-resync es cs)) (tbl-ids comp-id cs))
  (induction cs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [comps-resync tbl-ids])
  (simp [comps-resync tbl-ids ih comp-id comp-resync comp-set-pending]))

(a/theorem resync-has [es :- (List EdgeRow), cs :- (List CompRow), y :- Nat]
  (= (tbl-has comp-id y (comps-resync es cs)) (tbl-has comp-id y cs))
  (induction cs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [comps-resync tbl-has])
  (simp [comps-resync tbl-has ih comp-id comp-resync comp-set-pending]))

(a/theorem edge-ok-resync [es :- (List EdgeRow), cs :- (List CompRow), ts :- (List TaskRow),
                           xs :- (List SourceRow), as :- (List ActRow), rs :- (List ResRow), e :- EdgeRow]
  (= (edge-ok (comps-resync es cs) ts xs as rs e) (edge-ok cs ts xs as rs e))
  (simp only [edge-ok cred-ok deb-ok resync-has]))

(a/theorem drop-edges-ids-ok [w :- World, p :- (=> EdgeRow Bool)]
  (= (ids-ok (drop-edges w p)) (ids-ok (set-edges w (tbl-filter p (:edges w)))))
  (simp only [ids-ok ids-unique ids-below all-ids drop-edges set-comps set-edges resync-ids]))

(a/theorem inv-drop-edges [w :- World, p :- (=> EdgeRow Bool)]
  (=> (= (inv-sample w) true) (= (inv-sample (drop-edges w p)) true))
  (intro h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (have h1 (= (pending-exact (drop-edges w p)) true))
  (simp only [pending-exact pending-exact-in drop-edges set-comps set-edges])
  (exact (resync-exact (tbl-filter p (:edges w)) (:comps w)))
  (have h2 (= (edges-ref-ok (drop-edges w p)) true))
  (have hr (= (edges-ref-ok w) true)) (exact (And.left (And.right hs)))
  (simp only [edges-ref-ok edges-ref-ok-in] at hr)
  (simp only [edges-ref-ok edges-ref-ok-in drop-edges set-comps set-edges
              (tbl-all-congr EdgeRow (edge-ok (comps-resync (tbl-filter p (:edges w)) (:comps w)) (:tasks w) (:sources w) (:acts w) (:res w))
                (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w))
                (edge-ok-resync (tbl-filter p (:edges w)) (:comps w) (:tasks w) (:sources w) (:acts w) (:res w))
                (tbl-filter p (:edges w)))])
  (exact (tbl-all-filter EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) p (:edges w) hr))
  (have h3 (= (ids-ok (drop-edges w p)) true))
  (rw [drop-edges-ids-ok])
  (exact (edge-filter-ids-ok w p (And.right (And.right hs))))
  (exact (inv-intro (drop-edges w p) h1 h2 h3)))

;; after dropping every edge that names x, no edge names x
(a/theorem drop-edges-avoids [w :- World, x :- Nat]
  (= (unreferenced (drop-edges w (edge-avoids x)) x) true)
  (simp only [unreferenced drop-edges set-comps set-edges])
  (exact (tbl-all-filter-self EdgeRow (edge-avoids x) (:edges w))))

;; deleting a computation no edge names
(a/theorem inv-comp-del-unref [w :- World, x :- Nat]
  (=> (= (unreferenced w x) true) (= (inv-sample w) true) (= (inv-sample (comp-del w x)) true))
  (intros hu h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (exact (inv-intro (comp-del w x) (pending-exact-comp-del w x (And.left hs))
           (comp-del-edges-ref-ok w x hu (And.left (And.right hs)))
           (comp-del-ids-ok w x (And.right (And.right hs))))))

(a/theorem inv-scope-del [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (scope-del w x)) true))
  (intro h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (exact (inv-intro (scope-del w x) (Eq.trans (pending-exact-scope-del w x) (And.left hs))
           (Eq.trans (edges-ref-ok-scope-del w x) (And.left (And.right hs)))
           (scope-del-ids-ok w x (And.right (And.right hs))))))

(a/theorem ids-ok-cleanup-ins [w :- World, r :- CleanupRow] (= (ids-ok (cleanup-ins w r)) (ids-ok w)) (rfl))

(a/theorem inv-cleanup-ins [w :- World, r :- CleanupRow]
  (=> (= (inv-sample w) true) (= (inv-sample (cleanup-ins w r)) true))
  (intro h) (simp only [inv-sample pending-exact-cleanup-ins edges-ref-ok-cleanup-ins ids-ok-cleanup-ins])
  (simp only [inv-sample] at h) (exact h))


;; ===========================================================================
;; Part B. Row updates (id-preserving; computations also keep pending)
;; ===========================================================================

;; the model's error code for ::cancelled (results are opaque Nats, A#1): the reserved Nat 1
;; (the engine interns ::cancelled to 1 in its log)
(a/defn cancelled-code [] Nat 1)
(a/defn res-cancelled [] RunResult (RunResult.mk res-err cancelled-code))

(a/defn run-cancel-row [r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) act-done mode-unwinding (:slice r)
             (:effect-index r) (:finalizers r) (:resources r)))
;; an armed resource is told to cancel; a fired one waits for its acknowledgement
(a/defn res-cancel-row [z :- ResRow] ResRow
  (if (Nat.beq (:phase z) rp-armed) (ResRow.mk (:id z) (:owner z) (:kind z) (:at z) rp-cancelling) z))
(a/defn comp-clear-run [c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) 0 (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) (:handles c)))
;; I7 idle shape: no run, empty basis, no adoption; validity from the removed dep edges
(a/defn comp-make-idle [vs :- (List Valid), c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) 0 (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) true vs (List.nil Created)
              (List.nil Created) (List.nil AdoptBase) (:handles c)))
(a/defn source-close-row [s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) (:owner s) (:kind s) (:state s) (:version s) false (:handles s) (:queue s)))
(a/defn source-detach-row [s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) 0 (:kind s) (:state s) (:version s) false (:handles s) (:queue s)))
(a/defn task-detach-row [t :- TaskRow] TaskRow (TaskRow.mk (:id t) 0 (:run t) (:result t) (:handles t) (:inputs t)))
;; a cancelled task that has no result completes with err ::cancelled (reading 4)
(a/defn task-cancel-result [t :- TaskRow] TaskRow
  (if (Nat.beq (:tag (:result t)) res-none) (TaskRow.mk (:id t) (:owner t) (:run t) res-cancelled (:handles t) (:inputs t)) t))

(a/theorem run-cancel-row-id [r :- RunRow] (= (run-id (run-cancel-row r)) (run-id r)) (rfl))
(a/theorem res-cancel-row-id [z :- ResRow] (= (resource-id (res-cancel-row z)) (resource-id z))
  (cases h (Nat.beq (:phase z) rp-armed)) (all_goals (simp [res-cancel-row resource-id h])))
(a/theorem comp-clear-run-id [c :- CompRow] (= (comp-id (comp-clear-run c)) (comp-id c)) (rfl))
(a/theorem comp-clear-run-pending [c :- CompRow] (= (:pending (comp-clear-run c)) (:pending c)) (rfl))
(a/theorem comp-make-idle-id [vs :- (List Valid), c :- CompRow] (= (comp-id (comp-make-idle vs c)) (comp-id c)) (rfl))
(a/theorem comp-make-idle-pending [vs :- (List Valid), c :- CompRow] (= (:pending (comp-make-idle vs c)) (:pending c)) (rfl))
(a/theorem source-close-row-id [s :- SourceRow] (= (source-id (source-close-row s)) (source-id s)) (rfl))
(a/theorem source-detach-row-id [s :- SourceRow] (= (source-id (source-detach-row s)) (source-id s)) (rfl))
(a/theorem task-detach-row-id [t :- TaskRow] (= (task-id (task-detach-row t)) (task-id t)) (rfl))
(a/theorem task-cancel-result-id [t :- TaskRow] (= (task-id (task-cancel-result t)) (task-id t))
  (cases h (Nat.beq (:tag (:result t)) res-none)) (all_goals (simp [task-cancel-result task-id h])))

;; ===========================================================================
;; Part C. Queries: scope subtrees, owned work, T10 finalize
;; ===========================================================================

(a/defn parent-is [x :- Nat, s :- ScopeRow] Bool (Nat.beq (:parent s) x))
(a/defn child-scopes [w :- World, x :- Nat] (List Nat) (tbl-scan scope-id (parent-is x) (:scopes w)))
;; S and every scope below it (parent links reversed); fuel 2 + #scopes (each scope is the
;; child of one parent, so it is pushed at most once)
(a/defn scope-subtree [w :- World, s :- Nat] (List Nat)
  (:visited (reach-run-l (List.cons Nat 0 (List.cons Nat 0 (tbl-ids scope-id (:scopes w))))
                         (child-scopes w) (nz s))))

(a/defn task-owned-in [sub :- (List Nat), t :- TaskRow] Bool (reach-mem (:owner t) sub))
(a/defn source-owned-in [sub :- (List Nat), x :- SourceRow] Bool (reach-mem (:owner x) sub))
(a/defn fork-owned-in [sub :- (List Nat), f :- ForkRow] Bool (reach-mem (:owner f) sub))
(a/defn run-scoped-in [sub :- (List Nat), r :- RunRow] Bool (reach-mem (:scope r) sub))

;; the work a subtree owns: the non-done runs of the tasks it owns (reading 2)
(a/defn run-owned-by [w :- World, sub :- (List Nat), r :- RunRow] Bool
  (Bool.and (run-alive r) (opt-test (task-owned-in sub) (task-find w (:of r)))))
(a/defn owned-runs [w :- World, sub :- (List Nat)] (List Nat) (tbl-scan run-id (run-owned-by w sub) (:runs w)))

;; T10 finalize(d): remove the armed dep edges on d that are not unfilled members of an
;; activation (`finalize-one`), and cascade (Z#25): a creditor computation that becomes final
;; (D1: live and no dep edges; reading 9) is finalized in turn. A worklist with list fuel
;; 1 + #initial + #comps (a final computation has no dep edges, so it is never again the
;; creditor of a removed edge); `fin-done` says the worklist emptied (tests check it).
(a/defn act-has-member [x :- Nat, a :- ActRow] Bool (mem-has x (:members a)))
(a/defn fin-drop [as :- (List ActRow), d :- Nat, e :- EdgeRow] Bool
  (Bool.and (Nat.beq (:kind e) ek-dep)
   (Bool.and (Nat.beq (:phase e) ph-armed)
    (Bool.and (Nat.beq (:debtor e) d) (Bool.not (tbl-any (act-has-member (:id e)) as))))))
(a/defn fin-keep [as :- (List ActRow), d :- Nat, e :- EdgeRow] Bool (Bool.not (fin-drop as d e)))
(a/defn finalize-one [w :- World, d :- Nat] World (drop-edges w (fin-keep (:acts w) d)))
(a/defn edge-cred [e :- EdgeRow] Nat (:creditor e))
;; D1 for a computation: Z#32, computations are never final in layer 1 (T3 replacement and
;; explicit re-execution can always re-run them), so dep edges on them are never finalized
(a/defn comp-final [w :- World, c :- CompRow] Bool false)
(a/defn final-comp-id [w :- World, x :- Nat] Bool (opt-test (comp-final w) (comp-find w x)))
(a/structure FinRes [] (world World) (rest (List Nat)))
(a/defn fin-loop [fuel :- (List Nat), w :- World, ds :- (List Nat)] FinRes
  (match fuel
    [nil (FinRes.mk w ds)]
    [(cons h f) (match ds
                  [nil (FinRes.mk w (List.nil Nat))]
                  [(cons d t) (fin-loop f (finalize-one w d)
                                (List.append Nat t (tbl-filter (final-comp-id (finalize-one w d))
                                                     (tbl-scan edge-cred (fin-drop (:acts w) d) (:edges w)))))])]))
(a/defn fin-fuel [w :- World] (List Nat) (List.cons Nat 0 (List.cons Nat 0 (tbl-ids comp-id (:comps w)))))
(a/defn finalize-debtor [w :- World, d :- Nat] World
  (:world (fin-loop (fin-fuel w) w (List.cons Nat d (List.nil Nat)))))
(a/defn fin-done [w :- World, d :- Nat] Bool
  (match (:rest (fin-loop (fin-fuel w) w (List.cons Nat d (List.nil Nat)))) [nil true] [(cons h t) false]))

;; Z#53: closing a source wakes what waits on it, before T10: its armed wait edges (takes,
;; acquires, task awaits, host waits) and its armed dep edges that are activation members fire
;; (T9) with the source's final result, `deb-result` of the closed row: the value of a signal, a
;; cell or a delivered deferred, err ::closed (`closed-code`, the reserved Nat 2) for a mailbox, a
;; semaphore or an undelivered deferred. A member delivery consumes its dep edge (final debtor,
;; Z#39); T10 then removes the remaining armed dep edges (tracks). No run stays parked on a
;; final debtor.
(a/defn close-wakes [as :- (List ActRow), d :- Nat, e :- EdgeRow] Bool
  (Bool.and (Nat.beq (:debtor e) d)
            (Bool.or (Nat.beq (:kind e) ek-wait)
                     (Bool.and (Nat.beq (:kind e) ek-dep) (tbl-any (act-has-member (:id e)) as)))))
(a/defn wake-closed [w :- World, d :- Nat] World
  (nat-fold (fire-edge (deb-result w d)) w (tbl-scan edge-id (close-wakes (:acts w) d) (:edges w))))
;; closing a source makes it final (D1): wake (Z#53), then T10
(a/defn close-source [w :- World, x :- Nat] World (finalize-debtor (wake-closed (source-upd w x source-close-row) x) x))
(a/defn close-scope-id [w :- World, x :- Nat] World (scope-upd w x scope-close))

;; T16's local part on a subtree: every scope in it is closed, every source it owns is closed
(a/defn close-local [w :- World, sub :- (List Nat)] World
  (nat-fold close-source (nat-fold close-scope-id w sub) (tbl-scan source-id (source-owned-in sub) (:sources w))))

;; Z#56: the root scope is never removed, not even by T21's close of the whole tree: a subtree
;; holding a root-kind scope is never empty (Rule R's filter keeps the root scope: it is a root,
;; retain.clj `roots`, also after release)
(a/defn root-in [sub :- (List Nat), s :- ScopeRow] Bool (Bool.and (reach-mem (:id s) sub) (is-root-scope s)))
;; a subtree is empty when it has nothing but closed scopes: no task, run scope or fork marker
;; is owned by it (closed sources do not hold it: they are detached, reading 6)
(a/defn scope-closed-in [sub :- (List Nat), s :- ScopeRow] Bool
  (Bool.or (Bool.not (reach-mem (:id s) sub)) (Bool.not (:open s))))
;; and no scope outside it has its parent in it (always so for a converged subtree; the guard keeps
;; every remaining scope's parent without the convergence argument, literal I1, spindel.v2.i1)
(a/defn parent-outside [sub :- (List Nat), s :- ScopeRow] Bool
  (Bool.or (reach-mem (:id s) sub) (Bool.not (reach-mem (:parent s) sub))))
(a/defn subtree-empty [w :- World, sub :- (List Nat)] Bool
  (Bool.and (tbl-all (parent-outside sub) (:scopes w))
  (Bool.and (tbl-all (scope-closed-in sub) (:scopes w))
  (Bool.and (Bool.not (tbl-any (task-owned-in sub) (:tasks w)))
  (Bool.and (Bool.not (tbl-any (fork-owned-in sub) (:forks w)))
  (Bool.and (Bool.not (tbl-any (run-scoped-in sub) (:runs w)))
            (Bool.not (tbl-any (root-in sub) (:scopes w)))))))))
(a/defn remove-if-empty [w :- World, sub :- (List Nat)] World
  (if (subtree-empty w sub) (nat-fold scope-del w sub) w))

;; ===========================================================================
;; Part D. T14 cancel (local part), T13 retire, T16 close (local part)
;; ===========================================================================

;; debtor side (R#14): wait creditors of the entity get err ::cancelled (T9 fire), and for a
;; computation's current run, every armed dep edge on it is an invalidation (§4.5.3)
(a/defn fire-waits-cancelled [w :- World, d :- Nat] World
  (nat-fold (fire-edge res-cancelled) w (waits-on d (:edges w))))
(a/defn armed-dep-on [d :- Nat, e :- EdgeRow] Bool
  (Bool.and (Nat.beq (:kind e) ek-dep) (Bool.and (Nat.beq (:debtor e) d) (Nat.beq (:phase e) ph-armed))))
(a/defn invalidate-id [w :- World, x :- Nat] World
  (match (edge-find w x)
    [none w]
    [(some e) (if (Nat.beq (:phase e) ph-armed) (invalidate w e) w)]))
(a/defn invalidate-dependents [w :- World, d :- Nat] World
  (nat-fold invalidate-id w (tbl-scan edge-id (armed-dep-on d) (:edges w))))
;; Z#39: a cancelled task is final: like a completion (T12), its wait creditors AND the dep
;; edges of computations awaiting it fire with err ::cancelled (a delivery to a current member,
;; else an invalidation), then T10 removes its armed dep edges
(a/defn on-task [k :- Nat, e :- EdgeRow] Bool
  (Bool.and (Nat.beq (:debtor e) k) (Bool.or (Nat.beq (:kind e) ek-wait) (Nat.beq (:kind e) ek-dep))))
(a/defn fire-task-cancelled [w :- World, d :- Nat] World
  (finalize-debtor (nat-fold (fire-edge res-cancelled) w (tbl-scan edge-id (on-task d) (:edges w))) d))
(a/defn debtor-side [w :- World, r :- RunRow] World
  (match (comp-find w (:of r))
    [none (fire-task-cancelled (task-upd w (:of r) task-cancel-result) (:of r))]
    [(some c) (if (Nat.beq (:epoch r) (:epoch c))
                  (invalidate-dependents (fire-waits-cancelled w (:of r)) (:of r))
                  w)]))

;; cleanup[R] (§3.2 table, A#2): its run scope's subtree and the tasks and sources owned
;; there; the run row, run scope, body entity, resources, finalizer refs and the run scope's
;; current ancestors (Z#38, Z#52) are read from the run row by `cleanup-contrib` (retain)
(a/defn rows-of-sub [w :- World, sub :- (List Nat)] (List Nat)
  (nat-app sub (nat-app (tbl-scan task-id (task-owned-in sub) (:tasks w))
                        (tbl-scan source-id (source-owned-in sub) (:sources w)))))
;; Z#38/Z#52: cleanup[R] also retains its run scope's ancestors, but as the CURRENT chain read
;; from the parent fields at every Rule R pass (`scope-ancestors` in `cleanup-contrib`, retain),
;; not stored here: a detach that re-parents a scope of the chain moves the retention (I1)
(a/defn cleanup-rows-of [w :- World, r :- RunRow] (List Nat) (rows-of-sub w (scope-subtree w (:scope r))))
(a/defn cleanup-set [w :- World, rid :- Nat, rows :- (List Nat)] World
  (cleanup-ins (cleanup-del w rid) (CleanupRow.mk rid rows)))

(a/defn cancel-acts [w :- World, rid :- Nat] World
  (nat-fold drop-act w (tbl-scan act-id (act-of-run rid) (:acts w))))
(a/defn res-cancel [w :- World, z :- Nat] World (resource-upd w z res-cancel-row))
(a/defn cancel-res [w :- World, r :- RunRow] World (nat-fold res-cancel w (:resources r)))
;; cancel(R, replace) (Y#2, T11's predecessor) skips the debtor side of a computation run; it is
;; never issued for a task run, where the debtor side runs as for an ordinary cancel (so a
;; cancelled task always gets its result: the literal I10 proof, spindel.v2.lit)
(a/defn cancel-debtor [rep :- Bool, w :- World, r :- RunRow] World
  (if (Bool.and rep (comp-has w (:of r))) w (debtor-side w r)))

;; T14 on run r, local part: act := done, mode := unwinding; its activations go with their
;; wait/savepoint members (drop-act removes every edge an activation is the creditor of;
;; wait edges on resources too, Z#6); armed resources -> cancelling; cleanup[R]; the debtor
;; side unless `rep` (cancel(R, replace), Y#2). Children and T13 are cascade jobs.
(a/defn cancel-run-local [w :- World, r :- RunRow, rep :- Bool] World
  (cancel-debtor rep
    (cleanup-set (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r)
                 (:id r) (cleanup-rows-of w r))
    r))

;; T13 retire, in the order of Z#18: (1) C.run := none; (2) T16 on R.scope (local part; the
;; cancels are cascade jobs); (3) the run row and cleanup[R] go; (4) R.scope's subtree goes
;; when it is empty
;; Z#25(b): T13 step 1 clears C.run or K.run
(a/defn task-clear-run [t :- TaskRow] TaskRow (TaskRow.mk (:id t) (:owner t) 0 (:result t) (:handles t) (:inputs t)))
(a/defn clear-task-run [w :- World, r :- RunRow] World
  (match (task-find w (:of r))
    [none w]
    [(some t) (if (Nat.beq (:run t) (:id r)) (task-upd w (:of r) task-clear-run) w)]))
(a/defn clear-comp-run [w :- World, r :- RunRow] World
  (match (comp-find w (:of r))
    [none (clear-task-run w r)]
    [(some c) (if (Nat.beq (:run c) (:id r)) (comp-upd w (:of r) comp-clear-run) w)]))
(a/defn retire-with [w :- World, r :- RunRow, sub :- (List Nat)] World
  (remove-if-empty (cleanup-del (run-del (close-local (clear-comp-run w r) sub) (:id r)) (:id r)) sub))
(a/defn retire-local [w :- World, r :- RunRow] World (retire-with w r (scope-subtree w (:scope r))))

;; T16 close-scope(S), local part
(a/defn close-with [w :- World, sub :- (List Nat)] World (remove-if-empty (close-local w sub) sub))
(a/defn close-scope-local [w :- World, s :- Nat] World (close-with w (scope-subtree w s)))


;; ---- inv-sample for Parts C/D

(a/theorem inv-finalize-one [w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (finalize-one w d)) true))
  (intro h) (exact (inv-drop-edges w (fin-keep (:acts w) d) h)))

(a/theorem inv-fin-loop [fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat)]
    (=> (= (inv-sample w) true) (= (inv-sample (:world (fin-loop fuel w ds))) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w ds hw) (simp only [fin-loop]) (exact hw)
  (intros w ds hw)
  (cases ds)
  (simp only [fin-loop]) (exact hw)
  (rename_i d t)
  (simp only [fin-loop])
  (exact (ih _ _ (inv-finalize-one w d hw))))

(a/theorem inv-finalize-debtor [w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (finalize-debtor w d)) true))
  (intro h) (exact (inv-fin-loop (fin-fuel w) w _ h)))

(a/theorem inv-wake-closed [w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (wake-closed w d)) true))
  (intro h)
  (simp only [wake-closed])
  (exact (nat-fold-inv (fire-edge (deb-result w d)) (inv-fire-edge (deb-result w d)) _ w h)))

(a/theorem inv-close-source [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (close-source w x)) true))
  (intro h)
  (exact (inv-finalize-debtor _ x (inv-wake-closed _ x (inv-source-upd w x source-close-row source-close-row-id h)))))

(a/theorem inv-close-scope-id [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (close-scope-id w x)) true))
  (intro h) (exact (inv-scope-upd w x scope-close scope-close-scope-id h)))

(a/theorem inv-close-local [w :- World, sub :- (List Nat)]
  (=> (= (inv-sample w) true) (= (inv-sample (close-local w sub)) true))
  (intro h)
  (exact (nat-fold-inv close-source inv-close-source (tbl-scan source-id (source-owned-in sub) (:sources w)) _
           (nat-fold-inv close-scope-id inv-close-scope-id sub w h))))

(a/theorem inv-remove-if-empty [w :- World, sub :- (List Nat)]
  (=> (= (inv-sample w) true) (= (inv-sample (remove-if-empty w sub)) true))
  (intro h)
  (cases he (subtree-empty w sub))
  (simp only [remove-if-empty he]) (exact h)
  (simp only [remove-if-empty he]) (exact (nat-fold-inv scope-del inv-scope-del sub w h)))

(a/theorem inv-invalidate-id [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (invalidate-id w x)) true))
  (intro h)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [invalidate-id hf]) (exact h)
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [invalidate-id hf hp]) (exact h)
  (simp only [invalidate-id hf hp]) (exact (inv-invalidate w e h)))

(a/theorem inv-fire-waits-cancelled [w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (fire-waits-cancelled w d)) true))
  (intro h)
  (exact (nat-fold-inv (fire-edge res-cancelled) (inv-fire-edge res-cancelled) (waits-on d (:edges w)) w h)))

(a/theorem inv-fire-task-cancelled [w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (fire-task-cancelled w d)) true))
  (intro h)
  (simp only [fire-task-cancelled])
  (exact (inv-finalize-debtor _ d (nat-fold-inv (fire-edge res-cancelled) (inv-fire-edge res-cancelled) _ w h))))

(a/theorem inv-invalidate-dependents [w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (invalidate-dependents w d)) true))
  (intro h)
  (exact (nat-fold-inv invalidate-id inv-invalidate-id (tbl-scan edge-id (armed-dep-on d) (:edges w)) w h)))

(a/theorem inv-debtor-side [w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (= (inv-sample (debtor-side w r)) true))
  (intro h)
  (cases hc (comp-find w (:of r))) (case' [some c]) (case' [none])
  (simp only [debtor-side hc])
  (exact (inv-fire-task-cancelled _ (:of r) (inv-task-upd w (:of r) task-cancel-result task-cancel-result-id h)))
  (cases he (Nat.beq (:epoch r) (:epoch c)))
  (simp only [debtor-side hc he]) (exact h)
  (simp only [debtor-side hc he])
  (exact (inv-invalidate-dependents _ (:of r) (inv-fire-waits-cancelled w (:of r) h))))

(a/theorem inv-cleanup-set [w :- World, rid :- Nat, rows :- (List Nat)]
  (=> (= (inv-sample w) true) (= (inv-sample (cleanup-set w rid rows)) true))
  (intro h)
  (exact (inv-cleanup-ins _ (CleanupRow.mk rid rows) (inv-cleanup-del w rid h))))

(a/theorem inv-cancel-acts [w :- World, rid :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (cancel-acts w rid)) true))
  (intro h)
  (exact (nat-fold-inv drop-act inv-drop-act (tbl-scan act-id (act-of-run rid) (:acts w)) w h)))

(a/theorem inv-res-cancel [w :- World, z :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (res-cancel w z)) true))
  (intro h) (exact (inv-resource-upd w z res-cancel-row res-cancel-row-id h)))

(a/theorem inv-cancel-res [w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (= (inv-sample (cancel-res w r)) true))
  (intro h) (exact (nat-fold-inv res-cancel inv-res-cancel (:resources r) w h)))

(a/theorem inv-cancel-debtor [rep :- Bool, w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (= (inv-sample (cancel-debtor rep w r)) true))
  (intro h)
  (cases hc (Bool.and rep (comp-has w (:of r))))
  (simp only [cancel-debtor hc]) (exact (inv-debtor-side w r h))
  (simp only [cancel-debtor hc]) (exact h))

(a/theorem inv-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
  (=> (= (inv-sample w) true) (= (inv-sample (cancel-run-local w r rep)) true))
  (intro h)
  (simp only [cancel-run-local])
  (exact (inv-cancel-debtor rep _ r
           (inv-cleanup-set _ (:id r) (cleanup-rows-of w r)
             (inv-cancel-res _ r
               (inv-cancel-acts _ (:id r)
                 (inv-run-upd w (:id r) run-cancel-row run-cancel-row-id h)))))))

(a/theorem task-clear-run-id [t :- TaskRow] (= (task-id (task-clear-run t)) (task-id t)) (rfl))
(a/theorem inv-clear-task-run [w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (= (inv-sample (clear-task-run w r)) true))
  (intro h)
  (cases hc (task-find w (:of r))) (case' [some t]) (case' [none])
  (simp only [clear-task-run hc]) (exact h)
  (cases hr (Nat.beq (:run t) (:id r)))
  (simp only [clear-task-run hc hr]) (exact h)
  (simp only [clear-task-run hc hr])
  (exact (inv-task-upd w (:of r) task-clear-run task-clear-run-id h)))

(a/theorem inv-clear-comp-run [w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (= (inv-sample (clear-comp-run w r)) true))
  (intro h)
  (cases hc (comp-find w (:of r))) (case' [some c]) (case' [none])
  (simp only [clear-comp-run hc]) (exact (inv-clear-task-run w r h))
  (cases hr (Nat.beq (:run c) (:id r)))
  (simp only [clear-comp-run hc hr]) (exact h)
  (simp only [clear-comp-run hc hr])
  (exact (inv-comp-upd w (:of r) comp-clear-run comp-clear-run-id comp-clear-run-pending h)))

(a/theorem inv-retire-with [w :- World, r :- RunRow, sub :- (List Nat)]
  (=> (= (inv-sample w) true) (= (inv-sample (retire-with w r sub)) true))
  (intro h)
  (simp only [retire-with])
  (exact (inv-remove-if-empty _ sub
           (inv-cleanup-del _ (:id r) (inv-run-del _ (:id r) (inv-close-local _ sub (inv-clear-comp-run w r h)))))))

(a/theorem inv-retire-local [w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (= (inv-sample (retire-local w r)) true))
  (intro h) (exact (inv-retire-with w r (scope-subtree w (:scope r)) h)))

(a/theorem inv-close-scope-local [w :- World, s :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (close-scope-local w s)) true))
  (intro h)
  (simp only [close-scope-local close-with])
  (exact (inv-remove-if-empty _ (scope-subtree w s) (inv-close-local w (scope-subtree w s) h))))


;; ===========================================================================
;; Part E. The cascade: a job worklist with list fuel (T14 children, T13 after cancel, T16)
;; ===========================================================================

(a/inductive Job []
  (jcancel [r Nat] [rep Bool])   ; T14 cancel(r) / cancel(r, replace)
  (jretire [r Nat])              ; T13 retire?(r)
  (jclose [s Nat]))              ; T16 close-scope(s)

(a/defn cancel-jobs [xs :- (List Nat)] (List Job)
  (match xs [nil (List.nil Job)] [(cons h t) (List.cons Job (Job.jcancel h false) (cancel-jobs t))]))

(a/defn job-apply [w :- World, j :- Job] World
  (match j
    [(jcancel rid rep) (match (run-find w rid)
                         [none w]
                         [(some r) (if (run-alive r) (cancel-run-local w r rep) w)])]
    [(jretire rid) (match (run-find w rid)
                     [none w]
                     [(some r) (if (retirable r) (retire-local w r) w)])]
    [(jclose s) (if (scope-has w s) (close-scope-local w s) w)]))

;; follow-up jobs, read from the world before the job: cancel's children (the work owned by
;; R.scope's subtree) then T13 on R; retire's and close's T16 cancels
(a/defn job-next [w :- World, j :- Job] (List Job)
  (match j
    [(jcancel rid rep) (match (run-find w rid)
                         [none (List.nil Job)]
                         [(some r) (if (run-alive r)
                                       (List.append Job (cancel-jobs (owned-runs w (scope-subtree w (:scope r))))
                                                    (List.cons Job (Job.jretire rid) (List.nil Job)))
                                       (List.nil Job))])]
    [(jretire rid) (match (run-find w rid)
                     [none (List.nil Job)]
                     [(some r) (if (retirable r) (cancel-jobs (owned-runs w (scope-subtree w (:scope r))))
                                   (List.nil Job))])]
    [(jclose s) (if (scope-has w s) (cancel-jobs (owned-runs w (scope-subtree w s))) (List.nil Job))]))

(a/structure Casc [] (world World) (rest (List Job)))

(a/defn cascade [fuel :- (List Nat), w :- World, js :- (List Job)] Casc
  (match fuel
    [nil (Casc.mk w js)]
    [(cons h f) (match js
                  [nil (Casc.mk w (List.nil Job))]
                  [(cons j t) (cascade f (job-apply w j) (List.append Job t (job-next w j)))])]))

;; fuel: a cancel or retire acts once per run (the guards); each acting job queues at most
;; #runs + 1 jobs, and each initial job at most #runs. Not proved: `casc-done` is the flag.
(a/defn rep-list [xs :- (List Nat), unit :- (List Nat)] (List Nat)
  (match xs [nil (List.nil Nat)] [(cons h t) (List.append Nat unit (rep-list t unit))]))
(a/defn job-zeros [js :- (List Job)] (List Nat)
  (match js [nil (List.nil Nat)] [(cons h t) (List.cons Nat 0 (job-zeros t))]))
(a/defn casc-fuel [w :- World, js :- (List Job)] (List Nat)
  (List.cons Nat 0
    (List.append Nat (rep-list (job-zeros js) (List.cons Nat 0 (tbl-ids run-id (:runs w))))
      (rep-list (tbl-ids run-id (:runs w))
                (List.cons Nat 0 (List.cons Nat 0 (List.append Nat (tbl-ids run-id (:runs w)) (tbl-ids run-id (:runs w)))))))))

(a/defn cascade-run [w :- World, js :- (List Job)] Casc (cascade (casc-fuel w js) w js))
(a/defn run-cascade [w :- World, js :- (List Job)] World (:world (cascade-run w js)))
(a/defn jobs-empty [js :- (List Job)] Bool (match js [nil true] [(cons h t) false]))
(a/defn casc-done [w :- World, js :- (List Job)] Bool (jobs-empty (:rest (cascade-run w js))))

(a/theorem inv-job-apply [w :- World, j :- Job]
  (=> (= (inv-sample w) true) (= (inv-sample (job-apply w j)) true))
  (intro h)
  (cases j)
  ;; jcancel
  (rename_i rid rep)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [job-apply hf]) (exact h)
  (cases ha (run-alive r))
  (simp only [job-apply hf ha]) (exact h)
  (simp only [job-apply hf ha]) (exact (inv-cancel-run-local w r rep h))
  ;; jretire
  (rename_i rid)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [job-apply hf]) (exact h)
  (cases ha (retirable r))
  (simp only [job-apply hf ha]) (exact h)
  (simp only [job-apply hf ha]) (exact (inv-retire-local w r h))
  ;; jclose
  (rename_i s)
  (cases hs (scope-has w s))
  (simp only [job-apply hs]) (exact h)
  (simp only [job-apply hs]) (exact (inv-close-scope-local w s h)))

(a/theorem inv-cascade [fuel :- (List Nat)]
  (forall [w :- World, js :- (List Job)]
    (=> (= (inv-sample w) true) (= (inv-sample (:world (cascade fuel w js))) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w js hw) (simp only [cascade]) (exact hw)
  (intros w js hw)
  (cases js)
  (simp only [cascade]) (exact hw)
  (rename_i j t)
  (simp only [cascade])
  (exact (ih (job-apply w j) (List.append Job t (job-next w j)) (inv-job-apply w j hw))))

(a/theorem inv-run-cascade [w :- World, js :- (List Job)]
  (=> (= (inv-sample w) true) (= (inv-sample (run-cascade w js)) true))
  (intro h) (exact (inv-cascade (casc-fuel w js) w js h)))


;; ===========================================================================
;; Part F. Transitions T14, T16, T13 (full) and T15 with Z#6
;; ===========================================================================

;; T14 as a transition: the run must exist and not be done
(a/defn t14-cancel [w :- World, rid :- Nat, rep :- Bool] Outcome
  (match (run-find w rid)
    [none (refuse w)]
    [(some r) (if (run-alive r)
                  (accept (run-cascade w (List.cons Job (Job.jcancel rid rep) (List.nil Job))))
                  (refuse w))]))

;; T16 close-scope(S): the scope must exist
(a/defn t16-close-scope [w :- World, s :- Nat] Outcome
  (if (scope-has w s) (accept (run-cascade w (List.cons Job (Job.jclose s) (List.nil Job)))) (refuse w)))

;; T13 with the Z#18 steps and the T16 cascade (replaces step.clj's shallow retire-check)
(a/defn retire-full [w :- World, rid :- Nat] World
  (run-cascade w (List.cons Job (Job.jretire rid) (List.nil Job))))

;; T15 (Z#6): the acknowledgement token needs the resource row and no edge with Z as debtor
(a/defn t15-full [w :- World, z :- Nat] Outcome
  (if (ack-tok-ok w z)
      (match (resource-find w z)
        [none (refuse w)]
        [(some zr) (accept (retire-full (ack-raw w z (:owner zr)) (:owner zr)))])
      (refuse w)))

(a/theorem t14-inv [w :- World, rid :- Nat, rep :- Bool]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t14-cancel w rid rep))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t14-cancel hf refuse]) (exact h)
  (cases ha (run-alive r))
  (simp only [t14-cancel hf ha refuse]) (exact h)
  (simp only [t14-cancel hf ha accept]) (exact (inv-run-cascade w _ h)))

(a/theorem t14-refuse [w :- World, rid :- Nat, rep :- Bool]
  (=> (= (:accepted (t14-cancel w rid rep)) false) (= (:world (t14-cancel w rid rep)) w))
  (intro ha)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t14-cancel hf refuse])
  (cases hl (run-alive r))
  (simp only [t14-cancel hf hl refuse])
  (simp [t14-cancel hf hl accept] at ha))

(a/theorem t16-inv [w :- World, s :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t16-close-scope w s))) true))
  (intro h)
  (cases hs (scope-has w s))
  (simp only [t16-close-scope hs refuse]) (exact h)
  (simp only [t16-close-scope hs accept]) (exact (inv-run-cascade w _ h)))

(a/theorem t16-refuse [w :- World, s :- Nat]
  (=> (= (:accepted (t16-close-scope w s)) false) (= (:world (t16-close-scope w s)) w))
  (intro ha)
  (cases hs (scope-has w s))
  (simp only [t16-close-scope hs refuse])
  (simp [t16-close-scope hs accept] at ha))

(a/theorem t15-full-inv [w :- World, z :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t15-full w z))) true))
  (intro h)
  (cases hk (ack-tok-ok w z))
  (simp only [t15-full hk refuse]) (exact h)
  (cases hf (resource-find w z)) (case' [some zr]) (case' [none])
  (simp only [t15-full hk hf refuse]) (exact h)
  (simp only [t15-full hk hf accept retire-full])
  (have hu (= (tbl-all (no-debtor z) (:edges w)) true))
  (simp only [ack-tok-ok Bool.and_eq_true] at hk) (exact (And.right hk))
  (exact (inv-run-cascade _ _ (inv-ack-raw w z (:owner zr) hu h))))

(a/theorem t15-full-refuse [w :- World, z :- Nat]
  (=> (= (:accepted (t15-full w z)) false) (= (:world (t15-full w z)) w))
  (intro ha)
  (cases hk (ack-tok-ok w z))
  (simp only [t15-full hk refuse])
  (cases hf (resource-find w z)) (case' [some zr]) (case' [none])
  (simp only [t15-full hk hf refuse])
  (simp [t15-full hk hf accept] at ha))

(a/theorem t15-full-l4 [w :- World, z :- Nat]
  (=> (= (ack-tok-ok w z) false) (= (t15-full w z) (refuse w)))
  (intro hk) (simp only [t15-full hk]))

;; ===========================================================================
;; Part G. Rule R normalization: demote, detach, the loop
;; ===========================================================================

;; ---- demote (§3.3 step 1.3)

(a/defn run-alive-of [c :- Nat, r :- RunRow] Bool (Bool.and (run-alive r) (Nat.beq (:of r) c)))
;; the non-done runs of tasks named in ids (a basis)
(a/defn run-of-tasks [w :- World, ids :- (List Nat), r :- RunRow] Bool
  (Bool.and (run-alive r) (Bool.and (reach-mem (:of r) ids) (task-has w (:of r)))))
(a/defn demote-cancels [w :- World, c :- CompRow] (List Nat)
  (List.append Nat (tbl-scan run-id (run-alive-of (:id c)) (:runs w))
                   (tbl-scan run-id (run-of-tasks w (created-ids (:basis c))) (:runs w))))

;; validity entry of a removed dep edge (Z#24): (debtor, the version the edge last consumed),
;; i.e. its `seen`; an edge that never consumed a version gives the entry (0, 0), whose debtor
;; 0 never exists, so the validity fails and the computation must re-run (reading 7)
(a/defn crank-of [w :- World, x :- Nat] Nat (match (comp-find w x) [none 0] [(some c) (:rank c)]))
;; I14 (model-only fields): each entry carries the allocator and the creditor's rank at the demotion
(a/defn edge-valid [w :- World, e :- EdgeRow] Valid
  (if (:has-seen e) (Valid.mk (:debtor e) (:seen e) (:next-id w) (crank-of w (:creditor e)))
      (Valid.mk 0 0 (:next-id w) (crank-of w (:creditor e)))))
(a/defn valid-list [w :- World, es :- (List EdgeRow)] (List Valid)
  (match es [nil (List.nil Valid)] [(cons h t) (List.cons Valid (edge-valid w h) (valid-list w t))]))
(a/defn validity-of [w :- World, c :- Nat] (List Valid) (valid-list w (tbl-filter (dep-of c) (:edges w))))
(a/defn not-dep-of [c :- Nat, e :- EdgeRow] Bool (Bool.not (dep-of c e)))

;; kept as idle: a result, handles > 0 (Z#2), or a tombstone body entity of a cleanup entry
(a/defn demote-keep [w :- World, c :- CompRow] Bool
  (Bool.or (Bool.not (Nat.beq (:tag (:result c)) res-none))
           (Bool.or (Nat.blt 0 (:handles c)) (reach-mem (:id c) (cleanup-rows w)))))
(a/defn demote-finish [w :- World, cid :- Nat, vs :- (List Valid)] World
  (match (comp-find w cid)
    [none w]
    [(some c) (if (demote-keep w c)
                  (comp-upd w cid (comp-make-idle vs))
                  (comp-del (drop-edges w (edge-avoids cid)) cid))]))
(a/defn demote-edges [w :- World, cid :- Nat] World
  (demote-finish (drop-edges w (not-dep-of cid)) cid (validity-of w cid)))
;; Z#42: demotion steps the epoch when C.run is current (R.epoch = C.epoch; normalization may
;; have cancelled it earlier in the round, as the engine's demote! checks after its cancel), so
;; a run kept in cleanup is stale (I10)
(a/defn demote-cur [w :- World, c :- CompRow] Bool
  (match (run-find w (:run c))
    [none false]
    [(some r) (Nat.beq (:epoch r) (:epoch c))]))
(a/defn demote-epoch [w :- World, cid :- Nat, b :- Bool] World (if b (comp-upd w cid comp-inc-epoch) w))
(a/defn demote [w :- World, cid :- Nat] World
  (match (comp-find w cid)
    [none w]
    [(some c) (if (:idle c) w (demote-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) cid (demote-cur w c)) cid))]))

(a/theorem inv-demote-finish [w :- World, cid :- Nat, vs :- (List Valid)]
  (=> (= (inv-sample w) true) (= (inv-sample (demote-finish w cid vs)) true))
  (intro h)
  (cases hf (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [demote-finish hf]) (exact h)
  (cases hk (demote-keep w c))
  (simp only [demote-finish hf hk])
  (exact (inv-comp-del-unref _ cid (drop-edges-avoids w cid) (inv-drop-edges w (edge-avoids cid) h)))
  (simp only [demote-finish hf hk])
  (exact (inv-comp-upd w cid (comp-make-idle vs) (comp-make-idle-id vs) (comp-make-idle-pending vs) h)))

(a/theorem inv-demote-epoch [w :- World, cid :- Nat, b :- Bool]
  (=> (= (inv-sample w) true) (= (inv-sample (demote-epoch w cid b)) true))
  (intro h)
  (cases b)
  (simp only [demote-epoch]) (exact h)
  (simp only [demote-epoch]) (exact (inv-comp-upd w cid comp-inc-epoch comp-inc-epoch-comp-id comp-inc-epoch-pending h)))

(a/theorem inv-demote [w :- World, cid :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (demote w cid)) true))
  (intro h)
  (cases hf (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [demote hf]) (exact h)
  (cases hi (:idle c))
  (simp only [demote hf hi demote-edges])
  (exact (inv-demote-finish _ cid _ (inv-drop-edges _ (not-dep-of cid) (inv-demote-epoch _ cid _ (inv-run-cascade w _ h)))))
  (simp only [demote hf hi]) (exact h))

;; ---- detach (§3.3 step 2): sources and tasks whose owner row is gone

(a/defn owner-gone [w :- World, o :- Nat] Bool
  (Bool.and (Bool.not (Nat.beq o 0)) (Bool.and (Bool.not (scope-has w o)) (Bool.not (comp-has w o)))))
(a/defn src-orphan [w :- World, x :- SourceRow] Bool (owner-gone w (:owner x)))
(a/defn task-orphan [w :- World, t :- TaskRow] Bool (owner-gone w (:owner t)))
;; a detached source is closed, hence final (T10)
(a/defn detach-source [w :- World, x :- Nat] World (finalize-debtor (wake-closed (source-upd w x source-detach-row) x) x))
(a/defn detach-task [w :- World, x :- Nat] World (task-upd w x task-detach-row))
;; Z#23: a computation whose owner is removed gets owner := ⊥ (0), without being cancelled
(a/defn comp-orphan [w :- World, c :- CompRow] Bool (owner-gone w (:owner c)))
(a/defn comp-detach-row [c :- CompRow] CompRow
  (CompRow.mk (:id c) 0 (:inputs c) (:body c) (:run c) (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) (:handles c)))
(a/defn detach-comp [w :- World, x :- Nat] World (comp-upd w x comp-detach-row))
(a/defn detach [w :- World] World
  (nat-fold detach-comp
    (nat-fold detach-task (nat-fold detach-source w (tbl-scan source-id (src-orphan w) (:sources w)))
              (tbl-scan task-id (task-orphan w) (:tasks w)))
    (tbl-scan comp-id (comp-orphan w) (:comps w))))
;; no orphan left (I1's ownership half after the final detach, Z#25)
(a/defn no-orphans [w :- World] Bool
  (Bool.and (Bool.not (tbl-any (src-orphan w) (:sources w)))
            (Bool.and (Bool.not (tbl-any (task-orphan w) (:tasks w))) (Bool.not (tbl-any (comp-orphan w) (:comps w))))))

(a/theorem inv-detach-source [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (detach-source w x)) true))
  (intro h) (exact (inv-finalize-debtor _ x (inv-wake-closed _ x (inv-source-upd w x source-detach-row source-detach-row-id h)))))
(a/theorem inv-detach-task [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (detach-task w x)) true))
  (intro h) (exact (inv-task-upd w x task-detach-row task-detach-row-id h)))
(a/theorem comp-detach-row-id [c :- CompRow] (= (comp-id (comp-detach-row c)) (comp-id c)) (rfl))
(a/theorem comp-detach-row-pending [c :- CompRow] (= (:pending (comp-detach-row c)) (:pending c)) (rfl))
(a/theorem inv-detach-comp [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (detach-comp w x)) true))
  (intro h) (exact (inv-comp-upd w x comp-detach-row comp-detach-row-id comp-detach-row-pending h)))
(a/theorem inv-detach [w :- World]
  (=> (= (inv-sample w) true) (= (inv-sample (detach w)) true))
  (intro h)
  (exact (nat-fold-inv detach-comp inv-detach-comp (tbl-scan comp-id (comp-orphan w) (:comps w)) _
          (nat-fold-inv detach-task inv-detach-task (tbl-scan task-id (task-orphan w) (:tasks w)) _
           (nat-fold-inv detach-source inv-detach-source (tbl-scan source-id (src-orphan w) (:sources w)) w h)))))

;; ---- the loop

(a/defn run-norm [lv :- (List Nat), r :- RunRow] Bool (Bool.or (Bool.not (run-alive r)) (reach-mem (:id r) lv)))
(a/defn comp-norm [lv :- (List Nat), c :- CompRow] Bool (Bool.or (:idle c) (reach-mem (:id c) lv)))
(a/defn run-stray [lv :- (List Nat), r :- RunRow] Bool (Bool.not (run-norm lv r)))
(a/defn comp-stray [lv :- (List Nat), c :- CompRow] Bool (Bool.not (comp-norm lv c)))
(a/defn normalized-with [w :- World, lv :- (List Nat)] Bool
  (Bool.and (tbl-all (run-norm lv) (:runs w)) (tbl-all (comp-norm lv) (:comps w))))
;; §3.3: no non-done run and no non-idle computation outside live
(a/defn normalized [w :- World] Bool (normalized-with w (live-list w)))

;; one round: cancel (T14) the non-done runs outside live, demote the non-idle computations
;; outside live (live computed at the start of the round), detach the orphans
(a/defn norm-round-lv [w :- World, lv :- (List Nat)] World
  (detach (nat-fold demote (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray lv) (:runs w))))
                    (tbl-scan comp-id (comp-stray lv) (:comps w)))))
(a/defn norm-round [w :- World] World (norm-round-lv w (live-list w)))

(a/defn norm-loop [fuel :- (List Nat), w :- World] World
  (match fuel [nil w] [(cons h f) (if (normalized w) w (norm-loop f (norm-round w)))]))

(a/defn comp-active [c :- CompRow] Bool (Bool.not (:idle c)))
;; the measure #non-done runs + #non-idle computations, plus 1
(a/defn norm-fuel [w :- World] (List Nat)
  (List.cons Nat 0 (List.append Nat (tbl-scan run-id run-alive (:runs w)) (tbl-scan comp-id comp-active (:comps w)))))
(a/defn norm-measure [w :- World] Nat (+ (tbl-count run-alive (:runs w)) (tbl-count comp-active (:comps w))))

;; detach first: owners removed by the transition itself (T13 step 4) are detached even when
;; no round runs
(a/defn normalize [w :- World] World (norm-loop (norm-fuel (detach w)) (detach w)))



(a/theorem inv-norm-round [w :- World]
  (=> (= (inv-sample w) true) (= (inv-sample (norm-round w)) true))
  (intro h)
  (simp only [norm-round norm-round-lv])
  (exact (inv-detach _ (nat-fold-inv demote inv-demote _ _ (inv-run-cascade w _ h)))))

(a/theorem inv-norm-loop [fuel :- (List Nat)]
  (forall [w :- World] (=> (= (inv-sample w) true) (= (inv-sample (norm-loop fuel w)) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w hw) (simp only [norm-loop]) (exact hw)
  (intros w hw)
  (cases hn (normalized w))
  (simp only [norm-loop hn]) (exact (ih (norm-round w) (inv-norm-round w hw)))
  (simp only [norm-loop hn]) (exact hw))

(a/theorem inv-normalize [w :- World]
  (=> (= (inv-sample w) true) (= (inv-sample (normalize w)) true))
  (intro h) (exact (inv-norm-loop (norm-fuel (detach w)) (detach w) (inv-detach w h))))


;; ===========================================================================
;; Part I. The filter preserves inv-sample when it is edge-safe
;; ===========================================================================

;; filter-safe-k K w: a kept edge keeps its creditor (unless host) and its debtor, and a
;; marked edge whose creditor is kept is kept (so kept computations keep their pending)
(a/defn fs-ref [K :- (=> Nat Bool), e :- EdgeRow] Bool
  (Bool.or (Bool.not (K (:id e)))
           (Bool.and (Bool.or (host-cred e) (K (:creditor e))) (K (:debtor e)))))
(a/defn fs-mark [K :- (=> Nat Bool), e :- EdgeRow] Bool
  (Bool.or (Bool.not (Bool.and (:marked e) (K (:creditor e)))) (K (:id e))))
(a/defn filter-safe-k [K :- (=> Nat Bool), w :- World] Bool
  (Bool.and (tbl-all (fs-ref K) (:edges w)) (tbl-all (fs-mark K) (:edges w))))
;; for Rule R's keep set (live computed once)
(a/defn filter-safe [w :- World] Bool
  (filter-safe-k (keep-with w (live-list w) (cleanup-rows w) (storage w)) w))

(a/theorem tbl-all-keep [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), P :- (=> A Bool), Q :- (=> A Bool),
                         h :- (forall [r :- A] (=> (= (P r) true) (= (K (idf r)) true) (= (Q r) true))),
                         xs :- (List A)]
  (=> (= (tbl-all P xs) true) (= (tbl-all Q (tbl-keep K idf xs)) true))
  (induction xs)
  (case' [cons hd t ih])
  (case' [nil])
  (intro hp) (simp [tbl-keep tbl-all])
  (intro hp)
  (simp only [tbl-all Bool.and_eq_true] at hp)
  (cases hk (K (idf hd)))
  (simp only [tbl-keep hk]) (exact (ih (And.right hp)))
  (simp only [tbl-keep hk tbl-all Bool.and_eq_true])
  (exact (And.intro (h hd (And.left hp) hk) (ih (And.right hp)))))

(a/theorem tbl-all-keep2 [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), P :- (=> A Bool), R :- (=> A Bool),
                          Q :- (=> A Bool),
                          h :- (forall [r :- A] (=> (= (P r) true) (= (R r) true) (= (K (idf r)) true) (= (Q r) true))),
                          xs :- (List A)]
  (=> (= (tbl-all P xs) true) (= (tbl-all R xs) true) (= (tbl-all Q (tbl-keep K idf xs)) true))
  (induction xs)
  (case' [cons hd t ih])
  (case' [nil])
  (intros hp hr) (simp [tbl-keep tbl-all])
  (intros hp hr)
  (simp only [tbl-all Bool.and_eq_true] at hp)
  (simp only [tbl-all Bool.and_eq_true] at hr)
  (cases hk (K (idf hd)))
  (simp only [tbl-keep hk]) (exact (ih (And.right hp) (And.right hr)))
  (simp only [tbl-keep hk tbl-all Bool.and_eq_true])
  (exact (And.intro (h hd (And.left hp) (And.left hr) hk) (ih (And.right hp) (And.right hr)))))

(a/theorem tbl-all-keep-same [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), P :- (=> A Bool), xs :- (List A)]
  (=> (= (tbl-all P xs) true) (= (tbl-all P (tbl-keep K idf xs)) true))
  (induction xs)
  (case' [cons hd t ih])
  (case' [nil])
  (intro hp) (simp [tbl-keep tbl-all])
  (intro hp)
  (simp only [tbl-all Bool.and_eq_true] at hp)
  (cases hk (K (idf hd)))
  (simp only [tbl-keep hk]) (exact (ih (And.right hp)))
  (simp only [tbl-keep hk tbl-all Bool.and_eq_true])
  (exact (And.intro (And.left hp) (ih (And.right hp)))))

(a/theorem tbl-has-keep [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), y :- Nat, xs :- (List A)]
  (= (tbl-has idf y (tbl-keep K idf xs)) (Bool.and (K y) (tbl-has idf y xs)))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [tbl-has tbl-keep])
  (cases hb (Nat.beq (idf h) y))
  (case [false] (cases hk (K (idf h))) (all_goals (simp [tbl-has tbl-keep hb hk ih])))
  (case [true]
    (have he (= (idf h) y)) (exact (Nat.eq_of_beq_eq_true hb))
    (cases hk (K (idf h)))
    (case [false]
      (have hk2 (= (K y) false)) (rw [← he]) (exact hk)
      (simp [tbl-has tbl-keep hb hk hk2 ih]))
    (case [true]
      (have hk2 (= (K y) true)) (rw [← he]) (exact hk)
      (simp [tbl-has tbl-keep hb hk hk2]))))

(a/theorem marked-in-keep [K :- (=> Nat Bool), c :- Nat, es :- (List EdgeRow)]
  (=> (= (tbl-all (fs-mark K) es) true) (= (K c) true)
      (= (marked-in c (tbl-keep K edge-id es)) (marked-in c es)))
  (induction es)
  (case' [cons h t ih])
  (case' [nil])
  (intros hf hc) (simp [marked-in tbl-keep tbl-count])
  (intros hf hc)
  (simp only [tbl-all Bool.and_eq_true] at hf)
  (have ih2 (= (marked-in c (tbl-keep K edge-id t)) (marked-in c t))) (exact (ih (And.right hf) hc))
  (simp only [marked-in] at ih2)
  (simp only [marked-in])
  (cases hk (K (edge-id h)))
  (case [true] (simp only [tbl-keep hk tbl-count-cons ih2]))
  (case [false]
    (simp only [tbl-keep hk])
    (cases hm (marks c h))
    (case [false] (simp only [tbl-count-cons hm b2n ih2]))
    (case [true]
      (simp only [marks Bool.and_eq_true] at hm)
      (have hcr (= (:creditor h) c)) (exact (Nat.eq_of_beq_eq_true (And.left hm)))
      (have hf1 (= (fs-mark K h) true)) (exact (And.left hf))
      (simp only [edge-id] at hk)
      (simp [fs-mark hcr (And.right hm) hc hk] at hf1))))

(a/theorem kind-excl [e :- EdgeRow]
  (= (Bool.and (Nat.beq (:kind e) ek-dep) (host-cred e)) false)
  (cases hd (Nat.beq (:kind e) ek-dep))
  (simp)
  (have hk (= (:kind e) ek-dep)) (exact (Nat.eq_of_beq_eq_true hd))
  (simp [host-cred hk ek-dep ek-observe ek-wait]))

(a/theorem edge-ok-keep [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                         as :- (List ActRow), rs :- (List ResRow), K :- (=> Nat Bool), e :- EdgeRow]
  (=> (= (edge-ok cs ts xs as rs e) true) (= (fs-ref K e) true) (= (K (edge-id e)) true)
      (= (edge-ok (tbl-keep K comp-id cs) (tbl-keep K task-id ts) (tbl-keep K source-id xs)
                  (tbl-keep K act-id as) (tbl-keep K resource-id rs) e) true))
  (intros h1 h2 h3)
  (simp only [edge-id] at h3)
  (simp only [fs-ref h3 Bool.not_true Bool.false_or Bool.and_eq_true] at h2)
  (have hx := (kind-excl e))
  (simp only [edge-ok cred-ok deb-ok tbl-has-keep (And.right h2) Bool.true_and])
  (simp only [edge-ok cred-ok deb-ok Bool.and_eq_true] at h1)
  (cases hd (Nat.beq (:kind e) ek-dep))
  (all_goals (cases ho (host-cred e)))
  (all_goals (cases hc (K (:creditor e))))
  (all_goals (simp_all)))

;; ---- ids under the filter: all-ids of the filtered world is all-ids filtered by K

(a/theorem ids-keep [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), xs :- (List A)]
  (= (tbl-ids idf (tbl-keep K idf xs)) (tbl-filter K (tbl-ids idf xs)))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [tbl-ids tbl-keep tbl-filter])
  (cases hk (K (idf h)))
  (all_goals (simp [tbl-ids tbl-keep tbl-filter hk ih])))

(a/theorem filter-nat-app [K :- (=> Nat Bool), xs :- (List Nat), ys :- (List Nat)]
  (= (tbl-filter K (nat-app xs ys)) (nat-app (tbl-filter K xs) (tbl-filter K ys)))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [nat-app tbl-filter])
  (cases hk (K h))
  (all_goals (simp [nat-app tbl-filter hk ih])))

(a/theorem all-ids-keep [w :- World, K :- (=> Nat Bool)]
  (= (all-ids (filter-world K w)) (tbl-filter K (all-ids w)))
  (simp only [all-ids fw-scopes fw-comps fw-tasks fw-runs fw-sources fw-edges fw-acts fw-res fw-pubs fw-forks
              ids-keep filter-nat-app]))

(a/theorem nat-mem-filter [K :- (=> Nat Bool), y :- Nat, xs :- (List Nat)]
  (=> (= (nat-mem y xs) false) (= (nat-mem y (tbl-filter K xs)) false))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hm) (simp [tbl-filter nat-mem])
  (intro hm)
  (cases hy (Nat.beq h y))
  (case [true] (simp [nat-mem hy] at hm))
  (case [false]
    (simp only [nat-mem hy] at hm)
    (cases hk (K h))
    (simp only [tbl-filter hk]) (exact (ih hm))
    (simp only [tbl-filter hk nat-mem hy]) (exact (ih hm))))

(a/theorem nodup-filter [K :- (=> Nat Bool), xs :- (List Nat)]
  (=> (= (nat-nodup xs) true) (= (nat-nodup (tbl-filter K xs)) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hn) (simp [tbl-filter nat-nodup])
  (intro hn)
  (simp only [nat-nodup Bool.and_eq_true] at hn)
  (cases hk (K h))
  (simp only [tbl-filter hk]) (exact (ih (And.right hn)))
  (simp only [tbl-filter hk nat-nodup Bool.and_eq_true])
  (have hm (= (nat-mem h t) false)) (exact (bnot-true _ (And.left hn)))
  (simp only [(nat-mem-filter K h t hm)])
  (exact (And.intro True.intro (ih (And.right hn)))))

(a/theorem ids-ok-keep [w :- World, K :- (=> Nat Bool)]
  (=> (= (ids-ok w) true) (= (ids-ok (filter-world K w)) true))
  (intro h)
  (simp only [ids-ok ids-unique ids-below Bool.and_eq_true] at h)
  (simp only [ids-ok ids-unique ids-below Bool.and_eq_true all-ids-keep fw-next-id])
  (exact (And.intro (nodup-filter K (all-ids w) (And.left h))
           (And.intro (And.left (And.right h))
             (tbl-all-filter Nat (id-in-range (:next-id w)) K (all-ids w) (And.right (And.right h)))))))

(a/theorem inv-filter-world [w :- World, K :- (=> Nat Bool)]
  (=> (= (inv-sample w) true) (= (filter-safe-k K w) true) (= (inv-sample (filter-world K w)) true))
  (intros h hs)
  (have hp (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (simp only [filter-safe-k Bool.and_eq_true] at hs)
  (have h1 (= (pending-exact (filter-world K w)) true))
  (have hin (forall [r :- CompRow]
              (=> (= (comp-exact (:edges w) r) true) (= (K (comp-id r)) true)
                  (= (comp-exact (tbl-keep K edge-id (:edges w)) r) true))))
  (intros r hr hk)
  (simp only [comp-id] at hk)
  (simp only [comp-exact (marked-in-keep K (:id r) (:edges w) (And.right hs) hk)])
  (exact hr)
  (have hpe (= (tbl-all (comp-exact (:edges w)) (:comps w)) true)) (exact (And.left hp))
  (simp only [pending-exact pending-exact-in fw-comps fw-edges])
  (exact (tbl-all-keep CompRow K comp-id (comp-exact (:edges w)) (comp-exact (tbl-keep K edge-id (:edges w)))
           hin (:comps w) hpe))
  (have h2 (= (edges-ref-ok (filter-world K w)) true))
  (have her (= (tbl-all (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) (:edges w)) true))
  (exact (And.left (And.right hp)))
  (simp only [edges-ref-ok edges-ref-ok-in fw-comps fw-tasks fw-sources fw-acts fw-edges])
  (exact (tbl-all-keep2 EdgeRow K edge-id (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) (fs-ref K)
           (edge-ok (tbl-keep K comp-id (:comps w)) (tbl-keep K task-id (:tasks w)) (tbl-keep K source-id (:sources w))
                    (tbl-keep K act-id (:acts w)) (tbl-keep K resource-id (:res w)))
           (edge-ok-keep (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) K) (:edges w) her (And.left hs)))
  (exact (inv-intro (filter-world K w) h1 h2 (ids-ok-keep w K (And.right (And.right hp))))))

(a/theorem inv-rule-r-filter [w :- World]
  (=> (= (inv-sample w) true) (= (filter-safe w) true) (= (inv-sample (rule-r-filter w)) true))
  (intros h hs)
  (rw [rule-r-filter-eq])
  (exact (inv-filter-world w (keep-fn w) h hs)))


;; ---- Rule R: rounds until no orphan (Z#25)

;; One Rule R round = normalization, then the filter (§3.3 step 3). Z#25(a): detach runs once
;; more after the filter; when the filter removed an owner, that detach can close a source and
;; finalize it, so the model runs another round (normalize starts with detach) until a round
;; leaves no orphan. `rr-loop` with list fuel 1 + #ids; the result is always the output of a
;; last round, whose input is `rule-r-pre` (`rr-loop-eq`); `rr-safe` collects the filter-safe
;; hypothesis of every round, `no-orphans` of the result is the loop's flag (tests check both).
(a/defn rule-r-round [w :- World] World (rule-r-filter (normalize w)))
;; w1 is the output of the previous round
(a/defn rr-loop [fuel :- (List Nat), w1 :- World] World
  (match fuel
    [nil w1]
    [(cons h f) (if (no-orphans w1) w1 (rr-loop f (rule-r-round w1)))]))
(a/defn rr-fuel [w :- World] (List Nat) (List.cons Nat 0 (all-ids w)))
(a/defn rule-r [w :- World] World (rr-loop (rr-fuel w) (rule-r-round w)))
;; the input of the last round
(a/defn rr-pre [fuel :- (List Nat), w0 :- World] World
  (match fuel
    [nil w0]
    [(cons h f) (if (no-orphans (rule-r-round w0)) w0 (rr-pre f (rule-r-round w0)))]))
(a/defn rule-r-pre [w :- World] World (rr-pre (rr-fuel w) w))
;; filter-safe for every round
(a/defn rr-safe [fuel :- (List Nat), w0 :- World] Bool
  (match fuel
    [nil (filter-safe (normalize w0))]
    [(cons h f) (Bool.and (filter-safe (normalize w0))
                          (if (no-orphans (rule-r-round w0)) true (rr-safe f (rule-r-round w0))))]))
(a/defn rule-r-safe [w :- World] Bool (rr-safe (rr-fuel w) w))

;; ===========================================================================
;; Part J. Theorems about Rule R and the step
;; ===========================================================================

;; ---- inv-sample

(a/theorem inv-rule-r-round [w :- World]
  (=> (= (inv-sample w) true) (= (filter-safe (normalize w)) true) (= (inv-sample (rule-r-round w)) true))
  (intros h hs)
  (exact (inv-rule-r-filter (normalize w) (inv-normalize w h) hs)))

;; the loop's result is the last round's output
(a/theorem rr-loop-eq [fuel :- (List Nat)]
  (forall [w0 :- World] (= (rr-loop fuel (rule-r-round w0)) (rule-r-round (rr-pre fuel w0))))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intro w0) (simp only [rr-loop rr-pre])
  (intro w0)
  (cases ho (no-orphans (rule-r-round w0)))
  (simp only [rr-loop rr-pre ho]) (exact (ih (rule-r-round w0)))
  (simp only [rr-loop rr-pre ho]))

(a/theorem rule-r-eq [w :- World] (= (rule-r w) (rule-r-round (rule-r-pre w)))
  (simp only [rule-r rule-r-pre]) (exact (rr-loop-eq (rr-fuel w) w)))

(a/theorem inv-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (inv-sample w0) true) (= (rr-safe fuel w0) true)
                            (= (inv-sample (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w0 h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (inv-rule-r-round w0 h hs))
  (intros w0 h hs)
  (simp only [rr-safe Bool.and_eq_true] at hs)
  (have h1 := (inv-rule-r-round w0 h (And.left hs)))
  (cases ho (no-orphans (rule-r-round w0)))
  (simp only [ho] at hs) (simp only [rr-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs)))
  (simp only [rr-loop ho]) (exact h1))

(a/theorem inv-rule-r [w :- World]
  (=> (= (inv-sample w) true) (= (rule-r-safe w) true) (= (inv-sample (rule-r w)) true))
  (intros h hs)
  (simp only [rule-r-safe] at hs) (simp only [rule-r])
  (exact (inv-rr-loop (rr-fuel w) w h hs)))

;; ---- soundness of the normalized flag (the §3.3 proof shape's replacement of the frame lemma)

(a/theorem tbl-all-mem [A :- Type, P :- (=> A Bool), x :- A, xs :- (List A)]
  (=> (= (tbl-all P xs) true) (List.Mem x xs) (= (P x) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intros hp hm) (cases hm)
  (intros hp hm)
  (simp only [tbl-all Bool.and_eq_true] at hp)
  (cases hm)
  (exact (And.left hp))
  (rename_i hm2)
  (exact (ih (And.right hp) hm2)))

;; normalized w: every run that is not done is in live(W) ...
(a/theorem normalized-runs [w :- World, r :- RunRow]
  (=> (= (normalized w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (in-live w (:id r)) true))
  (intros hn hm ha)
  (simp only [normalized normalized-with Bool.and_eq_true] at hn)
  (have hp := (tbl-all-mem RunRow (run-norm (live-list w)) r (:runs w) (And.left hn) hm))
  (simp only [run-norm ha Bool.not_true Bool.false_or] at hp)
  (exact hp))

;; ... and every computation that is not idle is in live(W)
(a/theorem normalized-comps [w :- World, c :- CompRow]
  (=> (= (normalized w) true) (List.Mem c (:comps w)) (= (:idle c) false) (= (in-live w (:id c)) true))
  (intros hn hm hi)
  (simp only [normalized normalized-with Bool.and_eq_true] at hn)
  (have hp := (tbl-all-mem CompRow (comp-norm (live-list w)) c (:comps w) (And.right hn) hm))
  (simp only [comp-norm hi Bool.false_or] at hp)
  (exact hp))

;; ---- the filter keeps the world normalized (live is stable under it)

(a/theorem rr-runs [w :- World] (= (:runs (rule-r-filter w)) (tbl-keep (keep-fn w) run-id (:runs w))) (rfl))
(a/theorem rr-comps [w :- World] (= (:comps (rule-r-filter w)) (tbl-keep (keep-fn w) comp-id (:comps w))) (rfl))

(a/theorem rule-r-filter-normalized [w :- World]
  (=> (= (live-converged w) true) (= (live-converged (rule-r-filter w)) true) (= (normalized w) true)
      (= (normalized (rule-r-filter w)) true))
  (intros hc hc2 hn)
  (simp only [normalized normalized-with Bool.and_eq_true] at hn)
  (have er (forall [r :- RunRow] (= (run-norm (live-list (rule-r-filter w)) r) (run-norm (live-list w) r))))
  (intro r)
  (have e (= (in-live (rule-r-filter w) (:id r)) (in-live w (:id r)))) (exact (rule-r-live w (:id r) hc hc2))
  (simp only [in-live] at e)
  (simp only [run-norm e])
  (have ec (forall [c :- CompRow] (= (comp-norm (live-list (rule-r-filter w)) c) (comp-norm (live-list w) c))))
  (intro c)
  (have e (= (in-live (rule-r-filter w) (:id c)) (in-live w (:id c)))) (exact (rule-r-live w (:id c) hc hc2))
  (simp only [in-live] at e)
  (simp only [comp-norm e])
  (simp only [normalized normalized-with Bool.and_eq_true rr-runs rr-comps])
  (rw [(tbl-all-congr RunRow (run-norm (live-list (rule-r-filter w))) (run-norm (live-list w)) er
         (tbl-keep (keep-fn w) run-id (:runs w)))])
  (rw [(tbl-all-congr CompRow (comp-norm (live-list (rule-r-filter w))) (comp-norm (live-list w)) ec
         (tbl-keep (keep-fn w) comp-id (:comps w)))])
  (exact (And.intro (tbl-all-keep-same RunRow (keep-fn w) run-id (run-norm (live-list w)) (:runs w) (And.left hn))
                    (tbl-all-keep-same CompRow (keep-fn w) comp-id (comp-norm (live-list w)) (:comps w) (And.right hn)))))

;; ---- Rule R: I3 and I4

(a/theorem rule-r-i3-step [w :- World]
  (=> (= (live-converged (normalize (rule-r-pre w))) true) (= (live-converged (rule-r w)) true)
      (= (tbl-all (keep-fn (rule-r w)) (all-ids (rule-r w))) true))
  (intros hc hc2)
  (rw [rule-r-eq] at hc2) (rw [rule-r-eq])
  (exact (rule-r-i3 (normalize (rule-r-pre w)) hc hc2)))

(a/theorem rule-r-normalized [w :- World]
  (=> (= (live-converged (normalize (rule-r-pre w))) true) (= (live-converged (rule-r w)) true)
      (= (normalized (normalize (rule-r-pre w))) true) (= (normalized (rule-r w)) true))
  (intros hc hc2 hn)
  (rw [rule-r-eq] at hc2) (rw [rule-r-eq])
  (exact (rule-r-filter-normalized (normalize (rule-r-pre w)) hc hc2 hn)))

