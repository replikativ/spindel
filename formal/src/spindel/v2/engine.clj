(ns spindel.v2.engine
  "Layer-1 transitions that create runs and wire activations (spec v1.5.1 §5.1) and the
  model's step `world-step w item = finish (raw w item)`: an accepted raw outcome is followed
  by Rule R (`rule/rule-r`), a refusal is the input world. Kernel-checked, Init only.

  Parts:
    A  fresh-row inserts: `cred-ok-mono`/`deb-ok-mono`, `inv-<p>-ins-fresh` for scope, run,
       task, act, comp; `insert-edge-checked` (inserts only when the endpoints exist: the
       guards make it true, the lemma needs no guard bookkeeping)
    B  `add-run-scope` (run R = next-id, stamp R, its run scope R + 1); §3.4 validation
       (`valid-loop` worklist, each idle computation expanded once, list fuel, out of fuel =
       invalid; P6) and reactivation
       (`react-loop`, `demand-reactive`)
    C  T4 spawn (task, run, run scope; Z#26 parent = the owner scope or 0), T5 start (fresh or
       invalid idle; parent 0), T3 create-comp (absent / adopt / replace)
    D  T11 dispatch (needs-run, eligible; E = earliest fired dep edge in creation order (least id), Z#59; predecessor
       cancel(R, replace); dep edges created after E removed (siblings at E's site too, Z#59), baselines to adoption (Z#21), creations split
       basis/adoption; E consumed: restart re-arms with the OLD baseline (Z#22), resume with
       the new one; removed when the debtor is final, on resume and restart (Z#39); new run
       at E.at + 1 or 0 (Z#12))
    E  settle (§4.5.2: changed fires the out-edges, Z#20 delivers to current members in both
       cases, observe edges deliver and host waits are consumed (Z#9, Z#27), unchanged
       settles cascade through a worklist) and T12 complete (current/stale computation run,
       task: result, Q10 child cancel, wait creditors and dep creditors fire; armed resources
       cancelled; cleanup[R] unless retirable; T13 by the cascade; T10 when final)
    F  T6 await (one/all/any; activation id always allocated, Z#28; member edges per distinct
       debtor, a duplicate debtor one edge at several indices, Z#7; site edge reuse; fast path;
       park unless resumed; T10 on final debtors; ::cycle refusal), T22 host-await/unawait,
       T8 with validation and the Z#15 initial delivery, the scheduling choice, handle-new
       (Z#29), and the `any` loser cancel (`cancel-losers`, run after every accepted raw item)
    F2 source operations (§4.3: deliver, post, take = take/acquire, release), finally regions
       (B3: finally-enter/-exit), the `finalize R` cleanup slice (B8), host cancel (T14),
       open/close-scope (T16), detach (Q10), release-world (T21), B8 refusals (`in-cleanup`)
    G  `raw0` (every Item), `raw` = loser cancel after raw0, `world-step`, and the theorems
  Also: I12 ranks (`raise-run`: height adjustment before every new comp-comp dep edge of T6
  and of a reactivation; `ranks-ok`, checked by the tests after every step) and Blocked as
  the least fixpoint (`blocked-set` = spindel.v2.reach's Derive via `derive-run-l`;
  `blocked-sound`, `blocked-complete`).

  Theorems (per transition: -inv = inv-sample preserved, -refuse = a refusal leaves the world
  unchanged; L4 for the whole step):
    t3-inv/-refuse, t3-top-inv/-refuse, t4-*, t4-top-*, t5-*, t6-*, t11-*, t12-*, t22-*,
    t22-un-*, t8-full-*, sched-*, t-handle-new-*; t-deliver-*, t-post-*, t-take-* (+ -l4),
    t-release-*, t-finalize-*, t-cancel-*, t-release-world-*, t-open-scope-* (+ -l4),
    t-close-scope-*, t-detach-*, t-finally-enter-* / t-finally-exit-* (+ -l4), t-slice-exit-*
    (-inv, -refuse); inv-deliver-fire;
    inv-raise-loop, inv-raise-for, blocked-sound, blocked-complete; raw0-inv, raw0-refuse, raw0-l4 (every
    constructor); raw-inv, raw-refuse, raw-l4 (with the loser cancel);
    step-refuse, step-l4 (invalid token -> (refuse w)), step-accepted,
    step-inv     inv-sample w, rule-r-safe raw-world -> inv-sample (world-step w it)
    step-i3      accepted, live converged before/after the last round's filter -> I3
    step-normalized, step-i4   ... and normalized (normalize (rule-r-pre raw-world)) -> the
                 step's world is normalized and every non-done run is in its live set (I4)
  Honest hypotheses, checked by the tests after every step: the flags of rule.clj, plus
  `settle-done`/`fin-done` for the worklists (settle-done is proved, spindel.v2.l5
  `settle-done-ok`; fin-done holds trivially: comp-final is false, so the worklist is [d]).

  Readings (numbered; the rule.clj list continues to apply):
    B1. Demand (T6, T8, T22): only the reactive revalidation of a valid idle computation
        happens inside the transition (it allocates its edges after the item's own rows).
        Starting a fresh or invalid computation (T5) and re-running a needs-run one (T11) are
        separate items the engine issues next (\"the demanded debtor's first slice is the next
        step\"); the T5/T11 fresh-id order of the contract is then per item.
    B2. T5 on an idle computation with a result (invalid) steps its epoch, so it is dirty, not
        live, while the new run runs. A fresh computation (done-epoch none, idle or not, §2)
        starts without an epoch step. Validation never succeeds without a result.
    B3. T3 adoption and replacement leave handles unchanged (Z#29); creation sets 1. The item
        names the computation id (the engine's row id for the deterministic key); an absent
        id must be next-id. T3 does not validate an idle adoptee; demand does.
    B4. Eligibility (§4.5.7): every computation debtor of C is not dirty or is Blocked, the
        least fixpoint of §4.5.6 (`blocked-set`, Derive; spec answer: the engine uses it).
    B5. Z#30: settle fires every dep out-edge whose consumed version (`seen`, none counts as
        different) differs from D's version; otherwise only Z#20's delivery to a current
        member. Settle is triggered by a current completion and cascades to creditors whose
        last marked edge was unmarked; demotion and removal do not settle.
    B6. T6 parks the run (act parked, slice released) unless the fast path resumed the
        activation in the same commit; then the run stays active with its slice.
    B7. I12: ranks are maintained by height adjustment (`raise-run`) before T6 and a
        reactivation add a dep edge between computations; T6 refuses a cycle (a computation
        awaiting itself or one that reaches it through dep edges, which on a ranks-ok world is
        exactly \"the propagation reaches the debtor\"). A reactivation edge whose raise fails
        (a cycle through validity, not expected) is still added; `ranks-ok` is the tripwire.
    B8. T6 debtors: in a computation run a dep edge for computation, task and source
        debtors, a wait edge for a resource (Z#6); in a task run wait edges. Fast-ready: a
        live (or valid idle) computation, a completed task, a closed source, a delivered
        deferred, a fired resource, and (Z#31) a signal or cell, read at once (in a
        computation through its dep edge, like track; in a task as a snapshot whose wait edge
        goes with the resumed activation); an open deferred waits. Z#54: a mailbox or
        semaphore member is refused (`await-kind-bad` in raw0; the engine logs an await on a
        mailbox as `take`), so no dep edge has a mailbox or semaphore debtor.
    B9. `any` losers (engine `cancel-losers!`): when an `any` activation of a TASK run
        resolved and its run is not done, the tasks of `mine` (the activation's `spawned`)
        that are owned by the run's scope, still run and have no other out-edge are cancelled
        (ordinary cancel).
    B10. T22: the host-wait edge is consumed by the debtor's settle, a task's completion, a
        resource fire, at once when the debtor is fast-ready, or by the close of its source
        (Z#53, rule.clj `wake-closed`). Z#54: a host read of a mailbox or semaphore is refused
        (`deb-consuming` in raw0).
    B11. T12 releases the adoption basis: the predecessor's suffix creations (at > E.at)
        that the new run did not re-adopt (re-creation or re-spawn moves an id back into the
        basis); their running tasks are cancelled; prefix creations stay; the adoption
        basis and baselines are discarded.
    B12. The scheduling choice gives the slice to an active, normal run when no run holds
        one; a cleanup slice is given by `finalize R` (Part F2).
    B13. Z#32: computations are never final (rule.clj `comp-final` is false): dep edges on
        computations are never finalized; T10 applies to tasks, deferreds, closed sources.
    B14. §5.2 re-spawn: in a computation run, `spawn` whose `fresh` names a task in C's basis
        or adoption basis adopts it (no allocation; the logged inputs must equal the task's
        `inputs`, else refused); the task moves to the basis at the new site. Otherwise
        `fresh` must be next-id (task, run, run scope). Captured inputs are lists of Nats on
        computations and tasks; T3's equal-inputs test is list equality.
    B15. A task spawned in a task run is owned by the run's current scope (the innermost open
        explicit scope it opened, else its run scope; engine `current-scope!`), computed as
        the largest open explicit scope reachable from the run scope through open explicit
        children. T3 creations keep the run scope (as the engine); T1 sources: B22.
    B16. deliver (§4.3): only an open, undelivered deferred (version 0). It is a write for
        state := v, version := 1, its dep/observe edges fire (Z#36: not a write, nothing is
        marked), every wait edge on it fires with ok v, then T10 (it is final).
    B17. post/release: refused on a closed source (read-only, T16); the waiter is the oldest
        (smallest id) armed wait edge on X whose activation's run is current and parked
        (stale runs skipped; a cancelled run's waiters left with its activation); it is
        served through T9 (ok v / ok 1). take = acquire on a semaphore: a body effect of a
        normal run; available -> consumed at once (version + 1, two ids allocated and not
        kept); otherwise a `one` activation and its wait edge, the run parks. Z#57: a closed
        mailbox/semaphore still hands out what is left; with nothing left the take fails at once
        with err ::closed (ids allocated, effect index + 1, the run keeps its slice: `take-ready`).
    B18. finally-enter/-exit are body items (engine `[:finally-enter st]`/`[:finally-exit st]`).
        Regions open only in normal runs (B8: no finalizer adds one); the engine holds the
        regions' refs implicitly (closures), so a region is (F 0, at = effect-index, refs []).
        Z#35: `finalize R` gives the cleanup slice to a done, unwinding run with a region, when
        no run holds a slice; that one slice runs the whole chain innermost first, each
        region's exit a `finally-exit` (it pops the head region, committed at the block's
        start, so L2's measure drops per finalizer); after the last exit the outermost block
        still runs in the slice, and `slice-exit R` (the slice returns: R done, holding the
        slice, no region) releases it and runs T13. Z#40: a cleanup slice may only write,
        deliver, post, release and close: await/take/complete/finally-enter/open-scope need a
        normal run, and create-source/track/arm/spawn/create-comp are refused by raw0
        (`in-cleanup`). Z#43: complete with an open region is refused by raw0 (`fins-open`).
        Z#44: host items (no token) are accepted while a slice is held: they are effects of
        the slice-holding run (D0); the model has no per-run attribution state, so nothing
        else changes (host cancel of the slice-holding run itself is refused, B19, Z#37).
    B19. Host cancel R: R is a task's run that is not done and holds no slice (Z#37); an
        ordinary T14 with cascade (Z#39: the task is final, its dep creditors get the error).
    B20. open-scope st s: s = fresh, a child of the run's current scope, a body effect of a
        normal run without an effect-index step (as the engine). close-scope s: T16 on an
        explicit scope, no token. detach k s: a task without result whose owner is a scope
        moves to the open scope s, and its run scope is re-parented under s (Z#41); the old
        owner's subtree is then removed when empty.
    B21. release-world: refused when already released; removes every host-creditor edge
        (observe, host waits), drops pins, abandons pending-activation, sets every handle
        count to 0 (spec: released handles' rows are removed; the engine keeps handle counts),
        then T16 on the root scope (2). Later host items are not refused globally: top-level
        creations need an open scope, handle operations find 0 handles.
    B22. T1 in a body (`t1-full`, replacing step's T1 in the step): a computation run adopts a
        source of its basis/adoption basis named by `fresh` (creation order; same kind; no
        allocation); otherwise a new source owned by the computation, or in a task run by the
        run's current scope (B15).
    B23. Z#33: every demand (T6 in any run, T8, T22) on an idle computation clears `idle` in
        the demanding transition: a valid one is reactivated, a fresh or invalid one keeps no
        validity, and an invalid one gets the epoch step (B2 moves here), so the following T5
        starts it (`startable` admits it: not idle, done-epoch /= epoch, no run, no dep
        edges). Z#34: a fill resumes the run in the filling commit (active, slice-less); every
        new run (T4, T5, T11) is slice-less until `schedule` (as before).
    B24. Z#55: a resource effect is one item `arm st kind k fresh` (T17 + its park): resource
        fresh, `one` activation fresh + 1 (cont k), its wait edge fresh + 2 (at = the effect
        index), the run parks, effect-index + 1; kind timer or offload (`arm-kind-ok`); a normal
        run only. T15 needs only the resource row and no edge on it (Z#6), so it is accepted any
        time after T14 put the resource in cancelling, and retires the run within the item.
        Z#53: closing or detaching a source (rule.clj `close-source`/`detach-source`) wakes its
        armed wait edges and its armed member dep edges with `deb-result` (err ::closed = 2 for
        a mailbox, semaphore or undelivered deferred, step.clj `src-result`), then T10."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]))

;; ===========================================================================
;; Part A. Inserting fresh rows: monotone edges-ref-ok, inv-sample per table
;; ===========================================================================

(a/theorem cred-ok-mono [cs :- (List CompRow), cs2 :- (List CompRow), as :- (List ActRow), as2 :- (List ActRow),
                         e :- EdgeRow,
                         hc :- (forall [y :- Nat] (=> (= (tbl-has comp-id y cs) true) (= (tbl-has comp-id y cs2) true))),
                         ha :- (forall [y :- Nat] (=> (= (tbl-has act-id y as) true) (= (tbl-has act-id y as2) true)))]
  (=> (= (cred-ok cs as e) true) (= (cred-ok cs2 as2 e) true))
  (intro h)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [true] (simp only [cred-ok hk] at h) (simp only [cred-ok hk]) (exact (hc _ h)))
  (case [false]
    (cases hh (host-cred e))
    (case [true] (simp [cred-ok hk hh]))
    (case [false] (simp only [cred-ok hk hh] at h) (simp only [cred-ok hk hh]) (exact (ha _ h)))))

(a/theorem deb-ok-mono [cs :- (List CompRow), cs2 :- (List CompRow), ts :- (List TaskRow), ts2 :- (List TaskRow),
                        xs :- (List SourceRow), xs2 :- (List SourceRow), rs :- (List ResRow), rs2 :- (List ResRow),
                        e :- EdgeRow,
                        hc :- (forall [y :- Nat] (=> (= (tbl-has comp-id y cs) true) (= (tbl-has comp-id y cs2) true))),
                        ht :- (forall [y :- Nat] (=> (= (tbl-has task-id y ts) true) (= (tbl-has task-id y ts2) true))),
                        hx :- (forall [y :- Nat] (=> (= (tbl-has source-id y xs) true) (= (tbl-has source-id y xs2) true))),
                        hr :- (forall [y :- Nat] (=> (= (tbl-has resource-id y rs) true) (= (tbl-has resource-id y rs2) true)))]
  (=> (= (deb-ok cs ts xs rs e) true) (= (deb-ok cs2 ts2 xs2 rs2 e) true))
  (intro h)
  (simp only [deb-ok Bool.or_eq_true Bool.and_eq_true] at h)
  (simp only [deb-ok Bool.or_eq_true Bool.and_eq_true])
  (cases h)
  (rename_i h1) (exact (Or.inl (hc _ h1)))
  (rename_i h1) (cases h1)
  (rename_i h2) (exact (Or.inr (Or.inl (ht _ h2))))
  (rename_i h2) (cases h2)
  (rename_i h3) (exact (Or.inr (Or.inr (Or.inl (hx _ h3)))))
  (rename_i h3) (exact (Or.inr (Or.inr (Or.inr (And.intro (And.left h3) (hr _ (And.right h3))))))))

(a/theorem has-ins-mono [A :- Type, idf :- (=> A Nat), r :- A, xs :- (List A)]
  (forall [y :- Nat] (=> (= (tbl-has idf y xs) true) (= (tbl-has idf y (tbl-ins r xs)) true)))
  (intros y h) (simp [tbl-has-ins h]))

(a/theorem has-same [A :- Type, idf :- (=> A Nat), xs :- (List A)]
  (forall [y :- Nat] (=> (= (tbl-has idf y xs) true) (= (tbl-has idf y xs) true)))
  (intros y h) (exact h))

(a/theorem comp-ins-edges-ref-ok [w :- World, r :- CompRow]
  (=> (= (edges-ref-ok w) true) (= (edges-ref-ok (comp-ins w r)) true))
  (intro h)
  (have hpq (forall [e :- EdgeRow]
              (=> (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) e) true)
                  (= (edge-ok (tbl-ins r (:comps w)) (:tasks w) (:sources w) (:acts w) (:res w) e) true))))
  (intros e he)
  (simp only [edge-ok Bool.and_eq_true] at he)
  (simp only [edge-ok Bool.and_eq_true])
  (exact (And.intro
           (cred-ok-mono (:comps w) (tbl-ins r (:comps w)) (:acts w) (:acts w) e
             (has-ins-mono CompRow comp-id r (:comps w)) (has-same ActRow act-id (:acts w)) (And.left he))
           (deb-ok-mono (:comps w) (tbl-ins r (:comps w)) (:tasks w) (:tasks w) (:sources w) (:sources w)
             (:res w) (:res w) e (has-ins-mono CompRow comp-id r (:comps w)) (has-same TaskRow task-id (:tasks w))
             (has-same SourceRow source-id (:sources w)) (has-same ResRow resource-id (:res w)) (And.right he))))
  (simp only [edges-ref-ok comp-ins set-comps edges-ref-ok-in])
  (exact (tbl-all-mono EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w))
           (edge-ok (tbl-ins r (:comps w)) (:tasks w) (:sources w) (:acts w) (:res w)) hpq (:edges w) h)))

(a/theorem task-ins-edges-ref-ok [w :- World, r :- TaskRow]
  (=> (= (edges-ref-ok w) true) (= (edges-ref-ok (task-ins w r)) true))
  (intro h)
  (have hpq (forall [e :- EdgeRow]
              (=> (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) e) true)
                  (= (edge-ok (:comps w) (tbl-ins r (:tasks w)) (:sources w) (:acts w) (:res w) e) true))))
  (intros e he)
  (simp only [edge-ok Bool.and_eq_true] at he)
  (simp only [edge-ok Bool.and_eq_true])
  (exact (And.intro (And.left he)
           (deb-ok-mono (:comps w) (:comps w) (:tasks w) (tbl-ins r (:tasks w)) (:sources w) (:sources w)
             (:res w) (:res w) e (has-same CompRow comp-id (:comps w)) (has-ins-mono TaskRow task-id r (:tasks w))
             (has-same SourceRow source-id (:sources w)) (has-same ResRow resource-id (:res w)) (And.right he))))
  (simp only [edges-ref-ok task-ins set-tasks edges-ref-ok-in])
  (exact (tbl-all-mono EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w))
           (edge-ok (:comps w) (tbl-ins r (:tasks w)) (:sources w) (:acts w) (:res w)) hpq (:edges w) h)))

(a/theorem act-ins-edges-ref-ok [w :- World, r :- ActRow]
  (=> (= (edges-ref-ok w) true) (= (edges-ref-ok (act-ins w r)) true))
  (intro h)
  (have hpq (forall [e :- EdgeRow]
              (=> (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) e) true)
                  (= (edge-ok (:comps w) (:tasks w) (:sources w) (tbl-ins r (:acts w)) (:res w) e) true))))
  (intros e he)
  (simp only [edge-ok Bool.and_eq_true] at he)
  (simp only [edge-ok Bool.and_eq_true])
  (exact (And.intro
           (cred-ok-mono (:comps w) (:comps w) (:acts w) (tbl-ins r (:acts w)) e
             (has-same CompRow comp-id (:comps w)) (has-ins-mono ActRow act-id r (:acts w)) (And.left he))
           (And.right he)))
  (simp only [edges-ref-ok act-ins set-acts edges-ref-ok-in])
  (exact (tbl-all-mono EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w))
           (edge-ok (:comps w) (:tasks w) (:sources w) (tbl-ins r (:acts w)) (:res w)) hpq (:edges w) h)))

(defmacro ^:private definv-ins
  "inv-<p>-ins-fresh: inserting a row whose id is next-id, then bumping, keeps inv-sample.
  `pe` proves pending-exact of the insert from pending-exact w, `er` edges-ref-ok."
  [prefix row pe er]
  (let [ins (symbol (str prefix "-ins")) idf (symbol (str prefix "-id"))]
    `(a/theorem ~(symbol (str "inv-" prefix "-ins-fresh")) [~'w :- ~'World, ~'r :- ~row]
       (~'=> (~'= (~idf ~'r) (:next-id ~'w)) (~'= (~'inv-sample ~'w) true)
             (~'= (~'inv-sample (~'bump (~ins ~'w ~'r))) true))
       (~'intros ~'hr ~'h)
       (~'have ~'hs (~'And (~'= (~'pending-exact ~'w) true) (~'And (~'= (~'edges-ref-ok ~'w) true) (~'= (~'ids-ok ~'w) true))))
       (~'exact (~'inv-parts ~'w ~'h))
       (~'exact (~'inv-intro (~'bump (~ins ~'w ~'r))
                  (~'Eq.trans (~'pending-exact-bump (~ins ~'w ~'r)) ~pe)
                  (~'Eq.trans (~'edges-ref-ok-bump (~ins ~'w ~'r)) ~er)
                  (~(symbol (str prefix "-ins-fresh-ids-ok")) ~'w ~'r ~'hr (~'And.right (~'And.right ~'hs))))))))

(definv-ins scope ScopeRow (Eq.trans (pending-exact-scope-ins w r) (And.left hs))
  (Eq.trans (edges-ref-ok-scope-ins w r) (And.left (And.right hs))))
(definv-ins run RunRow (Eq.trans (pending-exact-run-ins w r) (And.left hs))
  (Eq.trans (edges-ref-ok-run-ins w r) (And.left (And.right hs))))
(definv-ins task TaskRow (Eq.trans (pending-exact-task-ins w r) (And.left hs))
  (task-ins-edges-ref-ok w r (And.left (And.right hs))))
(definv-ins act ActRow (Eq.trans (pending-exact-act-ins w r) (And.left hs))
  (act-ins-edges-ref-ok w r (And.left (And.right hs))))

;; a computation arrives with its exact pending: the count of marked edges naming it (0 for a
;; fresh id in any world built by the transitions; computed so the lemma needs no I2 fact)
(a/theorem inv-comp-ins-fresh [w :- World, r :- CompRow]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (inv-sample w) true) (= (inv-sample (bump (comp-ins w r))) true))
  (intros hr hp h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (exact (inv-intro (bump (comp-ins w r))
           (Eq.trans (pending-exact-bump (comp-ins w r)) (pending-exact-comp-ins w r hp (And.left hs)))
           (Eq.trans (edges-ref-ok-bump (comp-ins w r)) (comp-ins-edges-ref-ok w r (And.left (And.right hs))))
           (comp-ins-fresh-ids-ok w r hr (And.right (And.right hs))))))

;; insert an edge only when its endpoints exist (the transitions' guards make the check
;; true; it keeps the lemmas free of the guard bookkeeping)
(a/defn insert-edge-checked [w :- World, e :- EdgeRow] World
  (if (edge-ok-in w e) (insert-edge-fresh w e) w))

(a/theorem inv-insert-edge-checked [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (inv-sample (insert-edge-checked w e)) true))
  (intro h)
  (cases hk (edge-ok-in w e))
  (simp only [insert-edge-checked hk]) (exact h)
  (simp only [insert-edge-checked hk]) (exact (insert-edge-fresh-inv-sample w e hk h)))

;; ===========================================================================
;; Part B. Row constructors; a run with its run scope; §3.4 validation and reactivation
;; ===========================================================================

(a/defn none-result [] RunResult (RunResult.mk res-none 0))
(a/defn new-scope-row [id :- Nat, parent :- Nat] ScopeRow (ScopeRow.mk id parent scope-run true))
;; run stamp = run id (oracle contract)
(a/defn new-run-row [id :- Nat, of :- Nat, epoch :- Nat, scope :- Nat, ei :- Nat] RunRow
  (RunRow.mk id of id epoch scope act-active mode-normal false ei (List.nil Finalizer) (List.nil Nat)))
(a/defn new-task-row [id :- Nat, owner :- Nat, run :- Nat, inputs :- (List Nat)] TaskRow (TaskRow.mk id owner run none-result 1 inputs))

;; a run R (id next-id) of entity `of`, with its run scope S (next-id + 1, parent `parent`)
(a/defn add-run-scope [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat] World
  (bump (scope-ins (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))
                   (new-scope-row (+ (:next-id w) 1) parent))))

(a/theorem inv-add-run-scope [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (add-run-scope w of epoch parent ei)) true))
  (intro h)
  (simp only [add-run-scope])
  (have h1 (= (inv-sample (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))) true))
  (exact (inv-run-ins-fresh w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) (rfl) h))
  (have he (= (scope-id (new-scope-row (+ (:next-id w) 1) parent))
              (:next-id (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei))))))
  (rfl)
  (exact (inv-scope-ins-fresh (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))
           (new-scope-row (+ (:next-id w) 1) parent) he h1)))

;; ---- validation (§3.4, R#3): a worklist over validity entries with list fuel. An entry
;; (d, v) is valid when d is a source or task with version v, or a computation that is not
;; dirty, has no run in progress and has version v; an idle computation's own entries are
;; checked in turn (recursion through the worklist, not by rank), each idle computation's
;; entries once (`seen`: the check is pure, so a second expansion adds nothing; the engine's
;; recursive `validate!` reactivates the debtor, so it too expands it once). Out of fuel =
;; invalid.
;; P6 (found by branch z57): without `seen` the walk followed every path of the validity DAG
;; (a chain of k idle computations each validating the next through m entries has m^k paths)
;; and ran out of the fuel 1 + #entries x (1 + #comps) on reachable worlds (m = 4, k = 3): the
;; top computation was declared invalid and re-run where the engine reactivates it (engine_test
;; `p6-validity-chain`). With `seen` every computation is expanded at most once, so the pops are
;; bounded by its own entries plus all validity entries: fuel 2 + #entries (`valid-done-ok`,
;; spindel.v2.react).

(a/defn run-busy [w :- World, c :- CompRow] Bool
  (match (run-find w (:run c)) [none false] [(some r) (run-alive r)]))
(a/defn comp-clean [w :- World, c :- CompRow, v :- Valid] Bool
  (Bool.and (Bool.or (:idle c) (comp-live c))
            (Bool.and (Bool.not (run-busy w c)) (Nat.beq (:version c) (:version v)))))
(a/defn valid-loop [fuel :- (List Nat), w :- World, seen :- (List Nat), vs :- (List Valid)] Bool
  (match fuel
    [nil false]
    [(cons h f) (match vs
                  [nil true]
                  [(cons v t) (match (comp-find w (:debtor v))
                                [none (if (Bool.or (source-has w (:debtor v)) (task-has w (:debtor v)))
                                          (if (Nat.beq (deb-version w (:debtor v)) (:version v)) (valid-loop f w seen t) false)
                                          false)]
                                [(some c) (if (comp-clean w c v)
                                              (if (Bool.and (:idle c) (Bool.not (reach-mem (:id c) seen)))
                                                  (valid-loop f w (List.cons Nat (:id c) seen) (List.append Valid (:validity c) t))
                                                  (valid-loop f w seen t))
                                              false)])])]))
;; fuel: 2 + the number of validity entries of all computations
(a/defn valid-zeros [vs :- (List Valid)] (List Nat)
  (match vs [nil (List.nil Nat)] [(cons h t) (List.cons Nat 0 (valid-zeros t))]))
(a/defn all-valid-zeros [cs :- (List CompRow)] (List Nat)
  (match cs [nil (List.nil Nat)] [(cons h t) (List.append Nat (valid-zeros (:validity h)) (all-valid-zeros t))]))
(a/defn valid-fuel [w :- World] (List Nat)
  (List.cons Nat 0 (List.cons Nat 0 (all-valid-zeros (:comps w)))))
;; only a computation with a result can be valid (a fresh idle one, done-epoch none, has
;; nothing to reuse); its own entries are the start (it is seen)
(a/defn valid-idle [w :- World, c :- CompRow] Bool
  (Bool.and (Bool.not (Nat.beq (:done-epoch c) 0))
            (valid-loop (valid-fuel w) w (List.cons Nat (:id c) (List.nil Nat)) (:validity c))))

(a/defn comp-rank [w :- World, x :- Nat] Nat (match (comp-find w x) [none 0] [(some c) (:rank c)]))
(a/defn comp-set-rank [n :- Nat, c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (:epoch c) (:done-epoch c)
              (:pending c) n (:version c) (:result c) (:idle c) (:validity c) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) (:handles c)))
(a/theorem comp-set-rank-id [n :- Nat, c :- CompRow] (= (comp-id (comp-set-rank n c)) (comp-id c)) (rfl))
(a/theorem comp-set-rank-pending [n :- Nat, c :- CompRow] (= (:pending (comp-set-rank n c)) (:pending c)) (rfl))
(a/structure RJ [] (node Nat) (need Nat))
(a/structure RaiseRes [] (world World) (ok Bool))
(a/defn rjobs [n :- Nat, ys :- (List Nat)] (List RJ)
  (match ys [nil (List.nil RJ)] [(cons h t) (List.cons RJ (RJ.mk h n) (rjobs n t))]))
(a/defn raise-loop [fuel :- (List Nat), d :- Nat, w :- World, todo :- (List RJ)] RaiseRes
  (match fuel
    [nil (match todo [nil (RaiseRes.mk w true)] [(cons j t) (RaiseRes.mk w false)])]
    [(cons u f) (match todo
                  [nil (RaiseRes.mk w true)]
                  [(cons j t) (if (Nat.beq (:node j) d)
                                  (RaiseRes.mk w false)
                                  (if (Nat.ble (:need j) (comp-rank w (:node j)))
                                      (raise-loop f d w t)
                                      (raise-loop f d (comp-upd w (:node j) (comp-set-rank (:need j)))
                                                  (List.append RJ t (rjobs (+ (:need j) 1) (dep-creditors (:edges w) (:node j)))))))])]))
(a/defn raise-fuel [w :- World] (List Nat)
  (List.cons Nat 0 (rep-list (tbl-ids comp-id (:comps w)) (List.cons Nat 0 (tbl-ids edge-id (:edges w))))))
;; make room for the dep edge c -> d (only when d is a computation)
(a/defn raise-run [w :- World, c :- Nat, d :- Nat] RaiseRes
  (if (comp-has w d)
      (raise-loop (raise-fuel w) d w (List.cons RJ (RJ.mk c (+ (comp-rank w d) 1)) (List.nil RJ)))
      (RaiseRes.mk w true)))
(a/defn raise-for [w :- World, c :- Nat, d :- Nat] World (:world (raise-run w c d)))

(a/theorem inv-raise-loop [fuel :- (List Nat)]
  (forall [d :- Nat, w :- World, todo :- (List RJ)]
    (=> (= (inv-sample w) true) (= (inv-sample (:world (raise-loop fuel d w todo))) true)))
  (induction fuel)
  (case [nil] (intros d w todo h) (cases todo) (all_goals (simp only [raise-loop])) (all_goals (exact h)))
  (case [cons u f ih]
    (intros d w todo h)
    (cases todo)
    (case [nil] (simp only [raise-loop]) (exact h))
    (case [cons j t]
      (cases hd (Nat.beq (:node j) d))
      (case [true] (simp only [raise-loop hd]) (exact h))
      (case [false]
        (cases hn (Nat.ble (:need j) (comp-rank w (:node j))))
        (case [true] (simp only [raise-loop hd hn]) (exact (ih d w t h)))
        (case [false]
          (simp only [raise-loop hd hn])
          (exact (ih d _ _ (inv-comp-upd w (:node j) (comp-set-rank (:need j)) (comp-set-rank-id (:need j))
                              (comp-set-rank-pending (:need j)) h))))))))

(a/theorem inv-raise-for [w :- World, c :- Nat, d :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (raise-for w c d)) true))
  (intro h)
  (cases hd (comp-has w d))
  (simp only [raise-for raise-run hd]) (exact h)
  (simp only [raise-for raise-run hd]) (exact (inv-raise-loop (raise-fuel w) d w _ h)))

;; the I12 condition on one edge, and over the world (executable; preservation: spindel.v2.rank)
(a/defn rank-edge-ok [w :- World, e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:kind e) ek-dep))
   (Bool.or (Bool.not (comp-has w (:debtor e)))
    (Bool.or (Bool.not (comp-has w (:creditor e))) (Nat.blt (comp-rank w (:debtor e)) (comp-rank w (:creditor e)))))))
(a/defn ranks-ok [w :- World] Bool (tbl-all (rank-edge-ok w) (:edges w)))

;; ---- reactivation (§3.4 step 3, reactive demand on a valid idle computation): idle := false,
;; done-epoch := epoch, validity cleared, and a dep edge (cont restart, at 0, baseline and seen
;; = the recorded version) on every validity debtor; the idle computation debtors are
;; reactivated in turn (worklist, pre-order: C's edges first, then each debtor's).
(a/defn comp-react-row [c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (:epoch c) (:epoch c)
              (:pending c) (:rank c) (:version c) (:result c) false (List.nil Valid) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) (:handles c)))
(a/defn valid-edge [w :- World, c :- Nat, v :- Valid] EdgeRow
  (EdgeRow.mk 0 ek-dep c (:debtor v) cont-restart 0 ph-armed false true (:version v)
              true (deb-value w (:debtor v)) (:version v)))
;; each reactivation edge is followed by the I12 raise; if the raise fails (a cycle, not
;; reachable from a well-formed world: an edge onto C keeps it from being idle), the edge and
;; the raise are dropped
(a/defn react-ok [w :- World, c :- Nat, v :- Valid] Bool
  (Bool.and (Bool.not (deb-final w (:debtor v))) (:ok (raise-run (insert-edge-checked w (valid-edge w c v)) c (:debtor v)))))
;; Z#51: no edge on a debtor that is final (it is consumed, as at T6/T10 and Z#48; no id is
;; allocated): the result stays valid with no delivery and no re-run
(a/defn react-add [w :- World, c :- Nat, v :- Valid] World
  (if (react-ok w c v)
      (:world (raise-run (insert-edge-checked w (valid-edge w c v)) c (:debtor v)))
      w))
(a/defn react-edges [w :- World, c :- Nat, vs :- (List Valid)] World
  (match vs [nil w] [(cons v t) (react-edges (react-add w c v) c t)]))
(a/defn valid-debtors [vs :- (List Valid)] (List Nat)
  (match vs [nil (List.nil Nat)] [(cons h t) (List.cons Nat (:debtor h) (valid-debtors t))]))
(a/defn react-one [w :- World, c :- CompRow] World
  (react-edges (comp-upd w (:id c) comp-react-row) (:id c) (:validity c)))
(a/defn react-loop [fuel :- (List Nat), w :- World, q :- (List Nat)] World
  (match fuel
    [nil w]
    [(cons h f) (match q
                  [nil w]
                  [(cons x t) (match (comp-find w x)
                                [none (react-loop f w t)]
                                [(some c) (if (:idle c)
                                              (react-loop f (react-one w c) (List.append Nat t (valid-debtors (:validity c))))
                                              (react-loop f w t))])])]))
;; fuel (found by branch l5): every queued id is a validity entry's debtor of a computation
;; reactivated here (at most once each: it is no longer idle) or the start, so 2 + the number of
;; validity entries bounds the pops; the former bound 2 + |comps| ran out when a validity list
;; names a debtor several times (one entry per dep edge), leaving a valid idle debtor of a
;; reactivated computation idle (its result then goes stale: no edge on its own debtors)
(a/defn react-fuel [w :- World] (List Nat)
  (List.cons Nat 0 (List.cons Nat 0 (tbl-gather (fn [c :- CompRow] true) (fn [c :- CompRow] (valid-debtors (:validity c))) (:comps w)))))
;; reactive demand (observe, dep): a valid idle computation is reactivated; anything else is
;; left to the T5/T11 item the engine issues next (reading B1)
;; Z#33: demand on any idle computation clears `idle` in the demanding transition; a valid one
;; is reactivated (above); a fresh or invalid one leaves idle with its validity cleared, and an
;; invalid one (it has a result) gets the epoch step of B2 here (dirty, not live), so the T5
;; item that follows starts it (`startable`)
(a/defn comp-demand-row [c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c)
              (if (Nat.beq (:done-epoch c) 0) (:epoch c) (+ (:epoch c) 1)) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) false (List.nil Valid) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) (:handles c)))
(a/theorem comp-demand-row-id [c :- CompRow] (= (comp-id (comp-demand-row c)) (comp-id c)) (rfl))
(a/theorem comp-demand-row-pending [c :- CompRow] (= (:pending (comp-demand-row c)) (:pending c)) (rfl))
(a/defn demand-reactive [w :- World, d :- Nat] World
  (match (comp-find w d)
    [none w]
    [(some c) (if (:idle c)
                  (if (valid-idle w c)
                      (react-loop (react-fuel w) w (List.cons Nat d (List.nil Nat)))
                      (comp-upd w d comp-demand-row))
                  w)]))

(a/theorem comp-react-row-id [c :- CompRow] (= (comp-id (comp-react-row c)) (comp-id c)) (rfl))
(a/theorem comp-react-row-pending [c :- CompRow] (= (:pending (comp-react-row c)) (:pending c)) (rfl))

(a/theorem inv-react-add [w :- World, c :- Nat, v :- Valid]
  (=> (= (inv-sample w) true) (= (inv-sample (react-add w c v)) true))
  (intro h)
  (cases hk (react-ok w c v))
  (simp only [react-add hk]) (exact h)
  (simp only [react-add hk])
  (exact (inv-raise-for _ c (:debtor v) (inv-insert-edge-checked w _ h))))

(a/theorem inv-react-edges [vs :- (List Valid)]
  (forall [w :- World, c :- Nat] (=> (= (inv-sample w) true) (= (inv-sample (react-edges w c vs)) true)))
  (induction vs)
  (case' [cons h t ih])
  (case' [nil])
  (intros w c hw) (simp only [react-edges]) (exact hw)
  (intros w c hw) (simp only [react-edges]) (exact (ih _ c (inv-react-add w c h hw))))

(a/theorem inv-react-one [w :- World, c :- CompRow]
  (=> (= (inv-sample w) true) (= (inv-sample (react-one w c)) true))
  (intro h)
  (simp only [react-one])
  (exact (inv-react-edges (:validity c) _ (:id c)
           (inv-comp-upd w (:id c) comp-react-row comp-react-row-id comp-react-row-pending h))))

(a/theorem inv-react-loop [fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)] (=> (= (inv-sample w) true) (= (inv-sample (react-loop fuel w q)) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w q hw) (simp only [react-loop]) (exact hw)
  (intros w q hw)
  (cases q)
  (simp only [react-loop]) (exact hw)
  (rename_i x t)
  (cases hc (comp-find w x)) (case' [some c]) (case' [none])
  (simp only [react-loop hc]) (exact (ih w t hw))
  (cases hi (:idle c))
  (simp only [react-loop hc hi]) (exact (ih w t hw))
  (simp only [react-loop hc hi]) (exact (ih _ _ (inv-react-one w c hw))))

(a/theorem inv-demand-reactive [w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (demand-reactive w d)) true))
  (intro h)
  (cases hc (comp-find w d)) (case' [some c]) (case' [none])
  (simp only [demand-reactive hc]) (exact h)
  (cases hi (:idle c))
  (simp only [demand-reactive hc hi]) (exact h)
  (cases hv (valid-idle w c))
  (simp only [demand-reactive hc hi hv]) (exact (inv-comp-upd w d comp-demand-row comp-demand-row-id comp-demand-row-pending h))
  (simp only [demand-reactive hc hi hv]) (exact (inv-react-loop (react-fuel w) w _ h)))

;; ===========================================================================
;; Part C. T4 spawn, T5 start, T3 create-comp
;; ===========================================================================

;; Z#26: a task run's scope has the task's owner scope as parent (0 when the owner is a
;; computation); a computation run's scope has parent 0
(a/defn task-scope-parent [w :- World, owner :- Nat] Nat (if (scope-has w owner) owner 0))

;; T4 rows: task K = next-id, run R = K + 1, run scope S = K + 2 (fresh-id order)
(a/defn spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat)] World
  (add-run-scope (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs)))
                 (:next-id w) 0 (task-scope-parent w owner) 0))

(a/theorem inv-spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat)]
  (=> (= (inv-sample w) true) (= (inv-sample (spawn-rows w owner inputs)) true))
  (intro h)
  (simp only [spawn-rows])
  (exact (inv-add-run-scope _ (:next-id w) 0 (task-scope-parent w owner) 0
           (inv-task-ins-fresh w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs) (rfl) h))))

;; the run's current scope (engine `current-scope!`): its innermost open explicit scope, else
;; its run scope. Explicit scopes of a run are opened LIFO (with-scope), so the innermost one is
;; the largest id among the open explicit scopes reachable from the run scope through open
;; explicit children (reading B16)
(a/defn open-explicit-child [x :- Nat, s :- ScopeRow] Bool
  (Bool.and (Nat.beq (:parent s) x) (Bool.and (Nat.beq (:kind s) scope-explicit) (:open s))))
(a/defn open-explicit-children [w :- World, x :- Nat] (List Nat) (tbl-scan scope-id (open-explicit-child x) (:scopes w)))
(a/defn nat-max [m :- Nat, xs :- (List Nat)] Nat
  (match xs [nil m] [(cons h t) (nat-max (if (Nat.blt m h) h m) t)]))
(a/defn cur-scope [w :- World, r :- RunRow] Nat
  (nat-max (:scope r)
    (:visited (reach-run-l (List.cons Nat 0 (List.cons Nat 0 (tbl-ids scope-id (:scopes w))))
                           (open-explicit-children w) (List.cons Nat (:scope r) (List.nil Nat))))))
;; §5.2: a task spawned in a computation run is owned by the computation, in a task run by
;; the run's current scope (structured child, Q10)
(a/defn spawn-owner [w :- World, r :- RunRow] Nat (if (in-comp w r) (:of r) (cur-scope w r)))

;; §5.2 re-spawn: inside a computation run, `fresh` naming an existing task in C's basis or
;; adoption basis adopts it (allocates nothing); its recorded inputs must equal the logged ones
(a/defn respawn-target [w :- World, r :- RunRow, x :- Nat] (Option TaskRow)
  (match (comp-find w (:of r))
    [none (Option.none TaskRow)]
    [(some c) (if (reach-mem x (nat-app (created-ids (:basis c)) (created-ids (:adopt-basis c))))
                  (task-find w x) (Option.none TaskRow))]))
(a/defn created-other [x :- Nat, b :- Created] Bool (Bool.not (Nat.beq (:id b) x)))
;; the adopted task moves to the basis at the new site (its old entries go)
(a/defn comp-rebasis [b :- Created, c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c)
              (List.cons Created b (tbl-filter (created-other (:id b)) (:basis c)))
              (tbl-filter (created-other (:id b)) (:adopt-basis c)) (:adopt-baselines c) (:handles c)))
(a/theorem comp-rebasis-id [b :- Created, c :- CompRow] (= (comp-id (comp-rebasis b c)) (comp-id c)) (rfl))
(a/theorem comp-rebasis-pending [b :- Created, c :- CompRow] (= (:pending (comp-rebasis b c)) (:pending c)) (rfl))
(a/defn respawn-raw [w :- World, r :- RunRow, x :- Nat] World
  (run-upd (comp-upd w (:of r) (comp-rebasis (Created.mk x (:effect-index r)))) (:id r) run-tick))

;; inside a run (body effect): a re-spawn (above), or a new task (fresh = next-id) owned per
;; §5.2, recorded in a computation's basis; effect tick either way
(a/defn t4-spawn [w :- World, st :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat)] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (match (respawn-target w r fresh)
                [none (if (Nat.beq fresh (:next-id w))
                          (accept (run-upd (record-basis (spawn-rows w (spawn-owner w r) inputs) r fresh) (:id r) run-tick))
                          (refuse w))]
                [(some t) (if (nat-list-eq inputs (:inputs t)) (accept (respawn-raw w r fresh)) (refuse w))])]))
;; at top level: owned by the given open scope
(a/defn t4-spawn-top [w :- World, scope :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat)] Outcome
  (if (Bool.and (Nat.beq fresh (:next-id w)) (scope-open-at w scope)) (accept (spawn-rows w scope inputs)) (refuse w)))

(a/theorem t4-inv [w :- World, st :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat)]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t4-spawn w st body fresh inputs))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t4-spawn ht refuse]) (exact h)
  (cases hp (respawn-target w r fresh))
  (case [none]
    (cases hf (Nat.beq fresh (:next-id w)))
    (case [false] (simp only [t4-spawn ht hp hf refuse]) (exact h))
    (case [true]
      (simp only [t4-spawn ht hp hf accept])
      (exact (inv-run-upd _ (:id r) run-tick run-tick-run-id
               (inv-record-basis _ r fresh (inv-spawn-rows w (spawn-owner w r) inputs h))))))
  (case [some t]
    (cases he (nat-list-eq inputs (:inputs t)))
    (case [false] (simp only [t4-spawn ht hp he refuse]) (exact h))
    (case [true]
      (simp only [t4-spawn ht hp he accept respawn-raw])
      (exact (inv-run-upd _ (:id r) run-tick run-tick-run-id
               (inv-comp-upd w (:of r) _ (comp-rebasis-id _) (comp-rebasis-pending _) h))))))

(a/theorem t4-refuse [w :- World, st :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat)]
  (=> (= (:accepted (t4-spawn w st body fresh inputs)) false) (= (:world (t4-spawn w st body fresh inputs)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t4-spawn ht refuse])
  (cases hp (respawn-target w r fresh))
  (case [none]
    (cases hf (Nat.beq fresh (:next-id w)))
    (case [false] (simp only [t4-spawn ht hp hf refuse]))
    (case [true] (simp [t4-spawn ht hp hf accept] at ha)))
  (case [some t]
    (cases he (nat-list-eq inputs (:inputs t)))
    (case [false] (simp only [t4-spawn ht hp he refuse]))
    (case [true] (simp [t4-spawn ht hp he accept] at ha))))

(a/theorem t4-top-inv [w :- World, scope :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat)]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t4-spawn-top w scope body fresh inputs))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (scope-open-at w scope)))
  (simp only [t4-spawn-top hg refuse]) (exact h)
  (simp only [t4-spawn-top hg accept]) (exact (inv-spawn-rows w scope inputs h)))

(a/theorem t4-top-refuse [w :- World, scope :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat)]
  (=> (= (:accepted (t4-spawn-top w scope body fresh inputs)) false) (= (:world (t4-spawn-top w scope body fresh inputs)) w))
  (intro ha)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (scope-open-at w scope)))
  (simp only [t4-spawn-top hg refuse])
  (simp [t4-spawn-top hg accept] at ha))

;; ---- T5 start(C): a fresh computation (done-epoch none, §2: idle or not; no run in progress)
;; or an invalid idle one. Run R = next-id (epoch C.epoch, from the body: effect-index 0), run scope R + 1
;; (parent 0, Z#26). An idle computation leaves idle (validity cleared); one with a result gets
;; an epoch step, so it is dirty, not live, until the run completes (reading B2).
(a/defn start-epoch [c :- CompRow] Nat (if (Bool.and (:idle c) (Bool.not (Nat.beq (:done-epoch c) 0))) (+ (:epoch c) 1) (:epoch c)))
(a/defn comp-start-row [rid :- Nat, c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) rid (start-epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) false (List.nil Valid) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) (:handles c)))
(a/theorem comp-start-row-id [rid :- Nat, c :- CompRow] (= (comp-id (comp-start-row rid c)) (comp-id c)) (rfl))
(a/theorem comp-start-row-pending [rid :- Nat, c :- CompRow] (= (:pending (comp-start-row rid c)) (:pending c)) (rfl))

;; T5 applies to a fresh computation (no run in progress) or an invalid one: still idle
;; (undemanded), or demanded (Z#33: not idle, epoch stepped at the demand: done-epoch /= epoch,
;; no run, no dep edges)
(a/defn startable [w :- World, c :- CompRow] Bool
  (Bool.or (Bool.and (Nat.beq (:done-epoch c) 0) (Bool.not (run-busy w c)))
   (Bool.or (Bool.and (:idle c) (Bool.not (valid-idle w c)))
            (Bool.and (Bool.not (:idle c))
             (Bool.and (Bool.not (Nat.beq (:done-epoch c) (:epoch c)))
              (Bool.and (Nat.beq (:run c) 0) (Bool.not (tbl-any (dep-of (:id c)) (:edges w)))))))))
(a/defn start-raw [w :- World, c :- CompRow] World
  (comp-upd (add-run-scope w (:id c) (start-epoch c) 0 0) (:id c) (comp-start-row (:next-id w))))

(a/defn t5-start [w :- World, cid :- Nat, fresh :- Nat] Outcome
  (match (comp-find w cid)
    [none (refuse w)]
    [(some c) (if (Bool.and (Nat.beq fresh (:next-id w)) (startable w c)) (accept (start-raw w c)) (refuse w))]))

(a/theorem inv-start-raw [w :- World, c :- CompRow]
  (=> (= (inv-sample w) true) (= (inv-sample (start-raw w c)) true))
  (intro h)
  (simp only [start-raw])
  (exact (inv-comp-upd _ (:id c) (comp-start-row (:next-id w)) (comp-start-row-id (:next-id w))
           (comp-start-row-pending (:next-id w)) (inv-add-run-scope w (:id c) (start-epoch c) 0 0 h))))

(a/theorem t5-inv [w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t5-start w cid fresh))) true))
  (intro h)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [t5-start hc refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (startable w c)))
  (simp only [t5-start hc hg refuse]) (exact h)
  (simp only [t5-start hc hg accept]) (exact (inv-start-raw w c h)))

(a/theorem t5-refuse [w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (:accepted (t5-start w cid fresh)) false) (= (:world (t5-start w cid fresh)) w))
  (intro ha)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [t5-start hc refuse])
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (startable w c)))
  (simp only [t5-start hc hg refuse])
  (simp [t5-start hc hg accept] at ha))

;; ---- T3 create-comp(c, inputs, body). The item names the computation id c: an existing
;; computation (adoption or replacement), or else c must be next-id (a fresh computation).
;; Every case records C in a computation creator's basis (§5.2) and ticks the effect index.
;;   absent: fresh (epoch 1, done-epoch none, handles 1, Z#13), owner per §5.2
;;   present, equal inputs: adopted, handles unchanged (Z#29: a new handle is `handle-new`)
;;   present, different inputs (W#5): inputs/body replaced, handles unchanged (Z#29), the
;;     rerun-source write: C.epoch + 1 (Z#8, the restart site of T11: no fired edge) and the
;;     marking of §4.5.1 from C (C's out-edges and every dep edge whose debtor is reachable
;;     from C through reversed dep edges); an idle entry becomes fresh (idle := false,
;;     done-epoch := none, validity cleared)
(a/defn new-comp-row [w :- World, id :- Nat, owner :- Nat, inputs :- (List Nat), body :- Nat] CompRow
  (CompRow.mk id owner inputs body 0 1 0 (marked-in id (:edges w)) 0 0 none-result false
              (List.nil Valid) (List.nil Created) (List.nil Created) (List.nil AdoptBase) 1))
(a/defn comp-adopt-row [c :- CompRow] CompRow c)
(a/defn comp-replace-row [inputs :- (List Nat), body :- Nat, c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) inputs body (:run c) (+ (:epoch c) 1) (if (:idle c) 0 (:done-epoch c))
              (:pending c) (:rank c) (:version c) (:result c) false (List.nil Valid) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) (:handles c)))
(a/theorem comp-adopt-row-id [c :- CompRow] (= (comp-id (comp-adopt-row c)) (comp-id c)) (rfl))
(a/theorem comp-adopt-row-pending [c :- CompRow] (= (:pending (comp-adopt-row c)) (:pending c)) (rfl))
(a/theorem comp-replace-row-id [i :- (List Nat), b :- Nat, c :- CompRow] (= (comp-id (comp-replace-row i b c)) (comp-id c)) (rfl))
(a/theorem comp-replace-row-pending [i :- (List Nat), b :- Nat, c :- CompRow] (= (:pending (comp-replace-row i b c)) (:pending c)) (rfl))

;; §4.5.1 from C: mark the dep edges whose debtor is C or reachable from C
(a/defn mark-from [w :- World, c :- Nat] World
  (nat-fold mark-edge w (mark-targets (List.cons Nat c (cone-set w c)) (:edges w))))

(a/defn create-comp-raw [w :- World, c :- Nat, owner :- Nat, inputs :- (List Nat), body :- Nat] World
  (match (comp-find w c)
    [none (bump (comp-ins w (new-comp-row w (:next-id w) owner inputs body)))]
    [(some row) (if (nat-list-eq (:inputs row) inputs)
                    (comp-upd w c comp-adopt-row)
                    (mark-from (comp-upd w c (comp-replace-row inputs body)) c))]))
;; absent ids must be the fresh id
(a/defn create-ok [w :- World, c :- Nat] Bool (Bool.or (comp-has w c) (Nat.beq c (:next-id w))))

(a/defn t3-create [w :- World, st :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (if (create-ok w c)
                  (accept (run-upd (record-basis (create-comp-raw w c (src-owner w r) inputs body) r c) (:id r) run-tick))
                  (refuse w))]))
(a/defn t3-create-top [w :- World, scope :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat] Outcome
  (if (Bool.and (create-ok w c) (scope-open-at w scope)) (accept (create-comp-raw w c scope inputs body)) (refuse w)))

(a/theorem inv-mark-from [w :- World, c :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (mark-from w c)) true))
  (intro h) (exact (nat-fold-inv mark-edge mark-edge-inv-sample _ w h)))

(a/theorem inv-create-comp-raw [w :- World, c :- Nat, owner :- Nat, inputs :- (List Nat), body :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (create-comp-raw w c owner inputs body)) true))
  (intro h)
  (cases hc (comp-find w c)) (case' [some row]) (case' [none])
  (simp only [create-comp-raw hc])
  (exact (inv-comp-ins-fresh w (new-comp-row w (:next-id w) owner inputs body) (rfl) (rfl) h))
  (cases hi (nat-list-eq (:inputs row) inputs))
  (simp only [create-comp-raw hc hi])
  (exact (inv-mark-from _ c (inv-comp-upd w c (comp-replace-row inputs body) (comp-replace-row-id inputs body)
                              (comp-replace-row-pending inputs body) h)))
  (simp only [create-comp-raw hc hi])
  (exact (inv-comp-upd w c comp-adopt-row comp-adopt-row-id comp-adopt-row-pending h)))

(a/theorem t3-inv [w :- World, st :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t3-create w st c inputs body))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t3-create ht refuse]) (exact h)
  (cases hg (create-ok w c))
  (simp only [t3-create ht hg refuse]) (exact h)
  (simp only [t3-create ht hg accept])
  (exact (inv-run-upd _ (:id r) run-tick run-tick-run-id
           (inv-record-basis _ r c (inv-create-comp-raw w c (src-owner w r) inputs body h)))))

(a/theorem t3-refuse [w :- World, st :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat]
  (=> (= (:accepted (t3-create w st c inputs body)) false) (= (:world (t3-create w st c inputs body)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t3-create ht refuse])
  (cases hg (create-ok w c))
  (simp only [t3-create ht hg refuse])
  (simp [t3-create ht hg accept] at ha))

(a/theorem t3-top-inv [w :- World, scope :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t3-create-top w scope c inputs body))) true))
  (intro h)
  (cases hg (Bool.and (create-ok w c) (scope-open-at w scope)))
  (simp only [t3-create-top hg refuse]) (exact h)
  (simp only [t3-create-top hg accept]) (exact (inv-create-comp-raw w c scope inputs body h)))

(a/theorem t3-top-refuse [w :- World, scope :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat]
  (=> (= (:accepted (t3-create-top w scope c inputs body)) false) (= (:world (t3-create-top w scope c inputs body)) w))
  (intro ha)
  (cases hg (Bool.and (create-ok w c) (scope-open-at w scope)))
  (simp only [t3-create-top hg refuse])
  (simp [t3-create-top hg accept] at ha))

;; ===========================================================================
;; Part D. T11 dispatch(C) (X#2, X#3, Y#2, Z#12, Z#22)
;; ===========================================================================

;; needs-run (§2, Z#1): done-epoch /= epoch and C.run is none or not current
(a/defn run-current-of-comp [w :- World, c :- CompRow] Bool
  (match (run-find w (:run c)) [none false] [(some r) (Nat.beq (:epoch r) (:epoch c))]))
(a/defn needs-run [w :- World, c :- CompRow] Bool
  (Bool.and (Bool.not (Nat.beq (:done-epoch c) (:epoch c))) (Bool.not (run-current-of-comp w c))))
;; dirty (§2): not idle, not live, not fresh
(a/defn comp-dirty [c :- CompRow] Bool
  (Bool.and (Bool.not (:idle c)) (Bool.and (Bool.not (comp-live c)) (Bool.not (Nat.beq (:done-epoch c) 0)))))
;; Blocked (§4.5.6, W#7, X#8) as the least fixpoint, an instance of spindel.v2.reach's `Derive`:
;; base x = x (a computation or task) has a current run that is parked; deps x = the debtors of
;; the unfilled member edges of that run's activations; leaf y = y is a source or a resource
;; (a non-computation debtor). x is blocked iff Derive base deps leaf x: its run is parked and
;; every member debtor is a source, a resource, or blocked. `blocked-set` runs
;; `derive-run-l` over the computations and tasks (|nodes| + 1 rounds); `blocked-sound` and
;; `blocked-complete` connect it to Derive (the latter given convergence, which tests check).
(a/defn run-parked [r :- RunRow] Bool (Nat.beq (:act r) act-parked))
(a/defn run-parked-of [w :- World, c :- CompRow] Bool
  (match (run-find w (:run c)) [none false]
         [(some r) (Bool.and (Nat.beq (:act r) act-parked) (Nat.beq (:epoch r) (:epoch c)))]))
(a/defn ent-run [w :- World, x :- Nat] Nat
  (match (comp-find w x) [none (match (task-find w x) [none 0] [(some t) (:run t)])] [(some c) (:run c)]))
(a/defn blk-base [w :- World, x :- Nat] Bool
  (match (comp-find w x)
    [none (match (task-find w x) [none false] [(some t) (opt-test run-parked (run-find w (:run t)))])]
    [(some c) (run-parked-of w c)]))
(a/defn edge-debtor-of [w :- World, x :- Nat] Nat (match (edge-find w x) [none 0] [(some e) (:debtor e)]))
(a/defn debtors-of [w :- World, xs :- (List Nat)] (List Nat)
  (match xs [nil (List.nil Nat)] [(cons h t) (List.cons Nat (edge-debtor-of w h) (debtors-of w t))]))
(a/defn blk-deps [w :- World, x :- Nat] (List Nat)
  (debtors-of w (tbl-gather (act-of-run (ent-run w x)) act-contrib (:acts w))))
(a/defn blk-leaf [w :- World, y :- Nat] Bool (Bool.or (source-has w y) (resource-has w y)))
(a/defn blk-nodes [w :- World] (List Nat) (nat-app (tbl-ids comp-id (:comps w)) (tbl-ids task-id (:tasks w))))
(a/defn blocked-res [w :- World] DeriveResult
  (derive-run-l (List.cons Nat 0 (blk-nodes w)) (blk-base w) (blk-deps w) (blk-leaf w) (blk-nodes w)))
(a/defn blocked-set [w :- World] (List Nat) (:derived (blocked-res w)))
(a/defn blocked-converged [w :- World] Bool (:converged (blocked-res w)))

(a/theorem blocked-sound [w :- World, x :- Nat]
  (=> (= (reach-mem x (blocked-set w)) true) (Derive (blk-base w) (blk-deps w) (blk-leaf w) x))
  (intro h)
  (simp only [blocked-set blocked-res derive-run-l-eq] at h)
  (exact (derive-run-sound _ _ _ _ _ x h)))

(a/theorem blocked-complete [w :- World, x :- Nat]
  (=> (forall [a :- Nat] (=> (= (reach-mem a (blk-nodes w)) true)
        (forall [b :- Nat] (=> (= (reach-mem b (blk-deps w a)) true) (= (blk-leaf w b) false) (= (reach-mem b (blk-nodes w)) true)))))
      (= (blocked-converged w) true)
      (Derive (blk-base w) (blk-deps w) (blk-leaf w) x)
      (= (reach-mem x (blk-nodes w)) true)
      (= (reach-mem x (blocked-set w)) true))
  (intros hcl hc hd hx)
  (simp only [blocked-converged blocked-res derive-run-l-eq] at hc)
  (simp only [blocked-set blocked-res derive-run-l-eq])
  (exact (derive-run-complete _ _ _ _ _ x hcl hc hd hx)))

;; eligibility (§4.5.7): every computation debtor of C (through a dep edge) is not dirty
;; (settled) or blocked (B4, the least fixpoint above)
(a/defn debtor-settled [w :- World, bl :- (List Nat), e :- EdgeRow] Bool
  (match (comp-find w (:debtor e)) [none true]
         [(some d) (Bool.or (Bool.not (comp-dirty d)) (reach-mem (:id d) bl))]))
(a/defn dep-ok-for [w :- World, bl :- (List Nat), c :- Nat, e :- EdgeRow] Bool
  (Bool.or (Bool.not (dep-of c e)) (debtor-settled w bl e)))
(a/defn eligible [w :- World, c :- CompRow] Bool (tbl-all (dep-ok-for w (blocked-set w) (:id c)) (:edges w)))

;; E: the earliest fired dep edge of C in CREATION order (Z#59; the engine's C.ins order). Ids come
;; from one allocator and an edge keeps its id, so creation order is id order: the least id.
(a/defn fired-dep-of [c :- Nat, e :- EdgeRow] Bool (Bool.and (dep-of c e) (Nat.beq (:phase e) ph-fired)))
(a/defn earliest [best :- (Option EdgeRow), es :- (List EdgeRow)] (Option EdgeRow)
  (match es
    [nil best]
    [(cons h t) (earliest (match best [none (Option.some EdgeRow h)]
                                 [(some b) (if (Nat.blt (:id h) (:id b)) (Option.some EdgeRow h) best)]) t)]))
(a/defn entry-edge [w :- World, c :- Nat] (Option EdgeRow)
  (earliest (Option.none EdgeRow) (tbl-filter (fired-dep-of c) (:edges w))))

;; the cut: `has` = an entry edge exists; edges are cut by creation order (`cid` = E's id: every dep
;; edge of C created after E, siblings at E's site included, Z#59), creations by site (`cut` = E's
;; at); without an entry edge (the rerun-source restart of T3, or an invalid idle computation)
;; everything is suffix
(a/defn after-cut [has :- Bool, cut :- Nat, at :- Nat] Bool (if has (Nat.blt cut at) true))
(a/defn suffix-edge [c :- Nat, has :- Bool, cid :- Nat, e :- EdgeRow] Bool (Bool.and (dep-of c e) (after-cut has cid (:id e))))
(a/defn keep-prefix [c :- Nat, has :- Bool, cid :- Nat, e :- EdgeRow] Bool (Bool.not (suffix-edge c has cid e)))
(a/defn edge-base [e :- EdgeRow] AdoptBase (AdoptBase.mk (:at e) (:debtor e) (:base-value e) (:base-version e)))
(a/defn bases-of [es :- (List EdgeRow)] (List AdoptBase)
  (match es [nil (List.nil AdoptBase)]
         [(cons h t) (if (:has-base h) (List.cons AdoptBase (edge-base h) (bases-of t)) (bases-of t))]))
(a/defn created-after [has :- Bool, cut :- Nat, b :- Created] Bool (after-cut has cut (:at b)))
(a/defn created-upto [has :- Bool, cut :- Nat, b :- Created] Bool (Bool.not (after-cut has cut (:at b))))
;; basis := prefix creations, adoption basis := suffix creations (only the latest), adoption
;; baselines := the suffix edges' baselines (§4.4)
(a/defn comp-cut-row [has :- Bool, cut :- Nat, bs :- (List AdoptBase), c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c)
              (tbl-filter (created-upto has cut) (:basis c)) (tbl-filter (created-after has cut) (:basis c))
              bs (:handles c)))
(a/defn comp-set-run [rid :- Nat, c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) rid (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) (:handles c)))
(a/theorem comp-cut-row-id [h :- Bool, k :- Nat, bs :- (List AdoptBase), c :- CompRow] (= (comp-id (comp-cut-row h k bs c)) (comp-id c)) (rfl))
(a/theorem comp-cut-row-pending [h :- Bool, k :- Nat, bs :- (List AdoptBase), c :- CompRow] (= (:pending (comp-cut-row h k bs c)) (:pending c)) (rfl))
(a/theorem comp-set-run-id [rid :- Nat, c :- CompRow] (= (comp-id (comp-set-run rid c)) (comp-id c)) (rfl))
(a/theorem comp-set-run-pending [rid :- Nat, c :- CompRow] (= (:pending (comp-set-run rid c)) (:pending c)) (rfl))

;; D1 final debtors (`deb-final`, step.clj): a closed source, a delivered deferred, a
;; completed task (Z#32: never a computation)

;; E consumed (§4.2): removed when its debtor is final, on resume and on restart (Z#39);
;; otherwise restart re-arms it with its OLD baseline (Z#22) and a resume with the new one
(a/defn consume-entry [w :- World, e :- EdgeRow] World
  (if (deb-final w (:debtor e))
      (remove-edge w (:id e))
      (if (Nat.beq (:cont e) cont-restart)
          (edge-upd w (:id e) (edge-set-phase ph-armed))
          (edge-upd w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))))))
(a/defn entry-ei [e :- EdgeRow] Nat (if (Nat.beq (:cont e) cont-restart) 0 (+ (:at e) 1)))

;; predecessor: the run C.run, if not done, is cancelled with cancel(R, replace) (Y#2)
(a/defn cancel-pred [w :- World, c :- CompRow] World
  (match (run-find w (:run c))
    [none w]
    [(some r) (if (run-alive r)
                  (run-cascade w (List.cons Job (Job.jcancel (:id r) true) (List.nil Job)))
                  w)]))

(a/defn cut-suffix [w :- World, c :- Nat, has :- Bool, cut :- Nat, cid :- Nat] World
  (comp-upd (drop-edges w (keep-prefix c has cid)) c
            (comp-cut-row has cut (bases-of (tbl-filter (suffix-edge c has cid) (:edges w))))))

(a/defn new-run-of [w :- World, c :- CompRow, ei :- Nat] World
  (comp-upd (add-run-scope w (:id c) (:epoch c) 0 ei) (:id c) (comp-set-run (:next-id w))))

(a/defn dispatch-raw [w :- World, c :- CompRow] World
  (match (entry-edge w (:id c))
    [none (new-run-of (cut-suffix (cancel-pred w c) (:id c) false 0 0) c 0)]
    [(some e) (new-run-of (consume-entry (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e) c (entry-ei e))]))

(a/defn t11-dispatch [w :- World, cid :- Nat, fresh :- Nat] Outcome
  (match (comp-find w cid)
    [none (refuse w)]
    [(some c) (if (Bool.and (Nat.beq fresh (:next-id w))
                            (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c))))
                  (accept (dispatch-raw w c))
                  (refuse w))]))

(a/theorem inv-cancel-pred [w :- World, c :- CompRow]
  (=> (= (inv-sample w) true) (= (inv-sample (cancel-pred w c)) true))
  (intro h)
  (cases hr (run-find w (:run c))) (case' [some r]) (case' [none])
  (simp only [cancel-pred hr]) (exact h)
  (cases ha (run-alive r))
  (simp only [cancel-pred hr ha]) (exact h)
  (simp only [cancel-pred hr ha]) (exact (inv-run-cascade w _ h)))

(a/theorem inv-cut-suffix [w :- World, c :- Nat, has :- Bool, cut :- Nat, cid :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (cut-suffix w c has cut cid)) true))
  (intro h)
  (simp only [cut-suffix])
  (exact (inv-comp-upd _ c _ (comp-cut-row-id has cut _) (comp-cut-row-pending has cut _)
           (inv-drop-edges w (keep-prefix c has cid) h))))

(a/theorem inv-consume-entry [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (inv-sample (consume-entry w e)) true))
  (intro h)
  (cases hf (deb-final w (:debtor e)))
  (cases hr (Nat.beq (:cont e) cont-restart))
  (simp only [consume-entry hr hf])
  (exact (inv-edge-upd w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
           (edge-rearm-edge-id _ _) (edge-rearm-kind _ _) (edge-rearm-creditor _ _)
           (edge-rearm-debtor _ _) (edge-rearm-marked _ _) h))
  (simp only [consume-entry hr hf]) (exact (inv-edge-set-phase w (:id e) ph-armed h))
  (simp only [consume-entry hf]) (exact (inv-remove-edge w (:id e) h)))

(a/theorem inv-new-run-of [w :- World, c :- CompRow, ei :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (new-run-of w c ei)) true))
  (intro h)
  (simp only [new-run-of])
  (exact (inv-comp-upd _ (:id c) (comp-set-run (:next-id w)) (comp-set-run-id (:next-id w))
           (comp-set-run-pending (:next-id w)) (inv-add-run-scope w (:id c) (:epoch c) 0 ei h))))

(a/theorem inv-dispatch-raw [w :- World, c :- CompRow]
  (=> (= (inv-sample w) true) (= (inv-sample (dispatch-raw w c)) true))
  (intro h)
  (have h1 := (inv-cancel-pred w c h))
  (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
  (simp only [dispatch-raw he])
  (exact (inv-new-run-of _ c 0 (inv-cut-suffix _ (:id c) false 0 0 h1)))
  (simp only [dispatch-raw he])
  (exact (inv-new-run-of _ c _ (inv-consume-entry _ e (inv-cut-suffix _ (:id c) true (:at e) (:id e) h1)))))

(a/theorem t11-inv [w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t11-dispatch w cid fresh))) true))
  (intro h)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [t11-dispatch hc refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))))
  (simp only [t11-dispatch hc hg refuse]) (exact h)
  (simp only [t11-dispatch hc hg accept]) (exact (inv-dispatch-raw w c h)))

(a/theorem t11-refuse [w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (:accepted (t11-dispatch w cid fresh)) false) (= (:world (t11-dispatch w cid fresh)) w))
  (intro ha)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [t11-dispatch hc refuse])
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))))
  (simp only [t11-dispatch hc hg refuse])
  (simp [t11-dispatch hc hg accept] at ha))

;; ===========================================================================
;; Part E. Settle (§4.5.2, Z#9, Z#20) and T12 complete (Q10, Z#21)
;; ===========================================================================

;; an armed dep edge that is an unfilled member of an activation of its creditor's current run
(a/defn member-current [w :- World, e :- EdgeRow] Bool
  (match (act-with-member (:id e) (:acts w))
    [none false]
    [(some a) (run-current-of w (:run a) (:creditor e))]))
;; one out-edge of a settling D (version ver), Z#30: it fires (T9: a delivery to a current
;; member, else an invalidation) when the version it consumed (`seen`, none counts as
;; different) differs from D's; otherwise only a current member is delivered (Z#20). Then it
;; is unmarked. (`changed` no longer matters: Z#30 is the whole rule.)
(a/defn edge-behind [ver :- Nat, e :- EdgeRow] Bool (Bool.or (Bool.not (:has-seen e)) (Bool.not (Nat.beq (:seen e) ver))))
(a/defn settle-edge [changed :- Bool, ver :- Nat, w :- World, x :- Nat] World
  (match (edge-find w x)
    [none w]
    [(some e) (unmark-edge
                (if (Nat.beq (:phase e) ph-armed)
                    (if (Bool.or (edge-behind ver e) (member-current w e)) (fire-dep w e) w)
                    w)
                x)]))
(a/defn out-dep [d :- Nat, e :- EdgeRow] Bool (Bool.and (Nat.beq (:kind e) ek-dep) (Nat.beq (:debtor e) d)))
(a/defn out-marked [d :- Nat, e :- EdgeRow] Bool (Bool.and (out-dep d e) (:marked e)))
;; observe edges deliver (seen < version, Z#9); wait edges on D fire: host waits are consumed
;; (Z#27) and an activation's wait member is delivered (T6: a task awaits a computation through
;; a wait edge; §4.5.2 Z#20, T9). Found by the oracle (sample 3, commit 10).
(a/defn host-on [d :- Nat, e :- EdgeRow] Bool
  (Bool.and (Bool.or (Nat.beq (:kind e) ek-observe) (Nat.beq (:kind e) ek-wait)) (Nat.beq (:debtor e) d)))
(a/defn settle-host [w :- World, d :- Nat] World
  (nat-fold (fire-edge (deb-result w d)) w (tbl-scan edge-id (host-on d) (:edges w))))

;; D settles when it is not idle, pending = 0, done-epoch = epoch and no current run is in
;; progress (Y#1: a current run that has not completed does not count)
(a/defn settle-ready [w :- World, c :- CompRow] Bool
  (Bool.and (comp-live c) (Bool.not (Bool.and (run-current-of-comp w c) (run-busy w c)))))
(a/defn ready-id [w :- World, x :- Nat] Bool (opt-test (settle-ready w) (comp-find w x)))

(a/defn settle-one [w :- World, d :- Nat, changed :- Bool] World
  (settle-host (nat-fold (settle-edge changed (deb-version w d)) w (tbl-scan edge-id (out-dep d) (:edges w))) d))
;; the creditors whose marked edge on d was unmarked: candidates for an unchanged settle
(a/defn settle-next [w :- World, w2 :- World, d :- Nat] (List Nat)
  (tbl-filter (ready-id w2) (tbl-scan edge-cred (out-marked d) (:edges w))))

(a/defn settle-loop [fuel :- (List Nat), w :- World, q :- (List Nat)] FinRes
  (match fuel
    [nil (FinRes.mk w q)]
    [(cons h f) (match q
                  [nil (FinRes.mk w (List.nil Nat))]
                  [(cons d t) (settle-loop f (settle-one w d false)
                                (List.append Nat t (settle-next w (settle-one w d false) d)))])]))
;; fuel (found by branch l5): every queued creditor comes from a distinct marked edge that the
;; settle of its debtor unmarks (no edge is marked during a settle), so 2 + |edges| bounds the
;; pops; the former bound 2 + |comps| ran out when a creditor has several marked edges on one
;; debtor (each listed once in `settle-next`), leaving a live computation with marked in-edges
(a/defn settle-fuel [w :- World] (List Nat) (List.cons Nat 0 (List.cons Nat 0 (tbl-ids edge-id (:edges w)))))
(a/defn settle-res [w :- World, d :- Nat, changed :- Bool] FinRes
  (settle-loop (settle-fuel w) (settle-one w d changed) (settle-next w (settle-one w d changed) d)))
;; settle D if it is ready (the cascade's flag: `settle-done`, tests check it)
(a/defn settle [w :- World, d :- Nat, changed :- Bool] World
  (if (ready-id w d) (:world (settle-res w d changed)) w))
(a/defn settle-done [w :- World, d :- Nat, changed :- Bool] Bool
  (match (:rest (settle-res w d changed)) [nil true] [(cons h t) false]))

(a/theorem inv-settle-edge [changed :- Bool, ver :- Nat, w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (settle-edge changed ver w x)) true))
  (intro h)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [settle-edge hf]) (exact h)
  (have h1 (= (inv-sample (if (Nat.beq (:phase e) ph-armed)
                              (if (Bool.or (edge-behind ver e) (member-current w e)) (fire-dep w e) w)
                              w)) true))
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [hp]) (exact h)
  (cases hc (Bool.or (edge-behind ver e) (member-current w e)))
  (simp only [hp hc]) (exact h)
  (simp only [hp hc]) (exact (inv-fire-dep w e h))
  (simp only [settle-edge hf])
  (exact (unmark-edge-inv-sample _ x h1)))

(a/theorem inv-settle-host [w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (settle-host w d)) true))
  (intro h) (exact (nat-fold-inv (fire-edge (deb-result w d)) (inv-fire-edge (deb-result w d)) _ w h)))

(a/theorem inv-settle-one [w :- World, d :- Nat, changed :- Bool]
  (=> (= (inv-sample w) true) (= (inv-sample (settle-one w d changed)) true))
  (intro h)
  (simp only [settle-one])
  (exact (inv-settle-host _ d (nat-fold-inv (settle-edge changed (deb-version w d))
                                (inv-settle-edge changed (deb-version w d)) _ w h))))

(a/theorem inv-settle-loop [fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)] (=> (= (inv-sample w) true) (= (inv-sample (:world (settle-loop fuel w q))) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w q hw) (simp only [settle-loop]) (exact hw)
  (intros w q hw)
  (cases q)
  (simp only [settle-loop]) (exact hw)
  (rename_i d t)
  (simp only [settle-loop])
  (exact (ih _ _ (inv-settle-one w d false hw))))

(a/theorem inv-settle [w :- World, d :- Nat, changed :- Bool]
  (=> (= (inv-sample w) true) (= (inv-sample (settle w d changed)) true))
  (intro h)
  (cases hr (ready-id w d))
  (simp only [settle hr]) (exact h)
  (simp only [settle hr settle-res])
  (exact (inv-settle-loop (settle-fuel w) _ _ (inv-settle-one w d changed h))))

;; dep edges on final debtors are removed after the delivery (T10)
(a/defn fin-if-final [w :- World, d :- Nat] World (if (deb-final w d) (finalize-debtor w d) w))

(a/theorem inv-fin-if-final [w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (fin-if-final w d)) true))
  (intro h)
  (cases hf (deb-final w d))
  (simp only [fin-if-final hf]) (exact h)
  (simp only [fin-if-final hf]) (exact (inv-finalize-debtor w d h)))

;; ---- T12 complete(R, result)
(a/defn run-complete-row [r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) act-done (:mode r) false
             (:effect-index r) (:finalizers r) (:resources r)))
(a/theorem run-complete-row-id [r :- RunRow] (= (run-id (run-complete-row r)) (run-id r)) (rfl))
(a/defn res-same [a :- RunResult, b :- RunResult] Bool (Bool.and (Nat.beq (:tag a) (:tag b)) (Nat.beq (:val a) (:val b))))
;; current run: result, version (+1 when it differs, `=` on the opaque value), done-epoch; the
;; adoption ends with the run (Z#21: baselines discarded)
(a/defn comp-result-row [res :- RunResult, ep :- Nat, c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (:epoch c) ep
              (:pending c) (:rank c) (if (res-same res (:result c)) (:version c) (+ (:version c) 1)) res (:idle c)
              (:validity c) (:basis c) (List.nil Created) (List.nil AdoptBase) (:handles c)))
(a/theorem comp-result-row-id [res :- RunResult, ep :- Nat, c :- CompRow] (= (comp-id (comp-result-row res ep c)) (comp-id c)) (rfl))
(a/theorem comp-result-row-pending [res :- RunResult, ep :- Nat, c :- CompRow] (= (:pending (comp-result-row res ep c)) (:pending c)) (rfl))
(a/defn task-result-row [res :- RunResult, t :- TaskRow] TaskRow (TaskRow.mk (:id t) (:owner t) (:run t) res (:handles t) (:inputs t)))
(a/theorem task-result-row-id [res :- RunResult, t :- TaskRow] (= (task-id (task-result-row res t)) (task-id t)) (rfl))

;; creations of the predecessor that this run did not re-create are released: the tasks
;; among them that still run are cancelled (§5.2)
(a/defn released-run [w :- World, keep :- (List Nat), x :- Nat] Bool
  (Bool.and (Bool.not (reach-mem x keep))
            (match (task-find w x) [none false]
                   [(some t) (opt-test run-alive (run-find w (:run t)))])))
(a/defn task-run-of [w :- World, x :- Nat] Nat (match (task-find w x) [none 0] [(some t) (:run t)]))
(a/defn task-runs [w :- World, xs :- (List Nat)] (List Nat)
  (match xs [nil (List.nil Nat)] [(cons h t) (List.cons Nat (task-run-of w h) (task-runs w t))]))
(a/defn released-runs [w :- World, c :- CompRow] (List Nat)
  (task-runs w (tbl-filter (released-run w (created-ids (:basis c))) (created-ids (:adopt-basis c)))))

;; the edges a completed task fires: `on-task` (rule.clj), its wait creditors (activations
;; and host waits) and the dep edges of computations awaiting it

(a/defn complete-comp [w :- World, r :- RunRow, c :- CompRow, res :- RunResult] Casc
  (Casc.mk (settle (cancel-res (comp-upd w (:id c) (comp-result-row res (:epoch r))) r) (:id c)
                   (Bool.not (res-same res (:result c))))
           (cancel-jobs (released-runs w c))))
(a/defn complete-task [w :- World, r :- RunRow, k :- Nat, res :- RunResult] Casc
  (Casc.mk (nat-fold (fire-edge res) (cancel-res (task-upd w k (task-result-row res)) r)
                     (tbl-scan edge-id (on-task k) (:edges w)))
           (cancel-jobs (owned-runs w (scope-subtree w (:scope r))))))
;; R done; by kind of entity; a stale computation run's result is discarded (W#1)
(a/defn complete-body [w :- World, r :- RunRow, res :- RunResult] Casc
  (match (comp-find w (:of r))
    [none (match (task-find w (:of r))
            [none (Casc.mk w (List.nil Job))]
            [(some k) (complete-task w r (:id k) res)])]
    [(some c) (if (Nat.beq (:epoch r) (:epoch c)) (complete-comp w r c res) (Casc.mk w (List.nil Job)))]))
;; then: cleanup[R] unless retirable, the cancels and T13 (cascade), T10 on the entity when it
;; is final (a completed task; a final computation)
(a/defn retire-after [w :- World, rid :- Nat] World
  (match (run-find w rid)
    [none w]
    [(some r) (if (retirable r) w (cleanup-set w rid (cleanup-rows-of w r)))]))
(a/defn complete-raw [w :- World, r :- RunRow, res :- RunResult] World
  (fin-if-final
    (run-cascade (retire-after (:world (complete-body (run-upd w (:id r) run-complete-row) r res)) (:id r))
                 (List.append Job (:rest (complete-body (run-upd w (:id r) run-complete-row) r res))
                              (List.cons Job (Job.jretire (:id r)) (List.nil Job))))
    (:of r)))

(a/defn run-normal [r :- RunRow] Bool (Bool.and (run-alive r) (Nat.beq (:mode r) mode-normal)))
(a/defn t12-complete [w :- World, st :- Nat, tag :- Nat, v :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (if (run-normal r) (accept (complete-raw w r (RunResult.mk tag v))) (refuse w))]))

(a/theorem inv-complete-body [w :- World, r :- RunRow, res :- RunResult]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (complete-body w r res))) true))
  (intro h)
  (cases hc (comp-find w (:of r)))
  (case [none]
    (cases hk (task-find w (:of r)))
    (case [none] (simp only [complete-body hc hk]) (exact h))
    (case [some k]
      (simp only [complete-body hc hk complete-task])
      (exact (nat-fold-inv (fire-edge res) (inv-fire-edge res) _ _
               (inv-cancel-res _ r (inv-task-upd w (:id k) (task-result-row res) (task-result-row-id res) h))))))
  (case [some c]
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [complete-body hc he]) (exact h))
    (case [true]
      (simp only [complete-body hc he complete-comp])
      (exact (inv-settle _ (:id c) _ (inv-cancel-res _ r
               (inv-comp-upd w (:id c) (comp-result-row res (:epoch r)) (comp-result-row-id res (:epoch r))
                 (comp-result-row-pending res (:epoch r)) h)))))))

(a/theorem inv-retire-after [w :- World, rid :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (retire-after w rid)) true))
  (intro h)
  (cases hr (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [retire-after hr]) (exact h)
  (cases ht (retirable r))
  (simp only [retire-after hr ht]) (exact (inv-cleanup-set w rid _ h))
  (simp only [retire-after hr ht]) (exact h))

(a/theorem inv-complete-raw [w :- World, r :- RunRow, res :- RunResult]
  (=> (= (inv-sample w) true) (= (inv-sample (complete-raw w r res)) true))
  (intro h)
  (have h0 := (inv-run-upd w (:id r) run-complete-row run-complete-row-id h))
  (simp only [complete-raw])
  (exact (inv-fin-if-final _ (:of r) (inv-run-cascade _ _ (inv-retire-after _ (:id r) (inv-complete-body _ r res h0))))))

(a/theorem t12-inv [w :- World, st :- Nat, tag :- Nat, v :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t12-complete w st tag v))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t12-complete ht refuse]) (exact h)
  (cases hn (run-normal r))
  (simp only [t12-complete ht hn refuse]) (exact h)
  (simp only [t12-complete ht hn accept]) (exact (inv-complete-raw w r _ h)))

(a/theorem t12-refuse [w :- World, st :- Nat, tag :- Nat, v :- Nat]
  (=> (= (:accepted (t12-complete w st tag v)) false) (= (:world (t12-complete w st tag v)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t12-complete ht refuse])
  (cases hn (run-normal r))
  (simp only [t12-complete ht hn refuse])
  (simp [t12-complete ht hn accept] at ha))

;; ===========================================================================
;; Part F. T6 await(R, ds, mode) (X#4, Z#7, Z#28), T22 host-await (Z#27), T8 with validation,
;; the scheduling choice
;; ===========================================================================

(a/defn deb-exists [w :- World, d :- Nat] Bool
  (Bool.or (comp-has w d) (Bool.or (task-has w d) (Bool.or (source-has w d) (resource-has w d)))))
;; the debtor-list without repetitions, first occurrences in order
(a/defn nat-distinct-acc [seen :- (List Nat), xs :- (List Nat)] (List Nat)
  (match xs [nil (List.nil Nat)]
         [(cons h t) (if (nat-mem h seen) (nat-distinct-acc seen t)
                         (List.cons Nat h (nat-distinct-acc (List.cons Nat h seen) t)))]))
(a/defn nat-distinct [xs :- (List Nat)] (List Nat) (nat-distinct-acc (List.nil Nat) xs))
(a/defn nat-len [xs :- (List Nat)] Nat (match xs [nil 0] [(cons h t) (+ (nat-len t) 1)]))

;; fast path (T6): a live computation (or a valid idle one, read without reactivation), a
;; completed task, a closed source, a fired resource
(a/defn res-fired [w :- World, d :- Nat] Bool
  (match (resource-find w d) [none false] [(some z) (Nat.beq (:phase z) rp-fired)]))
;; Z#31: a signal or cell is read at once (a dep edge like track in a computation, a snapshot
;; in a task)
(a/defn sig-cell [w :- World, d :- Nat] Bool
  (match (source-find w d) [none false]
         [(some s) (Bool.or (Nat.beq (:kind s) sk-signal) (Nat.beq (:kind s) sk-cell))]))
(a/defn fast-ready [w :- World, d :- Nat] Bool
  (match (comp-find w d)
    [none (Bool.or (deb-final w d) (Bool.or (res-fired w d) (sig-cell w d)))]
    [(some c) (Bool.or (comp-live c) (Bool.and (:idle c) (valid-idle w c)))]))

;; member edges: in a computation run a dep edge (creditor C) for C/K/X debtors, a wait edge
;; (creditor A) otherwise and for resources (Z#6); cont per §2's re-entrancy rule (Y#3)
(a/defn await-cont [r :- RunRow, mode :- Nat, k :- Nat] Nat
  (if (Bool.and (Nat.beq mode am-one) (Bool.and (fins-empty (:finalizers r)) (nats-empty (:resources r)))) k cont-restart))
(a/defn as-dep [w :- World, r :- RunRow, d :- Nat] Bool (Bool.and (in-comp w r) (Bool.not (resource-has w d))))
(a/defn await-edge [w :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat] EdgeRow
  (if (as-dep w r d)
      (EdgeRow.mk 0 ek-dep (:of r) d (await-cont r mode k) (:effect-index r) ph-armed false false 0 false 0 0)
      (EdgeRow.mk 0 ek-wait a d cont-restart (:effect-index r) ph-armed false false 0 false 0 0)))
;; re-await of an existing site edge: re-armed with the new cont (its baseline stays)
(a/defn edge-reawait [c :- Nat, e :- EdgeRow] EdgeRow
  (EdgeRow.mk (:id e) (:kind e) (:creditor e) (:debtor e) c (:at e) ph-armed (:marked e) (:has-seen e) (:seen e)
              (:has-base e) (:base-value e) (:base-version e)))

(a/structure DE [] (deb Nat) (edge Nat))
(a/structure AwAcc [] (world World) (pairs (List DE)) (ok Bool))
;; one distinct debtor: reuse C's dep edge at this site (re-await ends adoption, Z#21) or insert
;; a fresh one (ids consecutive in debtor-list order); a new dep edge on a computation is
;; followed by the I12 raise, whose failure (the propagation reached the debtor: a cycle, or
;; out of fuel) clears `ok`, and T6 then refuses (::cycle)
(a/defn await-new-dep [w :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat] RaiseRes
  (raise-run (insert-edge-checked w (await-edge w r a mode k d)) (:of r) d))
(a/defn await-step [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat] AwAcc
  (if (as-dep (:world acc) r d)
      (match (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d)
        [none (AwAcc.mk (comp-upd (:world (await-new-dep (:world acc) r a mode k d))
                                  (:of r) (comp-consume-adopt (:effect-index r) d))
                        (List.cons DE (DE.mk d (:next-id (:world acc))) (:pairs acc))
                        (Bool.and (:ok acc) (:ok (await-new-dep (:world acc) r a mode k d))))]
        [(some e) (AwAcc.mk (comp-upd (edge-upd (:world acc) (:id e) (edge-reawait (await-cont r mode k)))
                                      (:of r) (comp-consume-adopt (:effect-index r) d))
                            (List.cons DE (DE.mk d (:id e)) (:pairs acc)) (:ok acc))])
      (AwAcc.mk (insert-edge-checked (:world acc) (await-edge (:world acc) r a mode k d))
                (List.cons DE (DE.mk d (:next-id (:world acc))) (:pairs acc)) (:ok acc))))
(a/defn await-wire [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, ds :- (List Nat)] AwAcc
  (match ds [nil acc] [(cons d t) (await-wire r a mode k (await-step r a mode k acc d) t)]))

(a/defn pair-edge [d :- Nat, ps :- (List DE)] Nat
  (match ps [nil 0] [(cons h t) (if (Nat.beq (:deb h) d) (:edge h) (pair-edge d t))]))
(a/defn mk-members [ps :- (List DE), i :- Nat, ds :- (List Nat)] (List Member)
  (match ds [nil (List.nil Member)]
         [(cons d t) (List.cons Member (Member.mk (pair-edge d ps) i) (mk-members ps (+ i 1) t))]))
(a/defn none-slots [ds :- (List Nat)] (List RunResult)
  (match ds [nil (List.nil RunResult)] [(cons h t) (List.cons RunResult none-result (none-slots t))]))
(a/defn act-set-members [ms :- (List Member), a :- ActRow] ActRow
  (ActRow.mk (:id a) (:run a) (:mode a) ms (:slots a) (:remaining a) (:cont a) (:spawned a)))
(a/theorem act-set-members-id [ms :- (List Member), a :- ActRow] (= (act-id (act-set-members ms a)) (act-id a)) (rfl))

;; fast fills: a ready debtor fills its slot(s) in the same commit (T9 on its member edge)
(a/defn fast-fill [ps :- (List DE), w :- World, d :- Nat] World
  (if (fast-ready w d) (fire-edge (deb-result w d) w (pair-edge d ps)) w))
(a/defn run-park-row [r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) act-parked (:mode r) false
             (:effect-index r) (:finalizers r) (:resources r)))
(a/theorem run-park-row-id [r :- RunRow] (= (run-id (run-park-row r)) (run-id r)) (rfl))
;; the run parks unless the fast path resumed it (its slice then continues, reading B6)
(a/defn park-if [w :- World, a :- Nat, rid :- Nat] World
  (if (act-has w a) (run-upd w rid run-park-row) w))

;; Activation A = next-id (always allocated, Z#28; no row remains when the fast path fills
;; every slot), then, in a computation run, the reactivation edges of valid idle debtors
;; (reactive demand, §3.4), then the member edges in debtor-list order. Other demand is the
;; T5/T11 item the engine issues next (reading B1).
(a/defn await-pre [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)] World
  (nat-fold demand-reactive
            (bump (act-ins (run-upd w (:id r) run-tick)
                           (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine)))
            (nat-distinct ds)))
(a/defn await-acc [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)] AwAcc
  (await-wire r (:next-id w) mode k (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (nat-distinct ds)))
(a/defn await-post [a :- Nat, rid :- Nat, ds :- (List Nat), acc :- AwAcc] World
  (nat-fold fin-if-final
    (park-if (nat-fold (fast-fill (:pairs acc))
                       (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds)))
                       (nat-distinct ds))
             a rid)
    (nat-distinct ds)))
(a/defn await-raw [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)] World
  (await-post (:next-id w) (:id r) ds (await-acc w r ds mode k mine)))

;; ::cycle (I12): a computation must not await itself or a computation that reaches it through
;; dep edges (debtor direction). Ranks are not maintained (reading B7).
(a/defn dep-debtors [es :- (List EdgeRow), x :- Nat] (List Nat)
  (match es [nil (List.nil Nat)]
         [(cons h t) (if (Bool.and (Nat.beq (:creditor h) x) (Nat.beq (:kind h) ek-dep))
                         (List.cons Nat (:debtor h) (dep-debtors t x)) (dep-debtors t x))]))
(a/defn cycle-fuel [w :- World, ds :- (List Nat)] (List Nat)
  (List.cons Nat 0 (List.append Nat ds (List.append Nat (tbl-ids edge-id (:edges w)) (tbl-ids edge-id (:edges w))))))
(a/defn await-cycle [w :- World, r :- RunRow, ds :- (List Nat)] Bool
  (Bool.and (in-comp w r)
            (reach-mem (:of r) (:visited (reach-run-l (cycle-fuel w ds) (dep-debtors (:edges w)) ds)))))

(a/defn mode-ok [mode :- Nat, ds :- (List Nat)] Bool
  (Bool.and (Nat.ble mode am-any)
            (Bool.and (Nat.blt 0 (nat-len ds)) (Bool.or (Bool.not (Nat.beq mode am-one)) (Nat.beq (nat-len ds) 1)))))
(a/defn await-ok [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, fresh :- Nat] Bool
  (Bool.and (Nat.beq fresh (:next-id w))
   (Bool.and (run-normal r)
    (Bool.and (mode-ok mode ds)
     (Bool.and (tbl-all (deb-exists w) ds) (Bool.not (await-cycle w r ds)))))))

(a/defn t6-await [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (if (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine)))
                  (accept (await-raw w r ds mode k mine)) (refuse w))]))

(a/theorem edge-reawait-edge-id [c :- Nat, e :- EdgeRow] (= (edge-id (edge-reawait c e)) (edge-id e)) (rfl))
(a/theorem edge-reawait-kind [c :- Nat, e :- EdgeRow] (= (:kind (edge-reawait c e)) (:kind e)) (rfl))
(a/theorem edge-reawait-creditor [c :- Nat, e :- EdgeRow] (= (:creditor (edge-reawait c e)) (:creditor e)) (rfl))
(a/theorem edge-reawait-debtor [c :- Nat, e :- EdgeRow] (= (:debtor (edge-reawait c e)) (:debtor e)) (rfl))
(a/theorem edge-reawait-marked [c :- Nat, e :- EdgeRow] (= (:marked (edge-reawait c e)) (:marked e)) (rfl))

(a/theorem inv-await-step [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (inv-sample (:world acc)) true) (= (inv-sample (:world (await-step r a mode k acc d))) true))
  (intro h)
  (cases hd (as-dep (:world acc) r d))
  (case [false]
    (simp only [await-step hd])
    (exact (inv-insert-edge-checked _ _ h)))
  (case [true]
    (cases hs (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none]
      (simp only [await-step hd hs])
      (simp only [await-new-dep])
      (exact (inv-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) d)
               (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _)
               (inv-raise-for _ (:of r) d (inv-insert-edge-checked _ _ h)))))
    (case [some e]
      (simp only [await-step hd hs])
      (exact (inv-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) d)
               (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _)
               (inv-edge-upd _ (:id e) (edge-reawait (await-cont r mode k)) (edge-reawait-edge-id _)
                 (edge-reawait-kind _) (edge-reawait-creditor _) (edge-reawait-debtor _) (edge-reawait-marked _) h))))))

(a/theorem inv-await-wire [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, ds :- (List Nat)]
  (forall [acc :- AwAcc] (=> (= (inv-sample (:world acc)) true) (= (inv-sample (:world (await-wire r a mode k acc ds))) true)))
  (induction ds)
  (case' [cons d t ih])
  (case' [nil])
  (intros acc h) (simp only [await-wire]) (exact h)
  (intros acc h) (simp only [await-wire]) (exact (ih _ (inv-await-step r a mode k acc d h))))

(a/theorem inv-fast-fill [ps :- (List DE), w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (fast-fill ps w d)) true))
  (intro h)
  (cases hr (fast-ready w d))
  (simp only [fast-fill hr]) (exact h)
  (simp only [fast-fill hr]) (exact (inv-fire-edge _ w _ h)))

(a/theorem inv-park-if [w :- World, a :- Nat, rid :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (park-if w a rid)) true))
  (intro h)
  (cases ha (act-has w a))
  (simp only [park-if ha]) (exact h)
  (simp only [park-if ha]) (exact (inv-run-upd w rid run-park-row run-park-row-id h)))

(a/theorem inv-await-pre [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (inv-sample w) true) (= (inv-sample (await-pre w r ds mode k mine)) true))
  (intro h)
  (have h1 := (inv-run-upd w (:id r) run-tick run-tick-run-id h))
  (have he (= (act-id (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine))
              (:next-id (run-upd w (:id r) run-tick))))
  (rfl)
  (simp only [await-pre])
  (exact (nat-fold-inv demand-reactive inv-demand-reactive _ _
           (inv-act-ins-fresh _ _ he h1))))

(a/theorem inv-await-post [a :- Nat, rid :- Nat, ds :- (List Nat), acc :- AwAcc]
  (=> (= (inv-sample (:world acc)) true) (= (inv-sample (await-post a rid ds acc)) true))
  (intro h)
  (have h2 (= (inv-sample (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds)))) true))
  (exact (inv-act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))
           (act-set-members-id (mk-members (:pairs acc) 0 ds)) h))
  (have h3 (= (inv-sample (nat-fold (fast-fill (:pairs acc))
                            (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds)))
                            (nat-distinct ds))) true))
  (exact (nat-fold-inv (fast-fill (:pairs acc)) (inv-fast-fill (:pairs acc)) (nat-distinct ds)
           (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))) h2))
  (have h4 := (inv-park-if (nat-fold (fast-fill (:pairs acc))
                            (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds)))
                            (nat-distinct ds)) a rid h3))
  (exact (nat-fold-inv fin-if-final inv-fin-if-final (nat-distinct ds) _ h4)))

(a/theorem inv-await-raw [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (inv-sample w) true) (= (inv-sample (await-raw w r ds mode k mine)) true))
  (intro h)
  (have h1 (= (inv-sample (:world (await-acc w r ds mode k mine))) true))
  (exact (inv-await-wire r (:next-id w) mode k (nat-distinct ds)
           (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (inv-await-pre w r ds mode k mine h)))
  (exact (inv-await-post (:next-id w) (:id r) ds (await-acc w r ds mode k mine) h1)))

(a/theorem t6-inv [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t6-await w st ds mode k fresh mine))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t6-await ht refuse]) (exact h)
  (cases hg (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
  (simp only [t6-await ht hg refuse]) (exact h)
  (simp only [t6-await ht hg accept]) (exact (inv-await-raw w r ds mode k mine h)))

(a/theorem t6-refuse [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
  (=> (= (:accepted (t6-await w st ds mode k fresh mine)) false) (= (:world (t6-await w st ds mode k fresh mine)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t6-await ht refuse])
  (cases hg (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
  (simp only [t6-await ht hg refuse])
  (simp [t6-await ht hg accept] at ha))

;; ---- T22 host-await(d) / host-unawait(e) (Z#27): a pending host-wait edge (kind wait,
;; creditor host = 0) is root 7. It is consumed when d settles (`settle-host`), completes (a
;; task's wait creditors), fires (a resource), or at once when d is already ready (fast path:
;; a live or valid idle computation, a completed task, a closed source, a fired resource).
;; An invalid idle or dirty d is demanded by the T5/T11 item that follows (reading B1).
(a/defn host-wait-edge [d :- Nat] EdgeRow
  (EdgeRow.mk 0 ek-wait 0 d cont-restart 0 ph-armed false false 0 false 0 0))
;; the edge (fresh), then the demand (Z#33: an idle d leaves idle; a valid one is reactivated)
(a/defn host-await-dem [w :- World, d :- Nat] World (demand-reactive (insert-edge-checked w (host-wait-edge d)) d))
(a/defn host-await-raw [w :- World, d :- Nat] World
  (if (fast-ready (host-await-dem w d) d)
      (fire-edge (deb-result (host-await-dem w d) d) (host-await-dem w d) (:next-id w))
      (host-await-dem w d)))
(a/defn t22-host-await [w :- World, d :- Nat, fresh :- Nat] Outcome
  (if (Bool.and (Nat.beq fresh (:next-id w)) (deb-exists w d)) (accept (host-await-raw w d)) (refuse w)))
(a/defn t22-host-unawait [w :- World, x :- Nat] Outcome
  (match (edge-find w x)
    [none (refuse w)]
    [(some e) (if (Bool.and (Nat.beq (:kind e) ek-wait) (Nat.beq (:creditor e) 0)) (accept (remove-edge w x)) (refuse w))]))

(a/theorem inv-host-await-raw [w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (host-await-raw w d)) true))
  (intro h)
  (have h1 (= (inv-sample (host-await-dem w d)) true))
  (exact (inv-demand-reactive _ d (inv-insert-edge-checked w (host-wait-edge d) h)))
  (cases hr (fast-ready (host-await-dem w d) d))
  (simp only [host-await-raw hr]) (exact h1)
  (simp only [host-await-raw hr]) (exact (inv-fire-edge _ _ (:next-id w) h1)))

(a/theorem t22-inv [w :- World, d :- Nat, fresh :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t22-host-await w d fresh))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (deb-exists w d)))
  (simp only [t22-host-await hg refuse]) (exact h)
  (simp only [t22-host-await hg accept]) (exact (inv-host-await-raw w d h)))

(a/theorem t22-refuse [w :- World, d :- Nat, fresh :- Nat]
  (=> (= (:accepted (t22-host-await w d fresh)) false) (= (:world (t22-host-await w d fresh)) w))
  (intro ha)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (deb-exists w d)))
  (simp only [t22-host-await hg refuse])
  (simp [t22-host-await hg accept] at ha))

(a/theorem t22-un-inv [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t22-host-unawait w x))) true))
  (intro h)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [t22-host-unawait hf refuse]) (exact h)
  (cases hk (Bool.and (Nat.beq (:kind e) ek-wait) (Nat.beq (:creditor e) 0)))
  (simp only [t22-host-unawait hf hk refuse]) (exact h)
  (simp only [t22-host-unawait hf hk accept]) (exact (inv-remove-edge w x h)))

(a/theorem t22-un-refuse [w :- World, x :- Nat]
  (=> (= (:accepted (t22-host-unawait w x)) false) (= (:world (t22-host-unawait w x)) w))
  (intro ha)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [t22-host-unawait hf refuse])
  (cases hk (Bool.and (Nat.beq (:kind e) ek-wait) (Nat.beq (:creditor e) 0)))
  (simp only [t22-host-unawait hf hk refuse])
  (simp [t22-host-unawait hf hk accept] at ha))

;; ---- T8 observe with validation (§3.4) and the Z#15 initial delivery: the edge is
;; registered (delivered at once for a source or live computation), d is demanded reactively
;; (a valid idle computation is reactivated, its edges get the next ids), and a d that became
;; live is delivered (seen = none -> its version)
(a/defn observe-raw [w :- World, d :- Nat, cb :- Nat] World
  (if (deb-ready (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) d)
      (fire-edge (deb-result (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) d)
                 (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) (:next-id w))
      (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d)))
(a/defn t8-full [w :- World, d :- Nat, cb :- Nat, fresh :- Nat] Outcome
  (if (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb)))
      (accept (observe-raw w d cb))
      (refuse w)))

(a/theorem t8-full-inv [w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t8-full w d cb fresh))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
  (simp only [t8-full hg refuse]) (exact h)
  (have he (= (edge-ok-in w (observe-edge w d cb)) true))
  (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
  (have h1 := (inv-demand-reactive _ d (insert-edge-fresh-inv-sample w (observe-edge w d cb) he h)))
  (simp only [t8-full hg accept observe-raw])
  (cases hr (deb-ready (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) d))
  (simp only [hr]) (exact h1)
  (simp only [hr]) (exact (inv-fire-edge _ _ (:next-id w) h1)))

(a/theorem t8-full-refuse [w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (:accepted (t8-full w d cb fresh)) false) (= (:world (t8-full w d cb fresh)) w))
  (intro ha)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
  (simp only [t8-full hg refuse])
  (simp [t8-full hg accept] at ha))

;; ---- the scheduling choice (D0): an active normal run without the slice gets it, when no
;; run holds one (cleanup slices of unwinding runs are not modelled)
(a/defn run-enter-row [r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) (:act r) (:mode r) true
             (:effect-index r) (:finalizers r) (:resources r)))
(a/theorem run-enter-row-id [r :- RunRow] (= (run-id (run-enter-row r)) (run-id r)) (rfl))
(a/defn run-slice [r :- RunRow] Bool (:slice r))
(a/defn sched-ok [w :- World, r :- RunRow] Bool
  (Bool.and (Nat.beq (:act r) act-active)
   (Bool.and (Nat.beq (:mode r) mode-normal)
    (Bool.and (Bool.not (:slice r)) (Bool.not (tbl-any run-slice (:runs w)))))))
(a/defn t-schedule [w :- World, rid :- Nat] Outcome
  (match (run-find w rid)
    [none (refuse w)]
    [(some r) (if (sched-ok w r) (accept (run-upd w rid run-enter-row)) (refuse w))]))

(a/theorem sched-inv [w :- World, rid :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-schedule w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-schedule hf refuse]) (exact h)
  (cases hg (sched-ok w r))
  (simp only [t-schedule hf hg refuse]) (exact h)
  (simp only [t-schedule hf hg accept]) (exact (inv-run-upd w rid run-enter-row run-enter-row-id h)))

(a/theorem sched-refuse [w :- World, rid :- Nat]
  (=> (= (:accepted (t-schedule w rid)) false) (= (:world (t-schedule w rid)) w))
  (intro ha)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-schedule hf refuse])
  (cases hg (sched-ok w r))
  (simp only [t-schedule hf hg refuse])
  (simp [t-schedule hf hg accept] at ha))

;; ---- handle-new x (Z#29): a row's handle count goes from 0 to 1 (computation, task, source
;; or publication, searched in that order); any other count, or no row, refuses
(a/defn comp-h1 [c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) 1))
(a/defn task-h1 [t :- TaskRow] TaskRow (TaskRow.mk (:id t) (:owner t) (:run t) (:result t) 1 (:inputs t)))
(a/defn source-h1 [s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) (:owner s) (:kind s) (:state s) (:version s) (:open s) 1 (:queue s)))
(a/defn pub-h1 [p :- PubRow] PubRow (PubRow.mk (:id p) (:edge p) (:basis p) 1))
(a/theorem comp-h1-id [c :- CompRow] (= (comp-id (comp-h1 c)) (comp-id c)) (rfl))
(a/theorem comp-h1-pending [c :- CompRow] (= (:pending (comp-h1 c)) (:pending c)) (rfl))
(a/theorem task-h1-id [t :- TaskRow] (= (task-id (task-h1 t)) (task-id t)) (rfl))
(a/theorem source-h1-id [s :- SourceRow] (= (source-id (source-h1 s)) (source-id s)) (rfl))
(a/theorem pub-h1-id [p :- PubRow] (= (pub-id (pub-h1 p)) (pub-id p)) (rfl))

(a/defn new-pub-handle [w :- World, x :- Nat] Outcome
  (match (pub-find w x) [none (refuse w)]
         [(some p) (if (Nat.beq (:handles p) 0) (accept (pub-upd w x pub-h1)) (refuse w))]))
(a/defn new-source-handle [w :- World, x :- Nat] Outcome
  (match (source-find w x) [none (new-pub-handle w x)]
         [(some s) (if (Nat.beq (:handles s) 0) (accept (source-upd w x source-h1)) (refuse w))]))
(a/defn new-task-handle [w :- World, x :- Nat] Outcome
  (match (task-find w x) [none (new-source-handle w x)]
         [(some t) (if (Nat.beq (:handles t) 0) (accept (task-upd w x task-h1)) (refuse w))]))
(a/defn t-handle-new [w :- World, x :- Nat] Outcome
  (match (comp-find w x) [none (new-task-handle w x)]
         [(some c) (if (Nat.beq (:handles c) 0) (accept (comp-upd w x comp-h1)) (refuse w))]))

(defmacro ^:private defnew-lemmas
  [f find upd row-f inv-lemma inv-args next-f]
  (let [inv (symbol (str f "-inv")) ref (symbol (str f "-refuse"))
        next-inv (when next-f (symbol (str next-f "-inv"))) next-ref (when next-f (symbol (str next-f "-refuse")))]
    `(do
       (a/theorem ~inv [~'w :- ~'World, ~'x :- ~'Nat]
         (~'=> (~'= (~'inv-sample ~'w) true) (~'= (~'inv-sample (:world (~f ~'w ~'x))) true))
         (~'intro ~'h)
         (~'cases ~'hc (~find ~'w ~'x)) (~'case' [~'some ~'c]) (~'case' [~'none])
         ~@(if next-f
             [`(~'simp ~'only [~f ~'hc]) `(~'exact (~next-inv ~'w ~'x ~'h))]
             [`(~'simp ~'only [~f ~'hc ~'refuse]) `(~'exact ~'h)])
         (~'cases ~'hn (~'Nat.beq (:handles ~'c) 0))
         (~'simp ~'only [~f ~'hc ~'hn ~'refuse]) (~'exact ~'h)
         (~'simp ~'only [~f ~'hc ~'hn ~'accept])
         (~'exact (~inv-lemma ~'w ~'x ~row-f ~@inv-args ~'h)))
       (a/theorem ~ref [~'w :- ~'World, ~'x :- ~'Nat]
         (~'=> (~'= (:accepted (~f ~'w ~'x)) false) (~'= (:world (~f ~'w ~'x)) ~'w))
         (~'intro ~'ha)
         (~'cases ~'hc (~find ~'w ~'x)) (~'case' [~'some ~'c]) (~'case' [~'none])
         ~@(if next-f
             [`(~'simp ~'only [~f ~'hc] ~'at ~'ha) `(~'simp ~'only [~f ~'hc]) `(~'exact (~next-ref ~'w ~'x ~'ha))]
             [`(~'simp ~'only [~f ~'hc ~'refuse])])
         (~'cases ~'hn (~'Nat.beq (:handles ~'c) 0))
         (~'simp ~'only [~f ~'hc ~'hn ~'refuse])
         (~'simp [~f ~'hc ~'hn ~'accept] ~'at ~'ha)))))

(defnew-lemmas new-pub-handle pub-find pub-upd pub-h1 inv-pub-upd [pub-h1-id] nil)
(defnew-lemmas new-source-handle source-find source-upd source-h1 inv-source-upd [source-h1-id] new-pub-handle)
(defnew-lemmas new-task-handle task-find task-upd task-h1 inv-task-upd [task-h1-id] new-source-handle)
(defnew-lemmas t-handle-new comp-find comp-upd comp-h1 inv-comp-upd [comp-h1-id comp-h1-pending] new-task-handle)

;; ---- `any` losers (T6): when an `any` activation resumed (its row is gone and its run is not
;; done), the tasks R created for this await (`spawned`, from the item) that are still running
;; and have no other creditor (no edge names them) are cancelled (T14, cascade). Applied after
;; every accepted raw transition (`post`), by comparing the activations before and after.
(a/defn loser-task [w1 :- World, s :- Nat, k :- Nat] Bool
  (Bool.and (tbl-all (no-debtor k) (:edges w1))
            (match (task-find w1 k) [none false]
                   [(some t) (Bool.and (Nat.beq (:owner t) s) (opt-test run-alive (run-find w1 (:run t))))])))
(a/defn run-of-task [w1 :- World, r :- RunRow] Bool (task-has w1 (:of r)))
(a/defn any-resolved [w1 :- World, a :- ActRow] Bool
  (Bool.and (Nat.beq (:mode a) am-any)
            (Bool.and (Bool.not (act-has w1 (:id a)))
                      (Bool.and (opt-test run-alive (run-find w1 (:run a))) (opt-test (run-of-task w1) (run-find w1 (:run a)))))))
(a/defn run-scope-of [w1 :- World, rid :- Nat] Nat (match (run-find w1 rid) [none 0] [(some r) (:scope r)]))
(a/defn loser-runs [w1 :- World, a :- ActRow] (List Nat)
  (task-runs w1 (tbl-filter (loser-task w1 (run-scope-of w1 (:run a))) (:spawned a))))
(a/defn cancel-losers [w0 :- World, w1 :- World] World
  (run-cascade w1 (cancel-jobs (tbl-gather (any-resolved w1) (loser-runs w1) (:acts w0)))))

;; ===========================================================================
;; Part F2. Source operations (§4.3), finalizers (B3, B8), host cancel (T14), scopes (T16,
;; Q10 detach), release-world (T21)
;; ===========================================================================

;; ---- allocation without a row (the take fast path allocates the activation and edge ids
;; it does not keep, as the engine does)
(a/theorem next-id-bump-pos [w :- World] (= (Nat.blt 0 (:next-id (bump w))) true) (simp only [bump set-next-id Nat.blt_eq]))
(a/theorem all-ids-bump [w :- World] (= (all-ids (bump w)) (all-ids w)) (rfl))

(a/theorem ids-ok-bump [w :- World]
  (=> (= (ids-ok w) true) (= (ids-ok (bump w)) true))
  (intro h)
  (simp only [ids-ok Bool.and_eq_true] at h)
  (have hu (= (ids-unique (bump w)) true)) (exact (And.left h))
  (have hb (= (ids-below w) true)) (exact (And.right h))
  (simp only [ids-below Bool.and_eq_true] at hb)
  (have hmono (forall [i :- Nat] (=> (= (id-in-range (:next-id w) i) true) (= (id-in-range (+ (:next-id w) 1) i) true))))
  (intros i hi)
  (simp only [id-in-range Bool.and_eq_true Nat.blt_eq] at hi)
  (simp only [id-in-range Bool.and_eq_true Nat.blt_eq])
  (omega)
  (have hall (= (tbl-all (id-in-range (+ (:next-id w) 1)) (all-ids w)) true))
  (exact (tbl-all-mono Nat (id-in-range (:next-id w)) (id-in-range (+ (:next-id w) 1)) hmono (all-ids w) (And.right hb)))
  (have hb2 (= (ids-below (bump w)) true))
  (simp only [ids-below Bool.and_eq_true (next-id-bump-pos w) (all-ids-bump w) true_and])
  (exact hall)
  (simp only [ids-ok hu hb2 Bool.and_self]))

(a/theorem inv-bump [w :- World]
  (=> (= (inv-sample w) true) (= (inv-sample (bump w)) true))
  (intro h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (exact (inv-intro (bump w) (Eq.trans (pending-exact-bump w) (And.left hs))
           (Eq.trans (edges-ref-ok-bump w) (And.left (And.right hs)))
           (ids-ok-bump w (And.right (And.right hs))))))

(a/theorem inv-set-released [w :- World, v :- Bool]
  (=> (= (inv-sample w) true) (= (inv-sample (set-released w v)) true))
  (intro h) (exact h))
(a/theorem inv-set-pending-act [w :- World, v :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (set-pending-act w v)) true))
  (intro h) (exact h))

;; ---- source rows
(a/defn source-bump [s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) (:owner s) (:kind s) (:state s) (+ (:version s) 1) (:open s) (:handles s) (:queue s)))
(a/defn source-enqueue [v :- Nat, s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) (:owner s) (:kind s) (:state s) (:version s) (:open s) (:handles s)
                (List.append Nat (:queue s) (List.cons Nat v (List.nil Nat)))))
(a/defn source-permit [s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) (:owner s) (:kind s) (+ (:state s) 1) (:version s) (:open s) (:handles s) (:queue s)))
(a/defn nat-tail [xs :- (List Nat)] (List Nat) (match xs [nil (List.nil Nat)] [(cons h t) t]))
;; take's immediate path: a mailbox drops its head message, a semaphore one permit; version + 1 (as the
;; engine). Nothing left (reached only on a closed source, Z#57: the take fails with err ::closed): unchanged.
(a/defn src-available [s :- SourceRow] Bool
  (if (Nat.beq (:kind s) sk-mailbox) (Bool.not (nats-empty (:queue s))) (Nat.blt 0 (:state s))))
(a/defn source-consume [s :- SourceRow] SourceRow
  (if (src-available s)
      (if (Nat.beq (:kind s) sk-mailbox)
          (SourceRow.mk (:id s) (:owner s) (:kind s) (:state s) (+ (:version s) 1) (:open s) (:handles s) (nat-tail (:queue s)))
          (SourceRow.mk (:id s) (:owner s) (:kind s) (- (:state s) 1) (+ (:version s) 1) (:open s) (:handles s) (:queue s)))
      s))
(a/theorem source-bump-id [s :- SourceRow] (= (source-id (source-bump s)) (source-id s)) (rfl))
(a/theorem source-enqueue-id [v :- Nat, s :- SourceRow] (= (source-id (source-enqueue v s)) (source-id s)) (rfl))
(a/theorem source-permit-id [s :- SourceRow] (= (source-id (source-permit s)) (source-id s)) (rfl))
(a/theorem source-consume-id [s :- SourceRow] (= (source-id (source-consume s)) (source-id s))
  (cases ha (src-available s)) (all_goals (cases h (Nat.beq (:kind s) sk-mailbox)))
  (all_goals (simp [source-consume source-id ha h])))

;; ---- waiters (§4.3): the oldest (smallest id) armed wait edge on x whose activation can
;; receive: its run is current (a task run, or a current computation run) and parked. Waiters
;; of stale runs are skipped; a cancelled run's waiters are already gone with its activation.
(a/defn act-receives [w :- World, a :- ActRow] Bool
  (Bool.and (run-current w (:run a)) (opt-test run-parked (run-find w (:run a)))))
(a/defn waiter-ok [w :- World, x :- Nat, e :- EdgeRow] Bool
  (Bool.and (Nat.beq (:kind e) ek-wait)
   (Bool.and (Nat.beq (:debtor e) x)
    (Bool.and (Nat.beq (:phase e) ph-armed) (opt-test (act-receives w) (act-find w (:creditor e)))))))
(a/defn min-id [best :- Nat, es :- (List EdgeRow)] Nat
  (match es [nil best]
         [(cons h t) (min-id (if (Bool.or (Nat.beq best 0) (Nat.blt (:id h) best)) (:id h) best) t)]))
(a/defn oldest-waiter [w :- World, x :- Nat] Nat (min-id 0 (tbl-filter (waiter-ok w x) (:edges w))))

;; ---- deliver(X, v) (§4.3): once (a deferred, open, version 0): state := v, version := 1;
;; its dep and observe edges fire (Z#36: not a write, no computation consumed the undelivered
;; deferred, so nothing is marked), every wait edge on X fires with ok v (host waits
;; consumed), then T10 finalizes X (it is final, D1)
(a/defn deliverable [s :- SourceRow] Bool
  (Bool.and (Nat.beq (:kind s) sk-deferred) (Bool.and (:open s) (Nat.beq (:version s) 0))))
(a/defn deliver-fire [w :- World, x :- Nat, v :- Nat] World
  (nat-fold (fire-edge (RunResult.mk res-ok v)) (source-upd w x (source-write v)) (edges-onto x (:edges w))))
(a/defn deliver-raw [w :- World, x :- Nat, v :- Nat] World
  (finalize-debtor (nat-fold (fire-edge (RunResult.mk res-ok v)) (deliver-fire w x v) (waits-on x (:edges w))) x))
(a/theorem inv-deliver-fire [w :- World, x :- Nat, v :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (deliver-fire w x v)) true))
  (intro h)
  (simp only [deliver-fire])
  (exact (nat-fold-inv (fire-edge (RunResult.mk res-ok v)) (inv-fire-edge (RunResult.mk res-ok v))
           (edges-onto x (:edges w)) _
           (inv-source-upd w x (source-write v) (source-write-source-id v) h))))
(a/defn t-deliver [w :- World, x :- Nat, v :- Nat] Outcome
  (match (source-find w x)
    [none (refuse w)]
    [(some s) (if (deliverable s) (accept (deliver-raw w x v)) (refuse w))]))

(a/theorem t-deliver-inv [w :- World, x :- Nat, v :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-deliver w x v))) true))
  (intro h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-deliver hs refuse]) (exact h)
  (cases hg (deliverable s))
  (simp only [t-deliver hs hg refuse]) (exact h)
  (simp only [t-deliver hs hg accept deliver-raw])
  (exact (inv-finalize-debtor _ x (nat-fold-inv (fire-edge (RunResult.mk res-ok v)) (inv-fire-edge (RunResult.mk res-ok v))
                                    _ _ (inv-deliver-fire w x v h)))))

(a/theorem t-deliver-refuse [w :- World, x :- Nat, v :- Nat]
  (=> (= (:accepted (t-deliver w x v)) false) (= (:world (t-deliver w x v)) w))
  (intro ha)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-deliver hs refuse])
  (cases hg (deliverable s))
  (simp only [t-deliver hs hg refuse])
  (simp [t-deliver hs hg accept] at ha))

;; ---- post(X, v) / release(X) (§4.3): version + 1; the oldest receiving waiter gets the
;; message (ok v) / the permit (ok 1) through T9 (its `one` activation resumes); otherwise the
;; message is appended to the queue / the permit count goes up. Refused on a closed source
;; (read-only, T16; reading B18).
(a/defn serve-or [w :- World, x :- Nat, res :- RunResult, keep :- (=> SourceRow SourceRow)] World
  (if (Nat.beq (oldest-waiter w x) 0) (source-upd w x keep) (fire-edge res w (oldest-waiter w x))))
(a/defn post-raw [w :- World, x :- Nat, v :- Nat] World
  (serve-or (source-upd w x source-bump) x (RunResult.mk res-ok v) (source-enqueue v)))
(a/defn release-raw [w :- World, x :- Nat] World
  (serve-or (source-upd w x source-bump) x (RunResult.mk res-ok 1) source-permit))
(a/defn open-kind [k :- Nat, s :- SourceRow] Bool (Bool.and (Nat.beq (:kind s) k) (:open s)))
(a/defn t-post [w :- World, x :- Nat, v :- Nat] Outcome
  (match (source-find w x)
    [none (refuse w)]
    [(some s) (if (open-kind sk-mailbox s) (accept (post-raw w x v)) (refuse w))]))
(a/defn t-release [w :- World, x :- Nat] Outcome
  (match (source-find w x)
    [none (refuse w)]
    [(some s) (if (open-kind sk-semaphore s) (accept (release-raw w x)) (refuse w))]))

(a/theorem inv-serve-or [w :- World, x :- Nat, res :- RunResult, keep :- (=> SourceRow SourceRow),
                         hk :- (forall [s :- SourceRow] (= (source-id (keep s)) (source-id s)))]
  (=> (= (inv-sample w) true) (= (inv-sample (serve-or w x res keep)) true))
  (intro h)
  (cases hz (Nat.beq (oldest-waiter w x) 0))
  (simp only [serve-or hz]) (exact (inv-fire-edge res w _ h))
  (simp only [serve-or hz]) (exact (inv-source-upd w x keep hk h)))

(a/theorem t-post-inv [w :- World, x :- Nat, v :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-post w x v))) true))
  (intro h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-post hs refuse]) (exact h)
  (cases hg (open-kind sk-mailbox s))
  (simp only [t-post hs hg refuse]) (exact h)
  (simp only [t-post hs hg accept post-raw])
  (exact (inv-serve-or _ x _ (source-enqueue v) (source-enqueue-id v) (inv-source-upd w x source-bump source-bump-id h))))

(a/theorem t-post-refuse [w :- World, x :- Nat, v :- Nat]
  (=> (= (:accepted (t-post w x v)) false) (= (:world (t-post w x v)) w))
  (intro ha)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-post hs refuse])
  (cases hg (open-kind sk-mailbox s))
  (simp only [t-post hs hg refuse])
  (simp [t-post hs hg accept] at ha))

(a/theorem t-release-inv [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-release w x))) true))
  (intro h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-release hs refuse]) (exact h)
  (cases hg (open-kind sk-semaphore s))
  (simp only [t-release hs hg refuse]) (exact h)
  (simp only [t-release hs hg accept release-raw])
  (exact (inv-serve-or _ x _ source-permit source-permit-id (inv-source-upd w x source-bump source-bump-id h))))

(a/theorem t-release-refuse [w :- World, x :- Nat]
  (=> (= (:accepted (t-release w x)) false) (= (:world (t-release w x)) w))
  (intro ha)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-release hs refuse])
  (cases hg (open-kind sk-semaphore s))
  (simp only [t-release hs hg refuse])
  (simp [t-release hs hg accept] at ha))

;; ---- take(X) (§4.3; acquire is a take on a semaphore, as the engine logs it): a body effect
;; of a normal run (B8: a cleanup slice cannot park), on a mailbox or semaphore. It always
;; allocates two ids, A = fresh and its wait edge E = fresh + 1 (as the engine). Available
;; (a queued message / a permit, also on a closed source, Z#57): consumed at once (version + 1),
;; nothing kept, the run keeps its slice. Closed with nothing left (Z#57): fails at once with
;; err ::closed (the run continues through its error continuation, opaque here): the same
;; commit as the available path without the consumption (`take-now`, `source-consume` leaves
;; the row unchanged; no version step, as the engine). Otherwise (open, nothing available)
;; A {one, slot 0, cont k} with the wait edge E on X (at = effect-index); the run parks.
(a/defn take-ready [s :- SourceRow] Bool (Bool.or (src-available s) (Bool.not (:open s))))
(a/defn takeable [s :- SourceRow] Bool
  (Bool.or (Nat.beq (:kind s) sk-mailbox) (Nat.beq (:kind s) sk-semaphore)))
(a/defn run-tick-park [r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) act-parked (:mode r) false
             (+ (:effect-index r) 1) (:finalizers r) (:resources r)))
(a/theorem run-tick-park-id [r :- RunRow] (= (run-id (run-tick-park r)) (run-id r)) (rfl))
(a/defn take-act [w :- World, r :- RunRow, k :- Nat] ActRow
  (ActRow.mk (:next-id w) (:id r) am-one (List.cons Member (Member.mk (+ (:next-id w) 1) 0) (List.nil Member))
             (List.cons RunResult none-result (List.nil RunResult)) 1 k (List.nil Nat)))
(a/defn take-edge [r :- RunRow, a :- Nat, x :- Nat] EdgeRow
  (EdgeRow.mk 0 ek-wait a x cont-restart (:effect-index r) ph-armed false false 0 false 0 0))
(a/defn take-park [w :- World, r :- RunRow, x :- Nat, k :- Nat] World
  (run-upd (insert-edge-checked (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x)) (:id r) run-tick-park))
(a/defn take-now [w :- World, r :- RunRow, x :- Nat] World
  (bump (bump (run-upd (source-upd w x source-consume) (:id r) run-tick))))
(a/defn t-take [w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (match (source-find w x)
                [none (refuse w)]
                [(some s) (if (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (takeable s)))
                              (if (take-ready s) (accept (take-now w r x)) (accept (take-park w r x k)))
                              (refuse w))])]))

(a/theorem inv-take-park [w :- World, r :- RunRow, x :- Nat, k :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (take-park w r x k)) true))
  (intro h)
  (simp only [take-park])
  (exact (inv-run-upd _ (:id r) run-tick-park run-tick-park-id
           (inv-insert-edge-checked _ _ (inv-act-ins-fresh w (take-act w r k) (rfl) h)))))

(a/theorem inv-take-now [w :- World, r :- RunRow, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (take-now w r x)) true))
  (intro h)
  (simp only [take-now])
  (exact (inv-bump _ (inv-bump _ (inv-run-upd _ (:id r) run-tick run-tick-run-id
                                   (inv-source-upd w x source-consume source-consume-id h))))))

(a/theorem t-take-inv [w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-take w st x k fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-take ht refuse]) (exact h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-take ht hs refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (takeable s))))
  (simp only [t-take ht hs hg refuse]) (exact h)
  (cases hv (take-ready s))
  (simp only [t-take ht hs hg hv accept]) (exact (inv-take-park w r x k h))
  (simp only [t-take ht hs hg hv accept]) (exact (inv-take-now w r x h)))

(a/theorem t-take-refuse [w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (:accepted (t-take w st x k fresh)) false) (= (:world (t-take w st x k fresh)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-take ht refuse])
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-take ht hs refuse])
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (takeable s))))
  (simp only [t-take ht hs hg refuse])
  (cases hv (take-ready s))
  (all_goals (simp [t-take ht hs hg hv accept] at ha)))

(a/theorem t-take-l4 [w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (run-tok-ok w st) false) (= (:world (t-take w st x k fresh)) w))
  (intro hf) (simp only [t-take (run-tok-none w st hf) refuse]))

;; ---- T17 arm (Z#55): a resource effect (`offload f`, `sleep`) is ONE body effect
;; `arm st kind k fresh` of a normal run (B8/Z#40: a cleanup slice cannot park): the armed
;; resource Z = fresh (owned by the run, at = effect-index, step.clj `arm-raw`), then a `one`
;; activation A = fresh + 1 (cont k) over Z's wait edge E = fresh + 2 (at = the same index), and
;; the run parks (`take-park` on the armed row); effect-index advances once. kind: timer (0) or
;; offload (2), the engine's `:timer`/`:offload`. T18 fires E (T9 fills A, the run resumes); T14
;; removes A with E and puts Z in cancelling; T15 acknowledges Z any time it has no edge.
(a/defn arm-kind-ok [kind :- Nat] Bool (Bool.or (Nat.beq kind rk-timer) (Nat.beq kind rk-offload)))
(a/defn arm-park [w :- World, r :- RunRow, kind :- Nat, k :- Nat] World
  (take-park (arm-raw w r kind) (run-arm (:next-id w) r) (:next-id w) k))
(a/defn t17-arm [w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (if (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind)))
                  (accept (arm-park w r kind k))
                  (refuse w))]))

(a/theorem inv-arm-park [w :- World, r :- RunRow, kind :- Nat, k :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (arm-park w r kind k)) true))
  (intro h)
  (simp only [arm-park])
  (exact (inv-take-park _ (run-arm (:next-id w) r) (:next-id w) k (inv-arm-raw w r kind h))))

(a/theorem t17-inv [w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t17-arm w st kind k fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t17-arm ht refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind))))
  (simp only [t17-arm ht hg refuse]) (exact h)
  (simp only [t17-arm ht hg accept]) (exact (inv-arm-park w r kind k h)))

(a/theorem t17-refuse [w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (:accepted (t17-arm w st kind k fresh)) false) (= (:world (t17-arm w st kind k fresh)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t17-arm ht refuse])
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind))))
  (simp only [t17-arm ht hg refuse])
  (simp [t17-arm ht hg accept] at ha))

(a/theorem t17-l4 [w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (run-tok-ok w st) false) (= (:world (t17-arm w st kind k fresh)) w))
  (intro hf) (simp only [t17-arm (run-tok-none w st hf) refuse]))

;; ---- finally regions (B3). `finally-enter st`: a normal run opens a region (innermost first,
;; at = effect-index; the engine holds its refs implicitly, so refs = []);
;; B8: a cleanup slice adds none. `finally-exit st`: the head region closes. For an unwinding
;; run this ends its cleanup slice (B8: a single slice per finalizer): slice := false, then T13
;; (`retire-full`). Neither is an effect: effect-index is unchanged (engine items
;; `[:finally-enter st]`, `[:finally-exit st]`).
(a/defn run-fin-push [fz :- Finalizer, r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) (:act r) (:mode r) (:slice r)
             (:effect-index r) (List.cons Finalizer fz (:finalizers r)) (:resources r)))
(a/defn fins-tail [fs :- (List Finalizer)] (List Finalizer) (match fs [nil (List.nil Finalizer)] [(cons h t) t]))
(a/defn run-fin-pop [r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) (:act r) (:mode r) (:slice r)
             (:effect-index r) (fins-tail (:finalizers r)) (:resources r)))
(a/defn run-fin-pop-end [r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) (:act r) (:mode r) false
             (:effect-index r) (fins-tail (:finalizers r)) (:resources r)))
(a/theorem run-fin-push-id [fz :- Finalizer, r :- RunRow] (= (run-id (run-fin-push fz r)) (run-id r)) (rfl))
(a/theorem run-fin-pop-id [r :- RunRow] (= (run-id (run-fin-pop r)) (run-id r)) (rfl))
(a/theorem run-fin-pop-end-id [r :- RunRow] (= (run-id (run-fin-pop-end r)) (run-id r)) (rfl))

(a/defn t-finally-enter [w :- World, st :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (if (run-normal r)
                  (accept (run-upd w (:id r) (run-fin-push (Finalizer.mk 0 (:effect-index r) (List.nil Nat)))))
                  (refuse w))]))
(a/defn run-unwinding [r :- RunRow] Bool (Nat.beq (:mode r) mode-unwinding))
(a/defn t-finally-exit [w :- World, st :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (if (fins-empty (:finalizers r)) (refuse w) (accept (run-upd w (:id r) run-fin-pop)))]))

;; ---- slice-exit r (Z#35): the slice of a cancelled run returns. A cleanup slice runs the
;; whole finally chain (each region's exit a `finally-exit`, committed at the block's start, so
;; the outermost block still runs in the slice after the last exit); when the slice returns,
;; R (done, holding the slice, no open region) releases it and T13 retires it. The engine logs
;; it since Z#49 (older logs: the oracle inserts it when the projection shows the slice gone).
;; `run-fin-pop-end` on an empty region list only clears the slice.
(a/defn exit-ready [r :- RunRow] Bool
  (Bool.and (Nat.beq (:act r) act-done) (Bool.and (:slice r) (fins-empty (:finalizers r)))))
(a/defn t-slice-exit [w :- World, rid :- Nat] Outcome
  (match (run-find w rid)
    [none (refuse w)]
    [(some r) (if (exit-ready r) (accept (retire-full (run-upd w rid run-fin-pop-end) rid)) (refuse w))]))

(a/theorem t-finally-enter-inv [w :- World, st :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-finally-enter w st))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-enter ht refuse]) (exact h)
  (cases hg (run-normal r))
  (simp only [t-finally-enter ht hg refuse]) (exact h)
  (simp only [t-finally-enter ht hg accept]) (exact (inv-run-upd w (:id r) _ (run-fin-push-id _) h)))

(a/theorem t-finally-enter-refuse [w :- World, st :- Nat]
  (=> (= (:accepted (t-finally-enter w st)) false) (= (:world (t-finally-enter w st)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-enter ht refuse])
  (cases hg (run-normal r))
  (simp only [t-finally-enter ht hg refuse])
  (simp [t-finally-enter ht hg accept] at ha))

(a/theorem t-finally-enter-l4 [w :- World, st :- Nat]
  (=> (= (run-tok-ok w st) false) (= (:world (t-finally-enter w st)) w))
  (intro hf) (simp only [t-finally-enter (run-tok-none w st hf) refuse]))

(a/theorem t-finally-exit-inv [w :- World, st :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-finally-exit w st))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-exit ht refuse]) (exact h)
  (cases he (fins-empty (:finalizers r)))
  (case [true] (simp only [t-finally-exit ht he refuse]) (exact h))
  (case [false] (simp only [t-finally-exit ht he accept]) (exact (inv-run-upd w (:id r) run-fin-pop run-fin-pop-id h))))

(a/theorem t-finally-exit-refuse [w :- World, st :- Nat]
  (=> (= (:accepted (t-finally-exit w st)) false) (= (:world (t-finally-exit w st)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-exit ht refuse])
  (cases he (fins-empty (:finalizers r)))
  (case [true] (simp only [t-finally-exit ht he refuse]))
  (case [false] (simp [t-finally-exit ht he accept] at ha)))

(a/theorem t-slice-exit-inv [w :- World, rid :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-slice-exit w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-slice-exit hf refuse]) (exact h)
  (cases hg (exit-ready r))
  (simp only [t-slice-exit hf hg refuse]) (exact h)
  (simp only [t-slice-exit hf hg accept retire-full])
  (exact (inv-run-cascade _ _ (inv-run-upd w rid run-fin-pop-end run-fin-pop-end-id h))))

(a/theorem t-slice-exit-refuse [w :- World, rid :- Nat]
  (=> (= (:accepted (t-slice-exit w rid)) false) (= (:world (t-slice-exit w rid)) w))
  (intro ha)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-slice-exit hf refuse])
  (cases hg (exit-ready r))
  (simp only [t-slice-exit hf hg refuse])
  (simp [t-slice-exit hf hg accept] at ha))

(a/theorem t-finally-exit-l4 [w :- World, st :- Nat]
  (=> (= (run-tok-ok w st) false) (= (:world (t-finally-exit w st)) w))
  (intro hf) (simp only [t-finally-exit (run-tok-none w st hf) refuse]))

;; ---- finalize R (B3, B8): the scheduling choice for a cleanup slice. R is done and unwinding
;; with an open finally region, holds no slice, and no run holds one (D0): R gets the slice;
;; its token is then valid for the head finalizer's cleanup slice (§2), which may write,
;; deliver, post, release and arm, and ends with `finally-exit` (B8: it cannot park, spawn or
;; create computations; await/take/complete need a normal run, spawn/create-comp are refused
;; in raw0)
(a/defn cleanup-ready [w :- World, r :- RunRow] Bool
  (Bool.and (Nat.beq (:act r) act-done)
   (Bool.and (run-unwinding r)
    (Bool.and (Bool.not (fins-empty (:finalizers r)))
     (Bool.and (Bool.not (:slice r)) (Bool.not (tbl-any run-slice (:runs w))))))))
(a/defn t-finalize [w :- World, rid :- Nat] Outcome
  (match (run-find w rid)
    [none (refuse w)]
    [(some r) (if (cleanup-ready w r) (accept (run-upd w rid run-enter-row)) (refuse w))]))

(a/theorem t-finalize-inv [w :- World, rid :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-finalize w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-finalize hf refuse]) (exact h)
  (cases hg (cleanup-ready w r))
  (simp only [t-finalize hf hg refuse]) (exact h)
  (simp only [t-finalize hf hg accept]) (exact (inv-run-upd w rid run-enter-row run-enter-row-id h)))

(a/theorem t-finalize-refuse [w :- World, rid :- Nat]
  (=> (= (:accepted (t-finalize w rid)) false) (= (:world (t-finalize w rid)) w))
  (intro ha)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-finalize hf refuse])
  (cases hg (cleanup-ready w r))
  (simp only [t-finalize hf hg refuse])
  (simp [t-finalize hf hg accept] at ha))

;; ---- cancel R (T14 from the host on a task, engine `cancel-task!` logs the task's run): R
;; exists, is not done, is a task's run and holds no slice (D0: host items run between
;; slices; reading B19). An ordinary cancel (debtor side included), cascading.
(a/defn host-cancel-ok [w :- World, r :- RunRow] Bool
  (Bool.and (run-alive r) (Bool.and (Bool.not (:slice r)) (task-has w (:of r)))))
(a/defn t-cancel [w :- World, rid :- Nat] Outcome
  (match (run-find w rid)
    [none (refuse w)]
    [(some r) (if (host-cancel-ok w r) (t14-cancel w rid false) (refuse w))]))

(a/theorem t-cancel-inv [w :- World, rid :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-cancel w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-cancel hf refuse]) (exact h)
  (cases hg (host-cancel-ok w r))
  (simp only [t-cancel hf hg refuse]) (exact h)
  (simp only [t-cancel hf hg]) (exact (t14-inv w rid false h)))

(a/theorem t-cancel-refuse [w :- World, rid :- Nat]
  (=> (= (:accepted (t-cancel w rid)) false) (= (:world (t-cancel w rid)) w))
  (intro ha)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-cancel hf refuse])
  (cases hg (host-cancel-ok w r))
  (simp only [t-cancel hf hg refuse])
  (simp only [t-cancel hf hg] at ha) (simp only [t-cancel hf hg]) (exact (t14-refuse w rid false ha)))

;; ---- open-scope st s / close-scope s (T16, with-scope): open allocates the explicit scope
;; s = fresh as a child of the run's current scope (a body effect of a normal run; not an
;; effect index step, as the engine); close is T16 on an explicit scope (the engine logs it
;; without a token at the end of with-scope; closing a closed scope repeats the cascade)
;; the run's current scope must exist (it always does: a run's scope exists, I1; the guard keeps
;; the new scope's parent existing without that invariant, literal I1 proof spindel.v2.i1)
(a/defn open-ok [w :- World, r :- RunRow] Bool (Bool.and (run-normal r) (scope-has w (cur-scope w r))))
(a/defn t-open-scope [w :- World, st :- Nat, s :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (if (Bool.and (Nat.beq s (:next-id w)) (open-ok w r))
                  (accept (bump (scope-ins w (ScopeRow.mk s (cur-scope w r) scope-explicit true))))
                  (refuse w))]))
(a/defn scope-explicit-at [w :- World, s :- Nat] Bool
  (match (scope-find w s) [none false] [(some sc) (Nat.beq (:kind sc) scope-explicit)]))
(a/defn t-close-scope [w :- World, s :- Nat] Outcome
  (if (scope-explicit-at w s) (t16-close-scope w s) (refuse w)))

(a/theorem t-open-scope-inv [w :- World, st :- Nat, s :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-open-scope w st s))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-open-scope ht refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq s (:next-id w)) (open-ok w r)))
  (simp only [t-open-scope ht hg refuse]) (exact h)
  (have hs (= s (:next-id w))) (simp only [Bool.and_eq_true Nat.beq_eq] at hg) (exact (And.left hg))
  (simp only [t-open-scope ht hg accept])
  (exact (inv-scope-ins-fresh w (ScopeRow.mk s (cur-scope w r) scope-explicit true) hs h)))

(a/theorem t-open-scope-refuse [w :- World, st :- Nat, s :- Nat]
  (=> (= (:accepted (t-open-scope w st s)) false) (= (:world (t-open-scope w st s)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-open-scope ht refuse])
  (cases hg (Bool.and (Nat.beq s (:next-id w)) (open-ok w r)))
  (simp only [t-open-scope ht hg refuse])
  (simp [t-open-scope ht hg accept] at ha))

(a/theorem t-open-scope-l4 [w :- World, st :- Nat, s :- Nat]
  (=> (= (run-tok-ok w st) false) (= (:world (t-open-scope w st s)) w))
  (intro hf) (simp only [t-open-scope (run-tok-none w st hf) refuse]))

(a/theorem t-close-scope-inv [w :- World, s :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-close-scope w s))) true))
  (intro h)
  (cases hg (scope-explicit-at w s))
  (simp only [t-close-scope hg refuse]) (exact h)
  (simp only [t-close-scope hg]) (exact (t16-inv w s h)))

(a/theorem t-close-scope-refuse [w :- World, s :- Nat]
  (=> (= (:accepted (t-close-scope w s)) false) (= (:world (t-close-scope w s)) w))
  (intro ha)
  (cases hg (scope-explicit-at w s))
  (simp only [t-close-scope hg refuse])
  (simp only [t-close-scope hg] at ha) (simp only [t-close-scope hg]) (exact (t16-refuse w s ha)))

;; ---- detach k s (Q10, §5.2): a task that has not completed and is owned by a scope is
;; re-owned to the open scope s (it outlives its creator), and its run scope is re-parented
;; under s (Z#41, Z#26); the old owner's subtree is then removed when it became empty (W#9;
;; engine `remove-scope-if-empty!`)
(a/defn task-set-owner [s :- Nat, t :- TaskRow] TaskRow
  (TaskRow.mk (:id t) s (:run t) (:result t) (:handles t) (:inputs t)))
(a/theorem task-set-owner-id [s :- Nat, t :- TaskRow] (= (task-id (task-set-owner s t)) (task-id t)) (rfl))
(a/defn scope-set-parent [p :- Nat, s :- ScopeRow] ScopeRow (ScopeRow.mk (:id s) p (:kind s) (:open s)))
(a/theorem scope-set-parent-id [p :- Nat, s :- ScopeRow] (= (scope-id (scope-set-parent p s)) (scope-id s)) (rfl))
(a/defn task-run-scope [w :- World, t :- TaskRow] Nat (match (run-find w (:run t)) [none 0] [(some r) (:scope r)]))
(a/defn detach-move [w :- World, k :- Nat, s :- Nat, rs :- Nat] World
  (scope-upd (task-upd w k (task-set-owner s)) rs (scope-set-parent s)))
(a/defn remove-empty-at [w :- World, o :- Nat] World (remove-if-empty w (scope-subtree w o)))
(a/defn detach-ok [w :- World, t :- TaskRow, s :- Nat] Bool
  (Bool.and (Nat.beq (:tag (:result t)) res-none) (Bool.and (scope-has w (:owner t)) (scope-open-at w s))))
(a/defn t-detach [w :- World, k :- Nat, s :- Nat] Outcome
  (match (task-find w k)
    [none (refuse w)]
    [(some t) (if (detach-ok w t s)
                  (accept (remove-empty-at (detach-move w k s (task-run-scope w t)) (:owner t)))
                  (refuse w))]))

(a/theorem t-detach-inv [w :- World, k :- Nat, s :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-detach w k s))) true))
  (intro h)
  (cases hf (task-find w k)) (case' [some t]) (case' [none])
  (simp only [t-detach hf refuse]) (exact h)
  (cases hg (detach-ok w t s))
  (simp only [t-detach hf hg refuse]) (exact h)
  (simp only [t-detach hf hg accept remove-empty-at detach-move])
  (exact (inv-remove-if-empty _ _ (inv-scope-upd _ _ (scope-set-parent s) (scope-set-parent-id s)
                                    (inv-task-upd w k (task-set-owner s) (task-set-owner-id s) h)))))

(a/theorem t-detach-refuse [w :- World, k :- Nat, s :- Nat]
  (=> (= (:accepted (t-detach w k s)) false) (= (:world (t-detach w k s)) w))
  (intro ha)
  (cases hf (task-find w k)) (case' [some t]) (case' [none])
  (simp only [t-detach hf refuse])
  (cases hg (detach-ok w t s))
  (simp only [t-detach hf hg refuse])
  (simp [t-detach hf hg accept] at ha))

;; ---- release-world (T21): released := true; the host-held roots are revoked: observe edges
;; and pending host waits are removed (their callbacks/promises get ::released, not state),
;; pins dropped, pending-activation abandoned; host admissions revoked: every handle count
;; becomes 0 (the released handles' operations fail; reading B20); then T16 on the root scope.
;; Rule R then reclaims every row except cleanup entries (L2: they retire through `finalize`
;; and resource acknowledgements). A second release is refused.
(a/defn not-host [e :- EdgeRow] Bool (Bool.not (host-cred e)))
(a/defn comp-h0 [c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) 0))
(a/defn task-h0 [t :- TaskRow] TaskRow (TaskRow.mk (:id t) (:owner t) (:run t) (:result t) 0 (:inputs t)))
(a/defn source-h0 [s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) (:owner s) (:kind s) (:state s) (:version s) (:open s) 0 (:queue s)))
(a/defn pub-h0 [p :- PubRow] PubRow (PubRow.mk (:id p) (:edge p) (:basis p) 0))
(a/theorem comp-h0-id [c :- CompRow] (= (comp-id (comp-h0 c)) (comp-id c)) (rfl))
(a/theorem comp-h0-pending [c :- CompRow] (= (:pending (comp-h0 c)) (:pending c)) (rfl))
(a/theorem task-h0-id [t :- TaskRow] (= (task-id (task-h0 t)) (task-id t)) (rfl))
(a/theorem source-h0-id [s :- SourceRow] (= (source-id (source-h0 s)) (source-id s)) (rfl))
(a/theorem pub-h0-id [p :- PubRow] (= (pub-id (pub-h0 p)) (pub-id p)) (rfl))
(a/defn comp-h0-at [w :- World, x :- Nat] World (comp-upd w x comp-h0))
(a/defn task-h0-at [w :- World, x :- Nat] World (task-upd w x task-h0))
(a/defn source-h0-at [w :- World, x :- Nat] World (source-upd w x source-h0))
(a/defn pub-h0-at [w :- World, x :- Nat] World (pub-upd w x pub-h0))
(a/defn zero-handles [w :- World] World
  (nat-fold pub-h0-at
    (nat-fold source-h0-at
      (nat-fold task-h0-at (nat-fold comp-h0-at w (tbl-ids comp-id (:comps w))) (tbl-ids task-id (:tasks w)))
      (tbl-ids source-id (:sources w)))
    (tbl-ids pub-id (:pubs w))))
(a/defn revoke-roots [w :- World] World
  (set-pending-act (set-pins (drop-edges (set-released w true) not-host) (List.nil Nat)) 0))
(a/defn release-world-raw [w :- World] World
  (run-cascade (zero-handles (revoke-roots w)) (List.cons Job (Job.jclose root-scope-id) (List.nil Job))))
(a/defn t-release-world [w :- World] Outcome
  (if (:released w) (refuse w) (accept (release-world-raw w))))

(a/theorem inv-zero-handles [w :- World]
  (=> (= (inv-sample w) true) (= (inv-sample (zero-handles w)) true))
  (intro h)
  (have hc (forall [w :- World, x :- Nat] (=> (= (inv-sample w) true) (= (inv-sample (comp-h0-at w x)) true))))
  (intros w2 x h2) (exact (inv-comp-upd w2 x comp-h0 comp-h0-id comp-h0-pending h2))
  (have ht (forall [w :- World, x :- Nat] (=> (= (inv-sample w) true) (= (inv-sample (task-h0-at w x)) true))))
  (intros w2 x h2) (exact (inv-task-upd w2 x task-h0 task-h0-id h2))
  (have hs (forall [w :- World, x :- Nat] (=> (= (inv-sample w) true) (= (inv-sample (source-h0-at w x)) true))))
  (intros w2 x h2) (exact (inv-source-upd w2 x source-h0 source-h0-id h2))
  (have hp (forall [w :- World, x :- Nat] (=> (= (inv-sample w) true) (= (inv-sample (pub-h0-at w x)) true))))
  (intros w2 x h2) (exact (inv-pub-upd w2 x pub-h0 pub-h0-id h2))
  (simp only [zero-handles])
  (exact (nat-fold-inv pub-h0-at hp _ _ (nat-fold-inv source-h0-at hs _ _
           (nat-fold-inv task-h0-at ht _ _ (nat-fold-inv comp-h0-at hc _ _ h))))))

(a/theorem inv-revoke-roots [w :- World]
  (=> (= (inv-sample w) true) (= (inv-sample (revoke-roots w)) true))
  (intro h)
  (simp only [revoke-roots])
  (exact (inv-set-pending-act _ 0 (inv-set-pins _ _ (inv-drop-edges _ not-host (inv-set-released w true h))))))

(a/theorem t-release-world-inv [w :- World]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t-release-world w))) true))
  (intro h)
  (cases hr (:released w))
  (simp only [t-release-world hr accept release-world-raw])
  (exact (inv-run-cascade _ _ (inv-zero-handles _ (inv-revoke-roots w h))))
  (simp only [t-release-world hr refuse]) (exact h))

(a/theorem t-release-world-refuse [w :- World]
  (=> (= (:accepted (t-release-world w)) false) (= (:world (t-release-world w)) w))
  (intro ha)
  (cases hr (:released w))
  (simp [t-release-world hr accept] at ha)
  (simp only [t-release-world hr refuse]))

;; ---- T1 in a body (engine `[:create-source st kind v fresh]`): in a computation run, `fresh`
;; naming a source of C's basis or adoption basis adopts it (creation order; no allocation, the
;; kind must match; it moves to the basis at the new site, like a re-spawn); otherwise fresh =
;; next-id creates it, owned by the computation, or in a task run by the run's current scope
;; (reading B22), recorded in a computation's basis. Effect tick either way.
(a/defn src-owner-cur [w :- World, r :- RunRow] Nat (if (in-comp w r) (:of r) (cur-scope w r)))
(a/defn readopt-source [w :- World, r :- RunRow, x :- Nat] (Option SourceRow)
  (match (comp-find w (:of r))
    [none (Option.none SourceRow)]
    [(some c) (if (reach-mem x (nat-app (created-ids (:basis c)) (created-ids (:adopt-basis c))))
                  (source-find w x) (Option.none SourceRow))]))
(a/defn create-source-cur [w :- World, r :- RunRow, kind :- Nat, v :- Nat] World
  (run-upd (record-basis (bump (source-ins w (new-source (:next-id w) (src-owner-cur w r) kind v))) r (:next-id w))
           (:id r) run-tick))
(a/defn t1-full [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (match (readopt-source w r fresh)
                [none (if (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind))
                          (accept (create-source-cur w r kind v)) (refuse w))]
                [(some x) (if (Nat.beq (:kind x) kind) (accept (respawn-raw w r fresh)) (refuse w))])]))

(a/theorem inv-create-source-cur [w :- World, r :- RunRow, kind :- Nat, v :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (create-source-cur w r kind v)) true))
  (intro h)
  (simp only [create-source-cur])
  (exact (inv-run-upd _ (:id r) run-tick run-tick-run-id
           (inv-record-basis _ r (:next-id w)
             (inv-source-ins-fresh w (new-source (:next-id w) (src-owner-cur w r) kind v) (rfl) h)))))

(a/theorem t1-full-inv [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t1-full w st kind v fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t1-full ht refuse]) (exact h)
  (cases ho (readopt-source w r fresh))
  (case [none]
    (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind)))
    (case [false] (simp only [t1-full ht ho hg refuse]) (exact h))
    (case [true] (simp only [t1-full ht ho hg accept]) (exact (inv-create-source-cur w r kind v h))))
  (case [some x]
    (cases hk (Nat.beq (:kind x) kind))
    (case [false] (simp only [t1-full ht ho hk refuse]) (exact h))
    (case [true]
      (simp only [t1-full ht ho hk accept respawn-raw])
      (exact (inv-run-upd _ (:id r) run-tick run-tick-run-id
               (inv-comp-upd w (:of r) _ (comp-rebasis-id _) (comp-rebasis-pending _) h))))))

(a/theorem t1-full-refuse [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (:accepted (t1-full w st kind v fresh)) false) (= (:world (t1-full w st kind v fresh)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t1-full ht refuse])
  (cases ho (readopt-source w r fresh))
  (case [none]
    (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind)))
    (case [false] (simp only [t1-full ht ho hg refuse]))
    (case [true] (simp [t1-full ht ho hg accept] at ha)))
  (case [some x]
    (cases hk (Nat.beq (:kind x) kind))
    (case [false] (simp only [t1-full ht ho hk refuse]))
    (case [true] (simp [t1-full ht ho hk accept] at ha))))

;; ---- B8 for spawn and create-comp: refused in a cleanup slice (a valid token of an
;; unwinding run)
(a/defn in-cleanup [w :- World, st :- Nat] Bool (opt-test run-unwinding (tok-run w st)))
;; I8 (spindel.v2.i8): a task run spawns a task / creates a source owned by its current scope; refused
;; when that scope is not open. A reachable-equivalent guard (an alive task run's current scope is
;; open: tripwire `cur-open-ok` on the random drivers and the oracle; its proof is obligation P10) that
;; keeps I8's proof local: no new task or source is owned by a closed scope.
(a/defn run-cur-closed [w :- World, r :- RunRow] Bool
  (Bool.and (Bool.not (in-comp w r)) (Bool.not (scope-open-at w (cur-scope w r)))))
(a/defn cur-closed [w :- World, st :- Nat] Bool (opt-test (run-cur-closed w) (tok-run w st)))
(a/defn body-shut [w :- World, st :- Nat] Bool (Bool.or (in-cleanup w st) (cur-closed w st)))
;; Z#43: completion with open finally regions is refused (the CPS body cannot produce it)
(a/defn run-fins-open [r :- RunRow] Bool (Bool.not (fins-empty (:finalizers r))))
(a/defn fins-open [w :- World, st :- Nat] Bool (opt-test run-fins-open (tok-run w st)))
;; a result is ok v or err e (§2); a complete item carrying another tag (none) is malformed and
;; refused (found by the literal I10 proof: a task completed with result none keeps no run)
(a/defn res-tag-ok [tag :- Nat] Bool (Bool.or (Nat.beq tag res-ok) (Nat.beq tag res-err)))
(a/defn complete-refused [w :- World, st :- Nat, tag :- Nat] Bool
  (Bool.or (fins-open w st) (Bool.not (res-tag-ok tag))))

;; Z#54 (§4.3, operation by kind): a mailbox or semaphore is only taken (`take`, a wait edge):
;; `await` with such a member (one, all or any; the engine logs `await` on a mailbox as `take`)
;; and the host read (T22) of one fail with no commit (refused here), so no dep edge ever has a
;; mailbox or semaphore debtor. `track` on another kind than signal/cell is T7's refusal.
(a/defn src-consuming [s :- SourceRow] Bool
  (Bool.or (Nat.beq (:kind s) sk-mailbox) (Nat.beq (:kind s) sk-semaphore)))
(a/defn deb-consuming [w :- World, d :- Nat] Bool (opt-test src-consuming (source-find w d)))
(a/defn await-kind-bad [w :- World, ds :- (List Nat)] Bool (tbl-any (deb-consuming w) ds))

;; ===========================================================================
;; Part G. The step: raw transition (every item), then Rule R
;; ===========================================================================

(a/defn raw0 [w :- World, it :- Item] Outcome
  (match it
    [(create-source st kind v fresh) (if (body-shut w st) (refuse w) (t1-full w st kind v fresh))]
    [(create-source-top scope kind v fresh) (t1-create-source-top w scope kind v fresh)]
    [(write x v) (t2-write w x v)]
    [(track st x k fresh) (if (in-cleanup w st) (refuse w) (t7-track w st x k fresh))]
    [(observe d cb fresh) (t8-full w d cb fresh)]
    [(unobserve e) (t8-unobserve w e)]
    [(fire e tag val) (t9-fire w e tag val)]
    [(resource-ack z) (t15-full w z)]
    [(arm st kind k fresh) (if (in-cleanup w st) (refuse w) (t17-arm w st kind k fresh))]
    [(resource-fire z tag val) (t18-resource-fire w z tag val)]
    [(handle-drop x) (t19-handle-drop w x)]
    [(pin x) (t20-pin w x)]
    [(unpin x) (t20-unpin w x)]
    [(create-comp st c i b) (if (in-cleanup w st) (refuse w) (t3-create w st c i b))]
    [(create-comp-top sc c i b) (t3-create-top w sc c i b)]
    [(spawn st b fresh ins) (if (body-shut w st) (refuse w) (t4-spawn w st b fresh ins))]
    [(spawn-top sc b fresh ins) (t4-spawn-top w sc b fresh ins)]
    [(start c fresh) (t5-start w c fresh)]
    [(await st ds m k fresh mine) (if (await-kind-bad w ds) (refuse w) (t6-await w st ds m k fresh mine))]
    [(dispatch-comp c fresh) (t11-dispatch w c fresh)]
    [(complete st tag val) (if (complete-refused w st tag) (refuse w) (t12-complete w st tag val))]
    [(schedule r) (t-schedule w r)]
    [(host-await d fresh) (if (deb-consuming w d) (refuse w) (t22-host-await w d fresh))]
    [(host-unawait e) (t22-host-unawait w e)]
    [(handle-new x) (t-handle-new w x)]
    [(deliver x v) (t-deliver w x v)]
    [(post x v) (t-post w x v)]
    [(take st x k fresh) (t-take w st x k fresh)]
    [(release x) (t-release w x)]
    [(finalize r) (t-finalize w r)]
    [(cancel r) (t-cancel w r)]
    [(release-world) (t-release-world w)]
    [(open-scope st s) (t-open-scope w st s)]
    [(close-scope s) (t-close-scope w s)]
    [(detach k s) (t-detach w k s)]
    [(finally-enter st) (t-finally-enter w st)]
    [(finally-exit st) (t-finally-exit w st)]
    [(slice-exit r) (t-slice-exit w r)]))

;; Z#56 (T21): a released world refuses the HOST's admissions (top-level creations, writes, observe,
;; pins, handles, host waits, source operations, cancel, close, detach), except while a run holds the
;; slice (Z#44: such items are that run's effects; a cleanup slice may still deliver, post, release,
;; write and close, Z#40). The scheduling choices, the cleanup slice items and resource completions
;; (fire, then ack: L2 joins) are no admissions.
(a/defn host-item [it :- Item] Bool
  (match it
    [(create-source st kind v fresh) false]
    [(create-source-top scope kind v fresh) true]
    [(write x v) true]
    [(track st x k fresh) false]
    [(observe d cb fresh) true]
    [(unobserve e) true]
    [(fire e tag val) false]
    [(resource-ack z) false]
    [(arm st kind k fresh) false]
    [(resource-fire z tag val) false]
    [(handle-drop x) true]
    [(pin x) true]
    [(unpin x) true]
    [(create-comp st c i b) false]
    [(create-comp-top sc c i b) true]
    [(spawn st b fresh ins) false]
    [(spawn-top sc b fresh ins) true]
    [(start c fresh) false]
    [(await st ds m k fresh mine) false]
    [(dispatch-comp c fresh) false]
    [(complete st tag val) false]
    [(schedule r) false]
    [(host-await d fresh) true]
    [(host-unawait e) true]
    [(handle-new x) true]
    [(deliver x v) true]
    [(post x v) true]
    [(take st x k fresh) false]
    [(release x) true]
    [(finalize r) false]
    [(cancel r) true]
    [(release-world) false]
    [(open-scope st s) false]
    [(close-scope s) true]
    [(detach k s) true]
    [(finally-enter st) false]
    [(finally-exit st) false]
    [(slice-exit r) false]))
(a/defn slice-held [w :- World] Bool (tbl-any run-slice (:runs w)))
(a/defn host-shut [w :- World, it :- Item] Bool
  (Bool.and (:released w) (Bool.and (host-item it) (Bool.not (slice-held w)))))
(a/defn raw0g [w :- World, it :- Item] Outcome (if (host-shut w it) (refuse w) (raw0 w it)))

;; after an accepted transition, the `any` losers are cancelled
(a/defn post [w :- World, o :- Outcome] Outcome (if (:accepted o) (accept (cancel-losers w (:world o))) o))
(a/defn raw [w :- World, it :- Item] Outcome (post w (raw0g w it)))

;; the item's validity token (§2): step's item-token-ok (with the Z#6 acknowledgement token)
(a/defn raw-token-ok [w :- World, it :- Item] Bool (item-token-ok w it))

;; an accepted raw outcome is followed by Rule R; a refusal is the input world
(a/defn finish [o :- Outcome] Outcome (if (:accepted o) (accept (rule-r (:world o))) o))
(a/defn world-step [w :- World, it :- Item] Outcome (finish (raw w it)))

(a/theorem raw0-inv [w :- World, it :- Item]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (raw0 w it))) true))
  (intro h)
  (cases it)
  (all_goals (simp only [raw0]))
  (rename_i st kind v fresh) (cases hc (body-shut w st))
  (simp only [hc]) (exact (t1-full-inv w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (t1-top-inv w _ _ _ _ h))
  (exact (t2-inv w _ _ h))
  (rename_i st x k fresh) (cases hc (in-cleanup w st))
  (simp only [hc]) (exact (t7-inv w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (t8-full-inv w _ _ _ h))
  (exact (t8-unobserve-inv w _ h))
  (exact (t9-inv w _ _ _ h))
  (exact (t15-full-inv w _ h))
  (rename_i st kind k fresh) (cases hc (in-cleanup w st))
  (simp only [hc]) (exact (t17-inv w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (t18-inv w _ _ _ h))
  (exact (t19-inv w _ h))
  (exact (t20-pin-inv w _ h))
  (exact (t20-unpin-inv w _ h))
  (rename_i st c i b) (cases hc (in-cleanup w st))
  (simp only [hc]) (exact (t3-inv w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (t3-top-inv w _ _ _ _ h))
  (rename_i st b fresh ins) (cases hc (body-shut w st))
  (simp only [hc]) (exact (t4-inv w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (t4-top-inv w _ _ _ _ h))
  (exact (t5-inv w _ _ h))
  (rename_i st ds m k fresh mine) (cases hc (await-kind-bad w ds))
  (simp only [hc]) (exact (t6-inv w _ _ _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (t11-inv w _ _ h))
  (rename_i st tag v) (cases hc (complete-refused w st tag))
  (simp only [hc]) (exact (t12-inv w _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (sched-inv w _ h))
  (rename_i d fresh) (cases hc (deb-consuming w d))
  (simp only [hc]) (exact (t22-inv w _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (t22-un-inv w _ h))
  (exact (t-handle-new-inv w _ h))
  (exact (t-deliver-inv w _ _ h))
  (exact (t-post-inv w _ _ h))
  (exact (t-take-inv w _ _ _ _ h))
  (exact (t-release-inv w _ h))
  (exact (t-finalize-inv w _ h))
  (exact (t-cancel-inv w _ h))
  (exact (t-release-world-inv w h))
  (exact (t-open-scope-inv w _ _ h))
  (exact (t-close-scope-inv w _ h))
  (exact (t-detach-inv w _ _ h))
  (exact (t-finally-enter-inv w _ h))
  (exact (t-finally-exit-inv w _ h))
  (exact (t-slice-exit-inv w _ h)))

(a/theorem raw0-refuse [w :- World, it :- Item]
  (=> (= (:accepted (raw0 w it)) false) (= (:world (raw0 w it)) w))
  (intro ha)
  (cases it)
  (all_goals (simp only [raw0] at ha))
  (all_goals (simp only [raw0]))
  (rename_i st kind v fresh) (cases hc (body-shut w st))
  (simp only [hc] at ha) (simp only [hc]) (exact (t1-full-refuse w _ _ _ _ ha))
  (simp only [hc refuse])
  (exact (t1-top-refuse w _ _ _ _ ha))
  (exact (t2-refuse w _ _ ha))
  (rename_i st x k fresh) (cases hc (in-cleanup w st))
  (simp only [hc] at ha) (simp only [hc]) (exact (t7-refuse w _ _ _ _ ha))
  (simp only [hc refuse])
  (exact (t8-full-refuse w _ _ _ ha))
  (exact (t8-unobserve-refuse w _ ha))
  (exact (t9-refuse w _ _ _ ha))
  (exact (t15-full-refuse w _ ha))
  (rename_i st kind k fresh) (cases hc (in-cleanup w st))
  (simp only [hc] at ha) (simp only [hc]) (exact (t17-refuse w _ _ _ _ ha))
  (simp only [hc refuse])
  (exact (t18-refuse w _ _ _ ha))
  (exact (t19-refuse w _ ha))
  (exact (t20-pin-refuse w _ ha))
  (exact (t20-unpin-refuse w _ ha))
  (rename_i st c i b) (cases hc (in-cleanup w st))
  (simp only [hc] at ha) (simp only [hc]) (exact (t3-refuse w _ _ _ _ ha))
  (simp only [hc refuse])
  (exact (t3-top-refuse w _ _ _ _ ha))
  (rename_i st b fresh ins) (cases hc (body-shut w st))
  (simp only [hc] at ha) (simp only [hc]) (exact (t4-refuse w _ _ _ _ ha))
  (simp only [hc refuse])
  (exact (t4-top-refuse w _ _ _ _ ha))
  (exact (t5-refuse w _ _ ha))
  (rename_i st ds m k fresh mine) (cases hc (await-kind-bad w ds))
  (simp only [hc] at ha) (simp only [hc]) (exact (t6-refuse w _ _ _ _ _ _ ha))
  (simp only [hc refuse])
  (exact (t11-refuse w _ _ ha))
  (rename_i st tag v) (cases hc (complete-refused w st tag))
  (simp only [hc] at ha) (simp only [hc]) (exact (t12-refuse w _ _ _ ha))
  (simp only [hc refuse])
  (exact (sched-refuse w _ ha))
  (rename_i d fresh) (cases hc (deb-consuming w d))
  (simp only [hc] at ha) (simp only [hc]) (exact (t22-refuse w _ _ ha))
  (simp only [hc refuse])
  (exact (t22-un-refuse w _ ha))
  (exact (t-handle-new-refuse w _ ha))
  (exact (t-deliver-refuse w _ _ ha))
  (exact (t-post-refuse w _ _ ha))
  (exact (t-take-refuse w _ _ _ _ ha))
  (exact (t-release-refuse w _ ha))
  (exact (t-finalize-refuse w _ ha))
  (exact (t-cancel-refuse w _ ha))
  (exact (t-release-world-refuse w ha))
  (exact (t-open-scope-refuse w _ _ ha))
  (exact (t-close-scope-refuse w _ ha))
  (exact (t-detach-refuse w _ _ ha))
  (exact (t-finally-enter-refuse w _ ha))
  (exact (t-finally-exit-refuse w _ ha))
  (exact (t-slice-exit-refuse w _ ha)))

(a/theorem inv-cancel-losers [w0 :- World, w1 :- World]
  (=> (= (inv-sample w1) true) (= (inv-sample (cancel-losers w0 w1)) true))
  (intro h) (exact (inv-run-cascade w1 _ h)))

;; a non-host item is never shut
(a/theorem raw0g-of [w :- World, it :- Item]
  (=> (= (host-item it) false) (= (raw0g w it) (raw0 w it)))
  (intro h)
  (cases hs (host-shut w it))
  (simp only [raw0g hs])
  (simp [host-shut h] at hs))

(a/theorem raw0g-inv [w :- World, it :- Item]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (raw0g w it))) true))
  (intro h)
  (cases hs (host-shut w it))
  (simp only [raw0g hs]) (exact (raw0-inv w it h))
  (simp only [raw0g hs refuse]) (exact h))

(a/theorem raw0g-refuse [w :- World, it :- Item]
  (=> (= (:accepted (raw0g w it)) false) (= (:world (raw0g w it)) w))
  (intro ha)
  (cases hs (host-shut w it))
  (simp only [raw0g hs] at ha) (simp only [raw0g hs]) (exact (raw0-refuse w it ha))
  (simp only [raw0g hs refuse]))

(a/theorem raw-inv [w :- World, it :- Item]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (raw w it))) true))
  (intro h)
  (have h0 := (raw0g-inv w it h))
  (cases ha (:accepted (raw0g w it)))
  (simp only [raw post ha]) (exact h0)
  (simp only [raw post ha accept]) (exact (inv-cancel-losers w _ h0)))

(a/theorem raw-refuse [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) false) (= (:world (raw w it)) w))
  (intro ha)
  (cases h0 (:accepted (raw0g w it)))
  (simp only [raw post h0]) (exact (raw0g-refuse w it h0))
  (simp [raw post h0 accept] at ha))

;; Z#10 / L4: an invalid token is a refusal
(a/theorem raw0-l4 [w :- World, it :- Item]
  (=> (= (raw-token-ok w it) false) (= (:accepted (raw0 w it)) false))
  (intro hg)
  (simp only [raw-token-ok] at hg)
  (cases it)
  (simp only [raw0 body-shut in-cleanup cur-closed opt-test t1-full (run-tok-none w _ hg) refuse Bool.or_false])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp only [raw0 in-cleanup opt-test t7-track (run-tok-none w _ hg) refuse])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp only [item-token-ok] at hg) (simp only [raw0 t9-fire hg refuse])
  (simp only [item-token-ok] at hg) (simp only [raw0 t15-full hg refuse])
  (simp only [raw0 in-cleanup opt-test t17-arm (run-tok-none w _ hg) refuse])
  (simp only [raw0 t18-resource-fire (res-tok-none w _ hg) refuse])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp only [raw0 in-cleanup opt-test t3-create (run-tok-none w _ hg) refuse])
  (simp [item-token-ok] at hg)
  (simp only [raw0 body-shut in-cleanup cur-closed opt-test t4-spawn (run-tok-none w _ hg) refuse Bool.or_false])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (rename_i st ds m k fresh mine) (cases hc (await-kind-bad w ds))
  (simp only [raw0 hc t6-await (run-tok-none w _ hg) refuse])
  (simp only [raw0 hc refuse])
  (simp [item-token-ok] at hg)
  (simp only [raw0 complete-refused fins-open opt-test t12-complete (run-tok-none w _ hg) refuse ite_self])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp only [raw0 t-take (run-tok-none w _ hg) refuse])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp only [raw0 t-open-scope (run-tok-none w _ hg) refuse])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp only [raw0 t-finally-enter (run-tok-none w _ hg) refuse])
  (simp only [raw0 t-finally-exit (run-tok-none w _ hg) refuse])
  (simp [item-token-ok] at hg))

(a/theorem raw-l4 [w :- World, it :- Item]
  (=> (= (raw-token-ok w it) false) (= (:accepted (raw w it)) false))
  (intro hg)
  (have h0 := (raw0-l4 w it hg))
  (have h1 (= (:accepted (raw0g w it)) false))
  (cases hs (host-shut w it))
  (simp only [raw0g hs]) (exact h0)
  (simp only [raw0g hs refuse])
  (simp only [raw post h1]))

(a/theorem outcome-eta [o :- Outcome] (= o (Outcome.mk (:world o) (:accepted o)))
  (cases o) (rfl))

(a/theorem step-refuse [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) false) (= (world-step w it) (refuse w)))
  (intro ha)
  (have ho := (outcome-eta (raw w it)))
  (rw [(raw-refuse w it ha)] at ho)
  (rw [ha] at ho)
  (simp only [world-step finish ha refuse])
  (exact ho))

;; L4 for the step: an invalid token is a refusal and leaves the world unchanged
(a/theorem step-l4 [w :- World, it :- Item]
  (=> (= (raw-token-ok w it) false) (= (world-step w it) (refuse w)))
  (intro hg) (exact (step-refuse w it (raw-l4 w it hg))))

(a/theorem step-accepted [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) true) (= (:world (world-step w it)) (rule-r (:world (raw w it)))))
  (intro ha) (simp only [world-step finish ha accept]))



(a/theorem step-inv [w :- World, it :- Item]
  (=> (= (inv-sample w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (inv-sample (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h)
  (have e2 := (step-accepted w it ha)) (rw [e2])
  (exact (inv-rule-r (:world (raw w it)) (raw-inv w it h) hs)))


;; I3 after the step: every row is live, storage, in a cleanup entry or admitted
(a/theorem step-i3 [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) true)
      (= (live-converged (normalize (rule-r-pre (:world (raw w it))))) true)
      (= (live-converged (rule-r (:world (raw w it)))) true)
      (= (tbl-all (keep-fn (:world (world-step w it))) (all-ids (:world (world-step w it)))) true))
  (intros ha hc hc2)
  (rw [(step-accepted w it ha)])
  (exact (rule-r-i3-step (:world (raw w it)) hc hc2)))

;; the step's world is normalized (no non-done run, no non-idle computation outside live)
(a/theorem step-normalized [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) true)
      (= (live-converged (normalize (rule-r-pre (:world (raw w it))))) true)
      (= (live-converged (rule-r (:world (raw w it)))) true)
      (= (normalized (normalize (rule-r-pre (:world (raw w it))))) true)
      (= (normalized (:world (world-step w it))) true))
  (intros ha hc hc2 hn)
  (rw [(step-accepted w it ha)])
  (exact (rule-r-normalized (:world (raw w it)) hc hc2 hn)))

;; I4 after the step: every active or parked run is in live(W)
(a/theorem step-i4 [w :- World, it :- Item, r :- RunRow]
  (=> (= (:accepted (raw w it)) true)
      (= (live-converged (normalize (rule-r-pre (:world (raw w it))))) true)
      (= (live-converged (rule-r (:world (raw w it)))) true)
      (= (normalized (normalize (rule-r-pre (:world (raw w it))))) true)
      (List.Mem r (:runs (:world (world-step w it))))
      (= (run-alive r) true)
      (= (in-live (:world (world-step w it)) (:id r)) true))
  (intros ha hc hc2 hn hm hr)
  (exact (normalized-runs (:world (world-step w it)) r (step-normalized w it ha hc hc2 hn) hm hr)))

;; ---- P1 (spindel.v2.retain/live-converged-all): the live worklist always converges, so the
;; step theorems hold without their live-converged hypotheses

;; I3 after every accepted step
(a/theorem step-i3-total [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) true)
      (= (tbl-all (keep-fn (:world (world-step w it))) (all-ids (:world (world-step w it)))) true))
  (intro ha)
  (exact (step-i3 w it ha (live-converged-all _) (live-converged-all _))))

(a/theorem step-normalized-total [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) true)
      (= (normalized (normalize (rule-r-pre (:world (raw w it))))) true)
      (= (normalized (:world (world-step w it))) true))
  (intros ha hn)
  (exact (step-normalized w it ha (live-converged-all _) (live-converged-all _) hn)))

;; I4 after every accepted step whose normalization reports `normalized`
(a/theorem step-i4-total [w :- World, it :- Item, r :- RunRow]
  (=> (= (:accepted (raw w it)) true)
      (= (normalized (normalize (rule-r-pre (:world (raw w it))))) true)
      (List.Mem r (:runs (:world (world-step w it))))
      (= (run-alive r) true)
      (= (in-live (:world (world-step w it)) (:id r)) true))
  (intros ha hn hm hr)
  (exact (step-i4 w it r ha (live-converged-all _) (live-converged-all _) hn hm hr)))
