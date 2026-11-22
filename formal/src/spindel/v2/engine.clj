(ns spindel.v2.engine
  "Layer-1 transitions that create runs and wire activations (spec v1.5.1 §5.1) and the
  model's step `world-step w item = then-rule-r (raw w item)`: an accepted raw outcome is followed
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
       (Z#29), and the `any`/`all` loser cancel (`cancel-losers`, run after every accepted raw
       item; Z#61 fail-fast `all`)
    F2 source operations (§4.3: deliver, post, take = take/acquire, release), finally regions
       (B3: finally-enter/-exit), the `finalize R` cleanup slice (B8), host cancel (T14),
       open/close-scope (T16), detach (Q10), release-world (T21), B8 refusals (`in-cleanup`)
    F3 C0 async sequences (§4.3 link/stream, §8.1): create-link (a pull head, owned by the root
       scope; in a computation a basis creation, adopted like a re-spawn), streams as a T1 kind
       (`t1-create-source`/`t1-create-source-top`: the stream and its first tail link S + 1), link-demand (the
       realizer task in the root scope, handles 0; T14/T21 clear `rtask` at the realizer's cancel;
       `realizer-live` also checks it), T8 observe on a stream refused (`t8-observe`),
       link-realize (tag 1 next pull link, 0 end, 2 memoized error), append, close; built from
       source-ins, source-upd and rule.clj's `realize-link` (= deliver with a result,
       `deliver-raw-res`). T16's close-source ends a stream's tail first (`end-stream`), a
       demotion closes the streams of the basis (`end-basis`); a stream is not awaitable
       (`source-consuming`)
    G  `transition` (every Item), `raw` = loser cancel after transition, `world-step`, and the theorems
  Also: I12 ranks (`raise-run`: height adjustment before every new comp-comp dep edge of T6
  and of a reactivation; `ranks-ok`, checked by the tests after every step) and Blocked as
  the least fixpoint (`blocked-set` = spindel.v2.reach's Derive via `derive-run-l`;
  `blocked-sound`, `blocked-complete`).

  Theorems (per transition: -inv = well-formed preserved, -refuse = a refusal leaves the world
  unchanged; L4 for the whole step):
    well-formed-t3-create/-refuse, well-formed-t3-create-top/-refuse, t4-*, t4-top-*, t5-*, t6-*, t11-*, t12-*, t22-*,
    t22-un-*, t8-full-*, sched-*, t-handle-new-*; t-deliver-*, t-post-*, t-take-* (+ -l4),
    t-release-*, t-finalize-*, t-cancel-*, t-release-world-*, t-open-scope-* (+ -l4),
    t-close-scope-*, t-detach-*, t-finally-enter-* / t-finally-exit-* (+ -l4), t-slice-exit-*
    (-inv, -refuse); well-formed-deliver-fire; C0: t-create-link-*, t-create-link-top-*, t1-stream-*,
    t1-body-*, t1-top-full-*, t-link-demand-*, t-link-realize-*, t-append-*, t-close-* (-inv, -refuse);
    well-formed-raise-loop, well-formed-raise-for, blocked-sound, blocked-complete; well-formed-transition, transition-refuse, transition-l4 (every
    constructor); well-formed-raw, raw-refuse, raw-l4 (with the loser cancel);
    step-refuse, step-l4 (invalid token -> (refuse w)), step-accepted,
    step-well-formed     well-formed w, rule-r-safe raw-world -> well-formed (world-step w it)
    step-i3      accepted, live converged before/after the last round's filter -> I3
    step-normalized, step-i4   ... and normalized (normalize (rule-r-last-input raw-world)) -> the
                 step's world is normalized and every non-done run is in its live set (I4)
  Premises of these per-step theorems: the flags of rule.clj, plus `settle-done`/`finalize-done` for the
  worklists. All are discharged for every step: live-converged (P1, spindel.v2.retain
  `live-converged-all`), normalized (P2, spindel.v2.progress.casc `rule-r-normalized-ok`), rule-r-safe /
  filter-safe (P3, spindel.v2.inv.base `step-rule-r-safe`), cascade-done (P4, spindel.v2.progress.casc
  `cascade-done-ok`), settle-done (spindel.v2.progress.l5 `settle-done-ok`); finalize-done holds trivially (comp-final
  is false, so the worklist is [d]). The forms without premises are the bundle theorems
  (`step-well-formed-total`, spindel.v2.inv.base; `inv-step`, spindel.v2.top). The tests still check the flags.

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
        (a cycle through validity, not expected) is dropped together with its raise (`react-add`);
        `ranks-ok` is preserved by every step (spindel.v2.inv.rank-step `step-ranks`).
    B8. T6 debtors: in a computation run a dep edge for computation, task and source
        debtors, a wait edge for a resource (Z#6); in a task run wait edges. Fast-ready: a
        live (or valid idle) computation, a completed task, a closed source, a delivered
        deferred, a fired resource, and (Z#31) a signal or cell, read at once (in a
        computation through its dep edge, like track; in a task as a snapshot whose wait edge
        goes with the resumed activation); an open deferred waits. Z#54: a mailbox or
        semaphore member is refused (`await-kind-refused` in transition; the engine logs an await on a
        mailbox as `take`), so no dep edge has a mailbox or semaphore debtor.
    B9. `any` losers (engine `cancel-losers!`): when an `any` activation of a TASK run
        resolved, or an `all` one failed fast at its first err slot (Z#61), and its run is not
        done, the tasks of `mine` (the activation's `spawned`) that are owned by the run's
        scope, still run and have no other out-edge are cancelled (ordinary cancel).
    B10. T22: the host-wait edge is consumed by the debtor's settle, a task's completion, a
        resource fire, at once when the debtor is fast-ready, or by the close of its source
        (Z#53, rule.clj `wake-closed`). Z#54: a host read of a mailbox or semaphore is refused
        (`deb-consuming` in transition).
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
    B18. finally-enter/-exit/-leave are body items (engine `[:finally-enter st]`/`[:finally-exit st]`,
        C1 `[:finally-leave st]`: `finally-exit` turns the head region into a running clause, which
        `finally-leave` pops; between them a normal run's suspending effects are refused, B8).
        Regions open only in normal runs (B8: no finalizer adds one); the engine holds the
        regions' refs implicitly (closures), so a region is (F 0, at = effect-index, refs []).
        Z#35: `finalize R` gives the cleanup slice to a done, unwinding run with a region, when
        no run holds a slice; that one slice runs the whole chain innermost first, each
        region's exit a `finally-exit` (it pops the head region, committed at the block's
        start, so L2's measure drops per finalizer); after the last exit the outermost block
        still runs in the slice, and `slice-exit R` (the slice returns: R done, holding the
        slice, no region) releases it and runs T13. Z#40: a cleanup slice may only write,
        deliver, post, release and close: await/take/complete/finally-enter/open-scope need a
        normal run, and create-source/track/arm/spawn/create-comp are refused by transition
        (`in-cleanup`). Z#43: complete with an open region is refused by transition (`fins-open`).
        Z#44: host items (no token) are accepted while a slice is held: they are effects of
        the slice-holding run (D0); the model has no per-run attribution state, so nothing
        else changes (host cancel of the slice-holding run itself is refused, B19, Z#37).
    B19. Host cancel R: R is a task's run that is not done and holds no slice (Z#37); an
        ordinary T14 with cascade (Z#39: the task is final, its dep creditors get the error).
    B20. open-scope st s: s = fresh, a child of the run's current scope, a body effect of a
        normal run without an effect-index step (as the engine). close-scope s: T16 on an
        explicit scope, no token. detach k s: a task without result whose owner is a scope
        moves to the open scope s, and its run scope is re-parented under s (Z#41); the old
        owner's subtree is then removed when empty. Z#69: refused when s lies in the task's own
        run-scope subtree (the run scope is s or on s's parent chain, `scope-within`).
    B21. release-world: refused when already released; removes every host-creditor edge
        (observe, host waits), drops pins, abandons pending-activation, sets every handle
        count to 0 (spec: released handles' rows are removed; the engine keeps handle counts),
        then T16 on the root scope (2). Later host items are not refused globally: top-level
        creations need an open scope, handle operations find 0 handles.
    B22. T1 in a body (`t1-create-nonstream`, replacing step's T1 in the step): a computation run adopts a
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
        a mailbox, semaphore or undelivered deferred, step.clj `source-result`), then T10."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]))

;; Reading map
;;
;; A step of the world is
;;
;;   world-step w it                = then-rule-r (raw w it)
;;   raw w it                       = then-cancel-losers w (host-guarded-transition w it)
;;   host-guarded-transition w it   = refuse when (host-item-refused w it), else (transition w it)
;;
;;   transition          the table: one branch per Item constructor, each `tN-<verb>` behind its
;;                       guard (`<item>-refused`, `require-root-open`)
;;   then-cancel-losers  after an accepted transition the `any` losers are cancelled
;;   then-rule-r         Rule R (rule.clj): rounds of normalize-then-filter until no row is
;;                       orphaned; normalize loops until `normalized`
;;
;; Names
;;   well-formed            the base invariant (edits.clj); `well-formed-<x>` says edit or
;;                          transition x keeps it
;;   <part>-<x>             the same for a part of the top invariant (i10-task-<x>, i8-closed-<x>);
;;                          these lemmas are in inv/ and are built by pres/
;;   tN-<verb>              transition N of the spec (§8); `t-<verb>` is a transition without a number
;;   <x>-basic              step.clj's first form of the transition (t1-create-source-basic)
;;   <item>-refused         the guard that refuses the item
;;   world-released         the world's `released` flag
;;   <x>-in-run, <x>-top    x called from a run, or by the host at top level
;;   <x>-total              the statement for every item, accepted or refused
;;
;; Part A fresh rows. B row constructors, validation. C T4, T5, T3. D T11 dispatch.
;; E settle, T12. F T6, T22, T8. G the step: the table and the pipeline above.
;; The re-entry rule of §2 (an edge's cont is a k only if its run holds no finalizer entry and no
;; resource) is `reentrant-cont-needs-no-finalizer`, next to `await-cont` in part F; T7's half is
;; next to `track-cont` in step.clj.
;; README.md has the full legend ("Names") and the old names ("Old kernel names").

;; ===========================================================================
;; Part A. Inserting fresh rows: monotone edges-ref-ok, well-formed per table
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
  "inv-<p>-ins-fresh: inserting a row whose id is next-id, then bumping, keeps well-formed.
  `pe` proves pending-exact of the insert from pending-exact w, `er` edges-ref-ok."
  [prefix row pe er]
  (let [ins (symbol (str prefix "-ins")) idf (symbol (str prefix "-id"))]
    `(a/theorem ~(symbol (str "well-formed-" prefix "-ins-fresh")) [~'w :- ~'World, ~'r :- ~row]
       (~'=> (~'= (~idf ~'r) (:next-id ~'w)) (~'= (~'well-formed ~'w) true)
             (~'= (~'well-formed (~'bump (~ins ~'w ~'r))) true))
       (~'intros ~'hr ~'h)
       (~'have ~'hs (~'And (~'= (~'pending-exact ~'w) true) (~'And (~'= (~'edges-ref-ok ~'w) true) (~'= (~'ids-ok ~'w) true))))
       (~'exact (~'well-formed-parts ~'w ~'h))
       (~'exact (~'well-formed-intro (~'bump (~ins ~'w ~'r))
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
(a/theorem well-formed-comp-ins-fresh [w :- World, r :- CompRow]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (well-formed w) true) (= (well-formed (bump (comp-ins w r))) true))
  (intros hr hp h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (well-formed-parts w h))
  (exact (well-formed-intro (bump (comp-ins w r))
           (Eq.trans (pending-exact-bump (comp-ins w r)) (pending-exact-comp-ins w r hp (And.left hs)))
           (Eq.trans (edges-ref-ok-bump (comp-ins w r)) (comp-ins-edges-ref-ok w r (And.left (And.right hs))))
           (comp-ins-fresh-ids-ok w r hr (And.right (And.right hs))))))

;; insert an edge only when its endpoints exist (the transitions' guards make the check
;; true; it keeps the lemmas free of the guard bookkeeping)
(a/defn insert-edge-checked [w :- World, e :- EdgeRow] World
  (if (edge-ok-in w e) (insert-edge-fresh w e) w))

(a/theorem well-formed-insert-edge-checked [w :- World, e :- EdgeRow]
  (=> (= (well-formed w) true) (= (well-formed (insert-edge-checked w e)) true))
  (intro h)
  (cases hk (edge-ok-in w e))
  (simp only [insert-edge-checked hk]) (exact h)
  (simp only [insert-edge-checked hk]) (exact (well-formed-insert-edge-fresh w e hk h)))

;; ===========================================================================
;; Part B. Row constructors; a run with its run scope; §3.4 validation and reactivation
;; ===========================================================================

(a/defn none-result [] RunResult (RunResult.mk res-none 0))
(a/defn new-scope-row [id :- Nat, parent :- Nat] ScopeRow (ScopeRow.mk id parent scope-run true))
;; run stamp = run id (oracle contract)
(a/defn new-run-row [id :- Nat, of :- Nat, epoch :- Nat, scope :- Nat, ei :- Nat] RunRow
  (RunRow.mk id of id epoch scope act-active mode-normal false ei (List.nil Finalizer) (List.nil Nat)))
(a/defn new-task-row [id :- Nat, owner :- Nat, run :- Nat, inputs :- (List Nat), loc :- Bool] TaskRow (TaskRow.mk id owner run none-result 1 inputs loc))

;; a run R (id next-id) of entity `of`, with its run scope S (next-id + 1, parent `parent`)
(a/defn add-run-scope [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat] World
  (bump (scope-ins (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))
                   (new-scope-row (+ (:next-id w) 1) parent))))

(a/theorem well-formed-add-run-scope [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (add-run-scope w of epoch parent ei)) true))
  (intro h)
  (simp only [add-run-scope])
  (have h1 (= (well-formed (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))) true))
  (exact (well-formed-run-ins-fresh w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) (rfl) h))
  (have he (= (scope-id (new-scope-row (+ (:next-id w) 1) parent))
              (:next-id (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei))))))
  (rfl)
  (exact (well-formed-scope-ins-fresh (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))
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
;; spindel.v2.progress.react).

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
              (:adopt-basis c) (:adopt-baselines c) (:handles c) (:tomb c)))
(a/theorem comp-set-rank-id [n :- Nat, c :- CompRow] (= (comp-id (comp-set-rank n c)) (comp-id c)) (rfl))
(a/theorem comp-set-rank-pending [n :- Nat, c :- CompRow] (= (:pending (comp-set-rank n c)) (:pending c)) (rfl))
(a/structure RJ [] (node Nat) (need Nat))
(a/structure RaiseRes [] (world World) (ok Bool))
(a/defn raise-jobs [n :- Nat, ys :- (List Nat)] (List RJ)
  (match ys [nil (List.nil RJ)] [(cons h t) (List.cons RJ (RJ.mk h n) (raise-jobs n t))]))
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
                                                  (List.append RJ t (raise-jobs (+ (:need j) 1) (dep-creditors (:edges w) (:node j)))))))])]))
(a/defn raise-fuel [w :- World] (List Nat)
  (List.cons Nat 0 (rep-list (tbl-ids comp-id (:comps w)) (List.cons Nat 0 (tbl-ids edge-id (:edges w))))))
;; make room for the dep edge c -> d (only when d is a computation)
(a/defn raise-run [w :- World, c :- Nat, d :- Nat] RaiseRes
  (if (comp-has w d)
      (raise-loop (raise-fuel w) d w (List.cons RJ (RJ.mk c (+ (comp-rank w d) 1)) (List.nil RJ)))
      (RaiseRes.mk w true)))
(a/defn raise-for [w :- World, c :- Nat, d :- Nat] World (:world (raise-run w c d)))

(a/theorem well-formed-raise-loop [fuel :- (List Nat)]
  (forall [d :- Nat, w :- World, todo :- (List RJ)]
    (=> (= (well-formed w) true) (= (well-formed (:world (raise-loop fuel d w todo))) true)))
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
          (exact (ih d _ _ (well-formed-comp-upd w (:node j) (comp-set-rank (:need j)) (comp-set-rank-id (:need j))
                              (comp-set-rank-pending (:need j)) h))))))))

(a/theorem well-formed-raise-for [w :- World, c :- Nat, d :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (raise-for w c d)) true))
  (intro h)
  (cases hd (comp-has w d))
  (simp only [raise-for raise-run hd]) (exact h)
  (simp only [raise-for raise-run hd]) (exact (well-formed-raise-loop (raise-fuel w) d w _ h)))

;; the I12 condition on one edge, and over the world (executable; preservation: spindel.v2.inv.rank)
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
              (:adopt-basis c) (:adopt-baselines c) (:handles c) false))
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
              (:adopt-basis c) (:adopt-baselines c) (:handles c) false))
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

(a/theorem well-formed-react-add [w :- World, c :- Nat, v :- Valid]
  (=> (= (well-formed w) true) (= (well-formed (react-add w c v)) true))
  (intro h)
  (cases hk (react-ok w c v))
  (simp only [react-add hk]) (exact h)
  (simp only [react-add hk])
  (exact (well-formed-raise-for _ c (:debtor v) (well-formed-insert-edge-checked w _ h))))

(a/theorem well-formed-react-edges [vs :- (List Valid)]
  (forall [w :- World, c :- Nat] (=> (= (well-formed w) true) (= (well-formed (react-edges w c vs)) true)))
  (induction vs)
  (case' [cons h t ih])
  (case' [nil])
  (intros w c hw) (simp only [react-edges]) (exact hw)
  (intros w c hw) (simp only [react-edges]) (exact (ih _ c (well-formed-react-add w c h hw))))

(a/theorem well-formed-react-one [w :- World, c :- CompRow]
  (=> (= (well-formed w) true) (= (well-formed (react-one w c)) true))
  (intro h)
  (simp only [react-one])
  (exact (well-formed-react-edges (:validity c) _ (:id c)
           (well-formed-comp-upd w (:id c) comp-react-row comp-react-row-id comp-react-row-pending h))))

(a/theorem well-formed-react-loop [fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)] (=> (= (well-formed w) true) (= (well-formed (react-loop fuel w q)) true)))
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
  (simp only [react-loop hc hi]) (exact (ih _ _ (well-formed-react-one w c hw))))

(a/theorem well-formed-demand-reactive [w :- World, d :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (demand-reactive w d)) true))
  (intro h)
  (cases hc (comp-find w d)) (case' [some c]) (case' [none])
  (simp only [demand-reactive hc]) (exact h)
  (cases hi (:idle c))
  (simp only [demand-reactive hc hi]) (exact h)
  (cases hv (valid-idle w c))
  (simp only [demand-reactive hc hi hv]) (exact (well-formed-comp-upd w d comp-demand-row comp-demand-row-id comp-demand-row-pending h))
  (simp only [demand-reactive hc hi hv]) (exact (well-formed-react-loop (react-fuel w) w _ h)))

;; ===========================================================================
;; Part C. T4 spawn, T5 start, T3 create-comp
;; ===========================================================================

;; Z#26: a task run's scope has the task's owner scope as parent (0 when the owner is a
;; computation); a computation run's scope has parent 0
(a/defn task-scope-parent [w :- World, owner :- Nat] Nat (if (scope-has w owner) owner 0))

;; T4 rows: task K = next-id, run R = K + 1, run scope S = K + 2 (fresh-id order)
(a/defn spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat), loc :- Bool] World
  (add-run-scope (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc)))
                 (:next-id w) 0 (task-scope-parent w owner) 0))

(a/theorem well-formed-spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat), loc :- Bool]
  (=> (= (well-formed w) true) (= (well-formed (spawn-rows w owner inputs loc)) true))
  (intro h)
  (simp only [spawn-rows])
  (exact (well-formed-add-run-scope _ (:next-id w) 0 (task-scope-parent w owner) 0
           (well-formed-task-ins-fresh w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc) (rfl) h))))

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
              (tbl-filter (created-other (:id b)) (:adopt-basis c)) (:adopt-baselines c) (:handles c) (:tomb c)))
(a/theorem comp-rebasis-id [b :- Created, c :- CompRow] (= (comp-id (comp-rebasis b c)) (comp-id c)) (rfl))
(a/theorem comp-rebasis-pending [b :- Created, c :- CompRow] (= (:pending (comp-rebasis b c)) (:pending c)) (rfl))
(a/defn respawn-raw [w :- World, r :- RunRow, x :- Nat] World
  (run-upd (comp-upd w (:of r) (comp-rebasis (Created.mk x (:effect-index r)))) (:id r) run-tick))

;; Z#77 fork-local tasks (K2): a scope is fork-local when it or a scope on its parent chain is the run
;; scope of a run of a fork-local task; a new task is fork-local when it is created with the option
;; (`flag`) or its owner is a fork-local scope (a computation owner never is: its id names no scope, and
;; a computation run's scope has no parent, Z#26). The mark is fixed at creation.
(a/defn task-is-local [t :- TaskRow] Bool (:local t))
(a/defn task-local-id [w :- World, k :- Nat] Bool (opt-test task-is-local (task-find w k)))
(a/defn run-scope-of-local [w :- World, x :- Nat, r :- RunRow] Bool
  (Bool.and (Nat.beq (:scope r) x) (task-local-id w (:of r))))
(a/defn local-run-scope [w :- World, x :- Nat] Bool (tbl-any (run-scope-of-local w x) (:runs w)))
(a/defn scope-local [w :- World, s :- Nat] Bool
  (tbl-any (local-run-scope w) (List.cons Nat s (scope-ancestors w s))))
(a/defn spawn-loc [w :- World, owner :- Nat, flag :- Bool] Bool (Bool.or flag (scope-local w owner)))
;; Z#77 (Q4): an unmarked task is not detached into a fork-local scope (the mark is the creator's: a fork-local
;; task detached elsewhere keeps it)
(a/defn detach-local-refused [w :- World, k :- Nat, s :- Nat] Bool (Bool.and (scope-local w s) (Bool.not (task-local-id w k))))
;; the option inside a computation body is refused (transition, Z#77: `{:spindel/invalid :fork-local}`)
(a/defn spawn-local-refused [w :- World, st :- Nat, flag :- Bool] Bool
  (Bool.and flag (match (tok-run w st) [none false] [(some r) (in-comp w r)])))

;; inside a run (body effect): a re-spawn (above), or a new task (fresh = next-id) owned per
;; §5.2, recorded in a computation's basis; effect tick either way
(a/defn t4-spawn [w :- World, st :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat), flag :- Bool] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (match (respawn-target w r fresh)
                [none (if (Nat.beq fresh (:next-id w))
                          (accept (run-upd (record-basis (spawn-rows w (spawn-owner w r) inputs (spawn-loc w (spawn-owner w r) flag)) r fresh) (:id r) run-tick))
                          (refuse w))]
                [(some t) (if (nat-list-eq inputs (:inputs t)) (accept (respawn-raw w r fresh)) (refuse w))])]))
;; at top level: owned by the given open scope
(a/defn t4-spawn-top [w :- World, scope :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat), flag :- Bool] Outcome
  (if (Bool.and (Nat.beq fresh (:next-id w)) (scope-open-at w scope)) (accept (spawn-rows w scope inputs (spawn-loc w scope flag))) (refuse w)))

(a/theorem well-formed-t4-spawn [w :- World, st :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat), flag :- Bool]
  (=> (= (well-formed w) true) (= (well-formed (:world (t4-spawn w st body fresh inputs flag))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t4-spawn ht refuse]) (exact h)
  (cases hp (respawn-target w r fresh))
  (case [none]
    (cases hf (Nat.beq fresh (:next-id w)))
    (case [false] (simp only [t4-spawn ht hp hf refuse]) (exact h))
    (case [true]
      (simp only [t4-spawn ht hp hf accept])
      (exact (well-formed-run-upd _ (:id r) run-tick run-tick-run-id
               (well-formed-record-basis _ r fresh (well-formed-spawn-rows w (spawn-owner w r) inputs (spawn-loc w (spawn-owner w r) flag) h))))))
  (case [some t]
    (cases he (nat-list-eq inputs (:inputs t)))
    (case [false] (simp only [t4-spawn ht hp he refuse]) (exact h))
    (case [true]
      (simp only [t4-spawn ht hp he accept respawn-raw])
      (exact (well-formed-run-upd _ (:id r) run-tick run-tick-run-id
               (well-formed-comp-upd w (:of r) _ (comp-rebasis-id _) (comp-rebasis-pending _) h))))))

(a/theorem t4-spawn-refuse [w :- World, st :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat), flag :- Bool]
  (=> (= (:accepted (t4-spawn w st body fresh inputs flag)) false) (= (:world (t4-spawn w st body fresh inputs flag)) w))
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

(a/theorem well-formed-t4-spawn-top [w :- World, scope :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat), flag :- Bool]
  (=> (= (well-formed w) true) (= (well-formed (:world (t4-spawn-top w scope body fresh inputs flag))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (scope-open-at w scope)))
  (simp only [t4-spawn-top hg refuse]) (exact h)
  (simp only [t4-spawn-top hg accept]) (exact (well-formed-spawn-rows w scope inputs (spawn-loc w scope flag) h)))

(a/theorem t4-spawn-top-refuse [w :- World, scope :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat), flag :- Bool]
  (=> (= (:accepted (t4-spawn-top w scope body fresh inputs flag)) false) (= (:world (t4-spawn-top w scope body fresh inputs flag)) w))
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
              (:adopt-basis c) (:adopt-baselines c) (:handles c) false))
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

(a/theorem well-formed-start-raw [w :- World, c :- CompRow]
  (=> (= (well-formed w) true) (= (well-formed (start-raw w c)) true))
  (intro h)
  (simp only [start-raw])
  (exact (well-formed-comp-upd _ (:id c) (comp-start-row (:next-id w)) (comp-start-row-id (:next-id w))
           (comp-start-row-pending (:next-id w)) (well-formed-add-run-scope w (:id c) (start-epoch c) 0 0 h))))

(a/theorem well-formed-t5-start [w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t5-start w cid fresh))) true))
  (intro h)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [t5-start hc refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (startable w c)))
  (simp only [t5-start hc hg refuse]) (exact h)
  (simp only [t5-start hc hg accept]) (exact (well-formed-start-raw w c h)))

(a/theorem t5-start-refuse [w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (:accepted (t5-start w cid fresh)) false) (= (:world (t5-start w cid fresh)) w))
  (intro ha)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [t5-start hc refuse])
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (startable w c)))
  (simp only [t5-start hc hg refuse])
  (simp [t5-start hc hg accept] at ha))

;; ---- T3 create-comp(c, inputs, body). The item names the computation id c: an existing
;; computation (adoption or replacement), or else c must be next-id (a fresh computation).
;; Every case records C in a computation creator's basis at the current site (§5.2), and takes it
;; out of the creator's adoption basis (a readopted creation leaves the adoption basis at
;; readoption, as a re-spawn's: `comp-rebasis`), and ticks the effect index.
;;   absent: fresh (epoch 1, done-epoch none, handles 1, Z#13), owner per §5.2
;;   present, equal inputs: adopted, handles unchanged (Z#29: a new handle is `handle-new`)
;;   present, different inputs (W#5): inputs/body replaced, handles unchanged (Z#29), the
;;     rerun-source write: C.epoch + 1 (Z#8, the restart site of T11: no fired edge) and the
;;     marking of §4.5.1 from C (C's out-edges and every dep edge whose debtor is reachable
;;     from C through reversed dep edges); an idle entry becomes fresh (idle := false,
;;     done-epoch := none, validity cleared)
(a/defn new-comp-row [w :- World, id :- Nat, owner :- Nat, inputs :- (List Nat), body :- Nat] CompRow
  (CompRow.mk id owner inputs body 0 1 0 (marked-in id (:edges w)) 0 0 none-result false
              (List.nil Valid) (List.nil Created) (List.nil Created) (List.nil AdoptBase) 1 false))
(a/defn comp-adopt-row [c :- CompRow] CompRow c)
(a/defn comp-replace-row [inputs :- (List Nat), body :- Nat, c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) inputs body (:run c) (+ (:epoch c) 1) (if (:idle c) 0 (:done-epoch c))
              (:pending c) (:rank c) (:version c) (:result c) false (List.nil Valid) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) (:handles c) false))
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
                  (accept (run-upd (comp-upd (create-comp-raw w c (source-owner w r) inputs body) (:of r)
                                             (comp-rebasis (Created.mk c (:effect-index r))))
                                   (:id r) run-tick))
                  (refuse w))]))
(a/defn t3-create-top [w :- World, scope :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat] Outcome
  (if (Bool.and (create-ok w c) (scope-open-at w scope)) (accept (create-comp-raw w c scope inputs body)) (refuse w)))

(a/theorem well-formed-mark-from [w :- World, c :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (mark-from w c)) true))
  (intro h) (exact (well-formed-nat-fold mark-edge well-formed-mark-edge _ w h)))

(a/theorem well-formed-create-comp-raw [w :- World, c :- Nat, owner :- Nat, inputs :- (List Nat), body :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (create-comp-raw w c owner inputs body)) true))
  (intro h)
  (cases hc (comp-find w c)) (case' [some row]) (case' [none])
  (simp only [create-comp-raw hc])
  (exact (well-formed-comp-ins-fresh w (new-comp-row w (:next-id w) owner inputs body) (rfl) (rfl) h))
  (cases hi (nat-list-eq (:inputs row) inputs))
  (simp only [create-comp-raw hc hi])
  (exact (well-formed-mark-from _ c (well-formed-comp-upd w c (comp-replace-row inputs body) (comp-replace-row-id inputs body)
                              (comp-replace-row-pending inputs body) h)))
  (simp only [create-comp-raw hc hi])
  (exact (well-formed-comp-upd w c comp-adopt-row comp-adopt-row-id comp-adopt-row-pending h)))

(a/theorem well-formed-t3-create [w :- World, st :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t3-create w st c inputs body))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t3-create ht refuse]) (exact h)
  (cases hg (create-ok w c))
  (simp only [t3-create ht hg refuse]) (exact h)
  (simp only [t3-create ht hg accept])
  (exact (well-formed-run-upd _ (:id r) run-tick run-tick-run-id
           (well-formed-comp-upd _ (:of r) _ (comp-rebasis-id _) (comp-rebasis-pending _)
             (well-formed-create-comp-raw w c (source-owner w r) inputs body h)))))

(a/theorem t3-create-refuse [w :- World, st :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat]
  (=> (= (:accepted (t3-create w st c inputs body)) false) (= (:world (t3-create w st c inputs body)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t3-create ht refuse])
  (cases hg (create-ok w c))
  (simp only [t3-create ht hg refuse])
  (simp [t3-create ht hg accept] at ha))

(a/theorem well-formed-t3-create-top [w :- World, scope :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t3-create-top w scope c inputs body))) true))
  (intro h)
  (cases hg (Bool.and (create-ok w c) (scope-open-at w scope)))
  (simp only [t3-create-top hg refuse]) (exact h)
  (simp only [t3-create-top hg accept]) (exact (well-formed-create-comp-raw w c scope inputs body h)))

(a/theorem t3-create-top-refuse [w :- World, scope :- Nat, c :- Nat, inputs :- (List Nat), body :- Nat]
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
(a/defn entity-run [w :- World, x :- Nat] Nat
  (match (comp-find w x) [none (match (task-find w x) [none 0] [(some t) (:run t)])] [(some c) (:run c)]))
(a/defn blocked-base [w :- World, x :- Nat] Bool
  (match (comp-find w x)
    [none (match (task-find w x) [none false] [(some t) (opt-test run-parked (run-find w (:run t)))])]
    [(some c) (run-parked-of w c)]))
(a/defn edge-debtor-of [w :- World, x :- Nat] Nat (match (edge-find w x) [none 0] [(some e) (:debtor e)]))
(a/defn debtors-of [w :- World, xs :- (List Nat)] (List Nat)
  (match xs [nil (List.nil Nat)] [(cons h t) (List.cons Nat (edge-debtor-of w h) (debtors-of w t))]))
(a/defn blocked-deps [w :- World, x :- Nat] (List Nat)
  (debtors-of w (tbl-gather (act-of-run (entity-run w x)) act-contrib (:acts w))))
(a/defn blocked-leaf [w :- World, y :- Nat] Bool (Bool.or (source-has w y) (resource-has w y)))
(a/defn blocked-nodes [w :- World] (List Nat) (nat-app (tbl-ids comp-id (:comps w)) (tbl-ids task-id (:tasks w))))
(a/defn blocked-res [w :- World] DeriveResult
  (derive-run-l (List.cons Nat 0 (blocked-nodes w)) (blocked-base w) (blocked-deps w) (blocked-leaf w) (blocked-nodes w)))
(a/defn blocked-set [w :- World] (List Nat) (:derived (blocked-res w)))
(a/defn blocked-converged [w :- World] Bool (:converged (blocked-res w)))

(a/theorem blocked-sound [w :- World, x :- Nat]
  (=> (= (reach-mem x (blocked-set w)) true) (Derive (blocked-base w) (blocked-deps w) (blocked-leaf w) x))
  (intro h)
  (simp only [blocked-set blocked-res derive-run-l-eq] at h)
  (exact (derive-run-sound _ _ _ _ _ x h)))

(a/theorem blocked-complete [w :- World, x :- Nat]
  (=> (forall [a :- Nat] (=> (= (reach-mem a (blocked-nodes w)) true)
        (forall [b :- Nat] (=> (= (reach-mem b (blocked-deps w a)) true) (= (blocked-leaf w b) false) (= (reach-mem b (blocked-nodes w)) true)))))
      (= (blocked-converged w) true)
      (Derive (blocked-base w) (blocked-deps w) (blocked-leaf w) x)
      (= (reach-mem x (blocked-nodes w)) true)
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
              bs (:handles c) (:tomb c)))
(a/defn comp-set-run [rid :- Nat, c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) rid (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) (:handles c) false))
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

(a/theorem well-formed-cancel-pred [w :- World, c :- CompRow]
  (=> (= (well-formed w) true) (= (well-formed (cancel-pred w c)) true))
  (intro h)
  (cases hr (run-find w (:run c))) (case' [some r]) (case' [none])
  (simp only [cancel-pred hr]) (exact h)
  (cases ha (run-alive r))
  (simp only [cancel-pred hr ha]) (exact h)
  (simp only [cancel-pred hr ha]) (exact (well-formed-run-cascade w _ h)))

(a/theorem well-formed-cut-suffix [w :- World, c :- Nat, has :- Bool, cut :- Nat, cid :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (cut-suffix w c has cut cid)) true))
  (intro h)
  (simp only [cut-suffix])
  (exact (well-formed-comp-upd _ c _ (comp-cut-row-id has cut _) (comp-cut-row-pending has cut _)
           (well-formed-drop-edges w (keep-prefix c has cid) h))))

(a/theorem well-formed-consume-entry [w :- World, e :- EdgeRow]
  (=> (= (well-formed w) true) (= (well-formed (consume-entry w e)) true))
  (intro h)
  (cases hf (deb-final w (:debtor e)))
  (cases hr (Nat.beq (:cont e) cont-restart))
  (simp only [consume-entry hr hf])
  (exact (well-formed-edge-upd w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
           (edge-rearm-edge-id _ _) (edge-rearm-kind _ _) (edge-rearm-creditor _ _)
           (edge-rearm-debtor _ _) (edge-rearm-marked _ _) h))
  (simp only [consume-entry hr hf]) (exact (well-formed-edge-set-phase w (:id e) ph-armed h))
  (simp only [consume-entry hf]) (exact (well-formed-remove-edge w (:id e) h)))

(a/theorem well-formed-new-run-of [w :- World, c :- CompRow, ei :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (new-run-of w c ei)) true))
  (intro h)
  (simp only [new-run-of])
  (exact (well-formed-comp-upd _ (:id c) (comp-set-run (:next-id w)) (comp-set-run-id (:next-id w))
           (comp-set-run-pending (:next-id w)) (well-formed-add-run-scope w (:id c) (:epoch c) 0 ei h))))

(a/theorem well-formed-dispatch-raw [w :- World, c :- CompRow]
  (=> (= (well-formed w) true) (= (well-formed (dispatch-raw w c)) true))
  (intro h)
  (have h1 := (well-formed-cancel-pred w c h))
  (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
  (simp only [dispatch-raw he])
  (exact (well-formed-new-run-of _ c 0 (well-formed-cut-suffix _ (:id c) false 0 0 h1)))
  (simp only [dispatch-raw he])
  (exact (well-formed-new-run-of _ c _ (well-formed-consume-entry _ e (well-formed-cut-suffix _ (:id c) true (:at e) (:id e) h1)))))

(a/theorem well-formed-t11-dispatch [w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t11-dispatch w cid fresh))) true))
  (intro h)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [t11-dispatch hc refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))))
  (simp only [t11-dispatch hc hg refuse]) (exact h)
  (simp only [t11-dispatch hc hg accept]) (exact (well-formed-dispatch-raw w c h)))

(a/theorem t11-dispatch-refuse [w :- World, cid :- Nat, fresh :- Nat]
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

(a/theorem well-formed-settle-edge [changed :- Bool, ver :- Nat, w :- World, x :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (settle-edge changed ver w x)) true))
  (intro h)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [settle-edge hf]) (exact h)
  (have h1 (= (well-formed (if (Nat.beq (:phase e) ph-armed)
                              (if (Bool.or (edge-behind ver e) (member-current w e)) (fire-dep w e) w)
                              w)) true))
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [hp]) (exact h)
  (cases hc (Bool.or (edge-behind ver e) (member-current w e)))
  (simp only [hp hc]) (exact h)
  (simp only [hp hc]) (exact (well-formed-fire-dep w e h))
  (simp only [settle-edge hf])
  (exact (well-formed-unmark-edge _ x h1)))

(a/theorem well-formed-settle-host [w :- World, d :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (settle-host w d)) true))
  (intro h) (exact (well-formed-nat-fold (fire-edge (deb-result w d)) (well-formed-fire-edge (deb-result w d)) _ w h)))

(a/theorem well-formed-settle-one [w :- World, d :- Nat, changed :- Bool]
  (=> (= (well-formed w) true) (= (well-formed (settle-one w d changed)) true))
  (intro h)
  (simp only [settle-one])
  (exact (well-formed-settle-host _ d (well-formed-nat-fold (settle-edge changed (deb-version w d))
                                (well-formed-settle-edge changed (deb-version w d)) _ w h))))

(a/theorem well-formed-settle-loop [fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)] (=> (= (well-formed w) true) (= (well-formed (:world (settle-loop fuel w q))) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w q hw) (simp only [settle-loop]) (exact hw)
  (intros w q hw)
  (cases q)
  (simp only [settle-loop]) (exact hw)
  (rename_i d t)
  (simp only [settle-loop])
  (exact (ih _ _ (well-formed-settle-one w d false hw))))

(a/theorem well-formed-settle [w :- World, d :- Nat, changed :- Bool]
  (=> (= (well-formed w) true) (= (well-formed (settle w d changed)) true))
  (intro h)
  (cases hr (ready-id w d))
  (simp only [settle hr]) (exact h)
  (simp only [settle hr settle-res])
  (exact (well-formed-settle-loop (settle-fuel w) _ _ (well-formed-settle-one w d changed h))))

;; dep edges on final debtors are removed after the delivery (T10)
(a/defn finalize-if-final [w :- World, d :- Nat] World (if (deb-final w d) (t10-finalize-debtor w d) w))

(a/theorem well-formed-finalize-if-final [w :- World, d :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (finalize-if-final w d)) true))
  (intro h)
  (cases hf (deb-final w d))
  (simp only [finalize-if-final hf]) (exact h)
  (simp only [finalize-if-final hf]) (exact (well-formed-t10-finalize-debtor w d h)))

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
              (:validity c) (:basis c) (List.nil Created) (List.nil AdoptBase) (:handles c) (:tomb c)))
(a/theorem comp-result-row-id [res :- RunResult, ep :- Nat, c :- CompRow] (= (comp-id (comp-result-row res ep c)) (comp-id c)) (rfl))
(a/theorem comp-result-row-pending [res :- RunResult, ep :- Nat, c :- CompRow] (= (:pending (comp-result-row res ep c)) (:pending c)) (rfl))
(a/defn task-result-row [res :- RunResult, t :- TaskRow] TaskRow (TaskRow.mk (:id t) (:owner t) (:run t) res (:handles t) (:inputs t) (:local t)))
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
  (finalize-if-final
    (run-cascade (retire-after (:world (complete-body (run-upd w (:id r) run-complete-row) r res)) (:id r))
                 (List.append Job (:rest (complete-body (run-upd w (:id r) run-complete-row) r res))
                              (List.cons Job (Job.jretire (:id r)) (List.nil Job))))
    (:of r)))

(a/defn run-normal [r :- RunRow] Bool (Bool.and (run-alive r) (Nat.beq (:mode r) mode-normal)))
(a/defn t12-complete [w :- World, st :- Nat, tag :- Nat, v :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (if (run-normal r) (accept (complete-raw w r (RunResult.mk tag v))) (refuse w))]))

(a/theorem well-formed-complete-body [w :- World, r :- RunRow, res :- RunResult]
  (=> (= (well-formed w) true) (= (well-formed (:world (complete-body w r res))) true))
  (intro h)
  (cases hc (comp-find w (:of r)))
  (case [none]
    (cases hk (task-find w (:of r)))
    (case [none] (simp only [complete-body hc hk]) (exact h))
    (case [some k]
      (simp only [complete-body hc hk complete-task])
      (exact (well-formed-nat-fold (fire-edge res) (well-formed-fire-edge res) _ _
               (well-formed-cancel-res _ r (well-formed-task-upd w (:id k) (task-result-row res) (task-result-row-id res) h))))))
  (case [some c]
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [complete-body hc he]) (exact h))
    (case [true]
      (simp only [complete-body hc he complete-comp])
      (exact (well-formed-settle _ (:id c) _ (well-formed-cancel-res _ r
               (well-formed-comp-upd w (:id c) (comp-result-row res (:epoch r)) (comp-result-row-id res (:epoch r))
                 (comp-result-row-pending res (:epoch r)) h)))))))

(a/theorem well-formed-retire-after [w :- World, rid :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (retire-after w rid)) true))
  (intro h)
  (cases hr (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [retire-after hr]) (exact h)
  (cases ht (retirable r))
  (simp only [retire-after hr ht]) (exact (well-formed-cleanup-set w rid _ h))
  (simp only [retire-after hr ht]) (exact h))

(a/theorem well-formed-complete-raw [w :- World, r :- RunRow, res :- RunResult]
  (=> (= (well-formed w) true) (= (well-formed (complete-raw w r res)) true))
  (intro h)
  (have h0 := (well-formed-run-upd w (:id r) run-complete-row run-complete-row-id h))
  (simp only [complete-raw])
  (exact (well-formed-finalize-if-final _ (:of r) (well-formed-run-cascade _ _ (well-formed-retire-after _ (:id r) (well-formed-complete-body _ r res h0))))))

(a/theorem well-formed-t12-complete [w :- World, st :- Nat, tag :- Nat, v :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t12-complete w st tag v))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t12-complete ht refuse]) (exact h)
  (cases hn (run-normal r))
  (simp only [t12-complete ht hn refuse]) (exact h)
  (simp only [t12-complete ht hn accept]) (exact (well-formed-complete-raw w r _ h)))

(a/theorem t12-complete-refuse [w :- World, st :- Nat, tag :- Nat, v :- Nat]
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
;; (creditor A) otherwise and for resources (Z#6); cont per §2's re-entrancy rule (Y#3):
;; cont = k only for mode `one` in a run with no finalizer entry (neither an open region nor a
;; running finally clause: T11 must not re-enter a clause) and no resource, as `track-cont`
(a/defn fin-region [fz :- Finalizer] Bool (Nat.beq (:f fz) 0))
(a/defn await-cont [r :- RunRow, mode :- Nat, k :- Nat] Nat
  (if (Bool.and (Nat.beq mode am-one) (Bool.and (fins-empty (:finalizers r)) (nats-empty (:resources r)))) k cont-restart))
;; The rule as theorems (true also when k itself is the restart code): a mode other than `one`, a
;; finalizer entry or a resource gives `cont-restart`. `reentrant-cont-needs-no-finalizer` states
;; the rule for both definitions (`track-cont`, step.clj): a cont other than restart needs a run
;; with no finalizer entry and no resource.
(a/theorem await-cont-restart-with-finalizer [r :- RunRow, mode :- Nat, k :- Nat]
  (=> (= (fins-empty (:finalizers r)) false) (= (await-cont r mode k) cont-restart))
  (intro h)
  (simp only [await-cont h Bool.false_and Bool.and_false]))

(a/theorem await-cont-restart-with-resource [r :- RunRow, mode :- Nat, k :- Nat]
  (=> (= (nats-empty (:resources r)) false) (= (await-cont r mode k) cont-restart))
  (intro h)
  (simp only [await-cont h Bool.and_false]))

(a/theorem await-cont-restart-unless-mode-one [r :- RunRow, mode :- Nat, k :- Nat]
  (=> (= (Nat.beq mode am-one) false) (= (await-cont r mode k) cont-restart))
  (intro h)
  (simp only [await-cont h Bool.false_and]))

(a/theorem await-cont-reentrant-needs-no-finalizer [r :- RunRow, mode :- Nat, k :- Nat]
  (=> (Not (= (await-cont r mode k) cont-restart))
      (And (= (Nat.beq mode am-one) true)
           (And (= (fins-empty (:finalizers r)) true) (= (nats-empty (:resources r)) true))))
  (intro hne)
  (cases hm (Nat.beq mode am-one))
  (case [false] (exact (absurd (await-cont-restart-unless-mode-one r mode k hm) hne)))
  (case [true]
    (cases hf (fins-empty (:finalizers r)))
    (case [false] (exact (absurd (await-cont-restart-with-finalizer r mode k hf) hne)))
    (case [true]
      (cases hz (nats-empty (:resources r)))
      (case [false] (exact (absurd (await-cont-restart-with-resource r mode k hz) hne)))
      (case [true] (exact (And.intro (rfl) (And.intro (rfl) (rfl))))))))

(a/theorem reentrant-cont-needs-no-finalizer [r :- RunRow, mode :- Nat, k :- Nat]
  (And (=> (Not (= (track-cont r k) cont-restart))
           (And (= (fins-empty (:finalizers r)) true) (= (nats-empty (:resources r)) true)))
       (=> (Not (= (await-cont r mode k) cont-restart))
           (And (= (Nat.beq mode am-one) true)
                (And (= (fins-empty (:finalizers r)) true) (= (nats-empty (:resources r)) true)))))
  (exact (And.intro (track-cont-reentrant-needs-no-finalizer r k) (await-cont-reentrant-needs-no-finalizer r mode k))))
(a/defn as-dep [w :- World, r :- RunRow, d :- Nat] Bool (Bool.and (in-comp w r) (Bool.not (resource-has w d))))
;; a dep member on a signal or cell records the source's state as its baseline at the site (engine
;; `await-group!`: E-BASE := X-VALUE), whether or not the fast path then fills it (Z#61: after the
;; resolving fill it does not)
(a/defn await-edge [w :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat] EdgeRow
  (if (as-dep w r d)
      (EdgeRow.mk 0 ek-dep (:of r) d (await-cont r mode k) (:effect-index r) ph-armed false false 0
                  (sig-cell w d) (if (sig-cell w d) (deb-value w d) 0) (if (sig-cell w d) (deb-version w d) 0))
      (EdgeRow.mk 0 ek-wait a d cont-restart (:effect-index r) ph-armed false false 0 false 0 0)))
;; re-await of an existing site edge: re-armed with the new cont (its baseline stays)
(a/defn edge-reawait [c :- Nat, e :- EdgeRow] EdgeRow
  (EdgeRow.mk (:id e) (:kind e) (:creditor e) (:debtor e) c (:at e) ph-armed (:marked e) (:has-seen e) (:seen e)
              (:has-base e) (:base-value e) (:base-version e)))

;; T6: the cont of the edges it writes. The wiring (`await-step`) writes, per distinct debtor, either
;; the row `await-edge` (inserted with a fresh id; a wait edge always restarts) or the site's
;; existing dep edge updated by `edge-reawait (await-cont r mode k)`, r being the run as it is in
;; the input world. `t6-await-reentrant-needs-no-finalizer` is stated about these two rows, not
;; about the resulting world: after the wiring the transition fills, parks and finalizes, and
;; Rule R follows. That the rows are in the world after the wiring is `current-members-prefix-fields`
;; (inv/members/await_wire.clj), under the invariant. T22's host-wait edge (`host-wait-edge`) is
;; `cont-restart` by definition.
(a/theorem await-edge-cont [w :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat]
  (= (:cont (await-edge w r a mode k d)) (if (as-dep w r d) (await-cont r mode k) cont-restart))
  (cases hd (as-dep w r d))
  (all_goals (simp only [await-edge hd])))

(a/theorem edge-reawait-cont [c :- Nat, e :- EdgeRow]
  (= (:cont (edge-reawait c e)) c) (rfl))

(a/theorem t6-await-reentrant-needs-no-finalizer [w :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat, e0 :- EdgeRow, e :- EdgeRow]
  (=> (Or (= e (await-edge w r a mode k d)) (= e (edge-reawait (await-cont r mode k) e0)))
      (Not (= (:cont e) cont-restart))
      (And (= (Nat.beq mode am-one) true)
           (And (= (fins-empty (:finalizers r)) true) (= (nats-empty (:resources r)) true))))
  (intros hw hne)
  (apply (await-cont-reentrant-needs-no-finalizer r mode k))
  (intro hc)
  (apply hne)
  (cases hw)
  (case [inl h] (rw [h]) (rw [await-edge-cont]) (rw [hc])
    (cases hd (as-dep w r d)) (all_goals (simp only [hd])))
  (case [inr h] (rw [h]) (exact hc)))

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

;; fast fills: a ready debtor fills its slot(s) in the same commit (T9 on its member edge),
;; while that edge is still an unfilled member: once the activation resolved (`any` on its
;; first fill, a failing `all` on its first err, Z#61) the later ready debtors fill nothing and
;; their edges stay as wired (engine `await-group!`: the fast path stops at the winner; a T9
;; on such a dep edge would be an invalidation of the awaiting computation). Such an edge on a
;; final debtor goes with T10 after the fills (`finalize-if-final` in await-post, as the engine's
;; removal of final debtors' site edges).
(a/defn still-member [w :- World, x :- Nat] Bool (tbl-any (act-has-member x) (:acts w)))
(a/defn fast-fill [ps :- (List DE), w :- World, d :- Nat] World
  (if (fast-ready w d)
      (if (still-member w (pair-edge d ps)) (fire-edge (deb-result w d) w (pair-edge d ps)) w)
      w))
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
  (nat-fold finalize-if-final
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

(a/theorem well-formed-await-step [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (well-formed (:world acc)) true) (= (well-formed (:world (await-step r a mode k acc d))) true))
  (intro h)
  (cases hd (as-dep (:world acc) r d))
  (case [false]
    (simp only [await-step hd])
    (exact (well-formed-insert-edge-checked _ _ h)))
  (case [true]
    (cases hs (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none]
      (simp only [await-step hd hs])
      (simp only [await-new-dep])
      (exact (well-formed-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) d)
               (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _)
               (well-formed-raise-for _ (:of r) d (well-formed-insert-edge-checked _ _ h)))))
    (case [some e]
      (simp only [await-step hd hs])
      (exact (well-formed-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) d)
               (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _)
               (well-formed-edge-upd _ (:id e) (edge-reawait (await-cont r mode k)) (edge-reawait-edge-id _)
                 (edge-reawait-kind _) (edge-reawait-creditor _) (edge-reawait-debtor _) (edge-reawait-marked _) h))))))

(a/theorem well-formed-await-wire [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, ds :- (List Nat)]
  (forall [acc :- AwAcc] (=> (= (well-formed (:world acc)) true) (= (well-formed (:world (await-wire r a mode k acc ds))) true)))
  (induction ds)
  (case' [cons d t ih])
  (case' [nil])
  (intros acc h) (simp only [await-wire]) (exact h)
  (intros acc h) (simp only [await-wire]) (exact (ih _ (well-formed-await-step r a mode k acc d h))))

(a/theorem well-formed-fast-fill [ps :- (List DE), w :- World, d :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (fast-fill ps w d)) true))
  (intro h)
  (cases hr (fast-ready w d))
  (simp only [fast-fill hr]) (exact h)
  (cases hm (still-member w (pair-edge d ps)))
  (simp only [fast-fill hr hm]) (exact h)
  (simp only [fast-fill hr hm]) (exact (well-formed-fire-edge _ w _ h)))

(a/theorem well-formed-park-if [w :- World, a :- Nat, rid :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (park-if w a rid)) true))
  (intro h)
  (cases ha (act-has w a))
  (simp only [park-if ha]) (exact h)
  (simp only [park-if ha]) (exact (well-formed-run-upd w rid run-park-row run-park-row-id h)))

(a/theorem well-formed-await-pre [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (well-formed w) true) (= (well-formed (await-pre w r ds mode k mine)) true))
  (intro h)
  (have h1 := (well-formed-run-upd w (:id r) run-tick run-tick-run-id h))
  (have he (= (act-id (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine))
              (:next-id (run-upd w (:id r) run-tick))))
  (rfl)
  (simp only [await-pre])
  (exact (well-formed-nat-fold demand-reactive well-formed-demand-reactive _ _
           (well-formed-act-ins-fresh _ _ he h1))))

(a/theorem well-formed-await-post [a :- Nat, rid :- Nat, ds :- (List Nat), acc :- AwAcc]
  (=> (= (well-formed (:world acc)) true) (= (well-formed (await-post a rid ds acc)) true))
  (intro h)
  (have h2 (= (well-formed (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds)))) true))
  (exact (well-formed-act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))
           (act-set-members-id (mk-members (:pairs acc) 0 ds)) h))
  (have h3 (= (well-formed (nat-fold (fast-fill (:pairs acc))
                            (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds)))
                            (nat-distinct ds))) true))
  (exact (well-formed-nat-fold (fast-fill (:pairs acc)) (well-formed-fast-fill (:pairs acc)) (nat-distinct ds)
           (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))) h2))
  (have h4 := (well-formed-park-if (nat-fold (fast-fill (:pairs acc))
                            (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds)))
                            (nat-distinct ds)) a rid h3))
  (exact (well-formed-nat-fold finalize-if-final well-formed-finalize-if-final (nat-distinct ds) _ h4)))

(a/theorem well-formed-await-raw [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (well-formed w) true) (= (well-formed (await-raw w r ds mode k mine)) true))
  (intro h)
  (have h1 (= (well-formed (:world (await-acc w r ds mode k mine))) true))
  (exact (well-formed-await-wire r (:next-id w) mode k (nat-distinct ds)
           (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (well-formed-await-pre w r ds mode k mine h)))
  (exact (well-formed-await-post (:next-id w) (:id r) ds (await-acc w r ds mode k mine) h1)))

(a/theorem well-formed-t6-await [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
  (=> (= (well-formed w) true) (= (well-formed (:world (t6-await w st ds mode k fresh mine))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t6-await ht refuse]) (exact h)
  (cases hg (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
  (simp only [t6-await ht hg refuse]) (exact h)
  (simp only [t6-await ht hg accept]) (exact (well-formed-await-raw w r ds mode k mine h)))

(a/theorem t6-await-refuse [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
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

(a/theorem well-formed-host-await-raw [w :- World, d :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (host-await-raw w d)) true))
  (intro h)
  (have h1 (= (well-formed (host-await-dem w d)) true))
  (exact (well-formed-demand-reactive _ d (well-formed-insert-edge-checked w (host-wait-edge d) h)))
  (cases hr (fast-ready (host-await-dem w d) d))
  (simp only [host-await-raw hr]) (exact h1)
  (simp only [host-await-raw hr]) (exact (well-formed-fire-edge _ _ (:next-id w) h1)))

(a/theorem well-formed-t22-host-await [w :- World, d :- Nat, fresh :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t22-host-await w d fresh))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (deb-exists w d)))
  (simp only [t22-host-await hg refuse]) (exact h)
  (simp only [t22-host-await hg accept]) (exact (well-formed-host-await-raw w d h)))

(a/theorem t22-host-await-refuse [w :- World, d :- Nat, fresh :- Nat]
  (=> (= (:accepted (t22-host-await w d fresh)) false) (= (:world (t22-host-await w d fresh)) w))
  (intro ha)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (deb-exists w d)))
  (simp only [t22-host-await hg refuse])
  (simp [t22-host-await hg accept] at ha))

(a/theorem well-formed-t22-host-unawait [w :- World, x :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t22-host-unawait w x))) true))
  (intro h)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [t22-host-unawait hf refuse]) (exact h)
  (cases hk (Bool.and (Nat.beq (:kind e) ek-wait) (Nat.beq (:creditor e) 0)))
  (simp only [t22-host-unawait hf hk refuse]) (exact h)
  (simp only [t22-host-unawait hf hk accept]) (exact (well-formed-remove-edge w x h)))

(a/theorem t22-host-unawait-refuse [w :- World, x :- Nat]
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
(a/defn t8-observe-any-kind [w :- World, d :- Nat, cb :- Nat, fresh :- Nat] Outcome
  (if (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb)))
      (accept (observe-raw w d cb))
      (refuse w)))

(a/theorem well-formed-t8-observe-any-kind [w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t8-observe-any-kind w d cb fresh))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
  (simp only [t8-observe-any-kind hg refuse]) (exact h)
  (have he (= (edge-ok-in w (observe-edge w d cb)) true))
  (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
  (have h1 := (well-formed-demand-reactive _ d (well-formed-insert-edge-fresh w (observe-edge w d cb) he h)))
  (simp only [t8-observe-any-kind hg accept observe-raw])
  (cases hr (deb-ready (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) d))
  (simp only [hr]) (exact h1)
  (simp only [hr]) (exact (well-formed-fire-edge _ _ (:next-id w) h1)))

(a/theorem t8-observe-any-kind-refuse [w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (:accepted (t8-observe-any-kind w d cb fresh)) false) (= (:world (t8-observe-any-kind w d cb fresh)) w))
  (intro ha)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
  (simp only [t8-observe-any-kind hg refuse])
  (simp [t8-observe-any-kind hg accept] at ha))

;; ---- the scheduling choice (D0): an active normal run without the slice gets it, when no
;; run holds one (cleanup slices of unwinding runs are not modelled)
(a/defn run-enter-row [r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) (:act r) (:mode r) true
             (:effect-index r) (:finalizers r) (:resources r)))
(a/theorem run-enter-row-id [r :- RunRow] (= (run-id (run-enter-row r)) (run-id r)) (rfl))
(a/defn run-slice [r :- RunRow] Bool (:slice r))
(a/defn schedule-ok [w :- World, r :- RunRow] Bool
  (Bool.and (Nat.beq (:act r) act-active)
   (Bool.and (Nat.beq (:mode r) mode-normal)
    (Bool.and (Bool.not (:slice r)) (Bool.not (tbl-any run-slice (:runs w)))))))
(a/defn t-schedule [w :- World, rid :- Nat] Outcome
  (match (run-find w rid)
    [none (refuse w)]
    [(some r) (if (schedule-ok w r) (accept (run-upd w rid run-enter-row)) (refuse w))]))

(a/theorem well-formed-t-schedule [w :- World, rid :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-schedule w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-schedule hf refuse]) (exact h)
  (cases hg (schedule-ok w r))
  (simp only [t-schedule hf hg refuse]) (exact h)
  (simp only [t-schedule hf hg accept]) (exact (well-formed-run-upd w rid run-enter-row run-enter-row-id h)))

(a/theorem t-schedule-refuse [w :- World, rid :- Nat]
  (=> (= (:accepted (t-schedule w rid)) false) (= (:world (t-schedule w rid)) w))
  (intro ha)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-schedule hf refuse])
  (cases hg (schedule-ok w r))
  (simp only [t-schedule hf hg refuse])
  (simp [t-schedule hf hg accept] at ha))

;; ---- handle-new x (Z#29): a row's handle count goes from 0 to 1 (computation, task, source
;; or publication, searched in that order); any other count, or no row, refuses; so does a
;; tombstone (engine: handle! on an existing row only runs through adoption, which finds the row
;; through a reference, and a tombstone has none)
(a/defn comp-first-handle [c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) 1 (:tomb c)))
(a/defn task-first-handle [t :- TaskRow] TaskRow (TaskRow.mk (:id t) (:owner t) (:run t) (:result t) 1 (:inputs t) (:local t)))
(a/defn source-first-handle [s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) (:owner s) (:kind s) (:state s) (:version s) (:open s) 1 (:queue s) (:rtask s) (:next s) (:tail s) (:fail s) (:max s)))
(a/defn pub-first-handle [p :- PubRow] PubRow (PubRow.mk (:id p) (:edge p) (:basis p) 1))
(a/theorem comp-first-handle-id [c :- CompRow] (= (comp-id (comp-first-handle c)) (comp-id c)) (rfl))
(a/theorem comp-first-handle-pending [c :- CompRow] (= (:pending (comp-first-handle c)) (:pending c)) (rfl))
(a/theorem task-first-handle-id [t :- TaskRow] (= (task-id (task-first-handle t)) (task-id t)) (rfl))
(a/theorem source-first-handle-id [s :- SourceRow] (= (source-id (source-first-handle s)) (source-id s)) (rfl))
(a/theorem pub-first-handle-id [p :- PubRow] (= (pub-id (pub-first-handle p)) (pub-id p)) (rfl))

(a/defn new-pub-handle [w :- World, x :- Nat] Outcome
  (match (pub-find w x) [none (refuse w)]
         [(some p) (if (Nat.beq (:handles p) 0) (accept (pub-upd w x pub-first-handle)) (refuse w))]))
(a/defn new-source-handle [w :- World, x :- Nat] Outcome
  (match (source-find w x) [none (new-pub-handle w x)]
         [(some s) (if (Nat.beq (:handles s) 0) (accept (source-upd w x source-first-handle)) (refuse w))]))
(a/defn new-task-handle [w :- World, x :- Nat] Outcome
  (match (task-find w x) [none (new-source-handle w x)]
         [(some t) (if (Nat.beq (:handles t) 0) (accept (task-upd w x task-first-handle)) (refuse w))]))
(a/defn t-handle-new [w :- World, x :- Nat] Outcome
  (match (comp-find w x) [none (new-task-handle w x)]
         [(some c) (if (Nat.beq (:handles c) 0) (if (:tomb c) (refuse w) (accept (comp-upd w x comp-first-handle))) (refuse w))]))

(defmacro ^:private defnew-lemmas
  [f find upd row-f inv-lemma inv-args next-f & [tomb?]]
  (let [inv (symbol (str "well-formed-" f)) ref (symbol (str f "-refuse"))
        next-inv (when next-f (symbol (str "well-formed-" next-f))) next-ref (when next-f (symbol (str next-f "-refuse")))]
    `(do
       (a/theorem ~inv [~'w :- ~'World, ~'x :- ~'Nat]
         (~'=> (~'= (~'well-formed ~'w) true) (~'= (~'well-formed (:world (~f ~'w ~'x))) true))
         (~'intro ~'h)
         (~'cases ~'hc (~find ~'w ~'x)) (~'case' [~'some ~'c]) (~'case' [~'none])
         ~@(if next-f
             [`(~'simp ~'only [~f ~'hc]) `(~'exact (~next-inv ~'w ~'x ~'h))]
             [`(~'simp ~'only [~f ~'hc ~'refuse]) `(~'exact ~'h)])
         (~'cases ~'hn (~'Nat.beq (:handles ~'c) 0))
         (~'simp ~'only [~f ~'hc ~'hn ~'refuse]) (~'exact ~'h)
         ~@(if tomb?
             [`(~'cases ~'ht (:tomb ~'c))
              `(~'simp ~'only [~f ~'hc ~'hn ~'ht ~'accept])
              `(~'exact (~inv-lemma ~'w ~'x ~row-f ~@inv-args ~'h))
              `(~'simp ~'only [~f ~'hc ~'hn ~'ht ~'refuse]) `(~'exact ~'h)]
             [`(~'simp ~'only [~f ~'hc ~'hn ~'accept])
              `(~'exact (~inv-lemma ~'w ~'x ~row-f ~@inv-args ~'h))]))
       (a/theorem ~ref [~'w :- ~'World, ~'x :- ~'Nat]
         (~'=> (~'= (:accepted (~f ~'w ~'x)) false) (~'= (:world (~f ~'w ~'x)) ~'w))
         (~'intro ~'ha)
         (~'cases ~'hc (~find ~'w ~'x)) (~'case' [~'some ~'c]) (~'case' [~'none])
         ~@(if next-f
             [`(~'simp ~'only [~f ~'hc] ~'at ~'ha) `(~'simp ~'only [~f ~'hc]) `(~'exact (~next-ref ~'w ~'x ~'ha))]
             [`(~'simp ~'only [~f ~'hc ~'refuse])])
         (~'cases ~'hn (~'Nat.beq (:handles ~'c) 0))
         (~'simp ~'only [~f ~'hc ~'hn ~'refuse])
         ~@(if tomb?
             [`(~'cases ~'ht (:tomb ~'c))
              `(~'simp [~f ~'hc ~'hn ~'ht ~'accept] ~'at ~'ha)
              `(~'simp ~'only [~f ~'hc ~'hn ~'ht ~'refuse])]
             [`(~'simp [~f ~'hc ~'hn ~'accept] ~'at ~'ha)])))))

(defnew-lemmas new-pub-handle pub-find pub-upd pub-first-handle well-formed-pub-upd [pub-first-handle-id] nil)
(defnew-lemmas new-source-handle source-find source-upd source-first-handle well-formed-source-upd [source-first-handle-id] new-pub-handle)
(defnew-lemmas new-task-handle task-find task-upd task-first-handle well-formed-task-upd [task-first-handle-id] new-source-handle)
(defnew-lemmas t-handle-new comp-find comp-upd comp-first-handle well-formed-comp-upd [comp-first-handle-id comp-first-handle-pending] new-task-handle true)

;; ---- `any` and `all` losers (T6, Z#61): when an `any` activation resumed, or an `all` one
;; failed fast (its row is gone and its run is not done), the tasks R created for this await
;; (`spawned`, from the item) that are still running and have no other creditor (no edge names
;; them) are cancelled (T14, cascade). Applied after every accepted raw transition (`then-cancel-losers`), by
;; comparing the activations before and after. The engine (`resume-at-fill!`) cancels for an
;; `all` only when a slot failed (A-WINNER); the model does not tell the two ways an `all` row
;; goes, and need not: an `all` that resumed with every slot filled has no running member task
;; (a task fills its slot when it completes, T12, whose run is done by then).
(a/defn loser-task [w1 :- World, s :- Nat, k :- Nat] Bool
  (Bool.and (tbl-all (no-debtor k) (:edges w1))
            (match (task-find w1 k) [none false]
                   [(some t) (Bool.and (Nat.beq (:owner t) s) (opt-test run-alive (run-find w1 (:run t))))])))
(a/defn run-of-task [w1 :- World, r :- RunRow] Bool (task-has w1 (:of r)))
(a/defn group-mode [m :- Nat] Bool (Bool.or (Nat.beq m am-any) (Nat.beq m am-all)))
(a/defn any-resolved [w1 :- World, a :- ActRow] Bool
  (Bool.and (group-mode (:mode a))
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

(a/theorem well-formed-bump [w :- World]
  (=> (= (well-formed w) true) (= (well-formed (bump w)) true))
  (intro h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (well-formed-parts w h))
  (exact (well-formed-intro (bump w) (Eq.trans (pending-exact-bump w) (And.left hs))
           (Eq.trans (edges-ref-ok-bump w) (And.left (And.right hs)))
           (ids-ok-bump w (And.right (And.right hs))))))

(a/theorem well-formed-set-released [w :- World, v :- Bool]
  (=> (= (well-formed w) true) (= (well-formed (set-released w v)) true))
  (intro h) (exact h))
(a/theorem well-formed-set-pending-act [w :- World, v :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (set-pending-act w v)) true))
  (intro h) (exact h))

;; ---- source rows
(a/defn source-bump [s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) (:owner s) (:kind s) (:state s) (+ (:version s) 1) (:open s) (:handles s) (:queue s)
                (:rtask s) (:next s) (:tail s) (:fail s) (:max s)))
(a/defn source-enqueue [v :- Nat, s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) (:owner s) (:kind s) (:state s) (:version s) (:open s) (:handles s)
                (List.append Nat (:queue s) (List.cons Nat v (List.nil Nat)))
                (:rtask s) (:next s) (:tail s) (:fail s) (:max s)))
(a/defn source-permit [s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) (:owner s) (:kind s) (+ (:state s) 1) (:version s) (:open s) (:handles s) (:queue s)
                (:rtask s) (:next s) (:tail s) (:fail s) (:max s)))
(a/defn nat-tail [xs :- (List Nat)] (List Nat) (match xs [nil (List.nil Nat)] [(cons h t) t]))
;; take's immediate path: a mailbox drops its head message, a semaphore one permit; version + 1 (as the
;; engine). Nothing left (reached only on a closed source, Z#57: the take fails with err ::closed): unchanged.
(a/defn source-available [s :- SourceRow] Bool
  (if (Nat.beq (:kind s) sk-mailbox) (Bool.not (nats-empty (:queue s))) (Nat.blt 0 (:state s))))
(a/defn source-consume [s :- SourceRow] SourceRow
  (if (source-available s)
      (if (Nat.beq (:kind s) sk-mailbox)
          (SourceRow.mk (:id s) (:owner s) (:kind s) (:state s) (+ (:version s) 1) (:open s) (:handles s) (nat-tail (:queue s))
                       (:rtask s) (:next s) (:tail s) (:fail s) (:max s))
          (SourceRow.mk (:id s) (:owner s) (:kind s) (- (:state s) 1) (+ (:version s) 1) (:open s) (:handles s) (:queue s)
                (:rtask s) (:next s) (:tail s) (:fail s) (:max s)))
      s))
(a/theorem source-bump-id [s :- SourceRow] (= (source-id (source-bump s)) (source-id s)) (rfl))
(a/theorem source-enqueue-id [v :- Nat, s :- SourceRow] (= (source-id (source-enqueue v s)) (source-id s)) (rfl))
(a/theorem source-permit-id [s :- SourceRow] (= (source-id (source-permit s)) (source-id s)) (rfl))
(a/theorem source-consume-id [s :- SourceRow] (= (source-id (source-consume s)) (source-id s))
  (cases ha (source-available s)) (all_goals (cases h (Nat.beq (:kind s) sk-mailbox)))
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
  (t10-finalize-debtor (nat-fold (fire-edge (RunResult.mk res-ok v)) (deliver-fire w x v) (waits-on x (:edges w))) x))
(a/theorem well-formed-deliver-fire [w :- World, x :- Nat, v :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (deliver-fire w x v)) true))
  (intro h)
  (simp only [deliver-fire])
  (exact (well-formed-nat-fold (fire-edge (RunResult.mk res-ok v)) (well-formed-fire-edge (RunResult.mk res-ok v))
           (edges-onto x (:edges w)) _
           (well-formed-source-upd w x (source-write v) (source-write-source-id v) h))))
(a/defn t-deliver [w :- World, x :- Nat, v :- Nat] Outcome
  (match (source-find w x)
    [none (refuse w)]
    [(some s) (if (deliverable s) (accept (deliver-raw w x v)) (refuse w))]))

(a/theorem well-formed-t-deliver [w :- World, x :- Nat, v :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-deliver w x v))) true))
  (intro h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-deliver hs refuse]) (exact h)
  (cases hg (deliverable s))
  (simp only [t-deliver hs hg refuse]) (exact h)
  (simp only [t-deliver hs hg accept deliver-raw])
  (exact (well-formed-t10-finalize-debtor _ x (well-formed-nat-fold (fire-edge (RunResult.mk res-ok v)) (well-formed-fire-edge (RunResult.mk res-ok v))
                                    _ _ (well-formed-deliver-fire w x v h)))))

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
;; Z#62: a release at the semaphore's maximum (`max`, its permit count at creation) is refused
;; (engine `sem-release!`: logged `[:release x]` refused, and the host call throws)
(a/defn releasable [s :- SourceRow] Bool
  (Bool.and (open-kind sk-semaphore s) (Nat.blt (:state s) (:max s))))
(a/theorem releasable-open [s :- SourceRow] (=> (= (releasable s) true) (= (open-kind sk-semaphore s) true))
  (intro h) (simp only [releasable Bool.and_eq_true] at h) (exact (And.left h)))
(a/defn t-release [w :- World, x :- Nat] Outcome
  (match (source-find w x)
    [none (refuse w)]
    [(some s) (if (releasable s) (accept (release-raw w x)) (refuse w))]))

(a/theorem well-formed-serve-or [w :- World, x :- Nat, res :- RunResult, keep :- (=> SourceRow SourceRow),
                         hk :- (forall [s :- SourceRow] (= (source-id (keep s)) (source-id s)))]
  (=> (= (well-formed w) true) (= (well-formed (serve-or w x res keep)) true))
  (intro h)
  (cases hz (Nat.beq (oldest-waiter w x) 0))
  (simp only [serve-or hz]) (exact (well-formed-fire-edge res w _ h))
  (simp only [serve-or hz]) (exact (well-formed-source-upd w x keep hk h)))

(a/theorem well-formed-t-post [w :- World, x :- Nat, v :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-post w x v))) true))
  (intro h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-post hs refuse]) (exact h)
  (cases hg (open-kind sk-mailbox s))
  (simp only [t-post hs hg refuse]) (exact h)
  (simp only [t-post hs hg accept post-raw])
  (exact (well-formed-serve-or _ x _ (source-enqueue v) (source-enqueue-id v) (well-formed-source-upd w x source-bump source-bump-id h))))

(a/theorem t-post-refuse [w :- World, x :- Nat, v :- Nat]
  (=> (= (:accepted (t-post w x v)) false) (= (:world (t-post w x v)) w))
  (intro ha)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-post hs refuse])
  (cases hg (open-kind sk-mailbox s))
  (simp only [t-post hs hg refuse])
  (simp [t-post hs hg accept] at ha))

(a/theorem well-formed-t-release [w :- World, x :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-release w x))) true))
  (intro h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-release hs refuse]) (exact h)
  (cases hg (releasable s))
  (simp only [t-release hs hg refuse]) (exact h)
  (simp only [t-release hs hg accept release-raw])
  (exact (well-formed-serve-or _ x _ source-permit source-permit-id (well-formed-source-upd w x source-bump source-bump-id h))))

(a/theorem t-release-refuse [w :- World, x :- Nat]
  (=> (= (:accepted (t-release w x)) false) (= (:world (t-release w x)) w))
  (intro ha)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-release hs refuse])
  (cases hg (releasable s))
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
(a/defn take-ready [s :- SourceRow] Bool (Bool.or (source-available s) (Bool.not (:open s))))
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

(a/theorem well-formed-take-park [w :- World, r :- RunRow, x :- Nat, k :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (take-park w r x k)) true))
  (intro h)
  (simp only [take-park])
  (exact (well-formed-run-upd _ (:id r) run-tick-park run-tick-park-id
           (well-formed-insert-edge-checked _ _ (well-formed-act-ins-fresh w (take-act w r k) (rfl) h)))))

(a/theorem well-formed-take-now [w :- World, r :- RunRow, x :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (take-now w r x)) true))
  (intro h)
  (simp only [take-now])
  (exact (well-formed-bump _ (well-formed-bump _ (well-formed-run-upd _ (:id r) run-tick run-tick-run-id
                                   (well-formed-source-upd w x source-consume source-consume-id h))))))

(a/theorem well-formed-t-take [w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-take w st x k fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-take ht refuse]) (exact h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-take ht hs refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (takeable s))))
  (simp only [t-take ht hs hg refuse]) (exact h)
  (cases hv (take-ready s))
  (simp only [t-take ht hs hg hv accept]) (exact (well-formed-take-park w r x k h))
  (simp only [t-take ht hs hg hv accept]) (exact (well-formed-take-now w r x h)))

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
;; C1: `await-op` arms a resource of kind op (its start/cancel arbitration and hooks are the
;; engine's: the log shows arm, fire (the op's result) and acknowledgement). Z#63: an `external` resource has the
;; same lifecycle (arm, then a one-shot completion fire + ack, accepted after release; its cancel leaves the physical
;; completion outstanding): admitted too (C1c stage B sample 35, the first external arm in a sample)
(a/defn arm-kind-ok [kind :- Nat] Bool
  (Bool.or (Nat.beq kind rk-timer) (Bool.or (Nat.beq kind rk-offload) (Bool.or (Nat.beq kind rk-op) (Nat.beq kind rk-external)))))
(a/defn arm-park [w :- World, r :- RunRow, kind :- Nat, k :- Nat] World
  (take-park (arm-raw w r kind) (run-arm (:next-id w) r) (:next-id w) k))
(a/defn t17-arm [w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (if (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind)))
                  (accept (arm-park w r kind k))
                  (refuse w))]))

(a/theorem well-formed-arm-park [w :- World, r :- RunRow, kind :- Nat, k :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (arm-park w r kind k)) true))
  (intro h)
  (simp only [arm-park])
  (exact (well-formed-take-park _ (run-arm (:next-id w) r) (:next-id w) k (well-formed-arm-raw w r kind h))))

(a/theorem well-formed-t17-arm [w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t17-arm w st kind k fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t17-arm ht refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind))))
  (simp only [t17-arm ht hg refuse]) (exact h)
  (simp only [t17-arm ht hg accept]) (exact (well-formed-arm-park w r kind k h)))

(a/theorem t17-arm-refuse [w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (:accepted (t17-arm w st kind k fresh)) false) (= (:world (t17-arm w st kind k fresh)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t17-arm ht refuse])
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind))))
  (simp only [t17-arm ht hg refuse])
  (simp [t17-arm ht hg accept] at ha))

(a/theorem t17-arm-l4 [w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (run-tok-ok w st) false) (= (:world (t17-arm w st kind k fresh)) w))
  (intro hf) (simp only [t17-arm (run-tok-none w st hf) refuse]))

;; ---- finally regions (B3). `finally-enter st`: a normal run opens a region (innermost first,
;; at = effect-index; the engine holds its refs implicitly, so refs = []);
;; B8: a cleanup slice adds none. `finally-exit st`: the head region closes. For an unwinding
;; run this ends its cleanup slice (B8: a single slice per finalizer): slice := false, then T13
;; (`t13-retire`). Neither is an effect: effect-index is unchanged (engine items
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
;; C1 (B8 for normal runs): a region's block runs between its `finally-exit` and the matching
;; `finally-leave` (engine R-INFIN). `finally-exit` replaces the head region (F 0) by a running
;; clause (F 1, at = effect-index, refs []); `finally-leave` pops the head clause. So the list
;; nests regions and running clauses as the CPS body does; the engine's R-FINS is the number of
;; regions (`fin-region`), R-INFIN the number of clauses (`fin-running`).
(a/defn fin-running [fz :- Finalizer] Bool (Bool.not (Nat.beq (:f fz) 0)))
(a/defn finally-exit-refused [fs :- (List Finalizer)] Bool (match fs [nil true] [(cons h t) (fin-running h)]))
(a/defn finally-leave-refused [fs :- (List Finalizer)] Bool (match fs [nil true] [(cons h t) (fin-region h)]))
(a/defn fin-mark [r :- RunRow] Finalizer (Finalizer.mk 1 (:effect-index r) (List.nil Nat)))
(a/defn fins-exit [m :- Finalizer, fs :- (List Finalizer)] (List Finalizer)
  (match fs [nil (List.nil Finalizer)] [(cons h t) (List.cons Finalizer m t)]))
(a/defn run-fin-exit [r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) (:act r) (:mode r) (:slice r)
             (:effect-index r) (fins-exit (fin-mark r) (:finalizers r)) (:resources r)))
(a/theorem run-fin-exit-id [r :- RunRow] (= (run-id (run-fin-exit r)) (run-id r)) (rfl))
(a/defn run-in-finally [r :- RunRow] Bool (tbl-any fin-running (:finalizers r)))

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
    [(some r) (if (finally-exit-refused (:finalizers r)) (refuse w) (accept (run-upd w (:id r) run-fin-exit)))]))
(a/defn t-finally-leave [w :- World, st :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (if (finally-leave-refused (:finalizers r)) (refuse w) (accept (run-upd w (:id r) run-fin-pop)))]))

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
    [(some r) (if (exit-ready r) (accept (t13-retire (run-upd w rid run-fin-pop-end) rid)) (refuse w))]))

(a/theorem well-formed-t-finally-enter [w :- World, st :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-finally-enter w st))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-enter ht refuse]) (exact h)
  (cases hg (run-normal r))
  (simp only [t-finally-enter ht hg refuse]) (exact h)
  (simp only [t-finally-enter ht hg accept]) (exact (well-formed-run-upd w (:id r) _ (run-fin-push-id _) h)))

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

(a/theorem well-formed-t-finally-exit [w :- World, st :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-finally-exit w st))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-exit ht refuse]) (exact h)
  (cases he (finally-exit-refused (:finalizers r)))
  (case [true] (simp only [t-finally-exit ht he refuse]) (exact h))
  (case [false] (simp only [t-finally-exit ht he accept]) (exact (well-formed-run-upd w (:id r) run-fin-exit run-fin-exit-id h))))

(a/theorem t-finally-exit-refuse [w :- World, st :- Nat]
  (=> (= (:accepted (t-finally-exit w st)) false) (= (:world (t-finally-exit w st)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-exit ht refuse])
  (cases he (finally-exit-refused (:finalizers r)))
  (case [true] (simp only [t-finally-exit ht he refuse]))
  (case [false] (simp [t-finally-exit ht he accept] at ha)))

(a/theorem well-formed-t-finally-leave [w :- World, st :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-finally-leave w st))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-leave ht refuse]) (exact h)
  (cases he (finally-leave-refused (:finalizers r)))
  (case [true] (simp only [t-finally-leave ht he refuse]) (exact h))
  (case [false] (simp only [t-finally-leave ht he accept]) (exact (well-formed-run-upd w (:id r) run-fin-pop run-fin-pop-id h))))

(a/theorem t-finally-leave-refuse [w :- World, st :- Nat]
  (=> (= (:accepted (t-finally-leave w st)) false) (= (:world (t-finally-leave w st)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-leave ht refuse])
  (cases he (finally-leave-refused (:finalizers r)))
  (case [true] (simp only [t-finally-leave ht he refuse]))
  (case [false] (simp [t-finally-leave ht he accept] at ha)))

(a/theorem well-formed-t-slice-exit [w :- World, rid :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-slice-exit w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-slice-exit hf refuse]) (exact h)
  (cases hg (exit-ready r))
  (simp only [t-slice-exit hf hg refuse]) (exact h)
  (simp only [t-slice-exit hf hg accept t13-retire])
  (exact (well-formed-run-cascade _ _ (well-formed-run-upd w rid run-fin-pop-end run-fin-pop-end-id h))))

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
(a/theorem t-finally-leave-l4 [w :- World, st :- Nat]
  (=> (= (run-tok-ok w st) false) (= (:world (t-finally-leave w st)) w))
  (intro hf) (simp only [t-finally-leave (run-tok-none w st hf) refuse]))

;; ---- finalize R (B3, B8): the scheduling choice for a cleanup slice. R is done and unwinding
;; with an open finally region, holds no slice, and no run holds one (D0): R gets the slice;
;; its token is then valid for the head finalizer's cleanup slice (§2), which may write,
;; deliver, post, release and arm, and ends with `finally-exit` (B8: it cannot park, spawn or
;; create computations; await/take/complete need a normal run, spawn/create-comp are refused
;; in transition)
(a/defn cleanup-ready [w :- World, r :- RunRow] Bool
  (Bool.and (Nat.beq (:act r) act-done)
   (Bool.and (run-unwinding r)
    (Bool.and (Bool.not (fins-empty (:finalizers r)))
     (Bool.and (Bool.not (:slice r)) (Bool.not (tbl-any run-slice (:runs w))))))))
(a/defn t-finalize [w :- World, rid :- Nat] Outcome
  (match (run-find w rid)
    [none (refuse w)]
    [(some r) (if (cleanup-ready w r) (accept (run-upd w rid run-enter-row)) (refuse w))]))

(a/theorem well-formed-t-finalize [w :- World, rid :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-finalize w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-finalize hf refuse]) (exact h)
  (cases hg (cleanup-ready w r))
  (simp only [t-finalize hf hg refuse]) (exact h)
  (simp only [t-finalize hf hg accept]) (exact (well-formed-run-upd w rid run-enter-row run-enter-row-id h)))

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
;; C1: a done (unretired) task run that holds no slice is still cancellable (engine `cancel-task!`
;; commits `[:cancel r]` while K.run names it): T14 is idempotent on the run itself, and the
;; cancellation reaches its run scope's subtree at once (R4): the alive runs owned there are
;; cancelled (none, unless work was moved into a scope it still holds). Its fired, unacknowledged
;; await-op has its controller cancelled by the engine (the acknowledgement follows as T15).
(a/defn host-cancel-done [w :- World, r :- RunRow] Bool
  (Bool.and (Bool.not (run-alive r)) (Bool.and (Bool.not (:slice r)) (task-has w (:of r)))))
(a/defn cancel-done [w :- World, r :- RunRow] Outcome
  (if (host-cancel-done w r)
      (accept (run-cascade w (cancel-jobs (owned-runs w (scope-subtree w (:scope r))))))
      (refuse w)))
(a/defn t14-host-cancel [w :- World, rid :- Nat] Outcome
  (match (run-find w rid)
    [none (refuse w)]
    [(some r) (if (host-cancel-ok w r) (t14-cancel w rid false) (cancel-done w r))]))

(a/theorem well-formed-t14-host-cancel [w :- World, rid :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t14-host-cancel w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t14-host-cancel hf refuse]) (exact h)
  (cases hg (host-cancel-ok w r))
  (cases hd (host-cancel-done w r))
  (simp only [t14-host-cancel hf hg cancel-done hd refuse]) (exact h)
  (simp only [t14-host-cancel hf hg cancel-done hd accept]) (exact (well-formed-run-cascade w _ h))
  (simp only [t14-host-cancel hf hg]) (exact (well-formed-t14-cancel w rid false h)))

(a/theorem t14-host-cancel-refuse [w :- World, rid :- Nat]
  (=> (= (:accepted (t14-host-cancel w rid)) false) (= (:world (t14-host-cancel w rid)) w))
  (intro ha)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t14-host-cancel hf refuse])
  (cases hg (host-cancel-ok w r))
  (cases hd (host-cancel-done w r))
  (simp only [t14-host-cancel hf hg cancel-done hd refuse])
  (simp [t14-host-cancel hf hg cancel-done hd accept] at ha)
  (simp only [t14-host-cancel hf hg] at ha) (simp only [t14-host-cancel hf hg]) (exact (t14-cancel-refuse w rid false ha)))

;; ---- open-scope st s / close-scope s (T16, with-scope): open allocates the explicit scope
;; s = fresh as a child of the run's current scope (a body effect of a normal run; not an
;; effect index step, as the engine); close is T16 on an explicit scope (the engine logs it
;; without a token at the end of with-scope; closing a closed scope repeats the cascade)
;; the run's current scope must exist (it always does: a run's scope exists, I1; the guard keeps
;; the new scope's parent existing without that invariant, literal I1 proof spindel.v2.inv.i1-scopes)
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

(a/theorem well-formed-t-open-scope [w :- World, st :- Nat, s :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-open-scope w st s))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-open-scope ht refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq s (:next-id w)) (open-ok w r)))
  (simp only [t-open-scope ht hg refuse]) (exact h)
  (have hs (= s (:next-id w))) (simp only [Bool.and_eq_true Nat.beq_eq] at hg) (exact (And.left hg))
  (simp only [t-open-scope ht hg accept])
  (exact (well-formed-scope-ins-fresh w (ScopeRow.mk s (cur-scope w r) scope-explicit true) hs h)))

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

(a/theorem well-formed-t-close-scope [w :- World, s :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-close-scope w s))) true))
  (intro h)
  (cases hg (scope-explicit-at w s))
  (simp only [t-close-scope hg refuse]) (exact h)
  (simp only [t-close-scope hg]) (exact (well-formed-t16-close-scope w s h)))

(a/theorem t-close-scope-refuse [w :- World, s :- Nat]
  (=> (= (:accepted (t-close-scope w s)) false) (= (:world (t-close-scope w s)) w))
  (intro ha)
  (cases hg (scope-explicit-at w s))
  (simp only [t-close-scope hg refuse])
  (simp only [t-close-scope hg] at ha) (simp only [t-close-scope hg]) (exact (t16-close-scope-refuse w s ha)))

;; ---- detach k s (Q10, §5.2): a task that has not completed and is owned by a scope is
;; re-owned to the open scope s (it outlives its creator), and its run scope is re-parented
;; under s (Z#41, Z#26); the old owner's subtree is then removed when it became empty (W#9;
;; engine `remove-scope-if-empty!`)
(a/defn task-set-owner [s :- Nat, t :- TaskRow] TaskRow
  (TaskRow.mk (:id t) s (:run t) (:result t) (:handles t) (:inputs t) (:local t)))
(a/theorem task-set-owner-id [s :- Nat, t :- TaskRow] (= (task-id (task-set-owner s t)) (task-id t)) (rfl))
(a/defn scope-set-parent [p :- Nat, s :- ScopeRow] ScopeRow (ScopeRow.mk (:id s) p (:kind s) (:open s)))
(a/theorem scope-set-parent-id [p :- Nat, s :- ScopeRow] (= (scope-id (scope-set-parent p s)) (scope-id s)) (rfl))
(a/defn task-run-scope [w :- World, t :- TaskRow] Nat (match (run-find w (:run t)) [none 0] [(some r) (:scope r)]))
(a/defn detach-move [w :- World, k :- Nat, s :- Nat, rs :- Nat] World
  (scope-upd (task-upd w k (task-set-owner s)) rs (scope-set-parent s)))
(a/defn remove-empty-at [w :- World, o :- Nat] World (remove-if-empty w (scope-subtree w o)))
;; Z#69: whether scope a is s or on s's parent chain (engine `within?`): the chain is s's
;; `scope-ancestors` (retain, the worklist over the parent fields that Rule R's cleanup uses)
(a/defn scope-within [w :- World, s :- Nat, a :- Nat] Bool
  (Bool.or (Nat.beq s a) (reach-mem a (scope-ancestors w s))))
;; Z#69: s must not lie in the task's own run-scope subtree (else re-parenting the run scope under
;; s closes a cycle of parents, and neither scope is ever removed)
(a/defn detach-ok [w :- World, t :- TaskRow, s :- Nat] Bool
  (Bool.and (Nat.beq (:tag (:result t)) res-none)
    (Bool.and (scope-has w (:owner t))
      (Bool.and (scope-open-at w s) (Bool.not (scope-within w s (task-run-scope w t)))))))
(a/defn t-detach [w :- World, k :- Nat, s :- Nat] Outcome
  (match (task-find w k)
    [none (refuse w)]
    [(some t) (if (detach-ok w t s)
                  (accept (remove-empty-at (detach-move w k s (task-run-scope w t)) (:owner t)))
                  (refuse w))]))

(a/theorem well-formed-t-detach [w :- World, k :- Nat, s :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-detach w k s))) true))
  (intro h)
  (cases hf (task-find w k)) (case' [some t]) (case' [none])
  (simp only [t-detach hf refuse]) (exact h)
  (cases hg (detach-ok w t s))
  (simp only [t-detach hf hg refuse]) (exact h)
  (simp only [t-detach hf hg accept remove-empty-at detach-move])
  (exact (well-formed-remove-if-empty _ _ (well-formed-scope-upd _ _ (scope-set-parent s) (scope-set-parent-id s)
                                    (well-formed-task-upd w k (task-set-owner s) (task-set-owner-id s) h)))))

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
(a/defn comp-no-handles [c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) 0 (:tomb c)))
(a/defn task-no-handles [t :- TaskRow] TaskRow (TaskRow.mk (:id t) (:owner t) (:run t) (:result t) 0 (:inputs t) (:local t)))
(a/defn source-no-handles [s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) (:owner s) (:kind s) (:state s) (:version s) (:open s) 0 (:queue s) (:rtask s) (:next s) (:tail s) (:fail s) (:max s)))
(a/defn pub-no-handles [p :- PubRow] PubRow (PubRow.mk (:id p) (:edge p) (:basis p) 0))
(a/theorem comp-no-handles-id [c :- CompRow] (= (comp-id (comp-no-handles c)) (comp-id c)) (rfl))
(a/theorem comp-no-handles-pending [c :- CompRow] (= (:pending (comp-no-handles c)) (:pending c)) (rfl))
(a/theorem task-no-handles-id [t :- TaskRow] (= (task-id (task-no-handles t)) (task-id t)) (rfl))
(a/theorem source-no-handles-id [s :- SourceRow] (= (source-id (source-no-handles s)) (source-id s)) (rfl))
(a/theorem pub-no-handles-id [p :- PubRow] (= (pub-id (pub-no-handles p)) (pub-id p)) (rfl))
(a/defn comp-zero-handles [w :- World, x :- Nat] World (comp-upd w x comp-no-handles))
(a/defn task-zero-handles [w :- World, x :- Nat] World (task-upd w x task-no-handles))
(a/defn source-zero-handles [w :- World, x :- Nat] World (source-upd w x source-no-handles))
(a/defn pub-zero-handles [w :- World, x :- Nat] World (pub-upd w x pub-no-handles))
(a/defn zero-handles [w :- World] World
  (nat-fold pub-zero-handles
    (nat-fold source-zero-handles
      (nat-fold task-zero-handles (nat-fold comp-zero-handles w (tbl-ids comp-id (:comps w))) (tbl-ids task-id (:tasks w)))
      (tbl-ids source-id (:sources w)))
    (tbl-ids pub-id (:pubs w))))
(a/defn revoke-roots [w :- World] World
  (set-pending-act (set-pins (drop-edges (set-released w true) not-host) (List.nil Nat)) 0))
(a/defn release-world-raw [w :- World] World
  (run-cascade (zero-handles (revoke-roots w)) (List.cons Job (Job.jclose root-scope-id) (List.nil Job))))
;; C1 world completion (T21, Z#67), layer 1 part: the world's unretired runs (the engine's W-RUNS:
;; +1 at run creation, -1 at T13; every task and computation run, cleanup included) and the local
;; test; a world is complete once released, with no run left and every owned child world complete
;; or collected (layer 2, the owner relation of spindel.v2.layer2.sys; an unborn instance released before
;; its activation is complete at once)
(a/defn world-runs [w :- World] Nat (List.length (:runs w)))
;; C1c stage B: and no fork marker (the engine's W-OWNED-N all zero and W-NORMALIZE empty, questions 15, 16)
(a/defn forks-nil [fs :- (List ForkRow)] Bool (match fs [nil true] [(cons h t) false]))
(a/defn world-quiet [w :- World] Bool (Bool.and (:released w) (Bool.and (Nat.beq (world-runs w) 0) (forks-nil (:forks w)))))

;; C1/E4: an unborn instance (layer 2, layer2/sys.clj `Cell.unborn`) released before its activation: nothing
;; in it runs, its copied work and finalizers included; the engine logs `[:release-world]` and only
;; sets the flag (the instance is complete at once, layer 2)
(a/defn release-unborn [w :- World] World (set-released w true))
(a/theorem well-formed-release-unborn [w :- World]
  (=> (= (well-formed w) true) (= (well-formed (release-unborn w)) true))
  (intro h) (simp only [release-unborn]) (exact (well-formed-set-released w true h)))

(a/defn t21-release-world [w :- World] Outcome
  (if (:released w) (refuse w) (accept (release-world-raw w))))

(a/theorem well-formed-zero-handles [w :- World]
  (=> (= (well-formed w) true) (= (well-formed (zero-handles w)) true))
  (intro h)
  (have hc (forall [w :- World, x :- Nat] (=> (= (well-formed w) true) (= (well-formed (comp-zero-handles w x)) true))))
  (intros w2 x h2) (exact (well-formed-comp-upd w2 x comp-no-handles comp-no-handles-id comp-no-handles-pending h2))
  (have ht (forall [w :- World, x :- Nat] (=> (= (well-formed w) true) (= (well-formed (task-zero-handles w x)) true))))
  (intros w2 x h2) (exact (well-formed-task-upd w2 x task-no-handles task-no-handles-id h2))
  (have hs (forall [w :- World, x :- Nat] (=> (= (well-formed w) true) (= (well-formed (source-zero-handles w x)) true))))
  (intros w2 x h2) (exact (well-formed-source-upd w2 x source-no-handles source-no-handles-id h2))
  (have hp (forall [w :- World, x :- Nat] (=> (= (well-formed w) true) (= (well-formed (pub-zero-handles w x)) true))))
  (intros w2 x h2) (exact (well-formed-pub-upd w2 x pub-no-handles pub-no-handles-id h2))
  (simp only [zero-handles])
  (exact (well-formed-nat-fold pub-zero-handles hp _ _ (well-formed-nat-fold source-zero-handles hs _ _
           (well-formed-nat-fold task-zero-handles ht _ _ (well-formed-nat-fold comp-zero-handles hc _ _ h))))))

(a/theorem well-formed-revoke-roots [w :- World]
  (=> (= (well-formed w) true) (= (well-formed (revoke-roots w)) true))
  (intro h)
  (simp only [revoke-roots])
  (exact (well-formed-set-pending-act _ 0 (well-formed-set-pins _ _ (well-formed-drop-edges _ not-host (well-formed-set-released w true h))))))

(a/theorem well-formed-t21-release-world [w :- World]
  (=> (= (well-formed w) true) (= (well-formed (:world (t21-release-world w))) true))
  (intro h)
  (cases hr (:released w))
  (simp only [t21-release-world hr accept release-world-raw])
  (exact (well-formed-run-cascade _ _ (well-formed-zero-handles _ (well-formed-revoke-roots w h))))
  (simp only [t21-release-world hr refuse]) (exact h))

(a/theorem t21-release-world-refuse [w :- World]
  (=> (= (:accepted (t21-release-world w)) false) (= (:world (t21-release-world w)) w))
  (intro ha)
  (cases hr (:released w))
  (simp [t21-release-world hr accept] at ha)
  (simp only [t21-release-world hr refuse]))

;; ---- T1 in a body (engine `[:create-source st kind v fresh]`): in a computation run, `fresh`
;; naming a source of C's basis or adoption basis adopts it (creation order; no allocation, the
;; kind must match; it moves to the basis at the new site, like a re-spawn); otherwise fresh =
;; next-id creates it, owned by the computation, or in a task run by the run's current scope
;; (reading B22), recorded in a computation's basis. Effect tick either way.
(a/defn source-owner-in-run [w :- World, r :- RunRow] Nat (if (in-comp w r) (:of r) (cur-scope w r)))
(a/defn readopt-source [w :- World, r :- RunRow, x :- Nat] (Option SourceRow)
  (match (comp-find w (:of r))
    [none (Option.none SourceRow)]
    [(some c) (if (reach-mem x (nat-app (created-ids (:basis c)) (created-ids (:adopt-basis c))))
                  (source-find w x) (Option.none SourceRow))]))
(a/defn create-source-in-run [w :- World, r :- RunRow, kind :- Nat, v :- Nat] World
  (run-upd (record-basis (bump (source-ins w (new-source (:next-id w) (source-owner-in-run w r) kind v))) r (:next-id w))
           (:id r) run-tick))
(a/defn t1-create-nonstream [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (match (readopt-source w r fresh)
                [none (if (Bool.and (Nat.beq fresh (:next-id w)) (source-kind-ok kind))
                          (accept (create-source-in-run w r kind v)) (refuse w))]
                [(some x) (if (Nat.beq (:kind x) kind) (accept (respawn-raw w r fresh)) (refuse w))])]))

(a/theorem well-formed-create-source-in-run [w :- World, r :- RunRow, kind :- Nat, v :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (create-source-in-run w r kind v)) true))
  (intro h)
  (simp only [create-source-in-run])
  (exact (well-formed-run-upd _ (:id r) run-tick run-tick-run-id
           (well-formed-record-basis _ r (:next-id w)
             (well-formed-source-ins-fresh w (new-source (:next-id w) (source-owner-in-run w r) kind v) (rfl) h)))))

(a/theorem well-formed-t1-create-nonstream [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t1-create-nonstream w st kind v fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t1-create-nonstream ht refuse]) (exact h)
  (cases ho (readopt-source w r fresh))
  (case [none]
    (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (source-kind-ok kind)))
    (case [false] (simp only [t1-create-nonstream ht ho hg refuse]) (exact h))
    (case [true] (simp only [t1-create-nonstream ht ho hg accept]) (exact (well-formed-create-source-in-run w r kind v h))))
  (case [some x]
    (cases hk (Nat.beq (:kind x) kind))
    (case [false] (simp only [t1-create-nonstream ht ho hk refuse]) (exact h))
    (case [true]
      (simp only [t1-create-nonstream ht ho hk accept respawn-raw])
      (exact (well-formed-run-upd _ (:id r) run-tick run-tick-run-id
               (well-formed-comp-upd w (:of r) _ (comp-rebasis-id _) (comp-rebasis-pending _) h))))))

(a/theorem t1-create-nonstream-refuse [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (:accepted (t1-create-nonstream w st kind v fresh)) false) (= (:world (t1-create-nonstream w st kind v fresh)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t1-create-nonstream ht refuse])
  (cases ho (readopt-source w r fresh))
  (case [none]
    (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (source-kind-ok kind)))
    (case [false] (simp only [t1-create-nonstream ht ho hg refuse]))
    (case [true] (simp [t1-create-nonstream ht ho hg accept] at ha)))
  (case [some x]
    (cases hk (Nat.beq (:kind x) kind))
    (case [false] (simp only [t1-create-nonstream ht ho hk refuse]))
    (case [true] (simp [t1-create-nonstream ht ho hk accept] at ha))))

;; ---- B8 for spawn and create-comp: refused in a cleanup slice (a valid token of an
;; unwinding run)
(a/defn in-cleanup [w :- World, st :- Nat] Bool (opt-test run-unwinding (tok-run w st)))
;; I8 (spindel.v2.inv.i8): a task run spawns a task / creates a source owned by its current scope; refused
;; when that scope is not open. A reachable-equivalent guard (an alive task run's current scope is
;; open: tripwire `cur-open-ok` on the random drivers and the oracle; its proof is obligation P10) that
;; keeps I8's proof local: no new task or source is owned by a closed scope.
(a/defn run-cur-closed [w :- World, r :- RunRow] Bool
  (Bool.and (Bool.not (in-comp w r)) (Bool.not (scope-open-at w (cur-scope w r)))))
(a/defn cur-closed [w :- World, st :- Nat] Bool (opt-test (run-cur-closed w) (tok-run w st)))
;; C1 (Q5, Q8): a released world takes no new root, handle or creation (world-released, below)
(a/defn world-released [w :- World] Bool (:released w))
(a/defn create-in-scope-refused [w :- World, st :- Nat] Bool (Bool.or (Bool.or (in-cleanup w st) (world-released w)) (cur-closed w st)))
(a/defn create-refused [w :- World, st :- Nat] Bool (Bool.or (in-cleanup w st) (world-released w)))
;; Z#43: completion with open finally regions is refused (the CPS body cannot produce it)
(a/defn run-fins-open [r :- RunRow] Bool (Bool.not (fins-empty (:finalizers r))))
(a/defn fins-open [w :- World, st :- Nat] Bool (opt-test run-fins-open (tok-run w st)))
;; a result is ok v or err e (§2); a complete item carrying another tag (none) is malformed and
;; refused (found by the literal I10 proof: a task completed with result none keeps no run)
(a/defn res-tag-ok [tag :- Nat] Bool (Bool.or (Nat.beq tag res-ok) (Nat.beq tag res-err)))
(a/defn complete-refused [w :- World, st :- Nat, tag :- Nat] Bool
  (Bool.or (fins-open w st) (Bool.not (res-tag-ok tag))))

;; ===========================================================================
;; Part F3. C0 async sequences (§4.3 link/stream, §8.1): links are once-cells owned by the root
;; scope (deferred-like for finality and awaiting); a pull link is realized by a realizer task
;; started at its first demand; a stream (a T1 kind) holds its tail link
;; ===========================================================================

(a/theorem deliver-raw-res [w :- World, x :- Nat, v :- Nat]
  (= (deliver-raw w x v) (deliver-res w x v (RunResult.mk res-ok v))) (rfl))

;; ---- create-link (a pull head; engine `[:create-link R L]` / `[:create-link-top root L]`): owned by
;; the root scope, handles 1; in a computation run a creation in its basis (at = effect-index),
;; and `l` naming a link of its basis or adoption basis adopts it (moved to the basis at the new
;; site, like a re-spawn; no allocation, handles unchanged). Effect tick either way.
(a/defn create-link-in-run [w :- World, r :- RunRow] World
  (run-upd (record-basis (bump (source-ins w (new-link (:next-id w) root-scope-id 0))) r (:next-id w)) (:id r) run-tick))
(a/defn t-create-link [w :- World, st :- Nat, l :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (match (readopt-source w r l)
                [none (if (Nat.beq l (:next-id w)) (accept (create-link-in-run w r)) (refuse w))]
                [(some x) (if (Nat.beq (:kind x) sk-link) (accept (respawn-raw w r l)) (refuse w))])]))
(a/defn t-create-link-top [w :- World, scope :- Nat, l :- Nat] Outcome
  (if (Bool.and (Nat.beq l (:next-id w)) (scope-open-at w scope))
      (accept (bump (source-ins w (new-link (:next-id w) scope 0))))
      (refuse w)))

(a/theorem well-formed-create-link-in-run [w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (= (well-formed (create-link-in-run w r)) true))
  (intro h)
  (simp only [create-link-in-run])
  (exact (well-formed-run-upd _ (:id r) run-tick run-tick-run-id
           (well-formed-record-basis _ r (:next-id w)
             (well-formed-source-ins-fresh w (new-link (:next-id w) root-scope-id 0) (rfl) h)))))

(a/theorem well-formed-t-create-link [w :- World, st :- Nat, l :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-create-link w st l))) true))
  (intro h)
  (cases ht (tok-run w st))
  (case [none] (simp only [t-create-link ht refuse]) (exact h))
  (case [some r]
    (cases ho (readopt-source w r l))
    (case [none]
      (cases hg (Nat.beq l (:next-id w)))
      (case [false] (simp only [t-create-link ht ho hg refuse]) (exact h))
      (case [true] (simp only [t-create-link ht ho hg accept]) (exact (well-formed-create-link-in-run w r h))))
    (case [some x]
      (cases hk (Nat.beq (:kind x) sk-link))
      (case [false] (simp only [t-create-link ht ho hk refuse]) (exact h))
      (case [true]
        (simp only [t-create-link ht ho hk accept respawn-raw])
        (exact (well-formed-run-upd _ (:id r) run-tick run-tick-run-id
                 (well-formed-comp-upd w (:of r) _ (comp-rebasis-id _) (comp-rebasis-pending _) h)))))))

(a/theorem t-create-link-refuse [w :- World, st :- Nat, l :- Nat]
  (=> (= (:accepted (t-create-link w st l)) false) (= (:world (t-create-link w st l)) w))
  (intro ha)
  (cases ht (tok-run w st))
  (case [none] (simp only [t-create-link ht refuse]))
  (case [some r]
    (cases ho (readopt-source w r l))
    (case [none]
      (cases hg (Nat.beq l (:next-id w)))
      (case [false] (simp only [t-create-link ht ho hg refuse]))
      (case [true] (simp [t-create-link ht ho hg accept] at ha)))
    (case [some x]
      (cases hk (Nat.beq (:kind x) sk-link))
      (case [false] (simp only [t-create-link ht ho hk refuse]))
      (case [true] (simp [t-create-link ht ho hk accept] at ha)))))

(a/theorem well-formed-t-create-link-top [w :- World, scope :- Nat, l :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-create-link-top w scope l))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq l (:next-id w)) (scope-open-at w scope)))
  (simp only [t-create-link-top hg refuse]) (exact h)
  (simp only [t-create-link-top hg accept])
  (exact (well-formed-source-ins-fresh w (new-link (:next-id w) scope 0) (rfl) h)))

(a/theorem t-create-link-top-refuse [w :- World, scope :- Nat, l :- Nat]
  (=> (= (:accepted (t-create-link-top w scope l)) false) (= (:world (t-create-link-top w scope l)) w))
  (intro ha)
  (cases hg (Bool.and (Nat.beq l (:next-id w)) (scope-open-at w scope)))
  (simp only [t-create-link-top hg refuse])
  (simp [t-create-link-top hg accept] at ha))

;; ---- streams (T1 with kind sk-stream; engine `[:create-source(-top) .. :stream 0 S]`): the stream
;; S = next-id and its first tail, the push link S + 1 (no item of its own), owned by the root scope
(a/defn stream-rows [w :- World, owner :- Nat, v :- Nat] World
  (bump (source-ins (bump (source-ins w (new-stream (:next-id w) owner v)))
                    (new-link (+ (:next-id w) 1) root-scope-id (:next-id w)))))
(a/defn create-stream-in-run [w :- World, r :- RunRow, v :- Nat] World
  (run-upd (record-basis (stream-rows w (source-owner-in-run w r) v) r (:next-id w)) (:id r) run-tick))
;; in a body: as `t1-create-nonstream` (adoption of a stream of C's basis or adoption basis, else fresh = next-id)
(a/defn t1-create-stream [w :- World, st :- Nat, v :- Nat, fresh :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (match (readopt-source w r fresh)
                [none (if (Nat.beq fresh (:next-id w)) (accept (create-stream-in-run w r v)) (refuse w))]
                [(some x) (if (Nat.beq (:kind x) sk-stream) (accept (respawn-raw w r fresh)) (refuse w))])]))
(a/defn t1-create-source [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat] Outcome
  (if (Nat.beq kind sk-stream) (t1-create-stream w st v fresh) (t1-create-nonstream w st kind v fresh)))
(a/defn t1-create-source-top [w :- World, scope :- Nat, kind :- Nat, v :- Nat, fresh :- Nat] Outcome
  (if (Nat.beq kind sk-stream)
      (if (Bool.and (Nat.beq fresh (:next-id w)) (scope-open-at w scope)) (accept (stream-rows w scope v)) (refuse w))
      (t1-create-nonstream-top w scope kind v fresh)))

(a/theorem well-formed-stream-rows [w :- World, owner :- Nat, v :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (stream-rows w owner v)) true))
  (intro h)
  (simp only [stream-rows])
  (exact (well-formed-source-ins-fresh (bump (source-ins w (new-stream (:next-id w) owner v)))
           (new-link (+ (:next-id w) 1) root-scope-id (:next-id w)) (rfl)
           (well-formed-source-ins-fresh w (new-stream (:next-id w) owner v) (rfl) h))))

(a/theorem well-formed-create-stream-in-run [w :- World, r :- RunRow, v :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (create-stream-in-run w r v)) true))
  (intro h)
  (simp only [create-stream-in-run])
  (exact (well-formed-run-upd _ (:id r) run-tick run-tick-run-id
           (well-formed-record-basis _ r (:next-id w) (well-formed-stream-rows w (source-owner-in-run w r) v h)))))

(a/theorem well-formed-t1-create-stream [w :- World, st :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t1-create-stream w st v fresh))) true))
  (intro h)
  (cases ht (tok-run w st))
  (case [none] (simp only [t1-create-stream ht refuse]) (exact h))
  (case [some r]
    (cases ho (readopt-source w r fresh))
    (case [none]
      (cases hg (Nat.beq fresh (:next-id w)))
      (case [false] (simp only [t1-create-stream ht ho hg refuse]) (exact h))
      (case [true] (simp only [t1-create-stream ht ho hg accept]) (exact (well-formed-create-stream-in-run w r v h))))
    (case [some x]
      (cases hk (Nat.beq (:kind x) sk-stream))
      (case [false] (simp only [t1-create-stream ht ho hk refuse]) (exact h))
      (case [true]
        (simp only [t1-create-stream ht ho hk accept respawn-raw])
        (exact (well-formed-run-upd _ (:id r) run-tick run-tick-run-id
                 (well-formed-comp-upd w (:of r) _ (comp-rebasis-id _) (comp-rebasis-pending _) h)))))))

(a/theorem t1-create-stream-refuse [w :- World, st :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (:accepted (t1-create-stream w st v fresh)) false) (= (:world (t1-create-stream w st v fresh)) w))
  (intro ha)
  (cases ht (tok-run w st))
  (case [none] (simp only [t1-create-stream ht refuse]))
  (case [some r]
    (cases ho (readopt-source w r fresh))
    (case [none]
      (cases hg (Nat.beq fresh (:next-id w)))
      (case [false] (simp only [t1-create-stream ht ho hg refuse]))
      (case [true] (simp [t1-create-stream ht ho hg accept] at ha)))
    (case [some x]
      (cases hk (Nat.beq (:kind x) sk-stream))
      (case [false] (simp only [t1-create-stream ht ho hk refuse]))
      (case [true] (simp [t1-create-stream ht ho hk accept] at ha)))))

(a/theorem well-formed-t1-create-source [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t1-create-source w st kind v fresh))) true))
  (intro h)
  (cases hk (Nat.beq kind sk-stream))
  (simp only [t1-create-source hk]) (exact (well-formed-t1-create-nonstream w st kind v fresh h))
  (simp only [t1-create-source hk]) (exact (well-formed-t1-create-stream w st v fresh h)))

(a/theorem t1-create-source-refuse [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (:accepted (t1-create-source w st kind v fresh)) false) (= (:world (t1-create-source w st kind v fresh)) w))
  (intro ha)
  (cases hk (Nat.beq kind sk-stream))
  (simp only [t1-create-source hk] at ha) (simp only [t1-create-source hk]) (exact (t1-create-nonstream-refuse w st kind v fresh ha))
  (simp only [t1-create-source hk] at ha) (simp only [t1-create-source hk]) (exact (t1-create-stream-refuse w st v fresh ha)))

(a/theorem well-formed-t1-create-source-top [w :- World, scope :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t1-create-source-top w scope kind v fresh))) true))
  (intro h)
  (cases hk (Nat.beq kind sk-stream))
  (simp only [t1-create-source-top hk]) (exact (well-formed-t1-create-nonstream-top w scope kind v fresh h))
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (scope-open-at w scope)))
  (simp only [t1-create-source-top hk hg refuse]) (exact h)
  (simp only [t1-create-source-top hk hg accept]) (exact (well-formed-stream-rows w scope v h)))

(a/theorem t1-create-source-top-refuse [w :- World, scope :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (:accepted (t1-create-source-top w scope kind v fresh)) false) (= (:world (t1-create-source-top w scope kind v fresh)) w))
  (intro ha)
  (cases hk (Nat.beq kind sk-stream))
  (simp only [t1-create-source-top hk] at ha) (simp only [t1-create-source-top hk]) (exact (t1-create-nonstream-top-refuse w scope kind v fresh ha))
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (scope-open-at w scope)))
  (simp only [t1-create-source-top hk hg refuse])
  (simp [t1-create-source-top hk hg accept] at ha))

;; ---- link-demand (`[:link-demand L K]`, after the T6/T22 commit that demanded L): an unrealized
;; open pull link without a live realizer (T14/T21 clear rtask at the realizer's cancel, rule.clj
;; `clear-rtasks`; the realizer is live while its task exists without a result) starts its realizer: task K owned by the root scope (handles 0),
;; its run and run scope (T4's rows, started: its first slice is a scheduling choice); L.rtask := K
(a/defn task-live [w :- World, k :- Nat] Bool
  (match (task-find w k) [none false] [(some t) (Nat.beq (:tag (:result t)) res-none)]))
(a/defn realizer-live [w :- World, s :- SourceRow] Bool
  (Bool.and (Bool.not (Nat.beq (:rtask s) 0)) (task-live w (:rtask s))))
(a/defn link-idle [w :- World, s :- SourceRow] Bool
  (Bool.and (link-open s) (Bool.and (Nat.beq (:tail s) 0) (Bool.not (realizer-live w s)))))
(a/defn link-demand-raw [w :- World, l :- Nat] World
  (source-upd (task-upd (spawn-rows w root-scope-id (List.nil Nat) false) (:next-id w) task-no-handles) l (link-set-rtask (:next-id w))))
(a/defn t-link-demand [w :- World, l :- Nat, k :- Nat] Outcome
  (match (source-find w l)
    [none (refuse w)]
    [(some s) (if (Bool.and (link-idle w s) (Bool.and (Nat.beq k (:next-id w)) (scope-open-at w root-scope-id)))
                  (accept (link-demand-raw w l)) (refuse w))]))

(a/theorem well-formed-link-demand-raw [w :- World, l :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (link-demand-raw w l)) true))
  (intro h)
  (simp only [link-demand-raw])
  (exact (well-formed-source-upd _ l _ (link-set-rtask-id _)
           (well-formed-task-upd _ (:next-id w) task-no-handles task-no-handles-id (well-formed-spawn-rows w root-scope-id (List.nil Nat) false h)))))

(a/theorem well-formed-t-link-demand [w :- World, l :- Nat, k :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-link-demand w l k))) true))
  (intro h)
  (cases hf (source-find w l)) (case' [some s]) (case' [none])
  (simp only [t-link-demand hf refuse]) (exact h)
  (cases hg (Bool.and (link-idle w s) (Bool.and (Nat.beq k (:next-id w)) (scope-open-at w root-scope-id))))
  (simp only [t-link-demand hf hg refuse]) (exact h)
  (simp only [t-link-demand hf hg accept]) (exact (well-formed-link-demand-raw w l h)))

(a/theorem t-link-demand-refuse [w :- World, l :- Nat, k :- Nat]
  (=> (= (:accepted (t-link-demand w l k)) false) (= (:world (t-link-demand w l k)) w))
  (intro ha)
  (cases hf (source-find w l)) (case' [some s]) (case' [none])
  (simp only [t-link-demand hf refuse])
  (cases hg (Bool.and (link-idle w s) (Bool.and (Nat.beq k (:next-id w)) (scope-open-at w root-scope-id))))
  (simp only [t-link-demand hf hg refuse])
  (simp [t-link-demand hf hg accept] at ha))

;; ---- link-realize (`[:link-realize L tag v N]`, after the realizer's T12 item): L (an unrealized
;; open pull link whose realizer is no longer live) is realized: tag 1 (res-ok) creates the next
;; pull link N = next-id and realizes L with [v N]; tag 0 the end (N = 0); tag 2 (res-err) the
;; memoized error v (N = 0). ::forked realizes nothing (no item; the next demand restarts it).
(a/defn link-next-raw [w :- World, l :- Nat, v :- Nat] World
  (realize-link (bump (source-ins w (new-link (:next-id w) root-scope-id 0))) l v false (:next-id w)))
(a/defn link-realize-raw [w :- World, l :- Nat, tag :- Nat, v :- Nat, n :- Nat] Outcome
  (if (Nat.beq tag res-ok)
      (if (Nat.beq n (:next-id w)) (accept (link-next-raw w l v)) (refuse w))
      (if (Nat.beq n 0)
          (if (Nat.beq tag res-none) (accept (realize-link w l 0 false 0))
              (if (Nat.beq tag res-err) (accept (realize-link w l v true 0)) (refuse w)))
          (refuse w))))
(a/defn t-link-realize [w :- World, l :- Nat, tag :- Nat, v :- Nat, n :- Nat] Outcome
  (match (source-find w l)
    [none (refuse w)]
    [(some s) (if (link-idle w s) (link-realize-raw w l tag v n) (refuse w))]))

(a/theorem well-formed-link-next-raw [w :- World, l :- Nat, v :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (link-next-raw w l v)) true))
  (intro h)
  (simp only [link-next-raw])
  (exact (well-formed-realize-link _ l v false _ (well-formed-source-ins-fresh w (new-link (:next-id w) root-scope-id 0) (rfl) h))))

(a/theorem well-formed-link-realize-raw [w :- World, l :- Nat, tag :- Nat, v :- Nat, n :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (link-realize-raw w l tag v n))) true))
  (intro h)
  (cases h1 (Nat.beq tag res-ok))
  (case [true]
    (cases h2 (Nat.beq n (:next-id w)))
    (case [false] (simp only [link-realize-raw h1 h2 refuse]) (exact h))
    (case [true] (simp only [link-realize-raw h1 h2 accept]) (exact (well-formed-link-next-raw w l v h))))
  (case [false]
    (cases h2 (Nat.beq n 0))
    (case [false] (simp only [link-realize-raw h1 h2 refuse]) (exact h))
    (case [true]
      (cases h3 (Nat.beq tag res-none))
      (case [true] (simp only [link-realize-raw h1 h2 h3 accept]) (exact (well-formed-realize-link w l 0 false 0 h)))
      (case [false]
        (cases h4 (Nat.beq tag res-err))
        (case [false] (simp only [link-realize-raw h1 h2 h3 h4 refuse]) (exact h))
        (case [true] (simp only [link-realize-raw h1 h2 h3 h4 accept]) (exact (well-formed-realize-link w l v true 0 h)))))))

(a/theorem link-realize-raw-refuse [w :- World, l :- Nat, tag :- Nat, v :- Nat, n :- Nat]
  (=> (= (:accepted (link-realize-raw w l tag v n)) false) (= (:world (link-realize-raw w l tag v n)) w))
  (intro ha)
  (cases h1 (Nat.beq tag res-ok))
  (case [true]
    (cases h2 (Nat.beq n (:next-id w)))
    (case [false] (simp only [link-realize-raw h1 h2 refuse]))
    (case [true] (simp [link-realize-raw h1 h2 accept] at ha)))
  (case [false]
    (cases h2 (Nat.beq n 0))
    (case [false] (simp only [link-realize-raw h1 h2 refuse]))
    (case [true]
      (cases h3 (Nat.beq tag res-none))
      (case [true] (simp [link-realize-raw h1 h2 h3 accept] at ha))
      (case [false]
        (cases h4 (Nat.beq tag res-err))
        (case [false] (simp only [link-realize-raw h1 h2 h3 h4 refuse]))
        (case [true] (simp [link-realize-raw h1 h2 h3 h4 accept] at ha))))))

(a/theorem well-formed-t-link-realize [w :- World, l :- Nat, tag :- Nat, v :- Nat, n :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-link-realize w l tag v n))) true))
  (intro h)
  (cases hf (source-find w l)) (case' [some s]) (case' [none])
  (simp only [t-link-realize hf refuse]) (exact h)
  (cases hg (link-idle w s))
  (simp only [t-link-realize hf hg refuse]) (exact h)
  (simp only [t-link-realize hf hg]) (exact (well-formed-link-realize-raw w l tag v n h)))

(a/theorem t-link-realize-refuse [w :- World, l :- Nat, tag :- Nat, v :- Nat, n :- Nat]
  (=> (= (:accepted (t-link-realize w l tag v n)) false) (= (:world (t-link-realize w l tag v n)) w))
  (intro ha)
  (cases hf (source-find w l)) (case' [some s]) (case' [none])
  (simp only [t-link-realize hf refuse])
  (cases hg (link-idle w s))
  (simp only [t-link-realize hf hg refuse])
  (simp only [t-link-realize hf hg] at ha) (simp only [t-link-realize hf hg]) (exact (link-realize-raw-refuse w l tag v n ha)))

;; ---- append (`[:append S v T]`): on an open stream whose tail is unrealized: the new tail T =
;; next-id (a push link), S.tail := T (version + 1), the old tail realized with [v T]; refused on a
;; closed stream
(a/defn append-raw [w :- World, x :- Nat, v :- Nat, old :- Nat] World
  (realize-link (bump (source-ins (source-upd w x (stream-set-tail (:next-id w))) (new-link (:next-id w) root-scope-id x)))
                old v false (:next-id w)))
(a/defn t-append [w :- World, x :- Nat, v :- Nat, t :- Nat] Outcome
  (match (source-find w x)
    [none (refuse w)]
    [(some s) (if (Bool.and (open-kind sk-stream s) (Bool.and (Nat.beq t (:next-id w)) (link-pending w (:tail s))))
                  (accept (append-raw w x v (:tail s))) (refuse w))]))

(a/theorem well-formed-append-raw [w :- World, x :- Nat, v :- Nat, old :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (append-raw w x v old)) true))
  (intro h)
  (simp only [append-raw])
  (exact (well-formed-realize-link _ old v false _
           (well-formed-source-ins-fresh (source-upd w x (stream-set-tail (:next-id w))) (new-link (:next-id w) root-scope-id x) (rfl)
             (well-formed-source-upd w x (stream-set-tail (:next-id w)) (stream-set-tail-id _) h)))))

(a/theorem well-formed-t-append [w :- World, x :- Nat, v :- Nat, t :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-append w x v t))) true))
  (intro h)
  (cases hf (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-append hf refuse]) (exact h)
  (cases hg (Bool.and (open-kind sk-stream s) (Bool.and (Nat.beq t (:next-id w)) (link-pending w (:tail s)))))
  (simp only [t-append hf hg refuse]) (exact h)
  (simp only [t-append hf hg accept]) (exact (well-formed-append-raw w x v _ h)))

(a/theorem t-append-refuse [w :- World, x :- Nat, v :- Nat, t :- Nat]
  (=> (= (:accepted (t-append w x v t)) false) (= (:world (t-append w x v t)) w))
  (intro ha)
  (cases hf (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-append hf refuse])
  (cases hg (Bool.and (open-kind sk-stream s) (Bool.and (Nat.beq t (:next-id w)) (link-pending w (:tail s)))))
  (simp only [t-append hf hg refuse])
  (simp [t-append hf hg accept] at ha))

;; ---- close (`[:close S tag v]`, tag 0 end / 2 error): on an open stream: its tail is realized
;; (the end, or the error v), then S closes (T16's close-source: the tail is no longer pending)
(a/defn close-tag-ok [tag :- Nat] Bool (Bool.or (Nat.beq tag res-none) (Nat.beq tag res-err)))
(a/defn close-raw [w :- World, x :- Nat, t :- Nat, tag :- Nat, v :- Nat] World
  (close-source (end-link w t (Nat.beq tag res-err) v) x))
(a/defn t-close [w :- World, x :- Nat, tag :- Nat, v :- Nat] Outcome
  (match (source-find w x)
    [none (refuse w)]
    [(some s) (if (Bool.and (open-kind sk-stream s) (close-tag-ok tag))
                  (accept (close-raw w x (:tail s) tag v)) (refuse w))]))

(a/theorem well-formed-close-raw [w :- World, x :- Nat, t :- Nat, tag :- Nat, v :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (close-raw w x t tag v)) true))
  (intro h)
  (simp only [close-raw])
  (exact (well-formed-close-source _ x (well-formed-end-link w t _ v h))))

(a/theorem well-formed-t-close [w :- World, x :- Nat, tag :- Nat, v :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-close w x tag v))) true))
  (intro h)
  (cases hf (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-close hf refuse]) (exact h)
  (cases hg (Bool.and (open-kind sk-stream s) (close-tag-ok tag)))
  (simp only [t-close hf hg refuse]) (exact h)
  (simp only [t-close hf hg accept]) (exact (well-formed-close-raw w x _ tag v h)))

(a/theorem t-close-refuse [w :- World, x :- Nat, tag :- Nat, v :- Nat]
  (=> (= (:accepted (t-close w x tag v)) false) (= (:world (t-close w x tag v)) w))
  (intro ha)
  (cases hf (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-close hf refuse])
  (cases hg (Bool.and (open-kind sk-stream s) (close-tag-ok tag)))
  (simp only [t-close hf hg refuse])
  (simp [t-close hf hg accept] at ha))

;; Z#54 (§4.3, operation by kind): a mailbox or semaphore is only taken (`take`, a wait edge):
;; `await` with such a member (one, all or any; the engine logs `await` on a mailbox as `take`)
;; and the host read (T22) of one fail with no commit (refused here), so no dep edge ever has a
;; mailbox or semaphore debtor. `track` on another kind than signal/cell is T7's refusal. C0: a
;; stream is not awaitable either (readers hold positions, its links): await/T22 on one refused.
(a/defn source-consuming [s :- SourceRow] Bool
  (Bool.or (Nat.beq (:kind s) sk-mailbox) (Bool.or (Nat.beq (:kind s) sk-semaphore) (Nat.beq (:kind s) sk-stream))))
(a/defn deb-consuming [w :- World, d :- Nat] Bool (opt-test source-consuming (source-find w d)))
(a/defn await-kind-refused [w :- World, ds :- (List Nat)] Bool (tbl-any (deb-consuming w) ds))
;; C1 (Q5, spindel #269): a released world takes no new root, also from a held slice (a cleanup
;; slice's own host operations, Z#40): observe, pin and host waits are refused (the engine throws
;; released-ex / delivers it to a value-async callback; no item). Write, deliver, post, release and
;; close stay as Z#40. (`host-item-refused` refuses the host's items only while no slice is held.)
(a/defn host-await-refused [w :- World, d :- Nat] Bool (Bool.or (world-released w) (deb-consuming w d)))
;; C1, B8 reduced (finalizers are synchronous): in a cancelled run's finally clause (its cleanup
;; slice, `in-cleanup`) every await and take is refused, settled debtor or not (engine
;; `unwinding-finalizer-refusal`: the effect fails with ::invalid :finalizer, no commit). A
;; suspending effect in a normal run's finally clause (between `finally-exit` and `finally-leave`,
;; `in-finally`) also fails with no commit (engine `finalizer-refusal`, C1 A5): an await whose
;; debtors are not settled now (`settled-now`, engine `settled-now?`: a live computation, a
;; completed task, a delivered deferred, a fired resource, any other source read at once; `one`
;; and `all` need every debtor, `any` one), a take with nothing to take on an open source, and
;; every arm (sleep, offload, await-op).
(a/defn in-finally [w :- World, st :- Nat] Bool (opt-test run-in-finally (tok-run w st)))
(a/defn arm-refused [w :- World, st :- Nat] Bool (Bool.or (in-cleanup w st) (in-finally w st)))
(a/defn settled-now [w :- World, d :- Nat] Bool
  (match (comp-find w d)
    [none (match (source-find w d)
            [none (Bool.or (deb-final w d) (res-fired w d))]
            [(some s) (Bool.or (Bool.not (Nat.beq (:kind s) sk-deferred)) (source-delivered s))])]
    [(some c) (comp-live c)]))
(a/defn settled-mode [w :- World, ds :- (List Nat), mode :- Nat] Bool
  (if (Nat.beq mode am-any) (tbl-any (settled-now w) ds) (tbl-all (settled-now w) ds)))
(a/defn finally-suspends [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat] Bool
  (Bool.and (in-finally w st) (Bool.not (settled-mode w ds mode))))
(a/defn await-refused [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat] Bool
  (Bool.or (in-cleanup w st) (Bool.or (finally-suspends w st ds mode) (await-kind-refused w ds))))
(a/defn take-refused [w :- World, st :- Nat, x :- Nat] Bool
  (Bool.or (in-cleanup w st) (Bool.and (in-finally w st) (Bool.not (opt-test take-ready (source-find w x))))))
(a/theorem arm-refused-cleanup [w :- World, st :- Nat] (=> (= (arm-refused w st) false) (= (in-cleanup w st) false))
  (intro h) (cases hc (in-cleanup w st)) (case [false] (rfl)) (case [true] (simp [arm-refused hc] at h)))
(a/theorem take-refused-cleanup [w :- World, st :- Nat, x :- Nat] (=> (= (take-refused w st x) false) (= (in-cleanup w st) false))
  (intro h) (cases hc (in-cleanup w st)) (case [false] (rfl)) (case [true] (simp [take-refused hc] at h)))
;; C0 (engine session, 2026-11-16): T8 observe on a stream is refused as await/T22 (the engine
;; delivers an error to the callback, creates no edge and logs no item)
(a/defn t8-observe [w :- World, d :- Nat, cb :- Nat, fresh :- Nat] Outcome
  (if (source-kind-at w sk-stream d) (refuse w) (t8-observe-any-kind w d cb fresh)))

(a/theorem well-formed-t8-observe [w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t8-observe w d cb fresh))) true))
  (intro h)
  (cases hs (source-kind-at w sk-stream d))
  (simp only [t8-observe hs]) (exact (well-formed-t8-observe-any-kind w d cb fresh h))
  (simp only [t8-observe hs refuse]) (exact h))

(a/theorem t8-observe-refuse [w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (:accepted (t8-observe w d cb fresh)) false) (= (:world (t8-observe w d cb fresh)) w))
  (intro ha)
  (cases hs (source-kind-at w sk-stream d))
  (simp only [t8-observe hs] at ha) (simp only [t8-observe hs]) (exact (t8-observe-any-kind-refuse w d cb fresh ha))
  (simp only [t8-observe hs refuse]))

;; C0 (engine session, feat/v2-world-completion): a link owned by the root scope is created only
;; while the root scope is open (create-link, create-link-top, append, a stream's first tail), and no
;; link is realized once it is closed (link-realize, every tag: the engine's link-done! realizes
;; nothing and logs no item); once it is closed (T21) the item is refused, as the engine (append logs
;; accepted false; the others are refused for a cancelled run or a released host). `b` says whether
;; the item is gated.
(a/defn root-open-if [b :- Bool, w :- World] Bool (Bool.or (Bool.not b) (scope-open-at w root-scope-id)))
(a/defn require-root-open [w :- World, b :- Bool, o :- Outcome] Outcome (if (root-open-if b w) o (refuse w)))

(a/theorem well-formed-require-root-open [w :- World, b :- Bool, o :- Outcome]
  (=> (= (well-formed w) true) (= (well-formed (:world o)) true) (= (well-formed (:world (require-root-open w b o))) true))
  (intros h ho)
  (cases hg (root-open-if b w))
  (simp only [require-root-open hg refuse]) (exact h)
  (simp only [require-root-open hg]) (exact ho))

(a/theorem require-root-open-refuse [w :- World, b :- Bool, o :- Outcome]
  (=> (= (:accepted (require-root-open w b o)) false) (=> (= (:accepted o) false) (= (:world o) w)) (= (:world (require-root-open w b o)) w))
  (intros ha ho)
  (cases hg (root-open-if b w))
  (simp only [require-root-open hg refuse])
  (simp only [require-root-open hg] at ha) (simp only [require-root-open hg]) (exact (ho ha)))

(a/theorem require-root-open-l4 [w :- World, b :- Bool, o :- Outcome]
  (=> (= (:accepted o) false) (= (:accepted (require-root-open w b o)) false))
  (intro ho)
  (cases hg (root-open-if b w))
  (simp only [require-root-open hg refuse])
  (simp only [require-root-open hg]) (exact ho))

;; ===========================================================================
;; Part G. The step: raw transition (every item), then Rule R
;; ===========================================================================

;; ---- C1c stage B (spindel.v2.owned): the owned-fork items 45-47. `own` is own-child!'s count in the parent at
;; the `(fork)` effect (engine `[:fork r c]`; s the forking run's `cur-scope`, m the child cell): counted only when
;; the world is not released and s is open and not the root (question 18a), a fork marker with the parent's fresh
;; id. `owned-done` (`[:owned-done s c]`): the marker c of s goes, then Z#18 at s. `drain` (`[:normalize]`): the
;; inherited markers ids (W-NORMALIZE) go, then Z#18 at each owner. Each is refused when it has nothing to do (no
;; count; no such marker; none of ids present). Internal: accepted after release; Rule R follows (`then-rule-r`).
(a/defn own-ok [w :- World, s :- Nat] Bool
  (Bool.and (Bool.not (:released w)) (Bool.and (Bool.not (Nat.beq s root-scope-id)) (scope-open-at w s))))
(a/defn t-own [w :- World, s :- Nat, m :- Nat] Outcome
  (if (own-ok w s) (accept (bump (fork-ins w (ForkRow.mk (:next-id w) m s)))) (refuse w)))
(a/defn marker-of [s :- Nat, c :- Nat, f :- ForkRow] Bool (Bool.and (Nat.beq (:id f) c) (Nat.beq (:owner f) s)))
(a/defn t-owned-done [w :- World, s :- Nat, c :- Nat] Outcome
  (if (tbl-any (marker-of s c) (:forks w)) (accept (remove-empty-at (fork-del w c) s)) (refuse w)))
(a/defn fork-in [ids :- (List Nat), f :- ForkRow] Bool (reach-mem (:id f) ids))
(a/defn owners-in [ids :- (List Nat), fs :- (List ForkRow)] (List Nat)
  (match fs [nil (List.nil Nat)]
         [(cons h t) (if (reach-mem (:id h) ids) (List.cons Nat (:owner h) (owners-in ids t)) (owners-in ids t))]))
(a/defn t-drain [w :- World, ids :- (List Nat)] Outcome
  (if (tbl-any (fork-in ids) (:forks w))
      (accept (nat-fold remove-empty-at (nat-fold fork-del w ids) (owners-in ids (:forks w))))
      (refuse w)))

(a/theorem open-at-has [w :- World, s :- Nat] (=> (= (scope-open-at w s) true) (= (tbl-has scope-id s (:scopes w)) true))
  (intro h)
  (cases hf (scope-find w s))
  (case [none] (simp [scope-open-at hf] at h))
  (case [some sc] (exact (tbl-find-has ScopeRow scope-id s sc (:scopes w) hf))))
(a/theorem own-ok-parts [w :- World, s :- Nat]
  (=> (= (own-ok w s) true)
      (And (= (:released w) false) (And (= (Nat.beq s 2) false) (= (tbl-has scope-id s (:scopes w)) true))))
  (intro h)
  (simp only [own-ok root-scope-id Bool.and_eq_true] at h)
  (exact (And.intro (bnot-true _ (And.left h)) (And.intro (bnot-true _ (And.left (And.right h))) (open-at-has w s (And.right (And.right h)))))))
(a/theorem well-formed-remove-empty-at [w :- World, o :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (remove-empty-at w o)) true))
  (intro h) (simp only [remove-empty-at]) (exact (well-formed-remove-if-empty w (scope-subtree w o) h)))
(a/theorem well-formed-t-own [w :- World, s :- Nat, m :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-own w s m))) true))
  (intro h)
  (cases ho (own-ok w s))
  (case [false] (simp only [t-own ho refuse]) (exact h))
  (case [true] (simp only [t-own ho accept]) (exact (well-formed-fork-ins-fresh w (ForkRow.mk (:next-id w) m s) (rfl) h))))
(a/theorem t-own-refuse [w :- World, s :- Nat, m :- Nat]
  (=> (= (:accepted (t-own w s m)) false) (= (:world (t-own w s m)) w))
  (intro ha)
  (cases ho (own-ok w s))
  (case [false] (simp only [t-own ho refuse]))
  (case [true] (simp [t-own ho accept] at ha)))
(a/theorem well-formed-t-owned-done [w :- World, s :- Nat, c :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-owned-done w s c))) true))
  (intro h)
  (cases hm (tbl-any (marker-of s c) (:forks w)))
  (case [false] (simp only [t-owned-done hm refuse]) (exact h))
  (case [true] (simp only [t-owned-done hm accept]) (exact (well-formed-remove-empty-at (fork-del w c) s (well-formed-fork-del w c h)))))
(a/theorem t-owned-done-refuse [w :- World, s :- Nat, c :- Nat]
  (=> (= (:accepted (t-owned-done w s c)) false) (= (:world (t-owned-done w s c)) w))
  (intro ha)
  (cases hm (tbl-any (marker-of s c) (:forks w)))
  (case [false] (simp only [t-owned-done hm refuse]))
  (case [true] (simp [t-owned-done hm accept] at ha)))
(a/theorem well-formed-t-drain [w :- World, ids :- (List Nat)]
  (=> (= (well-formed w) true) (= (well-formed (:world (t-drain w ids))) true))
  (intro h)
  (cases hm (tbl-any (fork-in ids) (:forks w)))
  (case [false] (simp only [t-drain hm refuse]) (exact h))
  (case [true]
    (simp only [t-drain hm accept])
    (exact (well-formed-nat-fold remove-empty-at well-formed-remove-empty-at (owners-in ids (:forks w)) (nat-fold fork-del w ids)
             (well-formed-nat-fold fork-del well-formed-fork-del ids w h)))))
(a/theorem t-drain-refuse [w :- World, ids :- (List Nat)]
  (=> (= (:accepted (t-drain w ids)) false) (= (:world (t-drain w ids)) w))
  (intro ha)
  (cases hm (tbl-any (fork-in ids) (:forks w)))
  (case [false] (simp only [t-drain hm refuse]))
  (case [true] (simp [t-drain hm accept] at ha)))

;; ---- Z#77 T28 `[:retire-local]` (internal; the first item of a world derived from one with fork-local runs:
;; layer 2 applies it at the world's first entry, layer2/sys.clj `sys-retire`). Every run of a fork-local task is retired
;; and nothing runs for it. Per run R (in `local-order`, deepest run scope first, so a subtree is empty when its
;; run retires): R's activations go with their wait/savepoint members (`cancel-acts`, as T14); R's resources are
;; deleted without a fire and without an acknowledgement item (`ack-raw`, guarded as T15); R loses its finalizers
;; and its slice (`run-drop-fins`: no cleanup entry, no cleanup slice). Then an R that is not done completes as by
;; T12 (`complete-raw`; the second test is always true here, retire-one being applied to such runs only): its task gets err v (v = ::forked with :spindel/fork-local) unless it already has a
;; result (a cleanup slice parked in a finally keeps it), the creditors are filled with it, T13 retires R (K.run :=
;; none, the run scope's subtree closed with its owned sources, Z#18, the run row goes, the subtree's scopes go
;; when empty), then T10. A done R (unwinding, or awaiting T13) is retired by T13 (`t13-retire`). The engine's
;; one commit (all runs silenced, then the tasks finished, then T13 on each) ends in the same world. Refused when
;; the world has no run of a fork-local task.
(a/defn run-of-local [w :- World, r :- RunRow] Bool (task-local-id w (:of r)))
(a/defn run-depth [w :- World, r :- RunRow] Nat (List.length (scope-ancestors w (:scope r))))
(a/defn ins-by-depth [w :- World, r :- RunRow, xs :- (List RunRow)] (List RunRow)
  (match xs [nil (List.cons RunRow r (List.nil RunRow))]
         [(cons h t) (if (Nat.ble (run-depth w h) (run-depth w r)) (List.cons RunRow r xs)
                         (List.cons RunRow h (ins-by-depth w r t)))]))
(a/defn sort-depth [w :- World, xs :- (List RunRow)] (List RunRow)
  (match xs [nil (List.nil RunRow)] [(cons h t) (ins-by-depth w h (sort-depth w t))]))
(a/defn local-order [w :- World] (List Nat) (tbl-ids run-id (sort-depth w (tbl-filter (run-of-local w) (:runs w)))))
(a/defn ack-if [rid :- Nat, w :- World, z :- Nat] World
  (if (tbl-all (no-debtor z) (:edges w)) (ack-raw w z rid) w))
(a/defn run-drop-fins [r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) (:act r) (:mode r) false
             (:effect-index r) (List.nil Finalizer) (:resources r)))
(a/theorem run-drop-fins-id [r :- RunRow] (= (run-id (run-drop-fins r)) (run-id r)) (rfl))
(a/defn retire-pre [w :- World, r :- RunRow] World
  (run-upd (nat-fold (ack-if (:id r)) (cancel-acts w (:id r)) (:resources r)) (:id r) run-drop-fins))
;; the result the retired run's task ends with: its own when it has one, else err v (never none)
(a/defn task-final-res [w :- World, k :- Nat, res :- RunResult] RunResult
  (match (task-find w k)
    [none res]
    [(some t) (if (Nat.beq (:tag (:result t)) res-none) res (:result t))]))
(a/theorem task-final-res-tag [w :- World, k :- Nat, v :- Nat]
  (= (Nat.beq (:tag (task-final-res w k (RunResult.mk res-err v))) res-none) false)
  (cases hf (task-find w k)) (case' [some t]) (case' [none])
  (simp only [task-final-res hf res-err res-none])
  (cases ht (Nat.beq (:tag (:result t)) res-none))
  (simp only [task-final-res hf]) (rw [ht]) (exact ht)
  (simp only [task-final-res hf]) (rw [ht]))
(a/defn retire-one [v :- Nat, w :- World, rid :- Nat] World
  (match (run-find w rid)
    [none w]
    [(some r) (match (run-find (retire-pre w r) rid)
                [none (retire-pre w r)]
                [(some r1) (if (Bool.and (run-alive r1) (run-of-local (retire-pre w r) r1))
                               (complete-raw (retire-pre w r) r1 (task-final-res (retire-pre w r) (:of r1) (RunResult.mk res-err v)))
                               (t13-retire (retire-pre w r) rid))])]))
(a/defn t28-retire-local [w :- World, v :- Nat] Outcome
  (if (tbl-any (run-of-local w) (:runs w))
      (accept (nat-fold (retire-one v) w (local-order w)))
      (refuse w)))

(a/theorem well-formed-ack-if [rid :- Nat, w :- World, z :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (ack-if rid w z)) true))
  (intro h)
  (cases hu (tbl-all (no-debtor z) (:edges w)))
  (case [false] (simp only [ack-if hu]) (exact h))
  (case [true] (simp only [ack-if hu]) (exact (well-formed-ack-raw w z rid hu h))))
(a/theorem well-formed-retire-pre [w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (= (well-formed (retire-pre w r)) true))
  (intro h)
  (simp only [retire-pre])
  (exact (well-formed-run-upd _ (:id r) run-drop-fins run-drop-fins-id
           (well-formed-nat-fold (ack-if (:id r)) (well-formed-ack-if (:id r)) (:resources r) _ (well-formed-cancel-acts w (:id r) h)))))
(a/theorem well-formed-retire-one [v :- Nat, w :- World, rid :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (retire-one v w rid)) true))
  (intro h)
  (cases hf (run-find w rid))
  (case [none] (simp only [retire-one hf]) (exact h))
  (case [some r]
    (have hp := (well-formed-retire-pre w r h))
    (cases hf1 (run-find (retire-pre w r) rid))
    (case [none] (simp only [retire-one hf hf1]) (exact hp))
    (case [some r1]
      (cases ha (Bool.and (run-alive r1) (run-of-local (retire-pre w r) r1)))
      (case [true] (simp only [retire-one hf hf1 ha]) (exact (well-formed-complete-raw _ r1 _ hp)))
      (case [false] (simp only [retire-one hf hf1 ha t13-retire]) (exact (well-formed-run-cascade _ _ hp))))))
(a/theorem well-formed-t28-retire-local [w :- World, v :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (:world (t28-retire-local w v))) true))
  (intro h)
  (cases hm (tbl-any (run-of-local w) (:runs w)))
  (case [false] (simp only [t28-retire-local hm refuse]) (exact h))
  (case [true] (simp only [t28-retire-local hm accept])
    (exact (well-formed-nat-fold (retire-one v) (well-formed-retire-one v) (local-order w) w h))))
(a/theorem t28-retire-local-refuse [w :- World, v :- Nat]
  (=> (= (:accepted (t28-retire-local w v)) false) (= (:world (t28-retire-local w v)) w))
  (intro ha)
  (cases hm (tbl-any (run-of-local w) (:runs w)))
  (case [false] (simp only [t28-retire-local hm refuse]))
  (case [true] (simp [t28-retire-local hm accept] at ha)))

(a/defn transition [w :- World, it :- Item] Outcome
  (match it
    [(create-source st kind v fresh) (if (create-in-scope-refused w st) (refuse w) (require-root-open w (Nat.beq kind sk-stream) (t1-create-source w st kind v fresh)))]
    [(create-source-top scope kind v fresh) (if (world-released w) (refuse w) (require-root-open w (Nat.beq kind sk-stream) (t1-create-source-top w scope kind v fresh)))]
    [(write x v) (t2-write w x v)]
    [(track st x k fresh) (if (in-cleanup w st) (refuse w) (t7-track w st x k fresh))]
    [(observe d cb fresh) (if (world-released w) (refuse w) (t8-observe w d cb fresh))]
    [(unobserve e) (t8-unobserve w e)]
    [(fire e tag val) (t9-fire w e tag val)]
    [(resource-ack z) (t15-resource-ack w z)]
    [(arm st kind k fresh) (if (arm-refused w st) (refuse w) (t17-arm w st kind k fresh))]
    [(resource-fire z tag val) (t18-resource-fire w z tag val)]
    [(handle-drop x) (t19-handle-drop w x)]
    [(pin x) (if (world-released w) (refuse w) (t20-pin w x))]
    [(unpin x) (t20-unpin w x)]
    [(create-comp st c i b) (if (create-refused w st) (refuse w) (t3-create w st c i b))]
    [(create-comp-top sc c i b) (if (world-released w) (refuse w) (t3-create-top w sc c i b))]
    [(spawn st b fresh ins loc) (if (create-in-scope-refused w st) (refuse w) (if (spawn-local-refused w st loc) (refuse w) (t4-spawn w st b fresh ins loc)))]
    [(spawn-top sc b fresh ins loc) (if (world-released w) (refuse w) (t4-spawn-top w sc b fresh ins loc))]
    [(start c fresh) (t5-start w c fresh)]
    [(await st ds m k fresh mine) (if (await-refused w st ds m) (refuse w) (t6-await w st ds m k fresh mine))]
    [(dispatch-comp c fresh) (t11-dispatch w c fresh)]
    [(complete st tag val) (if (complete-refused w st tag) (refuse w) (t12-complete w st tag val))]
    [(schedule r) (t-schedule w r)]
    [(host-await d fresh) (if (host-await-refused w d) (refuse w) (t22-host-await w d fresh))]
    [(host-unawait e) (t22-host-unawait w e)]
    [(handle-new x) (if (world-released w) (refuse w) (t-handle-new w x))]
    [(deliver x v) (t-deliver w x v)]
    [(post x v) (t-post w x v)]
    [(take st x k fresh) (if (take-refused w st x) (refuse w) (t-take w st x k fresh))]
    [(release x) (t-release w x)]
    [(finalize r) (t-finalize w r)]
    [(cancel r) (t14-host-cancel w r)]
    [(release-world) (t21-release-world w)]
    [(open-scope st s) (t-open-scope w st s)]
    [(close-scope s) (t-close-scope w s)]
    [(detach k s) (if (detach-local-refused w k s) (refuse w) (t-detach w k s))]
    [(finally-enter st) (t-finally-enter w st)]
    [(finally-exit st) (t-finally-exit w st)]
    [(slice-exit r) (t-slice-exit w r)]
    [(create-link st l) (if (create-refused w st) (refuse w) (require-root-open w true (t-create-link w st l)))]
    [(create-link-top sc l) (if (world-released w) (refuse w) (require-root-open w true (t-create-link-top w sc l)))]
    [(link-demand l k) (if (world-released w) (refuse w) (t-link-demand w l k))]
    [(link-realize l tag v n) (if (world-released w) (refuse w) (require-root-open w true (t-link-realize w l tag v n)))]
    [(append x v t) (if (world-released w) (refuse w) (require-root-open w true (t-append w x v t)))]
    [(close x tag v) (t-close w x tag v)]
    [(finally-leave st) (t-finally-leave w st)]
    [(own s m) (t-own w s m)]
    [(owned-done s c) (t-owned-done w s c)]
    [(drain ids) (t-drain w ids)]
    [(retire-local v) (t28-retire-local w v)]))

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
    [(spawn st b fresh ins loc) false]
    [(spawn-top sc b fresh ins loc) true]
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
    [(slice-exit r) false]
    [(create-link st l) false]
    [(create-link-top sc l) true]
    [(link-demand l k) false]
    [(link-realize l tag v n) false]
    [(append x v t) true]
    [(close x tag v) true]
    [(finally-leave st) false]
    [(own s m) false]
    [(owned-done s c) false]
    [(drain ids) false]
    [(retire-local v) false]))
(a/defn slice-held [w :- World] Bool (tbl-any run-slice (:runs w)))
(a/defn host-item-refused [w :- World, it :- Item] Bool
  (Bool.and (:released w) (Bool.and (host-item it) (Bool.not (slice-held w)))))
(a/defn host-guarded-transition [w :- World, it :- Item] Outcome (if (host-item-refused w it) (refuse w) (transition w it)))

;; after an accepted transition, the `any` losers are cancelled
(a/defn then-cancel-losers [w :- World, o :- Outcome] Outcome (if (:accepted o) (accept (cancel-losers w (:world o))) o))
(a/defn raw [w :- World, it :- Item] Outcome (then-cancel-losers w (host-guarded-transition w it)))

;; the item's validity token (§2): step's item-token-ok (with the Z#6 acknowledgement token)
(a/defn raw-token-ok [w :- World, it :- Item] Bool (item-token-ok w it))

;; an accepted raw outcome is followed by Rule R; a refusal is the input world
(a/defn then-rule-r [o :- Outcome] Outcome (if (:accepted o) (accept (rule-r (:world o))) o))
(a/defn world-step [w :- World, it :- Item] Outcome (then-rule-r (raw w it)))

(a/theorem well-formed-transition [w :- World, it :- Item]
  (=> (= (well-formed w) true) (= (well-formed (:world (transition w it))) true))
  (intro h)
  (cases it)
  (all_goals (simp only [transition]))
  (rename_i st kind v fresh) (cases hc (create-in-scope-refused w st))
  (simp only [hc]) (exact (well-formed-require-root-open w _ _ h (well-formed-t1-create-source w st kind v fresh h)))
  (simp only [hc refuse]) (exact h)
  (rename_i scope kind v fresh) (cases hc (world-released w))
  (simp only [hc]) (exact (well-formed-require-root-open w _ _ h (well-formed-t1-create-source-top w scope kind v fresh h)))
  (simp only [hc refuse]) (exact h)
  (exact (well-formed-t2-write w _ _ h))
  (rename_i st x k fresh) (cases hc (in-cleanup w st))
  (simp only [hc]) (exact (well-formed-t7-track w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (rename_i d cb fresh) (cases hc (world-released w))
  (simp only [hc]) (exact (well-formed-t8-observe w _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (well-formed-t8-unobserve w _ h))
  (exact (well-formed-t9-fire w _ _ _ h))
  (exact (well-formed-t15-resource-ack w _ h))
  (rename_i st kind k fresh) (cases hc (arm-refused w st))
  (simp only [hc]) (exact (well-formed-t17-arm w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (well-formed-t18-resource-fire w _ _ _ h))
  (exact (well-formed-t19 w _ h))
  (rename_i x) (cases hc (world-released w))
  (simp only [hc]) (exact (well-formed-t20-pin w _ h))
  (simp only [hc refuse]) (exact h)
  (exact (well-formed-t20-unpin w _ h))
  (rename_i st c i b) (cases hc (create-refused w st))
  (simp only [hc]) (exact (well-formed-t3-create w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (cases hc (world-released w))
  (simp only [hc]) (exact (well-formed-t3-create-top w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (rename_i st b fresh ins loc) (cases hc (create-in-scope-refused w st))
  (simp only [hc]) (cases hl (spawn-local-refused w st loc))
  (simp only [hl]) (exact (well-formed-t4-spawn w _ _ _ _ _ h))
  (simp only [hl refuse]) (exact h)
  (simp only [hc refuse]) (exact h)
  (cases hc (world-released w))
  (simp only [hc]) (exact (well-formed-t4-spawn-top w _ _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (well-formed-t5-start w _ _ h))
  (rename_i st ds m k fresh mine) (cases hc (await-refused w st ds m))
  (simp only [hc]) (exact (well-formed-t6-await w _ _ _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (well-formed-t11-dispatch w _ _ h))
  (rename_i st tag v) (cases hc (complete-refused w st tag))
  (simp only [hc]) (exact (well-formed-t12-complete w _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (well-formed-t-schedule w _ h))
  (rename_i d fresh) (cases hc (host-await-refused w d))
  (simp only [hc]) (exact (well-formed-t22-host-await w _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (well-formed-t22-host-unawait w _ h))
  (cases hc (world-released w))
  (simp only [hc]) (exact (well-formed-t-handle-new w _ h))
  (simp only [hc refuse]) (exact h)
  (exact (well-formed-t-deliver w _ _ h))
  (exact (well-formed-t-post w _ _ h))
  (rename_i st x k fresh) (cases hc (take-refused w st x))
  (simp only [hc]) (exact (well-formed-t-take w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (well-formed-t-release w _ h))
  (exact (well-formed-t-finalize w _ h))
  (exact (well-formed-t14-host-cancel w _ h))
  (exact (well-formed-t21-release-world w h))
  (exact (well-formed-t-open-scope w _ _ h))
  (exact (well-formed-t-close-scope w _ h))
  (rename_i k s) (cases hc (detach-local-refused w k s))
  (simp only [hc]) (exact (well-formed-t-detach w _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (well-formed-t-finally-enter w _ h))
  (exact (well-formed-t-finally-exit w _ h))
  (exact (well-formed-t-slice-exit w _ h))
  (rename_i st l) (cases hc (create-refused w st))
  (simp only [hc]) (exact (well-formed-require-root-open w _ _ h (well-formed-t-create-link w st l h)))
  (simp only [hc refuse]) (exact h)
  (rename_i sc l) (cases hc (world-released w))
  (simp only [hc]) (exact (well-formed-require-root-open w _ _ h (well-formed-t-create-link-top w sc l h)))
  (simp only [hc refuse]) (exact h)
  (cases hc (world-released w))
  (simp only [hc]) (exact (well-formed-t-link-demand w _ _ h))
  (simp only [hc refuse]) (exact h)
  (rename_i l tag v n) (cases hc (world-released w))
  (simp only [hc]) (exact (well-formed-require-root-open w _ _ h (well-formed-t-link-realize w l tag v n h)))
  (simp only [hc refuse]) (exact h)
  (rename_i x v t) (cases hc (world-released w))
  (simp only [hc]) (exact (well-formed-require-root-open w _ _ h (well-formed-t-append w x v t h)))
  (simp only [hc refuse]) (exact h)
  (exact (well-formed-t-close w _ _ _ h))
  (exact (well-formed-t-finally-leave w _ h))
  (exact (well-formed-t-own w _ _ h))
  (exact (well-formed-t-owned-done w _ _ h))
  (exact (well-formed-t-drain w _ h))
  (exact (well-formed-t28-retire-local w _ h)))

(a/theorem transition-refuse [w :- World, it :- Item]
  (=> (= (:accepted (transition w it)) false) (= (:world (transition w it)) w))
  (intro ha)
  (cases it)
  (all_goals (simp only [transition] at ha))
  (all_goals (simp only [transition]))
  (rename_i st kind v fresh) (cases hc (create-in-scope-refused w st))
  (simp only [hc] at ha) (simp only [hc]) (exact (require-root-open-refuse w _ _ ha (t1-create-source-refuse w st kind v fresh)))
  (simp only [hc refuse])
  (rename_i scope kind v fresh) (cases hc (world-released w))
  (simp only [hc] at ha) (simp only [hc]) (exact (require-root-open-refuse w _ _ ha (t1-create-source-top-refuse w scope kind v fresh)))
  (simp only [hc refuse])
  (exact (t2-write-refuse w _ _ ha))
  (rename_i st x k fresh) (cases hc (in-cleanup w st))
  (simp only [hc] at ha) (simp only [hc]) (exact (t7-track-refuse w _ _ _ _ ha))
  (simp only [hc refuse])
  (rename_i d cb fresh) (cases hc (world-released w))
  (simp only [hc] at ha) (simp only [hc]) (exact (t8-observe-refuse w _ _ _ ha))
  (simp only [hc refuse])
  (exact (t8-unobserve-refuse w _ ha))
  (exact (t9-fire-refuse w _ _ _ ha))
  (exact (t15-resource-ack-refuse w _ ha))
  (rename_i st kind k fresh) (cases hc (arm-refused w st))
  (simp only [hc] at ha) (simp only [hc]) (exact (t17-arm-refuse w _ _ _ _ ha))
  (simp only [hc refuse])
  (exact (t18-resource-fire-refuse w _ _ _ ha))
  (exact (t19-refuse w _ ha))
  (rename_i x) (cases hc (world-released w))
  (simp only [hc] at ha) (simp only [hc]) (exact (t20-pin-refuse w _ ha))
  (simp only [hc refuse])
  (exact (t20-unpin-refuse w _ ha))
  (rename_i st c i b) (cases hc (create-refused w st))
  (simp only [hc] at ha) (simp only [hc]) (exact (t3-create-refuse w _ _ _ _ ha))
  (simp only [hc refuse])
  (cases hc (world-released w))
  (simp only [hc] at ha) (simp only [hc]) (exact (t3-create-top-refuse w _ _ _ _ ha))
  (simp only [hc refuse])
  (rename_i st b fresh ins loc) (cases hc (create-in-scope-refused w st))
  (simp only [hc] at ha) (simp only [hc]) (cases hl (spawn-local-refused w st loc))
  (simp only [hl] at ha) (simp only [hl]) (exact (t4-spawn-refuse w _ _ _ _ _ ha))
  (simp only [hl refuse])
  (simp only [hc refuse])
  (cases hc (world-released w))
  (simp only [hc] at ha) (simp only [hc]) (exact (t4-spawn-top-refuse w _ _ _ _ _ ha))
  (simp only [hc refuse])
  (exact (t5-start-refuse w _ _ ha))
  (rename_i st ds m k fresh mine) (cases hc (await-refused w st ds m))
  (simp only [hc] at ha) (simp only [hc]) (exact (t6-await-refuse w _ _ _ _ _ _ ha))
  (simp only [hc refuse])
  (exact (t11-dispatch-refuse w _ _ ha))
  (rename_i st tag v) (cases hc (complete-refused w st tag))
  (simp only [hc] at ha) (simp only [hc]) (exact (t12-complete-refuse w _ _ _ ha))
  (simp only [hc refuse])
  (exact (t-schedule-refuse w _ ha))
  (rename_i d fresh) (cases hc (host-await-refused w d))
  (simp only [hc] at ha) (simp only [hc]) (exact (t22-host-await-refuse w _ _ ha))
  (simp only [hc refuse])
  (exact (t22-host-unawait-refuse w _ ha))
  (cases hc (world-released w))
  (simp only [hc] at ha) (simp only [hc]) (exact (t-handle-new-refuse w _ ha))
  (simp only [hc refuse])
  (exact (t-deliver-refuse w _ _ ha))
  (exact (t-post-refuse w _ _ ha))
  (rename_i st x k fresh) (cases hc (take-refused w st x))
  (simp only [hc] at ha) (simp only [hc]) (exact (t-take-refuse w _ _ _ _ ha))
  (simp only [hc refuse])
  (exact (t-release-refuse w _ ha))
  (exact (t-finalize-refuse w _ ha))
  (exact (t14-host-cancel-refuse w _ ha))
  (exact (t21-release-world-refuse w ha))
  (exact (t-open-scope-refuse w _ _ ha))
  (exact (t-close-scope-refuse w _ ha))
  (rename_i k s) (cases hc (detach-local-refused w k s))
  (simp only [hc] at ha) (simp only [hc]) (exact (t-detach-refuse w _ _ ha))
  (simp only [hc refuse])
  (exact (t-finally-enter-refuse w _ ha))
  (exact (t-finally-exit-refuse w _ ha))
  (exact (t-slice-exit-refuse w _ ha))
  (rename_i st l) (cases hc (create-refused w st))
  (simp only [hc] at ha) (simp only [hc]) (exact (require-root-open-refuse w _ _ ha (t-create-link-refuse w st l)))
  (simp only [hc refuse])
  (rename_i sc l) (cases hc (world-released w))
  (simp only [hc] at ha) (simp only [hc]) (exact (require-root-open-refuse w _ _ ha (t-create-link-top-refuse w sc l)))
  (simp only [hc refuse])
  (cases hc (world-released w))
  (simp only [hc] at ha) (simp only [hc]) (exact (t-link-demand-refuse w _ _ ha))
  (simp only [hc refuse])
  (rename_i l tag v n) (cases hc (world-released w))
  (simp only [hc] at ha) (simp only [hc]) (exact (require-root-open-refuse w _ _ ha (t-link-realize-refuse w l tag v n)))
  (simp only [hc refuse])
  (rename_i x v t) (cases hc (world-released w))
  (simp only [hc] at ha) (simp only [hc]) (exact (require-root-open-refuse w _ _ ha (t-append-refuse w x v t)))
  (simp only [hc refuse])
  (exact (t-close-refuse w _ _ _ ha))
  (exact (t-finally-leave-refuse w _ ha))
  (exact (t-own-refuse w _ _ ha))
  (exact (t-owned-done-refuse w _ _ ha))
  (exact (t-drain-refuse w _ ha))
  (exact (t28-retire-local-refuse w _ ha)))

(a/theorem well-formed-cancel-losers [w0 :- World, w1 :- World]
  (=> (= (well-formed w1) true) (= (well-formed (cancel-losers w0 w1)) true))
  (intro h) (exact (well-formed-run-cascade w1 _ h)))

;; a non-host item is never shut
(a/theorem host-guarded-transition-non-host [w :- World, it :- Item]
  (=> (= (host-item it) false) (= (host-guarded-transition w it) (transition w it)))
  (intro h)
  (cases hs (host-item-refused w it))
  (simp only [host-guarded-transition hs])
  (simp [host-item-refused h] at hs))

(a/theorem well-formed-host-guarded-transition [w :- World, it :- Item]
  (=> (= (well-formed w) true) (= (well-formed (:world (host-guarded-transition w it))) true))
  (intro h)
  (cases hs (host-item-refused w it))
  (simp only [host-guarded-transition hs]) (exact (well-formed-transition w it h))
  (simp only [host-guarded-transition hs refuse]) (exact h))

(a/theorem host-guarded-transition-refuse [w :- World, it :- Item]
  (=> (= (:accepted (host-guarded-transition w it)) false) (= (:world (host-guarded-transition w it)) w))
  (intro ha)
  (cases hs (host-item-refused w it))
  (simp only [host-guarded-transition hs] at ha) (simp only [host-guarded-transition hs]) (exact (transition-refuse w it ha))
  (simp only [host-guarded-transition hs refuse]))

(a/theorem well-formed-raw [w :- World, it :- Item]
  (=> (= (well-formed w) true) (= (well-formed (:world (raw w it))) true))
  (intro h)
  (have h0 := (well-formed-host-guarded-transition w it h))
  (cases ha (:accepted (host-guarded-transition w it)))
  (simp only [raw then-cancel-losers ha]) (exact h0)
  (simp only [raw then-cancel-losers ha accept]) (exact (well-formed-cancel-losers w _ h0)))

(a/theorem raw-refuse [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) false) (= (:world (raw w it)) w))
  (intro ha)
  (cases h0 (:accepted (host-guarded-transition w it)))
  (simp only [raw then-cancel-losers h0]) (exact (host-guarded-transition-refuse w it h0))
  (simp [raw then-cancel-losers h0 accept] at ha))

;; Z#10 / L4: an invalid token is a refusal
(a/theorem transition-l4 [w :- World, it :- Item]
  (=> (= (raw-token-ok w it) false) (= (:accepted (transition w it)) false))
  (intro hg)
  (simp only [raw-token-ok] at hg)
  (cases it)
  (rename_i st kind v fresh) (cases hc (create-in-scope-refused w st))
  (simp only [transition hc]) (apply require-root-open-l4)
  (simp only [t1-create-source t1-create-stream t1-create-nonstream (run-tok-none w _ hg) refuse ite_self])
  (simp only [transition hc refuse])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp only [transition in-cleanup opt-test t7-track (run-tok-none w _ hg) refuse])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp only [item-token-ok] at hg) (simp only [transition t9-fire hg refuse])
  (simp only [item-token-ok] at hg) (simp only [transition t15-resource-ack hg refuse])
  (simp only [transition arm-refused in-finally in-cleanup opt-test t17-arm (run-tok-none w _ hg) refuse Bool.or_false])
  (simp only [transition t18-resource-fire (res-tok-none w _ hg) refuse])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (cases hrs (world-released w))
  (simp only [transition create-refused in-cleanup hrs opt-test t3-create (run-tok-none w _ hg) refuse Bool.or_false Bool.or_true Bool.false_or ite_self])
  (simp only [transition create-refused in-cleanup hrs opt-test t3-create (run-tok-none w _ hg) refuse Bool.or_false Bool.or_true Bool.false_or ite_self])
  (simp [item-token-ok] at hg)
  (cases hrs (world-released w))
  (simp only [transition create-in-scope-refused in-cleanup cur-closed hrs opt-test spawn-local-refused t4-spawn (run-tok-none w _ hg) refuse Bool.or_false Bool.or_true Bool.false_or Bool.and_false ite_self])
  (simp only [transition create-in-scope-refused in-cleanup cur-closed hrs opt-test spawn-local-refused t4-spawn (run-tok-none w _ hg) refuse Bool.or_false Bool.or_true Bool.false_or Bool.and_false ite_self])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (rename_i st ds m k fresh mine) (cases hc (await-refused w st ds m))
  (simp only [transition hc t6-await (run-tok-none w _ hg) refuse])
  (simp only [transition hc refuse])
  (simp [item-token-ok] at hg)
  (simp only [transition complete-refused fins-open opt-test t12-complete (run-tok-none w _ hg) refuse ite_self])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp only [transition take-refused in-finally in-cleanup opt-test t-take (run-tok-none w _ hg) refuse Bool.false_and Bool.or_false])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp only [transition t-open-scope (run-tok-none w _ hg) refuse])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp only [transition t-finally-enter (run-tok-none w _ hg) refuse])
  (simp only [transition t-finally-exit (run-tok-none w _ hg) refuse])
  (simp [item-token-ok] at hg)
  (rename_i st l) (cases hc (create-refused w st))
  (simp only [transition hc]) (apply require-root-open-l4)
  (simp only [t-create-link (run-tok-none w _ hg) refuse])
  (simp only [transition hc refuse])
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp only [transition t-finally-leave (run-tok-none w _ hg) refuse])
  (all_goals (simp [item-token-ok] at hg)))

(a/theorem raw-l4 [w :- World, it :- Item]
  (=> (= (raw-token-ok w it) false) (= (:accepted (raw w it)) false))
  (intro hg)
  (have h0 := (transition-l4 w it hg))
  (have h1 (= (:accepted (host-guarded-transition w it)) false))
  (cases hs (host-item-refused w it))
  (simp only [host-guarded-transition hs]) (exact h0)
  (simp only [host-guarded-transition hs refuse])
  (simp only [raw then-cancel-losers h1]))

(a/theorem outcome-eta [o :- Outcome] (= o (Outcome.mk (:world o) (:accepted o)))
  (cases o) (rfl))

(a/theorem step-refuse [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) false) (= (world-step w it) (refuse w)))
  (intro ha)
  (have ho := (outcome-eta (raw w it)))
  (rw [(raw-refuse w it ha)] at ho)
  (rw [ha] at ho)
  (simp only [world-step then-rule-r ha refuse])
  (exact ho))

;; L4 for the step: an invalid token is a refusal and leaves the world unchanged
(a/theorem step-l4 [w :- World, it :- Item]
  (=> (= (raw-token-ok w it) false) (= (world-step w it) (refuse w)))
  (intro hg) (exact (step-refuse w it (raw-l4 w it hg))))

(a/theorem step-accepted [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) true) (= (:world (world-step w it)) (rule-r (:world (raw w it)))))
  (intro ha) (simp only [world-step then-rule-r ha accept]))



(a/theorem step-well-formed [w :- World, it :- Item]
  (=> (= (well-formed w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (well-formed (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h)
  (have e2 := (step-accepted w it ha)) (rw [e2])
  (exact (well-formed-rule-r (:world (raw w it)) (well-formed-raw w it h) hs)))


;; I3 after the step: every row is live, storage, in a cleanup entry or admitted
(a/theorem step-i3 [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) true)
      (= (live-converged (normalize (rule-r-last-input (:world (raw w it))))) true)
      (= (live-converged (rule-r (:world (raw w it)))) true)
      (= (tbl-all (keep-fn (:world (world-step w it))) (all-ids (:world (world-step w it)))) true))
  (intros ha hc hc2)
  (rw [(step-accepted w it ha)])
  (exact (rule-r-i3-step (:world (raw w it)) hc hc2)))

;; the step's world is normalized (no non-done run, no non-idle computation outside live)
(a/theorem step-normalized [w :- World, it :- Item]
  (=> (= (:accepted (raw w it)) true)
      (= (live-converged (normalize (rule-r-last-input (:world (raw w it))))) true)
      (= (live-converged (rule-r (:world (raw w it)))) true)
      (= (normalized (normalize (rule-r-last-input (:world (raw w it))))) true)
      (= (normalized (:world (world-step w it))) true))
  (intros ha hc hc2 hn)
  (rw [(step-accepted w it ha)])
  (exact (rule-r-normalized (:world (raw w it)) hc hc2 hn)))

;; I4 after the step: every active or parked run is in live(W)
(a/theorem step-i4 [w :- World, it :- Item, r :- RunRow]
  (=> (= (:accepted (raw w it)) true)
      (= (live-converged (normalize (rule-r-last-input (:world (raw w it))))) true)
      (= (live-converged (rule-r (:world (raw w it)))) true)
      (= (normalized (normalize (rule-r-last-input (:world (raw w it))))) true)
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
      (= (normalized (normalize (rule-r-last-input (:world (raw w it))))) true)
      (= (normalized (:world (world-step w it))) true))
  (intros ha hn)
  (exact (step-normalized w it ha (live-converged-all _) (live-converged-all _) hn)))

;; I4 after every accepted step whose normalization reports `normalized`
(a/theorem step-i4-total [w :- World, it :- Item, r :- RunRow]
  (=> (= (:accepted (raw w it)) true)
      (= (normalized (normalize (rule-r-last-input (:world (raw w it))))) true)
      (List.Mem r (:runs (:world (world-step w it))))
      (= (run-alive r) true)
      (= (in-live (:world (world-step w it)) (:id r)) true))
  (intros ha hn hm hr)
  (exact (step-i4 w it r ha (live-converged-all _) (live-converged-all _) hn hm hr)))
