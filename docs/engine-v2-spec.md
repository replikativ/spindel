# Spindel engine v2: specification

Status: **v1.5.1, signed off 2026-11-04, with numbered spec patches.**
Q4 and Q6–Q9 proceed with their proposals (§12). **Z#66 is the planned
restricted-cleanup contract (2026-11-05), specified before implementation.**
Its first slice is lexical cleanup operations and fork isolation; its dependent
second slice is world close/join. Neither slice is claimed implemented or
formally accepted here. References to Z#66 below state the target contract;
they do not describe shipped runtime behavior. Existing native protected-wait
prototypes are not acceptance evidence for this smaller operation API.

## History and tags

- v1 incorporated the decisions of 2026-11-03 and the review of v0
  (25 findings, `R#n`).
- v1.2 adopted **serial worlds** (D0) and fixed the review of v1.1
  (19 findings, `V#n`).
- v1.3 fixes the review of v1.2 (14 findings, `W#n`). It also applies the
  ansatz feasibility read (`A#n`):
  - **A#1:** opaque continuations;
  - **A#2:** an explicit cleanup table;
  - **A#3:** Rule R as a filter by `live`;
  - **A#4:** I11 split into I11a and I11b;
  - **A#5:** I13 as transition guards;
  - **A#6:** explicit ranks;
  - **A#7:** restricted finalizers;
  - **A#8:** L5 split into its safety and liveness halves;
  - **A#9:** no downward scope edges.
- v1.4 fixes the review of v1.3 (12 findings, `X#n`). Its main change is to
  make re-entry restricted, with no transfer of state:
  - a `dep` edge is re-entrant only at a site where its run holds no
    finalizer and no resource;
  - re-entry cancels the stale run normally and starts a new run from the
    edge's continuation (T11).
- v1.5 fixes the targeted review of v1.4 (`Y#n`). The fixes are local:
  - unchanged settlement requires a completed current run;
  - replacement cancels only the run being replaced;
  - group-await sites restart;
  - the inline budget counts ingress items;
  - a running run retains its finalizer refs;
  - detaching sources happens inside normalization.
- v1.5.1 clarifies retention after the ansatz §3 model (`Z#n`); no
  behavioral change:
  - `needs-run` is defined through `C.run` (Z#1);
  - creations are held through handles, with no "consumed" marker (Z#2);
  - finalizer refs are sources, and are kept as storage (Z#3);
  - armed publications with handles are roots (Z#4);
  - every source with `handles > 0` is admitted (Z#5).
- v1.5.1 also settles questions raised by the ansatz transition batch
  (Z#6–Z#19): resource debtors, slot positions, epoch steps, observe
  firing, refusals, effect indices, creation handles, pin counts, the
  `track` domain and the retirement order.
- Spec patches after sign-off, from the engine and the model (Z#20–Z#25):
  - Z#20: a settle, changed or not, delivers to unfilled activation members;
  - Z#21: suffix baselines keep retaining their debtors until adoption ends;
  - Z#22: on restart, E's baseline advances when the new run reads it;
  - Z#23: computations owned by a removed scope get `owner := ⊥`;
  - Z#24: validity uses the version each edge last consumed;
  - Z#25: detach also runs after the filter; T13 clears `K.run`; T10 cascades fully;
  - Z#26: a task run's scope has the task's owner scope as parent; a
    computation run's scope has none;
  - Z#27: pending host waits are roots (T22);
  - Z#28: T6 always allocates the activation id, even on the fast path;
  - Z#29: `handles` counts live handle objects. A row has at most one; an
    adoption reuses it while it is live and adds 1 only when it makes a new
    one (item `handle-new`), and T19 is its collection or explicit release;
  - Z#30: a settle fires every dep out-edge whose consumed version differs
    from the debtor's version (covers a debtor that completed changed while
    pending and then settles through the unchanged path);
  - Z#31: `await` on a signal or cell reads its current value at once (in a
    computation through a dep edge, like `track`; in a task as a snapshot);
  - Z#32: computations are never final in layer 1 (T3 replacement and
    explicit re-execution can always re-run them), so dep edges on them are
    not finalized (D1, T10);
  - Z#33: demand reactivates an idle computation in the demanding
    transition (`idle := false`, validity checked); a fresh or invalid one
    then starts by T5;
  - Z#34: a filled activation resumes its run in the filling commit; the
    run's next slice, like a new run's first, is a scheduling choice
    (`schedule r`); T12 includes the slice's exit;
  - Z#35: a cleanup slice unwinds the run's open finally regions innermost
    first, in one slice (the CPS error path runs them in sequence); each
    region's exit is a `finally-exit` item, so L2's measure still drops by
    one per finalizer;
  - Z#36: `deliver` is not a write: no computation consumed the undelivered
    deferred, so delivery marks nothing; it fires and finalizes (§4.3);
  - Z#37: host cancel of a run that holds the slice is refused (D0); posts,
    releases and writes to a closed source are refused; release-world drops
    every handle count to 0 (T21);
  - Z#38 (I1): a cleanup entry retains its run scope's ancestors as storage,
    so a scope's parent exists while any descendant scope is kept;
  - Z#39 (I5, T14): a cancelled entity becomes final; its dep creditors get
    the error delivery and their edges are removed (T10); T11 consuming an
    E whose debtor is final removes E instead of re-arming it;
  - Z#40 (B8, I9): a finalizer may write, deliver, post, release and close,
    nothing else: no creation, no track, no await, no offload; an unwinding
    run therefore holds no armed resource;
  - Z#41 (Z#26): `detach` re-parents the task's run scope to the new owner;
  - Z#42 (I10): demoting a computation steps its epoch when it cancels the
    current run, so a run kept in cleanup is stale;
  - Z#43 (T12, B-contract): completion with open finally regions is refused
    (the CPS body cannot produce it);
  - Z#44 (D0): host operations issued inside a slice (write, deliver, post,
    release, cancel, ...) are effects of the slice-holding run, processed at
    once; ingress from other threads is processed between slices;
  - Z#45 (§8.1): observe edges and host waits a fork inherits keep their
    demand in the child, but their callbacks belong to the parent's host
    and are not called there;
  - Z#46 (B6, Z#44): a host operation issued inside a slice acts on the
    slice's world, whatever world its handle was made in, so a body copied
    into a fork addresses the fork;
  - Z#47 (D3/Q4): `fork` is an effect of task runs (a computation's body
    cannot fork); the parent continues with `[:parent W']`, the child's copy
    of the run resumes at the effect with `[:child nil]`; forking from a
    nested slice (an inline demand) is refused for now;
  - Z#48 (I5, T7): `track` on a closed (final) source delivers its value
    once and its dep edge is consumed at once, as `await` on a final debtor
    (T6, T10);
  - Z#49 (log): a done run's slice that returns with the slice still held
    (a cleanup slice, an unwinding run) is the item `slice-exit r`;
  - Z#50 (I7, I10, model proofs): a result is `ok` or `err`, never none
    (T12); a filled activation resumes its run only when that run is parked
    on it, so a cancelled run never continues, and a savepoint `resume` or
    `activate` whose run is no longer parked there is refused (T9, S2, S4);
    `cancel(R, replace)` on a task run is an ordinary cancel (Y#2);
  - Z#51 (I5, §3.4): reactivation takes no dep edge on a debtor that became
    final while the computation was idle; a matching version keeps the
    result valid and the edge is consumed, as T6/T10/Z#48. In `slice-exit r`
    (Z#49), T13 retires the run within the item, as T12 does (Z#34);
  - Z#52 (I1, Z#38/Z#41): the ancestors a cleanup entry retains are its run
    scope's current chain through the parent fields, recomputed by each Rule R
    pass; a `detach` that re-parents a scope in the chain moves retention to
    the new parent. A run scope is removed no earlier than its run's
    retirement (T13 step 4), even when an ancestor's close empties its
    subtree first;
  - Z#53 (I5, T10, T16): closing a source fills its unfilled members and
    wakes its waiters (`dep` and `wait` edges alike): with the value for a
    signal, a cell or a delivered deferred, with `err ::closed` for a
    mailbox, a semaphore or an undelivered deferred. No run stays parked on
    a final debtor;
  - Z#54 (§4.3): `track` is for signals and cells; `await` on a mailbox is
    `take`; `await` on a semaphore, a group await with a consuming member,
    `track` on another kind and a host read of a mailbox or semaphore are
    errors;
  - Z#55 (T15, T17): a resource effect is one effect and one item
    `arm st kind k fresh` (resource, activation, wait edge allocated in that
    order); T15 retires the run (T13) within its own item, as Z#49/Z#51 do;
  - Z#56 (T21, §3.2, I1): a released world still accepts its finalizers'
    effects and its resources' completions, so cleanup joins (L2); a done
    task leaves its owner scope when its run retires, not when it finishes,
    so a cleanup entry keeps its tombstone and owner chain; the root scope
    is never removed;
  - Z#57 (§4.3, Z#53): `take`/`acquire` on a closed source consumes what is
    left; when nothing is, the effect fails at once with `err ::closed` (the
    take item is still committed, its wait edge consumed), instead of
    parking a run that nothing can wake;
  - Z#58 (F2, Q12, S3, S7; lifecycle design v2): forks are owned through
    markers in a per-world table (never inherited); owner close and
    `discard` release the child through its ingress, scheduled after the
    parent's gate is left; `fork`-effect markers are strong, root-owned
    markers (host forks, activated instances) weak, so an unreachable
    root-owned fork is collected without running its stuck finalizers; an
    instance is
    unborn until activation, gets its marker there, and is collected
    without running anything when dropped unactivated; a dropped pending
    publication abandons its run;
  - Z#59 (§4.5.1, T11, L5): marking starts only from computations whose
    dep edge on the written source fires (armed); T11's `E` is the earliest
    fired dep edge in creation order and its suffix is every dep edge created
    after it, siblings at `E`'s site included, so no fired edge outlives a
    re-entry;
  - Z#60 (§3.4, A#6): validation visits each idle computation at most once
    per demand and terminates by the acyclicity of validity entries, not by
    rank (ranks track live dep edges only); invariant I14 states the
    acyclicity;
  - Z#62 (§4.3, M6 parity): `semaphore(n)` starts with `n` permits and has
    maximum `n`; a release at the maximum is refused; a granted acquire
    delivers `:acquired`;
  - Z#63 (T15, T17, T18, §8.1; M6 R2): resource kind `external`. Its arm
    calls the host registration after the commit; its completion is a
    one-shot completion item (fire, then ack), accepted after release; its
    cancel calls the host cancel, which either answers `joined` (ack at once)
    or leaves the physical completion outstanding (it acks later, its value
    dropped). A resource's physical controller belongs to the world that set
    it: a copy in any other world holds none (F1), and an inherited external
    resource is dormant (§8.1);
  - Z#61 (T6, M6 parity with the old `parallel`): `await(all)` is fail-fast:
    its first `err` slot resumes the run with that error, and the unfilled
    members are released as `any` losers (loser tasks created for the await
    are cancelled);
  - Z#64 (§3.3 demotion, §3.4): a computation demoted while dirty (its
    result not for its current epoch: invalidated, or re-demoted at once
    after a failed validation) records validity `invalid`; validity is
    derived from its `dep` edges only when its result is current. Before,
    an idle chain read from the top returned a stale result.
  - Z#65 (§13; campaign decision 2026-11-05): public `race` and `timeout`
    are eager one-shot tasks. The first completion, including an error, wins;
    already-ready ties use input order. Shared input tasks are observed, not
    owned. Losing computations lose the race's demand. Create a race inside
    its owning task/scope to propagate cancellation; an externally created
    race is shared. Explicit `spin (await-any ...)` remains reactive.
  - Z#66 (§2–3, T12–T14, T21, T23–T26, B3/B8/B9, I6/I9/I11, §8.1,
    L2): planned explicit one-shot cleanup operations may be awaited only in
    lexical finalizers, including on normal entry. Cancellation publishes its
    result before cleanup retires, and preserves a sealed cleanup continuation.
    Inherited waits fail locally with `::forked`, including queued completions.
    World close/join additionally needs owned-child terminal acknowledgement
    (second slice). This supersedes Z#35's one-slice unwind and Z#40's prohibition
    of all cleanup waiting; ordinary offload remains forbidden. Formal obligations
    for these transitions are pending (§11), alongside the existing Z#64/I15 work.

  - Z#67 (C1, user decision 2026-11-16, `c1-cancellation-joins-design.md`):
    world completion (T21: released, every run retired, owned worlds complete
    or collected; host subscriptions that survive release), cancellation of
    the whole run-scope subtree at request time (T14, Q10), synchronous
    finalizers (B8 reduced to suspension), `await-op` with a race-safe
    controller and `idle?`. Task-level joins, deadlines and cross-world
    `spawn-in` follow; Z#66's cleanup operations remain planned.
  - Z#68 (T21, Z#40, Z#56; found by the C1 model): a released world takes no
    new root, also from its own cleanup slice: observe, pin and host waits
    are refused (`::released`, no item), so a quiet released world stays
    quiet. A Z#40 effect on a row Rule R already removed (a finalizer still
    holding a handle T21 revoked) reaches nobody and is not an item; the
    engine cannot record a finalizer's refs (§3.2 X#7) and relies on this.
  - Z#69 (Q10, Z#41; found by the C1c model check): `detach(K, S)` is refused
    when `S` lies in `K`'s own run-scope subtree (`K`'s run scope is on `S`'s
    parent chain). Otherwise re-parenting the run scope under `S` closes a
    cycle and neither scope is ever removed. Invariant: scope parents are
    acyclic.
  - Z#70 (C1c stage A, user decision 2026-11-16, `c1c-task-joins-design.md`
    v4, `c1c-options-evaluation.md`): **task completion.** A task is complete
    when it is done, its run has retired (T13) and its run scope was removed
    (Z#18) or never materialized; a scope is complete when its row is
    removed. Both are derived from the scope tree and stable. A run scope
    records its task when it is materialized. In T13, world completion (W1) is
    checked last, so a complete world implies every task in it is complete.
    Host `on-joined(K, cb)` / `await-joined` deliver once K is complete, or
    once its world is (an unborn instance's tasks never run: abandoned). They
    make no row, edge, handle or id and no item, are admitted after release,
    and are not inherited by forks. Not covered (stage A): computations
    created in the body and the tasks they own (world completion only), and
    forks owned by the task's scopes (stage B, Z#72). `detach` is refused into a
    scope of another world (family and lineage).
  - Z#71 (L12, W6, H2; a flaky merge test): engine metadata jobs (MVCC
    version pruning, handle-token drops, atom sweeps) are never ingress items
    and never work: each takes the gate only by trying, retries later, and
    hands off. `merge!` returns only after its item ran (as `host-call!`; B7)
    and waits out a turn or metadata job that holds the child's gate; it
    refuses only on the L12 conditions, never because a gate was briefly
    held. Before, version pruning was an ingress item, so a merge racing it
    saw a non-quiescent child, and a busy parent gate made `merge!` return
    false while the merge still ran later.
  - Z#72 (C1c stage B, `c1c-task-joins-design.md` v4 L2, model
    `spindel.v2.owned`): **owned-fork counts.** A fork made by the `(fork)`
    effect while its world is live and the forking run's current scope `s`
    is open is counted on `s` (W-OWNED-N) until it completes or is collected;
    the owner then runs the internal item `[:owned-done s child]` (accepted
    after release), which drops the count and applies Z#18 at `s`. Host
    forks and instances are owned weakly by the root scope and are not
    counted. A fork, savepoint basis or instance inherits the parent's
    counted scopes, with what the parent has not normalized yet, as
    W-NORMALIZE; it drains them at its first turn (an instance at its
    activation) with `[:normalize]`, applying Z#18 at each. Z#18 keeps a
    scope with a count or in W-NORMALIZE, so a task joins (Z#70) only after
    the forks its scopes own. W1: a world completes only with no count and
    an empty W-NORMALIZE; `[:owned-done]` and `[:normalize]` re-check it. A
    host item may precede the first-turn drain (the inline fast path), and
    the release of a child may precede its owner's `[:owned-done]`: neither
    completes a world early.
  - Z#73 (Z#68, H2; found by the foerster re-pin): Z#68's refusal goes to the
    caller only while that caller still waits on the operation. An observe or
    pin admitted before T21 but processed after it, in a turn another thread
    drains, is revoked as T21 revokes roots: its observe callback receives
    `::released`, its pin is dropped; no item either way. Before, the refusal
    was thrown into the draining thread (foerster: `release-world!` threw an
    observer's refusal).
  - Z#74 (§9, L12, R2, R6; C2, model `formal/c2-merge` sys.clj; user decision
    2026-11-17, option C): **seal, diff, resolver merge, transfer.**
    `seal(W)` refuses host admissions (task and computation starts from the
    host, observe) and every host source change (write, swap, deliver, post,
    semaphore release, append, close) until `unseal(W)`; bodies and
    propagation continue. A refusal throws `{:spindel/sealed true}` to a
    waiting caller; an item admitted before the seal and processed after it
    is a refused log entry (an observe's callback receives the refusal).
    Forks and instances start unsealed. `unseal` is refused in a released
    world. `diff(W′)` lists the inherited sources the mergeable fork changed,
    with base and current value; the base value is recorded at the fork's
    first copy of the row, which precedes its first change. `merge` requires
    the child sealed and quiescent as above (no unretired run, cleanup entry
    or outstanding resource, empty ingress; model F2: a run parked on an
    armed resource could fire and write after the seal), and the parent
    unsealed. A source both sides changed is passed to the caller's
    resolver `(f source base parent-value child-value)`, which returns the
    merged value or a refusal; it runs under both gates, is pure, and a throw
    is a refusal; the default refuses (L12 as before). One refusal refuses
    the whole merge. `transfer(m, k2)` moves the ownership of a fork owned by
    a root scope (host `fork!`, `:owner`, an instance) to `k2` of the same
    family in two steps (model sys-xfer-reserve/-move): `k2` reserves the
    obligation (kids + 1), then the old owner, under `m`'s gate, retargets
    `m`'s token to `k2`, drops its holder and ends its own obligation, and
    `k2` takes the holder in an item queued before `m` can complete; any
    failure undoes the reservation. Refused: a counted `(fork)`-effect
    child (it stays in its scope), `k2` the current owner, released or
    complete, or `k2` = `m` or a world `m` owns (a cycle). The token move is
    no log item. `descendant?(w, a)` is the lineage test; transfers change
    no answer.
  - Z#75 (I12, I14, §4.5.6, C1 Q5/Q8, T1/T2/T20; found by the ansatz formal
    review): (1) reactivation (validate) raises the creditor above each
    computation debtor as T6 does, and drops an edge whose raise would close
    a cycle: a debtor may be raised while its creditor is idle. (2) A host
    source change or host start admitted before T21 and processed after it is
    refused in its item (a refused log entry; a start allocates no id, its
    handle stays unbound), except a run's own slice (Z#40). (3) The blocked
    predicate and its propagation have no depth bound: from depth 64 on an
    exact iterative walk replaces recursion (a cycle is not blocked).
    (4) Kinds: write on signals and cells, deliver on deferreds, post on
    mailboxes, semaphore release on semaphores, take/acquire on mailboxes and
    semaphores, pin on computations, tasks and sources; misuse throws to the
    caller, or is a refused item when only the item sees it. Readoption by
    ordinal needs the same kind. `await-any` of no input is an error.
    `world-id` is public (unique within a family).
  - Z#76 (C1 Q5/Q8, T1/T3/T4; user decision 2026-11-18, model `world-released` on
    body paths): a released world takes no new work from bodies either: a
    body's spawn, computation, source or sequence creation in a released
    world throws `::released` before any item or state change. (Releasing
    from a body already cancels every run: tasks through the root scope,
    computations through their revoked demand; the refusal makes the rule
    explicit rather than a consequence.)
  - Z#78 (H2, H3; found by the dvergr port, 5d): a throw from a queued host
    item or a host callback belongs to that item's or callback's caller. The
    thread that processes it (another caller's inline budget, or the drainer)
    reports it and continues the turn; before, it escaped into that thread,
    so e.g. `release-world!` could throw `::released` from a `send-world!`
    item that wrote a source in the released world. Items run inline by
    their own caller still throw to it. No transition changes (a throwing
    item commits nothing it has not committed).
  - Z#79 (H2; user decision 2026-11-21, dvergr step 6b): **opt-in
    per-thread queued dispatch.** A JVM host thread inside
    `without-inline-turns` that holds no gate takes the non-inline path for
    its own operations, with the queued-result semantics listed in H2. A
    rejected handoff runs the drainer on a fresh platform thread instead of
    leaving the world marked scheduled with its queue stranded. No
    transition changes (another legal commit order); the model needs no
    change.
  - Z#77 (§1, §2, T4, T28, §5.2, I16, §8.1 F6, D3, S3/S8, §13; user decision
    2026-11-18, dvergr F9, `fork-local-design.md`): **fork-local tasks.**
    - A task started with `task-with {:fork-local true}` is fork-local, and
      so is every task its runs spawn under their scopes (fixed at creation;
      computations and their tasks never).
    - In every world derived from one that holds fork-local runs (host fork,
      `(fork)` effect, savepoint basis and instance, a fork of a fork), those
      runs are retired by the internal item `[:retire-local]` (T28),
      processed at the child's first gate entry before any other item, turn
      or activation:
      - no slice, finalizer, cleanup slice, host callback, resource fire,
        acknowledgement or timer re-arm happens for them;
      - their tasks without a result become final with `err ::forked`
        (`:spindel/fork-local true`), which inherited waiters receive, and
        complete (Z#70) in the child;
      - the sources their scopes own are closed (Z#18).
    - Everything else is inherited live as before.
    - Refused (`{:spindel/invalid :fork-local}`): `(fork)` in a fork-local
      run; `instantiate`/`consume` of its publication; the option inside a
      computation; `detach` of an unmarked task into a fork-local scope (a
      refused item).
    - Before this item, the inline fast path could process a host item in a
      never-entered fork before its first turn. That stays true for dormant
      activation and normalization; T28 precedes it.

Once approved, this document is the normative contract for the v2 engine. It
supersedes `engine-formalism.md` Part 4 and `engine-memory-v2.md`. Parts 1–3
of `engine-formalism.md` carry over unless this document says otherwise.

## Structure

Numbering:
- Requirements: `G*`
- Definitions: `D*`
- Host ingress: `H*`
- Transitions: `T*`
- Invariants: `I*`
- Temporal laws: `L*`
- Savepoint rules: `S*`
- Fork rules: `F*`
- Body contract: `B*`
- Open decisions: `Q*`

Sections:
- §1–7: normative layer 1 (one world);
- §8: layer 2 (forks and savepoints);
- §9: the settlement interface;
- §10–11: non-normative.

---

## 0. Workloads, goals, non-goals, gates

**Primary workloads.**
- **Probabilistic programming** (foerster):
  - SMC particles run as frozen forks of savepoints;
  - MCMC and other inference re-execute incrementally from a changed choice
    site;
  - replay depends on deterministic addressing.
- **Incremental updates** in data and UI pipelines.
- **Agent processes** (dvergr): long-lived tasks whose IO goes through
  deferreds.

Cheap forks, multi-shot savepoints and re-entry at an effect site are
first-class.

**G1 – memory.**
- Every retained row is reachable from an outstanding obligation (I11a).
- Each obligation's fan-out is bounded by its current content, never by
  history (I11b).
- A row loses its retention in the commit that removes its last reason. There
  is no deferred sweep.
- Host reachability (GC of handles) decides only about rows that have *no*
  engine reason:
  - idle caches, which may be recomputed;
  - unreferenced sources, which can no longer be written;
  - completed results and publications held by the host.

**G2 – resources.**
- Every run and resource has exactly one owner.
- Cancelling an owner reaches everything it owns.
- A run is retired exactly when these conditions hold together (T13, Z#66):
  - it is logically done;
  - its slice has exited;
  - its finalizers have exited, including any active boundary;
  - it has no cleanup waiter;
  - it has no outstanding resources.

**G3 – forks.**
- A fork costs O(1) at creation, plus O(touched pages) for later writes, plus
  O(inherited armed resources + inherited cleanup waits) when activated (Z#66).
- A terminally closed fork pins nothing; a release request may retain
  outstanding cleanup until acknowledgement (Z#66).
- Lineage is held as ids.

**G4 – performance.**
- Hard gate: median ≤ 10× missionary `m/cp` on JVM and Node.
- Goal: ≤ 1×. The hot-path spike measured 0.03–0.44× (§10).
- Allocation per update ≤ 20× missionary.

**G5 – verification.**
- Safety (I1–I13, L1, L4 and the safety half of L5) is a proof gate in
  ansatz over opaque continuations (§7, §11). Z#66's amended invariants and
  transitions remain unencoded/unproved; existing proofs do not cover them.
- Join progress (L2) requires the finite, acyclic, acknowledging cleanup
  assumptions below. Extending the per-run measure lemma for Z#66 is pending.
- The engine is checked against the ansatz-compiled model by differential
  testing.

**Non-goals for spindel:**
- settlement capabilities and custody;
- durable records and recovery;
- coordinated cuts;
- choosing merge policies (the engine applies a caller-supplied resolver,
  Z#74).

These belong to yggdrasil and dvergr, which build on §9.

**Gates:**

| Gate | Check |
|---|---|
| census | I11 is checked at every quiescent point, and row counts stay constant over 10⁵ iterations on JVM and Node for each workload: a dvergr-style task loop creating fresh computations, deferreds and timers; render/unmount churn; fork churn; savepoint publish/abandon churn; signal churn. The constant `k` of the row bound is measured here, not proved. |
| perf | The paired driver (≥ 5 interleaved trials) covers: fanout 100, chain 50, diamond, fanin 50, switch, switch-reactive, child per run, task lifecycle, task await, fork plus savepoint resume. |
| proofs | As in G5. |
| oracle | 10k generated programs with no divergence at any commit. |
| api | The existing public suites pass. The changes in §13 are approved. |

---

## 1. Vocabulary

- **World** `W`: an isolated state space. Its commits are linearizable.
- **Slice:** a maximal stretch of one run's body between two effects: from
  the run's start or a resume up to the next suspension, return or throw.
- **D0 – serial world (decided 2026-11-04).**
  - A world executes **at most one slice at a time**. The active slice holds
    the world's gate.
  - Every transition is a step of the world's single execution:
    - an effect of the active slice;
    - a completion;
    - a scheduling choice;
    - an ingress item processed between slices (H1).
  - Different worlds run in parallel. CPU parallelism inside one world's work
    comes from `offload` (§4.3) or from separate worlds (forks, instantiated
    savepoints).
  - Consequences:
    - no slice observes another slice's partial state;
    - a fork or savepoint boundary is the active slice itself;
    - user code inside a slice may run while the gate is held. This includes
      bodies, result equality and `swap!` functions.
- **Scope** `S`: a lifetime container. Scopes form a tree from the world root.
  Every run has a *run scope*, and explicit scopes come from `with-scope`.
  A task run's scope has the task's owner scope as its parent; a
  computation run's scope has no parent, because computations are retained
  by demand only (Z#26).
- **Computation** `C` (`spin`):
  - a body with a deterministic id, captured inputs and a cached result;
  - reactive: `track`, and `await` on non-final debtors, are *dependencies*.
- **Task** `K`:
  - an uncached body, used for processes, loops, agent turns and pumps;
  - subsumes `spawn!` and the work-admission `task`;
  - every `await` in a task is a one-shot *wait*.
- **Fork-local** (Z#77): a task created with the fork-local option, or owned
  by a fork-local scope; a scope is fork-local when its parent chain reaches
  the run scope of a fork-local task. The mark is fixed at creation.
  Computations and the tasks they own are never fork-local.
- **Run** `R`: one execution of a body. Its stamp `R.stamp` is fresh from the
  family allocator (§2) and never reused.
- **Source** `X`: signal, cell, deferred, mailbox or semaphore. Each kind has
  its operation contract (§4.3).
- **Edge** `E`: a subscription from a creditor to a debtor, with its own
  identity.
  - A `dep` edge is a computation's standing dependency. Its creditor is the
    computation, never a run (W#2).
  - A `wait` edge is consumed once. Its creditor is an activation.
- **Activation** `A`: one suspended `await` of a run. It holds the run's
  continuation, its mode (`one`, `all` or `any`), its member edges and their
  result slots. It references edges and does not own `dep` edges (V#4,
  W#2).
- **Resource** `Z`: a physical obligation owned by a run:
  - a timer;
  - an external wait;
  - an `offload` operation;
  - a native operation.
- **Finalizer** `F`: a lexical `finally` region that is open in a run; its
  boundary remains open until its body returns or throws, including while waiting.
- **Cleanup operation** `O` (Z#66, planned): an opaque one-shot capability for
  an explicitly declared, already-owned resource close/join. It is not a Spin,
  Task, deferred, mailbox, signal or arbitrary CPS function. Its adapter has
  finite nonblocking registration; physical close belongs to the operation,
  independently of its subscribers. Its **observation origin** (the world
  permitted to await it) is distinct from its **target** (the resource/world
  being closed). Origin checks compare the awaiting world with that observation
  origin, not with the target's world (§9). This is not a user-extensible scheduler.
- **Cleanup waiter** `Q` (Z#66, planned): one run's observation of `O`, holding
  a sealed finalizer continuation rather than an ordinary activation or edge.
- **Handle** `H`: a host object, for example `Spin`, a signal, a fork
  handle or a savepoint publication. Handles are weak and are never liveness
  reasons (§3.4), except that an armed publication's handles make it a root
  (§3.1, Z#4). A body's reference to an entity it created, held in its
  continuation, is such a handle (Z#2).
- **Ownership** is *cancellation and cleanup responsibility*. **Retention** is
  *reachability* (§3). These are deliberately separate (R#10).

---

## 2. State (layer 1)

Continuations are opaque values `k` (A#1). Layer 1 does not model body
trees.

```
Family = { stamp : Nat }                         ; fresh-id allocator shared by related worlds (R#5)

World  = { scopes  : S ↦ {parent: S?, kind: root|run|explicit, open: Bool}
           comps   : C ↦ {owner: S|C|⊥, inputs, body, run: R?,
                          epoch: Nat,                          ; increments when a rerun is required
                          done-epoch: Nat?,                    ; epoch of the run that set the result
                          pending: Nat,                        ; marked in-edges from dirty computations
                          rank: Nat,                           ; A#6
                          version: Nat, result: none | ok v | err e,
                          idle: Bool, validity: [(debtor, version)],    ; idle only
                          basis: {(C ∪ X ∪ K) × at},           ; creations of the last run
                          adoption: {basis, baselines: (site, X) ↦ baseline}?,   ; T11
                          handles: Nat}
           tasks   : K ↦ {owner: S|C, run: R?, result: none | ok v | err e, handles: Nat,
                          local: Bool}                         ; Z#77; scope locality is derived (§1)
           runs    : R ↦ {of: C|K, stamp, epoch: Nat, scope: S,
                          act: active | parked | done,
                          mode: normal | unwinding,
                          slice: Bool,
                          effect-index: Nat,                   ; Z#12: +1 per body effect; an effect's `at` is the index before it
                          finalizers: [(F, at, refs)],         ; open regions, innermost first; refs ⊆ sources (Z#3)
                          finalizer: {F, pending-outcome, k, ek}?, ; active boundary and outer unwind, Z#66
                          cleanup-wait: {origin, generation, sequence, F, operation,
                                         phase: registering|waiting|ready,
                                         k, ek, control}?,     ; sealed continuation, at most one, Z#66
                          cleanup-failures: [(region, release, error)], ; current report, Z#66
                          resources: {Z}}                      ; outstanding only
           sources : X ↦ {owner: S|C|⊥, kind, state, version: Nat, open: Bool, handles: Nat}   ; Z#13: created with version 0, open, handles 1
           edges   : E ↦ {kind: wait|dep|observe|savepoint,
                          creditor: C|A|host, debtor: C|K|X|Z, ; savepoint: creditor A, debtor its publication's entity; Z: wait edges only (Z#6)
                          cont: k | restart, at: Nat,          ; dep: re-entry point (X#2)
                          phase: armed | fired, marked: Bool,  ; marked: counted in creditor.pending
                          seen: Nat?,                          ; observe: last delivered version, none until the first delivery (Z#15)
                          baseline: (value, version)?}         ; track edges (§4.4)
           acts    : A ↦ {run: R, mode: one|all|any,
                          members: [(E, i)],                   ; unfilled members only (X#4), with slot index i (Z#7)
                          slots: [result?], remaining: Nat, cont: k}
           res     : Z ↦ {owner: R, kind, at: Nat, phase: armed|fired|cancelling}
           cleanup : R ↦ {rows: [row]}                         ; A#2: rows R must clean up
           pubs    : P ↦ {edge: E, basis, handles: Nat}
           pins    : (C ∪ X) ↦ Nat                          ; Z#16: a count; a row is pinned while its count is > 0
           forks   : M ↦ {child: world-id, owner: S}
           pending-activation : E?
           ingress : [item]
           released: Bool
           close: {pending-local, pending-children, failures,
                   subscribers, outcome}? }                 ; Z#66 slice 2: fresh world-local state
```

**Planned finalizer state (Z#66).** A boundary records the pending body
outcome separately from the entity's published result. Entry marks an already
registered region active; only exit removes it, on either success or exception.
Generated exit bookkeeping is not another finally region. A normally entered
finalizer may wait with `mode = normal`; cancellation converts its admission to
cleanup without replacing or restarting the boundary. A waiter is reachable only
through its run. It cannot grant demand, make a computation current/hot, or
install a normal activation/savepoint. Its origin is immutable world identity,
not the mutable copy-on-write owner epoch. Mutable boundary/waiter containers
must be copied before child edits; physical controls and callback authority must
never be copied (§8.1).

**Derived status of a computation.**
- `fresh`: `done-epoch = none`.
- `live`: `¬idle ∧ done-epoch = epoch ∧ pending = 0`. Its result is
  available.
- `dirty`: `¬idle ∧ ¬live ∧ ¬fresh`. Its result is unavailable.
- `needs-run`: `done-epoch ≠ epoch`, and `C.run` is none or not current
  (Z#1).

**`C.run` is the latest run (Z#1).** It is none or an existing run of `C`.
Only T5 and T11 create runs of `C`, and both set `C.run`. Hence `C` has at
most one current run, and if it has one, it is `C.run`. Retiring `C.run`
(T13) sets `C.run := none`.

A run `R` of `C` is **current** iff `R.epoch = C.epoch`, and **stale**
otherwise (W#1).

**`pending` is exact (X#1):** `C.pending` is always the number of existing
in-edges of `C` with `marked = true`.
- Marking an already marked edge is a no-op.
- Removing a marked edge decrements its creditor's `pending` in the same
  edit, and so does unmarking one.

**Re-entrant sites (X#2, X#3):** when a computation run registers a `dep`
edge at site `at`, the edge's `cont` is the run's continuation only if all
of these hold:
- the run then holds no finalizer;
- it holds no outstanding resource;
- the await has mode `one` (Y#3).

Otherwise `cont` is `restart`. A continuation after an `all`/`any` group
expects the whole group's result, so a single member's value cannot resume
it.

**Validity tokens (V#5).** Every operation carries the token of what it acts
for:
- **A body effect or completion** carries `R.stamp`. It is valid iff `R`
  exists, `R.slice` holds, and one of:
  - `R.mode = normal`;
  - `R.mode = unwinding` and the slice executes `R`'s head finalizer (W#3).
  The second case means `mode = unwinding ∧ finalizers ≠ []`: an unwinding
  run's slice is always its head finalizer's cleanup slice (Z#11).
- **A fire** carries the edge id. It is valid iff the edge exists and is
  `armed`.
- **A resource fire** carries the resource id. It is valid iff the resource
  row exists and is `armed`; a `cancelling` resource does not fire (Z#14).
- **A resource acknowledgement** carries the resource id. It is valid iff
  the resource row exists and no edge has it as debtor (Z#6).

Z#66 does not broaden ordinary run validity or ordinary resume guards. A
separate finalizer capability admits only B8 effects while a boundary executes,
on normal return, failure and cancellation alike. Cleanup completion validates
its origin, generation, sequence and boundary before invoking only the sealed
continuation (T25); it grants no ordinary body authority. Hidden helper calls,
custom effects and direct creation helpers must obey the same runtime check.

An invalid operation is a refusal: it is reported as not accepted and
changes nothing (L4, Z#10).

**Creation handles (Z#13).** Every creation (T1, T3, T4) starts with
`handles = 1`, including inside a body, where the handle is the body's
reference (Z#2). Adopting an existing computation in T3 adds one handle.

**Effect index (Z#12).** `effect-index` starts at 0 for a run started from
the body. A run that resumes `E.cont` in T11 starts at `E.at + 1`, so its
suffix sites get the same `at` as in the predecessor.

---

## 3. Retention

### 3.1 Roots

1. the world root scope while the world is not released;
2. pins;
3. `observe` edges;
4. explicit scopes that are open;
5. `pending-activation`, until it is activated or abandoned;
6. publications with `handles > 0` whose edge is armed (S7, Z#4);
7. pending host waits: `wait` edges whose creditor is the host (T22, Z#27).

### 3.2 Retention edges

`live(W)` is the **least** set that contains the roots and is closed under
these edges:

| From (live) | To |
|---|---|
| scope `S` | its parent scope; the task runs it owns; the fork markers it owns |
| run `R` (`act ≠ done`) | its run scope; its body entity; its activations; its resources; its `savepoint` edges |
| activation `A` | its member edges |
| computation `C`, not idle | `C.run` if it is current, or if `C` is `needs-run` and `C.run` is not done (the re-entry predecessor of T11) (Z#1); its `dep` edges; its `basis`; its `adoption` basis; the debtors of its adoption baselines (Z#21) |
| task `K` | its run |
| edge `E` | its debtor |
| publication `P` | its edge |

- **No downward scope edges (A#9).** A scope does not keep its child scopes
  alive. A run scope is reachable only from its run. Open explicit scopes are
  roots.
- A computation is retained only by **demand**: an edge on it, a `basis`
  membership of a live computation, or a pin. Its owner scope does not keep
  it. A task is retained by its owner scope while it runs.
- **Creations (Z#2).** A run keeps no extra reason for what it created.
  Running tasks are kept by their owner scope, and demanded computations
  by their edges. The body's reference to a creation is a handle, so a
  completed task or an undemanded computation it has not awaited yet is
  kept by §3.4 while that handle exists.

**Storage (X#7, Z#3).** `storage(W)` is the set of `refs` of the finalizers
of runs in `live(W)`. Refs are sources only: B8 lets a finalizer write,
deliver, post, release and close. Z#66 additionally retains an active boundary,
its pending outcome and its optional waiter/operation capability as cleanup
storage, including a normally entered finalizer parked before result publication.
An operation retains only its current close/join payload and subscriptions;
it is not a reactive debtor. Storage rows are kept but not expanded, and grant
no demand. A ref whose owner is removed is detached and closed like any other source (§3.3).

**Cleanup table (R#2, W#4, A#2).** Every run with `act = done` that is not
retired has an entry `cleanup[R]`, kept outside `live`:
- **The rows it retains as storage:**
  - its run row;
  - its run scope and that scope's subtree;
  - the current ancestor chain of its run scope, followed through the
    scopes' parent fields at each Rule R pass, not stored with the entry,
    so it follows a `detach` (Z#38, Z#52);
  - its outstanding resources;
  - its finalizers, active boundary, pending outcome and optional cleanup waiter;
  - its body entity as a tombstone when the entity has no other reason;
  - the rows it owns that have no other reason.
- **What its finalizers may touch:** these rows, plus the `refs` recorded
  with each finalizer at registration (X#7). `cleanup[R]` retains those refs
  as storage. They grant no demand, so a shared semaphore can still be
  released.
- **What it may not do:** start runs or grant demand.
- **When it goes:** with the run, at retirement (T13).

Z#66 makes normally entered pending finalizers obligations too: cancellation or
stale replacement moves their existing boundary/waiter to cleanup retention,
without dropping queued readiness or adding a second subscription. Callback,
continuation and detachable-control references clear when consumed or withdrawn.
A held callback after terminal claim contains no world/run reference. A held
terminal operation contains only its outcome, not a world, release closures,
child controllers or subscriber list. Pending diagnostics describe current
obligations, never an append-only event history. A nonacknowledging operation
remains pending and observable; a timeout cannot certify retirement.

### 3.3 Rule R (A#3, X#10)

After every commit:

1. **Normalize, to a fixpoint.** Repeat until nothing changes:
   1. recompute `live(W)`;
   2. cancel (T14) every `active` or `parked` run that is not in `live`;
   3. demote every non-idle computation that is not in `live`:
      - its current and stale runs are cancelled;
      - its `dep` edges are removed;
      - the tasks in its `basis` are cancelled;
      - if it has a result or `handles > 0`, it becomes `idle`, with
        `validity` taken from the removed edges' `(debtor, version)`, where
        `version` is the debtor version the edge last consumed. An edge that
        never consumed one makes the validity fail (Z#24). Without a result
        it stays `fresh` (Z#2);
      - otherwise it is removed.

   4. detach (step 2) every source or task whose owner was removed in this
      round. Closing a detached source can finalize it, and T10 cascades
      inside the loop (X#10).

   Cancelling can retire runs and close scopes (T13, T16), which shrinks
   `live`; that is why this step loops. It terminates, because each round
   that changes something decreases the number of non-done runs plus
   non-idle computations.
2. **Detach (W#6, X#5)**, applied inside step 1 and once more after step 3
   (Z#25): every source or task that survives and whose owner is removed
   gets `owner := ⊥`, and so does every computation (Z#23), without being
   cancelled. A detached source is
   closed. A detached task has already been cancelled by its owner's
   demotion or scope closure, so it only finishes its cleanup.
3. **Remove:** every row that is not in the final `live`, not in
   `storage`, not in `cleanup`, and not admitted by §3.4.

**Proof shape:** normalization is proved separately, as terminating and
establishing "no non-done run or non-idle computation outside `live`". The
filter in step 3 then gives I3, and L1 follows.

### 3.4 Rows without engine reason

- **An idle computation** keeps only `{result, version, validity, inputs,
  body}`. A fresh one has no result and is kept for its handle (Z#2).
  - It *may* be dropped at any time (implementation policy).
  - It *must* be dropped when `handles = 0`.
- **A source** with `handles > 0` is admitted, whether referenced or not
  (Z#5); a referenced one is also in `live`. It remains because the host
  may still write it. It is removed at `handles = 0` (T19). A source cannot
  be recomputed, so it is never dropped by policy.
- **A completed task with `handles > 0`** keeps only its result.
- **A publication with `handles > 0`** keeps its basis pages (§8.2). While
  its edge is armed it is a root (§3.1); once the edge is gone it keeps
  only its basis.

**Validation (R#3).** Demand on an idle computation `C`, by `await`,
`observe`, `dep` or adoption, first validates it, recursively in rank order:
1. Every computation debtor in `validity` is validated first, salsa-style.
   A debtor that is dirty, or has a run in progress, counts as **changed**.
   Validation therefore never waits.
2. `C` is valid iff every debtor still exists with the recorded version.
3. **Valid, and the demand is reactive** (`observe` or `dep`):
   - `C` is reactivated: `idle := false` and `done-epoch := epoch`;
   - it gets `dep` edges on its `validity` debtors whose `cont` is
     **restart**, with baselines equal to the recorded state; a debtor
     that is final gets no edge (Z#51);
   - a later change re-runs `C` from the beginning.
4. **Invalid:** `C` is re-run (T5).

Each idle computation is validated at most once per demand: validating
it clears its idle flag, so every later path reaches it as non-idle and
only compares versions. The walk is linear in the idle computations it
reaches. It terminates because the validity graph is acyclic: its entries
are recorded from `dep` edges, which are acyclic (I12), and an idle
computation's entries are frozen until it is validated. Ranks do not bound
it: they are maintained for live `dep` edges only (Z#60, I14).

`version` increments on each completion whose result differs from the
previous one. The comparison is `=`, evaluated inside the completing slice
(D0). For values without value equality it falls back to `identical?`.

---

## 4. Effects, finality, sources

### 4.1 Finality

**D1 – final.** `d` is final when its value can never change:
- a task that has completed;
- a deferred that has been delivered;
- a closed source (T16);
- an unkeyed source with `handles = 0` and no live writer;
- a computation that is `live`, has no `dep` edges, and is not rerunnable.

**Rerun sources.** Explicit re-execution (`rerun!`, `trace/update`,
`what-if`, a public invalidation) is a write to a computation's implicit
*rerun source*. A computation that admits re-execution holds a `dep` edge on
its rerun source, so it is never final while it can be rerun.

**D2 – consumption.**
- A `wait` edge is removed when its activation is resumed or removed.
- When a `dep` edge's debtor becomes final, the edge is removed after its
  current delivery (T10).

### 4.2 Edge phases

- **`dep` edges** stay registered across deliveries.
  - A fire moves an edge to `fired` and invalidates or delivers (T9).
  - A delivered `dep` edge returns to `armed` with its new baseline in the
    same commit, unless its debtor is final; then it is removed.
- **`observe` edges** are persistent.
  - A fire delivers `(value, version)` to the host callback and sets
    `seen := version`.
  - A fire whose version is ≤ `seen` is a no-op, which rejects delayed
    duplicates.

### 4.3 Source kinds and host operations

Consuming operations always create `wait` edges, even inside computations.
They are never dependencies. All operations are atomic commits (D0).

| Kind | Operations |
|---|---|
| signal, cell | `write(X, v)` (T2), `track` (dep edge) |
| deferred | `deliver(X, v)` once: fires all `wait` edges and finalizes the deferred; `await` in a computation is a dep edge that is consumed at once if the deferred is final |
| mailbox | `post(X, v)` appends to the queue; `take(X)` is a wait edge; FIFO, each message is delivered to exactly one waiter atomically; cancelling a waiter removes it from the queue order; on a closed, empty mailbox `take` fails at once with `err ::closed` (Z#57) |
| semaphore | `acquire(X)` is a wait edge, and a permit is consumed atomically on fire; `release(X)` fires the first armed waiter or increments the permit count, up to the maximum (Z#62); cancelling a waiter removes it; on a closed semaphore without permits `acquire` fails at once with `err ::closed` (Z#57) |
| link | A once-cell of an async sequence (C0), owned by the root scope. Final once realized: with `[v next]` (`next` the next link's handle), `end` (nil) or a memoized error. Awaited like a deferred, never tracked. Created by `create-link` (a pull head: `[:create-link R L]` in a run, `[:create-link-top root L]` on the host; in a computation run a creation in its basis, adopted on re-entry with equal captures and initial state, the item then naming the adopted link). A pull link carries a realizer `[f s]`: demand on it while unrealized and without a realizer (T6, T22) creates and starts its realizer task in the root scope in one item `[:link-demand L K]`; at most one unfinished realizer per link. The realizer's completion (its T12 item) is followed by one item `[:link-realize L tag v N]`: `tag 1` creates the next pull link `N` with `[f s']` and realizes `L` with `[v N]`, `tag 0` realizes the end, `tag 2` memoizes the error `v` (`N = 0` for both); an error `::forked` (§8.1) realizes nothing and, if `L` is demanded, is followed by a new `link-demand`. A cancelled realizer (T21) realizes nothing (no item). A link that nothing reaches any more (no handle, no edge) is not realized. A push link has no realizer and is realized by its stream. |
| stream | A producer whose state is its tail link, owned per §5.2; its creation item also creates the first tail (ID = the stream's + 1). `append(X, v)` is one item `[:append X v T]`: it creates the new tail `T` and realizes the old one with `[v T]`; on a closed stream, or once the root scope is closed (a released world's cleanup finalizers), it is refused; no root-owned link is created after release. `close(X)` / `close(X, err)` is one item `[:close X tag v]` (tag 0 end, 2 error) that realizes the tail and closes `X`. T16 (the owner's scope closes, Z#18) and, for a stream in a computation's basis, the computation's demotion (§3.3) realize the tail as `end` and close `X` inside that item. Not awaitable: readers hold positions (links). |

**Operation by kind (Z#54).** `track` applies to signals and cells only.
`await` on a mailbox is `take`. `await` on a semaphore, `await-all` or
`await-any` with a mailbox or semaphore member, and `track` on any other
kind fail the effect with `err` (no commit). The host read of a mailbox or
semaphore (T22) is refused.

**Links and forks (C0).** A link is a row: a fork copies it with the
world, so an element is realized at most once per world. A realizer that
was running at the fork continues in both worlds, and in the fork it gets
`::forked` where its run waited on a physical resource (then it restarts
as above). Links are not part of a mergeable fork's basis (L12); a stream
the fork appended to is, so such a merge is refused (stream merge: C2). A
link carries `[stream-id index]` for portable positions (C3).

**Offload.** `offload(f)` arms a resource `Z` that runs the plain function
`f` on a host executor, outside every world, and parks the run on a `wait`
edge.
- When `f` returns or throws, an ingress item fires the edge.
- Cancelling the run interrupts `f` on a best-effort basis.
- `Z` is joined when `f` has actually returned.
- `f` must not call into the world synchronously. It may enqueue ingress.

**`await-op` (C1).** `(await-op op)` runs a partial-cps op `(fn [resolve
reject])` as a resource of kind `op`, started on the world's executor after
the gate, with the run's bindings (B10) and the originating world.
- Start and cancel are arbitrated atomically: cancelled before it started, it
  never starts and is acknowledged at once.
- During start the op registers cancel hooks (`on-cancel!`); a registration
  after cancellation runs at once. Cancel runs each committed hook once, on the
  executor.
- The first `resolve`/`reject` fires the resource (T18). It is acknowledged
  (T15) only when start has returned, every committed hook has returned and the
  op settled. Adapter precondition: settle only after the op's own host work
  has finished.
- `{:detach true}`: cancel acknowledges at once and later results are dropped.

**`idle?` (C1).** A host snapshot: nothing runnable, no cleanup queued, no
outstanding resource in any phase, nothing dormant, no queued ingress. Parked
runs may remain; idle is not completion.

### 4.4 Track intervals (R#22, W#12)

Each `track` *site* in a run (identified by `at`) has its own edge, with
`baseline = (value, version)`: the state its creditor last observed there.

- **First track at a site:** the edge is created with the current state as
  baseline. The creditor receives `⟨old = nil, new = value, deltas = nil⟩`.
- **Delivery after a fire:** the creditor receives
  `⟨old = baseline.value, new = current value, deltas⟩`. The baseline is then
  advanced.
- **Re-entry (T11):** T11 moves the baselines of removed suffix edges into
  `C.adoption.baselines`, which keep retaining their debtors (Z#21), so a
  suffix debtor stays cached until the new run awaits it again or
  completes without it. A suffix site that the new run tracks again
  consumes its entry; otherwise it is a first track. The map is discarded
  together with the adoption basis. It is bounded by the number of suffix
  edges.
- **Deltas:** `deltas` is the composition of the source's deltas since
  `baseline.version`, or `nil` when they are not available.
- **Delta log:** a source keeps its log back to the oldest armed baseline,
  truncated at a constant bound `B`. A truncated range yields `nil`.

### 4.5 Coherence and scheduling (R#6, V#1, V#2, W#1, W#7)

1. **Mark.** In the same commit as a write to `X`:
   - every `dep` edge on `X` fires (T9), and every `observe` edge on `X`
     delivers (§4.2, Z#9);
   - for every computation whose `dep` edge on `X` fires (it was armed),
     and every computation reachable from those through `dep` edges, each
     in-edge from a computation that is being marked is set
     `marked := true`. Each such edge increments its creditor's `pending`.
     A fired (unarmed) edge on `X` starts no marking (Z#59).
2. **Settle.** When a computation `D` settles, each marked out-edge of `D`
   is unmarked and decrements its creditor's `pending`. `D` settles when it
   becomes `live` or idle, or is removed.
   - **Changed:** `D`'s completion changed its version. Its `dep` out-edges
     fire (T9) before they are unmarked, and its `observe` edges deliver
     (Z#9).
   - **Delivery (Z#20):** in both cases, an out-edge that is an unfilled
     member of an activation of its creditor's current run is delivered
     (T9), since that run is waiting for `D`'s coherent result. It is not an
     invalidation.
   - **Unchanged:** `D` reached `pending = 0` with `done-epoch = epoch` (Y#1).
     A current run that has not completed does not count. It becomes `live` again without running, and its
     marked out-edges are unmarked without firing.
3. **Invalidation is an epoch step.** A `dep` fire into `C` that is not a
   delivery (T9) sets `C.epoch += 1`. This happens per fire, so two sites
   fired in one commit add 2. Epochs are only compared for equality, and
   T3's epoch step is this same step for the rerun-source fire, not a
   second one (Z#8). This makes `C`'s current run stale and
   `C` `needs-run`. A delivery into an activation of a current run does not
   change the epoch.
4. **Stale runs cannot consume or publish (W#1, I13).**
   - A fire into an activation of a stale run is not delivered. The edge
     stays `fired`, as the re-entry point.
   - A completion by a stale run does not set the result. The run is
     retired (T12).
   - A stale run is cancelled when its replacement starts (T11).
   - The replacement run is current, so its completion publishes.
5. **Dirty results are unavailable.** A computation's result is consumed
   only when it is `live`. Awaiting a computation that is not `live` parks
   the creditor's activation, and the T6 fast path does not apply.
6. **Blocked (W#7, X#8).** *Blocked* is the least predicate, an inductive
   `Reach`, such that an entity `D` (a computation or a task) is blocked when
   its current run is parked, and every member edge of its activation has
   one of these debtors:
   - a source;
   - a resource, offload or external wait;
   - a blocked computation or task.

   Because it is a least fixpoint, a cyclic wait among tasks is a user
   deadlock, not "blocked". No rank is needed.
7. **Eligibility (Q11).** A `needs-run` computation `C` is *eligible* when
   every dirty computation debtor of `C` is either settled or blocked.
   - When every dirty debtor is settled, this is topological order, and no
     run is wasted.
   - With a blocked debtor, `C` runs its coherent prefix. It then parks at
     its first await of a dirty debtor (rule 5).
   - A parked run is not re-admitted until one of its activation's edges
     fires, so an unchanged prefix never repeats.

---

## 5. Host ingress and transitions (layer 1)

### 5.0 Host ingress (D0)

- **H1 – enqueue.** Every host operation is an ingress item on the world's
  MPSC queue. This covers `write`, `deliver`, `post`, `spawn`, `observe`,
  handle drops, resource fires and acknowledgements, and cross-world
  deliveries. Enqueueing never waits for the world.
- **H2 – bounded combining (W#11, X#9).** After enqueueing, the host thread
  *tries* to take the gate.
  - **It wins:** it processes its own item, then at most a constant budget of
    further work, counting both ingress items and slices (Y#4). Each slice
    is finite by B9. If work remains, it schedules the
    world's drainer on the world's executor and releases the gate.
  - **Inline is optional,** per world and per JVM host thread (Z#79). A
    world created with `:inline? false` runs no user slice on host threads;
    it suits UI threads. A JVM thread inside `without-inline-turns` (macro
    `no-inline`) that holds no gate does the same for its own operations.
    Such an operation is enqueued, handed to the world's drainer and returns
    at once: it has queued-result semantics, the ones of a non-inline world.
    - **Condition:** this keeps turns off the caller only when the world's
      executor runs handoffs asynchronously and accepts them. An executor
      that runs them in the caller defeats it; one that refuses them gets the
      fallback runner (Handoff, below).
    - **A thread inside a gate** (a slice, an item or a callback) ignores the
      setting: H1's held-gate path, H3's callback delivery, H4's
      cross-world routing and B7 are unchanged. The setting is the thread's,
      not a dynamic binding, so it never reaches a slice (B10).
    - **What an opted-in caller observes:**
      - a bare `gated`/`host!` item returns no value and throws nothing to
        its caller; its throw is reported by the processing thread (Z#78);
      - commands (`write!`, `reset!`, `deliver!`, `post!`, `cancel-task!`,
        `release!`) return what they return on a non-inline world before
        the item commits; `reset!` returns its value before the write
        commits;
      - `value-async` and `observe!` return their withdrawal fn before the
        registration commits; a withdrawal queues after it (FIFO);
      - a creation (`task`, `spawn!`, a source) returns a handle that stays
        unbound until its item commits;
      - `release-world!` returns its rows-left fn before the release
        commits;
      - a `host-call!` client (`swap!`, `get-in-world`, `fork!`, `consume`,
        ...) waits for the reply as before, but an interrupt now ends the
        wait also for an uncontended item; that item still runs later and
        may succeed or fail, unreported to the caller;
      - admission is checked at the call: an operation admitted before T21
        commits is refused in its item if it is processed after it (no
        state change, a refused log entry), and only one after it is
        refused at the call with `::released`; internal items
        (acknowledgements, terminal subscriptions) are still accepted;
      - a moved host item function (a `swap!` fn, a `send-world!` fn) runs
        under the drainer's dynamic bindings, not the caller's; bodies are
        unaffected, since creation captures the caller's frame (B10).
    - Inline callers of the same world may still process an opted-in
      caller's items in their budget. No transition changes: an opted-in
      operation can only choose another legal commit order (the drainer's
      instead of the caller's).
  - **What H2 guarantees:** no deadlock, because no host thread waits on
    another. It does not promise latency: an inline caller spends at most
    the budget of finite slices.
  - **It loses:** it returns at once.
  - **Handoff:** after releasing the gate, a thread re-checks the queue. If
    the queue is non-empty and no drainer is scheduled, it schedules one.
    Queued work is therefore never stranded.
    - The scheduling claim belongs to that submission until its drainer
      starts, once. If the executor refuses the submission (it throws: a
      rejection, a shutdown, or a run followed by a throw), the drainer runs
      on a fresh platform thread (JVM) instead. The caller sees no error,
      already-accepted work makes progress, a failed handoff after a gate
      skips none of the others, and a submission never clears a later
      submission's claim (Z#79).
  - No host thread ever blocks on a world.
  - **Throws belong to their caller (Z#78).** An item that its own caller
    processes inline throws to that caller. A queued item processed by
    another thread (an inline caller's budget, or the drainer) is that
    item's caller's: its throw is reported and the turn continues; it never
    reaches the thread that drives the turn.
- **H3 – results.** A host operation that has a result (`swap!`, host
  `deref`) returns a host promise. A blocking host read waits on that promise
  outside the gate, never inside a slice. Host callbacks (`observe`,
  `value-async`, and the like) run between items, each isolated: a throw is
  reported, the other callbacks still run, and it never reaches the thread
  that drives the turn (Z#78).
- **H4 – cross-world delivery.** A continuation or callback belonging to
  another world is delivered as an ingress item of that world. This replaces
  `in-callers-world`, which ran caller-world code inline on another world's
  thread.
- **`swap!`** is an ingress item whose pure function runs in the world
  between slices.

### 5.1 Transitions

Every transition:
- refuses with no state change, or commits atomically;
- applies Rule R before it commits;
- is a step of the world's single execution (D0).

Transitions are built from a small set of primitive table edits (§11).

| # | Transition | Effect (before Rule R) |
|---|---|---|
| T1 | `create-source(kind, v)` | Owner is the current scope; inside a computation run, the computation (§5.2). |
| T2 | `write(X, v)` | `version += 1`; deltas are logged; mark, fire `dep` edges and deliver to `observe` edges per §4.5.1 (Z#9). |
| T3 | `create-comp(id, inputs, body)` | **Absent id:** a `fresh` computation is created. **Present, equal inputs** (the conservative capture comparison, formalism §1.6): it is adopted. **Present, different inputs (W#5):** body and inputs are replaced at the same id, and the change is handled exactly like a write to `C`'s rerun source. Marking (§4.5.1) dirties `C`'s transitive dependents. `C.epoch += 1`, and the replacement run starts from the body (restart). An idle entry is replaced by a `fresh` one. In every case the creator records `C` (§5.2) before Rule R. |
| T4 | `spawn(body, local)` | Creates task `K` owned per §5.2 and starts its run (fresh stamp, run scope with parent `K.owner`, Z#26). `K.local := local ∨ local(K.owner)` (Z#77). Refused (`::fork-local`) when `local` and the creator is a computation run. |
| T5 | `start(C)` | **Applies to:** a `fresh` computation, or an invalid idle one. The new run starts from the body, with a fresh stamp and `R.epoch := C.epoch`. |
| T6 | `await(R, ds, mode)` | **Activation:** an activation `A = {run R, mode, slots, remaining = |ds|, cont}` is created. Its id is always allocated, even when the fast path fills every slot in the same commit and `A` is removed at once (Z#28). **Member edges:** in a computation, each debtor's `dep` edge at this site (`at`) is reused or created, with `C` as creditor; in a task, and for consuming operations, a `wait` edge is created with `A` as creditor. **Demand:** debtors that are not running are demanded (T5, or T11 if `needs-run`). The awaiting slice ends here, and the demanded debtor's first slice is the next step; running that slice on the host stack implements this suspend–run–resume sequence (I10). **Fast path:** a member whose debtor is `live` or final fills its slot in the same commit, but only while `A` is unresolved. Once a fill resolves `A` (any fill of an `any`, the first `err` of an `all`, the last fill of a `one`/`all`), a later ready member fills nothing. In a computation, its `dep` edge stays with `C` as a loser's does, and it does not invalidate `C`. **Baseline:** a `dep` member on a signal or cell records the debtor's current value and version at the site when its edge is created. A re-await at the same site re-arms the edge and keeps that baseline (Z#22). **`one`/`all`:** the run resumes when `remaining = 0`; an `all` activation also resumes at its first `err` slot, with that error, and its unfilled members are treated as `any` losers (fail-fast, Z#61). **`any`:** the first filled slot resumes it; loser `wait` edges are removed, and loser tasks created by `R` for this await that have no other creditor are cancelled (T14). Loser computations keep `C`'s `dep` edges, because they are dependencies of `C`. Filling slot `i` removes the entry `(E, i)` from `A.members` (X#4, Z#7). On resume, `A` is removed; `wait` members are removed with it, and `dep` members stay with `C` (W#2). |
| T7 | `track(R, X)` | **Domain:** `X` is a signal or a cell; otherwise it is refused (Z#17). Inside a computation: a `dep` edge per §4.4, read immediately. Inside a task: a snapshot read with no edge, which allocates nothing (Q1, Z#19). |
| T8 | `observe(host, d, cb)` / `unobserve` | Adds or removes an `observe` edge with `seen = none`; validates `d` if it is idle. **Initial delivery (Z#15):** if `d` is a source, or a `live` computation, its current `(value, version)` is delivered in the same commit. Otherwise `d` is demanded (T5, or T11) and the first delivery happens when it settles changed. |
| T9 | `fire(E, result)` | Requires `E` to be `armed`; then `E` becomes `fired`. **`wait` edge:** fill its activation's slot, at the index recorded with the member (Z#7); a member listed at several indices fills all of them. **`dep` edge** of `C`: if `E` is a member of an activation of `C`'s current run, fill the slot (delivery) and re-arm `E` per §4.2. Otherwise this is an invalidation (§4.5.3), and `E` stays `fired` as a re-entry point. **`savepoint` edge (X#6):** fill its activation's slot, resume the run once if it is still parked on that activation (Z#50; otherwise the fire is refused), and remove the edge; the publication keeps only its basis. **`observe` edge:** per §4.2; it stays `armed` (Z#9). **Slots:** a filled activation resumes per T6, only if its run is parked on it (Z#50). If its run is stale, the slot is not filled (§4.5.4). |
| T10 | `finalize(d)` | Unfilled members of an activation on `d` are filled with `d`'s final result first; a closed source without a value (a mailbox, a semaphore, an undelivered deferred) gives `err ::closed` (Z#53). Then removes armed `dep` edges on `d`, and cascades: a creditor that becomes final is finalized in turn (Z#25). A member edge is removed when its slot fills (X#4). |
| T11 | `dispatch(C)` (X#2, X#3) | **Requires:** `C` is eligible and `needs-run`. Let `E` be its earliest fired `dep` edge in creation order, or the rerun-source edge for T3. **Predecessor:** the stale run (if any) is cancelled with `cancel(R, replace)` (T14). It unwinds its own finalizers, and its resources join through `cleanup` and T13. Nothing transfers: by the re-entrancy rule (§2), no finalizer or resource predates `E.at`. **Suffix:** `dep` edges created after `E` are removed, siblings at `E`'s own site included (Z#59), their baselines move to `C.adoption.baselines` (§4.4), and the predecessor's creations with `at > E.at` become `C.adoption.basis` (only the latest is kept). **New run:** fresh stamp, `R.epoch := C.epoch`. If `E.cont = restart`, it starts from the body; prefix creations remain in `basis` for adoption, and `E` is re-armed with its old baseline, which advances when the new run reads the site (Z#22). Otherwise it resumes `E.cont` with `E`'s delivery: a track interval (§4.4) or the debtor's result. **Edge:** `E` is consumed: re-armed with its new baseline, or removed if its debtor is final (§4.2). This covers completed and parked predecessors alike. |
| T12 | `complete(R, result)` | **Requires:** a valid token (§2); `result` is `ok v` or `err e` (Z#50), after all lexical finalizer boundaries have exited (T26, Z#66). `R.act := done`. **Computation, current run:** `result`, `version` and `done-epoch := R.epoch` are set; creations in `basis` that this run did not re-create are released; armed resources are cancelled. Settling follows §4.5.2. **Computation, stale run:** the ordinary result is discarded; actual cleanup failures still enter the owning world's ordered close report before retirement (Z#66). **Task:** children that were not awaited and not detached are cancelled (Q10); armed resources are cancelled; the result fires the task's `wait` creditors. **Then:** if `R` is not retirable, `cleanup[R]` is created (§3.2), then T13, then T10 if the result is final. |
| T13 | `retire?(R)` | `R` is retired iff `act = done ∧ ¬slice ∧ finalizers = [] ∧ finalizer = none ∧ cleanup-wait = none ∧ resources = ∅` (W#3, W#4, Z#66). **Retiring, in order (Z#18):** (1) if `R` is the entity's run (`C.run` or `K.run`), it is set to none (Z#25); (2) T16 closes `R.scope`: runs owned by the subtree that are not done are cancelled (normally none, because T12/T14 already cancelled them), open explicit scopes in the subtree are closed, and sources owned by the subtree are closed; (3) the run row and `cleanup[R]` are removed; (4) `R.scope` is removed if its subtree is empty, otherwise it stays closed until its last child row is removed (W#9). Children still unwinding keep the closed scope as their owner. Retirement happens inside the transition, before Rule R; Rule R's normalization retires further runs with the same steps. It is called by every path that can make the predicate true: slice exit, finalizer exit, cleanup completion, resource join and completion. Cleanup failures enter the world report before run deletion; neither physical resource acknowledgement alone nor a queued cleanup completion implies finalizer exit (Z#66). |
| T14 | `cancel(R)`, `cancel(R, replace)` | `act := done`, `mode := unwinding`. **Removed:** `R`'s activations, their `wait` members, and its `savepoint` edges. **Resources:** told to cancel (phase `cancelling`). **Children (C1):** the runs of the tasks in `R.scope`'s subtree, explicit child scopes included, are cancelled, and the worlds the subtree's scopes own are released (their completion obligations stay); Q10 at a task run's completion does the same. Sources still close and scopes are still removed at retirement (Z#18). **Cleanup:** `cleanup[R]` is created. **Finalizers (Z#66):** if a boundary is executing or waiting, preserve it and its waiter, including queued completion; record cancellation for outer unwinding and schedule no duplicate entry. Otherwise schedule the head finalizer as a cleanup slice (B3, B8). Cleanup resumption continues the current finalizer once, then unwinds outer regions; no ordinary body suffix or successful result may run. Repeated cancellation does not inject another error into a cleanup wait. **Replacement (Y#2):** `cancel(R, replace)` affects only the run itself: its activations, resources, children and finalizers. It has **no debtor-side effect**: the computation's creditors keep waiting for the replacement's coherent result. **Debtor side (R#14), for an ordinary cancel only:** `wait` creditors of the cancelled entity receive `err ::cancelled` immediately, independently of retirement; later cleanup cannot amend that result; for a computation, cancelling its **current** run is an invalidation of its dependents (§4.5.3). Cancelling a stale run invalidates nothing, because the epoch step already did. Then T13. |
| T15 | `resource-ack(Z)` | **Requires:** no edge has `Z` as debtor (Z#6). Its wait edge is consumed when `Z` fires, or removed with its activation on cancel. Removes `Z` from its run's resources and from `res`, then T13 within the same item (Z#55). The host "offload returned" item is a fire (refused while `cancelling`) followed by an acknowledgement. |
| T16 | `open-scope` / `close-scope(S)` | **Close** cancels all work owned by `S` and its subtree, and closes the explicit child scopes in that subtree (W#9). It closes every source they own; such sources are detached by Rule R step 3 if their owner is removed. A closed source is final and read-only, and survives only through its own reasons (R#15). Closing wakes the waiters of a source without a value with `err ::closed` (Z#53). A scope row is removed once its subtree has no rows other than closed scopes. |
| T17 | `arm(R, Z)` | Adds an outstanding resource owned by `R`, with `at = R.effect-index`. A resource effect (`offload`, `sleep`) is one body effect: T17 and T6 on `Z` in one commit, allocating `Z`, its activation and its `wait` edge in that order; `effect-index` advances once (Z#55). |
| T18 | `resource-fire(Z, v)` | **Requires:** `Z` is `armed` (Z#14). `armed` becomes `fired`, exactly once, and every armed `wait` edge with debtor `Z` fires (T9) (Z#6). `Z` remains outstanding until its acknowledgement (T15). |
| T19 | `handle-drop(H)` | `handles -= 1`; Rule R applies §3.4. A publication handle reaching 0 abandons it (S7). |
| T20 | `pin` / `unpin` | Increments or decrements the row's pin count (Z#16). An `unpin` at count 0 is refused. A row is a root while its count is > 0. |
| T21 | `release-world` | **Request:** sets `released := true`. **Roots revoked:** `observe` callbacks receive `::released`, pins are dropped, `pending-activation` is abandoned. **Host admissions revoked:** remaining handles become released handles, whose operations fail with `::released`, and their rows are removed. **Still admitted (Z#56, Z#66):** B8 cleanup effects, existing/new explicit cleanup waits inside finalizers, their sealed completions, and outstanding resource acknowledgements. Then T16 closes the root scope; it remains the administrative allowance (I11a). Request return does not certify terminal close. **Completion (C1):** the world is *complete* once it is released, none of its runs is unretired (`runs`: +1 at run creation, −1 at T13, every task and computation run, cleanup included) and every child world it owns is complete or was collected (`kids`: one exactly-once token per accepted child, +1 at ownership, −1 when the child completes or is collected; never inherited). Completion runs the host terminal subscriptions (`on-complete`, admitted after release and never revoked) after the gate and acknowledges the owner's token through the owner's ingress. A fork copies its parent's `runs` (it inherits every unretired run) and acknowledges at its first turn the inherited resources that were cancelling or fired but unacknowledged (they have no counterpart in it); an unborn instance released before activation is complete at once (E4). A released marker or emptied owner list is not completion. |
| T22 | `host-await(d)` / `host-unawait(E)` (Z#27) | **Await:** adds a `wait` edge with creditor host on `d` (demanding it, T5/T11), and validates `d` if it is idle. A root while it exists. **Fire:** when `d` settles or becomes final, the edge is consumed and the host promise receives the result. **Unawait:** a host that stops waiting removes the edge. |
| T27 | `rerun(C)` (host) | A write to `C`'s rerun source (§4.1). **`C` idle:** its validity becomes invalid, so the next demand starts it (T5). **Otherwise:** the epoch step of §4.5 step 3, `restart := true` (the next run starts from the body, not at a fired edge), `C`'s creditors are marked, and `C` is scheduled if demanded. |
| T28 | `retire-local` (internal, Z#77) | **Requires:** `W.retire ≠ ⊥` (§8.1 F6), and it is the world's first item. For each `R ∈ W.retire` (resolved in `W`): `R`'s activation (with its `wait` members), resources (with their dormant, discharge and outstanding entries), finalizers, boundary, cleanup entries and queue entries are removed without fire, acknowledgement, slice or callback. A task `K` of such a run without a result gets `err ::forked` (`:spindel/fork-local true`) and is finalized (T10; host waits without callback, Z#45). Then each `R` retires (T13): its run scope closes without cancellation (owned sources closed, Z#18; owned computations `owner := ⊥`, Z#23), the scopes go bottom-up, Z#18 is re-checked at each unmarked owner scope, and task completion (Z#70) and W1 are re-checked. `W.retire := ⊥`. |

**Planned cleanup transitions (Z#66, slice 1; not yet implemented/modelled):**

| # | Item | Effect |
|---|---|---|
| T23 | `finalizer-enter(R, F, outcome)` | Mark the registered head region active and retain the pending body outcome plus outer unwind continuations. Entry is once per region; normal entry has the same B8 restrictions as cancellation entry. |
| T24 | `await-finalization(R, O, k, ek)` | Requires an active lexical boundary, no existing waiter, a local-origin explicit operation and an admissible owned join (§7). Install the run-owned waiter under the gate before registering with the adapter after the gate. Synchronous completion enqueues T25, never invokes a continuation from registration. Registration throw becomes error completion; the first terminal claim wins, including completion followed by throw. |
| T25 | `cleanup-complete(origin, R, generation, sequence, outcome)` | A distinct tagged ingress item, separate from cancellation entry and resource acknowledgement. Validate the exact waiter; consume its readiness/control references once and resume only its sealed finalizer `k`/`ek` in a slice. Duplicate/stale items do nothing. Release a detachable subscription exactly once, including one returned after completion raced registration return. Detach withdraws observation, never physical close. |
| T26 | `finalizer-exit(R, F, outcome)` | Runs on both return and throw; clears the active boundary and removes the region exactly once, only after its body finishes. A finalizer-local catch may recover a cleanup error. Otherwise preserve a body failure as cause with ordered cleanup failures; success plus cleanup failure fails. Cancellation stays irrevocable outside the finalizer and continues outer cancellation unwinding. On ordinary completion, all cleanup precedes result publication. On cancellation, failures enter the eventual world close/join report without amending the published canceled result. Then T13. |

Failures use stable run/region/release order, not callback timing. Operation
subscriber exceptions cannot stop delivery to other subscribers or change the
settled outcome. No generic per-task close ticket is introduced. Physical
resource acknowledgement (T15), operation completion (T25), finalizer exit
(T26) and run retirement (T13) remain distinct evidence.

### 5.2 Ownership of created rows (R#9)

| Creator | Created computation | Created source | Spawned task |
|---|---|---|---|
| computation run | in `basis` with `at`; owner is the computation | in `basis` with `at`; owner is the computation | in `basis` with `at`; owner is the computation; cancelled if a later run does not re-spawn it |
| task run | owner is the run scope; retained while running or until consumed | owner is the run scope; retained by edges and handles only | structured child of the run scope (Q10); `detach` re-owns it to a named open scope outside its own run-scope subtree (Z#69) |
| top level | owner is the current scope | owner is the current scope | owner is the current scope |

A fork-local run's children are fork-local (Z#77). `detach` into a fork-local
scope requires a fork-local task.

**Errors.**
- A throw completes the run with `err e` after lexical cleanup; Z#66 preserves
  the body failure as cause when cleanup also fails.
- Errors flow along edges like values.
- Cancellation reaches `wait` creditors as `err ::cancelled` (T14).

---

## 6. Invariants and temporal laws

Invariants hold after every commit. Inside a commit, a constraint may be
violated for the rows the commit is still processing, for example a cancelled
run's task before its result is written, or the live runs of a closed scope
before the cascade cancels them. No uncommitted state is observable: a commit
runs under the world's gate, and every reader goes through the gate. The
formal model calls these parts "deferred within a step" (`formal/README.md`).

| # | Invariant |
|---|---|
| I1 | **Ownership:** every non-root scope has an existing parent. Every task, resource and non-detached source has an existing owner, or belongs to a cleanup entry. Every run belongs to an existing entity (possibly a tombstone in a cleanup entry). A detached source is closed. |
| I2 | **Referential integrity:** every edge's creditor and debtor exist. Every activation's run and its unfilled member edges exist, and its `dep` members belong to the run's computation. Every `basis` member exists or is idle. |
| I3 | **Liveness:** every row is in `live(W)`, in `storage(W)`, in a cleanup entry, or is admitted by §3.4. |
| I4 | **Work is reachable:** every run with `act ≠ done` is in `live(W)`. Every run with `act = done` that is not retired has a cleanup entry. |
| I5 | **Consumption:** no `wait` edge exists without its activation. No armed `dep` edge has a final debtor. An `observe` edge's `seen` never exceeds its debtor's version. |
| I6 | **Continuation placement:** engine continuations exist only in activations, in `dep` edges (as re-entry points), in a run's active finalizer boundary/optional sealed cleanup waiter (Z#66), and in its scheduled slice. Host data (publications, §8.2) may hold immutable continuation values; B6 makes them free of engine objects. |
| I7 | **Idle shape:** an idle computation has no edges, no run, an empty `basis` and no adoption. |
| I8 | **Closed scopes:** a closed scope owns no run with `act ≠ done` and no open source. |
| I9 | **Unwinding:** a run with `mode = unwinding` has no ordinary activations and no `savepoint` edges. Its ordinary resources are `cancelling` or `fired`. Its sole permitted suspension is an explicit sealed cleanup waiter (Z#66), which grants no ordinary activation or demand. |
| I10 | **Runs:** a computation has at most one current run, and every other run of it is stale and retiring. A task has exactly one run until it completes. At most one run in the world has `slice = true` (D0). |
| I11a | **Retention is reachable from obligations (A#4, X#12):** every row is either part of the fixed per-world administrative allowance (the root scope and the world record), or reachable by the edges of §3.2 from an outstanding obligation, a cleanup entry or a §3.4 admission, or a finalizer ref of a reachable run (Z#3). The **obligations** are: open explicit scopes; runs with `act ≠ done`; outstanding resources; open/active finalizer boundaries and pending cleanup waiters (including normal entry); pending world close and owned-child acknowledgements (Z#66 slice 2); `observe` edges; pins; host handles; `pending-activation`. |
| I11b | **Bounded fan-out (W#13):** no table is keyed by history. Each row's references are bounded by its current content: <br>• a computation's edges, `basis` and adoption are bounded by its last two runs' effect indices; <br>• an activation's members by its `ds`; <br>• a run's finalizers/boundaries by lexical nesting depth, with at most one current cleanup waiter per run; <br>• an operation's subscriptions and a closing world's child obligations by currently pending observers/owned children, never past registrations; ordered failures by the current close report, cleared from runs at retirement (Z#66); <br>• a source's delta log by `B`; <br>• a mailbox's queue by (posted − taken); <br>• a world's lineage (§8.1) by its fork depth: one `[ancestor, cut]` pair per fork on its path, shared with every descendant of that ancestor. This is the one bound not by current content (decision 2026-11-14). <br>Combined with I11a, retained rows are a function of the obligations' current content. The constant factor is measured by the census gate. Physical pages are bounded separately (F5). |
| I12 | **Rank (A#6):** for every `dep` edge between computations, `rank(creditor) > rank(debtor)`. **Adding an edge** that would violate this raises the creditor's rank and propagates the raise to its creditors. **A cycle:** if the propagation reaches the edge's debtor, the transition refuses with `::cycle`. The model proves the rank order. That the transition refuses with `::cycle` exactly when the propagation reaches the debtor is not proved: the raise loop is fuel-bounded. |
| I13 | **Coherence as guards (A#5, W#1):** T9 fills a slot from a computation only if that computation is `live`. T12 sets a result only for a current run. |
| I14 | **Validity is acyclic (Z#60):** the graph whose nodes are idle computations and whose edges go from each to the computation debtors in its `validity` has no cycle. Validation (§3.4) relies on it to terminate. Witness: validity entries strictly decrease in the lexicographic pair (demotion pass, rank at demotion). Demotions in one Rule R pass share their pass and are ordered by I12; a later pass is later; I12 raises happen only in allocating steps, so they never reorder entries recorded in one pass. Rank alone is not a witness: a still-live debtor can be raised after its creditor's demotion (proved in the model, together with "no dep edge has an idle debtor"). |
| I15 | **Coherence of results (Z#64):** (a) a `live` computation's `dep` edges all have `seen` equal to their debtor's current `version`, and its result is the one its current run produced from those reads; (b) an idle computation whose `validity` is not `invalid` has `done-epoch = epoch`, and each entry records the version its current result read of that debtor; (c) hence validation (§3.4) reactivates a result only when every debtor still has the version the result was computed at. A stale read is a violation of (a) or (b). |
| I16 | **Fork-local closure (Z#77):** a task owned by a fork-local scope is fork-local; no counted fork marker is owned by a fork-local scope; a world with `retire ≠ ⊥` has processed no item. |

| # | Temporal law |
|---|---|
| L1 | **Prompt reclamation:** if transition `t` removes the last reason of a row `r`, then after `t` the row is removed, demoted, admitted by §3.4, or in a cleanup entry. This is a corollary of I3 and Rule R (A#3). |
| L2 | **Join (W#14, X#11, Z#66), conditional progress.** Each finalizer starts finitely many cleanup joins; declared ownership/join dependencies are acyclic; each physical operation eventually completes and each resource/owned child eventually acknowledges; each slice is finite and runnable slices/ingress receive fair dispatch. Under these assumptions, each wait resumes, each finalizer exits once, and each run retires when its remaining resources acknowledge. World terminal close additionally waits for its owned-child acknowledgements (slice 2). B9 alone does not prove async finalizer termination: arbitrary loops or nonacknowledging adapters can stay pending forever. Such obligations remain observable, with no successful timeout-based join. The extended measure/progress proof is pending (§11). |
| L3 | **Serial execution (D0):** at most one slice of a world executes at any time, and host ingress never waits for the gate (H1, H2). |
| L4 | **No resurrection:** an operation with an invalid token (§2) changes nothing. |
| L5 | **Admission (A#8).** *Safety half (proved):* if no slice is runnable and some demanded computation is dirty, then at least one of these holds:
- its dirty cone contains an entity blocked on a non-computation debtor (§4.5.6);
- an eligible `needs-run` computation exists;
- the cone contains a parked task that is not blocked (in practice a cyclic wait among tasks, a user deadlock, X#8). *Liveness half (argued, not proved):* a scheduler that is fair to eligible computations starts each of them eventually. |

---

## 7. Body interface (the CPS contract)

Layer 1 treats continuations as opaque (A#1). Each slice is represented by
the effect it ends with, which is an ingress item of the model. Quantifying
over all items covers all bodies. The tree below defines what partial-cps
must refine:

```
Body ::= return v | throw e
       | effect op (λ result. Body)
       | finally Body Body
op   ::= await (ds, mode) | track X | create-comp | create-source | spawn | detach
       | write X v | deliver X v | post X v | take X | acquire X | release X
       | arm Z | offload f | open-scope | close-scope | savepoint addr | fork
       | await-finalization O
```

`partial-cps` is checked by property tests against a direct-style
interpreter of the same trees:
- **B1:** a slice ends in exactly one of: suspend at a registered effect,
  return, throw.
- **B2:** an engine continuation is resumed at most once per fire. T9's phase
  check rejects duplicates. Savepoint continuations are multi-shot; each
  resume belongs to its own run.
- **B3 (Z#66):** entered `finally` regions execute exactly once per run on
  return, throw or cancellation, innermost first. Entry retains the region
  until exit on success or exception; a cleanup wait may span slices. Cancel
  during normal-entry cleanup preserves its continuation and then unwinds
  outer regions, without restarting that finalizer or running a body suffix.
  T11 transfers no open region: re-entry requires a site with none (§2).
- **B4:** effects occur only at lexically visible registered sites
  (CLAUDE.md Rule 2).
- **B5:** closures held by user code are not engine state.
- **B6:** continuations close over no engine object (world, run, context,
  edge). The engine supplies them through the activation at slice start.
- **B7 (D0):** code inside a slice does not block the thread: no blocking IO,
  host `deref`, sleep or lock wait. Ordinary body work goes through `offload`;
  finalizer physical close uses the declared cleanup adapter (B8, Z#66). A
  violation stalls only its own world; it cannot break an invariant.
- **B8, C1 (in force):** finalizers are synchronous. A suspending effect inside
  a finally clause (an await on an unsettled debtor, a take/acquire that would
  wait, offload, sleep, external, `await-op`, fork, savepoint), on normal and
  cancellation entry alike, fails with `::invalid :finalizer`. The run tracks
  the finally clauses it executes, separately from its open regions. The
  broader Z#66 contract below remains planned.
- **B8 (A#7, Z#66, planned):** every lexical finalizer has the same restricted effect
  domain on normal return, error and cancellation. It may write, deliver, post,
  release, close, and suspend only with `await-finalization` on an explicit
  cleanup operation. Reject ordinary await/track/external/sleep, ordinary offload
  (including unawaited offload), spawn/computation/source creation, fork/savepoint
  and new engine-owned finally regions. Physical asynchronous close belongs in
  the declared cleanup adapter. Pure helper `try/finally` is legal and adds no
  engine obligation. A finalizer-local catch can recover a cleanup error, but
  cannot recover the outer canceled result. Runtime checks apply at every effect
  or creation entry, including hidden helpers; macro diagnostics alone do not
  enforce the boundary.
- **B9 (X#9, Z#66):** every slice terminates and adapter registration is finite
  and nonblocking. A non-terminating pure loop or blocking call violates the body
  contract. Async finalizer termination additionally needs L2's assumptions.
- **B10 (JVM):** dynamic bindings belong to the run, not to the thread of a
  slice. A run starts from its creator's binding frame (a computation's frame is
  the one of its latest creation; bindings are not inputs and cause no rerun).
  Each slice runs on the run's frame and saves it back at slice exit, so a
  `binding` spanning effects pushes and pops on the run's frame, the resuming
  thread's bindings do not reach the body and the body's do not leak out. A
  fork, `(fork)` or savepoint copies the run with the frame live at that point.
  `set!` of a binding made in another slice fails (Clojure's thread check).
  CLJS has no thread frames: the run keeps a map of the vars it binds. A
  `binding` inside a body adds to it (the body macro rewrites it); each slice
  sets those vars and restores the globals at exit, reading the values back
  (a `set!` inside the body's binding persists). A host-level `binding`
  reaches a creation only for vars declared with `convey`; others are not
  conveyed (as in core.async).

**Declared joins (Z#66).** Cleanup operations describe acyclic already-owned
lifetimes. Engine bodies may join downward owned targets; a host coordinator
outside the target tree may join its targets. Reject self, current-world,
ancestor and unrelated sibling/cross-world joins before parking. A close request
without joining may target the caller's owner. Consumer activity leases are
adapter obligations: release the lease before joining. The engine does not
infer hidden host/CPS dependencies or build a global cross-world cycle detector.
Independent cross-world joins outside this ownership profile fail explicitly.

---

## 8. Layer 2: forks and savepoints

### 8.1 Forks

**D3 – fork.** `fork(W, mode)` is an effect of the active slice. By D0 that
slice is the only one executing, so the fork boundary is the effect's commit.
The effect is refused in a computation body, in a nested slice (Z#47) and
in a run of a fork-local task (Z#77: the child would retire the forking run).

The child `W′` gets:
- copy-on-write views of `W`'s layer-1 tables: `W′` sees every row as it was
  at the fork (MVCC representation below);
- `lineage = {parent: id(W), mode}`;
- **Handle lineage:** a handle of another world reaches a row only if the world inherited it: the row was created by the world, or by an ancestor below the cut of the fork that leads to it (each row records its creator; each world its `[ancestor, cut]` chain). Otherwise the operation fails with `:spindel/invalid :lineage`.
- **no** world-lifecycle rows: `forks`, `pubs`, `pending-activation` and
  `ingress` start empty;
- in `W`: a fork marker `M = {child, owner: current scope}`, retained by its
  owner scope. A host fork (between slices) is owned by `W`'s root scope, or
  by the root scope of another world of the same family named as its owner
  (2026-11-14), as for instances (S3): copies of a world then outlive it. An
  owner already released releases the fork.

**Representation (MVCC, 2026-11-15, `v2-fork-memory-design`).** A row is an
identity and its owner world's current state: the owner (the world whose
epoch stamps it — its creator, or the fork that copied it) changes it in
place. A world's epoch carries an ordinal that advances at each fork it
makes; a fork at ordinal `o` receives a token for `o`, held strongly by its
lineage (and its descendants'), weakly by the owner. Before its first change
to a row after a fork, the owner saves the row's state as a version
`[k m image]` on the row (the state forks with ordinal `k..m` see) — only if
a token in that range is still reachable — and restamps it. A fork resolves
an inherited reference through its lineage `[owner cut ordinal token
copy-map]` (nearest first): an ancestor's copy as it was at the fork, or the
owner's row at the fork's ordinal (the live row, cloned, if unchanged since,
else its version), and copies what it writes into its own map. Owner and
reader synchronize per row (a monitor held for one row clone). A root world
keeps no forwarding state; a fork's own copy map is bounded by the rows it
inherited; versions live as long as a fork or anchor that can read them.

**Token end (MVCC).** A token ends when it is no longer reachable (holders:
the lineage of every world object, live or released and uncollected; a
publication's basis until `dispose`; instances through the shared basis
lineage), **or** at its fork's finish if it is unshared: the fork is released,
its metadata is closed, and it has no pending work (ingress, callbacks,
ready/resume/start/cleanup queues), no queued cleanup and no armed resource.
Deriving a world from a fork (a fork of it, an instance of its basis) marks the
fork's token shared; shared is sticky (conservative), so a shared token ends
only when unreachable. A finished world resolves no inherited row again:
released worlds refuse host items (T21), and finish requires no slice or armed
resource. When a token ends, its owner prunes the versions it listed (as a
completion item under the owner's gate); a version stays while any live token
covers its range.

**Mode (Q3, decided):**
- **frozen** is the default: untouched reads see the fork-time basis.
- **following** applies to **sources only**:
  - writes of the parent to a source `W′` has not written are pushed to
    `W′` as T2 ingress items, with their deltas;
  - the first local write to a source in `W′` shadows it and ends following
    for that source;
  - when the parent **closes** a followed source, the close is pushed too.
    When the parent **removes** it, following ends for that source, and `W′`
    keeps its last value as a local source (R#19);
  - the push link belongs to the marker and ends when the marker ends.

  Computations in `W′` are always local.

**F6 – fork-local runs (Z#77).** Let `W′` be a child of `W` (a host fork, a
`(fork)` effect, a savepoint basis or one of its instances, or any other
derived world) and `L` the runs of fork-local tasks unretired in `W′`'s
source at the fork (`W′.retire`: `W`'s own, with what `W` has not retired
itself). In `W′` every run in `L` is retired by T28; no body slice,
finalizer, cleanup slice or host callback runs for it, and no resource of it
is activated, fired, acknowledged or re-armed. Normatively this holds at the
fork boundary: no operation on `W′` observes a run in `L`. T28 is `W′`'s
first item, processed at its first gate entry (the inline fast path, a
drainer turn, a host operation, `activate`), before the first ingress item,
the first normalization and the first dormant activation, also in an unborn
instance (it runs nothing, so E4 holds). A child that is never entered is
collected or completed without it. Retiring at copy time instead would cost
`O(|L|)` under the parent's gate on every fork; no operation can observe the
difference, since every access to `W′`'s rows goes through its gate.

**Inherited work (R#18, R#21, W#8):**
- **Fork-local runs (Z#77)** are not inherited as work: T28 retires them
  before anything else happens in `W′` (F6). The remaining bullets apply to
  every other run.
- Parked runs, their activations and edges are copied as values (B6).
- `R`'s copy in `W′` is parked at the `fork` effect and resumes with a
  child-side result (Q4).
- Physical resources are inherited as **dormant descriptors**. They are
  activated when `W′` is first scheduled:
  - timers re-arm with their deadline;
  - external waits, offloads and native operations fire `err ::forked` into
    their edges and are joined at once. They never had a physical
    counterpart in `W′`, so no acknowledgement is invented.
- **Inherited `savepoint` edges**, other than `W′.pending-activation`, also
  fire `err ::forked`: the child has no publication for them (W#8).
- **Z#66 inherited cleanup waits (planned slice 1):** fork captures descriptors
  lazily, preserving O(1) creation. The child has fresh close state and inherits
  no parent physical controller, callback or host subscription authority.
  First local activation resumes each inherited pending **or already queued but
  not resumed** wait through its sealed error continuation with `::forked`
  exactly once. Remove/replace inherited cleanup-resume items; no copied parent
  success may resume the child. Parent completion still resumes only the parent.
  This is local failure of observation, not re-execution of physical close.
- An explicit operation is a world-origin capability. Using a captured parent
  operation later in a child fails `::forked` before adapter registration. Child
  owners must allocate child-local operations and resources; copying a raw
  captured external handle does not make its cleanup branch-local.
- This activation cost is the G3 term "inherited armed resources", extended by
  inherited pending cleanup wait descriptors (Z#66).

**Fork rules:**
- **F1:** `W′` holds no reference to `W`'s live context: only ids, its
  lineage (tokens, copy maps) and the push link; it reads `W`'s rows through
  clones and versions, never the live row.
- **F2 (R#20, W#10):** marker `M` is removed when `W′` is released. `W′` is
  released when:
  - `M`'s owner scope closes; or
  - `discard(W′)` is called explicitly; or
  - **idle release (Q12):** `W′` has no runs (a run parked on a consumed
    savepoint does not count, S8), no pins, no `observe` edges,
    no open explicit scopes, no `pending-activation` and no handles. Its
    administrative root scope does not count. Realized physically (Z#58):
    a marker of the `fork` effect holds `W′` strongly (its owner scope
    bounds it); a marker of a host fork or an activated instance (owned by
    the root scope) holds it weakly. Such a `W′` stays reachable while
    anything can still act in it (the host, a timer, an offload, a drainer);
    once nothing can, it is collected. Its parked runs can never resume, so
    their finalizers do not run.

  Dropping the last handle of a fork that still has live work does not
  release it. Its work is owned through `M`.
- **F3:** each world applies Rule R to its own tables. A row's saved versions
  are dropped when no reachable token covers them (pruned when the row is
  saved again, or by the sweep of rows holding versions); this is physical
  reclamation, not a semantic reason.
- **F4:** discarding an activated fork cancels its runs and joins their own
  cleanup (T21 in `W′`). Frozen/unborn instances discarded without activation run
  no finalizer, detach or physical-close callback. Release before first normal
  execution respects that activation/discard distinction and cannot detach the
  parent. Activated forks finish their local inherited finalizer chains and
  retire independently of the parent's pending physical operation (Z#66).
- **F5:** the layer-1 invariants hold in every world. Physical storage is
  bounded by Σ over live worlds of their own rows and copies, plus the
  versions that live forks and anchors (publications) can read.

### 8.2 Savepoints (R#7, R#17)

A savepoint publishes the rest of a body to a handler (see `savepoints.md`).

- **S1 – publish** (effect `savepoint addr`). The run `R` of entity `E`
  parks in an activation `A_sp` (mode `one`) whose single member is a
  `savepoint` edge `E_sp` (X#6). A publication `P = {edge: E_sp, basis}`
  is created, and the handler receives its handle.
  - `basis` is a frozen basis of `W` at this commit.
  - `P` is host data. It pins only its basis pages and retains `E_sp`.
- **S2 – in-place resume** (affine; the current API). The handler fires
  `E_sp` in `W` with a value. This is T9's savepoint branch, at most once. `P` then
  keeps only its basis.
- **S3 – instantiate.** `instantiate(P)` creates a frozen fork `W′` of
  `basis` *without activating it*:
  - its marker is created at activation (S4), owned by the root scope of
    its *owner*: the publication's world by default, or another world of the
    same family named at `instantiate(P, owner)`, e.g. a session's root, so
    that instances outlive the world that published them (S8); the handler
    runs as host code (Z#58);
  - until activation `W′` is **unborn** (Z#58): host items commit, but its
    inherited work and dormant resources wait for S4;
  - refused (`::fork-local`, Z#77) when `R` is a run of a fork-local task:
    every instance would retire it (F6); S2's in-place resume stays allowed;
  - `R`'s copy in `W′` is parked on its copied `savepoint` edge, which
    becomes `W′.pending-activation`;
  - every other inherited `savepoint` edge fires `err ::forked` (§8.1);
  - before activation, the handler may perform writes in `W′` (trace
    entries, weights, counters, handlers).
- **S4 – activate.** `activate(W′, v)` fires `W′.pending-activation` with `v`
  and clears it. Instantiating `P` `n` times gives `n` independent
  particles. In the source world, I10 holds by construction: the copied run
  is the run, so nothing is added (R#7).
- **S5 – incremental re-execution.** Re-running from a changed choice is
  either S3/S4 with the new value, or T11 at the choice's `dep` edge. Both
  adopt the creations made before the site.
- **S6 – resources.** As in §8.1, inherited external waits fire
  `err ::forked`. A handler may refuse to publish while any exist (the
  portable-savepoint restriction).
- **S7 – abandonment.**
  - **Publication:** when `P`'s handles reach 0, or `abandon(P)` is called,
    while `E_sp` is still armed, `R` is cancelled (T14). Its creditors
    receive `err ::abandoned`. The basis is freed once no fork made from it
    remains.
  - **Pending fork:** dropping an unactivated `W′` collects it without running
    anything: nothing in it ever ran, and running the finalizers it copied
    would repeat the source's side effects once per dropped particle
    (Z#58). Discarding it releases it (F4).
  - **Collection** of a publication while `E_sp` is armed abandons it. The
    publication is read-only host data, so it is never copied by accident.
  - The handler returning without resuming is **not** abandonment. `P`
    stays valid while it has handles.

- **S8 – consume (copy).** `consume(P, k, owner)` continues `R` only in `k`
  new instances, never in its own world `W` (2026-11-14):
  - **Requires:** `E_sp` armed, `R` holds no resource other than its
    savepoint (the S6 portable restriction), and `R` is not fork-local
    (Z#77). Otherwise refused, and `P` stays pending.
  - In one commit of `W`: `k` instances of `P` are created (S3, owned by
    `owner`), and `E_sp` becomes *consumed*: `R` stays parked on it, can no
    longer be resumed (S2) or abandoned (S7), and its finalizers never run
    in `W`. Its continuation lives on in the instances only.
  - A run parked on a consumed savepoint does not keep `W` alive: F2's idle
    release ignores it, so `W` is collected without running it once nothing
    else can act in `W`.
- **S9 – dispose.** `dispose(P)` ends a publication used as an anchor: if
  `E_sp` is still armed it is abandoned first (S7); then `P` drops its basis
  (F3's page refcount) and every reference to `W`. `instantiate` of a
  disposed publication is refused. A publication holds `W` only while
  `E_sp` is armed; once it is resumed, abandoned or consumed it keeps only
  its basis.

**Addresses of effect sites (2026-11-14).** A registered effect receives,
besides its `site`, the occurrence's `key` (the site and a per-run ordinal of
that site, as for creations) and its `frame`: the creation keys of the
entities that created the run's entity, outermost first, and of the entity
itself (a site and ordinal in the creating run); empty for an entity the host
created. The frame follows creation, not ownership, so `detach` keeps it. A consumer's
address for an effect occurrence is `[frame key]` or an explicit id. The
ordinal is counted when the effect is entered, before a savepoint freezes the
run, so instances continue the count of the run they copy. In task runs and
their instances keys are stable; in a computation run re-entered by T11 only
creation ordinals are restored (formalism §1.6), so effect-only keys after the
re-entry point count from there.

**Paths of effect sites (2026-11-14).** Readable, hierarchical names for
effect occurrences (Gen's `:step => i => :x`), for consumers that let callers
name sites from outside:
- **P1 – label.** `with-path p body` (`p` a vector) appends `p` to the run's
  *path* for the extent of `body`. A registered effect receives, besides
  `key` and `frame`, the occurrence's `path`: the run's path when the effect
  is entered. Paths nest.
- **P2 – restore.** `with-path` is a `finally` region (§7): when `body`
  exits, by return, throw or cancellation (B3), the path is restored to its
  value at entry. Like any new engine-owned region it is not admitted inside
  a finalizer (B8); restoring an entered path is.
- **P3 – inheritance.** Every run records its path when it is created: its
  entity's path, which is the creating run's path when the entity was
  created, empty for an entity the host created. The run's path changes
  only by P1/P2, never by later changes to its entity. Like the frame, the
  path follows creation, not ownership, so `detach` keeps it.
- **P4 – adoption.** A computation adopted (T3) under a path other than its
  own is adopted as one whose inputs changed, and takes the new path; a
  task spawned in a computation run under another path is replaced, as for
  changed captures. An empty path is the same as none.
- **P5 – suspension and copies.** The path belongs to the run, so it
  survives suspension; a fork or instance copies the run with its path.
  Re-entry (T11) never starts inside a path: the `finally` region makes the
  `dep` edges inside it non-re-entrant (§2), so a new run starts with its
  entity's path. Keep path regions narrow in computations: an invalidation
  inside one restarts the body.
- **P6 – metadata.** A path determines neither identity nor ownership: it
  labels effect occurrences and creations, and only P4 compares paths.
  Outside a body `with-path` runs `body` unlabeled.

**API change:** savepoints gain `instantiate`/`activate`/`abandon` alongside
the existing in-place resume, and `consume`/`dispose` (S8, S9).

---

## 9. Settlement interface

- `quiescent?(W)`: true when all of these hold:
  - no run has `act ≠ done`;
  - there are no cleanup entries;
  - there are no outstanding resources;
  - the ingress queue is empty.
- `seal(W)`: refuses new host admissions (T4/T5 from the host, T8).
  Propagation continues.
- `release(W)`: T21's request/report interface. Existing request-level
  `release-world!`/`discard!` diagnostic-function returns are not changed by Z#66.
- **Planned Z#66 slice 2:** narrowly named `close-world!` requests closure and
  returns an opaque world cleanup operation, consumable by `await-finalization`;
  host observers may subscribe/withdraw. No generic close-ticket protocol and
  no normal-body wait are added by this phase. Repeated close/observation sees
  one terminal outcome; withdrawal affects only that subscriber.
  **Origin versus target:** `close-world!(child)` invoked in a parent slice
  returns a parent-origin observation capability targeting that child. The
  parent's finalizer can await it if the downward owned-join check passes.
  Origin does not become the child's identity merely because it is the target.
  All observation capabilities for that target share its single physical close
  and stable terminal outcome; a new observer does not restart physical close.
  A copied parent-origin capability still fails `::forked` when awaited in a
  child, even if that child is its target. A host caller must explicitly select
  the observation-origin world, by an explicit origin argument or selected-world
  binding; the target is never an implicit origin. Host subscription/withdrawal
  requires no engine slice and grants no authority to await in another world.
  Origin selection also does not bypass the target ownership/join restrictions.
  Terminal close needs all local root-subtree obligations/resources and owned
  child acknowledgements. Record a pending child before dropping its live
  ownership marker; admission before close with publication afterward still
  requires disposal and acknowledgement. Child acknowledgement queues ingress
  after releasing its gate; never acquire a foreign gate while holding one.
  Production counters/sets track pending work independently of verify-only row
  census. Root-owned fork references remain weak in ordinary lifetime; a pending
  close may hold its target until acknowledgement, then clears all controllers,
  release closures, world references and subscribers, retaining only the outcome.
- `diff(W′)`: source rows written in `W′` relative to its basis.
- merge entry point: refuses unless `W′` is quiescent and sealed. Merge
  semantics, stamping, durability and recovery are the settlement layer's
  responsibility. The engine's `merge!` (L12, signals only) keeps, for each
  inherited source the fork touched, `[identity version-number]` at the fork:
  the change and conflict checks compare version numbers, and the write goes
  through the identity resolved in the parent (MVCC).

---

## 10. Implementation design (non-normative)

**Evidence.**
- From 2026-10-28 to 11-02:
  - `simple` ran at 50–145× missionary;
  - the compact owned path at 8–12×;
  - the public owned path at 17–56×, dominated by scope and binding
    transport.
- The hot-path spike of 2026-11-03 (branch `spike/v2-hotpath`, about 470
  lines; results in `.internal/bench/`):
  - median paired ratio against `m/cp`, ≥ 5 interleaved trials;
  - the spike is serial (D0), uses mutable rows and the epoch / pending
    scheduling of §4.5, and has no forks, cancellation trees, ranks or weak
    handles.

| case | JVM | Node |
|---|---|---|
| fanout 100 | 0.25× | 0.21× |
| chain 50 | 0.33× | 0.44× |
| diamond | 0.20× | 0.06× |
| fanin 50 | 0.13× | 0.03× |
| switch | 0.34× | 0.36× |
| switch-reactive | 0.26× | 0.08× |
| child per run | 0.39× | 0.27× |
| task lifecycle vs `m/sp` | 2.6× | 0.19× |
| task await vs `m/dfv` | 1.3× | 0.34× |

Allocation per update on the JVM was 0.25–0.97× missionary for the reactive
cases.

**Design.**
1. **Rows are mutable objects** in per-world int-indexed tables with named
   fields. Retention bookkeeping uses counters and intrusive lists.
2. **The gate:** one per world. On the JVM it is a lock that host threads
   only *try* (H2), with a scheduled drainer on the world's executor. On JS
   it is the event loop. Edits are in place, with a journal only where a
   refusal can follow the first write.
3. **No event queue for local completions.** §4.5's mark and settle phases
   are counters on rows and edges. A computation whose `pending` reaches 0
   either runs (`needs-run`) or is cleaned. Only host ingress uses the MPSC
   queue.
4. **The ready-await fast path** (T6) returns the cached value
   synchronously.
5. **Dependency edges are reused across runs:** a run walks its previous edge
   list by `at`, and allocates only where the dependencies diverge.
6. **Activation is lexical:** the body closure binds its run row, so effects
   need no ThreadLocal or `binding` (B6). A world field holds the active run
   for non-lexical calls.
7. **Ranks (I12)** are maintained by height adjustment on edge insertion, as
   in self-adjusting computation. The spike must measure the cost of this on
   `switch`.
8. **Lazy invalidation (Q2)** via hot counts: observers plus hot creditors.
9. **Ids:**
   - 64-bit non-cryptographic `(creator, site, ordinal)`, where `site` is a
     macro-time int;
   - keywords and UUIDs only for serialization;
   - no `random-uuid` on hot paths.
10. **Rule R incrementally:**
    - reference counts on the edge classes of §3.2;
    - ranks make `dep` edges alone acyclic, but `basis` plus a `dep` back-edge
      (a creation that awaits its creator) can close a retention cycle;
    - a local trial-deletion tracer runs only on such `basis` cycles.

    The proof obligation is that the removed set equals the complement of
    `live ∪ cleanup ∪ §3.4`.
11. **Copy-on-write pages** with owner epochs. Inherited resources are
    activated lazily.
12. **Weak handles:** one Cleaner or FinalizationRegistry registration per
    host-visible handle. The callback only enqueues T19 (H1).
13. **Logging and direct compilation:** trace and debug logging is elided at
    compile time; bodies that cannot park are compiled direct.
14. **Task captures:** a task runs its body once, so its row drops the body
    once the first slice starts, and keeps its captured inputs only where a
    computation may adopt it (§5.2) or in verify mode, where the projection
    reads them. A long-running task therefore does not retain what it
    captured, e.g. the head of a sequence it walks (C0).
15. **Control signals without traces:** `::cancelled`, `::closed`,
    `::released`, `::forked` and the unborn error are signals, made once per
    affected row; on the JVM they carry no stack trace (a trace per retained
    row cost foerster's benchmark ~1 GB of a 1 GB heap).

---

## 11. Verification plan (non-normative)

Shaped by the ansatz feasibility read (`ansatz/.internal/design/spindel-v2-feasibility.md`).

1. **The ansatz model.**
   - Rows are structures in association-list maps.
   - One generic `Reach succ roots` inductive is reused for `live(W)`, for
     blockedness and for L5.
   - A fuel-bounded worklist returns a `converged` flag. Proved:
     `converged ⇒` the result is sound and closed, hence equals `live`. The
     oracle asserts `converged`. Fuel sufficiency is proved for normalization
     (P1/P2), cascades (P4), reactivation (P6/P8), the obligation reach, the
     scope subtree and ancestors, and the cycle reach. It is open for the I12
     raise loop, Derive/blocked, the dirty cone and `cur-scope`. There, fuel
     is a parameter and convergence is checked by flags.
   - `step : World × item → Outcome` is sequential (D0). Items are slice
     effects with opaque continuation ids, completions, scheduling choices and
     ingress items. The step is `world-step w it = then-rule-r (raw w it)`: `raw`
     (host guard, `transition`, `any` losers cancelled), then Rule R.
   - Preservation is proved once, for the base invariant `well-formed`, as a
     tree of lemmas that follows the step: primitive table edits, the
     composites built from them, the transitions, Rule R. The tree is restated
     over an arbitrary part `Q` of the invariant (`pres.tree`). A part
     supplies only what is its own: one lemma per primitive edit it must be
     checked against, the facts it needs at particular points of a step, and
     hand proofs for the few composites where it breaks and is restored
     inside the composite. The core of the invariant is a chain of 13 nested
     links (`chain-start` … `chain`), each adding one campaign's parts.
   - No Mathlib: Init's `List` lemmas suffice.

   Size: about 77k lines in 70 namespaces grouped by topic
   (`formal/README.md` has the map, the name legend and the old names); about
   6,000 theorems are written by hand and about 10,200 are generated from the
   tree for the parts (kernel-checked like the rest).

2. **Safety.** The model's top invariant is
   `inv w := chain w ∧ i5-seen w ∧ inv-i9 w ∧ inv-i10-slice w ∧ i3 w`
   (`spindel.v2.top`). Proved: `inv-empty`; `inv-step` (every item, accepted
   or refused, keeps `inv`); and `reach-inv` (every world reachable from the
   empty world by steps satisfies `inv`).
   - Covered by `inv`: I1, I3, I4, I5, I8, I9 (synchronous finalizers), I10,
     I11a, I12 (the rank order; see I12), I14; L4 (`step-l4`); and the safety
     half of L5 (`l5-safety-total`).
   - Partial: I2 (member edges of current runs; "every basis member exists or
     is idle" is not proved), I7 (the empty-basis clause is checked by the
     oracle, not proved), I13 (guard lemmas only).
   - Out of scope: I6 (continuations are opaque ids) and I11b (the census
     gate). Z#66 waiters and I15 are not modelled (§11.3).
   - L1 is proved in state form (`live-converged`/`normalized` premises),
     with the premises discharged by P1/P2 separately.
   - I8 rests on a model-only guard, `cur-closed`: a spawn or creation is
     refused when the run's current scope is closed. The obligation that the
     guard never fires (P10) is open.
   - Rule R's lemma obligation (§3.3) is proved once.
   - I16 (Z#77): the run half of LOC1 (`loc1-runs`) and LOC3
     (`sys-reach-rinv`: nothing runs in a cell before its retirement) are
     proved; LOC1's task half and LOC2 are not proved as step invariants
     (the oracle checks them on samples 51–60); `retire-clean` and
     `retire-quiet` are checked on replayed worlds, not proved.

   **Layer 2** (`spindel.v2.layer2.top`): `SysReach` (the systems reachable from
   an initial one by the operations of `spindel.v2.layer2.sys`, each with the
   premises its theorems take, e.g. a fresh id for fork, fork effect and
   instance) and `sys-reach-inv`. Every reachable system satisfies `sysinv`:
   - every live world and every live publication's basis satisfies `inv`;
   - completion soundness: a live complete cell is released, has no run,
     every kid is done and no marker remains;
   - every live world is quiet-compatible;
   - host joins are well formed.

   **Physical:** `mv-refinement` (`spindel.v2.layer2.mvcc`). In every MVCC family
   state reachable from the initial one, every active world reads each id as
   the value-copy model of layer 2 has it.

3. **Join.** The pre-Z#66 L2 argument uses the measure lemma on `μ(R)`
   and well-foundedness of ℕ × ℕ. That argument does not cover suspended
   finalizers. Z#66 needs explicit cleanup-enter/wait/complete/exit steps and
   preservation of I6/I9/I11, plus a progress lemma under L2's finite, acyclic,
   acknowledging and fair-dispatch assumptions.

   **Z#66 acceptance remains pending.** Required formal obligations are: exact
   once-only boundary/waiter consumption through cancel/queued completion;
   cleanup retention independent of reactive demand and ordinary run validity;
   fork-origin isolation including queued completion; and conditional retirement.
   Origin/target witnesses must admit a parent-origin capability joining its
   owned child while rejecting that same capability when copied into a child.
   Slice 2 additionally needs conservation of owned-child acknowledgement debt
   through close/late publication and terminal-close soundness. The external
   model must encode these transitions and pin its revision in acceptance
   evidence. Old oracle replay cannot prove steps it cannot express. A local
   finite contract test is supplementary evidence only; it neither discharges
   these lemmas nor the existing Z#64/I15 obligation.

4. **Oracle.**
   - The model and its proofs load together; namespaces are grouped by topic
     (2026-11-18); a definitions-only namespace for a fast oracle gate is
     still open.
   - The engine writes a test-only commit log. Each item carries the stamps
     and ids the engine allocated, and the model checks their freshness.
   - Scheduling choices are items, so the model refuses inadmissible ones.
     A refusal counts as divergence.
   - After each commit:
     - the projected engine state is compared with the model as id-keyed
       sets;
     - executable invariant checks (`inv-all`, `lit-all`) run as tripwires.
       The proved `inv` itself is not yet evaluated on replayed states: fork
       markers and validity crank/stamp are not projected;
     - refusals are compared through `Outcome.accepted`. Samples 43–50 drive
       the refusals of T21, the cycle, pins and handles, resources and the
       semaphore maximum.
   - Divergences are reported per commit; there is no automatic shrinking
     (test.check is not used by the oracle).

5. **The body contract:** B1–B8 property tests in partial-cps and spindel.

6. **Census, soak and perf:** the gates of §0.

---

## 12. Decisions

**Resolved 2026-11-03 (user):**
- Q1, Q2 (lazy invalidation of unobserved computations), Q3 and Q10 are
  accepted.
- Q11 (dependents wait for every dirty debtor) and Q12 (implicit release of
  idle forks) are accepted as proposed.
- Savepoint `instantiate`/`activate` is approved.
- `spawn!` inside a computation is owned by the computation.
- The computation/task split is accepted.
- `await` in a task does not re-run on upstream change.

**Resolved 2026-11-04 (user):**
- **D0, serial worlds**, together with non-blocking host ingress (H1–H4) and
  `offload`.
  - Evidence: the spike (§10).
  - A read-only audit of dvergr and foerster found no structural reliance on
    parallel slices inside one world. The work it found:
    - dvergr: about 5 durable `post!` sites in `discourse/llm.clj` should use
      `offload`;
    - foerster: `compiled.clj:146` must use `offload`; two `theta-smc` loops
      may;
    - foerster's multi-chain HMC/NUTS driver must run each chain's driver in
      its own world (H4).
- **Strict source ownership (Z#18):** a source created by a task run is
  owned by its run scope, and is closed when that run retires, even if it
  was handed out. A long-lived source is created in an outer scope or at top
  level, or detached.

**Specification choices made in v1.3 (signed off 2026-11-04):**
- Q11 is refined by the transitive *blocked* case (§4.5.6–7).
- Re-entry (T11) is possible only at `dep` sites where the run holds no
  `finally` region and no resource (§2). Other sites restart the body. The
  stale run is cancelled normally, so nothing transfers between runs.
  Z#66 permits only explicit cleanup-operation waits in finalizers; ordinary
  parking and spawning remain forbidden (B8).
- Computations carry explicit ranks (I12).
- The row-bound constant is measured by the census gate, not proved (I11b).

**Open:**

| # | Question | Proposal |
|---|---|---|
| Q4 | Does the forking run exist in the child? | Yes: parked at the `fork` effect, resuming with a child-side result. |
| Q6 | Are mailboxes bounded? | Unbounded by default (messages are live data); optional capacity for back-pressure. |
| Q7 | What is the idle-cache eviction policy? | Must drop at `handles = 0`; may drop under a configurable cap (default unbounded). |
| Q8 | Which sources are final when unreferenced? | Unkeyed sources with `handles = 0`. Keyed sources are final only when closed. |
| Q9 | Effect-index truncation in forks and savepoints | Carry over formalism §3.4, and re-verify against foerster replay. |

---

## 13. Mapping to the current API

| Current | v2 |
|---|---|
| `spin` | computation |
| `spawn!`, work `task` / `submit-work!` | task (structured; `detach` for fire-and-forget) |
| `task` with options | `task-with {:fork-local true}`: retired in every fork (Z#77) |
| `run-spin!` (one-shot) | a host `wait`-style delivery |
| `render-spin!`, subscriptions | `observe` |
| `parallel` | reactive computation over `await(all)` |
| `race`, `timeout` | eager one-shot task over `await(any)` (Z#65); first completion wins, shared tasks are not cancelled as losers |
| explicit reactive selection | `spin (await-any ...)`; computation dependency semantics |
| `signal`, `atom`, `deferred`, `mailbox`, `semaphore` | sources (§4.3) |
| `mult`, `pub`, `debounce`, `throttle` | library tasks over mailboxes and timers |
| `rerun!`, `trace/update`, `what-if`, `mark-dirty!` | writes to rerun sources (§4.1) |
| `spindel.blocking` | `offload` |
| `in-callers-world` | cross-world ingress (H4) |
| `fork-context` | §8.1 (frozen default; sources may follow) |
| `engine.addressing/with-scope` (readable site names) | `with-path` (§8.2 P1–P6) |
| savepoint in-place resume | S2 |
| new: `instantiate`/`activate`/`abandon` | S3, S4, S7 |
| `stop-context!`, `release-context!` | `seal` / `release` |
| `snapshot-context` / `serialize-context` | frozen fork plus basis serialization (layer 2b) |

**Behavior changes (approved 2026-11-03 through 2026-11-05):**
- lazy invalidation of unobserved computations;
- `track` in a task is a snapshot read;
- frozen is the default fork mode;
- structured tasks;
- public `race` and `timeout` are one-shot tasks (Z#65);
- `await` in a task is one-shot;
- dependents wait for asynchronous recomputation, unless the dirty debtor is
  blocked (Q11, §4.5.6–7);
- implicit release of idle forks (Q12);
- savepoint `instantiate`/`activate`, and abandonment of dropped
  publications;
- `spawn!` inside a computation is owned by the computation;
- **serial worlds (D0)**:
  - one slice at a time per world on the JVM, as on JS;
  - host operations enqueue and never wait;
  - blocking work inside bodies moves to `offload`.
