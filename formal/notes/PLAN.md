# spindel engine v2, layer 1: ansatz model

Spec: `../spindel-v2/docs/engine-v2-spec.md` (v1.5 at the start; read-only, never edit spindel trees).
Feasibility notes: `../ansatz/.internal/design/spindel-v2-feasibility.md`.

## Conventions (all namespaces)
- Init only (`(a/load-init!)`), no Mathlib.
- **One global id space**: every row (scope, comp, task, run, source, edge, act, resource, pub,
  fork marker) has a Nat id from one allocator; 0 = none. A retention node is just that id, so the
  generic reachability library works over `Nat`.
- Values, results, continuations, bodies, inputs: opaque Nat (A#1).
- Tables are `List` of `a/structure` rows keyed by `:id`. Kinds/phases/modes are Nat codes
  with named `a/defn` constants (ledger style; cheap to compile, decidable by `Nat.beq`).
- Executable predicates return `Bool` (they run in the oracle); proofs state `(= (p ...) true)`.
  Prop inductives only where leastness matters (Reach, Derive).
- Every transition is built from a small set of primitive table edits; invariants are proved
  once per primitive edit, transitions only discharge preconditions.

## Layout
| ns | content | stage |
|---|---|---|
| `spindel.v2.reach` | generic `Reach succ roots`, worklist closure (fuel, converged flag), soundness/closure/completeness; generic `Derive` least fixpoint (blockedness) | skeleton |
| `spindel.v2.state` | rows of §2, lookups, primitive edits | skeleton |
| `spindel.v2.edits` | exact-`pending` edit lemmas, I2 edit lemmas | skeleton |
| `spindel.v2.retain` | §3.1 roots and §3.2 successors over a World, `live` via reach, cleanup rows, §3.4 admissions, Rule R filter (stability, I3, idempotence) | done (filter) |
| `spindel.v2.step` | Item (payload table), raw T1, T2, T7–T9, T15, T17–T20 | done |
| `spindel.v2.rule` | T13 (Z#18/Z#25), T14, T15 (Z#6), T16, T10 cascade, Rule R rounds (normalize + filter until no orphan) | done |
| `spindel.v2.engine` | T3–T6, T8 (validation), T11, T12, settle, T22, scheduling choice, handle-new; `world-step` and the step theorems | done (layer 1 minus finalizer/savepoint/source-op items) |
| `spindel.v2.rank-step` | P5: `inv-rank` (inv-sample + I12 ranks) preserved by every step (`step-rank`); ranks frames per primitive edit, composite inv-sample lemmas re-checked for the bundle (`rank-copy!`) | done |
| `spindel.v2.casc` | P4: cascade completion under acts-alive (`casc-done-ok`, potential `casc-pot`); P2: normalization ends normalized (`normalized-ok`, `rule-r-normalized-ok`, `step-normalized-ok`); bundle copy `bc-copy!` | done |
| `spindel.v2.acts` | activation invariant `ga` preserved by every step (`step-acts`), so P2/P4 without acts-alive (`step-normalized-ga`, `step-i4-ga`, `casc-done-ga`); generic bundle copier `copy!` (bundles `ga`, `gx`) | done |
| `spindel.v2.inv` | predicates for I1/I5/I7/I9/I10/I11a (tripwire `inv-all`), counterexamples to literal I1/I5/I7/I8/I9/I10, I13 guards, L1, I10 D0 (`step-i10-slice`), I9 (`step-i9`), I5 wait half (`step-i5-wait`) | in progress |
| `spindel.v2.lit` | literal invariants through `world-step`: I10 task part (`step-lit-i10-task`, bundle `gl`), I9 resources (`step-lit-i9-res`, bundle `g9`); P3 core `filter-safe-of-refs`; copier `lcopy!` with source patches (`patch!`) | in progress |
| `spindel.v2.idle` | I7 (idle shape) through the step: bundle `g7` (a7, dep/marked creditor awake, idle clean, slice-normal alive, observe host), companion `awo` (T6/T11/reactivation chains), cascade completeness for demote (`kdb`, `casc-kill`); `step-g7`, `step-lit-i7` | done (honest hyps ga, rule-r-safe) |
| `spindel.v2.p3` | P3 complete: bundles `mdb` (marked edges are dep), `esb` (edge-sep: references are non-edge ids), `aha` (activation runs exist and are alive), round invariant `ri` -> every round filter-safe (`rule-r-safe-ri`); combined bundle `p3b` (ga, inv-rank, gl, g9, g7, mdb, esb, aha) with `step-p3b` and the step theorems with no honest hypothesis (`step-rule-r-safe`, `step-inv-total`, `step-acts-total`, `step-rank-total`, ...) | done |
| `spindel.v2.i10` | literal I10, computation part (one current run per computation) through the step: bundle `g10 gxz gkz` (E1 run epoch <= C.epoch, E2 a current run is C.run of an awake C and alive or C.done-epoch = C.epoch, run pointers name runs of their entity; computations gxz / runs gkz exempt), job condition for cascades (`job-ok`, transport bundle `nq`), bundle `g10r` = g10 [] [] for the raw transition (T5); `step-g10`, `step-lit-i10-current`, `p3c` = p3b && g10r with `step-p3c`, `p3c-empty`, `step-lit-i10-current-total` (no honest hypothesis) | done |
| `spindel.v2.i11` | I11a through the step: bundle `gw` (id 2 is the root scope's, run scopes are not 2, no fork markers), `reach-roots-obl` (reach from the roots = the root scope or reach from the obligations), `i11a-of` (from I3); `p3d` = p3c && gw && inv-i11a with `step-p3d`, `p3d-empty`, `step-i11a-total` (no honest hypothesis) | done |
| `spindel.v2.l5` | L5 reduced to step invariants: h-cur from g10r (`l5-h-cur`), h-mem's step form `h-mem2` (`h-mem-of2` at quiescent points), `l5-safety-inv` (p3c, h-mark, h-mem2); settle worklist fuel sufficiency (`settle-done-ok`); I5 dep-final as the model has it (`i5-dep-final-mem`, tripwire) | in progress (h-mark, h-mem2 through the step open) |
| `spindel.v2.progress` | L2 as measure lemmas: bundle `mb` (slice-ok + a tracked run's bound, 146 lemmas copied by `lcopy!`), `step-sok`, `step-mu-le` (no step raises a done run's (mu-f, mu-z)), `finally-exit-dec`, `slice-exit-dec`, `ack-dec`, `slice-exit-retires`, `ack-retires`; L5 safety half `l5-safety` (rank induction) under three tripwire-checked state facts (h-cur, h-mark, h-mem); fair-execution and L5 liveness stay paper arguments (ns docstring) | done |
| `spindel.v2.i1` | literal I1, scope clause, through the step: Rule R's filter keeps every kept scope's parent (`filter-lit-i1-scope`: live is parent-closed, cleanup rows and storage are closed upward under the current parent fields, Z#52); bundle `g1` = inv-sample && lit-i1-scope copied over raw/normalize; `p3e` = p3d && g1 with `step-p3e`, `p3e-empty`, `step-lit-i1-scope-total` | done (scope clause; the other clauses in i1o/i1r) |
| `spindel.v2.i5` | literal I5 dep-final clause through the step: bundle `g5 xd` (armed dep edges have a non-final or exempt debtor), discharging fires (`jw`, `jw-fire-edge`, `jw-fold`) at close/detach (Z#53), T14, T12, deliver, T6's fast path; `p3f` = p3e && g5 [] with `step-p3f`, `p3f-empty`, `step-lit-i5-dep-final-total` | done (branch rest) |
| `spindel.v2.i1o` | Rule R's loop ends with no orphan (`rule-r-no-orphans`: the owner count never grows, NZ bundle over normalize, and `detach-lt`); literal I1 owners of tasks/computations/sources (bundle `gso`: owner 0 => closed); `p3g` = p3f && gso && i1-own, `step-lit-i1-owners-total` | done (branch rest) |
| `spindel.v2.i1r` | literal I1 resource owners and run entities/scopes (bundles grx/gr0, krb/neb for T12's retirement through the cascade, acts-alive threaded through normalization, `gr0-filter`); `p3h` = p3g && gr0, `step-lit-i1-total` (every clause of inv-i1) | done (branch rest) |
| `spindel.v2.i8` | literal I8 (closed scopes) through the step: bundle `g8 xs` over key lists (alive runs of tasks owned by a closed scope are in the escape list xs; open sources have a non-closed owner), `close-local` (escape grows by `owned-runs`), cascade with the pending cancel jobs as escape list (`g8-cascade`, P4 empties it), ga threaded to the raw cascade sites, acts-alive through Rule R; `p3i` = p3h && g8 [], `step-lit-i8-total` | done (with the raw0 guard `cur-closed`: obligation P10 open) |
| `spindel.v2.z59` | Z#59 as theorems: T11 leaves no fired dep edge of the re-entered computation (`z59-t11-no-fired`), a fired edge on a written source starts no marking (`z59-fired-starts-none`); tripwires for the step form and the aux facts dle/cde (z59_test) | done (h-mark/h-mem2 through the step open) |
| `spindel.v2.hmk` | h-mark (P11) through the step: bundle `hmk hxm` (marked edges are dep edges on a computation that is strongly waiting, `hk-wt`, or exempt), every primitive (non-frames with premises: mark/unmark/remove/drop), overrides for fires, T10 finalize, T7, reactivation, release, T11 (watch `hsw`), T3 (mark fold with the marked set exempt, discharged at the end), detach; `hk-h-mark` (hmk [] -> h-mark) | done (continued in hmk2) |
| `spindel.v2.hmk2` | h-mark (P11) through the step, continued: edge keys backward `hk-ek` (ek-* copied from l5's es-nm), edge survival through fires (`hk-sv-*`), comps frames through fires/settles (`hk-cs-*`); T2 (`hmk-write-raw-x`, `t2-hmk`: roots strong after their armed edge's fire, cone in-edges survive and are marked), T12 + settle (`hmk-complete-raw-x`, `t12-hmk`: the completed computation, then the settle queue, is the exemption list), Rule R's demote (`hmk-norm-round`, `hmk-rule-r`: the round's strays are exempt, i14's `vr`), raw0 with gd/g7/ga/g10r premises, `step-hmk`, `p3l` = p3k && hmk [], `step-p3l`, `p3l-empty`, `step-h-mark-total` | done (h-mark; h-mem2 open) |
| `spindel.v2.i14` | I14 (Z#60: the validity graph over idle computations is acyclic) through the step: validity entries carry model-only `stamp`/`crank` (allocator and creditor rank at demotion); `iv14` + `dna` as bundle `v14` with a raw-part bundle `vq xq xw xs` (reactivation queue, demand watch, strict window for I12 raises) and a Rule R bundle `vr xd xr` (the round's strays); `step-v14`, `p3k` = p3j && v14 with `step-p3k`, `p3k-empty`; `i14-acyclic`, `step-i14-total` | done (branch i14) |
| `spindel.v2.hm5` | h-mem2 (P11) overrides continued: T7 track, take/T17 arm, T14 cancel-acts, T10 finalize family (hmk threaded), T13 run-pointer clears; tools for new activations (`h3r-act-ins`, `h3-undo-g`, `h3-r-new2`) | in progress (branch hm5) |
| `spindel.v2.react` | P8 (`react-done-ok`: reactivation worklist empties within react-fuel) and P6 (`valid-done-ok`: the validation walk, each idle computation expanded once, ends within valid-fuel) | done |
| `spindel.v2.oracle` (test) | lockstep driver against the engine commit log (table + legacy formats, re-sync, quiesce, implicit `slice-exit`, refused items without projection, triage in `oracle_test`) | done (samples 1-13; 4, 6-13 without divergence (7-11 regenerated against engine 27fc1e4, 12 from 4d8a06e, 13 from e735039); 1-3, 5 legacy with triaged lists) |

## Running
- One JVM per worker, through `../ansatz/.internal/scripts/jvm-slot.sh` (`repl PORT` or
  `run -- …`), `-Xmx1g`, shared 4 GB MemAvailable floor.
- `clojure -M:test` runs all proofs (loading a ns = kernel-checking it) plus runtime checks.
- `-A:ansatz-local` checks against the local ansatz checkout instead of release 0.2.613.

## Ansatz gaps
Record any ansatz limitation in `notes/ansatz-gaps.md` with a minimal repro; it gets fixed upstream
(ansatz PR), not worked around silently.

## Pending spec migrations (v1.5.1, after the rule pass)
- Z#6 `edges.debtor` admits resources (wait edges only); T18 fires every armed wait edge on Z; T15 requires no edge on Z.
- Z#7 `acts.members : [(E, i)]` (unfilled only; an edge may appear at several indices; a fire fills all of them).
- Z#16 `pins : id ↦ count`; unpin at 0 refused; root while count > 0.
- Z#15 `edges.seen : Nat?` (none until first delivery); observe registration delivers at once for a source or live comp, else demands d.
- Z#9 a write and a changed settle deliver to observe edges.
- Z#12 T11 resume run starts at `E.at + 1`; restart at 0. Z#13 every creation starts at handles = 1; T3 adoption adds 1.

## Oracle contract (agreed with the spindel session, 2026-11-03; spec v1.5.1 signed off)
- Multi-row items carry the FIRST fresh id; the model allocates consecutively in a fixed per-item order documented in
  step.clj (T4: task, run, run-scope; T5/T11: run, run-scope; T6: act, then member edges in debtor-list order, one edge
  per distinct debtor). Run stamp = run id.
- Engine log: seq of `{:item [:tag …] :accepted bool :proj {table {id row-map}}}` per commit; nil = none (model 0);
  enums as keywords; values/continuations opaque Nats; result `[:ok v]`/`[:err e]`/nil.
- `spindel.v2.oracle` (ours): replay items through compiled `step`, compare accepted + projection (id-keyed sets,
  model-held fields only), assert live-converged + normalization convergence + invariant tripwire; uncovered items
  skipped and counted.
- Engine log samples: `../spindel-v2/.internal/oracle/log-sample-1.edn` (10 commits), `log-sample-2.edn` (34 commits:
  tasks, await all, deferred/mailbox, host read, finally + cancel/finalize). Projection deviations to handle in the
  driver: `:runs :finalizers` = list of N zeros (count only; compare count), `:cleanup {run {:rows []}}` (engine keeps
  storage implicitly; compare keys only), cycle refusals (I12) logged as `{:accepted false}`.
- Next model pass (after the migration): deliver, mailbox post/take, semaphore take/release, `finalize R`, host `cancel`,
  T21 `release-world` (revoke roots: observe/host waits get released, pins dropped, close root scope, Rule R reclaims),
  I12 ranks + cycle refusal. Engine finalizer refs are implicit (closure-held): oracle compares finalizer counts only.
- Alignment pass DONE (branch `align`, 2026-11-04): Z#35 one cleanup slice runs the whole finally chain
  (`finally-exit` pops at the block's start; new item 37 `slice-exit r` = the slice's return, then T13; the
  oracle inserts it when the engine's projection shows the slice gone); Z#36 deliver marks nothing; `::cancelled`
  = reserved Nat 1; closed sources final (T10, write/post/release refused: already so); Z#38 cleanup retains the
  run scope's ancestors; Z#39 T14 fires a cancelled task's dep creditors + T10, `dep-consumed` (T9 delivery
  removes the edge on a final debtor), T11 removes E on a final debtor on resume and restart; Z#40 create-source/
  track/arm refused in a cleanup slice; Z#41 detach re-parents the run scope; Z#42 demote steps the epoch when
  C.run is current; Z#43 complete refused with open regions; Z#44 host items in a slice accepted (already so).
  Acceptance logs 4 (regenerated), 5, 6 (engine a28563d, engine-v2) in test/spindel/v2/oracle/: zero
  divergences; refused items carry no `:proj` (accepted flag compared). The former literal-reading
  counterexamples are resolved and the `lit-*` predicates run as a second tripwire (random drivers; oracle
  except I5). Open finding: T7 `track` on a closed (final) signal keeps an armed dep edge in engine and model
  (sample 5 commit 11), against literal I5 (D2: remove after the delivery, as T6 does with T10).

## Invariants (spindel.v2.inv): findings (2026-11-04)
Predicates for I1, I5, I7, I9, I10, I11a run as a tripwire (`inv-all`) in engine_test's random driver,
inv_test (unrestricted and D0-respecting drivers) and the oracle (`:inv-all` flag). The spec's literal
readings below are FALSE on the model; each has a D0 counterexample of accepted items in
`inv_test/counterexamples` (`lit-*` predicates). Model bug or spec issue — to decide:
- I1 scope parent (`lit-i1-scope`): Rule R's filter removes the parent of a run scope that only a
  cleanup entry keeps (A#9 no downward edges) — contradicts W#9 ("stays closed until its last child row
  is removed"). Holds as "parent 0, existing, or the scope is in a cleanup entry".
- I5 (`lit-i5-dep-final`): T14's debtor side fires only wait creditors; a computation awaiting the
  cancelled task through a dep edge keeps an armed dep edge on a final debtor and its run stays parked
  (T12 fires dep creditors, T14 does not; no T10). Also: T9 `deliver-dep` re-arms when the debtor is
  final (§4.2 says remove), and T11 restart re-arms E even when its debtor is final (Z#22 vs §4.2).
- I7 basis (`lit-i7-basis`) and I8 sources (`lit-i8-sources`): T1 create-source is accepted in a
  cleanup slice (B8 forbids spawn/create-comp, says nothing about sources): it records into an idle
  (demoted) computation's basis, or creates an open source owned by a closed run scope.
- I8 runs (`lit-i8-runs`): detach re-owns the task but its run scope keeps the old parent (Z#26), so
  closing the old owner's subtree closes the running task's run scope; its spawns are then owned by a
  closed scope.
- I9 resources (`lit-i9-res`): B8 lets a cleanup slice offload, which arms a resource of an unwinding run.
- I10 current (`lit-i10-current`): demoting a fresh computation leaves its cancelled run (finalizers) in
  cleanup with R.epoch = C.epoch; T5 (fresh: no epoch step, B2) starts a second current run. Holds as
  "every non-done run of C is C.run".
Also seen (not invariants): `complete` is accepted with open finally regions (normal mode, done, never
retires: L2); host items are accepted while a run holds the slice (D0 is the engine's, not the model's).
RESOLVED by the alignment pass (Z#38–Z#44, branch `align`): every counterexample above now ends with the literal
reading true or its offending item refused (inv_test `literal-readings-resolved`); the literal predicates hold on
both random drivers and run as a tripwire there (and in the oracle, except I5: T7 on a closed signal, open finding).

### Invariant proofs: status and what the rest needs (2026-11-04)
Proved through `world-step`: I10 D0 half (no hypothesis), I9 activations (inv-sample for unique run ids at
T6/take), I5 wait half (from I2), I13 guards, L1 (from step-i3/-i4). Architecture: one `<p>-<f>` lemma per
World function on the step's path (Parts C/D of inv.clj); the `s9-` chain was generated from the `sl-` chain
by renaming, so a new invariant costs its primitive-edit lemmas plus the composites where it is not preserved
edit by edit. Iterate with a loader that skips already-declared constants (scratch `load-new!`: reads the
file, expands local macros, evaluates only undeclared a/defn/a/theorem forms): a reload of inv.clj is ~5 s
against an engine snapshot.

Remaining, with the auxiliary invariants each needs (all predicates already run as tripwire):
- I10 task part 1 (`task-run-is`: a run of task K is K.run): aux R1 "every run's `of` < next-id" (T4's new
  task id is fresh for runs), inv-sample for T5/T11 (a computation id is no task id); state it as
  tbl-all over tasks x runs (no `task-find`, so the filter is monotone); composite lemma for `retire-with`
  (clear-task-run then run-del). R1's chain: bump/insert-edge-fresh become implications (18 spots).
- I10 task part 2 (`task-has-run`) and I10 comp (`comp-run-is`): need "every activation's run is parked"
  (resume never revives a done run), done-monotonicity through the cascade (demote/T11 cancel all of C's
  runs), and, for part 2, `normalized` in EVERY Rule R round (an alive run kept by each round's filter) —
  today's honest flag covers only the last round (`rule-r-pre`).
- I7 (idle shape): aux "an alive run's computation is not idle"; the dep edges a cleanup slice adds for a
  demoted computation (`track` is accepted in a cleanup slice) are removed only by the filter, so the proof
  must characterize live (an edge of an idle creditor is not reached) — needs live soundness per round.
- I1: existence after the filter = the keep set closed under the references (like `filter-safe` for edges,
  P3) plus `no-orphans` of the final round (rr-loop's flag) for detach; sources "detached => closed" alone is
  cheap (a sources-only chain).
- I5 observe `seen` <= debtor version: debtor version monotone and the debtor kept while the observe edge is
  (filter closure again).
- I11a: from I3 plus roots ⊆ obligations; the root scope's successors need I10 task part 1 (a running task
  owned by the root scope is reached from its run).
- I6 is structural in the model (continuations are `cont` fields of edges and activations only); I11b is a
  census gate (no table keyed by history: activation members <= |ds|, finalizers by nesting) — not proved.
- Alignment pass also folds in the counterexample decisions Z#38–Z#44: Z#38 cleanup storage retains the run scope's
  ancestor chain (I1 kept as written); Z#39 T14 makes the cancelled entity final — dep creditors get the err delivered and
  their edges removed (T10); delivery through a dep edge on a final debtor removes the edge; T11 removes (not re-arms) E
  whose debtor is final, on resume and restart; Z#40 cleanup slices may only write/deliver/post/release/close (refuse
  create/track/await/offload/arm); Z#41 detach re-parents the task's run scope; Z#42 demote steps the epoch when it
  cancels the current run; Z#43 complete refused with open finally regions; Z#44 host items while a slice is held are
  effects of the slice-holding run (accept, attribute to it). DONE (branch `align`); next: re-prove the literal
  I1/I5/I7/I8/I9/I10 forms (they now hold on every tripwire; I5 still needs T7 on a closed source decided).

### Literal invariants (branch `lit`, 2026-11-04)
Proved through `world-step` (spindel.v2.lit, hypotheses as step-inv: `rule-r-safe` of the raw world, plus `ga` for I10):
- I10 task part: `step-lit-i10-task : ga w -> gl w -> rule-r-safe raw -> inv-i10-task (world-step w it)` (every run of a
  task K is K.run; a task without result has its run, not done), bundle `gl` preserved (`step-gl`).
- I9 resources: `step-lit-i9-res : g9 w -> rule-r-safe raw -> lit-i9-res (world-step w it)`, bundle `g9` (`step-g9`).
- I10 D0 was proved before (`step-i10-slice`).
- P3 core: `filter-safe-of-refs : inv-sample W -> acts-alive W -> normalized W -> p3-refs W -> filter-safe W`; no Reach
  inversion is needed (a kept edge's creditor is shown live directly: dep creditor non-idle -> live by `normalized`;
  wait/savepoint creditor = activation whose run is alive -> live by `normalized` + live closure).
Found: `complete` with result tag none was accepted (task ends with result none and no run: literal I10 false) ->
the model refuses it (`complete-refused`, test `complete-tag-none-refused`). `cancel(R, replace)` on a task run (never
issued) skipped the task's result -> `cancel-debtor` skips the debtor side only for a computation run.
Remaining, with what each needs (gap 20: `simp only [← h]` ignores the arrow):
- lit-i10-current: `cur-ok` (a run with C's epoch is C.run), epoch >= 1, `idle -> run 0` and `cur-done` (a done current
  run means done-epoch = epoch). `cur-done` is broken inside a normalization round between the stray-run cancel and the
  demotion of the stray computation (Z#42 steps the epoch there); the round override needs the live-closure argument
  (a current run outside live has its computation outside live, `live-close`) carried through `run-cascade` with an
  exemption set (stray computations), and T11 needs "no current run of C" carried through cancel-pred/cut (bundle like
  `ch`: epochs only grow, no run is created there).
- I7 (and `dep-active` of P3): needs "an alive (normal) run's computation is not idle" (a7) at every dep-edge insertion
  and basis edit. a7 is not preserved by `resume` without `acts-alive` (resume would revive a done run), so the bundle
  must contain `ga`: a `g7 = ga && rest7` copy needs every GA override (16) again plus the I7 ones (demote, T5, T3
  replace, reactivation, track/await edges, record-basis/rebasis/cut). Alternative: make `resume` activate only a parked
  run (no reachable change by `ga`), which makes all run-based invariants revival-robust.
- I8 (runs and sources): closing a scope (T16/T13 `close-local`) and cancelling the runs of its tasks are separate
  cascade jobs, so the invariant holds only when the worklist is empty: needs a cascade-worklist invariant (every alive
  run of a task owned by a closed scope has a pending cancel job), not the copy approach. T1 by a normal run needs its
  run scope open (same invariant).
- I1: existence after the filter needs the keep set closed under the references (like P3's `edge-sep`), plus Z#38.
- P3 (rule-r-safe with no hypothesis): `p3-refs` (dep-active = I7's edge part, act-run-has, marked-dep, edge-sep) must be
  preserved by every step and by normalize/filter; dep-active needs the `ga` bundle above; edge-sep needs
  "no reference list names an edge id" for scope parents, run scope/of/resources, finalizer refs and cleanup rows.
### Branch `p3` (2026-11-04)
- Model refinements (no reachable change under `ga`): `resume` wakes only a parked run (`run-wake`, Z#50), so no
  activation fill revives a done run; T7 on a closed (final) source consumes its dep edge in the same commit, the edge
  id stays allocated (Z#48, `track-fin`).
- Oracle: logs with `[:slice-exit r]` items (Z#49) get no implicit exits; `quiesce` also retires a retirable run still
  in cleanup (the engine commits `slice-exit` before T13: sample 7 commit 19, granularity). Sample 7 (engine 6136b5b):
  one granularity divergence (commit 19). Sample 5 (engine a28563d) predates Z#48: its dep edge 14 on the closed signal
  is gone in the model (commits 11-39, recorded). The oracle's `:lit-all` tripwire includes `lit-i5-dep-final`.
- I7 proved through the step (`step-lit-i7`; spindel.v2.idle): a7 needs demote's own cascade to kill every alive run of
  C (`demote-dead`: per-job cascade completeness over `casc-done-ok`, which needs acts-alive: normalization threads it).
- P3 proved (spindel.v2.p3): `step-p3b : p3b w -> p3b (world-step w it)`, `step-rule-r-safe : p3b w -> rule-r-safe raw`;
  the honest hypothesis is discharged for step-inv, step-acts, step-rank, step-gl, step-g9, step-g7 (`*-total`).
  `p3b empty-world` by rfl.
- Literal I5 is FALSE again (inv_test `literal-i5-reactivation-counterexample`): reactivation (§3.4, engine `validate!`)
  re-arms a dep edge per validity entry even when the debtor became final (a closed signal) while the computation was
  idle. Spec decision needed (e.g. a validity entry on a final debtor is delivered/consumed at reactivation, as T6/T10
  and Z#48, or makes the computation invalid). I5's other parts: wait half proved (`step-i5-wait`); seen <= version open.
- Next: I5 seen <= version (bundle over source/computation versions, monotone; filter keeps observed debtors), then I10
  one-current-run, I1, I8 (analysis above).

- (done in branch p3) Next small pass (after branch `lit` merges): Z#48 T7 on a closed (final) source delivers once and consumes its dep edge
  in the same commit (edge id still allocated = `fresh`), so literal I5 holds; Z#49 the engine logs `[:slice-exit r]` for
  a done run's slice return (cleanup slice / cancelled while unwinding) — drop the oracle's implicit slice-exit insertion
  for logs that carry it. Acceptance: `log-sample-7.edn` (22 commits). Then prove literal I5.
- Layer 2 (forks, savepoints) is in the engine (engine-v2): `:fork`, `:fork-host`, `:savepoint`, `:resume-savepoint`,
  `:activate`, `:abandon-savepoint`. Agreed log shape: ONE log per family, entries `{:world w :item … :accepted … :proj …}`
  (proj = that world's tables), fork entries carry the child id, the child's first entry a full :proj; append order =
  commit order across the family (engine family lock). Start only after layer-1 proofs close; tell the engine then.
- Z#50 (confirmed by the engine): T12 result is ok or err only; replace-cancel only on computation runs (T11 restart,
  demotion); fill/resume only for a run parked on that activation — the engine's savepoint path violated this (a resume
  after cancel continued the cancelled body; fixed engine-v2 36a6c36). Layer-2 acceptance case: refused
  `:resume-savepoint`/`:activate` after a cancel.

### Branch `i10` (2026-11-04): literal I10, computation part
Proved (spindel.v2.i10): `step-lit-i10-current-total : p3c w -> lit-i10-current (world-step w it)` with
`p3c = p3b && g10r`, `step-p3c`, `p3c-empty`. The sketch (cur-ok, epochs <= C.epoch, of below the allocator) needed:
- `cur-done` as part of E2 (a current run is alive, or C.done-epoch = C.epoch): T5's fresh case (done-epoch none,
  C.run not busy) would otherwise start a second current run next to a cancelled current run kept in cleanup.
  E2 is broken inside a normalization round (the stray cancel ends C's current run; C's demotion steps the epoch
  later in the same round): the bundle carries an exempt computation list `gxz` (the round's stray computations;
  demote drops C from it once no run is current for C) and an exempt run list `gkz` (a run being retired: C.run is
  cleared before the row goes).
- the cascade cannot cancel an arbitrary run: `job-ok` (every cancel job's run is no current run of a computation
  outside gxz) is threaded through `cascade` (transport bundle `nq`, generic pair predicates over (id, of, epoch) x
  (id, epoch, idle) with proofs that an epoch step keeps them, since T10/invalidation step creditor epochs inside the
  cascade) and discharged at every caller: task runs (T14 host cancel, T6 losers, T12 children/released runs, via
  `K.run names a run of K`), T11's stale predecessor (needs-run), demote's own cancels (C exempt), the round's stray
  cancels (`stray-pair`: a computation outside the strays is idle or live, and a live computation keeps its current
  run live).
- T5 is proved only at gxz = gkz = [] (bundle `g10r`; every other raw lemma is G10's, instantiated by generated
  wrappers): `start-cur` (a current run would be alive or completed, against `startable`).
- T11 carries `kcq` (C keeps an epoch >= its old one, stays awake, has no run at it) through the predecessor's
  cancel, the cut and the entry (the cancel's cascade can step C's epoch by T10 on a cancelled child it awaited: the
  new run is then stale at once, which I10 allows).
No counterexample. Tripwire: i10_test random drivers (g10r and lit-i10-current on every step).

### Branch `i10`, continued: I1, I8, Z#51 (2026-11-04)
- Literal I1 (scope parent) is FALSE (inv_test `literal-i1-reparent-counterexample`, D0, only `lit-i1-scope` fails):
  cleanup[R]'s rows hold R's run scope's ancestors as computed when the entry is made (Z#38, `cleanup-rows-of`), and
  detach re-parents a task's run scope later (Z#41). Run 15 (task 14, scope 16 under task 8's run scope 10) is
  cancelled with a finally region (cleanup rows (2 10 16)); task 8 is detached to the explicit scope 24; closing 24
  cancels and retires run 9; scope 10 stays (kept by cleanup[15]), its parent 24 is not kept and Rule R removes it.
  Spec decision needed: the ancestors a cleanup entry retains are its run scope's current ancestors (the model
  would read them at filter time, as `run-stored`), or detach also rewrites stored chains. The other I1 parts
  (owners of tasks/sources/computations are detached by Rule R's detach, Z#23/Z#25) are not proved yet.
- I8 (closed scopes): no counterexample found (the tripwire holds; spawn/create-source go to `cur-scope`, an open
  scope; top-level items require an open scope; closing a subtree cancels the runs of the tasks it owns in the same
  cascade; detach needs an open target). Proof plan, not started: bundle over runs (of, scope, alive), tasks (owner),
  scopes (id, parent, open), sources (owner, open) with (a) an alive run's task owner and its own run scope are open,
  (b) an open source's owner is open, (c) a task run's scope has the task's owner scope as parent (Z#26/Z#41),
  (d) a run scope belongs to one run; the cascade carries "every alive run violating (a) has a pending cancel job"
  (job-next of retire/close = cancel-jobs of owned-runs of the closed subtree; (c) plus the inversion of
  `scope-subtree` membership place a run whose scope is in the subtree among them), complete at the end by P4.
- Z#51 (spec patch from the coordinator): reactivation takes no dep edge on a final debtor (`react-ok`, consumed, no
  id allocated). inv_test `literal-i5-reactivation-resolved` (was the counterexample); oracle samples 7
  (regenerated: T13 now within the slice-exit commit) and 8 (new, the I5 trace) replay with no divergence. Literal
  I5's dep-final clause now holds on every tripwire; its proof through the step is open (needs an invariant on
  unfilled member dep edges: T10 keeps armed dep edges that are unfilled activation members).
- I11a proved (spindel.v2.i11, `step-i11a-total : p3d w -> inv-i11a (world-step w it)`): from I3 (the filter keeps
  live/cleanup/admitted/stored rows) and reach from the roots = the root scope (id 2) or reach from the obligations.
  The root scope's successors are the running tasks it owns (reached from their alive run, using i10's "K.run names a
  run of K") and its fork markers (none in layer 1). Tripwire: i11_test random drivers (gw, inv-i11a).
- Z#51 (engine-confirmed): reactivation (§3.4 step 3) takes no dep edge on a FINAL debtor (consumed as in T6/T10/Z#48;
  result stays valid if the version matches; no delivery, no re-run); fixes the literal-I5 reactivation counterexample.
  Slice-exit: T13 retires before the `[:slice-exit r]` commit. Acceptance: regenerated `log-sample-7.edn`, new
  `log-sample-8.edn` (the I5 trace shape) in ../spindel-v2/.internal/oracle/ (engine engine-v2 f35c8d5). Then prove the
  dep-final clause of I5.

### Branch `progress` (2026-11-04)
- L2 proved as measure lemmas (spindel.v2.progress): mu-f = |finalizers| + [a finalizer or the slice is held] (the cleanup
  slice still to return, Z#35), mu-z = |resources|; lexicographic (finalizers, then resources), both components monotone.
  (b) `step-mu-le`: a done run is, after any step, absent or done with mu-f and mu-z at most as before (under p3b and the new
  invariant `sok`: a run holding the slice is alive or unwinding, `step-sok`); new cancellations enter the measure.
  (a) `finally-exit-dec` (mu-f - 1), `slice-exit-dec` (1 -> 0), `ack-dec` (mu-z drops; the resource is listed in its run,
  g9); `finalize` and `resource-fire` do not change the measure (the fire of a done run's resource is refused while
  cancelling). (c) `slice-exit-retires`, `ack-retires`: the event that brings mu to (0, 0) retires the run in that step.
  Fair execution => retirement / release-world completes: paper argument from WF of N x N (ns docstring).
- L5 safety half proved (`l5-safety`, `l5-dirty`): quiescent world, non-idle non-live c0 -> its cone has a Blocked entity, an
  eligible needs-run computation, or a parked non-Blocked task (cyclic wait, paper argument). Hypotheses not yet proved
  through the step (tripwires in progress_test at 650+ quiescent points, all hold): `h-cur` (a done current computation run
  has set done-epoch = epoch; cf. `cur-done` in the lit notes), `h-mark` (a marked edge is a dep edge on a waiting
  computation), `h-mem` (an unfilled member of a parked computation run is a leaf, a task with a parked current run, or a
  waiting computation with a dep edge). Next: prove these three as bundles (h-mark needs settle/unmark through the step;
  h-mem needs fast-path/settle delivery to live debtors).
- No counterexample found: the measure never increased for a done run on the random drivers, and L5 held at every quiescent
  point.
- Z#52 (I1 decision, option a): a cleanup entry's ancestor storage is its run scope's CURRENT parent chain, recomputed by
  every Rule R pass (detach moves retention to the new parent) — replace the stored chain. Second half: a run scope is held
  until its run retires (T13 step 4), even when an ancestor's close empties its subtree first (the engine removed it early;
  fixed). Check the model removes a closed empty run scope only at T13. Acceptance: `log-sample-9.edn` (24 commits; the I1
  counterexample shape; offload ack at the end; engine engine-v2 72845ae). Then prove literal I1.

### Branch `l5` (2026-11-04): L5 toward unconditional, I5 dep-final
- h-cur proved from i10's g10r (`l5-h-cur`: E2 + rof); `l5-safety-p3c`/`l5-step-p3c` state L5 on p3c worlds.
- h-mem is NOT a step invariant (a member task's run may be running between quiescent points). Its step form `h-mem2`
  (member = leaf, a task whose run is ALIVE, or a waiting computation the creditor has a dep edge on) holds after every
  step of the random drivers (36k+ steps) and gives h-mem at a quiescent point (`h-mem-of2`). h-mark holds after every
  step as stated. `l5-safety-inv : p3c w -> quiescent w -> h-mark w -> h-mem2 w -> ... -> False` is L5 from p3c and the
  two step invariants. Tripwire (l5_test, every step): h-cur, h-mark, h-mem2, i5-dep-final-mem.
- Two MODEL BUGS found (worklist fuels too small with duplicate queue entries), both fixed in engine.clj, regression tests
  in l5_test:
  - `settle-fuel` was 2 + |comps|; `settle-next` lists a creditor once per marked edge on the settled debtor, so a
    creditor with k dep edges on one debtor is queued k times (`settle-fuel-duplicates`: 8 sites -> 10 pops > 7). The
    loop stopped with a live computation still holding a marked in-edge: its creditor kept pending = 1 with
    done-epoch = epoch forever (not live, not needs-run: stuck; h-mark false). Fuel now 2 + |edges|, and PROVED
    sufficient (`settle-done-ok`, the former honest flag; potential |queue| + #marked edges, Part C of l5.clj).
  - `react-fuel` was 2 + |comps|; `valid-debtors` repeats a debtor once per validity entry (one per dep edge), so the
    reactivation queue ran out before the last idle debtor (`react-fuel-duplicates`): a reactivated computation then had
    a dep edge on an idle computation with no edge on its own source, and a write left the chain live with STALE
    results (coherence, §4.5). Fuel now 2 + the number of validity entries (not proved; same potential argument:
    each idle computation is reactivated once).
  The engine has no fuel (Clojure worklists), so neither bug is expected there; the oracle never hit them.
- Literal I5's dep-final clause WAS FALSE for unfilled members (resolved by Z#53/Z#54 in branch z55: inv_test `literal-i5-member-final-resolved`; was `literal-i5-member-final-counterexample`, D0,
  10 items after `base`): computation 17's run awaits mailbox 14 owned by task 8's run scope; cancelling task 8 removes
  the scope, Rule R detaches (closes) 14, and T10 keeps the armed member edge (spec table T10: "removes armed dep edges
  ... that are not unfilled members"), so an armed dep edge has a final debtor and the run stays parked on a closed
  source (it is Blocked, so L5 is unaffected). Spec decision needed: T10/close delivers err (e.g. ::closed) to unfilled
  members (as T14 does for a cancelled task, Z#39), or I5 exempts unfilled members. The model satisfies the exempting
  reading on every tripwire (`i5-dep-final-mem`); not proved through the step (wait for the decision).
- Proof plan for the rest of L5 (not started; each is a bundle over the whole step like i10's g10):
  h-mark (bundle over edges (marked, kind, debtor) and computations (idle, epoch, done-epoch, pending)):
    (1) marking (`write-raw`, `mark-from`): after the whole fold every debtor in the dirty set has a marked out-edge or
        was invalidated / delivered (its current run not done): needs `dirty-run` CONVERGENCE (Nat fuel 2|E|+1, not
        proved; reach's `reach-run-l-conv` is the template) and Reach soundness for the dirty set;
    (2) aux invariants: done-epoch <= epoch (so an epoch step never makes a computation live) and "an alive current
        run means done-epoch /= epoch" (so a delivered member's computation is not live; ready = live);
    (3) T12: the settle worklist invariant "every live computation with a marked in-edge is queued" plus
        `settle-done-ok`; (4) demote: a stray debtor becomes idle before its stray creditor is demoted in the same
        round: exemption list (like i10's gxz) or show the creditor's edges go first; (5) edge removals that lower a
        creditor's pending (cut-suffix, demote, filter) keep it non-live (needs-run / idle / removed).
  h-mem2: members are filled at once from a live debtor (T6 fast path) and settles deliver to current members (Z#20),
  so a member's computation debtor is never live while the member is unfilled; a task member's task has no result
  (T12/T14 fire wait members) so its run is alive (I10 task part, gl); a member's edge exists, is a dep edge of the
  creditor (computation creditor) and a leaf member's source/resource row exists while the member does (filter keeps
  them: I3). Needs the same done-epoch/current-run aux facts as h-mark.

### Branch `z52` (2026-11-04): ansatz 0.2.613, Z#52, sample 9, literal I1 (scope clause)
- **Bump to ansatz 0.2.613** (tracker gaps 1-9 fixed upstream). What broke: four i10 proofs that relied on 0.2.604's lenient
  `rw` (one silent no-op, one rewrite by a lemma about `:of q` on `:of (rk10 q)`, three rewrites inside a beta-redex left by an
  earlier rw: new gap 22) and one oracle assertion (samples 7/8 regenerated with `::closed` = 2, opaque Nats now start at 3).
  New gaps 22 (rw leaves `(fun r => ..) a` from an instantiated function argument; Lean's instantiateMVars beta-reduces) and
  23 (`induction` on Nat states `Nat.succ n`, Lean `n + 1`). Workarounds removed: #1 (`derive-run-complete` by `induction`),
  #8 (partial `(Reach succ roots)`); kept with reasons: #2, #4, #5, #6, #9 (valid Lean, renames too wide), #7 list fuel (the
  fuel theorems count list cells; measured equal cost, `dirty-run` keeps the Nat form and is linear now). See ansatz-fixes.md.
- **Z#52** (model): a cleanup entry stores only its subtree rows; `cleanup-contrib` = `anc-close` of (run, rows, run-stored):
  every retained id plus its scope's CURRENT ancestor chain (`scope-ancestors`, parent links read at the Rule R pass). The
  run scope's chain is the Z#52 chain; closing every retained row upward adds nothing in reachable worlds (a stored subtree
  scope's parent is in the subtree or is the run scope) and makes the cleanup rows parent-closed by construction. Storage is
  closed upward the same way (refs are sources, Z#3; layer 1 registers none). Proofs: `scope-anc-conv` (the chain converges
  in every world, fuel 2 + #scopes), `scope-anc-filter`/`anc-close-filter` (the filter keeps it: frame + `reach-run-conv-eq`,
  a converged worklist does not depend on its fuel), cleanup-in-filter/storage-filter/crows-in-ok/storage-obl adapted.
  Second half: a run scope is removed only at its run's retirement — already so (`subtree-empty` counts run rows scoped in
  the subtree; Rule R keeps a done run's scope through cleanup[R]); test `z52-run-scope-held-until-retirement`.
  inv_test `literal-i1-reparent-counterexample` -> `literal-i1-reparent-resolved`.
- **Oracle sample 9** (engine 72845ae, 24 commits): replays; triaged divergences (oracle_test `sample-9-known`):
  (d-offload-index) commits 13-20 `[:runs 15 :effect-index]`: the engine's `(offload f)` is one body effect logged as two
  items (`arm-and-park!` takes one `next-at!`), the model's T17 and T6 each advance the index (Z#12 read per item) — spec
  decision needed; (g) commit 22: the engine commits `[:resource-ack 20]` before T13 retires run 15 (`retire-check!` after
  `commit!`; T15 says "then T13", as Z#51 settled for slice-exit) — engine fix suggested. Adapter: a refused fire is logged
  `[:resource-fire z]` (no payload) and maps to the model's refused T18.
- **Literal I1, scope clause, PROVED through the step** (spindel.v2.i1): `step-lit-i1-scope-total : p3e w -> lit-i1-scope
  (world-step w it)`, `p3e = p3d && g1`, `step-p3e`, `p3e-empty`. Crux `filter-lit-i1-scope`: a kept scope is live (live is
  closed under the parent edge), retained by cleanup or storage (closed upward), or admitted (impossible: ids are unique).
  Bundle g1 copied over raw and normalize (144 lemmas) with overrides for add-run-scope (+ spawn/start/dispatch: the parent
  exists or is 0, Z#26), open-scope, detach (the new parent is an open scope) and remove-if-empty. Two reachable-equivalent
  guards in the model: `open-ok` (open-scope requires the run's current scope to exist) and `parent-outside` in
  `subtree-empty` (no scope outside the subtree has its parent in it: always so for a converged subtree). Tripwire i1_test.
- **Literal I1, open clauses** (tripwired by inv-all's `inv-i1` = the literal owner/entity clauses, random drivers + oracle):
  owners of tasks/computations (0 or existing) and sources (existing, or detached and closed) need `no-orphans` of Rule R's
  last round, i.e. rr-loop termination: measure = #rows with a non-zero owner (detach lowers it, normalize and the filter do
  not raise it; fuel 1 + #ids); then a bundle "a source with owner 0 is closed". Resources: owner run exists (the filter keeps
  a resource only with its run: needs res.owner = r <-> res in r.resources, g9-like). Runs: entity and scope exist (the filter
  keeps a done live run's scope only through cleanup[R]: needs "every done run has a cleanup entry", copier per run-upd site).
- DONE (branch z55) Z#53 (I5 member-final decision, option a): closing a source fills its unfilled members and fires its waiters (dep AND
  wait edges): signal/cell/delivered deferred give their value; mailbox/semaphore/undelivered deferred give `err ::closed`
  (reserve a Nat code like cancelled = 1). T10 fills unfilled members first, then removes armed edges; T16 close wakes
  waiters. Engine `take!`/`acquire!` use wait edges. The engine delivered raw source state as ok (bug, fixed). Acceptance:
  `log-sample-10.edn` (20 commits; engine engine-v2 b399a83; ::closed = Nat 2, opaque values from 3; samples 7–10
  regenerated with this numbering, 1–6 keep the old meaning). Then prove I5's dep-final clause literally.
- DONE (branch z55) Z#54 (§4.3, engine 9817ac9): `track` only on signal/cell; `await` on a mailbox = `take` (wait edge, FIFO; logged as
  `:take`); errors with err `{:spindel/invalid op}` and NO commit (model: refusal): `await` on a semaphore, `await-all`/
  `await-any` with a mailbox/semaphore member, `track` on other kinds; host read (T22) of a mailbox/semaphore refused.
  So no dep edge ever has a mailbox/semaphore debtor. Model pass needed: refuse these in T6/T7/T22 (I5/Z#53 traces with a
  computation awaiting a mailbox become `take`). Check the logged `:take` payload matches table row 27 (`take st x k fresh`).
- Engine 5faa399 (engine-v2): `:take` now carries its continuation, `[:take st x k fresh]` = table row 27 (also used for
  semaphore acquire; the model dispatches on source kind). Samples 9 and 10 regenerated with it.
- DONE (branch z55) Z#55 (engine f01b480): (1) offload/timer is ONE body effect `[:arm st kind k fresh]` (kind :offload|:timer, k opaque):
  allocates resource = fresh, activation = fresh+1, wait edge = fresh+2, parks the run, effect-index +1 (replaces table
  row 8 `arm st kind fresh` + a separate await). (2) T15 runs T13 before committing `[:resource-ack z]`; a resource that
  joins at its cancel (unscheduled timer) acks as its own item right after `[:cancel r]` — the model must allow T15 any
  time after T14 put the resource in phase cancelling. Acceptance: samples 7–11 regenerated against f01b480
  (`log-sample-11.edn` new: `[:arm 4 :timer 4 6]` … `[:cancel 4]` `[:resource-ack 6]`).
- DONE (branch z55) Z#56 (engine 27fc1e4): (1) after T21 release-world only HOST admissions are revoked; a cleanup slice's own effects
  (deliver/post/release/write/close, Z#40) and resource completions (fire, then ack) stay accepted so L2 joins; (2) a done
  task leaves its owner scope's task set (that ownership reason) at T13 retirement, not at completion — check the model
  (if T12/T14 drop it at completion, expect an I1 counterexample: cancelled task with an outstanding resource at release);
  (3) the root scope is never removed, even after T21 (I11a allowance). Samples 7–11 regenerated against 27fc1e4.

### Branch `z55` (2026-11-04): Z#53-Z#56, samples 7-11
- **Z#55** (model): Item row 8 is `arm st kind k fresh` = T17 + its park (spindel.v2.engine `t17-arm`/`arm-park`):
  resource fresh (step.clj `arm-raw`, which no longer steps the index: `run-arm` only adds the resource), then
  `take-park` on the armed row: `one` activation fresh + 1 (cont k), its wait edge fresh + 2 on the resource (at = the
  effect index), the run parks, effect-index + 1 once. kind timer (0) | offload (2) (`arm-kind-ok`); a normal run only.
  step.clj's `dispatch` refuses `arm` (the park is engine's); `t17-inv/-refuse/-l4` moved to engine.clj with the new
  statement. Bundles: generic copies where possible; overrides `<b>-arm-park` (+ `t17-<b>`) in acts (GA), lit (G9),
  idle (G7), p3 (AHA; ESB overrides `inv-arm-raw`), progress (MB); inv's `sl-t17`/`s9-t17` by hand (new
  `tbl-upd-mem-self`, `arm-raw-mem`). T15 already accepted any time the resource has no edge (Z#6): after T14 the
  activation and its wait edge are gone, so the ack is accepted and retires the run in the item (sample 11, test
  `z55-arm-one-effect`).
- **Z#53** (model): `close-source` and `detach-source` (rule.clj) run `wake-closed` before T10: every armed wait edge on
  the source and every armed dep edge that is an activation member fires (T9) with the closed source's `deb-result`;
  step.clj `src-result`: a closed mailbox/semaphore/undelivered deferred gives err ::closed (`closed-code` = 2), else
  ok state. Tracks (non-member dep edges) are not invalidated. Proof impact: casc's run-row frame of close-source became a
  run-id frame (`run-ids`, `ri-*`, retire-rows-lt via `count-any-del-lt`); lit's `kw` frame got `kw-fire-edge` & co;
  inv's sl/s9 close/detach lemmas fold `sl-fold-fire`/`s9-fold-fire`; every other bundle copied unchanged.
  inv_test `literal-i5-member-final-counterexample` -> `literal-i5-member-final-resolved` (the take form and the
  undelivered-deferred dep-member form both wake with err ::closed; literal I5 holds).
- **Z#54** (model): raw0 refuses `await` with a mailbox/semaphore member (`await-kind-bad`) and the host read of one
  (`deb-consuming`); T7 already tracked signals/cells only. Engine test `z53-close-wakes-z54-kinds`.
- **Z#56** (model): (1) the model refused nothing for `released` but T21 itself; the engine (27fc1e4) refuses host
  admissions after release except while a run holds the slice. Now `raw = post (raw0g w it)` with `raw0g` = refusal when
  `host-shut` (released, a host item (`host-item`: top-level creations, write, observe/unobserve, pins, handles, host
  waits, deliver/post/release, cancel, close-scope, detach), no run holding the slice); resource fire/ack, the
  scheduling and cleanup-slice items are no admissions. Proof impact: `raw0g-inv/-refuse/-of` (engine), i10-raw/i9-raw
  (inv), `mb-step-of-raw0` takes `host-item it = false`, AHA patches raw0g-inv, i10's raw-deps exclude raw0g-inv; every
  other bundle copied it. Test `release-world-keeps-cleanup-working` (host pin/spawn refused after release, the cleanup
  slice's pin accepted, fire then ack after release, L2 joins);
  (2) the model never drops a done task's ownership before its row goes (no counterexample: T12/T14 keep the owner;
  `subtree-empty` counting a retired task only delays `remove-if-empty`, the filter removes such a closed scope in the
  same Rule R pass and detach then clears the owner; test `z56-retired-task-ownership`); (3) the root scope is never removed: `roots` keeps root-kind
  scopes after release (retain.clj; i11 `root-cases` simplified) and `subtree-empty` is false for a subtree holding a
  root-kind scope (`root-in`).
- **Oracle**: samples 7-11 re-copied (engine engine-v2 27fc1e4): all replay with NO divergence (sample 9's two
  triaged divergences are gone: Z#55 settled both). Samples 1-6 unchanged (no `arm` in them), same known lists.
- **Finding** (spec/engine, not fixed): a `take` on an already-closed, empty mailbox or semaphore parks the run for good
  in the engine (core.cljc `consume-effect!` has no closed check) and in the model; Z#53's "no run stays parked on a
  final debtor" suggests err ::closed at once. Not an I5 violation (wait edge). Spec decision needed.
- **Literal I5 dep-final through the step**: PROVED in branch rest (spindel.v2.i5; see that section). Plan as it was: Plan: bundle `g5 xd w = inv-sample &&
  every armed dep edge has a non-final debtor or one in the exempt list xd` (lit copier with a parameter). Finality
  sites (exempt chains, overrides): `close-source`/`detach-source` (needs: after `wake-closed`, no armed dep member on
  d: fire-edge disarms its target, arms nothing, adds no member; then T10's `finalize-one` drops the rest), `deliver-raw`,
  T12 task completion, T14 `fire-task-cancelled`. Arming sites (need a non-final debtor or a following T10): T6 member
  edges (+ `fin-if-final`), T7 (`track-fin`), site reuse (T6 `edge-reawait`, T7 rearm), `dep-consumed` (guarded), T11 E
  (Z#39), reactivation (`react-ok`), settle re-arm (debtor a computation: `comp-final` false, needs unique ids). fire-edge
  preserves the bundle without hypothesis. The filter only removes rows (with unique ids, finality cannot appear).


### Branch `rest` (2026-11-04): literal I5 dep-final, all of literal I1, h-mark counterexample
- **Literal I5 dep-final PROVED** (spindel.v2.i5): `step-lit-i5-dep-final-total : p3f w -> lit-i5-dep-final (world-step w it)`,
  `p3f = p3e && g5 []`, `step-p3f`, `p3f-empty`. Bundle `g5 xd` (every armed dep edge has a non-final debtor, or one in
  xd; finality read from the source/task tables, `fin-st`), lit's copier with keys (`ek5` edge (kind, phase, debtor),
  `sfin`, `task-done`). Arming sites with guards: dep-consumed/consume-entry (non-final only, p3's kx: rows with the
  edge's id share its debtor), T7 (open trackable source is not final; a closed one consumes the edge, Z#48),
  reactivation (Z#51). Finality sites discharge in the same commit through an escape predicate `jw xd esc` and
  `jw-fire-edge` (a fire disarms its edge: removes it, marks it fired, or re-arms only on a non-final debtor;
  memberships only shrink): close/detach (Z#53, `g5-wake-final`: after wake-closed every armed dep edge on the closed
  source is a non-member, T10 removes it), T14/T12/deliver (`g5-fold-all`: the fired list holds every dep edge on the
  debtor), T6 (`g5-await-raw`: an armed member edge on a final debtor is its debtor's recorded pair `esc6`, and the
  fast path fires it: a final debtor is fast-ready, `fast-not-final`). Tripwire: i5_test (g5 [] and lit-i5-dep-final).
- **h-mark is FALSE** (l5_test `h-mark-fired-sibling-counterexample`, D0, every item accepted): computation 16 awaits two
  signals in one `all` await (two dep edges at the same site); both are invalidated (writes), T11's entry is the first
  fired edge (re-armed for the restart), its sibling stays fired (the cut keeps at <= cut); the new run completes
  without re-awaiting, 16 is live with a leftover fired dep edge on signal 14. A write to 14 fires nothing, but the
  model's dirty set (§4.5.1 "every computation reachable from X through dep edges", any phase) contains 16, so the
  in-edge 23 -> 16 is marked again: 23 has pending 1, done-epoch = epoch, and its debtor 16 never settles again. At the
  quiescent world, 23 is demanded and not live, and its cone has no Blocked entity, no eligible needs-run computation and
  no parked task: **L5's safety half fails**. The engine marks only from computations its fires invalidate (core.cljc
  `invalidate!` -> `mark-from!`), so it is not affected. Spec decision needed: mark through ARMED dep edges only (engine),
  and/or T11 consumes every fired edge at the entry site. Consequence: L5 cannot be proved unconditionally (goal 2); h-mem2
  through the step was not attempted.
- **Rule R terminates with no orphan PROVED** (spindel.v2.i1o, `rule-r-no-orphans`): the owner count (rows with a non-zero
  owner) never grows through normalization (bundle NZ, 100+ lemmas copied) or the filter, and detach lowers it when the
  round's input has an orphan (`detach-lt`); the fuel 1 + #ids suffices. This is new obligation P9.
- **Literal I1 PROVED, every clause** (spindel.v2.i1o + i1r): owners of tasks/computations (0 or existing) and sources
  (existing, or 0 and closed: bundle gso) from no-orphans; resource owners and run entities/scopes from bundle gr0
  (R1 a resource's owner run holds it, R2 a run's entity and scope exist, R3 a run is alive or has a cleanup entry)
  and Rule R's filter keeping every run (`run-kept`). Needed: (1) T12: a run that completes retirable has no cleanup
  entry until the cascade's last job retires it: tracked through the cascade (`track-cascade`, bundles krb/neb over
  job-apply) with P4 (`casc-done-ga`; ga threaded into the GR0 copies of t12/raw0/raw0g/raw by source patches);
  (2) demotion deletes a computation only when no run of it is left (`gr0-demote-aa`: demote's cascade kills its alive
  runs, `demote-dead` with acts-alive; dead runs have cleanup entries storing their entity) — normalization threaded
  with acts-alive (P2's round bundle bn). `step-lit-i1-total : p3h w -> inv-i1 (world-step w it)`, `p3h = p3g && gr0`.
  Tripwires: i1o_test (gso, i1-own, no-orphans), i1r_test (gr0, inv-i1).
- Open: I8 (closed scopes: runs and sources), h-mem2/h-mark (blocked by the spec decision above), P6, P8.

- Z#57 (engine 4d8a06e): `take`/acquire on a CLOSED source still consumes what is left (mailbox backlog / remaining
  permits); when nothing is left it fails at once with err ::closed (2): the take item is still committed and accepted,
  activation (fresh) and wait edge (fresh+1) allocated and consumed as in the available fast path, and the run continues
  through its error continuation. Applies to `await` on a mailbox (= take, Z#54). Acceptance: `log-sample-12.edn` (17
  commits). DONE (branch z57, below).
- Z#59 (L5 decision, engine engine-v2 e735039): (a) §4.5.1 marking starts only from computations whose dep edge on the
  written source FIRES (was armed); from those it follows their dep out-edges in any phase; (b) T11's cut is by CREATION
  ORDER: E = earliest fired dep edge in C.ins order; every dep edge created after E is cut into adoption baselines
  (siblings at E's site included); group sites restart from the body (Y#3), E re-armed. Acceptance: `log-sample-13.edn`
  (26 commits; the L5 counterexample trace). Then retry h-mark / h-mem2 and L5 unconditional.

### Branch `z57` (2026-11-04): Z#57, sample 12, literal I8, P8, P6
- **Z#57** (model): `take-ready s` = available or closed: the immediate path `take-now` (two ids allocated, effect index
  + 1, the run keeps its slice; err ::closed is the continuation's business, opaque here); `source-consume` leaves a
  source with nothing left unchanged (no version step, as engine 4d8a06e). Proof impact: every bundle's take override
  cases on `take-ready` (acts GA, p3 AHA, idle G7, i5 G5, progress MB, inv sl/s9), the source-consume lemmas of i5
  (`sfin-consume`), p3 (`source-consume-hv`), i1o (`src0-consume`) case on availability. The z55 finding (a take on a
  closed empty mailbox parked for good) is resolved.
- **Oracle sample 12** (engine engine-v2 4d8a06e, 17 commits): replays with NO divergence (oracle_test
  `sample-12-table-format`: the closed, detached mailbox hands out its backlog [7] (version 1 -> 2), the next take fails
  with no version step and ids 19, 20 allocated). Samples 7-11 unchanged, still zero divergences.
- **Literal I8 PROVED** (spindel.v2.i8): `step-lit-i8-total : p3i w -> lit-i8-runs (world-step w it) && lit-i8-sources
  (world-step w it)`, `p3i = p3h && g8 []`, `step-p3i`, `p3i-empty`. Bundle `g8 xs` over key lists (runs (id, of, alive)
  = lit's rkey, tasks (id, owner), scopes (id, open), sources (id, owner, open)); closedness is `tbl-any` over the keys
  (monotone under deletions and the filter, no unique-ids argument). The plan as written: closing a subtree
  (`close-local`) closes its scopes and the sources it owns in one edit (`i8k-close`: sources by a fold invariant, the
  run part by `cov8`); the alive runs of the tasks it owns join the escape list, and they are exactly the cancel jobs the
  cascade queues next (`owned-runs`); through the cascade the escape list is the pending cancel jobs (`cj`, `g8-job`,
  `g8-cascade`); a cancel discharges its id (kw8 of T14's local part: only that run's key goes down); P4 empties the
  worklist (`g8-run-cascade-ga` via `casc-done-ga`, `g8-run-cascade-aa` via `casc-done-ok`). ga is threaded to every
  raw cascade site (T11 predecessor cancel, T12, T14, T15, T16, T21, slice-exit, the `any` losers: raw0/raw0g patched,
  raw overridden), acts-alive through Rule R (demote, the strays; copied from GR0). Parks need the parked run alive
  (take/arm: the slice holder; await: mini bundle `ka` through the wiring and fills). T11's new run is a computation's
  (`t8ks-cascade`: the cascade keeps the task keys). Detach: the new owner is an open scope (`open-not-closed`, unique
  scope ids); Rule R's detach sets owner 0 (no scope 0).
  **Deviation from the plan**: the plan's run-scope half ((a) an alive task run's own scope is open, (c) a task run's
  scope has the task's owner as parent, (d)/(e) run scopes) is replaced by a raw0 guard: spawn/create-source by a task
  run whose current scope is not open is refused (`cur-closed`, engine.clj; reachable-equivalent: tripwire `cur-open-ok`
  on the random drivers and every commit of samples 7-12, i8_test). New obligation **P10**: discharge the guard (prove
  `cur-open-ok` through the step: (a) with the escape list again; at `close-local` an alive task run whose scope lies in
  the subtree must be in `owned-runs`, which needs (c) + the subtree inversion (every visited scope is the root or a child
  of a visited one: an invariant of `reach-closure-l`, no convergence needed) + (d) distinct runs have distinct scopes and
  (e) run scopes have kind run (T16 closes explicit scopes only, T21 the root)).
- **P8 PROVED** (spindel.v2.react, `react-done-ok : inv-sample w -> react-done w d`): `react-run8` = react-loop with its
  leftover queue (`react-run8-world`); potential |queue| + vm8 (validity entries of idle computations); the
  reactivation's edges and rank raises keep every computation's (id, idle, #validity) key.
- **P6: model bug found and fixed, then PROVED**. `valid-loop` walked every path of the validity DAG (no memo): three
  computations each validating the next through four entries need about 150 pops against the fuel 1 + 13 x (1 + 5) = 79, so
  the top was declared invalid (epoch step, re-run) although nothing changed; the engine's recursive `validate!`
  reactivates each debtor once (it is then not idle) and reactivates the top (react_test `p6-validity-chain`, D0, all
  items accepted; fails on cb43bb2). Fix: a `seen` list expands each idle computation once (the check is pure);
  `valid-fuel` = 2 + #validity entries. `valid-done-ok : inv-sample w -> comp-find w x = some c -> valid-done w c`
  (potential: pending entries + entries of unexpanded idle computations, `useen-add`). The oracle never hit it (no
  sample has such a chain). Note: the spec's "§3.4 validation recursion bounded by rank" is not what bounds the walk
  (ranks of a validity entry's debtor can rise after the demotion); the bound is the expansion count.
- Tripwires: i8_test (g8 [], lit-i8-runs/-sources, cur-open-ok: random drivers + samples 7-12), react_test (react-done on
  every computation of the random drivers' worlds, the P6 regression).
- Open: P10 (the cur-closed guard), L5 h-mark/h-mem2 (Z#59 pending), layer 2.
- Z#60 + I14 (engine engine-v2 e6d463f; also: a resource joined at its cancel is now acked via the cleanup queue, FIFO with cleanup slices, still its own `[:resource-ack z]` item after the cancel): §3.4 validation visits each idle computation at most once per demand (the engine's idle flag
  is the visited set), linear; terminates because the validity graph over idle computations is acyclic (not by rank).
  Proposed new invariant I14 "validity graph over idle computations is acyclic" (engine termination relies on it; the
  model's walk uses an explicit seen set). Queue: prove I14 through world-step after the z59 pass.

### Branch `z59` (2026-11-04): Z#59, sample 13
- **Z#59** (model; engine engine-v2 e735039): (a) §4.5.1 marking starts only from computations whose dep edge on the
  written source fires (was ARMED): `dirty-run w x` = reach from `armed-creditors (:edges w) x` (step.clj; was every dep
  creditor of x in any phase), then follows dep out-edges in any phase as before (`dirty-from`). T3's replacement
  (`mark-from`) keeps the any-phase cone from c (`cone-set`, the engine's `mark-from!`). (b) T11: E = the earliest fired
  dep edge in CREATION order = the least id (one allocator, ids never change; the engine's C.ins order: matched prefix
  edges first, new edges appended), and every dep edge of C created after E is cut (`suffix-edge` compares ids,
  siblings at E's site included); the creations still split by site (`after-cut` on E.at for basis/adoption). So
  `cut-suffix w c has cut cid` takes E's id as a fifth argument (every bundle's dispatch override threads `(:id e)`,
  `0` without an entry). Proof impact: ONE proof changed (p3 `earliest-mem` cases on `Nat.blt (:id ..)`); every other
  theorem re-checks unchanged (generic in the cut predicate and the marked list).
- l5_test `h-mark-fired-sibling-counterexample` -> `h-mark-fired-sibling-resolved`: E = 21 (the earliest fired edge by
  creation) is re-armed, its sibling 22 at the same site is cut; a write to 15 marks nothing; a write to 14 fires E,
  16 is dirty, needs-run and eligible, h-mark holds and L5's safety half holds for 23 at the quiescent point.
  New tripwire `l5-facts-samples` (h-mark, h-mem2 at every commit of samples 7-13).
- **Oracle sample 13** (engine e735039, 26 commits, the former counterexample as an engine trace): replays with NO
  divergence (oracle_test `sample-13-table-format`: both edges 15, 16 of computation 5 fired, T11 re-arms 15 and cuts
  16, the later write to 4 marks nothing, 6 stays live). Samples 7-12 unchanged: zero divergences. i8_test's
  cur-open-ok tripwire runs over samples 7-13. Suite after merging main: 121 tests / 138,514 assertions, green.
- **Z#59 as theorems** (spindel.v2.z59, 16 lemmas): `z59-t11-no-fired : entry-edge w c = some e -> no dep edge of c is
  fired in consume-entry (cut-suffix w c true k (:id e)) e` (E is the least fired id, `z59-earliest-min`; every later
  dep edge is cut, `z59-cut-p1`; E itself is re-armed or removed); `z59-fired-starts-none` (a computation with no ARMED
  dep edge on x is no root of the write's marking). The theorem cuts the world the entry is read from; `dispatch-raw`
  reads E before the predecessor's cancel (`cancel-pred`, a cascade), so the step form is a tripwire (z59_test: after
  every accepted T11 through `world-step` the computation has no fired dep edge; random drivers + samples 7-13).
  Note: the model marks from every ARMED fire, the engine only from invalidations; a write never DELIVERS (T6's fast
  path fills a signal/cell member at once: `fast-ready`/`sig-cell`), so the two agree.
- **Goal "L5 unconditional" NOT reached** (h-mark, h-mem2 through `world-step` still open). Refined plan for h-mark (the
  pieces Z#59 changed are proved; the rest is i10-sized):
  (0) aux bundle over computations and runs: `dle` (done-epoch <= epoch) and `cde` (a computation whose current run is
      alive has done-epoch /= epoch). Both TRIPWIRED with no violation (z59_test: random drivers incl. 30 x 120 steps,
      samples 7-13). Sites: T12 sets done-epoch := epoch only for the current run (and retires it), T5/T11 start a run
      only when needs-run (done-epoch /= epoch), reactivation sets done-epoch := epoch on an idle computation with
      run 0 (no current run), demote/T3 replace step the epoch; `resume` revives no done run (ga).
  (1) T2/T3 marking (Z#59 a): final-state argument, NO dirty-run convergence needed: a visited d is a root (creditor
      of an armed dep edge on x: the fire invalidates it, epoch + 1 > done-epoch by dle; a delivery is impossible, see
      above) or a dep creditor of a visited m (`Reach` inversion), whose edge on m is a mark target, so pending(d) >= 1
      after the fold (pending-exact); d is awake (g7: a dep creditor is not idle). Pre-existing marks stay valid:
      fire-edge only steps epochs, re-arms/fires/seens edges, removes unmarked edges (wait edges, the activation's
      members by `drop-act`, dep edges on final debtors: never marked since a marked debtor is a computation).
      Reusable lemma to write first: `hm-fire-edge` (h-mark, dle, inv-sample preserved by every T9).
  (2) T12 + settle: loop invariant "every marked edge's debtor is waiting or queued"; a settle unmarks every marked
      out-edge of the popped d (l5 Part C `sd-fold`), invalidations only step epochs, `settle-next` queues each creditor
      that becomes ready; a live creditor with a busy current run is never left unqueued by cde; `settle-done-ok` empties
      the queue.
  (3) demote (Rule R): a stray debtor is demoted while its stray creditors still hold marked edges on it: exemption list
      (as i10's gxz) discharged when the creditor's edges go (`demote-edges` drops the creditor's own dep edges);
      filter: a removed computation's creditors are removed too (retention follows dep edges, P3's filter-safe).
  (4) T11/cut, consume-entry, remove-edge of a marked edge: the creditor keeps done-epoch /= epoch (needs-run) or is
      being dispatched; T3 replace of an idle computation: no dep edge has an idle debtor (third aux fact `dna`, to
      tripwire). h-mem2: as in branch l5's plan, on top of the same aux bundle.
- M6 phase A (engine, public API on v2) adds log items, none change existing ones: `[:world-state st v-old v-new]`
  (st = run id or nil on the host; opaque interned per-world persistent map; no rows, no Rule R role; forked by value; a
  body write is an effect at its site, repeated on re-run) — model as an uninterpreted per-world cell + item. Coming:
  `:external` resource kind (T17/T18 lifecycle, cancel may join at once), Z#61 fail-fast `await-all` (an all activation
  completes at its first err slot), Z#62 semaphore maximum. Each arrives with a sample.
- Z#62 + Z#63 (engine 4c2ef43; no invariant-shape change): Z#62 semaphore starts with n permits, maximum n; release at the
  maximum refused; a granted acquire delivers `:acquired`. Z#63 resource kind `external`: T17/T18/T15 lifecycle;
  completion is a one-shot fire+ack item accepted after release; cancel either joins (ack at once) or leaves the physical
  completion outstanding (acks later); controller belongs to the world that set it (F1); inherited external is dormant
  (§8.1, like offload). Samples follow with the phase-A batch.

### Branch `l5b` (2026-11-04): the h-mark plan's auxiliary facts through the step (P11 step (0))
- **Aux bundle `gd` PROVED through `world-step`** (spindel.v2.hm): per computation (keyed (id, run, epoch,
  done-epoch), `gdkeys`) `dle` (done-epoch <= epoch, 0 < epoch), `hrb` (C.run below the allocator), `rof` (C.run
  names a run of C), `cde` (done-epoch = epoch -> no ALIVE run of C at its epoch, by `of`: any run id). `step-gd :
  g7 w -> g10r w -> gd w -> rule-r-safe raw -> gd (world-step w it)`; `p3j = p3i && gd`, `step-p3j`, `p3j-empty`
  (no honest hypothesis), `step-gd-facts-total`. The tripwire form of cde (z59_test `aux-ok?`, C.run only) follows
  from cde + rof. Architecture: computation edits that keep the id, keep or clear C.run, do not lower the epoch and
  keep or clear done-epoch (`gd-cmono`) and run edits that keep id/of/epoch and never revive (`gd-rmono`) are frames
  via a source patch (`gd-patch`, as G7's); overrides only where done-epoch is SET or a run is created/parked:
  T12 (`gd-complete-body/-raw`, `t12-gd`: the completed run is C's only run at C's epoch, i10's `cur-eq` from
  g10r, `gd-u1-of-g10r`), reactivation (`gd-react-one/-loop`, `gd-demand-reactive`, T6/T8/T22: an idle
  computation has no alive run, g7's a7, `gd-noal-idle`), T5 (`gd-start-raw`: startable -> done-epoch /=
  start-epoch, `gd-start-ne`), T11 (`gd-new-run-of`, `gd-dispatch-raw`: the new run is at the epoch read BEFORE
  the predecessor's cancel; watch bundle `hkw c e` (rows with id c keep epoch >= e, done-epoch /= e; cmono keeps
  it) copied through cancel-pred/cut-suffix/consume-entry), new runs (`gd-add-run-scope` with `gd-ok-new`; T4's
  task run has epoch 0 < every computation's epoch), parks (i8's overrides with KA, transformed by `gd-from-g8`).
  g7 and g10r are threaded from the step's input (raw0/raw0g/raw patched with two premises; p3i supplies both:
  `p3i-ctx`, `p3i-g7`). Rule R and the filter copy with no override. Tripwire: hm_test (gd after every step of
  the random drivers and every commit of samples 7-13).
- **Part F (h-mark step (1) groundwork)**: `reach-closure-inv`/`reach-run-inv` (every visited node of the worklist
  closure is a root or a successor of a visited node: Bool form `rinv-q`, no convergence), `hm-dirty-back` (a dirty
  computation is a creditor of an ARMED dep edge on the written source or a dep creditor of a dirty one, so its
  edge on that one is a mark target), `hm-cone-back` (T3).
- New tripwires (z59_test): `dna` (no dep edge has an idle computation debtor) holds everywhere. `nms` as first
  stated (no unfilled activation member is a dep edge on a signal/cell) is FALSE on the random driver (seed
  20261591 run 12 step 73, `[18 6 [17 3] 1 1 39 []]`): a STALE computation run awaiting a signal gets no delivery
  from the fast path (`fire-dep`: `run-current-of` fails), the edge is INVALIDATED (fired) and stays an unfilled
  member. The ARMED form (no unfilled member is an armed dep edge on a signal/cell) holds on every tripwire and is
  what the write argument needs ("a write never delivers", PLAN z59 (1)); it is not proved. Alternative for the
  write's roots that avoids it: a delivery needs `member-current` (a run of C at C's epoch with an activation:
  alive by ga), so by gd's cde C was not live before the write; done-epoch never changes in the fire fold and
  the epoch only grows.
- Suite (after merging main, 7b3dfd5): 124 tests / 145,671 assertions, green.
- **Goal "L5 unconditional" NOT reached**: h-mark and h-mem2 through the step remain open (P11). Design for the
  `hm` bundle as learned here: rest over keyed edges (kind, marked, debtor) and keyed computations (id, idle,
  epoch, done-epoch, pending) with an exemption list of debtors (`hmo xm`: marked -> dep and (debtor waiting or in
  xm)); thread gd (now a step invariant), g7 (dm: a dep creditor is not idle) and ga as gd threads g7/g10r.
  Non-frame primitives: mark-edge (debtor waiting/exempt at the end: T2/T3 final-state argument with
  `hm-dirty-back`, needs a fire-fold frame: computations' done-epoch constant, epochs non-decreasing, dep edges
  on computations untouched), unmark-edge/remove-edge of a MARKED edge (its creditor may become live: settle's
  queue as the exemption list, P7's `sd-fold`/`es-nm` for "no marked out-edge of the settled debtor"; cde + rof
  make every live creditor settle-ready, so `settle-next` queues it), comp-result-row (T12: the settled debtor
  is exempt until popped), comp-make-idle (demote: stray debtors exempt until their creditors' edges are dropped),
  drop-edges/drop-cred (pending changes: the creditor is idle or needs-run), epoch steps (frames given dle).
  h-mem2 on top of the same bundle (plan in branch l5). Then I14, P10 (untouched in this branch).

### Branch `hm` (2026-11-04): the h-mark bundle (P11), all but T2, T12 and demote
- **Bundle `hmk hxm`** (spindel.v2.hmk) = inv-sample && every marked edge is a dep edge whose debtor is a computation row
  (`tbl-has`) and either every row with that id is *strongly waiting* (`hk-wt`: not idle, and done-epoch < epoch or
  pending /= 0) or the debtor is in the exemption list `hxm`. The strict `<` makes every epoch step a frame without dle;
  with gd's dle it is the same as waiting. `hk-h-mark : hmk [] w -> h-mark w`, `hmk-empty`. Tripwire (hmk_test): `hmk []`
  after every step of the random drivers (2 x 12 x 80) and every commit of samples 7-13: no violation.
- **Primitives**: frames by rfl (rows other than comps/edges), `hkr-edge-upd` (kind/debtor/marked kept), comp edits through a
  source patch (`hmk-patch` -> `hmk-comp-upd-m`, row functions that keep a waiting row waiting: inc-epoch, demand, replace,
  start, `-hkm` lemmas; identity-like ones by defeq), comp-ins (the new row is waiting: `(Eq.refl true)` extra arg),
  comp-del (unreferenced), filter-world (fs-ref keeps a kept edge's debtor), insert-edge (unmarked). Non-frames take a
  premise, so their callers are overrides: `hmk-mark-edge` (rows with the id, once marked, satisfy the fact: `hk-mok`),
  `hmk-unmark-edge`/`hmk-remove-edge` (the found edge, if marked, has a *safe* creditor: exempt, or every row with its id
  idle or done-epoch < epoch: `hk-safe`, so a pending decrement keeps its waiting), `hmk-drop-edges` (every dropped marked
  edge has a safe creditor: `hk-dok`; pendings re-counted, `hk-count-eq`), `hmk-drop-cred`/`hmk-drop-act` (no computation
  has the activation's id).
- **Overrides proved** (copy checked by `lcopy!` of every raw0 transition except t2-inv/t12-inv, plus cancel-losers and
  detach): resume/fill-slot/fire-dep/fire-wait-act/fire-wait/fire-edge (an activation id is no computation: `act-not-comp`;
  a removed fired edge is unmarked: wait/observe kind, or a final debtor = no computation, `hk-final-not-comp`),
  cancel-acts (fold over activation ids), T10 finalize-one/fin-loop/finalize-debtor (premise: the debtor is no computation)
  and its callers close-source/close-local/fire-task-cancelled/debtor-side/fin-if-final/T-deliver/detach-source/detach
  (computation ids are kept by every fire: `hk-has-fire-edge`, `hk-fold-has`, `hmk-fold-noc`), T7 track-fin/track-raw
  (new edge, or the site edge on a source: unmarked), release-world (only host edges stay: `hk-dok-host`), reactivation
  (`hmk-comp-react`: comp-react-row on an IDLE computation, no non-exempt marked edge is justified by it), T11 (the
  dispatched C is strong: needs-run + gd's dle; watch bundle `hsw c` copied through cancel-pred: every gd-cmono edit keeps
  done-epoch < epoch; the entry edge keeps its debtor: p3's `kx`), T3 replace (`hmk-mfr`: the mark fold runs with the
  marked set S = C :: cone exempt (`hmk-fold-mark-x`, `hk-tg`), discharged at the end (`hmk-discharge`): C is strong
  (`hk-rc-replace`, gd's dle), every cone member is a dep creditor of an edge on S (`hk-cone-edge`), that edge is a target,
  every target is marked after the fold (`hk-fold-J`, needs edge-id nodup), so its pending > 0 and it is awake (g7's dm):
  `hk-fold-wif`). t3-hmk/t3-top-hmk take `gd w`, `g7 w`; t11-hmk takes `gd w`.
- **Open (P11)**, in order of the remaining work:
  (1) T2 write (`inv-write-raw`): the mark fold part is the T3 toolkit with S = dirty-set; new needs: (a) the fire fold over
      `edges-onto x` keeps each target id's kind/debtor (a kx-like watch for kind+debtor copied through fire-edge), the
      cone's in-edges (`tbl-any (hk-ck d T)` through fire-edge: an edge on a computation is never removed by a fire) and
      awake; (b) a ROOT d (armed creditor of x) is strong after the fire fold: its armed edge e on x is untouched by the
      fires of other ids (needs: a fire removes only its own edge or activation-creditor edges), and at e's turn the fire is an
      invalidation (epoch + 1 > done-epoch by dle) or a delivery, which needs a current alive run of d (ga) so done-epoch /=
      epoch by cde; afterwards `hsw d` copied through fire-edge keeps it. Then `hmk-discharge` as in T3.
  (2) T12 complete + settle: complete-body's comp-result-row makes C possibly live while it has marked out-edges: exempt
      [C]; `settle-edge`'s unmark: the creditor is safe or becomes settle-ready (live => settle-ready by gd's cde + rof),
      so the loop invariant is `hmk q w` with q = the queue; `settle-done-ok` (l5) empties it; needs a loop lemma over
      `settle-loop` with gd/g7 at every iteration (GD/G7 copies of settle-one exist).
  (3) demote (Rule R): the round's strays as exemption list (a stray's creditor is a stray: live is closed, retain
      successors follow dep edges, `live-close`); discharged after the demote fold because every stray creditor's dep
      edges are dropped (`demote-edges`); needs a fold invariant "no dep edge has a demoted creditor".
  (4) Integration: raw0/raw0g/raw patched to take gd and g7 (as GD's `gd-add-hyps`), rule-r rounds, `step-hmk`,
      `p3k = p3j && hmk []`, `step-p3k`, `p3k-empty`, `step-h-mark-total`. Then h-mem2 (not started; plan in branch l5) and
      `l5-safety-total`.
- No counterexample found: `hmk []` (strong form) holds on every tripwire.
- Suite (after merging main, a04effc): 127 tests / 147,790 assertions, green.

### Branch `i14` (2026-11-04): I14 through the step
- **Model addition (model-only, not projected; oracle unchanged at zero divergences on samples 7-13)**: a validity entry
  `Valid` has two more fields, `stamp` = the allocator (`next-id`) and `crank` = the creditor's I12 rank, both recorded by
  `edge-valid` at demotion (rule.clj; `crank-of` = engine's `comp-rank`). The oracle's projection reads (debtor, version)
  only; its re-sync fills 0 0. No theorem of the earlier namespaces changed.
- **Why not the rank alone**: an idle computation's validity debtor that is still live can be raised by I12 after the
  demotion (a later await) and demoted later with a larger rank, so the frozen rank order of the entries goes the wrong
  way across passes. The witness is lexicographic: a later pass has a larger stamp (Rule R never allocates, so a pass
  shares the stamp; T6, T8 and T22 allocate before any reactivation or raise), within a pass I12 orders the demotions
  (a dep edge's debtor has a smaller rank, ranks do not move in Rule R).
- **Invariant `v14`** (spindel.v2.i14) = inv-sample && `iv14` (for every idle C and entry v: stamp(v) <= next-id; for every
  row D with v's debtor id: stamp(v) < next-id or rank(D) < crank(v), and when D is idle every entry of D is below v)
  && `dna` (no dep edge has an idle computation debtor; z59_test's tripwire, now a theorem). `i14-acyclic`: along a
  validity path the entries strictly descend (`prec14` transitive, irreflexive: `reach-above`, `any-above-self`).
- **Proof architecture**: every invariant part is closed under *domination* (a row keeps id and rank, and if it is idle
  afterwards it was idle with the same validity; edges keep kind/creditor/debtor): `cpres`/`epres`, one frame lemma
  per bundle (`vqk-frame`, `vrk-frame`), primitive edits via `wdom`. Two bundles copied with lit's copier:
  `vq zq9 zw9 zs9` (raw part: zq9 = the reactivation queue as exemption list for dep edges on idle computations, zw9 =
  computations demanded and therefore awake, zs9 = strict window: every stamp below the allocator, under which I12's
  `comp-set-rank` is a frame, `vq-set-rank` via the rank-free `ivs14`) with overrides T6 (`vq-await-raw`: the act
  allocation opens the window, the demand fold watches the debtors, the wiring's dep edges hit awake debtors), T7
  (`vq-track-raw`, the debtor is a source), T8/T22 (the fresh edge opens the window; T22's edge is ok by deb-exists),
  take-park (explicit worlds); reactivation (`vq-r8` over react-run8 with the leftover queue; react-done-ok empties it).
  `vr zd9 zr9` (Rule R: zd9 = the round's strays, zr9 = strays not yet demoted; `dne14`: a dep edge on an idle stray
  has the pass's stamp and a crank below its creditor's rank) with `vr-demote` (`vrk-make-idle`: the new entries carry
  the pass stamp and x's rank, I12 orders them), `vr-pass-start` (live closure: a dep creditor of a stray is a stray),
  `vr-pass-end`, `vr-norm-round`/`-loop`, `vr-normalize`, `vr-rule-r`. inv-rank is threaded with rank-step's copies.
- **Theorems**: `step-v14 : v14 w -> g7 w -> inv-rank w -> rule-r-safe raw -> v14 (world-step w it)`, `p3k = p3j && v14`,
  `step-p3k`, `p3k-empty`, `i14-acyclic : v14 w -> Not (Reach (vsucc14 w) (vsucc14 w x) x)`, `step-i14-total`.
- No counterexample. Tripwire i14_test: v14 and a DFS acyclicity check after every step of the random drivers and every
  commit of samples 7-13; a validity chain demoted in one Rule R pass (one stamp, cranks strictly decreasing) and
  reactivated. New gap #25 (`exact (Exists.intro ..)`).
- **P10 (i8's raw0 guard `cur-closed`, part of `body-shut`) reduced, not closed**: `cur-open-of-run-scope : inv-sample w ->
  scope-open-at w (:scope r) -> run-cur-closed w r = false` (the current scope is `nat-max` of the run scope and the nodes
  reached through `open-explicit-children`; a reached node other than the root is an open scope row, unique scope ids)
  and `cur-open-of-rso : inv-sample w -> tbl-all (rso w) runs -> cur-open-ok w`, where `rso` = every alive normal task
  run's RUN scope is open. What remains is `rso` through `world-step`. Plan (cheaper than z57's escape-list plan: no
  escape list, the cascade is edit-by-edit): a bundle over run keys (id, of, alive, scope), task keys (id, owner), scope
  keys (id, parent, open, kind) with
    (c) a task run's scope row has the task's owner as parent, or a parent that is no scope (Rule R's detach orphans
        the task with owner 0; its run scope's parent was removed; a computation-owned task gets parent 0),
    (d) distinct runs have distinct scopes, (e) every run's scope has kind run,
    (si) a closed scope of an alive task run has a closed parent scope.
  close-local closes a subtree: a newly closed run scope that is not the subtree's root has a visited parent (subtree
  inversion, as hm's `reach-run-inv`), so its parent is closed; the root is a retiring (done) run's scope (T13), an
  explicit scope (T16, (e)) or the root scope (T21). At a step boundary rso follows: an alive task run with a closed
  scope has, by (si) and (c), a closed owner scope, which I8 (`g8 []`) excludes. The filter and the detach item are the
  only places where (si) needs rso first (the filter can remove a closed parent; detach re-parents), and both run where
  `g8 []` holds (copy g8 facts in as gd threaded g7). Overrides: close-local, add-run-scope, open-scope, detach item,
  Rule R's detach-task, filter, remove-if-empty. All five facts hold on every tripwire (i14_test: random drivers,
  samples 7-13). Then `body-shut` = `in-cleanup` for every token whose run is valid, i.e. the guard is redundant.

- Suite (after merging main, hmk included): 131 tests / 156,116 assertions, green.

### Branch `hm2` (2026-11-04): h-mark through the step (P11, first half)
- **h-mark PROVED through `world-step` with no honest hypothesis** (spindel.v2.hmk2): `step-p3l : p3l w -> p3l (world-step w it)`,
  `p3l = p3k && hmk []` (p3k = p3j && v14 from branch i14), `p3l-empty`, `step-h-mark-total : p3l w -> h-mark (world-step w it)`,
  `p3l-h-mark`. `step-hmk` takes gd, g7, ga, g10r, inv-rank, v14 and rule-r-safe of the input world (all from p3k).
- T2 (`hmk-write-raw-x`): W0 = source-upd, W1 = the fire fold over `edges-onto x`, W2 = the mark fold over
  `mark-targets (dirty-set w x) (edges w)`. The dirty set S is exempt during the mark fold (`hmk-fold-mark-x`); the targets keep
  kind and debtor through the fires (`hk-ek`, edge keys backward incl. marked-monotone, `hk-tg-ek`); discharge
  (`hmk-discharge`) per d in S by `hm-dirty-back`: a ROOT (creditor of an armed dep edge e0 on x) is strong after the fold
  (`hk-root-fold`: until e0's turn e0 survives (`hk-sv-fire-edge`: an edge whose creditor is a computation survives a fire of
  another id); at its turn `hk-root-fire`: an invalidation steps the epoch (gd's dle), a delivery needs a current run of d
  that is alive (ga: acts-alive), so done-epoch /= epoch by gd's cde (`hk-rc-cur`); strong is kept by every later fire and
  mark (`hk-cs-fold`, `hk-cs-mark`)); a CONE member d (dep creditor of m in S) keeps its in-edge on m (not onto x:
  `hk-not-onto`), which is a target, so it is marked after the fold and d is awake (g7) and pending > 0 (`hk-fold-wif`).
  `t2-hmk` takes gd, g7, ga.
- T12 (`hmk-complete-raw-x`, `t12-hmk` with g10r, gd, g7): the result row exempts C (`hmk-comp-upd-x`); gd at that world from
  gd-complete-body's inner step (`hk-gd-result`). `hmk-settle-x`: not ready -> C waiting (`hk-wif-nready`: awake + not
  settle-ready + gd => strong waiting, since a live computation is settle-ready by cde + rof, `hk-wt-nready`); ready ->
  `hk-settle-step` (one pop of d with queue tail L: exemption d :: Cr ++ L, Cr = creditors of d's marked out-edges; every
  unmark has a creditor in Cr (`hk-unm-safe` via `hk-ek` + unique ids); after the pop d has no marked in-edge (l5's sd-fold),
  each c in Cr is queued (ready) or waiting) and `hk-settle-loop` (the queue is the exemption list; `settle-done-ok` empties
  it). General discharge `hmk-dis`: an exempt id leaves when it stays listed, is waiting, or has no marked in-edge (`hk-nmd`).
- Demote (`hmk-demote-x`, `hmk-norm-round`): the round's strays S are exempt; i14's pass bundle `vr S R` (a dep edge on a stray
  has a not-yet-demoted stray creditor) gives the safe creditor of every marked edge dropped by `demote-finish`'s
  `edge-avoids` (`hk-dok-avoid`), and at the pass end (`vr S []`) no dep edge has a stray debtor (`hk-nmd-pass`). Rule R's
  loop with inv-rank and `vr [] []` threaded as in i14 (`hmk-rule-r`).
- Integration: raw0/raw0g/raw copied with gd, g7, ga, g10r premises (`hmk-add-hyps`), `raw-hmk`, `step-hmk`.
- No counterexample: everything proved; the strong form `hmk []` was already tripwired (hmk_test).
- **h-mem2 through the step NOT started** (goal 3 of the branch); `l5-safety-total` therefore still needs h-mem2. Design notes
  (unchanged from branch l5): members of a computation's current parked run are its dep edges (creditor C); an unfilled
  member's debtor y is a source/resource that exists (filter keeps them, I3), a task whose run is alive (a completed task
  fires its wait members), or a computation that is waiting (the T6 fast path fills members on a live debtor; a settle
  delivers to current members (Z#20) before y can be seen live; an invalidation keeps y non-live) with the member edge itself
  as the dep edge. Expect a bundle the size of hmk (every transition; overrides at T6, T9/fires, T12/settle, T14/cascade,
  T10, demote/filter), on top of gd/g7/ga and h-mark (`hmk []`).
- Suite (main merged at 361cca6, hmk2 included): 131 tests / 156,148 assertions, green.

### Branch `hm3` (2026-11-04): the h-mem2 bundle (P11, second half), in progress
- **Bundle `h3 xm`** (spindel.v2.hm3), tripwired clean (hm3_test: random drivers 3 x 12-15 x 80, samples 7-13) =
  inv-sample && per activation A and run row R with id A.run: A.run < next-id, R.of < next-id, R.epoch <= C.epoch for
  every row C with id R.of (E1 on activation runs), and, unless R.of is exempt, when R is current for C (a row with
  C.epoch <= R.epoch): C's rows have done-epoch < epoch (`h3-cs`), every member x of A is exempt by id or names an edge, and
  each edge E with id x is *structural* (`h3-s`: armed; dep -> creditor R.of; otherwise creditor A; A is the first
  activation with member x, i.e. `act-with-member`'s answer) and, unless E's debtor is exempt, *its debtor is fine*
  (`h3-m`: a task debtor's run is alive; a computation debtor is reached by a dep edge and all its rows are hmk's
  strongly waiting `hk-wt`). The exemption list mixes computation ids, debtor ids and member ids (ids are global).
  Why each clause: E1 + "current" by `<=` make every epoch step a frame (obligations only shrink); `armed` and
  "first activation" are what settle's `member-current` and fire-dep's delivery read, so they must hold for an exempt
  (settling) debtor too; `h3-cs` gives the safe creditor when a delivered member edge is removed (final debtor).
- **Proved**: `h3-h-mem2 : h3 [] w -> gd w -> h-mem2 w` (with gd's rof) and `h3-l5-safety` (L5's safety half from p3c,
  gd, h3 [], quiescent, h-mark). So `l5-safety-total` is one step away once `h3 []` is a step invariant (p3m = p3l && h3 []).
- **Proof architecture (done)**: Part B `h3-rest-rel` transfers h3 through any change of computations, tasks, runs, edges
  and the allocator with the activations kept, from per-table conditions (ids below the allocator only: fresh rows are
  frames; a removed or re-phased edge must be `h3-free`: no current non-exempt activation holds it); per-table forms
  (`h3r-cs/ts/rs/es/nid`), activation changes (`h3r-acts`, `h3r-act-del`, `h3r-act-upd` with the first-activation
  lemma `h3-awm-upd`, act ids unique). Primitives: comp/run/task/act/edge updates (`h3-*-upd-m`, row-function side
  conditions: epoch not lowered, hk-wt kept, done<epoch kept, alive runs stay alive, phase armed kept), fresh inserts,
  run-del (no alive row), comp-del, insert-edge, mark/unmark/remove-edge, drop-cred/drop-act/drop-edges (free ids,
  hmk's hk-dok for the resync). Part C: lit's copier bundle `H3` (prefix `hm3-`), source patch `h3-patch2` routing every
  row-function edit that keeps the read keys through the `-m` forms; the others are renamed to `*-NONE` so their users
  fail loudly. Part D: `h3-invalidate` (the creditor's epoch step ends every current holder, which by `h3-s` is a run of
  the creditor; then the phase change is on a free edge), `h3-resume`/`h3-fill-slot` (activation first, then its own
  edges, free by `h3-free-cred`), `h3-rest-xm` (exemption monotone), `h3-undo-x` (a member-id exemption leaves when the
  id is free, no computation and no debtor).
- **Copier status**: `lcopy-try! H3 'raw-inv` copies 87 of the 173 raw0 lemmas; 86 fail, rooted in the overrides below.
- **Remaining (P11, h-mem2), each with its argument**:
  1. fires: `deliver-dep` final debtor (remove-edge of a held member: exempt the member id, fill-slot, undo: the holder was
     the first activation, now without x or gone), `fire-dep` (first holder current -> deliver, else invalidate; a marked
     delivered edge has a safe creditor by `h3-cs`), `fire-wait` (host wait: creditor 0 is no activation -> free),
     `fire-wait-act` (no activation -> free; not current -> unobligated by E1; current -> exempt, fill-slot, undo via
     `h3-s`'s creditor = activation), `fire-edge`, then T9, T18, wake-closed, settle-host, fast-fill, deliver-fire follow.
  2. T2 write (fire fold + mark fold; marks are frames). T7 track-fin (site edge of a running run's computation: no
     current activation of it), T8/T22 unobserve/unawait (observe/host edges are free: creditor 0).
  3. T6 await / take: `act-ins` with E1 (g10r) and R.of < next-id (gl) at the input; `act-set-members`: the new activation
     is the head (first) for its members; a re-awaited site edge is held by no current activation: needs **AR (every
     alive run of a computation is C.run)** + ga (activation runs are parked) — AR is a new invariant, tripwire clean
     (random drivers, samples), not yet proved; fast-fill delivers ready debtors, the rest are demanded computations that
     are not live (hk-wt by gd's dle), tasks without result (alive run, gl), leaves.
  4. cascade: `run-cancel-row` of a task run (task debtor exempt until fire-task-cancelled delivered/invalidated its
     members), cancel-acts, retire (run-del of a done run, task-clear-run).
  5. T12: comp-result-row (debtor exempt), settle loop with the queue as exemption list (hmk2's `hk-settle-*` shape;
     settle's member-current is guaranteed by `h3-s`), complete-task (task exempt through its on-task fires).
  6. reactivation (comp-react-row on an idle computation: no obligation onto it is non-exempt; an idle computation has no
     alive run, g7 a7, so no current activation), T11 (cancel-pred, cut-suffix drops C's suffix: C has no current
     activation by needs-run + AR/E2; consume-entry), T10 finalize (fin-keep keeps members), T13.
  7. Rule R: demote with the strays exempt (hmk2 + i14's `vr`), filter (a retained activation retains its members, their
     debtors and a task's run), detach; release-world (every computation exempt until Rule R has demoted them).
  8. Integration as hmk2: raw0 with gd/g7/ga/g10r/gl (+ AR) premises, `step-h3`, `p3m = p3l && h3 []`, `step-p3m`,
     `p3m-empty`, `l5-safety-total` from `h3-l5-safety`. Then P11 is closed.
- No counterexample: every tripwire of h3 [] (and of AR) is clean.
- Suite (main unchanged at f37264f, hm3 included): 135 tests / 162,102 assertions, green.

### Branch `hm4` (2026-11-04): AR through the step; the h-mem2 fires
- **AR PROVED through the step** (spindel.v2.ar, own bundle `ar`, copier `AR`, prefix ar-): `ar` = inv-sample && every alive
  run R has R.of < next-id and every computation row with id R.of has run = R.id (I10's computation part; `ar-i10-comp` gives
  the literal `inv-i10-comp`). `step-ar : g7 w -> ga w -> ar w -> rule-r-safe raw -> ar (world-step w it)`, `ar-empty`.
  Frames: computation edits keeping (id, run) (`ark`), run edits keeping (id, of, alive) (`arrk`) or by idle's `run-down`
  (cancel/complete/fin-pop-end). Overrides: T13 clear (`ar-clear-comp-run`: the retired run is dead, so by AR + unique run ids
  its computation has no alive run, `ar-none-of-dead`; threaded through retire-with/retire-local/job-apply), parks
  (`ar-park-if`, `ar-take-park` with run-ok-for; T6/take/arm via i8's G8 forms, `ar-from-g8`), new task runs
  (`ar-add-run-scope`: no computation has the task's id), T5 (`ar-startable-none`: done-epoch 0 and not run-busy -> C.run is
  not alive; idle -> g7's a7; C.run = 0 -> run ids are positive), T11 (`ar-cancel-pred-none`: idle's KDB/casc-kill with
  kl0 = [C.run]; acts-alive from ga), demote (`ar-demote-finish` with idle's `demote-dead`), normalize via G7's forms.
  raw0 patched with g7 (T5) and ga (T11).
- **h3 fires PROVED** (spindel.v2.hm4): `h3-fire-edge : h3 xm w -> h3 xm (fire-edge res w x)` for every xm. Mechanism: the
  first activation with member x is the only one that can be obliged to x (`h3-freeb-of`; for a non-dep edge the creditor's
  id: `h3-freeb-cred`); a fill removes x from every row with that id (`h3-free-fill`), so x is free afterwards; a delivery to a
  final debtor / a current wait fire exempts x (`h3-xm-cons`), edits the edge (remove: hk-safe of a current run's computation by
  `h3-cs`, `h3-deliver-safe`; phase: free by the exemption), fills, and undoes the exemption (`h3-undo-fill`: an edge id is no
  computation and no debtor, `h3-edge-not-debtor`). Not current (`run-current` false): E1 makes every holder not obliged
  (`h3-cur-run-current`, `h3-fa-ncur`); no activation / host wait (creditor 0, `h3-act-id-pos`): free.
- Also: T8 unobserve (g7's obs-one: an observe edge's creditor is 0; `t8-unobserve-hm3` takes g7), T22 unawait,
  invalidate-dependents (`h3-inval-fold`: the scanned ids name dep edges, kinds kept). Copies now checked in the suite:
  T2 (write: fire fold + marks are frames), T9, T18, wake-closed, settle-host, fast-fill, deliver-fire.
- **Copier status**: `lcopy-try! H3 'raw-inv` fails 63 (was 86). Remaining roots, in PLAN-hm3 order:
  T7 track-fin (site edge of the running run's computation: needs AR + ga in the bundle context: an activation of C has a
  parked run, C's alive run is C.run = the running run); T6/take/await (`act-ins`, `act-set-members`, needs AR);
  cascade (`run-cancel-row` of a task run kills the debtor's run: task debtor exempt until fire-task-cancelled;
  `cancel-acts`; `task-clear-run`; clear-comp-run); react-one (`comp-react-row`: idle -> awake); T11 (cut-suffix's
  drop-edges with hk-dok, consume-entry's remove-edge); T12 (settle-edge = fire-dep then unmark (hk-safe): the settle queue as
  exemption list, hmk2's `hk-settle-*` shape; complete-body's comp-result-row); T10 (finalize-one/fin-loop/finalize-debtor);
  T13 (retire); revoke-roots, release-world; Rule R (demote/filter/detach). Then raw0 integration with the premises
  (g7, ga, gd, AR, hmk, g10r as needed), `step-h3`, `p3m = p3l && ar && h3 []`, `step-p3m`, `p3m-empty`, `l5-safety-total`.
- No counterexample (the tripwires of h3 [] and AR stay clean).

### Branch `hm5` (2026-11-04): h3 overrides, continued (T7, take/T17, the first cascade pieces)
- **Proved** (spindel.v2.hm5, all kernel-checked, hm5_test):
  - tools: `h3-free-by` (freeness by contradiction from an obliged holder), `h3-ob-has` (an obliged non-exempt member
    names an edge), `h3-free-noedge`, freeness transport (`h3-free-ins-fresh`, `h3-free-edge-upd`, `h3-fa-congr`,
    `h3-fa-run-upd`, `h3-fa-use`); new activations: `h3-g10-run` (g10r: R.of < next-id and E1), `h3-gd-cs` (gd: an alive
    run at C's epoch -> done-epoch < epoch), `h3-r-new`/`h3-r-new2` (the h3-r obligation of a fresh activation),
    `h3r-act-ins` (insertion at the head: the members are exempt or name no edge; generalized transfer `h3-akqg`/
    `h3-r-acts-g`/`h3-a-acts-g`), `h3-undo-g` (undo of an exemption x that is no computation and no debtor, whose
    obliged holders are good for x: the T6/take shape, where `h3-undo-x` needs x free).
  - T7 track (`t7-h3`, premises in-cleanup false, g7, ga, ar, hmk []): the fresh edge is no edge before (free); the
    site edge (dep, creditor C = tracking run's computation) is held by no obliged activation: its run would be
    parked (ga), alive, hence C.run (AR), as is the tracking run (alive by g7's sn), so it would be the tracking run,
    which holds the slice (`h3-t7-free`); unmarked by hmk (`hk-found-noncomp`).
  - take (`h3-take-park`, `t-take-h3`, premises g10r, gd) and T17 arm (`h3-arm-park`, `t17-h3`): the new activation's
    member next-id+1 is exempt from `act-ins` until its wait edge exists (`h3-take-a(-g)`: ab/ao/E1 from g10r, h3-cs
    from gd's cde), then `h3-undo-g` (the new edge is structural for the head activation; every other holder is not
    obliged: the id was no edge, freeness carried by `h3-fa-*`); generic form `h3-take-park-g`.
  - T14 `h3-cancel-acts` (premise-free, renamed in the copier: an activation's own edges go with it, `h3-drop-act-nc`).
  - T10 with **hmk threaded** (a marked edge's debtor is a computation; the finalized debtor is none, so the dropped
    edges are unmarked; they are members of no activation, so free): `h3-finalize-one`, `h3-fin-loop`,
    `h3-finalize-debtor`, `h3-close-source`, `h3-close-local`, `h3-fire-task-cancelled`, `h3-fin-if-final`,
    `t-deliver-h3` (each takes `hmk hx w` for any hx and uses the HMK copies to carry it).
  - T13 `h3-clear-task-run`/`h3-clear-comp-run` (premises: r in runs, r dead; K had no alive run, so no obliged member
    on K; C.run is not read by h3).
- **Copier wiring**: renames `inv-track-fin/raw`, `t7-inv`, `inv-take-park`, `inv-arm-park`, `t-take-inv`, `t17-inv`,
  `inv-cancel-acts`. The overrides with extra premises need raw0's patch (as hmk2's `hmk-add-hyps`), not done:
  `(t7-inv w _ _ _ _ h)` -> `+ hc hg7 hga har hhk`, `(t-take-inv ...)`/`(t17-inv ...)` -> `+ hg10 hgd`, T-deliver ->
  `+ hmk`. The finalize family takes an extra parameter `hx` (hmk's exemption list) and so cannot be a plain rename:
  its callers (cascade, T12, T6 await-post, release) must be overrides that thread `hmk hx`.
- **Remaining roots (exact)**, with what blocks each:
  1. cascade `cancel-run-local`: `run-cancel-row` kills run r; for a task run of K every obliged member edge with debtor
     K breaks (`h3-tk`) until `fire-task-cancelled` has fired the on-task edges. Exempting K needs, at the undo, (a) K
     free as a member id (K is no edge, but freeness must be carried from the start through every edit of the job:
     **freeness monotonicity**, not available as copies; plan: a small copier bundle `hf [xm x]` = inv-sample &&
     h3-free xm w x, whose primitives are all frames or monotone except act-ins/run-ins/comp-ins (absent in the
     cascade), copied over `inv-run-cascade`'s closure), (b) no obliged member edge left with debtor K (each fired
     on-task edge is free right after its fire — hm4's fire proofs show it internally, to be exported — and stays free
     by (a)'s bundle; observe/savepoint edges on K need g7's obs-one / a savepoint fact), (c) other tasks whose
     run pointer is r.id: needs gl's trun/thas (premise-free GL copies exist) or g10's tof-pair. Then `cancel-debtor`,
     `debtor-side`, `job-apply`, `cascade`, `run-cascade` as hmk-threaded overrides (HMK copies `hmk-job-apply`,
     `hmk-cascade` are premise-free).
  2. T13 `retire-with`: `run-del` needs the run row dead after `close-local` (fires can resume a parked run: needs
     aha/acts-alive threaded, premise-free AHA copies exist), plus `remove-if-empty`/cleanup (frames).
  3. reactivation `react-one` (`comp-react-row`: idle -> awake, done-epoch := epoch): `h3r-comp-upd`/`h3-rest-rel`
     require h3-cs transfer for every k2 (fails for k2.of = C). Plan: a variant `h3-rest-rel-x` whose hc5 (and ht)
     are only required for ids not in xm (the proof uses them only there), then exempt C, react, undo C with: no
     activation run of C (g7's a7 + aha: activation runs alive, C idle), C free (no edge id), no obliged member on C
     (C idle, so before the step every such edge was debtor-exempt). G7/AHA react copies are premise-free.
  4. T6 await: `await-pre` (act-ins with no members: `h3r-act-ins` + `h3-r-new2`; then the demand fold = 3),
     `await-post` (`act-set-members` on the head activation: every member edge structural, the first activation is
     the head; fast-fill fires; the rest as PLAN-hm3 item 3: demanded computations not live are hk-wt by gd's dle,
     tasks without result have an alive run by gl, leaves), `park-if`, `fin-if-final` (done, with hmk).
  5. T11 `cut-suffix` (drop-edges with hk-dok, hmk) / `consume-entry`, `cancel-pred` (= 1).
  6. T12 `settle-edge` (fire-dep then unmark: hk-safe of the creditor; settle queue as exemption list, hmk2's
     `hk-settle-*` shape; `h3-fire-dep` exists), `complete-body` (comp-result-row: done-epoch := epoch with the
     computation exempt until its settle), `complete-raw`.
  7. T16 close-scope, slice-exit, cancel-losers, T15: all via `run-cascade` (= 1).
  8. release-world (`revoke-roots` drops every non-host edge: every computation exempt until Rule R's demote/filter
     removes their activations), Rule R demote/filter/detach.
  9. Integration: raw0 patch with premises g7, ga, gd, g10r, ar, hmk []; `step-h3`, `p3m = p3l && ar && h3 []`,
     `step-p3m`, `p3m-empty`, `l5-safety-total`.
- No counterexample found (every override so far went through with invariants already proved).
- Suite (main merged, up to date at eb05b78; hm5 included): 138 tests / 162,224 assertions, green.

### `hm14` (2026-11-13): T11 dispatch keeps h3 through `raw`
- **Proved** (spindel.v2.hm14, statements = notes/hm14-contracts.edn, test hm14_test): `h14-dispatch-raw-h3`,
  `h14-t11-outcome`, `h14-raw0g-dispatch-outcome`, `h14-raw-dispatch-accepted`, `h14-raw-dispatch-outcome`
  (p3la w, h3 xm w -> h3 xm at `raw w (dispatch-comp c fresh)`; a refusal is the input world).
- Argument: after `cancel-pred` no activation holds a run of C (`ar-cancel-pred-none` + acts-alive), so every dep
  edge of C is free (`h14-free-dep-no-holder`: a member dep edge's creditor is the run's `of`, h3-s); the cut drops
  only such edges (`hk-dok-cut`), the entry edge is gone or still a dep edge of C (bundle `kc`: an edge id keeps
  kind and creditor, copied through cancel-pred and the cut like p3's `kx`), so its removal on a final debtor is
  free; the re-arm keeps keys and armedness; the new run and scope are fresh rows, `comp-set-run` keeps epoch,
  pending and waiting.
- **Deviation from the contracts**: the three edge-predicate helpers (job-apply, cascade, cancel-pred keys) are
  replaced by the `kc` bundle; the other 16 statements are literal.
- **Remaining for h-mem2 through the step**: items 6 (T12), 8 (release-world, Rule R) and 9 (integration) above.

### `hm15` (2026-11-13): raw lifts, T22 host await, T8 observe
- **Proved** (spindel.v2.hm15): `h15-raw0g-lift` (h3 at raw0's world -> at raw0g's), `h15-raw-lift` (p3la w, h3 at
  raw0g's world -> at raw's, via `h13-raw0g-support` + `h13-post-h3`): the assembly over all items is now one case per
  item at `raw0`. `h15-host-await-raw-h3`, `h15-raw0-host-await-h3` (T22), `h15-t8-full-h3` (T8): the fresh edge
  (`hm3-insert-edge-checked`, `insert-edge-fresh-h3`), the demand (`h3-demand-reactive` with g7 and aha of the world
  after the insert), the fire (`h3-fire-edge`).
- **Remaining**: T12 (complete-comp/-task, settle with the queue as exemption list, retire-after, the cascade,
  fin-if-final), release-world (`revoke-roots`), `raw0-h3` by cases, then Rule R (`finish`).

### `hm16` (2026-11-13, in progress): T12 complete + settle for h3
- **Proved**: `h16-undo-c` (undo of a COMPUTATION's exemption x: no activation holds a run of x, x free as a member
  id, every edge on x unarmed / host / h3-m): hm6's `h3-undo-d` with the no-holder premise in place of "x is no
  computation". The no-holder premise comes from acts-alive + "no alive run of x" (hm14's `h14-acts-alive-no-holder`).
- **Design for the rest** (hmk2 Part E is the template; an id in xm exempts three roles: `of` of a run, member id,
  debtor of a member edge):
  1. `complete-raw`: exempt `(:of r)`, then `h3-run-kill` for `run-upd r run-complete-row` (its premise: every task
     with run r is exempt), complete-body, `hm3-retire-after`, `h3-run-cascade-g` (needs g10, hmk, ekb of that world:
     the hmk/gd/g7 copies of complete-body exist), `h3-fin-if-final`.
  2. task case: `task-upd` result row, `cancel-res`, the fold of `h3-fire-edge` over the edges on the task; then the
     task's exemption is undone by `h3-undo-d` (every edge on it is fired, so unarmed).
  3. comp case C: `comp-upd` result row with C exempt (done-epoch := epoch breaks h3-cs for C's holders and hk-wif
     for member edges on C), `cancel-res`, then settle: settle-edge = settle-fire (`h3-fire-dep`) + `h3-unmark-edge`
     (premise hk-safe of the creditor: exempt the creditors of the marked out-edges, as hmk2's `hk-se-fold`).
     Discharge per id y of the list: still queued (ready), or not ready: then y has no holder (completed, ar: no
     alive run) and is waiting (hk-wif, pending /= 0), so `h16-undo-c`. For C itself: no holder, and after
     settle-one no armed member-current edge has debtor C (each was fired by `member-current`): `h16-undo-c` needs
     its edge premise restricted to contrib members of obligated activations (generalize the premise as in
     `h3-undo-g`), plus a fold invariant "a processed out-dep edge of C is not (armed and member-current)".
  4. the loop: the queue is the exemption list (hk-settle-loop's shape, `settle-done-ok` empties it).
- **hm16 status (2026-11-13, later)**: proved (34 forms, REPL): `h16-complete-task-x` (task half), `h16-free-fire-dep`,
  `h16-free-nmc`, the frame `h16-fm-settle-*`, `h16-se-fold` (fold over out-dep edges: h3 under Lst and every processed
  edge id FREE; a delivered dep edge is re-armed, so "free" replaces "unarmed"), `h16-nh` (no current holder) with
  `-fm`/`-done`, `h16-free-mono/-drop`, `h16-undo2` (generalized undo), `h16-dis` (list discharge).
- **Remaining for the comp half** (design fixed):
  1. `h16-J xm B W` bundle, B = comps at the settle start: (a) strong_B c => strong_W c; (b) not-strong_B c => nh W c;
     (c) comp y at W => h3-free xm W y; (d) every edge at W is dep, or its debtor no comp / in xm, or its id free under
     xm; (e) comp-has equal to B. Stable under settle-one (fm, hk-ek back relation, hk-cs closure). Init: (c),(d) at
     the pre-world from h3 xm, moved by fm; (b) by `h16-nh-done` (acts-alive from ga + `ga-run-upd-free`).
  2. `h16-settle-step`: h3 (d :: Lq) W -> h3 (next ++ Lq) (settle-one W d ch), Lst = (d :: NS) ++ Lq with NS = the
     creditors of marked out-edges not strong at W (never exempt a strong = running creditor: its holders' member
     facts would be lost). Discharge by `h16-dis`: d via free edge ids (`h16-free-drop`), a not-ready creditor via
     `hk-wif-nready`; queue elements need only "not strong at B".
  3. loop (`hk-settle-loop` shape), `settle`, complete-body comp case (result row with C exempt via comp-upd lemma),
     `complete-raw` wrapper (`h3-run-kill`, `hm3-retire-after`, `h3-run-cascade-g`, `h3-fin-if-final`), `t12`.
- **hm16 done (2026-11-13)**: `h16-t12-h3` — T12 complete keeps h3 (premises: `res-tag-ok tag`, g10r, g10, ga, gd, g7,
  hmk, ekb of the input world). Path: `h16-J` bundle + `h16-settle-step` / `-loop` / `h16-settle-x`,
  `h16-complete-comp-x`, `h16-complete-pre` (cases: no owner row / task / stale computation / current computation),
  `h16-g10-body` (g10 at the complete-body world, from i10's cmp-* cases), `h16-complete-raw-x`.
  Note for the assembly: T12's h3 needs `res-tag-ok` (as `gl`'s T12 in lit.clj): the `raw` case must take it from
  the step guard `complete-refused`.
- **Left for h-mem2 through the step**: release-world (`inv-revoke-roots`, `t-release-world-inv`), then the
  assembly `raw0-h3` over the 38 items, Rule R, `p3m`, `l5-safety-total`.
- **hm17 done (2026-11-13)**: release-world (`h17-host-free`: a host edge's id is free; `h17-revoke-roots`,
  `h17-t-release-world`) and the assembly `h17-raw0-h3` / `h17-raw-h3`: `p3la w -> h3 xm w -> h3 xm (raw w it)` over all
  38 items (19 plain items lift with the H3 copier unaided).
- **Rule R for h3 (hm18, not started)**. Copier probe (`lcopy-try! H3`): everything fails only through three roots:
  1. `inv-finalize-one` (-> fin-loop, finalize-debtor, detach-source, detach): needs an h3 lemma for finalize-one.
  2. `inv-demote-finish` / `inv-demote`: follow hmk-demote-x: exempt the stray set S during the fold
     (`h3 (S ++ xm)`), cascade by `h3-run-cascade-g`, demote-epoch by a comp-upd lemma with epoch <=, drop of the dep
     edges of x (creditor x in S: ids free, `hk-dok` from hmk), comp-del-unref / make-idle; discharge at the pass end
     with `h16-dis`: no-holder `h16-nh` of x from the epoch step (held runs have epoch <= the old epoch, `h3-e1`) or,
     when demote-cur is false, from i10's `ncq` lemma (i10.clj ~3087: no current run of c); freeness of x and the
     per-edge condition as in hm16.
  3. `inv-filter-world` (Rule R's filter): an `h3-filter-world` from `filter-safe` (precedent `hmk-filter-world`).
  Then `h3-rr-loop` / `h3-rule-r` (inv-rank and `vr [] []` threaded as in hmk2), `step-h3`, `p3m`, `l5-safety-total`.
