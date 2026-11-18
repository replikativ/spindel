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
| `spindel.v2.qworld` | C1 quiet half: bundle `gc` (every cleanup entry's run is a run row; `step-gc-rest`), `qinv` = p3l && K && gc && I3 (`step-qinv`, `qinv-empty`), the closure lemma `quiet-rows` (a quiet world with qinv holds only scopes), the refusal lemma `quiet-refused`, `quiet-step`, `quiet-stays` | done |
| `spindel.v2.ledger` | C1c stage A (Z#70): derived completion ledger, `task-held`, `task-complete` (not held and no run scope row k + 2), `scope-complete` (no row); layer-2 host joins in sys.clj (`Cell.joins` of `Join` records, `sys-join`, `sys-deliver`, `sys-withdraw`, `complete-cell` delivers the rest) | done (theorems in lstab, oscope, qworld, sys) |
| `spindel.v2.lstab` | C1c stage A proof stage, stability: parametric bundle `gst k s` (k below the allocator and task k not held, s below the allocator and no scope row s), copied over raw/normalize with T12/T13/T14 task-row overrides; `step-gst`, `task-complete-stable`, `scope-complete-stable` | done |
| `spindel.v2.oscope` | C1c stage A proof stage (questions 10, 14): bundle `gos` (every open non-root scope has a run row whose run scope is it or on its parent chain), copied with overrides at run creation, open-scope (`cur-scope` cases), detach, Z#18 deletion (`parent-outside`), T13 (subtree convergence `sub-conv`, completeness `sub-within`, witness bundle `gox x` over the source closes) and Rule R (`run-kept`, kept parents); `step-gos`, `gos-empty` | done |
| `spindel.v2.owned` | C1c stage B (Z#71, v4 L2): owned forks as layer-1 world operations. The count W-OWNED-N is the fork markers (`ForkRow`: id = the child world's id, owner = the forking run's current scope; one per counted child), the inherited markers of a fork are its W-NORMALIZE (`Cell.norm` in sys.clj); `own-world` (+1, counting branch `own-ok`), `owned-done-world` (`[:owned-done s child]`), `drain-world` (`[:normalize]`), `no-markers` (completion); retention: retain.clj `fork-keep` (a marker keeps itself and its owner's ancestor chain, storage) | model (theorems: proof stage) |
| `spindel.v2.tomb` | C1 Q6: tombstones are dormant. Bundle `gy y` (copy of the raw step and of normalization): every alive run's computation and every dep edge's creditor is no tombstone (`ta-one`, `dep-untomb`), nor is computation y; `gy 0` is in P3's round invariant `ri` (`refs-untomb`, the new premise of `filter-safe-of-refs`); `trc` (acts-alive && gy 0) is the round context the i10/i14/hmk2/hm18 normalization chains take; `step-gy`, `gy-empty` | done |
| `spindel.v2.acyc` | Z#69: scope parents are acyclic. Bundle `gcy` = inv-sample && `gcy-rest` (every scope's parent below the allocator, `cy-par-below`; no scope on its own `scope-ancestors`, `scopes-acyclic`, equivalently no `Reach (scope-up w) (scope-up w y) y`); generic graph lemmas (sub-graph, fresh node, re-parenting outside the subtree); copy as i1's G1 with overrides at run creation, open-scope and detach; `step-gcy`, `step-acyc` / `acyc-empty` (from p3b), `step-acyclic`, `step-acyclic-reach` | done |
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
| `spindel.v2.mvcc` | layer 2 physical, MVCC representation (engine #260): rows with stamps and versions, tokens and cells, lineage resolution, barrier, pruning, token end; refinement against the value-copy model (`mv-refinement`, `mv-no-missing-version`) and the row-monitor interleaving (`mi-protocol`); see notes/LAYER2.md §9 | done (2026-11-15) |
| `spindel.v2.oracle` (test) | lockstep driver against the engine commit log (table + legacy formats, re-sync, quiesce, implicit `slice-exit`, refused items without projection, triage in `oracle_test`) | done (every sample of the replay set without divergence or triage list; 1 regenerated by spindel #271, 4-5 by #270; 2 and 3 retired to adapter fixtures, 2026-11-16) |

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
- **hm18 design (2026-11-13; detach done: `h18-detach`)**. Rule R is where h-mem2 needs liveness, not only frames:
  - demote x (x in the round's stray set S, exempt): cascade (`h3-run-cascade-g`), epoch step and make-idle by
    `h16-comp-upd-x`, drop of x's dep edges: free because the creditor is exempt (a current member dep edge has
    creditor = of k). Delete branch (`edge-avoids x`): creditor-x edges as before (non-dep: creditor would be an act
    id); debtor-x dep edges have a stray creditor (vr's dnb14), free; **debtor-x non-dep edges (waits, observes) need
    a new fact NW(S, W)**: no activation has a member non-dep edge whose debtor is in S. At the pass start (after the
    stray-run cascade): the holder's run is alive (acts-alive), a stray run was cancelled (cancel-acts removed the
    activation; needs "a cancel cascade leaves the listed runs dead", idle.clj's casc-kill is the per-computation
    precedent), a live run makes act -> member edge -> debtor live (retain-succ: run-contrib, act-contrib,
    edge-contrib; closure as in `vr-pass-start` / i1's `live-parent`), contradicting stray. NW is kept along the fold
    by frames (acts only removed, edges keep id/kind/debtor).
  - discharge of S at the pass end by `h16-dis`: `h16-nh` (epoch step + `h3-e1`, or i10's ncq when demote-cur is
    false, or no row), freeness of x, per-edge condition.
  - filter at the normalized world: a kept current activation's member edges and their debtors are kept (closure of
    the live list; check what keeps an activation besides liveness: cleanup-rows / storage).
  - **Refinement (same day)** after reading the code: the exemption by debtor hides `h3-m` for edges on a stray x, so
    the freeness of the non-dep edges on x must be taken at the pass start (list [], `h3-m`: a current member edge on a
    computation is a dep edge) and carried. No frame through the cascade exists as a lemma (`h3-run-cascade-g` is a
    copier lift), but `h3-fm w (op w)` exists for nearly every primitive (hm6: fm-run-upd, -act-del, -comp-upd,
    -edge-upd, -remove-edge, -drop-act, -drop-edges, -cancel-mid, -same, ...). Plan:
    R1. copier bundle `fb L F S w` = inv-sample, every id of F is `h3-free L w`, every edge is dep or has its debtor
        outside S or its id in F (F = ids of the non-dep edges on S at the pass start); prims from the fm lemmas;
        lift inv-run-cascade / inv-demote. (Only tasks' activations hold such edges: await-edge's as-dep.)
    R2. no holder at the pass end: per demoted d "no alive run of d" (idle.clj: after demote's cancel cascade
        `not-alive-of`, line ~1834; the KDB bundle `kdb d kl kd` lifts through cascades) carried to the end, then
        acts-alive gives `h16-nh`; check the no-row / idle-at-its-turn cases (g7's a7-one for idle).
    R3. `h18-demote-x` with L = S: cascade, epoch step and make-idle by `h16-comp-upd-x` + `h16-dis` (x already in
        L), dep-edge drop (creditor exempt; `hk-dok-own`), delete branch (`hk-dok-avoid`; debtor-x dep: creditor in R
        by vr; debtor-x non-dep: fb; creditor-x non-dep: an act id is no computation id), `h3r-comp-del`.
    R4. fold, discharge (`h16-dis`), norm-round, norm-loop, normalize. R5. filter. R6. rr-loop, rule-r, step, p3m.

### hm18 done (2026-11-13): Rule R keeps h3; P11 closed

- Pass: `h18-nh-demote` (after its demote no activation holds a current run of x), `h18-demote-fold` (accumulator
  `h18-acc` collects the demoted strays in the bundle's zd), `h18-fb-init` (F = the strays plus the ids of the non-dep edges
  on a stray; free at a world with `h3 []` by `h3-m`), `h18-pass-end` (`h16-dis` with L = nil), `h18-norm-round`,
  `h18-norm-loop`, `h18-normalize`. The carried freeness is at the empty list (`h18-free-nil` weakens it where needed).
- Filter: `h18-filter-k` for a generic K under two premises (K keeps every run; K keeps the member edges of an activation
  whose run row exists) and `h18-filter` for `keep-fn` at a normalized world (`run-kept` from gr0; the member edges are live
  through run -> activation -> member edge). `h18-awm-keep`: the first activation with a member survives the filter.
- `h18-rule-r-round`, `h18-rr-loop`, `h18-rule-r` (threaded: inv-rank, vr [] [], hmk [], g10 [] [], ekb, acts-alive, g7, gr0).
- **`step-h3`**, `p3m = p3la && h3 []`, `step-p3m`, `p3m-empty`, `step-h3-total`, and
  **`l5-safety-total : p3m w -> quiescent w -> ... -> False`** with no honest hypothesis (h-mark and h-mem2 are invariants).
- Open after P11: I15 as a literal statement over `p3m`, random lockstep in CI, the formal CI job, spec §8 rows.

### Branch `formal/c0-model` (2026-11-15): C0 async sequences, Stage A (engine 60f6a62)

- Links and streams are source kinds of the ONE model (`sk-link 6`, `sk-stream 7`; `sk-rerun 5` stays, never
  created). `SourceRow` gains `rtask next tail fail` (state.clj docstring: a link is realized iff version > 0 with
  state v / next N, the end (next 0), or `fail` (memoized error, `src-result` = err state); `tail` = a push link's
  stream (0 = pull link) or a stream's tail link). Row functions + id lemmas at the end of edits.clj.
- Items 38-43 (step.clj table): `create-link st l` / `create-link-top scope l` (pull head in the root scope; in a
  computation a basis creation adopted like a re-spawn), `link-demand l k` (realizer task k in the root scope with
  handles 0, run, run scope = T4's rows; `rtask` is stale-tolerant: `realizer-live` = task exists without result),
  `link-realize l tag v n` (1 next pull link n / 0 end / 2 error), `append x v t`, `close x tag v`. Streams are T1's
  kind 7 (`t1-body`, `t1-top-full`: stream S and its first tail link S + 1). All built from source-ins, source-upd and
  rule.clj's `realize-link` = `deliver-res` (deliver with a result: `deliver-raw-res`, rfl).
- Changed: `close-source` = `close-source0 (end-stream w x) x` (T16/T13/T21/Rule R: a stream's tail ends first);
  `demote-edges` closes the streams of C's basis after C's dep edges go (`end-basis`, engine `demote!`); links are
  deferred-like (`once-kind` in `src-valueless`/`src-delivered`); `src-consuming` refuses await/T22 on a stream.
  No existing theorem statement changed; the sl-/s9- chains, casc (`ri-*`, `bn-end-basis`, `demote-lt`) and the copiers
  (bc, ga/gx) cover the new items.
- Oracle: projection `:rtask` (raw; none when that task exists with a result: the engine clears it at a cancel with no
  item), `:pull` (tail 0 and unrealized, or a computation's head), `:next`, stream `:tail`/`:state nil`; deviation
  `:link-state` (the engine interns [v next-handle]). Samples 18-21 replay with no divergence (oracle_test
  `sample-18` .. `sample-21`, `projection-roundtrip-c0`); engine_test `random-steps-c0` (C0 items mixed in, all
  per-step tripwires).
- Stage B: see the next section (every namespace loads).

### Stage B (2026-11-16): model changes settled with the engine session

- **rtask at cancel** (T14/T21): `debtor-side` of a task run ends with `clear-rtasks w k` (rule.clj: every link whose
  `rtask` is k gets `link-set-rtask 0`), the engine's cancel! -> finish-task! -> link-cancelled!. The oracle's
  `:rtask` projection is now the raw field (the "none once the task has a result" case is gone; samples 1-21 at 0
  divergences). `realizer-live` keeps its task check (harmless).
- **T8 observe on a stream** is refused (`t8-obs` in engine.clj, raw0's observe arm), as await/T22 (`src-consuming`).
- engine_test `c0-realizer-cancel-and-stream-observe` checks both.

### Stage B (2026-11-16): every bundle outside the core loads under C0

- **All namespaces load** (lit .. hm18, skip, sys, z59, cow, mvcc), kernel-checked, no `sorry`, no statement weakened
  (the temporary hypothesis `c0-root` of the first pass is discharged by the root gate, below).
- Repair pattern: one lemma per bundle and C0 primitive, reused by the copiers: the frames `kw`/`kw8`/`res`/`hk-has`
  for `deliver-res`, `end-link`, `end-stream`, `close-source0`, `clear-rtasks`; overrides where a bundle reads the
  realized row (`g5-deliver-res`, `g5-append-raw` with the guard's stream row, `svb` with `stream-set-tail-hv`, `gso`
  fresh links owned, `hmk-deliver-res`/`hmk-realize-link`/`hmk-close-raw` and the `h3-` analogues with the realized
  link / closed stream a source, i.e. no computation). Demote's `end-basis`: `kdb-end-basis` (no run of C revives:
  `end-basis-dead`), the bundle `edb` (no dep edge of C appears: `end-basis-no-dep`), `wdom-end-basis` (i14: comps keep
  id/idle/rank/validity, edges keep kind/creditor/debtor, the allocator stays), so `vr-demote-tail`, `hmk-demote-x`,
  `h18-demote-x`, `g7-demote`, `gr0-demote-aa`, `ar-demote`, `demote-tail` (i10) carry their facts across it.
- Model refactor (same worlds): `append-raw` updates the stream row before inserting the new tail link (the rows are
  independent), so a bundle can use the guard's row of the stream.
- Layer 2 (L12, spec §4.3 Links and forks): `diff` in sys.clj leaves links out of a mergeable fork's basis (`not-link`);
  a stream the fork appended to stays in, so that merge is refused (stream merge: C2). sys_test
  `c0-merge-links-out-streams-in`.

#### Root gate (branch `formal/c0-guard`, 2026-11-16): `c0-root` is no hypothesis any more

The first Stage B pass carried a temporary hypothesis `c0-root w it` (an item that creates a link owned by the root
scope runs while the root scope is open) on step-g8, step-p3i, step-lit-i8-total, step-p3j, step-gd-facts-total,
step-p3k, step-i14-total, step-p3l, step-h-mark-total, step-p3la, step-p3m, step-h3-total, step-h-mem2-total and
sinv-step; g8 (literal I8) needs it. The engine session (feat/v2-world-completion) made it a rule: every root-owned link
creation is refused once the root scope is closed (append logs `[:append s v 0]` accepted false, a cancelled
finalizer's corner after release, Z#56; link-realize logs nothing; the others are refused for a cancelled run or a
released host); and link-done! realizes nothing at all once the root scope is closed (every tag, no item). Model:
raw0 wraps `create-source(-top)` with kind `sk-stream`, `create-link`, `create-link-top`, `link-realize` (every tag:
the end and an error realize nothing either) and `append` in `c0-gate w b o = if (root-ok-if b w) o (refuse w)` (engine.clj, before
Part G; `root-ok-if b w = !b || scope-open-at w root-scope-id`), with `c0-gate-inv`/`-refuse`/`-l4`, `i10-gate`,
`s9-gate`; engine_test `c0-root-gate` (append, create-link-top and link-realize tags 0/1/2 refused with the world
unchanged under a closed root scope, accepted under an open one); samples 1-21 replay with no divergence. The proofs
take the gate locally: g8's transition overrides take `root-ok-if` (link-realize's through `root-ok-any`),
`c0-gate-g8` gives it to them in raw0's copy (a refused item keeps the world),
h3's raw0 assembly (hm17) wraps the gated arms in `c0-gate-h3`. Every theorem listed above has its original
statement again.

#### Former temporary hypothesis `c0-root w it` (first pass, superseded)

`c0-root w it = !(c0-root-item it) || scope-open-at w root-scope-id` was defined in i8.clj and threaded through the
theorems listed above (commits ad4a953 .. f0ee12c on `formal/c0-model`); the root gate removed it and its definition.

## C1 (2026-11-16): world-level completion, cancellation, synchronous finalizers, await-op

Engine 823771c / engine-v2 d3b22f1 (spec Z#67, T14, T21, B8 reduced, §4.3 await-op/idle?; c1-cancellation-joins-design.md).
Branch `formal/c1-model`. Stage A (model, oracle, tests) and Stage B (downstream bundles, layer-2 completion) done;
Stage B found one false obligation (completion stability, below). A4/A5 wait for spindel PR #268.

### Mapping of the C1 rules onto the model

| C1 rule | level | model |
|---|---|---|
| `runs` (+1 at run creation, -1 at T13) | layer 1, derived | the run rows: `world-runs w = length (:runs w)` (engine.clj). Rule R's filter keeps every run (gr0 `run-kept`), so rows = unretired runs. No counter. |
| `kids`, child token, acceptance (own-child!, host fork!, activate!), "whichever of acceptance and completion comes second acknowledges", "a complete owner takes no new obligation" | layer 2 | `Cell.kids` (accepted children, never inherited) and `sys-accept` (a complete owner takes none). The exactly-once token is the engine's bookkeeping of the same relation: a child counts while it is accepted, live and not complete (`kid-done`); a child complete before its acceptance is done at once. Acceptance is its own operation (also for the fork effect: `sys-fork-effect` keeps its frame theorems). |
| completion (released, runs = 0, kids = 0), latched | layer 2 | `Cell.complete`, set by `sys-complete` when `complete-ready` (released and: unborn, or no run and every kid done). Internal: no item (the engine logs none). Layer 1 has the local part `world-quiet`. |
| host terminal subscriptions (on-complete), survive T21 | host | out of scope: callbacks after the gate; they observe the latch and change no row. |
| fork/instance copy runs; kids/subscriptions/token start empty | layer 2 | a fork cell copies the world (so its run rows) with `kids []`, `complete false`. |
| R1: inherited non-armed resources (cancelling, fired unacknowledged) acknowledged at the child's first turn | layer 2 | `fork-cell`/`fork-effect-cell`/`inst-cell` inherit every outstanding resource (`res-ids`); `wake-one` keeps only an armed timer and settles the rest (armed: fire ::forked + ack; non-armed: ack, its fire refused). |
| E4: an unborn instance released before activation is complete at once | layer 1 + 2 | `release-unborn w` (engine.clj: the flag only, nothing in it runs), `sys-release-unborn`, `sys-complete` (unborn). A later activation is refused (`act-ok` requires an unreleased world; sample 24). |
| T14/Q10: cancel the whole run-scope subtree at request time, release the subtree's worlds | layer 1 + 2 | the model already cancelled `owned-runs` of `scope-subtree` in the cancel's cascade (T14 job-next, T12's Q10, T16); no change. Releasing the owned worlds is the child's own `[:release-world]` through its ingress (layer 2: a `sys-step` of the child), as the engine (`release-child!`). |
| tombstones: a done task leaves its owner scope once its run retired (Z#56, `release-ownership!`) | layer 1 | `subtree-empty` ignores a done task with no run (`task-held-in`): sample 22 closes scopes whose tasks the request-time cancel already retired. Was latent before C1. |
| B8 reduced: suspending effects in a finally clause fail with ::invalid :finalizer; every await/take refused in a cancelled run's finally clause; custom effects refused in finally | layer 1 | the refused effect is never an item (it fails before any commit; samples 25, 25b). Modelled: in a cancelled run's cleanup slice (`in-cleanup`) T6 (`await-bad`) and take are refused. Not modelled: the normal-run clause (the engine logs no item for the clause's end, `leave-finalizer!`, so the model cannot track it; such items never appear). |
| await-op (resource kind :op): start/cancel arbitration, hooks, ack when start returned ∧ hooks done ∧ settled, :detach | layer 1 | `rk-op 4`, armable (`arm-kind-ok`); arbitration, hooks and the ack condition are the engine's physical side: the log shows arm, fire (the result) and the ack (T15), which the model already admits in any phase without an edge on Z. |
| a fired, unacknowledged op is still cancellable, also on a done run | layer 1 | `t-cancel` on a done, unretired task run holding no slice (`host-cancel-done`) is `cancel-done`: T14 is idempotent on the run and R4 reaches its run scope's subtree at once, so the cascade cancels the alive runs owned in that subtree (none unless work was detached into a scope the done run still holds). Engine `cancel-task!` commits `[:cancel r]` (A2). |
| link guards (append/link-realize/... under a closed root) | layer 1 | c0-guard's `c0-gate`, unchanged. |
| idle? | host | out of scope (a snapshot of queues the model does not have: runnable work, cleanup queue, ingress). |

### Oracle (Stage A)
- res kind `:op`; `replay-family` (root, host fork, fork effect, instance; `:from`/`:owner` separate, sample 23a) and
  `check-observations`: per sidecar checkpoint and world, the model's `runs` = W-RUNS, `released?`, derived `complete?`
  (released and: unborn, or no run and every owned child complete), and the engine's `kids` at most the model's open
  children; tokens are not compared (bookkeeping). `:unborn?` replays E4.
- `kids` compared exactly (A3): accepted children not complete and not collected, at every sidecar checkpoint.
  Acceptance is at creation (fork effect, host fork), at activation (instance), and for a host fork into a busy owner
  at the owner's queued internal item (family spec `:accepted-from`, sample 23a's `:owner-free`).
- A run scope that owns nothing (no task, no source owner, no child scope) reads as closed (A1: never materialized
  means nothing to close); the former `:lazy-run-scope` deviation is dropped.
- Deviation: `:released-proj` (the engine's verify projection, test/org/replikativ/spindel/v2/verify.clj, hard-codes
  `:released false` after the release commit; the sidecar has `:released? true`). Dropped when PR #268 merges (A4).
- Samples 22-27: every world replays with 0 divergences and every checkpoint of every sidecar matches; samples 1-21
  unchanged (0 divergences, triaged lists as before).

### Changed statements
None: every theorem statement of the core is unchanged (definitions changed: `raw0` await/take arms, `t-cancel`,
`subtree-empty`, `arm-kind-ok`, `res-kind-ok`; layer 2 `Cell`, `wake-one`, `fork-cell`/`fork-effect-cell`/`inst-cell`,
`act-ok`). New: `await-bad`, `host-cancel-done`, `cancel-done`, `task-held-in`, `release-unborn` (+`inv-release-unborn`),
`world-runs`, `world-quiet`, `rk-op`; sys `res-ids`, `timer-kept`, `accept-cell`, `sys-accept`, `kid-done`,
`complete-ready`, `complete-cell`, `sys-complete`, `release-unborn-cell`, `sys-release-unborn`, `sinv-accept`,
`sinv-complete`, `complete-latch`; Stage B: `p3l-release-unborn`, `sinv-release-unborn`, `wq`, `cinv` and its
lemmas (below). Test-side: sys_test's unarmable kind is `rk-native` (op is armable now).

### Loads / breaks (Stage A)
Core (state .. acts, rank, rank-step) load; lit .. hm11, skip, z59, cow, sys, mvcc load unchanged. Break: hm12
(`await-kind-bad` -> `await-bad` in `h12-raw0-await-outcome`, mechanical), hm17 (h3's raw0 assembly: the await arm's
guard and the take arm's cleanup refusal), hm18 (blocked by hm17).

### Stage B results
- hm12, hm17, hm18 repaired (mechanical: `await-bad` in the await arm, the take arm's cleanup refusal); the done-run
  cancel (A2) needed the subtree cascade in i10 (`t-cancel-g10`), i8 (`t-cancel-g8`) and hm6 (`t-cancel-h3`). Every
  namespace loads; no statement changed.
- `sinv-release-unborn`: `p3l (release-unborn w) = p3l w` holds definitionally (`p3l-release-unborn`, `rfl`): no bundle
  of `p3l` reads `released`. No per-bundle copies needed.
- Completion soundness `cinv cells`: every live complete cell is `complete-ready` (released and: unborn, or no run and
  every accepted child complete or collected). `cinv-none` (no complete cell); kept outright by `sys-accept`,
  `sys-complete`, `sys-release-unborn`, `sys-activate` (a complete cell is released, so neither touches one),
  `sys-drop`, `sys-idle-release`; by `sys-fork`, `sys-fork-effect`, `sys-instantiate` for an id no cell has accepted
  (`forall j, tbl-all (nat-ne m) (:kids (cells j))`); by `sys-step`, `sys-wake`, `sys-resume`, `sys-merge`,
  `sys-publish`, `sys-abandon` under the premise `hq`:
  `forall w it, p3l w -> wq w (:world (world-step w it))`, `wq w w2` = released stays released and `world-quiet`
  stays quiet. `complete-latch` (earlier) is the latch.
- **Finding: `hq`'s quiet half is false in the current model**, so completion stability is NOT proved. Sequence
  (layer 1, from the empty world): create-comp-top c, observe c, start c (run r), schedule r, release-world (T21: r cancelled,
  mode unwinding, still holding the slice), `observe c` (or `pin c`) ACCEPTED (host-shut exempts a held slice), slice-exit
  r: released, 0 runs (`world-quiet`), c observed/pinned and startable; `start c` accepted: a run in a quiet world. A
  cell completed at the quiet point would be complete with a run. The released half (nothing clears `released`) is
  believed true but not proved; `hq` stays an explicit premise, not a theorem.
- B8 as an invariant fact: no bundle needed it.

### After PR #268 / #269 (A4, A5, Q5)
- A4 (7964d55): `:released-proj` dropped; samples 26b/26c/27 compare `:released` directly.
- A5 (24d5e4a): item 44 `finally-leave st`. `finally-exit` turns the head region (F 0) into a running clause
  (F 1, `fins-exit`), `finally-leave` pops it (`fin-exit-bad`/`fin-leave-bad` guards). B8 for normal runs: in a
  clause (`in-fin`) raw0 refuses an await whose debtors are not settled now (`settled-now`, engine `settled-now?`;
  one/all every debtor, any one: `fin-suspends` in `await-bad w st ds m`), a take with nothing to take on an open
  source (`take-bad`), every arm (`fin-shut`). `await-cont` reads regions only (engine `reentrant-k`). progress:
  a region weighs 2 and a clause 1 in mu-f; `finally-exit-dec` holds again, `finally-leave-dec` is new. Changed
  statements: the overrides `t17-g9`/`t17-mb` take `fin-shut w st = false` (was `in-cleanup w st = false`;
  `fin-shut-cleanup` gives the old fact); progress.clj's `mfv-pop-held`/`pop-held` (a pop of any head drops mu-f by
  one: false once a region weighs 2) are replaced by `mfv-exit-held`/`exit-held` (exit of a head region) and
  `mfv-leave-held`/`leave-held` (pop of a head clause); `fx-row` now concludes for `run-fin-exit` (was
  `run-fin-pop`), with `q-fx` guarded by `fin-exit-bad` (was `fins-empty`); `finally-exit-dec`'s statement is
  unchanged. Oracle: run finalizers project regions; logs with exits and no leave
  (samples 4, 5: no generator exists; they predate #268) end each clause within its exit's commit; sample 7
  regenerated (`oracle/gen/samples-legacy.clj`, only the leave is new); 22, 25, 25b replay with 0 divergences.
- Q5 (c25c0de, 29021c7): a released world takes no new root, also from a held slice: raw0 refuses observe and pin
  (`root-shut`) and host waits (`host-await-bad`) once released. engine_test `c1-no-roots-after-release` replays
  the counterexample (refused; quiet after the slice exit; c cannot start).
- Sample 28 (#269): the sidecar matches at every checkpoint (complete after the slice exit, c2 never starts), but
  the replay has 5 divergent commits, triaged in `c1-sample-28-triaged` (questions 6, 7).
- `hq` is still a premise. Plan (not done): `wq` = R (released stays released) and Q (quiet stays quiet).
  R: a bundle `b -> released w` over the step (every primitive edit is a frame except `set-released`).
  Q needs an invariant beyond the guard: K w = pending-act = 0, pubs = [] (no layer-1 transition creates one),
  and released -> pins = [] and no host-creditor edge (only T8/T22/pin add them, now refused when released; T21
  removes them). With K, I3 (every id kept, `step-i3-total`; refused steps keep the world), I1 (`lit-i1-scope`:
  scope parents are scopes) and ids-unique, a quiet world's live set is scopes and forks only (no run, so no
  running task; roots: root/open explicit scopes), so it holds no computation, task, source, edge, activation or
  resource, and every item is refused there (token items: no run; host items: `host-shut`; start/dispatch/
  link-demand/fire/ack: no row). K's bundle needs patches at the edge insertions (await's wait edge: creditor =
  the fresh activation id > 0; take likewise) and an override for `revoke-roots`. Layer 2 then carries K and I3
  for every live born cell (an unborn instance released by E4 needs only R).

### hq (step 3), state
- Released half: DONE (0c2a49e). spindel.v2.quiet `grel` bundle; `step-released` (p3b w, released w -> released after
  any step).
- K: DONE (0d8d35c). `gk-rest` = pending-act = 0, no publication row, and once released no pin and no host-creditor
  edge; `step-k` (p3b w, K w -> K after any step), `k-empty`. Edge insertions are patched (track/reactivation: dep;
  await/take: wait edge whose creditor is the fresh activation id, > 0 by ids-below; T8/T22 only while not released,
  raw0's root-shut / host-await-bad), pin needs root-shut, unpin deletes from no pins, revoke-roots resets all. No
  counterexample to K.
- Quiet half: BLOCKED (question 8). The planned argument (a quiet world's rows are scopes and forks only, so every
  item is refused) fails on §3.4 admissions: `keep-fn` keeps a row with handles > 0 (`admitted`) without a root.
  T21 zeroes every handle, but `handle-new` is a host item that a held slice may still issue after T21 (it is not
  one of #269's roots). Trace (engine_test helpers, from the empty world): create-comp-top c, observe c, start c
  (run r), schedule r, release-world, `handle-new c` ACCEPTED (r's cleanup slice), slice-exit r: released, no run
  (quiet), c kept (idle, handles 1, done-epoch 0); `start c` ACCEPTED. In this trace Rule R cancels and retires the
  stray run in the same step, so the world stays quiet, but completion stability then rests on Rule R's stray-run
  handling plus facts the invariants do not give (an admitted link source with `link-demand` would need the root
  scope's closure after T21, also not an invariant yet). With `handle-new` refused once released (as observe/pin),
  K extends by "released -> every handle count is 0" and the planned proof goes through.

- Q8 answered (no handle after T21): 7881eaf refuses, once released, handle-new, the top-level creations,
  create-source/spawn in a body (`body-shut`), create-comp/create-link in a body (`cc-shut`), link-demand,
  link-realize and append (`root-shut`), besides observe/pin/host waits. Remaining for the quiet half, in order:
  (1) K gains "released -> every comp/task/source handle count is 0": the `gk` copy then needs the handle facts
  at `inv-comp-upd`/`inv-task-upd`/`inv-source-upd` (extra argument: f keeps a zero count; comp-h0/dec keep it,
  comp-h1/task-h1/source-h1 only under `root-shut w = false`, from handle-new's guard) and a `released = false`
  premise at every row creation (`inv-*-ins-fresh` in t1-body/t1-top, t3, spawn-rows (t4, t4-top, link-demand),
  create-link(-top), link-realize, append), threaded from the raw0 guards above; `drop-edges`'s comps-resync and
  `drop-cred`'s comp-set-pending keep the counts. (2) the closure lemma: K, I3 (`step-i3-total`), I1
  (`lit-i1-scope`), ids-unique and no run give a live set of scopes and forks and no admitted row, hence no
  computation, task, source, edge or resource (cleanup rows: to check that a cleanup entry's run exists); (3) the
  quiet-world refusal lemma (token items: no run; host items: host-shut; start/dispatch/link/fire/ack: no row);
  (4) sys.clj carries K and I3 for every live born cell (fork copies, instance basis via pinv, activation) and
  discharges `hq` (E4 unborn cells need only `step-released`).

### Questions (engine session)
Answered: 1 (A4: the projection is fixed in PR #268; drop `:released-proj` then), 2 (A1), 4 (A2); 3 is A5 (after #268).
New (Stage B finding):
5. After T21, a cancelled run's cleanup slice still holds the slice, and Z#56 exempts a held slice from the host
   refusal, so `observe`/`pin` (and other host items beyond Z#40's deliver/post/release/write/close) are accepted there.
   Once the slice exits the world is released with no run but holds a demanded (or pinned) computation, which T5/T11
   then start. Does the engine admit these in a cleanup slice after release, and if so what does completion do (latch
   complete, then a run)? Candidate fixes: in a released world a cleanup slice admits only Z#40's items; or completion
   also requires that no computation is demanded/startable.
   Answered (#269): option 1.
6. Sample 28, commits 10-14: after T21 the engine keeps computation 5 not idle with run 7 (cancelled, unwinding,
   cleanup pending); the model's Rule R idles it (validity :invalid, run cleared: a non-idle computation outside
   live, its run held only by the cleanup entry). Which is intended?
7. Sample 28, commit 13: `[:write 3 12]` from the cleanup slice is logged accepted although signal 3 was collected at
   T21 (both projections lack it); the model refuses a write to a missing source. Is an accepted no-op write the
   log contract here?
8. After T21, may a cleanup slice create a handle (`[:handle-new x]`, re-admitting a row by §3.4 handles > 0)?
   If not (a released world takes no new admission, as no new root), the model refuses it and completion
   stability follows from K; if yes, a computation admitted that way can be started (T5) after completion.

1. `:released` in the verify projection is `false` after the release commit (verify.clj `projection`); keep the
   deviation or fix the projection?
2. A run scope never materialized is not closed by T16/T21 (it is no S-CHILD) while a materialized one is (sample 9 vs
   27): is "the run scope closes at its run's retirement" the intended rule for both? The model closes both with the
   subtree (as the materialized case).
3. B8 in a normal run's finally clause: should the engine log `[:finally-leave r]` (the clause's end) so the model can
   refuse suspending items there too? Without it the refusal is invisible in the log and unneeded for replay.
4. `cancel-task!` on a done, unretired run commits `[:cancel r]` (no row change in the model); confirm that is intended
   also when the run holds no op resource.

### Engine PR #270 (Q7) and Q6 (2026-11-16)
- Merged origin/engine-v2 65991b6 (spec Z#68). Q7: a Z#40 effect on a row Rule R removed is no item; the model needs
  no change (it never sees the item). Samples 4 (43 commits) and 5 (41) regenerated with `[:finally-leave]`; sample 4
  logs run 29's cleanup `[:slice-exit 29]`; sample 28 lost its write. The oracle's fallback that ended a clause at its
  exit (logs without `[:finally-leave]`) is gone. Samples 4-28 replay with 0 divergences and every sidecar matches;
  sample 28 is a normal C1 sample (`c1-samples`). Samples 1-3 keep their triaged lists (logs of older engines with no
  generator: legacy epoch step at demand, settle/E granularity; not reproducible without a generator).
- Q6 (spec §3.3 step 1.3, §3.2): the demotion keeps a computation idle only with a result or handles > 0; one with
  neither whose run is in cleanup (in `cleanup-rows`) stays a **tombstone**: not idle, no validity, basis/adoption
  released, C.run = its (stale, epoch-stepped) cancelled run; T13 clears C.run and the filter removes it (no reason).
  Model: `CompRow.tomb` (model-only, not projected), set only by `comp-demote-row` (rule.clj; field-wise
  `comp-make-idle` when `demote-idle`, else `comp-tomb-row`), cleared by every row that starts a run or wakes
  (`comp-start-row`, `comp-set-run`, `comp-react-row`, `comp-demand-row`, `comp-replace-row`,
  `comp-make-idle`); copied by every other row. Normalization leaves a tombstone alone (`comp-norm` = idle or tomb or
  live; `comp-active` = neither idle nor tomb, the P2 measure). A re-demanded tombstone is dispatched (T11/T5) like
  the engine (`needs-run?`), which clears the flag. handle-new on a tombstone is refused (engine session: `handle!`
  on an existing row runs only through adoption, which finds the row through a reference, and a tombstone has none):
  `t-handle-new`'s computation arm refuses `(:tomb c)`, and `comp-h1` copies the flag (was: cleared it; the former
  corner "handle-new on a tombstone clears the flag" is gone). engine_test `c1-handle-new-tombstone-refused`.
- Proofs: the tombstone is dormant (spindel.v2.tomb, `gy`); P3 (`filter-safe-of-refs`) needs it for a dep edge's
  creditor (`refs-untomb`), I10/I14/h-mark/h-mem2's normalization rounds for a stray run's or a dep edge's
  computation (`trc`). Demotion proofs split on `demote-idle` (`demote-row-idle-upd`/`demote-row-tomb-upd`, lit.clj):
  I10 `g10-tomb` (key `ck-tomb`), I14 `vrk-frame` with domination (`dom14-wake`).
- **Changed statements** (premises added; every `step-p3x`/`*-total` headline theorem is unchanged):
  `normalized-comps` (+ `(:tomb c) = false`: a tombstone may sit outside live); `step-l1-comp` (conclusion
  `idle || tomb`: L1 for a computation outside live); casc `demote-lt` (+ not a tombstone: only strays are demoted);
  lit `dep-cred-live`, `cred-kept`, `fs-ref-ok`, `fs-mark-ok`, `filter-safe-of-refs` (+ `refs-untomb w`); p3 `ri`
  gains `gy 0` (so `ri-parts`/`ri-intro` have 5 parts); i10 `stray-pair`, `stray-ncw`, `g10-norm-round` (+ the
  `ta-one` list), `g10-norm-loop`, `g10-normalize`, `g10-rule-r-round`, `g10-rr-loop`, `g10-rule-r` (+ acts-alive,
  gy 0), `step-g10`, `step-lit-i10-current` (+ `p3b w`); i14 `vr-pass-start`, `vr-norm-round`, `vr-norm-loop`,
  `vr-normalize`, `vr-rule-r-round`, `vr-rr-loop`, `vr-rule-r` (+ `trc w`), `step-v14` (+ ga, gy 0); hmk2
  `hmk-norm-round`, `hmk-norm-loop`, `hmk-normalize-x`, `hmk-rule-r-round`, `hmk-rr-loop`, `hmk-rule-r` (+ `trc w`),
  `step-hmk` (+ gy 0); hm18 `h18-norm-round`, `h18-norm-loop`, `h18-normalize`, `h18-rule-r-round`, `h18-rr-loop`,
  `h18-rule-r` (+ `trc w`). Reason for all: a tombstone is a non-idle computation outside live, and the facts these
  lemmas used ("not idle and normalized, hence live") need "and not a tombstone", which `gy 0` gives.
- Released-world `[:append s v 0]` from a cleanup slice is logged as a refusal entry (engine session); the model
  refuses it with the world unchanged (raw0's `root-shut`) and the oracle compares the accepted flag only.

- Next (quiet half, step (1) of "hq (step 3), state"): extend `gk-rest`'s released clause by "every comp/task/source
  handle count is 0". Findings for the copy: the handle-carrying creations are exactly 10 source-theorem sites
  (`inv-comp-ins-fresh` in create-comp-raw; `inv-task-ins-fresh` in spawn-rows; `inv-source-ins-fresh` in t1-body,
  t1-top, t1-full, create-link, create-link-top, the stream rows, link-realize, append), all with handles 1 and all
  reached only through raw0 arms guarded by body-shut / cc-shut / root-shut (each implies `root-shut w = false`); no
  cascade, dispatch (respawn) or Rule R step creates a row. T21's `release-world-raw` sets `released` (revoke-roots)
  before `zero-handles`, so GK needs an override of `release-world-raw` (not of `revoke-roots`); `comp-h1`/`task-h1`/
  `source-h1` need handle-new's `root-shut` premise, `comp-dec-handles`/`*-h0` keep 0. `release-unborn` (E4) sets the
  flag only (unborn cells need `step-released` only).

### Quiet half, step (1): K's handle clause (2026-11-16)
- Follow-up A first (543bd4e): handle-new refuses a tombstone (engine session); `comp-h1` copies the flag.
- `gk-rest` = `gk0-rest` (the former K) and `gh-rest`: once released, every computation, task and source has handle
  count 0 (`hz-all`). `step-k`, `k-empty`: statement text unchanged, K is stronger (the definition of `gk-rest`
  changed). Helper lemmas about the former K were renamed `gk0-*` (`gk0-rest-mono`, `gk0-rest-edge-upd`, ...,
  `gk0-set-pins-*`, `gk0-rest-revoke`); the `gk-rest-*` names are now the combined lemmas. `gk-revoke-roots` is gone
  (revoke-roots alone breaks the handle clause: T21 sets `released` before zeroing): T21 is overridden whole
  (`t-release-world-gk`: `gk-zero-revoke`, `zero-handles-hz`, then the cascade copy).
- The copy: computation/task/source row edits take `hz` (a zero count stays zero; default by rfl, per-case lemmas
  `task-cancel-result-hk`/`source-consume-hk`, decrements `-z` with `sub1-zero`, serve-or overridden with its `keep`'s
  hz); handle-new's h1 (`-open`) and the three creations with handles 1 take `hr0 : root-shut w = false`, threaded
  (`add-premise`) through the 27 theorems between raw0's arms and the creations (`gk-threaded`); raw0's arms supply it
  from their guards (`body-root`, `cc-root`, or the root-shut case). No counterexample: every creation and h1 is
  under a released guard.

### Follow-up B (2026-11-16): samples 1-3
- Merged origin/engine-v2 54e3df1 (#271: log-sample-1.edn regenerated by gen/samples-legacy-1.clj, table format,
  12 commits). oracle_test `sample-1-table-format` = `(aligned 1 12)`: 0 divergences, no triage.
- Samples 2 (legacy format) and 3 (early table format) are sample 4's scenario: retired from the replay set
  (`sample-2-legacy`, `sample-3-table-format`, `sample-3-strict`, `sample-3-known` removed); they stay as adapter
  fixtures in `projection-roundtrip` (roundtrip + `log-format`). The strict deviations stay covered by sample 4's
  strict test. Every sample of the replay set replays with 0 divergences and no triage list.

### Quiet half, step (2): the closure lemma (spindel.v2.qworld)
- New bundle `gc`: every cleanup entry's run is a run row. Cleanup entries are written at a run's cancel
  (`cancel-run-local`, from `job-apply`'s run-find) and at T12's `retire-after` (run-find), and go with the run
  (`retire-with`: run-del then cleanup-del); the filter keeps every cleanup entry's run (it is in `cleanup-rows`).
  Overrides: `cleanup-set` (premise: the run exists), `retire-after`, `cancel-run-local`, `job-apply`, `retire-with`.
  `step-gc-rest`, `gc-empty`. Checked: a cleanup entry always has its run (no counterexample).
- `i3 w` = the filter keeps every id (`tbl-all (keep-fn w) (all-ids w)`); a state fact through every step
  (`step-i3-inv`: accepted steps by `step-i3-total`, refused ones keep the world).
- `qinv` = p3l && K (`gk-rest`) && gc && i3; `step-qinv`, `qinv-empty`. `qh` = qinv && released && no run.
- `quiet-rows` (`qh w -> only-scopes w`): no computation (tombstones included), task, run, source, edge, activation,
  resource, cleanup entry, publication or fork marker. Live is scopes only (`reach-scope`: roots are scopes since no
  pin, host edge, pending activation or publication; a scope's successors are its parent, a scope by literal I1 and
  gw's root-ok for the root scope; no running task (no run); no fork marker (gw)); keep is live (`keep-scope`: no
  cleanup entry (gc), nothing admitted (K's handle clause), no storage (no run)); a scope id is no other row's id
  (`scope-only`, unique ids); I3 keeps every row id, so every non-scope table is empty.

### Quiet half, step (3): the refusal lemma (spindel.v2.qworld)
- `quiet-refused` (`qh w -> (:accepted (raw w it)) = false` for every item): host items by `host-shut` (released, no
  run holds a slice); the others (`raw0-quiet`) by raw0's released guards (creations and link items: root-shut,
  body-shut, cc-shut), for want of a run (every token item: `tok-run` is none; schedule, finalize, slice-exit), or for
  want of their row (start/dispatch: no computation; fire: no edge; resource-ack/resource-fire: no resource);
  release-world by the released flag. So `quiet-step` (the step leaves a quiet world unchanged) and `quiet-stays`
  (`qinv w`, `world-quiet w` -> `world-quiet` after any step). A released-world `[:append s v 0]` (the engine's
  refusal entry) is refused with the world unchanged (host-shut / root-shut); qworld_test `quiet-world-runtime`
  replays the Q5 trace and checks K, gc, I3, only scopes and the refusal of eight item kinds at runtime.

### Quiet half, step (4): layer 2 without hq (sys.clj)
- `cq c` = (unborn and released: an E4 instance) or `qinv` of its world; `qsinv cells` = every live cell has cq;
  `qpinv pubs` = every live publication's basis is released or holds qinv. Kept by every system operation
  (`qsinv-step/-wake/-resume/-merge/-publish/-abandon/-accept/-complete/-drop/-idle-release/-release-unborn/
  -activate/-fork/-fork-effect/-instantiate`, `qpinv-publish/-abandon`; start: `qsinv-init`, `qpinv-none`).
  Activation: `act-ok` says not released, so the instance's cq is qinv, and the activated world keeps it.
- `wqc c w2` (released stays; a born cell's quiet world stays quiet) replaces `wq` for the cell: an unborn cell is
  ready by its flag, so it needs only the released half. Composites: `rel-*` (released stays: `step-released`),
  `qid-*` (a quiet qinv world is left as it is: `quiet-step`; fire-ack, wake-one/-all, apply-diff, merge-world),
  `qinv-*` (qinv through them: `step-qinv`).
- Completion stability outright: `cinv-step-q`, `cinv-wake-q`, `cinv-resume-q`, `cinv-merge-q`, `cinv-publish-q`,
  `cinv-abandon-q` (premises sinv, qsinv, cinv; no hq). The hq-premised `cinv-*` theorems are unchanged (hq itself
  stays false of an arbitrary p3l world: quiet stability needs qinv).
- Premise of `qsinv-fork`/`qsinv-fork-effect`: the forked cell is not an E4-released unborn instance (its world need
  not have K: handles may be > 0, so a born copy could start an admitted computation after completing). Question 9.
  Gone since question 9 was answered (below): both fork forms are refused from an unborn cell.

### Questions (engine session), C1 quiet half
9. May a fork (host `fork!` or the fork effect) be taken from an unborn instance, in particular one released by E4?
   The model's `sys-fork`/`sys-fork-effect` have no guard; the completion invariant for the child assumes the parent
   is not an E4-released instance (a released world with handles > 0 copied into a born cell could, after its runs
   retire and it completes, start a computation admitted by a handle).
   Answered (engine-v2 54e3df1, core.cljc): no, neither form, E4-released or not. Host `fork!` throws "fork! of an
   unactivated instance" while W-UNBORN is set (host-fork-call!); an E4 release keeps the instance unborn (`born?`
   requires not released); the `(fork)` effect needs a valid run inside a slice, and an unborn instance drains no
   slice (E4: its inherited work waits).

### Question 9 answered: fork guard (sys.clj, 2026-11-16)
- `sys-fork` and `sys-fork-effect` are guarded by "the source cell is born" (`(:unborn (cells k)) = false`); otherwise
  the operation is refused with the system unchanged (the `sys-wake`/`sys-activate` convention): `fork-refused`,
  `fork-effect-refused` (new). This is LAYER2.md L2's guard "not unborn", now in the model.
- `qsinv-fork`/`qsinv-fork-effect` hold for every live source cell: the refused case keeps qsinv, the accepted case
  is born, so its cq is qinv (`cq-born`). Completion stability (`qsinv`, `qpinv`) is kept by every system operation
  with no premise beyond liveness of the source.
- **Changed statements**: `qsinv-fork`, `qsinv-fork-effect`: premise `(:unborn (cells k)) && (:released ...) = false`
  removed (discharged by the guard). `fork-copy`: premise `(:unborn (cells k)) = false` added (a refused fork leaves
  cell m as it was, so the child's world is the parent's only when the fork is taken). Unchanged statements, proofs
  split on the guard: `fork-frame`, `fork-effect-frame`, `sinv-fork`, `sinv-fork-effect`, `cinv-fork`,
  `cinv-fork-effect`.
- sys_test: no existing case forked an unborn cell (`c1-fork-discharge` forks a born, released world). New
  `c1-fork-of-unborn-refused`: both forms are refused from an unborn and from an E4-released instance (system
  unchanged at the source and the target id), and both are taken from the same world as a born cell.
- Fresh-JVM `clojure -M:test` (2026-11-16, after question 9): 245 tests, 207,430 assertions, 0 failures, 0 errors.
  No sorry.
- Fresh-JVM `clojure -M:test` (2026-11-16, after step 4): 244 tests, 207,419 assertions, 0 failures, 0 errors. No sorry.

### Z#69 detach acyclic (engine PR #272, c8829bf; 2026-11-16)
- Merge of origin/engine-v2 c8829bf (a21b69e): spec Z#69, core.cljc `within?` + the `detach!` guard, task_test
  `detach-into-own-subtree-is-refused`; nothing under formal/ changed. No new oracle sample.
- Guard (engine.clj, 3544ef0): `scope-within w s a` = `s == a` or `a` on `scope-ancestors w s` (the worklist over the
  parent fields Rule R's cleanup already uses; engine `within?` walks the same chain). `detach-ok` gains
  `not (scope-within w s (task-run-scope w t))` as its innermost conjunct, so detach is refused (refusal entry, world
  unchanged, `t-detach-refuse`) when the destination is the task's run scope or any scope below it. A task with no
  run has run scope 0, which is never on a chain (scope-up drops parent 0), as the engine skips the check without
  a run scope.
- Proof repairs: the three bundle overrides that destructure `detach-ok` take the open-scope conjunct from its new
  position (`t-detach-g1` i1, `t-detach-esb` p3, `t-detach-g8` i8; proof text only). Every other detach proof cases
  on `detach-ok` only (refusing more is a refused case). **No theorem statement changed.** Definitions changed:
  `detach-ok`; new: `scope-within`.
- Invariant (spindel.v2.acyc, 97e634e): `scopes-acyclic w` = no scope is on its own `scope-ancestors` (executable),
  equivalent to `forall y, Reach (scope-up w) (scope-up w y) y -> False` (`cy-acyc-of`, `cy-acyc-intro`). The
  bundle `gcy-rest` adds `cy-par-below`: every scope's parent is below the allocator. That auxiliary fact is needed
  for scope creation: a fresh scope (id next-id) is then nobody's parent, so no cycle passes through it; it holds
  because new scopes get parent 0 or an existing scope (run creation: 0 or `task-scope-parent`; open-scope: the
  current scope under `open-ok`), and detach's destination is an open (so existing) scope.
  Generic lemmas over the parent function: a sub-graph keeps acyclicity (`cy-acyc-sub`: scope deletion,
  `remove-if-empty`, Rule R's filter, parent-preserving scope edits), a fresh node no edge points to keeps it
  (`cy-acyc-fresh`), re-parenting x under p keeps it when x is neither p nor above p (`cy-acyc-reparent`: every walk
  either never uses x's new edge, or after it stays in p's chain, which avoids x). The guard is exactly the last
  premise; without it detach is the only transition that breaks the invariant (no other path re-parents a scope).
- Theorems: `step-gcy` (Rule R's honest hypothesis), `step-acyc` (p3b w, gcy-rest w -> gcy-rest after any step),
  `acyc-empty`, `step-acyclic`, `step-acyclic-reach`. No counterexample: the invariant holds for every step.
- Cross-world destination: not expressible in layer 1 (ids are world-local); the engine refuses it (#273).
- Tests: engine_test `z69-detach-into-own-subtree-refused` (K0 opens O and spawns J; J opens S below its run scope;
  detach J S and detach J (J's run scope) are refused with the world unchanged; the unguarded `detach-move` makes the
  parent fields cyclic by a direct parent walk; detach J root is accepted, J and its run scope move under the root).
  acyc_test: the theorems, and `scopes-acyclic` on the empty world and on a 2-cycle.
- Fresh-JVM `clojure -M:test` (2026-11-16, after Z#69): 248 tests, 207,177 assertions, 0 failures, 0 errors. No sorry.
  (+3 tests: acyc_test's two, engine_test's z69 case. Fewer assertions than after question 9 (207,430), not investigated; likely engine_test's
  random-item walks now refuse some detaches, and a refused step makes fewer per-step checks than an accepted one.)

## C1c stage A (2026-11-16): task/scope completion ledger, host joins

Engine PR #273 (engine-v2 1aac850, spec Z#70; `c1c-task-joins-design.md` v4 amendments), oracle samples PR #274
(branch `test/v2-oracle-c1c-stage-a`, generator `oracle/gen/samples-c1c-a.clj`, samples 29, 30, 31a, 31b, 32 with
sidecars). Merged both into `formal/c1-model` (the samples branch had not merged into engine-v2 yet). No log shape
changed: no new item, so no `Item` constructor and no layer-1 transition changes; every namespace loads as before.

### Facts checked against the model (from the earlier review)
- The run scope is K+2 and created eagerly: T4's `spawn-rows` (engine.clj ~610) allocates task K, run K+1 and run
  scope K+2 (`add-run-scope`) in one step; the engine materializes it on first use (`run-scope!`).
- Z#18 `subtree-empty` (rule.clj ~411) requires every scope of the subtree closed, no scope outside it with its parent
  inside, no held task (`task-held-in`: owned there and not done or its run unretired), no fork marker, no run scoped
  in it, and no root-kind scope.
- No upward cascade in the model: T13's `retire-with` runs `remove-if-empty` on the retiring run's subtree only. A
  parent left closed and empty is not live (scopes retain only upward, `scope-contrib`; downward retention comes from
  alive runs, open explicit roots and cleanup entries via `anc-close`), so the same step's Rule R filter (`keep-fn`,
  retain.clj ~297) removes it. The engine cascades in `remove-scope-if-empty!`; at commit boundaries the rows agree.
- Computations' run scopes have parent 0 (`start-raw` and `new-run-of` call `add-run-scope ... 0`), and a task owned
  by a computation has run scope parent 0 (`task-scope-parent`: its owner is no scope). Neither is in any task's run
  scope subtree, so a task's completion never waits for computations created in its body nor for the tasks they own
  (the D2 boundary of the v4 amendments).

### Mapping
| Z#70 rule | level | model |
|---|---|---|
| task complete: done, run retired (T13), run scope removed or never materialized | layer 1, derived | `spindel.v2.ledger/task-complete w k` = not `task-held w k` (a task row with result none or run /= 0) and no scope row k+2. The eager run scope collapses the two engine cases: one never materialized owns nothing, so T13 removes it in the retiring step (`remove-if-empty`), exactly when the engine completes the task with no K-SROW. |
| scope complete: its row removed | layer 1, derived | `scope-complete w s` = no scope row s. The root scope is never removed (Z#56: `root-in`, and it is a root), so it is never complete, also in a complete world (sidecars: scope 2 present after completion). |
| K-COMPLETE / S-COMPLETE flags, set once | engine bookkeeping | not modelled: derived predicates. Stability (once complete, complete forever) is a theorem to prove (later stage). |
| S-TASK / K-SROW recorded at materialization | engine bookkeeping | the pairing k <-> k+2 is fixed by the allocation order (oracle contract), no field. |
| `retire!`: `maybe-complete!` last, after `release-ownership!` | layer 1 + 2 | layer-2 completion (`sys-complete`) is a separate system operation after a step, so the order is given; "complete world => every task complete" becomes a theorem from `quiet-rows` (later stage, below). |
| host `on-joined` / `await-joined` | layer 2 | `Cell.joins` (new last field): the pending host joins of the cell, a list of target task ids (one entry per subscription). `sys-join` admits one: no row, edge, handle, id or item; no released guard (admitted after release); delivered at once (not recorded) when the target is complete or the cell is. `sys-deliver` delivers the pending joins whose target is complete (the engine does it inside the completing commit). `complete-cell` empties the list (abandonment: joins still pending at world completion are delivered with it). `fork-cell`, `fork-effect-cell` and `inst-cell` start with no joins (not inherited). Both operations are system operations, not Items. |
| `detach!` refuses a scope of another world | - | not expressible in layer 1 (ids are world-local; see Z#69 above). |

### Identity of a removed id
The model keeps no kind for an id after its row is gone (one global id space, nothing typed after deletion). A
removed id is known to be a task by its holder: a host join records the id it was admitted for (the host holds a
task handle, so the id was allocated: admission requires `k < next-id`), and the oracle remembers every task and
scope it has seen (as the generator's `seen`). For such a task id, no task row reads as not held, so
`task-complete` is then "no scope row k+2". Removal of the task row with its run scope still present (handles 0, kept
only by a child's cleanup chain) is therefore not complete, as in the engine (its K-SROW is still a present row).

### Oracle
- `check-observations` compares, when the sidecar has them, per task (every task seen at a checkpoint so far)
  `:done?` (result /= none; no row = true), `:retired?` (run = 0; no row = true), `:srow-present?` (scope k+2 present
  and materialized), `:complete?` (`task-complete`); per scope (every scope seen so far) `:open?`, `:present?`,
  `:complete?` (`scope-complete`); and `:pending-joins` (length of the cell's `joins` after `sys-join` of the joins the
  spec registers before that checkpoint and `sys-deliver`). The task and scope key sets are compared exactly.
- Materialized (oracle only): a run scope is reported once it has owned something (a task, a source, a child scope or
  a fork marker) in some model world up to the checkpoint; never-materialized run scopes are not in the engine's
  registry, so they are left out of the scope set and read `srow-present? false`.
- Host joins are not in the log: the family spec lists them (`:joins [[world step target]]`: registered before
  checkpoint `step`).

### Results
- Commits: 661415c (this plan), ee2fddc (`spindel.v2.ledger`), e1c1078 (sys.clj host joins), 0f3500d (oracle,
  samples 29-32), b38bf56 (tests).
- Every namespace loads (no item, no layer-1 transition changed; sys.clj re-checks with the new Cell field). No
  `sorry`. **No theorem statement changed.** Definitions changed: `Cell` (new last field `joins`) and its
  constructors (`cell-step`, `wake-cell`, `accept-cell`, `release-unborn-cell`, `drop-cell`, `resume-cell`,
  `act-cell`, `merge-cell` keep `joins`; `fork-cell`, `fork-effect-cell`, `inst-cell` start with none;
  `complete-cell` empties it). New: ledger `task-srow`, `task-held`, `task-complete`, `scope-complete`; sys
  `join-pending`, `join-cell`, `join-ok`, `sys-join`, `deliver-cell`, `sys-deliver`.
- Oracle: samples 29, 30, 31a, 31b (family, instance at `[:arm 4 :savepoint]`) and 32 replay with 0 divergences, and
  `check-observations` gives [] on every field, the C1c ones included (key sets of `:tasks`/`:scopes` exact). Checked
  not vacuous: dropping a join from the spec, or freezing the model's worlds, gives mismatches. Every earlier sample
  replays as before. The sidecars and the model agree everywhere; no side to pick.
- Tests: engine_test `c1c-completion-ledger` (the three conditions; P > E > C > G with G's offload: P, C and the
  scopes P+2, E, C+2 complete only in the step that retires G; G's unmaterialized run scope goes with G; the root
  scope never completes); sys_test `c1c-join-delivered-at-target-completion`, `c1c-abandoned-join-delivered-at-completion`
  (E4 instance), `c1c-join-after-release` (admitted after release; at once on a complete target or world; refused
  for an unallocated id or a collected world), `c1c-joins-not-inherited` (fork, fork effect, instance); oracle_test
  `c1c-sample-shapes`.
- Fresh-JVM `clojure -M:test` (2026-11-16, after C1c stage A): 254 tests, 207,529 assertions, 0 failures, 0 errors.

### Theorems for the proof stage (done: see "C1c stage A, proof stage" below)
- Stability: `task-complete w k -> task-complete (step w it) k` for a task id k (k + 2 < next-id): a scope id is never
  re-inserted (scope creation takes next-id; ids below the allocator), a task row with a result keeps it and run 0
  stays 0 (tasks never restart; re-spawn adoption creates no run), no task row reappears. Same for
  `scope-complete`. Through Rule R: the filter only removes.
- Complete world => every task and every non-root scope complete: `quiet-rows` gives no task row (not held); what is
  missing is "a quiet qinv world holds the root scope only" (live = roots = the root scope, as no open explicit scope
  survives its run: needs an invariant that an open explicit scope lies in the run-scope subtree of an alive run).
- Layer 2: `jinv` (a complete cell has no pending join; after `sys-deliver` every pending target is incomplete); frames
  (`sys-join`/`sys-deliver` keep sinv, cinv, qsinv, qpinv: the world is untouched); delivery exactly once (an entry
  leaves only by `sys-deliver`/`complete-cell` and the list grows only by `sys-join`); abandonment is only ever
  needed for an unborn cell (a born complete cell's targets are complete, by the previous theorem).

### Questions (engine session), C1c stage A
10. The root scope is never removed (Z#56), so it is never complete, also in a complete world (every sidecar shows
    scope 2 present after completion). The statement "a complete world has every task and scope complete" then
    reads "every task and every non-root scope". Intended?
11. Materialization: the oracle infers a materialized run scope from what it has owned (a task, a source, a
    computation, a child scope, a fork marker). Does `run-scope!` materialize in any other case? If so,
    `:srow-present?` and the scope key set could differ on a future sample; an `:materialized?` per scope (or the
    S-TASK presence) in the sidecar would make the comparison independent of the inference.
12. `:pending-joins` counts every entry of W-JOIN-SUBS, withdrawn ones included (pruned lazily, every 16). The model
    has no withdrawal (host side). Should the sidecar count live subscriptions only, and is withdrawal meant to be
    modelled?
13. `on-joined` on a task of a world that was collected (idle release, merge): the model refuses it (nothing ever
    delivered). What does the engine do (deliver, as the world is gone, or never)?
14. Pending joins at the completion of a born world: by the theorem above none should remain (every task complete).
    Is `complete-world!`'s delivery meant only for unborn instances (a tripwire candidate: assert nothing pending in a
    born world)?

## C1c stage A, proof stage (2026-11-16, branch `formal/c1c-a-proofs`)

### Engine session answers (questions 10-14)
10. Intended: a complete world has every task and every NON-root scope complete. The root scope is never removed. A
    computation run's scope (parent 0) is not the root and is included.
11. The engine materializes a run scope only when it immediately owns something. Engine PR #275 adds `:materialized?`
    per task to the sidecar; the oracle is to use it instead of inferring.
12. Withdrawal is part of the contract: `on-joined` returns a withdraw fn (a host-side flag: no gate, no item).
    Delivery is at most once (a CAS races withdrawal, the winner is final); a subscription withdrawn before delivery
    never fires. #275 makes `:pending-joins` count only live joins and adds sample 33 (two joins, one withdrawn;
    checkpoints 2, 1, 0; only the live one fires). Model: a host-side mark that delivery skips, a system operation,
    not an Item.
13. `on-joined` on a task of a collected world is unreachable in the engine; the model's refusal stays.
14. For a BORN world nothing is pending at completion: once runs = 0 every task is done and every non-root scope
    removed before completion, so only an unborn instance's copied tasks can be pending. To be a theorem.

### Step 1: engine #275 folded in (engine-v2 3fa691a), withdrawal in layer 2
- Merged origin/engine-v2 3fa691a (#275: sidecars of 29-32 add per task `:materialized?` and count live joins only,
  logs byte-identical; sample 33, withdrawal).
- Oracle: a task's run scope (k + 2) is materialized as the sidecar says (scope key set, `:srow-present?`); a run
  scope of no task (a computation's) is still inferred ("owned something"). The model's `:materialized?` is that
  inference for the task's run scope and is compared with the sidecar's: it agrees on every checkpoint of 29-33
  (question 11 cross-checked). Withdrawals are listed in the family spec as `:withdraw [[step join-id]]`.
  Sample 33 replays exactly: `:pending-joins` 2, 1, 0; without the withdrawal the model reads 2 at `:one-withdrawn`.
- Layer 2 (sys.clj), definitions changed: `Cell.joins` is a `(List Join)`; `Join` = id (the number of joins the
  cell admitted before it), target, state (`js-pending` / `js-delivered` / `js-withdrawn`). Entries are never
  removed: `join-cell` records every admitted join (delivered at once when the target or the cell is complete);
  `deliver-cell` and `complete-cell` mark pending joins delivered (`hj-done`), the new `sys-withdraw`
  (`withdraw-cell`) marks a pending join withdrawn (`hj-drop`); both act on a pending join only, so the race's winner
  is final. `pending-joins` counts the pending ones (the sidecar's `:pending-joins`). `join-ok` now also refuses
  target 0 (none: no handle names it; without the guard a join on 0 would wait for scope 2, the root scope, which is
  never removed). Removed: `join-pending`. Fork, fork effect and instance start with no joins.
- Ansatz note: the elaborator failed with "Unknown constant: joinant" on a defn named `join-deliver` passed as a
  value (renamed `hj-done`; not investigated further).
- Tests: sys_test reads pending targets (`pj`), new `c1c-join-withdrawal` (2, then 1 live join; only the live one is
  delivered; a delivered join stays delivered under withdraw and a second delivery; join on 0 refused); oracle_test
  sample 33 in `c1c-specs`, `c1c-sample-shapes` checks `:materialized?` presence and the 2/1/0 counts.

### Step 2: stability (spindel.v2.lstab)
- Bundle `gst k s` = inv-sample && `gst-rest k s` (k < next-id, task k not held: no row, or result /= none and run 0;
  s < next-id, no scope row s), parameters `tk9`/`sc9` (the copier puts parameters before the source binders, which
  use `k` and `s`). Primitives: `*-ins-fresh` insert at next-id (> k, s), scope update/deletion/filter only keep or
  remove rows, the allocator only grows. Task row updates take an extra argument (`th-row t = false -> th-row (f t)
  = false`, rfl for every update that keeps result and run); the three that write them: `task-cancel-result`
  (writes over none only, `gst-task-tcr`, patch of `inv-debtor-side`), `task-clear-run` (`gst-task-tcl`, patch of
  `inv-clear-task-run`), and T12's `task-result-row res` (run kept, result tag ok/err from raw0's `complete-refused`
  guard: overrides `gst-complete-body`, `gst-complete-raw`, `t12-gst` and the raw0 patch, as GL in spindel.v2.lit).
- Theorems: `step-gst` (Rule R's honest hypothesis), `task-complete-stable` (p3b w, k + 2 < next-id, task-complete w k
  -> task-complete after any step), `scope-complete-stable` (p3b w, s < next-id, scope-complete w s -> the same after
  any step; the bundle at k = 0, which is never a row). No counterexample. A collected task row with its run scope
  still present reads not held, so its completion is then "no scope row k + 2" (covered: the clauses are separate).

### Step 3: a complete world has every task and every non-root scope complete (spindel.v2.oscope, qworld)
- New invariant `gos-rest w`: every scope row that is open and not root-kind (`os-need`) has a run row whose run scope
  is the row itself or on its parent chain (`hw`, via Z#69's `scope-within`). With no run, no open non-root scope;
  then live is the root scope (roots: root scope and open explicit scopes; the root scope's parent is 0, gw), and
  I3 + K leave only live rows.
- Why it holds (bundle `gos` = inv-sample && gos-rest, copied over raw/normalize with spindel.v2.lit's copier):
  frames for every table but scopes and runs; run updates keep `:scope` (extra argument, rfl); `run-ins` adds a
  witness; scope closes remove obligations (`close-hk`); overrides:
  `gos-add-run-scope` (the run scope's witness is the new run), `t-open-scope-gos` (`cur-scope` is the run scope or
  an open explicit scope reached through open explicit children, `cur-cases`: the new scope inherits its witness),
  `t-detach-gos` (the re-parented run scope is witnessed by its own run; a chain through it either survives or
  reaches it, `rp-within`), `gos-remove-if-empty` (Z#18 deletes a subtree with `parent-outside`: kept chains are
  unchanged, `keep-within`), `gos-retire-local` (T13: the run row goes after `close-local` closed its run scope's
  whole subtree; `scope-subtree` converges, `sub-conv`, fuel 2 + #scopes against a deduplicated parent list, so it
  holds every scope whose chain reaches the run scope, `sub-within`; between the close and the deletion a second
  bundle `gox x` (every open non-root scope has a witness run whose id is not x) is copied over the source closes,
  which update runs only id- and scope-preservingly; ids are unique, so the retiring run's row is the only one with
  its id, `find-uniq`), Rule R's filter (`gos-filter`: every run is kept, i1r `run-kept` with gr0 and normalized;
  every kept scope's parent is kept, `keep-parent`, i1's closure argument). `step-gos` (ga, gr0, gos, rule-r-safe
  raw), `gos-empty`.
- qworld: `qinv` gains the conjunct `gos-rest` (definition changed); `step-qinv` takes it from `step-gos`
  (gr0 from p3l via p3h: `p3l-gr0`). New: `qinv-gos`, `quiet-no-open`, `roots-root`, `root-succ-none`, `keep-live`,
  `live-root`, `quiet-root-only` (`qh w`, scope-has w y -> y = root-scope-id), `quiet-task-complete` (`qh w`,
  t /= 0 -> task-complete w t), `quiet-scope-complete` (`qh w`, s /= 2 -> scope-complete w s).
- Changed statements: `qinv-intro` (new premise `gos-rest w`: qinv has a fifth conjunct). `qinv-parts`, `step-qinv`,
  `qinv-empty` and every sys.clj `cq`/`qsinv`/`qpinv` statement are unchanged in text (qinv is stronger). Task id 0
  is excluded in `quiet-task-complete` (its "run scope" would be scope 2, the root, never removed).
- Ansatz notes: constants are global by name (two namespaces may not define the same theorem name: `beq-comm`,
  `ids-len`, `runs-nodup` renamed `os-*`); `(simp only ...)` that turns a hypothesis into False errors instead of
  closing the goal (full `simp` closes); `cases` on `List.Mem` substitutes either variable (use an eliminator lemma).

### Step 4: layer-2 joins (sys.clj)
- `jinv cells`: every live cell is `jok`: complete -> no pending join; join ids distinct and below the number of
  joins admitted; targets not 0. Kept by every system operation: `jinv-join`, `-deliver`, `-withdraw`, `-complete`,
  `-step`, `-publish`, `-abandon`, `-wake`, `-accept`, `-release-unborn`, `-drop`, `-idle-release`, `-resume`,
  `-activate`, `-merge`, `-fork`, `-fork-effect`, `-instantiate`; start: `jinv-init` (live cells have no joins).
- `deliver-pending`: every pending join after `sys-deliver` has an incomplete target.
- Frames (the world and every flag but the joins untouched): `sinv-join/-deliver/-withdraw`,
  `cinv-join/-deliver/-withdraw`, `qsinv-join/-deliver/-withdraw`; `qpinv` reads publications only, which none of
  the three touches (no lemma needed).
- Delivery at most once: `jkeep js js2` (every non-pending join of js is in js2 as it is); `once-deliver`,
  `once-withdraw`, `once-complete`, `once-join`; with distinct ids (jinv), `final-stays`: a delivered or withdrawn
  join is the only join with its id afterwards, so the race's winner is final (no second delivery, a withdrawn
  join never fires).
- Question 10, layer 2: `complete-born-ledger` (qsinv, cinv, a live complete born cell -> every task id /= 0 and every
  scope /= 2 complete in its world). Question 14: `born-complete-delivered` (qsinv, jinv, a live born cell with
  complete-ready -> after sys-deliver no join is pending: every target is complete) and `born-abandon-none` (then
  `complete-cell` changes no join): abandonment delivery is only ever needed for an unborn instance.
- No earlier statement changed in this step.

### Suite (C1c stage A, proof stage)
- Fresh-JVM `clojure -M:test` (2026-11-17, after steps 1-4 and the merge of engine-v2 f09aa35): 258 tests,
  207,650 assertions, 0 failures, 0 errors. No sorry. (+4 tests: lstab_test, oscope_test's two, sys_test
  `c1c-join-withdrawal`.)
- Merge of #278 (f09aa35): its `:materialized?` line in `ledger-obs` is dropped in favour of the step-1 version
  (the model's "owned something" inference for the task's run scope, compared with the sidecar's value; the
  sidecar's value itself feeds the scope key set and `:srow-present?`). Every sample, 33 included, replays exactly.

### Engine session answers after the proof stage (2026-11-17)
- A host join's target 0 is unreachable (`join-ok` refuses it; no handle names id 0).
- The oracle's "owned something" inference is exact for computation run scopes too: no sidecar flag is needed for them.
- Pruning withdrawn or delivered joins is unobservable: keeping them forever (the model) is sound.

## C1c stage B (2026-11-17, branch `formal/c1c-b-model`): owned forks, model stage

Design `c1c-task-joins-design.md` v4 L2 (owned-fork counts, `[:owned-done s child]`, W-NORMALIZE), model first: the
engine follows this model. Mapping and questions 15-18 agreed with the engine session (answers below).

### Mapping
- **Count.** W-OWNED-N {scope -> n} is the layer-1 fork markers (`ForkRow {id child owner}`, empty before stage B):
  one marker per counted child; `id` = the child world's id (`alloc-id!` of the parent in fork-world*, the id
  `[:fork r child]` logs), `owner` = the forking run's current scope (`current-scope!` = `cur-scope`: an open explicit
  scope or the run scope, never the root). Counted only in own-child!'s counting branch of the `(fork)` effect (the
  world is not released, the owner is open): `own-world`, system operation `sys-own` (with `sys-fork-effect`, which
  copies the world first, so the child does not inherit its own marker, and `sys-accept`). A host fork and an
  activated instance are owned weakly by the root and never counted (question 18a).
- **Keep reason.** Z#18's `subtree-empty` already refused a subtree owning a marker (`fork-owned-in`). Rule R's filter
  keeps a marker and its owner's ancestor chain: retain.clj `fork-keep`, part of storage (`storage-gather` =
  `storage-gather0` ++ `fork-keep`). The engine has no filter over scope rows (question 17): scopes go only by
  remove-scope-if-empty!, which gains `W-OWNED-N[s] = 0` and `s ∉ W-NORMALIZE`; the filter is the model's encoding.
- **`[:owned-done s child]`** (internal item of the owner, accepted after release; posted by kid-done! for a counted
  child, on completion or collection, question 18b): `owned-done-world` drops the marker, then Z#18 at s
  (`remove-empty-at`) and Rule R; without that marker the world is unchanged. `sys-owned-done` ends with
  `sys-complete` (maybe-complete!).
- **W-NORMALIZE.** A fork, fork effect, savepoint basis and instance copy their source's world, so they hold its
  markers: its counts and its own undrained inherited markers, which is v4's union. `Cell.norm` = the marker ids the
  cell's world started with (`fork-cell`, `fork-effect-cell`: the source world's markers; `inst-cell`: the basis's).
  `[:normalize]` (logged once, only when W-NORMALIZE is non-empty; engine sites: run-turn!'s first-turn entry and
  activate!, next to activate-dormant!, condition `(seq W-NORMALIZE)`): `drain-world` drops them, Z#18 at each owner,
  Rule R; `sys-drain` (born cells only; an E4-released unborn instance completes abandoned) ends with `sys-complete`.
  Engine: fork-world* sets the child's W-NORMALIZE := source W-NORMALIZE ∪ {s | W-OWNED-N[s] > 0} and W-OWNED-N :=
  nil; instance-world* copies the basis's.
- **Completion (questions 15, 16).** `complete-ready` (born branch) also requires `no-markers`: W-OWNED-N all zero and
  W-NORMALIZE empty (engine maybe-complete!). The fast path may run a host item before the first-turn drain (as for
  activate-dormant!): a release there does not complete the world; the drain that follows does.
- **Oracle.** `[:fork r c]`: bump to c, then `own-world` with the run's `cur-scope` (else bump past c);
  `[:owned-done s c]`, `[:normalize]`: the world operations (the replay's `norm0` = the markers of the world the log
  starts from). Marker rows are not compared (the engine projects `:forks {}`); the sidecar's per-world
  `:owned {s n}` (counts > 0) and `:normalize #{s}` are (question 18c), against the markers outside / inside `norm0`.
  The oracle's world completion also requires no marker. Logs of an engine before stage B (no `[:owned-done]` or
  `[:normalize]` anywhere in the family, `stage-b-log?`; option `:owned?`) count nothing at the fork effect: samples
  15 and 22 replay as before. Samples with fork effects should be regenerated with the stage B engine.
- **Tests.** sys_test `c1c-owned-fork-holds-its-scope` (the run scope stays after the task retires, the task is not
  complete and a host join waits; owned-done removes the scope and completes the task), `c1c-owned-fork-early-branch-not-counted`
  (released world, no open scope), `c1c-completion-waits-for-the-count` (question 16: the collected child leaves
  W-KIDS empty, the count holds completion, owned-done completes), `c1c-normalization` (a fork inherits the marker as
  `norm`; question 15: released before the drain it is not complete; the drain removes the scope, completes the task
  and the world; the parent keeps its count; a fork of the undrained child inherits it; an unborn cell does not drain).

### Questions (engine session), C1c stage B, and answers (2026-11-17, engine c8e2ac6)
15. The fast path (ingress-body runs the host item before run-turn!) lets a release complete a fresh fork before its
    first-turn drain, with a scope still kept by W-NORMALIZE (Q10 broken). Answer: maybe-complete! also requires
    W-OWNED-N empty and W-NORMALIZE empty; the drain and owned-done end with maybe-complete!. The fast-path order
    stays (the drain follows in run-turn!).
16. kid-done! decrements W-KIDS outside the gate before the owner runs `[:owned-done]`: a run retiring in between
    completes the world with a count left. Answer: the same fix as 15.
17. Answer: no filter over scopes in the engine; scope rows go only by remove-scope-if-empty! (close-scope!,
    release-ownership!, detach!); ancestors are kept by S-CHILDREN. remove-scope-if-empty! gains `W-OWNED-N[s] = 0`
    and `s ∉ W-NORMALIZE` (the second for a task in an inherited s retiring before the drain).
18. (a) no count on root: counted iff strong? and not the early branch; (b) kid-done! posts `[:owned-done s child]`
    for counted children only (the kid token carries s), also on collection (kid-collected! goes through kid-done!);
    the owner is never complete then; (c) sidecar per world `:owned {s n}` (n > 0) and `:normalize #{s}`; (d) `child`
    is the child world's id. Additions: owned-done commits `[:owned-done s child]`; the drain commits `[:normalize]`.

### Changed statements (model stage)
- retain.clj `storage-gather` (now `storage-gather0` ++ `fork-keep`); `storage-filter` (new premise use:
  `fork-keep-filter`). p3.clj `esk` takes the markers (`frow-ok`: id and owner are references) and every esb lemma
  carries them (`esk-fparts`, `frow-mono`, `fork-keep-ok`); i11 `storage-obl` splits the marker half. sys.clj
  `Cell` gains `norm`; `complete-ready` gains `no-markers`.
- Unchanged: `p3l` still contains gw's `forks-nil` (layer 1 creates no marker). Worlds with markers arise only from the
  new system operations, whose invariants are the proof stage: generalize gw (markers: ids below the allocator,
  owners are scopes), `sinv-own`/`-owned-done`/`-drain`, cinv with markers, Q10 (complete born world -> every scope
  but the root complete) with markers, and normalization: after the drain every inherited scope is complete or kept.

### Stage B samples 34-38 (engine Z#72, `feat/c1c-b-engine`; oracle gaps closed on `formal/c1c-b-oracle`)
- Samples: 34 (owned fork outlives the task; owned-done completes it), 35 (counted child on an external op that ignores
  cancellation, collected), 36 (`:touched` drains at its first turn; `:untouched` released first, question 15), 37
  (question 16 ordering), 38 (savepoint while counted: the instance drains at activation); 15 and 22 regenerated (each
  gains the parent's `[:owned-done]`). All in `c1-samples`: every world replays with 0 divergences and the sidecars
  (`:owned`, `:normalize` included) match.
- Oracle gaps closed: (A) a world starts with its source's materialization up to the fork commit (K-SROW is a copied
  row flag; fork-effect! materializes the forking run's scope before the boundary), recursively; (B) the id-less
  `[:owned-done]`/`[:normalize]` align the allocator to the projection (family counter W-NEXT); (C) a child collected
  without a log item: spec flag `:collected-at <checkpoint>` (done for its owner's `:kids` and `:complete?` from then).
- Changed statement: engine.clj `arm-kind-ok` admits `rk-external` (Z#63: arm, then a one-shot completion fire + ack,
  accepted after release; the same lifecycle as `op`). Sample 35 has the first external arm. No proof needed a change.


## C1c stage B, proof stage (2026-11-17, branch `formal/c1c-b-proofs`, from engine-v2 eea3112)

### Step 1: layer 1 with markers (gw generalized; quiet = no marker)
- i11 `gwk`: `forks-nil fs` is replaced by `tbl-all fk-ok fs` (`fk-ok f` = the owner is not the root scope 2: the
  owner is the forking run's `cur-scope`, never the root; question 18a). Used where gw's marker clause was read:
  `gw-rest-filter` (kept by the filter) and `root-scope-succ` (no marker is owned by the root scope, `fk-root`). Every
  layer-1 step keeps it (no layer-1 transition inserts a marker; deletions and the filter keep `tbl-all`).
- engine.clj `world-quiet` gains `forks-nil (:forks w)` (moved here from i11): the layer-1 part of completion is
  released, no run and no marker (W-OWNED-N all zero, W-NORMALIZE empty: questions 15, 16). owned.clj `no-markers w`
  = `forks-nil (:forks w)`.
- qworld `qh` gains `forks-nil (:forks w)`; `qh-parts` is unchanged in text; new `qh-forks`. Removed:
  `p3l-forks-nil` (false now); its four users read the markers from `qh-forks`. sys.clj: `p3l-no-markers` removed;
  `ready-put`, `ready-put-q`, `cinv-world`, `cinv-world-q` lose the stage-B no-markers premise again (world-quiet now
  carries it: a complete-ready born world is quiet, and `wq`/`wqc` keep quiet), call sites as before stage B.
- Changed statements: `gwk`/`gw-rest` (weaker), `world-quiet` and `qh` (stronger), the four sys.clj lemmas above
  (one premise fewer). `wq`, `wqc`, `cinv`, `qsinv` are unchanged in text (HQ of the `cinv-*` lemmas is stronger
  through world-quiet). Test: qworld_test, a marker keeps a released world without runs from being quiet and qh.

### Step 2a: layer 2 under HB (sys.clj)
- HB (`hb-ops`, as HQ was for C1): own, owned-done and the drain keep p3l and qinv and keep a released world released
  (`hb-world w w2`). Its discharge is per bundle (step 2b).
- Definitions changed (owned.clj): `own-ok` also refuses the root scope (the owner is `cur-scope`, never the root:
  question 18a; it is what keeps gw's `fk-ok`); `drain-world` leaves the world as it is unless one of the inherited
  markers is present (the engine logs `[:normalize]` only with W-NORMALIZE non-empty). New: `owned-done-none`,
  `drain-none` (no marker: unchanged), `own-released` (released: unchanged).
- Theorems: `sinv-own/-owned-done/-drain`, `qsinv-own/-owned-done/-drain` (with sinv: an unborn released cell's world
  stays released, `cq-world`), `cinv-own` (no HB: own leaves a released world as it is), `cinv-owned-done/-drain` (a
  quiet world has no marker, so both leave it as it is; released stays released by HB), `jinv-own/-owned-done/-drain`,
  `complete-no-markers` (cinv: a live complete born cell has no marker: W-OWNED-N all zero and W-NORMALIZE drained).
- Question 10 with markers needs no new proof: `complete-born-ledger` goes through `qh`, which now includes no marker.

### Step 2b: the owned-fork operations as layer-1 items (HB discharged)
- Engine session answers (2026-11-17, engine-v2 eea3112): `[:owned-done s c]` is an internal item (accepted after
  release); `[:normalize]` is a commit at the start of the first turn of a born fork (run-turn!, activate!), not an
  ingress item, unaffected by release; `[:fork r c]` is the forking run's effect in the parent; Rule R runs at every
  commit; an unborn released instance completes without draining (E4, W-NORMALIZE kept: the model's unborn branch of
  complete-ready needs no marker condition, no engine change). At layer 1 each is a world transition; the engine's
  orders (queued / fast path) are layer-2 interleavings.
- Model: step.clj items 45 `own s m`, 46 `owned-done s c`, 47 `drain ids` (internal: not host items; token true);
  engine.clj `t-own` (own-ok moved here), `t-owned-done`, `t-drain` (each refused when it has nothing to do), with
  `-inv`/`-refuse` and raw0/raw-inv/raw0-refuse/raw0-l4 arms. owned.clj `own-world`, `owned-done-world`,
  `drain-world` are now `(:world (world-step w it))` (Rule R and the any-loser cancel included, as the engine's
  commit!); `internal-refused` (a refused internal item leaves the world as it is) gives `owned-done-none`,
  `drain-none`, `own-released`.
- Primitives: edits.clj `inv-fork-del`, `inv-fork-ins-fresh`, `fork-del-ids-ok`/`fork-filter-ids-ok` (the last id
  table, `deffilter-last`, `nat-app-nil-r`); engine.clj `inv-remove-empty-at`, `open-at-has` (moved from i1),
  `own-ok-parts`. Every copier bundle: `inv-fork-del` a frame (gw: `gw-rest-fork-del`, esb: `esb-rest-fork-del`),
  `inv-fork-ins-fresh` handled as `inv-source-ins-fresh` (or a frame next to `inv-resource-ins-fresh`); gw and esb
  override `t-own-inv` (`t-own-gw`: the owner is not the root, own-ok; `t-own-esb` / `esb-fork-ins-own`: the
  marker's id and owner are references); rank_step `rk-fork-*`; hm3 `h3r-bump` for fork-ins; i1r GR0 wraps
  `inv-fork-del`, `inv-remove-empty-at` (used as values in `t-drain-inv`); acts' GA/GX prims; hm17's h3 assembly and
  inv.clj's i10/i9 chains (`ra-of`: the three change neither runs nor activations). qworld `raw0-quiet` gains
  `(:forks w) = nil` (from `qh-forks`): a quiet world refuses the three as well.
- sys.clj: `hb-ops` and every hb premise removed; `hb-step` (step-p3l, step-qinv, step-released) gives `hb-own`,
  `hb-owned-done`, `hb-drain`; `own-is-step`, `owned-done-is-step` (rfl). The step 2a theorems keep their statements
  minus the premise.
- REPL notes: tomb's `GY` is a `defonce` (unmap it before reloading tomb); the 1g REPL slot runs out of heap in i14
  after several reloads (a 4g REPL via `jvm-slot.sh run` loads everything).

### Step 3: normalization (spindel.v2.drained, sys.clj)
- `drain-clean`: p3l w -> after `drain-world w ids` no marker has an id in ids (a refused drain: there was none).
  The drain deletes them (`fold-del-out`: `nat-fold fork-del` leaves no fork with an id in the list); Z#18's removal,
  the any-loser cancel and Rule R add no marker: the copier bundle `gnf ids` (`fork-out`: the id is not in ids;
  frames, `gnf-rest-fork-del`, `gnf-rest-filter`, the edge edits), `lcopy!` of `inv-remove-empty-at`,
  `nat-fold-inv`, `inv-cancel-losers`, `inv-normalize`; `gnf-rule-r` with `step-rule-r-safe` of the raw world.
- `sys-drain-clean` (layer 2): sinv, a live born cell k -> after `sys-drain` its `norm` is empty and its world holds
  none of the markers it inherited (W-NORMALIZE drained; a scope they kept is then removed by Z#18 if empty, or
  kept by something else).
- With `complete-no-markers` (a complete born world has no marker), `complete-born-ledger` (question 10 through qh,
  which now has no marker) and step 2b, the stage B proof obligations listed in "Changed statements (model stage)"
  are discharged.

## C2 merge layer, model stage (2026-11-17, branch `formal/c2-merge`, from engine-v2 97514a6)

Option C (decided): the engine owns the mechanism, not the policy. Modelled in sys.clj, in the order asked:

### 1. seal + diff; merge requires sealed and quiescent
- `Cell.sealed` (fork, fork effect, instance start unsealed); `sys-seal` (irreversible). `cell-step` goes through
  `cstep`: a sealed cell refuses a `seal-item` outside a slice (`seal-shut`, as `host-shut`: a body's items, held
  slice, are not host items). `seal-item`: the admissions of spec §9 (spawn-top = T4, host-await = T5 from the
  host, observe = T8) **and** the host source changes (write, deliver, post, release, append, close). Withdrawals,
  handles, pins, cancel, close-scope, release and every internal item are taken (propagation continues).
- `diff c b` is the existing L12 diff (inherited non-link sources whose version moved).
- `merge-guard`: sealed, not released, `quiescent` (no slice, every run parked or done; the engine's
  `work-pending?` check is of the same strength). `merge-unsealed`: an unsealed child never merges.
- Lemmas through the gate: `p3l-cstep`, `wq-cstep`, `rel-cstep`, `qid-cstep`, `qinv-cstep`, `sealed-write`.
  `own-is-step`/`owned-done-is-step` are now simp (the seal gate is in `sys-step`).

### 2. the resolver step of L12
- `pick rv p c b x`: the child's value when the parent's version of x is the basis's, else
  `(rv x base parent-value child-value)` (none = refusal). `merge-writes` picks every diff source against the parent
  as it is at the merge (the engine's entries under both gates), then `items-run` writes them in diff order. One
  refusal (resolver, or a write: closed, removed, stream) refuses the merge: `merge-world` is then the parent
  (`merge-refused`), and `sys-merge-release` (merge!: parent side, then T21 in the child; k = m refused) leaves
  the system unchanged (`merge-release-refused`).
- `merge-default`: with `refuse-all`, `merge-ok` is today's L12 (guard, `no-conflict`, every `apply-diff` write
  accepted); `writes-default-ok`/`-no`, `run-wr`.
- Invariants: sinv/cinv(-q)/qsinv/jinv of `sys-merge`, `sys-merge-release`, `sys-seal`.

### 3. R6 transfer (dvergr transfer-fork!)
- Decided with the engine session (Q4, Q5 below): only a root-owned fork (host fork, or `:owner`) transfers, into the
  new owner's root scope, uncounted; a counted `(fork)`-effect child never leaves its scope. Two operations with
  anything between them: `sys-xfer-reserve` (k2 takes the token; refused unless k2 live, open, not the current
  owner, not owned by m within the fuel: `owned-under`) and `sys-xfer-move` (if m live, open, not counted in k1
  (`counted-in`: no marker), k1 live and not complete, reservation held: k1 gives the token back, maybe-complete!,
  m's owner := k2; otherwise the reservation is undone). m's own completion then acknowledges k2.
- Invariants: sinv/cinv/qsinv/jinv of each (`cinv-disown-any`: giving a token back is safe in a complete owner).
- The first, atomic `sys-transfer` (which also moved a count) is gone: it passed the cell index to
  `[:owned-done s1 m]`, whose argument is the marker id, and the decision removed the counted case.

### 4. R2 descendant? over lineage
- `descendant cells a d n` (fuel n) over `parent`: `descendant-refl`, `descendant-fork`, `descendant-par`;
  `descendant-xfer-reserve`/`-move`: a transfer changes no lineage answer (ownership is not lineage).

### Engine findings (for the engine session)
- F1 seal must refuse host source changes too, not only T4/T5/T8: otherwise a host write after seal changes
  diff(W′), and a settlement layer's preflight of the diff can differ from what merge! applies.
- F2 quiescence: merge!'s check (`work-pending?`; the model's `quiescent`) admits a run parked on an armed
  resource. Fires are internal and not refused by seal, so after seal a timer can resume a parked task that
  writes: diff(W′) is stable only under spec §9's quiescence (no unretired run, no outstanding resource). merge!
  itself is atomic, so this matters for a diff read before merge!, not for merge! with the resolver inside.
- F3 the resolver needs the base value: W-MBASE keeps `[identity version]`; base is the fork-time state
  (readable through the child's lineage at its ordinal, or kept with the version).
- F4 the resolver runs under the parent's and the child's gates: it must be a pure function of its four
  arguments (no world operation, B7); a throw is a refusal.
- F5 transfer: refuse an owner in the fork's owned subtree (or the fork itself): an ownership cycle and neither
  world completes. Order in the engine: old side and the token retarget under the old owner's and the fork's
  gates; k2's acceptance queued before the fork can complete (FIFO ingress puts its `[:owned-done s2 m]` after
  it); a refused acceptance refuses the transfer (dvergr's prepare/abort expects an unchanged fork).
- Not modelled yet (as asked): stream append on merge; stock resolvers.

### Engine design questions (2026-11-17) and answers from the model
- Q1 unseal: `sys-unseal` (refused in a released world, so after a merge) keeps sinv/cinv/qsinv/jinv: the flag only
  gates host items and merge. A diff read before an unseal is stale after it.
- Q2 merge! sealing the child itself: `merge-seal-same` (k ≠ m): the seal changes no world, so the merge reads the
  same child, as sealed. But a refused merge then leaves the child sealed unless the item clears it again (the
  refusal must change neither world): effectively the guard without `sealed`.
- Q3 base at the child's first change: the child's state before its first change of x is the basis's (frozen
  fork, no following), so `[ident base-version base-value]` recorded then is `version-of b x`/`state-of b x`.
- Q4 the engine's order, as two system operations with anything between them: `sys-xfer-reserve` (k2 takes
  the token; refused unless k2 live, open, not the current owner, not owned by m) and `sys-xfer-move` (old side
  and m's owner := k2 if m live and open, k1 live, not complete, reservation held; else the reservation is undone).
  Each keeps sinv/cinv/qsinv/jinv (`cinv-disown-any`: giving a token back is safe in a complete owner too).
  k2 ≠ current owner is required: with a token list, reserve then move into the same owner drops it.
- Q5 counted re-owning: not needed. Decided: transfer! refuses a counted `(fork)`-effect child (no s1, no
  `[:owned-done]`); `sys-xfer-move` narrowed accordingly.
- Decided (engine session): Q1 unseal! under the child's gate; Q2 no auto-seal, merge! refuses unsealed; Q3 base
  recorded at the first change of every kind; Q4 reserve then move, no `[:transfer]` item (sidecar).

### Aligned with the engine (spec Z#74, feat/c2-merge-engine)
- `merge-guard` is §9: `settled` (W-RUNS 0, no cleanup entry, no outstanding resource; the empty ingress is the
  engine's, an item is atomic here) and not released; the model's weaker `quiescent` is no longer used.
- `seals-ok`: the child sealed and the parent not. A sealed parent refuses the merge (its writes would be host
  writes past its own seal: without the guard, merge would bypass `cstep`).
- `seal-item` is the in-item refusals only: write (swap logs a write), deliver, post, release, append, close.
  The admissions (spawn-top, create-comp-top, observe) throw at admission and make no item, so they are not
  layer-1 refusals: an admission taken before the seal is processed as usual.
- The race of a spawn-top admitted before the seal: harmless for a diff read at sealed and settled, as long as no
  admission can still enqueue after that point (check and enqueue atomic with the seal flag, or the seal waits for
  in-flight admissions). Otherwise refusing in the item is needed.
- W-MBASE `[ident base-version base-value]` at own-copy!: the first copy precedes the first change, so it is the
  basis state (Q3). transfer!: as `sys-xfer-reserve`/`sys-xfer-move`.

### Samples 39-42 (engine #289, generator oracle/gen/samples-c2.clj), registered in oracle_test
- `replay :sealed-from n`: seal makes no item; from commit n an item the model's `seal-shut` refuses is refused
  unchanged (layer-2 `cstep`). 39: the child's `[:write 3 7]`/`[:post 4 8]` refused as the engine's; unsealed
  the model would take both (2 divergences).
- 40: the merges with `sys/merge-world` and a resolver over the decoded values (logs carry interned ids):
  throw and ::refuse are none; the value resolver gives the parent's two merge writes exactly.
- 41: the child sealed from commit 4: the body write after the seal is taken (slice held); `settled` false while
  the task is parked on its timer (first merge refused), true after its retirement; the second merge is the
  model's (the parent's `:next-id` is the family allocator, not compared).
- 42: `sys-xfer-reserve`/`sys-xfer-move`, then the releases (k2's release releases m, F2) and completions give
  the sidecar's :owner (until completion), pending :kids, :released? and :complete? at all four checkpoints.
