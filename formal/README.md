# Formal model of the v2 engine

A machine-checked model of the engine in `src/org/replikativ/spindel/v2/` and of its specification
`docs/engine-v2-spec.md`, written in the [ansatz](https://github.com/replikativ/ansatz) DSL (Lean 4's
kernel and tactics in Clojure syntax). Every namespace is checked by the ansatz kernel when it loads;
there is no `sorry`, `admit` or axiom, and only Lean's `Init` is used (no Mathlib). The model is not
part of the spindel jar (`build.clj` packages `src/` only). The ansatz version is pinned in `deps.edn`.

## What is proved, in plain words

**One world (layer 1).** The state of one world is a record of tables (`World`, spec §2). A step
`world-step w it` applies one item (a slice effect, a completion, a scheduling choice or a host
operation): the item's raw transition (spec §5.1), then Rule R to normalization (§3.3). A refused item
leaves the world unchanged.

- `inv w` is the single top invariant of a world (`spindel.v2.top`), a conjunction of executable Bool
  predicates that together state the invariants of spec §6 (table below).
- `inv-empty`: the empty world satisfies `inv`.
- `inv-step`: every item, accepted or refused, keeps `inv`; the only premise is `inv w`.
- `reach-inv`: every world reachable from the empty world by steps (`Reach1`) satisfies `inv`.
- `l5-safety-total` (L5, safety half): in a world satisfying the invariant where no slice can run, a
  demanded computation that is waiting has in its cone a blocked dependency, a computation that can be
  run, or a parked task that is not blocked (a user deadlock).
- `step-l4` (L4): an item with an invalid token changes nothing.

**A system of worlds (layer 2).** Forks, savepoints (publish, resume, instantiate, activate, abandon),
release, joins, owned forks, seal and merge, transfer and fork-local retirement are operations on a
system of cells, each holding one layer-1 world (`spindel.v2.sys`).

- `sys-reach-inv`: every system reachable from an initial one (`SysReach`: `init` and one constructor
  per operation, 29, each with the guard the engine guarantees as a premise) satisfies `sysinv`
  (`spindel.v2.systop`): every live world and every live publication's basis satisfies `inv`; a live
  complete cell is ready (released, no run, every kid done, no marker); every live world is
  quiet-compatible; the host joins are well formed.
- `sys-reach-rinv` (Z#77, LOC3): in every reachable system, a cell whose fork-local retirement is
  pending has processed no item.

**Physical representation.** `mv-refinement` (`spindel.v2.mvcc`): in every state of the MVCC row heap
reachable by the engine's operations (write, own-copy, create, fork, instance, prune, finish, drop,
collect), every active world reads every id exactly as the value-copy model has it. So layer 2's value
copies are a sound abstraction of the way the engine shares rows between forks.

## The parts

| Part | What | Namespaces (`spindel.v2.*`) |
|------|------|------------|
| Transition system | state and tables, primitive table edits, retention (`live`), the `Item` type and raw transitions, Rule R and the cancel family, the transitions that create runs, `world-step` | `state`, `edits`, `reach`, `retain`, `step`, `rule`, `engine`; `ledger` (task/scope completion ledger), `owned` (owned forks) |
| Predicates | one executable Bool predicate per invariant of spec §6 (the tripwires the oracle runs), the spec's literal readings `lit-*`, I13 as guard lemmas, L1 | `inv`; `local` (Z#77) |
| Layer-1 invariant proofs | the bundle chain `p3b ⊂ … ⊂ p3m` and its step theorems (next section) | `acts`, `lit`, `rank`, `rank_step`, `idle`, `tomb`, `p3`, `i10`, `i11`, `i1`, `i5`, `i1o`, `i1r`, `i8`, `hm`, `i14`, `acyc`, `hmk`, `hmk2`, `ar`, `hm3`–`hm18`, `hm6_base` |
| Progress | fuel sufficiency and termination (P1–P12), L2 measures, L5 safety | `casc`, `react`, `progress`, `l5`, `z59` |
| Completion (C1, C1c) | released and quiet worlds, completion stability, open scopes, draining of inherited markers | `quiet`, `qworld`, `lstab`, `oscope`, `drained` |
| Headline, layer 1 | `inv`, `inv-step`, `Reach1`, `reach-inv` | `top` |
| Layer 2 | cells, publications and their operations; `skip` (an id taken by a sibling world); `sysinv`, `SysReach`, `sys-reach-inv` | `sys`, `skip`, `systop` |
| Physical | the MVCC row representation (tokens, versions, copy maps) | `mvcc`; `cow` (the superseded forward-map version) |
| Oracle (tests) | replays commit logs recorded from the engine through the model, compares every committed state | `test/spindel/v2/oracle.clj`, `oracle_test.clj`, `oracle/` |

Files are `src/spindel/v2/<name>.clj` (`-` in a namespace name is `_` in the file name). Kernel names are
global: a theorem is `step-p3m`, not `spindel.v2.hm18/step-p3m`.

### The invariant: bundles and the chain

`inv-sample w` (`edits`) is the base of every proof: exact pending counts, every edge's creditor and
debtor exist and have the right kind, ids are unique and below the allocator. A *bundle* is
`inv-sample w && rest w`. Its step theorem is built from one lemma per primitive table edit (the rest
part under that edit) and then carried over every composite lemma of `step-inv` by a source-level lemma
copier (`lit`: `mk-bundle`, `prim!`, `lcopy!`; `override!` supplies a hand proof for a transition whose
rest part is not compositional, `patch!` adds a premise to a source proof). Every copy is
kernel-checked.

The bundles form one chain, one link per proof campaign. Each link is `(Bool.and previous new)` and has
`step-<link> : link w -> link (world-step w it)` and `<link>-empty`:

| Link | Adds | Spec | Where |
|------|------|------|-------|
| p3b | `ga` activations (`acts`), `inv-rank` ranks (`rank_step`), `gl` task runs and `g9` resources (`lit`), `ri` the facts every Rule R round needs: `g7` idle shape (`idle`), `mdb` marked edges are dep edges, `esb` references are no edge ids, `aha` activations' runs are alive, `gy` tombstones are dormant (`tomb`) | I12, I10 (tasks), I9 (resources), I7, P3 | `p3` |
| p3c | `g10r` computation runs (a run's epoch, the current run) | I10 | `i10` |
| p3d | `gw` root scope and fork markers, `inv-i11a` retention | I11a | `i11` |
| p3e | `g1` scope parents | I1 | `i1` |
| p3f | `g5` no armed dep edge on a final debtor | I5 | `i5` |
| p3g | `gso`, `i1-own` owners of tasks, computations, sources | I1 | `i1o` |
| p3h | `gr0` resource owners, run entities and scopes, a done run has a cleanup entry | I1, I4 | `i1r` |
| p3i | `g8` closed scopes | I8 | `i8` |
| p3j | `gd` per-computation facts (done-epoch, C.run) | L5 | `hm` |
| p3k | `v14` validity graph acyclic, no dep edge on an idle debtor | I14, I7 | `i14` |
| p3l | `hmk` h-mark: a marked edge is a dep edge on a waiting computation | L5 (P11) | `hmk`, `hmk2` |
| p3la | `ar` alive runs of a computation are its C.run, `ekb` edge kinds | I10, I9 | `ar`, `hm6`, `hm6_base` |
| p3m | `h3` h-mem2: the unfilled members of current computation runs | L5 (P11), I2 | `hm3`–`hm18` |

`inv = p3m && svb && inv-i9 && inv-i10-slice && i3` adds the invariants proved alongside the chain:
`svb` I5 observe (`p3`), `inv-i9` I9 activations and `inv-i10-slice` D0 (`inv`), `i3` I3 (`qworld`).

The link names record the history of the proof (`p3` was obligation P3). They are kernel names reused in
thousands of generated theorem names, so they are kept; read `inv` and this table instead.

## Invariant table

Status: **proved**: a theorem from `inv`, or a step theorem whose only premise is its bundle;
**partial**: some clauses proved, the rest named; **oracle only**: an executable predicate checked on
replayed engine states, no theorem; **open**: neither; **out of scope**: not modelled, by design.

| Spec | Predicate | Theorem (namespace) | Status |
|------|-----------|---------------------|--------|
| I1 ownership | `inv-i1`, `lit-i1-scope`, `i1-own`, `i1-runs` | `step-lit-i1-total` (`i1r`), `step-lit-i1-scope-total` (`i1`), `step-lit-i1-owners-total` (`i1o`) | proved (model readings Z#23, Z#25, Z#26) |
| I2 referential integrity | `edges-ref-ok` (in `inv-sample`), `aha`, member facts of `h3` | `step-inv-total`, `step-p3b` (`p3`), `step-p3m` (`hm18`) | partial: "every basis member exists or is idle" and the member edges of activations of task runs or stale computation runs are not covered |
| I3 liveness | `i3` | `step-i3-inv` (`qworld`); part of `inv` | proved |
| I4 work reachable | `normalized-runs`, `r3-ok` (in `gr0`) | `step-i4-p3` (`p3`, accepted steps; a refusal changes nothing), `step-p3h` (`i1r`) | proved |
| I5 consumption | `wait-cred-ok`, `lit-i5-dep-final`, `svb` | `step-i5-wait` (`inv`), `step-lit-i5-dep-final-total` (`i5`), `step-svb-total`, `step-i5-total` (`p3`) | proved |
| I6 continuation placement | none | none | out of scope: continuations are opaque ids |
| I7 idle shape | `inv-i7`; `dna` (in `v14`); `lit-i7-basis` | `step-lit-i7-total` (`p3`) | partial: the empty-basis clause `lit-i7-basis` is oracle only; wait or observe edges on an idle computation are not excluded by a proved predicate |
| I8 closed scopes | `lit-i8-runs`, `lit-i8-sources` | `step-lit-i8-total` (`i8`) | proved, under the model-only guard `cur-closed` (P10, open) |
| I9 unwinding | `inv-i9`, `lit-i9-res`, `ekb` | `step-i9` (`inv`), `step-lit-i9-res-total` (`p3`), `step-ekb` (`hm6`) | proved for synchronous finalizers (Z#66 is not modelled) |
| I10 runs | `lit-i10-current`, `inv-i10-comp`, `inv-i10-task`, `inv-i10-slice` | `step-lit-i10-current-total` (`i10`), `ar-i10-comp` (`ar`), `step-lit-i10-task-total` (`p3`), `step-i10-slice` (`inv`) | proved |
| I11a retention from obligations | `inv-i11a` | `step-i11a-total` (`i11`) | proved (the Z#66 obligations are not modelled) |
| I11b bounded fan-out | none | none | out of scope: a census gate |
| I12 rank | `ranks-ok` (in `inv-rank`) | `step-ranks` (`rank_step`), `step-rank-total` (`p3`) | proved for the order; "refuses with ::cycle iff the propagation reaches the debtor" is open (T6 also refuses when the raise loop runs out of fuel) |
| I13 coherence as guards | guard lemmas | `i13-fire-dep-live`, `i13-fire-dep-stale`, `i13-fire-wait-stale`, `i13-complete-stale`, `i13-complete-raw-stale` (`inv`) | partial: a wait edge on a computation debtor has no liveness lemma |
| I14 validity acyclic | `vsucc14`, `v14` | `step-i14-total` (`i14`) | proved |
| I15 coherence of results | none | none | open (not modelled) |
| I16 / LOC1, run half: a run of a fork-local task has a fork-local run scope | `loc1-run` | `loc1-runs` (`local`) | proved (in every world) |
| I16 / LOC1, task half: a task owned by a fork-local scope is fork-local | `loc1-task` | none | **open** as part of `inv`; oracle only (fork-local samples 51-60) |
| I16 / LOC2: no fork marker is owned by a fork-local scope | `loc2` | none | **open** as part of `inv`; oracle only (samples 51-60) |
| I16 / LOC3: a pending retirement precedes every item | `rinv` | `sys-reach-rinv` (`systop`) | proved |
| Z#77 `retire-clean` / `retire-quiet`: after `[:retire-local]` no run of a fork-local task, no cleanup entry, every fork-local task done | executable form in `oracle_test` (`fork-local-closure`) | none | **open** as theorems; checked on the replayed sample worlds only |
| Z#69 scope parents acyclic | `scopes-acyclic` | `step-acyc` (`acyc`) | proved (alongside p3b; not part of `inv`) |
| L1 prompt reclamation | — | `step-l1`, `step-l1-comp`, `step-l1-run` (`inv`) | proved in state form, with `live-converged`/`normalized` premises that P1/P2 discharge; no packaged form |
| L2 join | measure `mu-f`, bundle `mb` | `step-mu-le`, `finally-exit-dec`, `slice-exit-retires`, `ack-dec`, `ack-retires` (`progress`) | partial: fair termination is a paper argument; Z#66 is not modelled |
| L3 serial execution | `inv-i10-slice` | `step-i10-slice`, `step-d0` (`inv`) | partial: sequential by construction (D0); host ingress is not modelled |
| L4 no resurrection | `raw-token-ok` | `step-l4` (`engine`) | proved |
| L5 admission, safety half | `quiescent`, `comp-waiting` | `l5-safety-total` (`hm18`) | proved; its third disjunct is "a parked task in the cone that is not blocked" (that this is a cyclic wait is a paper step); the liveness half is a paper argument |

**Layer 2.** `sys-reach-inv` (`systop`) gives, in every reachable system: `sinv` (F5: every live world
satisfies `inv`), `pinv` (every live publication's basis does), `cinv` (completion soundness),
`qsinv`/`qpinv` (quiet-compatible), `jinv` (host joins). Caveats: the merge takes its basis as a free
argument (there is no `Cell.mbase`), so `SysReach`'s merge admits any basis; guards that layer 2 does
not have (a fork of a released world, a merge without a parent relation, a join on any id) are not
premises either. `mvcc`'s refinement is to its own ghost value-copy tables, not to `sys`'s cells.

### Progress obligations

| # | Obligation | Status | Theorem (namespace) |
|---|---|---|---|
| P1 | live worklist fuel sufficiency | proved | `live-converged-all` (`retain`) |
| P2 | normalization terminates and ends normalized | proved | `normalized-ok`, `rule-r-normalized-ok` (`casc`) |
| P3 | Rule R's filter is safe | proved | `filter-safe-of-refs` (`lit`), `step-rule-r-safe` (`p3`) |
| P4 | cascade completion | proved | `casc-done-ok` (`casc`) |
| P5 | I12 ranks kept | proved | `step-rank`, `step-ranks` (`rank_step`) |
| P6 | §3.4 validation walk within fuel | proved | `valid-done-ok` (`react`) |
| P7 | settle worklist within fuel | proved | `settle-done-ok` (`l5`) |
| P8 | reactivation worklist within fuel | proved | `react-done-ok` (`react`) |
| P9 | Rule R's loop ends with no orphans | proved | `rule-r-no-orphans` (`i1o`) |
| P10 | the raw0 guard `cur-closed` never fires | **open**; reduced to `rso` (an alive normal task run's run scope is open), which the tests check | `cur-open-of-run-scope`, `cur-open-of-rso` (`i14`) |
| P11 | h-mark and h-mem2 are step invariants | proved | `step-h-mark-total` (`hmk2`), `step-h-mem2-total`, `l5-safety-total` (`hm18`) |
| P12 | I14 acyclic | proved | `step-i14-total` (`i14`) |

Fuel with no sufficiency theorem (fuel is a parameter, convergence a checked flag): the I12 raise loop
(an exhausted raise refuses T6), Derive/blocked (`blocked-complete` assumes `blocked-converged`), the
dirty cone and `cur-scope`.

## Trust boundary

- **Kernel.** Every statement is checked by the ansatz kernel (a port of Lean 4's) when its namespace
  loads. Generated theorems (the copier's) are checked like hand-written ones.
- **Model against spec.** The model's predicates and transitions are read against
  `docs/engine-v2-spec.md`; every namespace's docstring names the spec items it covers, and the readings
  where the model differs from the spec's wording are listed there (engine.clj's B1-B10, rule.clj's
  readings, inv.clj's predicates).
- **Model against engine: the oracle.** The engine is not verified. `test/spindel/v2/oracle.clj` replays
  commit logs recorded from the engine (samples 1-60 in `test/spindel/v2/oracle/`, generated by
  `oracle/gen/`) through `world-step` and the layer-2 operations, and compares every committed state
  (id-keyed tables) and every refusal. On every accepted step it checks Rule R's flags and the
  executable invariants `inv-all` and `lit-all` (tripwires). `inv` itself is evaluated on every world of
  samples 4, 5 and 13 (`top_test`), not on every replayed world. A divergence fails the test.
- **Premises of the reachability inductives** (`SysReach`, `mvcc`'s `MReach`) are the guards the
  engine guarantees. They are assumptions about the engine, checked only through the oracle.

## Running

From this directory (ansatz comes from Clojars; the proofs need a large stack, set in the aliases):

```bash
clojure -M:test -n spindel.v2.oracle-test     # engine logs against the model
clojure -M:test -n spindel.v2.top-test        # layer-1 headline; loads all of layer 1
clojure -M:test -n spindel.v2.sys-test        # layer 2; loads layer 1 and layer 2
clojure -M:test                               # everything, tens of minutes
```

New log samples are generated from the engine by `test/spindel/v2/oracle/gen/` (each generator's header
says how to run it).

## Notes

- `notes/LAYER2.md`: the design note for layer 2.
- `notes/ansatz-fixes.md`: the ansatz gaps found by the model and the obligations tracker;
  `notes/ansatz-gaps.md`: their repros.
- `notes/history/PLAN.md`: the journal of the proof campaign in order (per branch: what was proved,
  model changes, questions to and answers from the engine session).
- `notes/hm13-contracts.edn`, `notes/hm14-contracts.edn`: working contracts of two h-mem2 stages.
