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
system of cells, each holding one layer-1 world (`spindel.v2.layer2.sys`).

- `sys-reach-inv`: every system reachable from an initial one (`SysReach`: `init` and one constructor
  per operation, 29, each with the guard the engine guarantees as a premise) satisfies `sysinv`
  (`spindel.v2.layer2.top`): every live world and every live publication's basis satisfies `inv`; a
  live complete cell is ready (released, no run, every kid done, no marker); every live world is
  quiet-compatible; the host joins are well formed.
- `sys-reach-rinv` (Z#77, LOC3): in every reachable system, a cell whose fork-local retirement is
  pending has processed no item.

**Physical representation.** `mv-refinement` (`spindel.v2.layer2.mvcc`): in every state of the MVCC
row heap reachable by the engine's operations (write, own-copy, create, fork, instance, prune, finish,
drop, collect), every active world reads every id exactly as the value-copy model has it. So layer 2's
value copies are a sound abstraction of the way the engine shares rows between forks.

## How the step proof works

The headline `inv-step` (every step keeps `inv`) is a large proof. This section gives its idea, then the
names, then a reading list. `notes/proof-layout.md` has the measurements behind the numbers and the plan
for making the proofs read the way this section describes them.

### The idea

Think of one world-step as a database transaction and of `inv` as its integrity constraints. `inv` must
hold at commit: in the world before the step and in the world after it. Nobody sees a world in the middle
of a step: the engine commits whole steps, no other world reads a half-done one, and the oracle compares
committed states only. So inside a step the proof may let a constraint fail for a few named ids, provided
the same step repairs them before it ends. That is a constraint declared `DEFERRABLE INITIALLY DEFERRED`,
or an `ON DELETE CASCADE` that deletes row by row and is consistent again only when the cascade is done.

The proof has four layers.

1. **A step is a raw transition followed by Rule R.** `world-step w it = finish (raw w it)`. `raw` applies
   the item (`raw0`, a case split over the 49 constructors of `Item`; then `post` cancels the losers of an
   accepted await). `finish` runs Rule R (`rule-r`: rounds of `normalize` then `rule-r-filter`, bounded
   by fuel) if the item was accepted, and keeps the input world if it was refused.
2. **Every transition is glue around primitive edits.** The glue is case splits on a lookup or a guard,
   sequencing, folds over a list, and loops bounded by fuel (the cancel cascade, normalization, Rule R's
   rounds, the finalizer loop). The primitive edits are 39 small table edits: insert, delete or update a
   row of one table; mark, unmark, remove or insert an edge; bump the allocator; `set-pins`,
   `set-released`, `set-pending-act`; and Rule R's `filter-world`. The base proof `step-inv` reaches them
   through about 220 composite lemmas, with 154 call sites of primitives.
3. **`inv` is a base plus parts.** The base is `inv-sample` (`edits`): exact pending counts, every edge
   references existing rows of the right kind, ids are unique and below the allocator. On top of it sit
   about 45 *parts*, each a Bool predicate on a world, for example `gl-rest` (I10, task part) or
   `g8-rest` (I8). A part together with the base is a *bundle*: `gl w = inv-sample w && gl-rest w`.
4. **A part survives each primitive edit for one of four reasons.**
   - **Frame.** The edit does not change what the part reads. `g1` (I1, scope parents) reads only the
     scope table, so every edit of runs, tasks or edges keeps it, by `rfl`. About two thirds of the
     (edit, part) pairs are frames.
   - **Local obligation.** The edit changes what the part reads, and a short argument at that edit shows
     that the part still holds. The argument may use the base, the part itself, the facts on the path to
     the edit (a guard that was checked, a row that was found) and companion parts (below). Example: a new
     scope keeps `g1` if its parent exists (`g1-scope-ins-fresh`); at T16's open that premise comes from
     the guard `open-ok` on the path, at a run's new scope from `task-scope-parent`.
   - **Deferred within a step.** An edit breaks the part for a named set of ids, and a later edit of the
     same step repairs it. The part then has an *exempt form* with that set as a parameter: `Q[X]`, with
     `Q = Q[∅]`. The set holds the pending deferred violations and is empty at commit. Example: T14
     cancels a run, and for a moment its task has neither a result nor an alive run, which `gl` forbids.
     `glx-kill` weakens `gl` to `glx k` (task `k` exempt), and `gl-task-done-x` gives back `gl` when the
     task gets its result, in the same transition (`gl-cancel-run-local-o`). In a loop the set is ghost
     state equal to the pending work: in the cancel cascade `g8`'s escape list is the runs of the queued
     cancel jobs (`g8-cascade`), and it is empty when the worklist is (P4, `g8-cascade-done`). Deferral is
     per part and per transition, not one relaxed invariant for the whole step: each part has its own
     kind of exempt id (tasks, runs, computations, members), and each violation is repaired inside the
     composite that made it (a raw transition, or one round of Rule R). The literature analogue is seL4's
     `invs_except`.
   - **Companions.** The argument for one part may use other parts of the input world: `g8` needs `ga`
     for P4 (the cascade's worklist empties), `gd` needs `g7` and `g10r`. No part is inductive on its own;
     the conjunction is, because the "uses" relation is acyclic (each part is inductive *relative to* the
     parts before it).

Each part has a step theorem `step-<part>`: from the part, its companions and `rule-r-safe (raw w it)`
(P3: Rule R's filter is safe), the part holds after the step. The chain links `p3b` … `p3m` (below)
conjoin the parts in one order that respects the companions, and `inv-step` is the last link plus the
invariants proved alongside the chain.

**Companions** (the premises of `step-<part>` besides the part itself and `rule-r-safe`; `rule-r-safe`
comes from `p3b` by `step-rule-r-safe`):

| Part | Companions | Part | Companions |
|------|------------|------|------------|
| `ga`, `inv-rank`, `g9`, `mdb`, `esb`, `gw`, `g1`, `g5`, `gso`, `ekb`, `svb` | none | `gd` | `g7`, `g10r` |
| `gl`, `g7`, `aha`, `gr0`, `g8` | `ga` | `v14` | `ga`, `gy`, `g7`, `inv-rank` |
| `gy`, `ar` | `ga`, `g7` | `hmk` | `ga`, `gy`, `g7`, `gd`, `g10r`, `inv-rank`, `v14` |
| `g10r` | `p3b` (all of `ga`, `inv-rank`, `gl`, `g9`, `ri`) | `h3` | `p3la` (every part above, with `ar` and `ekb`) |

### How the code expresses it today

The proofs are not written part by part and edit by edit. A bundle's step theorem is obtained by
re-checking the base proof once per bundle (`spindel.v2.pres.part`):

- `mk-bundle` declares a bundle and its parameters (an exemption set such as `g8`'s escape list `x8s`, or
  a fixed id that a helper bundle talks about).
- `prim!` fills one cell: the base lemma of one primitive edit, plus a proof of the part. `nil` means a
  frame, proved by `rfl`. Hand lemmas renamed into the bundle (`swap! (:renames B) …`) fill cells that need
  an extra premise.
- `lcopy!` copies every composite lemma of the base proof that `step-inv` needs, with `inv-sample`
  replaced by the bundle and every callee by its copy: the glue is re-checked once per bundle.
- `override!` replaces the copy of one composite lemma by a hand proof. Overrides are where a part is
  deferred within a step (they use an exempt form), and where a leaf needs a fact the base proof does not
  pass down (a guard, a found row, a companion): then every lemma from the item down to that leaf is
  overridden to pass it.
- `patch!` rewrites the text of a base proof before it is copied, for the same purpose.

So the four reasons appear as: frames are the `nil` cells (969 of the 1,357 cells), and since the
declarations below mostly generated cells (`frame!`); local obligations are the other cells and some
overrides; deferred violations are overrides that use an exempt form;
companions are bundle premises passed down by patches and overrides. About 10,000 of the 16,119
theorems in the environment are copies. `notes/proof-layout.md` gives the counts and the target layout,
in which a part declares what it reads (frames follow), its exempt form, and only the cells and
composites that matter to it.

**Declarations (stage 1 of that plan).** Most parts of the chain are now declared through a front end
that emits the same copier calls:

- `spindel.v2.pres.frames` states what every primitive edit writes (`writes-<edit>`: the edited world is
  the input world with only those fields replaced) and, through `defview`, what a part reads
  (`<rest>-frame-<field>`: replacing a field outside the view leaves the part unchanged, by `rfl`).
- `defpart` (`pres.part`) declares a part's view and the cells that need an argument; every other
  primitive's cell is generated from the two lemmas above (`frame!`). So a part's declaration lists only
  the edits that write what it reads, e.g. `(defpart G1 :reads '[scopes] :cells {...})`.
- `spindel.v2.pres.exempt` records each exemption form (`defexempt`): its exempt ids and its empty
  instance at commit, with uniform aliases `<part>-exempt-<role>` (`break`, `repair`, `mono`, `loop`,
  `exit`, `transport`) for the lemmas that open and close deferred violations.

- `spindel.v2.pres.tree` checks every composite lemma of the base proof once, over an abstract part Q,
  by open recursion: `pres-<x>` proves x for Q from one hypothesis per lemma x's proof calls. An update
  primitive is one hypothesis per row function (a *site*: `run-upd` at `run-wake` is not `run-upd` at
  `run-tick`). `restate!` gives a part its generated lemmas as applications of the generic ones, with
  the part's own lemma for every callee. The part's table (`part!`) declares where its own proof
  replaces the generic one, and the facts it takes from the path (the run is a row, a guard, a
  companion) with the terms that pass them; the nodes on those paths get the part's own generic lemma
  (`pres-<x>@<part>`). On the tree so far: `gl` (`inv.i10-task`), `g9` (`inv.i9-res`), `g8` (`inv.i8`),
  `g7` (`inv.idle`), `gd` (`inv.comp-facts`), `hmk` (`inv.marks`), `gy` (`inv.tomb`), `gcy`
  (`inv.acyclic`), `g1` (`inv.i1-scopes`), `gw` (`inv.i11`), `mdb`, `esb`, `aha` and `svb` (`inv.base`), `g10` and `g10r` (`inv.i10`), `g5` (`inv.i5`), `nzb` and `gso`
  (`inv.i1-owners`), `grx` and `gr0` (`inv.i1-runs`), `gox` and `gos`
  (`completion.open-scopes`), `vq` and `vr` (`inv.i14`), `mb` (`progress.measures`), `grel`, `gc` and `gst`
  (`completion`) and the companions `awo`, `edb`, `gnf`, `hkw`, `hsw`, `kc`, `kdb`, `krb`, `kx`,
  `mdk`, `na`, `neb`, `nq` (notes/proof-layout.md sections 5b–5s).

`gl` (`inv.i10-task`), `g9` (`inv.i9-res`), `g1` (`inv.i1-scopes`) and `g8` (`inv.i8`) carry a fixed comment block before
their declaration: the part in words, its view, its exempt form, its cells, where it is deferred within
a step, and its companions.

### Reading list: the whole proof in 14 stops

Kernel names are global; find a name with `grep -rn "(a/theorem NAME \["` (or `a/defn`) under `src/`.

1. `inv`, `inv-step`, `Reach1`, `reach-inv` (`top`): the headline and its four-line induction.
2. `World` (`state`), `Item` (`step`): the state (11 row tables, `pins`, `pending-act`, `released`,
   `next-id`) and the 49 items.
3. `world-step`, `raw`, `post`, `finish`, `raw0` (`engine`), `rule-r`, `rule-r-round` (`rule`): what a
   step is.
4. `inv-sample`, `inv-parts`, `inv-intro` (`edits`): the base every part sits on.
5. `step-inv` → `raw0-inv` (`engine`) → `inv-cancel-run-local` (`rule`) → `inv-run-upd`: the base proof
   from an item down to one primitive edit.
6. `filter-safe-of-refs` (`inv.copier`), `step-rule-r-safe` (`inv.base`): P3, Rule R's filter is safe;
   the premise every part shares.
7. `p3b`, `step-p3b` (`inv.base`): how parts are assembled with their companions.
8. `step-gl` (`inv.i10-task`): one part's step theorem: a refused item, then raw, then Rule R, with the
   companion `ga`.
9. `gl-rest`, `l10k`, `kw`, `gl-rest-kw` (`inv.copier`): a part, its view (what it reads) and its frame.
10. `glx`, `glx-kill`, `gl-task-done-x` (`inv.copier`), `gl-cancel-run-local-o` (`inv.i10-task`): a
    violation deferred within a step: its break and its repair.
11. `mk-bundle`, `prim-form`, `copy-subst`, `lcopy!` (`pres.part`): how most parts reuse the base proof
    today; `pres-form`, `restate!`, `part!` (`pres.tree`): how `gl` does, from the generic tree.
12. `g8-close-local`, `g8-cascade`, `g8-cascade-done` (`inv.i8`), `casc-done-ga` (`inv.acts`): an
    exemption set as ghost state in a loop, emptied by P4.
13. `step-p3m`, `l5-safety-total` (`inv.members.step`): the end of the chain and what it buys (L5's
    safety half). The `inv.members.bundle` docstring describes `h3`, the most complex part.
14. `notes/generic-preservation.md` and its prototype: proving the glue once over an abstract part
    instead of once per bundle.

## Map of the namespaces

Namespaces are `spindel.v2.<name>` in `src/spindel/v2/<name>.clj` (a `.` in the name is a directory,
a `-` is `_` in the file name). Kernel names are global: a theorem is `step-p3m`, not
`spindel.v2.inv.members.step/step-p3m`, so moving a namespace changes no statement.

| Part | Namespaces | What |
|------|------------|------|
| Transition system | `state`, `edits`, `reach`, `retain`, `step`, `rule`, `engine` | tables and rows; primitive table edits and the base invariant `inv-sample`; least fixpoints and worklists; retention (`live`, storage, Rule R's filter); the `Item` type and raw transitions; Rule R and the cancel family; the transitions that create runs, `raw` and `world-step` |
| | `ledger`, `owned` | the task/scope completion ledger (derived); owned forks as world operations |
| Predicates | `inv`, `local` | one executable Bool predicate per invariant of spec §6 (the tripwires the oracle runs), the spec's literal readings `lit-*`, I13 as guard lemmas, L1, I9 and I10's slice half; Z#77's LOC1/LOC2 |
| Headline, layer 1 | `top` | `inv`, `inv-step`, `Reach1`, `reach-inv` |
| Layer-1 invariant proofs | `inv.*` | the bundle chain `p3b ⊂ … ⊂ p3m` (next section), one namespace per invariant |
| | `inv.members.*` | h-mem2 (the bundle `h3`, P11), one namespace per group of transitions |
| Progress | `progress.*` | fuel sufficiency and termination (P1–P12), L2 measures, L5 safety |
| Completion (C1, C1c) | `completion.*` | released and quiet worlds, completion stability, open scopes, draining of inherited markers |
| Layer 2 | `layer2.sys`, `layer2.skip`, `layer2.top` | cells, publications and their operations; an id taken by a sibling world (`bump`); `sysinv`, `SysReach`, `sys-reach-inv` |
| Physical | `layer2.mvcc` | the MVCC row representation (tokens, versions, copy maps), `mv-refinement` |
| Utilities | `util` | function update at a Nat key (`fupd`) |
| Proof layout | `pres.part`, `pres.frames`, `pres.exempt`, `pres.tree` | part definitions: the base proof as data, the bundle record, the primitive cells, `defpart`, and the copier `lcopy!` for the parts not yet on the tree (part); footprints of the primitive edits and views of the parts (frames); the exemption forms and their uniform names; the generic step tree (`pres-<x>`, `part!`, `restate!`) that eight parts use instead of a copy |
| Oracle (tests) | `test/spindel/v2/oracle.clj`, `oracle_test.clj`, `oracle/` | replays commit logs recorded from the engine through the model, compares every committed state |

`inv.*`, in load order (each requires the ones before it that it uses):

| Namespace | Contents |
|-----------|----------|
| `inv.acts` | `ga`: activations (each run's only one, its run parked); the first copier (`copy!`) |
| `inv.copier` | the predicates, cells and lemmas of `gl` (I10 task part) and `g9` (I9 resources); P3's core `filter-safe-of-refs` |
| `inv.rank`, `inv.rank-step` | I12: the raise loop establishes `ranks-ok`; `inv-rank` through every step (P5) |
| `inv.idle` | I7: bundle `g7` (idle shape, no dep edge on an idle creditor) |
| `inv.tomb` | C1 Q6: tombstones are dormant (`gy`) |
| `inv.i10-task`, `inv.i9-res` | `gl` and `g9` on the generic tree (`pres.tree`): their tables and steps |
| `inv.base` | P3's reference facts (`mdb`, `esb`, `aha`, the round invariant `ri`), the first link `p3b`, I5 observe (`svb`) |
| `inv.i10` | I10, computation part (`g10r`), link `p3c` |
| `inv.i11` | I11a (`gw`, `inv-i11a`), link `p3d` |
| `inv.i1-scopes` | I1 scope parents (`g1`), link `p3e` |
| `inv.i5` | I5 dep-final (`g5`), link `p3f` |
| `inv.i1-owners` | I1 owners (`gso`, `i1-own`), P9, link `p3g` |
| `inv.i1-runs` | I1 resource owners, run entities and scopes (`gr0`), all of I1 (`inv-i1`), link `p3h` |
| `inv.i8` | I8 closed scopes (`g8`), link `p3i` |
| `inv.comp-facts` | per-computation facts L5 needs (`gd`), link `p3j` |
| `inv.i14` | I14 validity acyclic (`v14`), P10 reduced to `rso`, link `p3k` |
| `inv.acyclic` | Z#69: scope parents acyclic (`gcy`, `step-acyc`) |
| `inv.marks`, `inv.marks-step` | h-mark (`hmk`, P11 first half), link `p3l` |
| `inv.alive-runs` | AR: an alive run of a computation is its C.run (`ar`, `inv-i10-comp`) |
| `inv.members.bundle` | the h-mem2 bundle `h3`, its transfer and primitive lemmas, first fires, `h3-h-mem2` |
| `inv.members.fires` | every fire keeps `h3` |
| `inv.members.track-take` | T7 track, new activations, take / T17 arm, first cascade pieces |
| `inv.members.cascade` | edge kinds `ekb` (`step-ekb`), freeness monotonicity, the cascade |
| `inv.members.base` | link `p3la` = p3l ∧ `ar` ∧ `ekb` |
| `inv.members.react` | reactivation |
| `inv.members.await-prep`, `-wire`, `-fill`, `-post`, `-guard`, `-raw` | T6 await: preparation, wiring, member installation and fast fills, finalization, the guarded transition, raw await through post and loser cancel |
| `inv.members.dispatch` | T11 dispatch |
| `inv.members.raw-lifts` | raw0 to raw, T22 host await, T8 observe |
| `inv.members.complete` | T12 complete and settle |
| `inv.members.raw` | release-world; `h3` through every raw transition |
| `inv.members.step` | Rule R; `step-h3`, link `p3m`, `step-p3m`, `l5-safety-total` |

`progress.*`: `casc` (P4 cascade completion, P2 normalization), `react` (P8 reactivation, P6
validation walk), `measures` (L2 join measure, L5 safety under the three state facts), `l5` (L5 on step
worlds, P7 settle), `z59` (Z#59: T11 consumes the earliest fired dep edge).

`completion.*`: `quiet` (released stays released; bundles `grel`, `gk`), `quiet-world` (a quiet world
stays quiet; `qinv`, I3's `i3`), `stable` (completion is stable, Z#70), `open-scopes` (every open
non-root scope is in a run's subtree), `drained` (`[:normalize]` leaves no inherited marker).

### Old namespace names

The namespaces were named after the proof campaign that produced them until 2026-11-18; notes, commit
messages and messages from that time use the old names. Kernel names did not change.

| Old | New | Old | New |
|-----|-----|-----|-----|
| `acts` | `inv.acts` | `hm3` | `inv.members.bundle` |
| `lit` | `inv.copier` | `hm4` | `inv.members.fires` |
| `rank` | `inv.rank` | `hm5` | `inv.members.track-take` |
| `rank-step` | `inv.rank-step` | `hm6` | `inv.members.cascade` |
| `idle` | `inv.idle` | `hm6-base` | `inv.members.base` |
| `tomb` | `inv.tomb` | `hm7` | `inv.members.react` |
| `p3` | `inv.base` | `hm8` | `inv.members.await-prep` |
| `i10` | `inv.i10` | `hm9` | `inv.members.await-wire` |
| `i11` | `inv.i11` | `hm10` | `inv.members.await-fill` |
| `i1` | `inv.i1-scopes` | `hm11` | `inv.members.await-post` |
| `i5` | `inv.i5` | `hm12` | `inv.members.await-guard` |
| `i1o` | `inv.i1-owners` | `hm13` | `inv.members.await-raw` |
| `i1r` | `inv.i1-runs` | `hm14` | `inv.members.dispatch` |
| `i8` | `inv.i8` | `hm15` | `inv.members.raw-lifts` |
| `hm` | `inv.comp-facts` | `hm16` | `inv.members.complete` |
| `i14` | `inv.i14` | `hm17` | `inv.members.raw` |
| `acyc` | `inv.acyclic` | `hm18` | `inv.members.step` |
| `hmk` | `inv.marks` | `casc` | `progress.casc` |
| `hmk2` | `inv.marks-step` | `react` | `progress.react` |
| `ar` | `inv.alive-runs` | `progress` | `progress.measures` |
| `quiet` | `completion.quiet` | `l5` | `progress.l5` |
| `qworld` | `completion.quiet-world` | `z59` | `progress.z59` |
| `lstab` | `completion.stable` | `sys` | `layer2.sys` |
| `oscope` | `completion.open-scopes` | `skip` | `layer2.skip` |
| `drained` | `completion.drained` | `systop` | `layer2.top` |
| `cow` | retired (superseded by `layer2.mvcc`; `fupd` is in `util`) | `mvcc` | `layer2.mvcc` |

Unchanged: `state`, `edits`, `reach`, `retain`, `step`, `rule`, `engine`, `ledger`, `owned`, `inv`,
`local`, `top`. Test namespaces follow (`spindel.v2.hm13-test` is `spindel.v2.inv.members.await-raw-test`).

## The invariant: bundles and the chain

`inv-sample w` (`edits`) is the base of every proof: exact pending counts, every edge's creditor and
debtor exist and have the right kind, ids are unique and below the allocator. A *bundle* is
`inv-sample w && rest w`. Its step theorem is built from one lemma per primitive table edit (the rest
part under that edit) and then carried over every composite lemma of `step-inv` by a source-level lemma
copier (`pres.part`: `mk-bundle`, `prim!`, `lcopy!`; `override!` supplies a hand proof for a
transition whose rest part is not compositional, `patch!` adds a premise to a source proof). Every copy
is kernel-checked.

The bundles form one chain, one link per proof campaign. Each link is `(Bool.and previous new)` and has
`step-<link> : link w -> link (world-step w it)` and `<link>-empty`:

| Link | Adds | Spec | Namespace |
|------|------|------|-----------|
| p3b | `ga` activations, `inv-rank` ranks, `gl` task runs, `g9` resources, `ri` the facts every Rule R round needs: `g7` idle shape, `mdb` marked edges are dep edges, `esb` references are no edge ids, `aha` activations' runs are alive, `gy` tombstones are dormant | I12, I10 (tasks), I9 (resources), I7, P3 | `inv.base` (parts from `inv.acts`, `inv.rank-step`, `inv.copier`, `inv.idle`, `inv.tomb`) |
| p3c | `g10r` computation runs (a run's epoch, the current run) | I10 | `inv.i10` |
| p3d | `gw` root scope and fork markers, `inv-i11a` retention | I11a | `inv.i11` |
| p3e | `g1` scope parents | I1 | `inv.i1-scopes` |
| p3f | `g5` no armed dep edge on a final debtor | I5 | `inv.i5` |
| p3g | `gso`, `i1-own` owners of tasks, computations, sources | I1 | `inv.i1-owners` |
| p3h | `gr0` resource owners, run entities and scopes, a done run has a cleanup entry | I1, I4 | `inv.i1-runs` |
| p3i | `g8` closed scopes | I8 | `inv.i8` |
| p3j | `gd` per-computation facts (done-epoch, C.run) | L5 | `inv.comp-facts` |
| p3k | `v14` validity graph acyclic, no dep edge on an idle debtor | I14, I7 | `inv.i14` |
| p3l | `hmk` h-mark: a marked edge is a dep edge on a waiting computation | L5 (P11) | `inv.marks-step` |
| p3la | `ar` alive runs of a computation are its C.run, `ekb` edge kinds | I10, I9 | `inv.members.base` |
| p3m | `h3` h-mem2: the unfilled members of current computation runs | L5 (P11), I2 | `inv.members.step` |

`inv = p3m && svb && inv-i9 && inv-i10-slice && i3` adds the invariants proved alongside the chain:
`svb` I5 observe (`inv.base`), `inv-i9` I9 activations and `inv-i10-slice` D0 (`inv`), `i3` I3
(`completion.quiet-world`).

The link and bundle names (`p3b`..`p3m`, `ga`, `gl`, `g9`, `gd`, `v14`, ...) record the history of the
proof (`p3` was obligation P3). They are kernel names, reused as prefixes of thousands of generated
theorem names, so they are kept; read `inv` and this table instead.

## Invariant table

Status: **proved**: a theorem from `inv`, or a step theorem whose only premise is its bundle;
**partial**: some clauses proved, the rest named; **oracle only**: an executable predicate checked on
replayed engine states, no theorem; **open**: neither; **out of scope**: not modelled, by design.

| Spec | Predicate | Theorem (namespace) | Status |
|------|-----------|---------------------|--------|
| I1 ownership | `inv-i1`, `lit-i1-scope`, `i1-own`, `i1-runs` | `step-lit-i1-total` (`inv.i1-runs`), `step-lit-i1-scope-total` (`inv.i1-scopes`), `step-lit-i1-owners-total` (`inv.i1-owners`) | proved (model readings Z#23, Z#25, Z#26) |
| I2 referential integrity | `edges-ref-ok` (in `inv-sample`), `aha`, member facts of `h3` | `step-inv-total`, `step-p3b` (`inv.base`), `step-p3m` (`inv.members.step`) | partial: "every basis member exists or is idle" and the member edges of activations of task runs or stale computation runs are not covered |
| I3 liveness | `i3` | `step-i3-inv` (`completion.quiet-world`); part of `inv` | proved |
| I4 work reachable | `normalized-runs`, `r3-ok` (in `gr0`) | `step-i4-p3` (`inv.base`, accepted steps; a refusal changes nothing), `step-p3h` (`inv.i1-runs`) | proved |
| I5 consumption | `wait-cred-ok`, `lit-i5-dep-final`, `svb` | `step-i5-wait` (`inv`), `step-lit-i5-dep-final-total` (`inv.i5`), `step-svb-total`, `step-i5-total` (`inv.base`) | proved |
| I6 continuation placement | none | none | out of scope: continuations are opaque ids |
| I7 idle shape | `inv-i7`; `dna` (in `v14`); `lit-i7-basis` | `step-lit-i7-total` (`inv.base`) | partial: the empty-basis clause `lit-i7-basis` is oracle only; wait or observe edges on an idle computation are not excluded by a proved predicate |
| I8 closed scopes | `lit-i8-runs`, `lit-i8-sources` | `step-lit-i8-total` (`inv.i8`) | proved, under the model-only guard `cur-closed` (P10, open) |
| I9 unwinding | `inv-i9`, `lit-i9-res`, `ekb` | `step-i9` (`inv`), `step-lit-i9-res-total` (`inv.base`), `step-ekb` (`inv.members.cascade`) | proved for synchronous finalizers (Z#66 is not modelled) |
| I10 runs | `lit-i10-current`, `inv-i10-comp`, `inv-i10-task`, `inv-i10-slice` | `step-lit-i10-current-total` (`inv.i10`), `ar-i10-comp` (`inv.alive-runs`), `step-lit-i10-task-total` (`inv.base`), `step-i10-slice` (`inv`) | proved |
| I11a retention from obligations | `inv-i11a` | `step-i11a-total` (`inv.i11`) | proved (the Z#66 obligations are not modelled) |
| I11b bounded fan-out | none | none | out of scope: a census gate |
| I12 rank | `ranks-ok` (in `inv-rank`) | `step-ranks` (`inv.rank-step`), `step-rank-total` (`inv.base`) | proved for the order; "refuses with ::cycle iff the propagation reaches the debtor" is open (T6 also refuses when the raise loop runs out of fuel) |
| I13 coherence as guards | guard lemmas | `i13-fire-dep-live`, `i13-fire-dep-stale`, `i13-fire-wait-stale`, `i13-complete-stale`, `i13-complete-raw-stale` (`inv`) | partial: a wait edge on a computation debtor has no liveness lemma |
| I14 validity acyclic | `vsucc14`, `v14` | `step-i14-total` (`inv.i14`) | proved |
| I15 coherence of results | none | none | open (not modelled) |
| I16 / LOC1, run half: a run of a fork-local task has a fork-local run scope | `loc1-run` | `loc1-runs` (`local`) | proved (in every world) |
| I16 / LOC1, task half: a task owned by a fork-local scope is fork-local | `loc1-task` | none | **open** as part of `inv`; oracle only (fork-local samples 51-60) |
| I16 / LOC2: no fork marker is owned by a fork-local scope | `loc2` | none | **open** as part of `inv`; oracle only (samples 51-60) |
| I16 / LOC3: a pending retirement precedes every item | `rinv` | `sys-reach-rinv` (`layer2.top`) | proved |
| Z#77 `retire-clean` / `retire-quiet`: after `[:retire-local]` no run of a fork-local task, no cleanup entry, every fork-local task done | executable form in `oracle_test` (`fork-local-closure`) | none | **open** as theorems; checked on the replayed sample worlds only |
| Z#69 scope parents acyclic | `scopes-acyclic` | `step-acyc` (`inv.acyclic`) | proved (alongside p3b; not part of `inv`) |
| L1 prompt reclamation | — | `step-l1`, `step-l1-comp`, `step-l1-run` (`inv`) | proved in state form, with `live-converged`/`normalized` premises that P1/P2 discharge; no packaged form |
| L2 join | measure `mu-f`, bundle `mb` | `step-mu-le`, `finally-exit-dec`, `slice-exit-retires`, `ack-dec`, `ack-retires` (`progress.measures`) | partial: fair termination is a paper argument; Z#66 is not modelled |
| L3 serial execution | `inv-i10-slice` | `step-i10-slice`, `step-d0` (`inv`) | partial: sequential by construction (D0); host ingress is not modelled |
| L4 no resurrection | `raw-token-ok` | `step-l4` (`engine`) | proved |
| L5 admission, safety half | `quiescent`, `comp-waiting` | `l5-safety-total` (`inv.members.step`) | proved; its third disjunct is "a parked task in the cone that is not blocked" (that this is a cyclic wait is a paper step); the liveness half is a paper argument |

**Layer 2.** `sys-reach-inv` (`layer2.top`) gives, in every reachable system: `sinv` (F5: every live
world satisfies `inv`), `pinv` (every live publication's basis does), `cinv` (completion soundness),
`qsinv`/`qpinv` (quiet-compatible), `jinv` (host joins). Caveats: the merge takes its basis as a free
argument (there is no `Cell.mbase`), so `SysReach`'s merge admits any basis; guards that layer 2 does
not have (a fork of a released world, a merge without a parent relation, a join on any id) are not
premises either. `layer2.mvcc`'s refinement is to its own ghost value-copy tables, not to
`layer2.sys`'s cells.

### Progress obligations

| # | Obligation | Status | Theorem (namespace) |
|---|---|---|---|
| P1 | live worklist fuel sufficiency | proved | `live-converged-all` (`retain`) |
| P2 | normalization terminates and ends normalized | proved | `normalized-ok`, `rule-r-normalized-ok` (`progress.casc`) |
| P3 | Rule R's filter is safe | proved | `filter-safe-of-refs` (`inv.copier`), `step-rule-r-safe` (`inv.base`) |
| P4 | cascade completion | proved | `casc-done-ok` (`progress.casc`) |
| P5 | I12 ranks kept | proved | `step-rank`, `step-ranks` (`inv.rank-step`) |
| P6 | §3.4 validation walk within fuel | proved | `valid-done-ok` (`progress.react`) |
| P7 | settle worklist within fuel | proved | `settle-done-ok` (`progress.l5`) |
| P8 | reactivation worklist within fuel | proved | `react-done-ok` (`progress.react`) |
| P9 | Rule R's loop ends with no orphans | proved | `rule-r-no-orphans` (`inv.i1-owners`) |
| P10 | the raw0 guard `cur-closed` never fires | **open**; reduced to `rso` (an alive normal task run's run scope is open), which the tests check | `cur-open-of-run-scope`, `cur-open-of-rso` (`inv.i14`) |
| P11 | h-mark and h-mem2 are step invariants | proved | `step-h-mark-total` (`inv.marks-step`), `step-h-mem2-total`, `l5-safety-total` (`inv.members.step`) |
| P12 | I14 acyclic | proved | `step-i14-total` (`inv.i14`) |

Fuel with no sufficiency theorem (fuel is a parameter, convergence a checked flag): the I12 raise loop
(an exhausted raise refuses T6), Derive/blocked (`blocked-complete` assumes `blocked-converged`), the
dirty cone and `cur-scope`.

## Trust boundary

- **Kernel.** Every statement is checked by the ansatz kernel (a port of Lean 4's) when its namespace
  loads. Generated theorems (the copier's) are checked like hand-written ones.
- **Model against spec.** The model's predicates and transitions are read against
  `docs/engine-v2-spec.md`; the namespaces' docstrings name the spec items they cover and list the
  readings where the model differs from the spec's wording (engine.clj's B1-B10, rule.clj's readings,
  inv.clj's predicates).
- **Model against engine: the oracle.** The engine is not verified. `test/spindel/v2/oracle.clj` replays
  commit logs recorded from the engine (samples 1-60 in `test/spindel/v2/oracle/`, generated by
  `oracle/gen/`) through `world-step` and the layer-2 operations, and compares every committed state
  (id-keyed tables) and every refusal. On every accepted step it checks Rule R's flags and the
  executable invariants `inv-all` and `lit-all` (tripwires). `inv` itself is evaluated on every world of
  samples 4, 5 and 13 (`top_test`), not on every replayed world. A divergence fails the test.
- **Premises of the reachability inductives** (`SysReach`, `layer2.mvcc`'s `MReach`) are the guards the
  engine guarantees. They are assumptions about the engine, checked only through the oracle.

## Running

From this directory (ansatz comes from Clojars; the proofs need a large stack, set in the aliases):

```bash
clojure -M:test -n spindel.v2.oracle-test          # engine logs against the model
clojure -M:test -n spindel.v2.top-test             # layer-1 headline; loads all of layer 1
clojure -M:test -n spindel.v2.layer2.sys-test      # layer 2; loads layer 1 and layer 2
clojure -M:test                                    # everything, tens of minutes
```

Loading every namespace (the whole model, kernel-checked) takes about 8 minutes.

New log samples are generated from the engine by `test/spindel/v2/oracle/gen/` (each generator's header
says how to run it).

## Notes

- `notes/LAYER2.md`: the design note for layer 2.
- `notes/ansatz-fixes.md`: the ansatz gaps found by the model and the obligations tracker;
  `notes/ansatz-gaps.md`: their repros.
- `notes/history/PLAN.md`: the journal of the proof campaign in order (per branch: what was proved,
  model changes, questions to and answers from the engine session). It uses the old namespace names.
- `notes/proof-layout.md`: how to make the preservation proofs readable: the proof idea of "How the step
  proof works" with measurements, the options (views and frames, exemption forms for deferred
  violations, a generic step tree, transition summaries), the target layout, staging and risks.
- `notes/generic-preservation.md`: replacing the lemma copier by one generic preservation theorem over a
  structure of per-primitive obligations; a prototype (`notes/generic-preservation-proto.clj`) and the path.
- `notes/hm13-contracts.edn`, `notes/hm14-contracts.edn`: working contracts of two h-mem2 stages
  (`inv.members.await-raw`, `inv.members.dispatch`).
