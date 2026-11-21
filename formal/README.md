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
- `reach-inv`: every world reachable from the empty world by steps (`WorldReach`) satisfies `inv`.
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

1. **A step is a raw transition followed by Rule R.** `world-step w it = then-rule-r (raw w it)`. `raw` applies
   the item (`transition`, a case split over the 49 constructors of `Item`; then `then-cancel-losers` cancels the losers of an
   accepted await). `then-rule-r` runs Rule R (`rule-r`: rounds of `normalize` then `rule-r-filter`, bounded
   by fuel) if the item was accepted, and keeps the input world if it was refused.
2. **Every transition is glue around primitive edits.** The glue is case splits on a lookup or a guard,
   sequencing, folds over a list, and loops bounded by fuel (the cancel cascade, normalization, Rule R's
   rounds, the finalizer loop). The primitive edits are 39 small table edits: insert, delete or update a
   row of one table; mark, unmark, remove or insert an edge; bump the allocator; `set-pins`,
   `set-released`, `set-pending-act`; and Rule R's `filter-world`. The base proof `step-well-formed` reaches them
   through about 220 composite lemmas, with 154 call sites of primitives.
3. **`inv` is a base plus parts.** The base is `well-formed` (`edits`): exact pending counts, every edge
   references existing rows of the right kind, ids are unique and below the allocator. On top of it sit
   about 45 *parts*, each a Bool predicate on a world, for example `i10-task-rest` (I10, task part) or
   `i8-closed-rest` (I8). A part together with the base is a *bundle*: `i10-task w = well-formed w && i10-task-rest w`.
4. **A part survives each primitive edit for one of four reasons.**
   - **Frame.** The edit does not change what the part reads. `i1-scopes` (I1, scope parents) reads only the
     scope table, so every edit of runs, tasks or edges keeps it, by `rfl`. About two thirds of the
     (edit, part) pairs are frames.
   - **Local obligation.** The edit changes what the part reads, and a short argument at that edit shows
     that the part still holds. The argument may use the base, the part itself, the facts on the path to
     the edit (a guard that was checked, a row that was found) and companion parts (below). Example: a new
     scope keeps `i1-scopes` if its parent exists (`i1-scopes-scope-ins-fresh`); at T16's open that premise comes from
     the guard `open-ok` on the path, at a run's new scope from `task-scope-parent`.
   - **Deferred within a step.** An edit breaks the part for a named set of ids, and a later edit of the
     same step repairs it. The part then has an *exempt form* with that set as a parameter: `Q[X]`, with
     `Q = Q[∅]`. The set holds the pending deferred violations and is empty at commit. Example: T14
     cancels a run, and for a moment its task has neither a result nor an alive run, which `i10-task` forbids.
     `i10-task-exempt-kill` weakens `i10-task` to `i10-task-exempt k` (task `k` exempt), and `i10-task-task-done-x` gives back `i10-task` when the
     task gets its result, in the same transition (`i10-task-cancel-run-local-hand`). In a loop the set is ghost
     state equal to the pending work: in the cancel cascade `i8-closed`'s escape list is the runs of the queued
     cancel jobs (`i8-closed-cascade`), and it is empty when the worklist is (P4, `i8-closed-cascade-done`). Deferral is
     per part and per transition, not one relaxed invariant for the whole step: each part has its own
     kind of exempt id (tasks, runs, computations, members), and each violation is repaired inside the
     composite that made it (a raw transition, or one round of Rule R). The literature analogue is seL4's
     `invs_except`.
   - **Companions.** The argument for one part may use other parts of the input world: `i8-closed` needs `acts-parked`
     for P4 (the cascade's worklist empties), `comp-facts` needs `i7-idle` and `i10-current`. No part is inductive on its own;
     the conjunction is, because the "uses" relation is acyclic (each part is inductive *relative to* the
     parts before it).

Each part has a step theorem `step-<part>`: from the part, its companions and `rule-r-safe (raw w it)`
(P3: Rule R's filter is safe), the part holds after the step. The chain links `chain-start` … `chain` (below)
conjoin the parts in one order that respects the companions, and `inv-step` is the last link plus the
invariants proved alongside the chain.

**Companions** (the premises of `step-<part>` besides the part itself and `rule-r-safe`; `rule-r-safe`
comes from `chain-start` by `step-rule-r-safe`):

| Part | Companions | Part | Companions |
|------|------------|------|------------|
| `acts-parked`, `i12-ranks`, `i9-res`, `marks-on-dep`, `refs-not-edges`, `root-scope-reserved`, `i1-scopes`, `i5-dep-final`, `i1-detached-closed`, `edge-kinds`, `i5-seen` | none | `comp-facts` | `i7-idle`, `i10-current` |
| `i10-task`, `i7-idle`, `act-runs-alive`, `i1-runs`, `i8-closed` | `acts-parked` | `i14-ordered` | `acts-parked`, `tombs-dormant`, `i7-idle`, `i12-ranks` |
| `tombs-dormant`, `alive-run-latest` | `acts-parked`, `i7-idle` | `marks-waiting` | `acts-parked`, `tombs-dormant`, `i7-idle`, `comp-facts`, `i10-current`, `i12-ranks`, `i14-ordered` |
| `i10-current` | `chain-start` (all of `acts-parked`, `i12-ranks`, `i10-task`, `i9-res`, `round-facts`) | `current-members` | `chain-to-edge-kinds` (every part above, with `alive-run-latest` and `edge-kinds`) |

### How the code expresses it today

The proofs are not written part by part and edit by edit. The base proof is checked once more over
an abstract part, and every part's lemmas are that generic proof applied to the part's cells
(`spindel.v2.pres.part`, `spindel.v2.pres.tree`):

- `mk-bundle` declares a bundle and its parameters (an exemption set such as `i8-closed`'s escape list `x8s`, or
  a fixed id that a helper bundle talks about).
- `prim!` fills one cell: the base lemma of one primitive edit, plus a proof of the part. `nil` means a
  frame, proved by `rfl`. Hand lemmas registered in the bundle (`swap! (:renames B) …`) fill cells that
  need an extra premise.
- `restate!` gives the part every composite lemma of the base proof that its step needs, as the
  generic lemma applied to the part's lemma for every callee.
- The part's table (`part!`) says where that is not enough: its own proofs (`:over`: a violation
  deferred within a step, an argument over edits), the row functions that need a lemma (`:sites`), and
  the facts a leaf needs that the base proof does not pass down (a guard, a found row, a companion),
  with the terms that pass them (`:ctx`, `:own`, `:pass`).

So the four reasons appear as: frames are the `nil` cells and the generated frame cells (`frame!`);
local obligations are the other cells and the sites; deferred violations are own proofs that use an
exempt form; companions are facts in a part's table.

Until stage 4 of `notes/proof-layout.md` this was done by a source-level lemma copier (`lcopy!`,
`override!`, `patch!`): the base proof's text was re-checked once per bundle, with a hand proof or a
source rewrite wherever a part needed more (337 overrides, 94 patches). It is deleted; the notes give
the counts before and after.

**Declarations.** A part is declared through a front end:

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
  (`pres-<x>@<part>`). Every part is on the tree: `i10-task` (`inv.i10-task`), `i9-res` (`inv.i9-res`), `i8-closed` (`inv.i8`),
  `i7-idle` (`inv.idle`), `comp-facts` (`inv.comp-facts`), `marks-waiting` (`inv.marks`), `tombs-dormant` (`inv.tomb`), `scope-parents-acyclic`
  (`inv.acyclic`), `i1-scopes` (`inv.i1-scopes`), `root-scope-reserved` (`inv.i11`), `marks-on-dep`, `refs-not-edges`, `act-runs-alive` and `i5-seen` (`inv.base`), `i10-current-exempt` and `i10-current` (`inv.i10`), `i5-dep-final` (`inv.i5`), `owner-count-at-most` and `i1-detached-closed`
  (`inv.i1-owners`), `i1-runs-exempt` and `i1-runs` (`inv.i1-runs`), `open-scopes-have-runs-exempt` and `open-scopes-have-runs`
  (`completion.open-scopes`), `i14-validity-raw` and `i14-validity-rule-r` (`inv.i14`), `l2-measure` (`progress.measures`), `stays-released`, `host-roots-revoked`, `cleanup-runs-exist` and `task-unheld-scope-absent`
  (`completion`), `acts-parked` and `acts-parked-exempt` (`inv.acts`), `alive-run-latest` (`inv.alive-runs`), `current-members`, `edge-kinds` and `members-round-frame`
  (`inv.members`) and the companions `comp-awake-owns-run`, `comp-exists`, `no-dep-edges-of`, `markers-gone`, `dispatch-epoch-kept`, `done-epoch-below`, `awaiting-run-alive`, `edge-kind-kept`, `alive-runs-listed`, `run-retirable`, `edge-debtor-kept`,
  `mark-targets-dep`, `no-act-of-run`, `run-gone`, `i10-current-transport` (notes/proof-layout.md sections 5b–5x).

`i10-task` (`inv.i10-task`), `i9-res` (`inv.i9-res`), `i1-scopes` (`inv.i1-scopes`) and `i8-closed` (`inv.i8`) carry a fixed comment block before
their declaration: the part in words, its view, its exempt form, its cells, where it is deferred within
a step, and its companions.

### Reading list: the whole proof in 14 stops

Kernel names are global; find a name with `grep -rn "(a/theorem NAME \["` (or `a/defn`) under `src/`.

1. `inv`, `inv-step`, `WorldReach`, `reach-inv` (`top`): the headline and its four-line induction.
2. `World` (`state`), `Item` (`step`): the state (11 row tables, `pins`, `pending-act`, `released`,
   `next-id`) and the 49 items.
3. `world-step`, `raw`, `then-cancel-losers`, `then-rule-r`, `transition` (`engine`), `rule-r`, `rule-r-round` (`rule`): what a
   step is.
4. `well-formed`, `well-formed-parts`, `well-formed-intro` (`edits`): the base every part sits on.
5. `step-well-formed` → `well-formed-transition` (`engine`) → `well-formed-cancel-run-local` (`rule`) → `well-formed-run-upd`: the base proof
   from an item down to one primitive edit.
6. `filter-safe-of-refs` (`inv.copier`), `step-rule-r-safe` (`inv.base`): P3, Rule R's filter is safe;
   the premise every part shares.
7. `chain-start`, `step-chain-start` (`inv.base`): how parts are assembled with their companions.
8. `step-i10-task` (`inv.i10-task`): one part's step theorem: a refused item, then raw, then Rule R, with the
   companion `acts-parked`.
9. `i10-task-rest`, `i10-task-keys-ok`, `i10-task-view`, `i10-task-rest-frame` (`inv.copier`): a part, its view (what it reads) and its frame.
10. `i10-task-exempt`, `i10-task-exempt-kill`, `i10-task-task-done-x` (`inv.copier`), `i10-task-cancel-run-local-hand` (`inv.i10-task`): a
    violation deferred within a step: its break and its repair.
11. `mk-bundle`, `prim-form` (`pres.part`): a part's record and its cells; `pres-form`, `restate!`,
    `part!` (`pres.tree`): how every part reuses the base proof, from the generic tree.
12. `i8-closed-close-local`, `i8-closed-cascade`, `i8-closed-cascade-done` (`inv.i8`), `cascade-done-acts-parked` (`inv.acts`): an
    exemption set as ghost state in a loop, emptied by P4.
13. `step-chain`, `l5-safety-total` (`inv.members.step`): the end of the chain and what it buys (L5's
    safety half). The `inv.members.bundle` docstring describes `current-members`, the most complex part.
14. `notes/generic-preservation.md` and its prototype: proving the glue once over an abstract part
    instead of once per bundle.

## Map of the namespaces

Namespaces are `spindel.v2.<name>` in `src/spindel/v2/<name>.clj` (a `.` in the name is a directory,
a `-` is `_` in the file name). Kernel names are global: a theorem is `step-chain`, not
`spindel.v2.inv.members.step/step-chain`, so moving a namespace changes no statement.

| Part | Namespaces | What |
|------|------------|------|
| Transition system | `state`, `edits`, `reach`, `retain`, `step`, `rule`, `engine` | tables and rows; primitive table edits and the base invariant `well-formed`; least fixpoints and worklists; retention (`live`, storage, Rule R's filter); the `Item` type and raw transitions; Rule R and the cancel family; the transitions that create runs, `raw` and `world-step` |
| | `ledger`, `owned` | the task/scope completion ledger (derived); owned forks as world operations |
| Predicates | `inv`, `local` | one executable Bool predicate per invariant of spec §6 (the tripwires the oracle runs), the spec's literal readings `lit-*`, I13 as guard lemmas, L1, I9 and I10's slice half; Z#77's LOC1/LOC2 |
| Headline, layer 1 | `top` | `inv`, `inv-step`, `WorldReach`, `reach-inv` |
| Layer-1 invariant proofs | `inv.*` | the bundle chain `chain-start ⊂ … ⊂ chain` (next section), one namespace per invariant |
| | `inv.members.*` | h-mem2 (the bundle `current-members`, P11), one namespace per group of transitions |
| Progress | `progress.*` | fuel sufficiency and termination (P1–P12), L2 measures, L5 safety |
| Completion (C1, C1c) | `completion.*` | released and quiet worlds, completion stability, open scopes, draining of inherited markers |
| Layer 2 | `layer2.sys`, `layer2.skip`, `layer2.top` | cells, publications and their operations; an id taken by a sibling world (`bump`); `sysinv`, `SysReach`, `sys-reach-inv` |
| Physical | `layer2.mvcc` | the MVCC row representation (tokens, versions, copy maps), `mv-refinement` |
| Utilities | `util` | function update at a Nat key (`fupd`) |
| Proof layout | `pres.part`, `pres.frames`, `pres.exempt`, `pres.tree` | part definitions: the base proof as data, the bundle record, the primitive cells, `defpart` (part); footprints of the primitive edits and views of the parts (frames); the exemption forms and their uniform names; the generic step tree (`pres-<x>`, `part!`, `restate!`) that gives every part its composite lemmas |
| Oracle (tests) | `test/spindel/v2/oracle.clj`, `oracle_test.clj`, `oracle/` | replays commit logs recorded from the engine through the model, compares every committed state |

`inv.*`, in load order (each requires the ones before it that it uses):

| Namespace | Contents |
|-----------|----------|
| `inv.acts` | `acts-parked`: activations (each run's only one, its run parked), with `acts-parked-exempt` (the invariant inside T6 and take); both on the generic tree |
| `inv.copier` | the predicates, cells and lemmas of `i10-task` (I10 task part) and `i9-res` (I9 resources); P3's core `filter-safe-of-refs` |
| `inv.rank`, `inv.rank-step` | I12: the raise loop establishes `ranks-ok`; `i12-ranks` through every step (P5) |
| `inv.idle` | I7: bundle `i7-idle` (idle shape, no dep edge on an idle creditor) |
| `inv.tomb` | C1 Q6: tombstones are dormant (`tombs-dormant`) |
| `inv.i10-task`, `inv.i9-res` | `i10-task` and `i9-res` on the generic tree (`pres.tree`): their tables and steps |
| `inv.base` | P3's reference facts (`marks-on-dep`, `refs-not-edges`, `act-runs-alive`, the round invariant `round-facts`), the first link `chain-start`, I5 observe (`i5-seen`) |
| `inv.i10` | I10, computation part (`i10-current`), link `chain-to-i10-current` |
| `inv.i11` | I11a (`root-scope-reserved`, `inv-i11a`), link `chain-to-i11a` |
| `inv.i1-scopes` | I1 scope parents (`i1-scopes`), link `chain-to-i1-scopes` |
| `inv.i5` | I5 dep-final (`i5-dep-final`), link `chain-to-i5-dep-final` |
| `inv.i1-owners` | I1 owners (`i1-detached-closed`, `lit-i1-own`), P9, link `chain-to-i1-detached-closed` |
| `inv.i1-runs` | I1 resource owners, run entities and scopes (`i1-runs`), all of I1 (`inv-i1`), link `chain-to-i1-runs` |
| `inv.i8` | I8 closed scopes (`i8-closed`), link `chain-to-i8-closed` |
| `inv.comp-facts` | per-computation facts L5 needs (`comp-facts`), link `chain-to-comp-facts` |
| `inv.i14` | I14 validity acyclic (`i14-ordered`), P10 reduced to `rso`, link `chain-to-i14-ordered` |
| `inv.acyclic` | Z#69: scope parents acyclic (`scope-parents-acyclic`, `step-acyc`) |
| `inv.marks`, `inv.marks-step` | h-mark (`marks-waiting`, P11 first half), link `chain-to-marks-waiting` |
| `inv.alive-runs` | AR: an alive run of a computation is its C.run (`alive-run-latest`, `inv-i10-comp`) |
| `inv.members.bundle` | the h-mem2 bundle `current-members`, its transfer and primitive lemmas, first fires, `current-members-h-mem2` |
| `inv.members.fires` | every fire keeps `current-members` |
| `inv.members.track-take` | T7 track, new activations, take / T17 arm, first cascade pieces |
| `inv.members.cascade` | edge kinds `edge-kinds` (`step-edge-kinds`), freeness monotonicity, the cascade |
| `inv.members.base` | link `chain-to-edge-kinds` = chain-to-marks-waiting ∧ `alive-run-latest` ∧ `edge-kinds` |
| `inv.members.react` | reactivation |
| `inv.members.await-prep`, `-wire`, `-fill`, `-post`, `-guard`, `-raw` | T6 await: preparation, wiring, member installation and fast fills, finalization, the guarded transition, raw await through post and loser cancel |
| `inv.members.dispatch` | T11 dispatch |
| `inv.members.raw-lifts` | transition to raw, T22 host await, T8 observe |
| `inv.members.complete` | T12 complete and settle |
| `inv.members.raw` | release-world; `current-members` through every raw transition |
| `inv.members.step` | Rule R; `step-current-members`, link `chain`, `step-chain`, `l5-safety-total` |

`progress.*`: `casc` (P4 cascade completion, P2 normalization), `react` (P8 reactivation, P6
validation walk), `measures` (L2 join measure, L5 safety under the three state facts), `l5` (L5 on step
worlds, P7 settle), `z59` (Z#59: T11 consumes the earliest fired dep edge).

`completion.*`: `quiet` (released stays released; bundles `stays-released`, `host-roots-revoked`), `quiet-world` (a quiet world
stays quiet; `quiet-world-inv`, I3's `i3`), `stable` (completion is stable, Z#70), `open-scopes` (every open
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
| `marks-waiting` | `inv.marks` | `casc` | `progress.casc` |
| `hmk2` | `inv.marks-step` | `react` | `progress.react` |
| `alive-run-latest` | `inv.alive-runs` | `progress` | `progress.measures` |
| `quiet` | `completion.quiet` | `l5` | `progress.l5` |
| `qworld` | `completion.quiet-world` | `z59` | `progress.z59` |
| `lstab` | `completion.stable` | `sys` | `layer2.sys` |
| `oscope` | `completion.open-scopes` | `skip` | `layer2.skip` |
| `drained` | `completion.drained` | `systop` | `layer2.top` |
| `cow` | retired (superseded by `layer2.mvcc`; `fupd` is in `util`) | `mvcc` | `layer2.mvcc` |

Unchanged: `state`, `edits`, `reach`, `retain`, `step`, `rule`, `engine`, `ledger`, `owned`, `inv`,
`local`, `top`. Test namespaces follow (`spindel.v2.hm13-test` is `spindel.v2.inv.members.await-raw-test`).

## The invariant: bundles and the chain

`well-formed w` (`edits`) is the base of every proof: exact pending counts, every edge's creditor and
debtor exist and have the right kind, ids are unique and below the allocator. A *bundle* is
`well-formed w && rest w`. Its step theorem is built from one lemma per primitive table edit (the rest
part under that edit) and then carried over every composite lemma of `step-well-formed` by the generic step
tree (`pres.part`: `mk-bundle`, `prim!`; `pres.tree`: `part!`, `restate!`; the part's table supplies
its own proof for a transition whose rest part is not compositional, and the facts a leaf needs).
Every generated lemma is kernel-checked.

The bundles form one chain, one link per proof campaign. Each link is `(Bool.and previous new)` and has
`step-<link> : link w -> link (world-step w it)` and `<link>-empty`:

| Link | Adds | Spec | Namespace |
|------|------|------|-----------|
| chain-start | `acts-parked` activations, `i12-ranks` ranks, `i10-task` task runs, `i9-res` resources, `round-facts` the facts every Rule R round needs: `i7-idle` idle shape, `marks-on-dep` marked edges are dep edges, `refs-not-edges` references are no edge ids, `act-runs-alive` activations' runs are alive, `tombs-dormant` tombstones are dormant | I12, I10 (tasks), I9 (resources), I7, P3 | `inv.base` (parts from `inv.acts`, `inv.rank-step`, `inv.copier`, `inv.idle`, `inv.tomb`) |
| chain-to-i10-current | `i10-current` computation runs (a run's epoch, the current run) | I10 | `inv.i10` |
| chain-to-i11a | `root-scope-reserved` root scope and fork markers, `inv-i11a` retention | I11a | `inv.i11` |
| chain-to-i1-scopes | `i1-scopes` scope parents | I1 | `inv.i1-scopes` |
| chain-to-i5-dep-final | `i5-dep-final` no armed dep edge on a final debtor | I5 | `inv.i5` |
| chain-to-i1-detached-closed | `i1-detached-closed`, `lit-i1-own` owners of tasks, computations, sources | I1 | `inv.i1-owners` |
| chain-to-i1-runs | `i1-runs` resource owners, run entities and scopes, a done run has a cleanup entry | I1, I4 | `inv.i1-runs` |
| chain-to-i8-closed | `i8-closed` closed scopes | I8 | `inv.i8` |
| chain-to-comp-facts | `comp-facts` per-computation facts (done-epoch, C.run) | L5 | `inv.comp-facts` |
| chain-to-i14-ordered | `i14-ordered` validity graph acyclic, no dep edge on an idle debtor | I14, I7 | `inv.i14` |
| chain-to-marks-waiting | `marks-waiting` h-mark: a marked edge is a dep edge on a waiting computation | L5 (P11) | `inv.marks-step` |
| chain-to-edge-kinds | `alive-run-latest` alive runs of a computation are its C.run, `edge-kinds` edge kinds | I10, I9 | `inv.members.base` |
| chain | `current-members` h-mem2: the unfilled members of current computation runs | L5 (P11), I2 | `inv.members.step` |

`inv = chain && i5-seen && inv-i9 && inv-i10-slice && i3` adds the invariants proved alongside the chain:
`i5-seen` I5 observe (`inv.base`), `inv-i9` I9 activations and `inv-i10-slice` D0 (`inv`), `i3` I3
(`completion.quiet-world`).

The link and bundle names (`chain-start`..`chain`, `acts-parked`, `i10-task`, `i9-res`, `comp-facts`, `i14-ordered`, ...) record the history of the
proof (`p3` was obligation P3). They are kernel names, reused as prefixes of thousands of generated
theorem names, so they are kept; read `inv` and this table instead.

## Invariant table

Status: **proved**: a theorem from `inv`, or a step theorem whose only premise is its bundle;
**partial**: some clauses proved, the rest named; **oracle only**: an executable predicate checked on
replayed engine states, no theorem; **open**: neither; **out of scope**: not modelled, by design.

| Spec | Predicate | Theorem (namespace) | Status |
|------|-----------|---------------------|--------|
| I1 ownership | `inv-i1`, `lit-i1-scope`, `lit-i1-own`, `lit-i1-runs` | `step-lit-i1-total` (`inv.i1-runs`), `step-lit-i1-scope-total` (`inv.i1-scopes`), `step-lit-i1-owners-total` (`inv.i1-owners`) | proved (model readings Z#23, Z#25, Z#26) |
| I2 referential integrity | `edges-ref-ok` (in `well-formed`), `act-runs-alive`, member facts of `current-members` | `step-well-formed-total`, `step-chain-start` (`inv.base`), `step-chain` (`inv.members.step`) | partial: "every basis member exists or is idle" and the member edges of activations of task runs or stale computation runs are not covered |
| I3 liveness | `i3` | `step-i3-inv` (`completion.quiet-world`); part of `inv` | proved |
| I4 work reachable | `normalized-runs`, `r3-ok` (in `i1-runs`) | `step-i4-p3` (`inv.base`, accepted steps; a refusal changes nothing), `step-chain-to-i1-runs` (`inv.i1-runs`) | proved |
| I5 consumption | `wait-cred-ok`, `lit-i5-dep-final`, `i5-seen` | `step-i5-wait` (`inv`), `step-lit-i5-dep-final-total` (`inv.i5`), `step-i5-seen-total`, `step-i5-total` (`inv.base`) | proved |
| I6 continuation placement | none | none | out of scope: continuations are opaque ids |
| I7 idle shape | `inv-i7`; `dna` (in `i14-ordered`); `lit-i7-basis` | `step-lit-i7-total` (`inv.base`) | partial: the empty-basis clause `lit-i7-basis` is oracle only; wait or observe edges on an idle computation are not excluded by a proved predicate |
| I8 closed scopes | `lit-i8-runs`, `lit-i8-sources` | `step-lit-i8-total` (`inv.i8`) | proved, under the model-only guard `cur-closed` (P10, open) |
| I9 unwinding | `inv-i9`, `lit-i9-res`, `edge-kinds` | `step-i9` (`inv`), `step-lit-i9-res-total` (`inv.base`), `step-edge-kinds` (`inv.members.cascade`) | proved for synchronous finalizers (Z#66 is not modelled) |
| I10 runs | `lit-i10-current`, `inv-i10-comp`, `inv-i10-task`, `inv-i10-slice` | `step-lit-i10-current-total` (`inv.i10`), `alive-run-latest-i10-comp` (`inv.alive-runs`), `step-lit-i10-task-total` (`inv.base`), `step-i10-slice` (`inv`) | proved |
| I11a retention from obligations | `inv-i11a` | `step-i11a-total` (`inv.i11`) | proved (the Z#66 obligations are not modelled) |
| I11b bounded fan-out | none | none | out of scope: a census gate |
| I12 rank | `ranks-ok` (in `i12-ranks`) | `step-ranks` (`inv.rank-step`), `step-rank-total` (`inv.base`) | proved for the order; "refuses with ::cycle iff the propagation reaches the debtor" is open (T6 also refuses when the raise loop runs out of fuel) |
| I13 coherence as guards | guard lemmas | `i13-fire-dep-live`, `i13-fire-dep-stale`, `i13-fire-wait-stale`, `i13-complete-stale`, `i13-complete-raw-stale` (`inv`) | partial: a wait edge on a computation debtor has no liveness lemma |
| I14 validity acyclic | `vsucc14`, `i14-ordered` | `step-i14-total` (`inv.i14`) | proved |
| I15 coherence of results | none | none | open (not modelled) |
| I16 / LOC1, run half: a run of a fork-local task has a fork-local run scope | `loc1-run` | `loc1-runs` (`local`) | proved (in every world) |
| I16 / LOC1, task half: a task owned by a fork-local scope is fork-local | `loc1-task` | none | **open** as part of `inv`; oracle only (fork-local samples 51-60) |
| I16 / LOC2: no fork marker is owned by a fork-local scope | `loc2` | none | **open** as part of `inv`; oracle only (samples 51-60) |
| I16 / LOC3: a pending retirement precedes every item | `rinv` | `sys-reach-rinv` (`layer2.top`) | proved |
| Z#77 `retire-clean` / `retire-quiet`: after `[:retire-local]` no run of a fork-local task, no cleanup entry, every fork-local task done | executable form in `oracle_test` (`fork-local-closure`) | none | **open** as theorems; checked on the replayed sample worlds only |
| Z#69 scope parents acyclic | `scopes-acyclic` | `step-acyc` (`inv.acyclic`) | proved (alongside chain-start; not part of `inv`) |
| L1 prompt reclamation | — | `step-l1`, `step-l1-comp`, `step-l1-run` (`inv`) | proved in state form, with `live-converged`/`normalized` premises that P1/P2 discharge; no packaged form |
| L2 join | measure `mu-f`, bundle `l2-measure` | `step-mu-le`, `finally-exit-dec`, `slice-exit-retires`, `ack-dec`, `ack-retires` (`progress.measures`) | partial: fair termination is a paper argument; Z#66 is not modelled |
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
| P4 | cascade completion | proved | `cascade-done-ok` (`progress.casc`) |
| P5 | I12 ranks kept | proved | `step-rank`, `step-ranks` (`inv.rank-step`) |
| P6 | §3.4 validation walk within fuel | proved | `valid-done-ok` (`progress.react`) |
| P7 | settle worklist within fuel | proved | `settle-done-ok` (`progress.l5`) |
| P8 | reactivation worklist within fuel | proved | `react-done-ok` (`progress.react`) |
| P9 | Rule R's loop ends with no orphans | proved | `rule-r-no-orphans` (`inv.i1-owners`) |
| P10 | the transition guard `cur-closed` never fires | **open**; reduced to `rso` (an alive normal task run's run scope is open), which the tests check | `cur-open-of-run-scope`, `cur-open-of-rso` (`inv.i14`) |
| P11 | h-mark and h-mem2 are step invariants | proved | `step-h-mark-total` (`inv.marks-step`), `step-h-mem2-total`, `l5-safety-total` (`inv.members.step`) |
| P12 | I14 acyclic | proved | `step-i14-total` (`inv.i14`) |

Fuel with no sufficiency theorem (fuel is a parameter, convergence a checked flag): the I12 raise loop
(an exhausted raise refuses T6), Derive/blocked (`blocked-complete` assumes `blocked-converged`), the
dirty cone and `cur-scope`.

## Trust boundary

- **Kernel.** Every statement is checked by the ansatz kernel (a port of Lean 4's) when its namespace
  loads. Generated theorems (the tree's) are checked like hand-written ones.
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
