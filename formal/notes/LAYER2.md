# Layer 2 (forks, savepoints, merge): formal design, draft 1 (2026-11-13, for sign-off)

Sources: spec §8/§9 at `feat/m6-phase-a` (277e1c9), engine `fork-world*`, `activate-dormant!`,
`instantiate`, `activate!` in `core.cljc`, `rows.cljc` (`rv`, `resolve-row`, `own-copy!`),
yggdrasil `DESIGN.md` (Overlayable, overlay-as-prepare).

## 1. Two layers, two kinds of theorem

| Layer | State | What a fork is | Theorems |
|---|---|---|---|
| **Semantic** (`spindel.v2.sys`) | a system: table of worlds, publications, one allocator | a *value copy* of the parent's tables, then a fix-up made of layer-1 items | every world keeps the layer-1 bundle; no cross-world reference; release leaves nothing; activation at most once; merge laws |
| **Physical** (`spindel.v2.cow`) | a heap of rows, each with an owner epoch; per world an epoch and a forward map | epoch rotation, O(1); copy on first access | the heap read through a world's view *is* that world's tables (refinement); a write in one world changes no other view; storage bound F5 |

In the semantic layer isolation of frozen forks holds by construction (worlds are separate
values). The content of "copy-on-write is correct" is the refinement theorem of the physical
layer. That theorem is independent of the layer-1 proofs and is done first.

## 2. Facts taken from the engine (spec §8 leaves them implicit)

- **One allocator per family.** The child's id comes from the parent's allocator and row ids are
  never reused across worlds: an inherited row has the same id in parent and child.
- **Copied by value:** all layer-1 tables, the ready/resume/start/cleanup/Rule R queues, pins, roots
  (so host `observe` and host-await edges and pins exist in the child too).
- **Fresh in the child:** ingress, gate, callbacks list, ownership (`owned`, `holder`), savepoint
  table, `pending-activation`, watches.
- **Dormant list:** the parent's armed resources and pending savepoints (plus what the parent
  itself still held dormant).
- **Fix-up at the child's first turn** (`activate-dormant!`) is a sequence of existing items:
  for each dormant savepoint other than `pending-activation`: deliver `err ::forked`;
  for each dormant resource still armed: timer -> re-arm; other -> T18 `resource-fire(err ::forked)`
  then T15 `resource-ack`.
- **Unborn** (instantiated, not activated): host items commit; the fix-up and inherited work wait.

## 3. Semantic state

```
WorldCell = { wid, world : World, parent : wid|0, mode, unborn : Bool,
              dormant-res : [id], dormant-sp : [id] }
Pub       = { pid, world : wid, edge : id, basis : World, handles }
System    = { cells : [WorldCell], pubs : [Pub], next-id }      -- one allocator
```

`World` loses its own `next-id` in the system view (threaded from `System`); `forks` rows
`{id, child : wid, owner : scope, strong : Bool}` stay in the parent world.

## 4. Transitions (to become spec rows T27–T34)

| # | Item | Requires | Effect |
|---|---|---|---|
| L1 | `step(wid, it)` | cell exists, not released; if `unborn`, `it` is a host item | `world-step` in that cell; no other cell changes |
| L2 | `fork-host(wid)` | no slice held; not unborn | child = `copy(world)` with empty `forks`/`pubs`/`pending-act`; dormant lists set; marker in the parent owned by the root scope, weak |
| L3 | `fork-effect(wid, R)` | `R` is a task run holding the slice | as L2; marker owned by `R`'s current scope, strong; `R` continues in the parent with `[:parent child]`; `R`'s copy is parked on a filled activation with `[:child nil]` |
| L4 | `wake(wid)` | not unborn; dormant lists non-empty | the fix-up of §2 as layer-1 items; lists emptied |
| L5 | `publish(wid, R, addr)` (S1) | `R` holds the slice | activation `one` with one `savepoint` edge; `Pub` with `basis = copy(world)` |
| L6 | `resume(pid, v)` (S2) | `edge` armed | T9 savepoint branch in the pub's world |
| L7 | `instantiate(pid)` (S3) | pub exists | new cell from `basis`, `unborn = true`, `pending-act = edge` |
| L8 | `activate(wid, v)` (S4) | `unborn`, `pending-act` set | marker in the pub's world (root scope, weak); `unborn := false`; fire `pending-act` with `v`; then L4 |
| L9 | `abandon(pid)` / pub handles reach 0 (S7) | — | if `edge` armed: T14 cancel of its run, creditors get `err ::abandoned`; pub removed |
| L10 | `discard(wid)` / owner scope closes (F2, F4) | — | born: T21 in the child, cell removed when quiescent; unborn: cell removed, nothing runs; marker removed |
| L11 | `idle-release(wid)` (Q12) | idle predicate: no runs, pins, observe edges, open explicit scopes, pending-act, handles; marker weak | cell and marker removed |
| L12 | `merge(wid)` | child quiescent and sealed; for every source in `diff(child)`: parent version = version at fork | each diff entry is a T2 write in the parent; then L10 |

L11 replaces "collected by the garbage collector": the collector is one scheduler of this item.

## 5. Theorems

Semantic:
- **S-inv (F5):** every cell's world satisfies the layer-1 bundle. Needs (a) `copy` keeps the bundle,
  (b) L4/L6/L8/L9/L12 are layer-1 items, so `step-p3l` applies.
- **S-frame:** a step in one cell leaves every other cell and pub unchanged (L1 by definition).
- **S-closed (F1):** no row of a cell names another cell except marker `child` and `parent`.
- **S-release (F2):** after L10/L11 no marker, pub or cell names the released wid.
- **S-once (S2, S4):** a savepoint edge fires at most once; `activate` succeeds at most once per cell.
- **S-indep (S4):** two instances of one pub start from equal worlds; runs with equal items agree.
- **S-idle:** L11 is unobservable: any item accepted after it is accepted with the same projection
  on the remaining cells without it.
- **S-merge:** refused merge changes nothing; accepted merge = the diff as T2 writes; merge after no
  child write is the identity on the parent.

Physical:
- **P-view:** `view(heap, W)` (resolve every reference through owner epoch / forward map) is preserved
  by `resolve`, `own-copy` and path compression.
- **P-fork:** after epoch rotation `view(parent) = view(child) =` the view before.
- **P-write:** a write through `W` changes `view(W)` at that row only and no other world's view.
- **P-bound (F5):** rows in the heap <= shared basis + sum of rows each live world owns.

## 6. Prerequisite in layer 1

The proved bundle excludes two things layer 2 needs: `ekb` (no savepoint edges) and `gw` (no fork
markers). Both must be lifted first: savepoint edges as a fourth edge kind through the step
(S1, S2, T14's removal), and markers as rows retained by their owner scope.

## 7. Order and status (2026-11-13)

1. `spindel.v2.cow`: physical model. **Done** (views, fast and slow path of `rv`, family invariants kept by
   copy/write/fork/alloc/release).
2. Layer 1 lift of `ekb`/`gw`: **not needed.** Fork markers live on the child cell (a marker retains nothing in
   the parent); a savepoint is a resource of kind `rk-savepoint`, so S1/S2/S7 are T17/T18+T15/T14.
3. `spindel.v2.sys`: **done** for L1 step, L2/L3 fork, L4 wake, L5 publish, L6 resume, L7 instantiate, L8 activate,
   L9 abandon, L10 drop, L11 idle release, L12 merge. Proved: every live world and every live basis keeps `p3l`
   (F5); frames; fork and instance start from the parent's world / the basis; a second activation changes nothing;
   a refused merge changes nothing; a merge without child writes changes nothing; a drop commutes with steps elsewhere.
   `spindel.v2.skip`: skipping ids keeps `p3l` (`p3l-skip`, `p3l-skip-ids`). The worlds of a family share one
   allocator in the engine; a world's log replays in the model with `skip-ids` between items.
   **Correction (2026-11-13):** the first version armed savepoints with a resource kind of their own (4). Layer 1
   arms timers and offloads only, so every publish was refused and the savepoint theorems held of nothing. A
   savepoint is now an offload-kind resource (told apart by `Pub.res`), and `sys_test` runs the compiled model:
   publish is accepted and parks the run, a resume makes it active, the fork effect's child starts resumed.
   L3 (the fork effect) had been modelled as a plain copy; it is now `fork-effect-world` (the child's run arms a
   resource that fires and is acknowledged at once), with `sinv-fork-effect` and its frame.
   Conformance: samples 14 (host fork) and 15 (fork effect, child released by its owner scope) replay with no
   divergence, parent and child (`oracle_test`). Differences the replay bridges, each removable in the engine:
   - closed in the engine (branch `feat/v2-layer2-conformance`): the fork effect reserves the ids of the child's
     resource, activation and edge in T17's order and counts the effect in the child's run, so sample 15 replays
     exactly;
   - closed in the engine (branch `feat/v2-savepoint-resource`): a savepoint is a resource the run arms (kind
     `:savepoint`, no controller). Publish is `arm`, resume and activate are fire + acknowledge, abandon is a
     cancel after which the resource joins at once, and an inherited one settles with the other dormant
     resources. Sample 16 (in-place resume, two instances, abandon) replays with no divergence in the publishing
     world and in both instances, started from the basis;
   - the engine's projection (`verify.clj`) hard-codes `pubs`, `forks`, `pending-act` and (fixed locally)
     `released`: the layer-2 tables are not compared yet.
4. Open in the semantic layer:
   - guards not yet enforced by `sys-step`: an unborn cell accepts host items only; a dropped cell accepts nothing;
   - the marker's owner scope closing drops the child (needs a per-step check of the parent's scope table);
   - a savepoint fires at most once (needs the layer-1 fact "a fired resource does not fire again" as a theorem);
   - `wake` leaves no inherited non-timer resource armed;
   - following mode (not in the engine at phase A either), sealing, sources created in the child are not merged.
5. Spec §8 as rows from §4; engine log items for L2–L12 and oracle samples (the oracle maps the engine's
   savepoint edge to the model's savepoint resource).

## 8. Open points

- Following mode (parent source writes pushed to the child as T2 items): modelled after step 3 as a
  system-level item pair; frozen first.
- Host `observe` edges are copied into the child (engine behaviour): the same callback is then called
  by both worlds. Keep, or drop host edges at fork? Affects L2/L3.
- Merge conflict rule (§4 L12) is the minimal one: version at fork must equal the parent's version.
  Yggdrasil's per-system merge sits above it (system values are source values).

## 9. Physical layer, MVCC representation (`spindel.v2.mvcc`, 2026-11-15)

Engine engine-v2 3eb18b7 (#260) + e2bd63e replaced the forward-map representation `cow` models by MVCC rows
(spec §8.1 "Representation (MVCC, 2026-11-15)", `v2-fork-memory-design` §2, §7; spec answers A1–A8 from the
spindel session, recorded below). `spindel.v2.mvcc` models the new one; `sys` (a fork is a value copy) is
unchanged and remains the semantics; `cow` stays as the model of the old representation.

**State** (`MSt`): heap `h : address -> MRow` (`[id ow so val vers]`, versions `[k m img]`), next address `n`
(address 0 = "no copy"), `home : id -> address` (the creator's row), per world `MW` `[ord fwd lin cells]` (ordinal,
copy map, lineage `[own f tok mp]` nearest first, the owner's token cells `[o tok]`), token states `ts` (0 live,
1 shared, 2 ended), the active worlds, the savepoint bases, and as ghost state the value-copy tables `dom`/`tab`.
Values opaque Nats; references abstract to ids (as in `cow`); the lineage cut is the domain.

**Operations** (one per engine function): `mv-write` (`rv` barrier `mv-pres` = `preserve!`, then the change),
`mv-copy` (`own-copy!`), `mv-create`, `mv-fork` (`fork-world*`: ordinal advances, token registered, the
parent's own token shared), `mv-inst` (`instance-world*`: the basis's lineage, its token shared), `mv-prune`
(`prune-cell!`, the sweep, the prune inside `preserve!`), `mv-finish` (`maybe-finish-token!`: the own token ends
unless shared), `mv-drop` (a world collected / a publication disposed), `mv-collect` (an unreachable token ends).
`MReach mv-init` is the closure under them with the engine's preconditions (fresh ids/tokens, a basis never
runs or forks, copy only of a row neither owned nor copied).

**Theorems** (all kernel-checked, Init only, 146):

| obligation | statement |
|---|---|
| 1 fork view | `mv-refinement`: in every reachable state every active world (root, fork at any depth, savepoint instance) reads every id of its domain exactly as its value-copy table; `mv-fork-res-c`, `mv-inst-res-c`: a new child / instance reads the parent's / basis's tables |
| 2 barrier | `mv-vat-pres`: after `preserve!` at ordinal o and a change, a fork at f < o with a live token reads the same state; `mv-write-ref`/`mv-write-inv`: a write keeps the refinement for every world |
| 3 reclamation | `mv-no-missing-version` (`version-of`'s throw is unreachable); `mv-tokens-live` (every active lineage entry has a live, registered token); `mv-prune-covered` (safety form, A7: after pruning every version left is covered by a live token); `mv-finish-inv` (finish ends only an unshared token: shared ones are named by other active worlds, `mv-wtok-lin`), `mv-collect-inv` |
| 4 concurrency | `mi-protocol` over `MIReach` (one row, its owner, a fork reader, any interleaving): the owner restamps under the monitor (`o-pres`), changes the row unmonitored afterwards (`o-tear`, any number of partial changes, also via the fast path `o-fast` while the reader is inside its critical section), prunes under the monitor; the reader's clone is NOT atomic (`r-stamp`, then `r-copy`); a reader that has copied holds the row's state at its fork. The protocol invariant `mi-inv-f`: mutual exclusion, an unrestamped row is unchanged, a restamped row keeps the version for f, the stamp the reader saw holds, the owner changes only restamped rows |
| 5 oracle | not representation-level: the commit log carries no MVCC events (versions, tokens), so the samples replay through `sys` (§7). `mvcc_test` runs the compiled model on the agreed sample shapes (fork during a parked run, nested fork with a released intermediate, instances after owner writes, finished unshared fork) checking the refinement after every step and after pruning every row, and two mutants (finish ending a shared token; a write without the barrier) that the checks reject |

**Supporting invariant** `mv-good` = `mv-inv` (`k-row`: stamps not ahead of the owner's ordinal, versions older
than the stamp; `k-fwd`: copies are rows of their id owned by the world; `k-lin`: entries fork-older than the owner's
ordinal, token not ended and registered, copy maps sound; `k-home`; `k-share`: tokens below a lineage's head
are shared, two active worlds with one head token (instances) share it; `k-bas`: a basis owns no row and has no
copy; `ref`) + `k-ownfwd` (a world copies only rows it does not own: a fork reads the parent's copy map before
its rows) + `0 < n`. `mv-reach-good`: every reachable state is good; `mv-init-good`.

**Spec answers used (spindel session, 2026-11-15):**
- A1 token end = unreachable OR (finish AND unshared); shared is sticky (conservative, no refcounts).
- A2 a released world refuses every host item except from its own running slice; after finish nothing in it
  resolves an inherited row (so `mv-finish` deactivates the world).
- A3 holders: lineages of live / released-uncollected worlds (until finish, then only if shared), a publication's
  basis until dispose, instances via the shared basis lineage. Owners hold cells only.
- A4 `prune-cell!` runs as `internal!` under the owner's gate: serialized with the owner (in `MIReach`,
  `o-prune` is an owner step under the monitor).
- A5 no reader clones an owned current-epoch row; path-compression write-backs and container mutation only on
  restamped rows; `notify-blocked!` reads the immutable `E-KIND` of a raw edge; pre-fork writes reach the reader
  through the fork hand-off (sequential consistency assumed per monitor).
- A6 merge base = `[identity version-number]` (merge stays in `sys`, L12).
- A7 the storage bound in safety form (`mv-prune-covered`); liveness of GC/Cleaner is an assumption.
- A8 out of scope: following mode, the optimistic stamp/validate variant.

**Modelling choices to keep in mind.** A version range is saved as a whole (one live token in `[k, m]` keeps
it), as the engine does. `mv-share` maps a non-ended token to shared (`mv-shr`); the engine's states are only 0/1/2,
so this matches `token-share!`. Allocation freshness (ids, worlds, tokens) is a precondition of each operation,
not derived from counters. The lineage cut and handle lineage (`inherited?`) are the domain of the value-copy
model and are not represented physically.
