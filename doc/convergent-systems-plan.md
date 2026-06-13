# Convergent systems — CRDTs as conflict-free yggdrasil systems

> Status: plan (2026-06). The continuation artifact for the "distributed
> programming model" arc. Read alongside `distributed-context-reflection.md`
> (the workspace-peer keystone that this generalizes).

## Thesis

A CRDT is **not** a new kind of thing bolted next to versioned state — it is
yggdrasil's *multi-head regime run with a conflict-free merge law*. yggdrasil's
system algebra (Snapshotable / Branchable / Graphable / Mergeable / …) already
describes forkable, mergeable, snapshotable systems; datahike collapsed it to
**single-head + 3-way merge + conflict detection**. A CRDT is the **same
algebra** in the **multi-head + 2-way join + no-conflicts** regime. The design
doc already anticipated this: *"multi-head is policy, not architecture."*

Consequences that drive the whole plan:

- **One merge algebra, in yggdrasil**, with a capability axis:
  `needs-ancestor? / conflicts-possible?` (datahike, git) vs **conflict-free /
  2-way / no-ancestor** (CRDT). Not two `Mergeable` protocols.
- **Systems are the unit of fork/merge; signals are reactive projections.** You
  don't merge signals — you `track` a system; the signal re-derives.
- **spindel needs ~zero new merge machinery.** Its existing yggdrasil
  integration — `register!`, `pfork` (PForkable), `merge-to-parent!`, and the
  **workspace-peer we already shipped** — handles CRDT systems for free, because
  a CRDT *is* a system. `merge-contexts` ≡ `merge-to-parent!`; **a peer is a
  remote fork of the context, so distributed-sync ≡ fork-merge.**
- The `merge!`-on-signals verb shrinks to a thin local convenience
  (`(swap! sig #(join % delta))`) sharing the same lattice core — NOT the spine.

## Where things live (decided)

- **CRDT lattices** = a small **cljc, dependency-light library** that *implements
  yggdrasil's (cross-platform) system protocols*. The "improved yggdrasil" the
  catalog plugs into. Because it speaks the protocols spindel already integrates
  against, spindel picks it up unchanged.
- **NOT in spindel** (would split the merge world in two) and **NOT buried in
  yggdrasil core** (keep the catalog separable). It depends on a cross-platform
  yggdrasil; yggdrasil does not depend on it.
- Durable convergent state (the registry) stays a specialized durable G-Set; the
  generic catalog is for the rest (presence, shared sets, convergent metadata).

## What the exploration established (feasibility is good)

**yggdrasil cross-platform gap (audit):**
- Already cljc + portable: `protocols.cljc`, `types.cljc`, `compose.cljc`.
  Protocol methods **already take `{:sync?}`** — the async surface is designed in.
- Must become cljc + async (konserve `async+sync` pattern): `storage`,
  `registry`, `composite`, `workspace` (+ `gc`, `hooks`, `compliance` are
  pure → rename to `.cljc`, ~0 change). Rewrite is **mostly mechanical**:
  replace `(<!! (k/...))` with sync?-threaded konserve calls; the datahike
  adapter *already* uses `{:sync? true}`, proving the store layer supports it.
  Est. ~2–3 days for the registry/composite/workspace trio.
- Stay **permanently JVM-only** (correct): every adapter — `datahike`, `git`,
  `btrfs/zfs/dolt/lakefs/podman/overlayfs/iceberg/ipfs` (shell + JVM libs), and
  `watcher.clj` (ScheduledExecutorService → on cljs the konserve-sync
  `on-key-update` callbacks ARE the watch).
- **PSS is Java.** `persistent-sorted-set` is a JVM B-tree; cljs has no port
  here. The registry/composite use it for the durable history index. **Open
  issue O1 below.**

**konserve sync/async recipe (to mirror in yggdrasil):**
- `konserve.utils/async+sync` macro + `*default-sync-translation*`
  (`go-try-→try`, `<?-→do`, `go-locked→locked`) + `superv.async` `go-try-`/`<?-`.
- Pattern: `.cljc` file; wrap each method body in
  `(async+sync (:sync? opts) *default-sync-translation* (go-try- … (<?- …)))`;
  the call site passes `{:sync? true}` on JVM (returns value) / omits it on cljs
  (returns channel). No runtime overhead either side. Tests loop both modes.

**replikativ CRDT joins to port (catalog):**
- `crdt.cljc` records: `SimpleGSet {elements}`, `ORMap {adds removals}`,
  `MergingORMap {adds removals merge-code}`, `LWWR {register timestamp}`, plus
  `CDVCS` (which we DON'T port — datahike already is its single-head form).
- `POpBasedCRDT/-downstream` is the join, and for these types it is
  **state-to-state** (the "op" is itself a small state): G-Set `set/union`,
  LWWR timestamp-max (deterministic `pr-str` tiebreak), OR-Map
  `(merge-with merge …)`. **Pure, cljc, zero konserve/peer coupling.** ~180 LOC
  total incl. write-side ops. Tags: OR-Map uses `hasch/uuid`; LWWR wall-clock;
  G-Set value-identity. Serialization = incognito record handlers.
- Note: OR-Map's `-missing-commits` (konserve commit-fetch) is a **separate**
  concern from the join — don't port it; the join stands alone.

## Build order (bottom-up)

### Layer 0 — `merge-contexts` framing (no code; the conceptual spine)
Confirm the model in `distributed-context-reflection.md`: fork-merge ≡ peer-sync
≡ per-element reconcile dispatched on system capability. The workspace-peer,
checkout descriptor, and single-writer lease are **instances**, not separate
mechanisms. (Done — captured here + in that doc.)

### Layer 1 — yggdrasil cross-platform (`feat/cljc` branch)
Make the registry/composite/workspace trio run on cljs.
1. `types.cljc`: `System/currentTimeMillis` → `#?(:clj … :cljs (.getTime (js/Date.)))`
   for HLC. (Trivial. Note determinism: HLC must be injectable for spindel replay.)
2. `storage.clj → .cljc`: konserve calls via `async+sync`; PSS IStorage behind a
   protocol with a JVM (PSS) impl and a cljs impl (see O1).
3. `registry.clj → .cljc`, `composite.clj → .cljc`, `workspace.clj → .cljc`:
   thread `{:sync?}`, `async+sync` the konserve/index-persist calls.
4. `gc/hooks/compliance → .cljc` (rename, ~0 change). Run `compliance` on cljs.
5. Keep all adapters `.clj`. `watcher.clj` stays JVM; cljs watch = sync callbacks.
**Exit:** registry + composite + an in-memory system construct/branch/merge on
cljs (shadow-cljs test), JVM path unchanged (datahike/git suites green).

### Layer 2 — the conflict-free merge law in yggdrasil protocols  [SLICE LANDED]
**Merge is NOT scoped to a parent.** CRDT replicas are *peers*; the join is
symmetric (`a∪b ≡ b∪a`), any-to-any, no privileged ancestor. So the CRDT law is
a **separate, symmetric primitive**, distinct from the branch-oriented,
hierarchical `merge!`/`conflicts`/`merge-to-parent!` (the versioned tree tier):
- `yggdrasil.convergent/PConvergent` — `-join [this other]` (commutative,
  associative, idempotent; no ancestor/conflict/parent) + `-conflict-free?`.
  `join` folds it over peers (order-independent). **[landed]**
- A conflict-free system MAY *also* satisfy `Mergeable` (its branch-merge is a
  join, `conflicts` ⇒ `[]`) so it can still ride the tree machinery — but `-join`
  is its native form, and the general distributed model merges peers with
  `-join`, **not to a parent**.
- Capability dispatch (`-conflict-free?`): the merge path skips `common-ancestor`
  and never surfaces conflicts. NB the existing `merge-to-parent!` already
  accommodates a conflict-free system (it conflict-pre-checks via `conflicts`
  and never calls `common-ancestor` on the merge path) — so the *tree* case needs
  **no yggdrasil change**; the new work is the **symmetric peer-merge** of
  contexts/systems (Layer 4), which `merge-to-parent!` does NOT cover.
**Status:** `yggdrasil.convergent` (PConvergent) + G-Set as a conflict-free
system (`yggdrasil.convergent.gset`) landed on `feat/cljc`; 4 tests/22 assertions
(symmetric/idempotent/associative join, conflict-free capability, valid ygg
system, branch-merge = join). **TODO:** a symmetric **`merge-peers!`** at the
context level (not parent-scoped) — Layer 4.

### Layer 3 — the CRDT catalog library (`convergent-crdts`, cljc leaf)
Port LWWR / SimpleGSet / ORMap (+ MergingORMap) as **yggdrasil conflict-free
systems**:
- pure lattice (record + `-join` = ported `downstream`) — ~180 LOC.
- wrap each as a yggdrasil system (Snapshotable + ConvergentMergeable +
  SystemIdentity), in-memory first; konserve-backed (durable) variant later.
- incognito/fressian/transit handlers for the wire.
- op/write-side helpers (`set`, `add`, `assoc/dissoc`) generating tagged deltas.
**Exit:** `(merge sys-a sys-b)` converges (property tests: comm/assoc/idem);
two in-memory replicas converge regardless of op order.

### Layer 4 — spindel integration (mostly free)
- A CRDT system registered with `ygg/register!` forks via `pfork`, merges via
  `merge-to-parent!`, reflects over the wire via the **existing workspace-peer**
  — prove with **zero new spindel merge code**. This is the decisive spike.
- Thin convenience: `merge!` signal verb = `(swap! sig #(join % x))` for in-graph
  folds, sharing the catalog's lattice. Optional, small.
- `signal_sync` `reset!` → keep as LWW-Register instance (server-authoritative
  descriptor) OR a CRDT system — unify per the algebra.
**Exit:** the workspace-peer integration test, extended with a presence/G-Set
CRDT system in the composite, reflects + converges over the two-peer wire with
no new spindel code.

### Layer 5 — dvergr / simmis
- simmis: replace `branching_sync.cljs` / `db_signal.cljc` / `projected-branch-dbs`
  with cross-platform yggrasil (Layer 1) + the workspace-peer reflection.
  Branch-metadata (`kb-branches`, out-of-order pubsub events) → a convergent
  system, not a hand-rolled `apply-event!`.
- dvergr: presence / live "who's on which fork" as an ephemeral G-Set/OR-Map
  system if/when multiplayer is real (currently single-writer-per-lease — no
  rush).

## Reconciliation with the current arc + simmis

- **Arc artifacts become instances:** checkout descriptor = LWW-Register system
  (server-authoritative); single-writer lease = the conflict policy for a
  non-conflict-free signal at a merge boundary; workspace-peer re-seat =
  `merge-contexts` restricted to external-refs. Nothing is discarded.
- **simmis reality:** single-user-per-session, multi-agent-per-room, **no
  presence / no concurrent-writer need today**. So the *immediate* simmis payoff
  is the cross-platform-yggdrasil cleanup (Layer 1 + workspace-peer replacing the
  hand-rolled cljs sync), NOT multi-writer CRDTs. The catalog (Layer 3) is the
  forward-looking capability. **Do not gate simmis on multi-writer convergence.**

## Open issues / decisions (raise before/at each layer)

- **O1 — PSS on cljs (Layer 1).** Registry/composite history index uses Java PSS.
  Options: (a) **ephemeral in-memory `sorted-set-by` on cljs** (browser registry
  is rebuilt from sync, no durable index) — recommended first cut; (b) port PSS to
  cljs (separate effort); (c) konserve-async-backed IStorage protocol. Decision:
  (a) now, (b)/(c) when durable browser index is needed.
- **O2 — op-based vs state-based (Layer 2/3).** replikativ is op-based
  (`POpBasedCRDT`), but these types' `downstream` is state-to-state. Decide:
  expose a **state-based `-join`** as the yggdrasil law (cleanest for
  `merge-to-parent!`), implemented via `downstream` where op=state. Keep the
  op/delta form for the *wire* (cheap) — δ-CRDT: delta is a small state, join
  handles both.
- **O3 — durable vs ephemeral CRDT systems (Layer 3).** First cut: ephemeral
  in-memory (presence). Durable (konserve-synced, survives restart) needs the
  async storage layer — wire it after Layer 1's async store lands.
- **O4 — value-CRDT-in-signal vs system-CRDT (Layer 4).** Keep both, sharing the
  lattice: system for forkable/reflectable/durable; signal-value for lightweight
  in-graph folds. Don't force everything to be a heavyweight system.
- **O5 — HLC determinism (Layer 1).** spindel forbids `Date.now`/`random` for
  replay; HLC must be injectable (context-carried clock), not a raw wall-clock.
- **O6 — release/dep graph.** New leaf lib + cross-platform yggdrasil release;
  datahike/dvergr/simmis bumps. Sequence so JVM consumers never break.

## The decisive spike (do early, de-risks the whole plan)

Make yggdrasil `protocols`+`types`+a minimal `composite`/`registry` cljc+async
(Layer 1 slice) → port **one** CRDT (G-Set) as a conflict-free system (Layer 2+3
slice) → register it in a spindel context → show it **forks via `pfork`, merges
via `merge-to-parent!`, and reflects over the wire via the existing
workspace-peer — with zero new spindel merge code.** If green: "CRDTs as
improved-yggdrasil systems that automatically work in spindel" is proven, and the
rest is porting the catalog + the async sweep. If the cljs/async friction is
worse than hoped, fall back to CRDT-as-spindel-algebra (the smaller, two-merge-
world design) — but only then.
