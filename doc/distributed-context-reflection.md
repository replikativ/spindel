# Distributed context reflection — coordinated forks over the wire

> Status: design (2026-06). Keystone landed (datahike-kabel `f1f8ed1f`, konserve-sync
> `65d5aa7`). The workspace-peer + registry-as-synced-store remain to build.

## Goal

Reflect a spindel **execution context** — specifically its yggdrasil workspace at
`[:external-refs ::workspace]` — between a JVM server and a ClojureScript client,
so an app layer (simmis, dvergr) does **not** hand-roll request-remoting + state
sync. When the server forks a room, the client cleanly **swaps** to the fork with
snapshot-isolated consistency; writes on the branch you're viewing are just
`transact!` on the conn you're viewing. Single-writer per branch (no concurrent
commits to one branch — fork to write, merge to reconcile).

## The key realization: reflect the *workspace*, not the reactive graph

A spindel context's reactive graph (spins, signals, continuations) is **peer-local**
— the browser has its own UI spins; you never want the server's. The only thing that
must be coherent across peers is the **workspace**: which yggdrasil systems exist and
what snapshot/branch each is at. That is portable data:

    composite descriptor = { system-id → { store-id, branch, snapshot-id, hlc } }

(`yggdrasil.types/SnapshotRef` + HLC are `.cljc`/JSON-serializable; datahike
`commit-id`s are content-addressed hasch UUIDs → a client with the synced blocks
reconstructs the *exact* server db via `commit-as-db`.)

Do **not** serialize+ship the whole context and re-execute spins (the obvious path):
it drops continuations, re-runs the model, and reintroduces torn reads. Reflect the
descriptor + sync the stores; keep the reactive graph local.

## It's konserve-sync all the way down (one mechanism, not two)

The yggdrasil **registry is already a konserve store** — a persistent-sorted-set
(B-tree of content-addressed blocks + a saved root), HLC-ordered, grow-only ⇒ it is
*itself* a CRDT (G-Set). So the "control plane" is not a separate distributed-pub-sub
CRDT; it is the registry store, replicated by the same konserve-sync as the data
stores.

```
  kabel.pubsub  — one transport; strategy protocol (-handshake/-apply/-publish;
                  callbacks on-key-update / on-handshake-complete / on-publish)
   ├─ StoreSyncStrategy (konserve-sync)  — replicates a konserve store (blocks)
   │     • REGISTRY store  (PSS)   → needs a PSS walker
   │     • system store kb (datahike) ┐ datahike-walk-fn walks every branch ✓
   │     • system store msgs           ┘ key-sort-fn = mutable pointers LAST ✓
   │     • git system → registry metadata only; blocks NOT browser-replicable
   └─ SignalSyncStrategy (spindel signal-sync) — replicates a value; -apply-publish
         does (reset! signal-atom v)  ← the bridge prototype: a strategy drives a
                                          spindel signal
            │ callbacks
            ▼
  spindel WORKSPACE-PEER (the reactive/coordination layer):
     on-key-update(system root)   → (reset! head-signal[system] commit)
     on-key-update(registry root) → (reset! registry-signal …)
     projection spin (interval/delta):  target = registry {system→pinned head};
        actual = {system→head-signal};  COMPOSITE GATE: expose snapshot S only when
        ∀ system: actual reached pinned  →  resolve [:external-refs ::workspace] to
        branch-scoped conns at the pinned heads  →  checkout = re-seat on change
```

## The fetch-gate (two levels)

The control tier (registry / branch pointer) races ahead of the value tier (blocks).
A peer must not expose a branch at head C until C's blocks are local.

- **Per-store (intra), built-in via ordering.** konserve-sync auto-publishes a
  commit's changed keys through a konserve write-hook, ordered by `:key-sort-fn`.
  datahike-kabel sets it so **content-addressed (uuid) blocks publish first and the
  mutable branch pointer last** (`(fn [k] (if (keyword? k) 1 0))` — every
  `:branches`/branch-HEAD keyword after the blocks). So the branch pointer's
  `on-key-update` *is* the "commit C fully present" signal (datahike's `on-db-sync!`
  already keys off it). The initial handshake additionally fires `on-complete`.
- **Composite (cross-store), in the workspace-peer.** Combine the N per-store
  "reached head C_i" signals + the registry's target; expose composite snapshot S
  only when all systems reach their pinned heads (HLC/ancestry check). This is the
  only genuinely-new coordination piece; konserve-sync is per-store.

## CDVCS lineage / single-writer

CDVCS (replikativ) is the prior art: state `{commit-graph, heads}` where a branch is
a **set of heads** (multi-head, merge-to-converge — a metadata CRDT) and `pull` is
the two-tier op (commit-graph delta over pubsub + lazy value fetch). datahike is its
**coordinated single-head** descendant: `:branches` is a set of *names*, one head
each; `common-ancestor` (LCA) + 3-way merge kept; multi-head dropped. **Single-writer
per branch is precisely that single-head regime** — it makes `pull`/`checkout`
unambiguous and merge needed only at fold-back-to-parent. yggdrasil adds the
**composite** (N such systems + HLC), which CDVCS never had. The door to multi-head
(true local-first) is policy, not architecture: re-enable head-sets + LCA-prune *in
datahike's own versioning* if ever needed.

## Operations (single-writer)

1. **Fork** (server forks room R): yggdrasil composite fork → per system `branch!`
   (head C on branch B; blocks written) → append RegistryEntries → registry root
   advances → konserve-sync notifies.
2. **Checkout** (client): registry delta → projection recomputes {system→(B,C)} →
   fetch-gate awaits each commit's blocks → re-seat conns → workspace reflects B.
3. **Advance** (write on B): single writer commits → head C′ + entry → sync delivers
   blocks + delta → conn advances; if the client wrote, the **branch-agnostic
   optimistic overlay** (`datahike.optimistic`) reconciles on the echo.
4. **Merge** (fold B→parent): yggdrasil 3-way LCA → 2-parent entry; conflicts are
   real (datahike adapter's `compute-conflicts`) → LLM/human review (the same
   reconciliation seam as dvergr's merge-reviewer / the human merge UI).

## Durable vs ephemeral CRDTs

- **Durable, versioned** convergent state (rooms/KBs/branches): the konserve-synced
  registry *is* the CRDT (grow-only + HLC). No new CRDT lib.
- **Ephemeral, high-frequency** convergent state (presence, cursors, "which branch is
  each peer viewing"): do NOT want a konserve commit per change → build a lightweight
  in-memory CRDT (ORMap/LWWR, mined from replikativ) on **spindel interval/delta +
  kabel.pubsub**. This is where "CRDTs on spindel primitives" belongs — the
  complement to konserve-sync's durable tier.

## The checkout pointer is irreducible (registry-as-store does not subsume it)

A subtlety the implementation surfaced: the yggdrasil **snapshot indices carry
content + history + per-`[system, branch]` heads, but NOT "which branch is this
room checked out to."** Concretely:

- The composite index entry (`composite.clj` `commit!`) records
  `{:composite-snap-id, :parent-ids, :timestamp, :sub-snapshots {system→snap}}`
  — **no branch label** — and `branch!` writes *no* entry at all; only `commit!`
  does. The current branch lives in the in-memory `current-branch-name` (set by
  `checkout`).
- The registry (snapshot index) *does* record `branch-name` per entry, so
  `latest-by-system-branch` yields `{[system branch] → head}` — but that still
  doesn't say which branch the room is *following*.
- The client needs a **branch name** to re-seat a *writable* conn:
  `(d/connect (assoc cfg :branch B))` (the wire-test materialization). A
  snapshot-id alone only yields a read-only `commit-as-db`.

So there is an irreducible **checkout descriptor** — `{system-id → {:store-id,
:branch, :head, :hlc}}` — that the server computes from the composite's current
state and reflects to the client. **Registry-as-store and the checkout
descriptor are complementary, not either/or:** the registry/composite indices
give durable content + history + as-of; the descriptor gives the live "which
branch, at which head" the peer should re-seat to. The descriptor rides the
existing **`signal_sync`** bridge (it is exactly a value to `reset!`); the
per-system datahike stores ride `konserve-sync` for the blocks; the registry
rides `konserve-sync` (via `registry-walk-fn`) for history/as-of.

The **composite gate** is then pure: given the target descriptor and the
locally-synced per-system head-state, expose the workspace at snapshot S only
when every target system's local head has reached (== or descends) its pinned
head. This is the one genuinely-new coordination function and is unit-testable
with no networking (`workspace_peer` pure core).

## Status / build order

1. **[LANDED] Keystone** — datahike-kabel `key-sort-fn` generalized to all branch
   pointers (`f1f8ed1f`); konserve-sync walker reaches every branch + fork-sync test
   (`65d5aa7`); two-peer wire test (`dfaf952e`).
2. **[2a LANDED] Registry PSS walker** — `konserve-sync.walkers.yggdrasil-registry`
   (`855d756`): pure-data `registry-walk-fn` (reachability) + `read-registry-entries`
   / `latest-by-system-branch` (control-plane projection). cljc, no yggdrasil dep,
   read-only-cljs-safe. 4 tests green. **Remaining 2b/2c:** register the registry
   store for remote access (`register-store!` + `:walk-fn`, same keyword-last
   `:key-sort-fn`); add a branch-owner lease (single-writer).
3. **Workspace-peer** (spindel, `.cljc`) — checkout descriptor (`signal_sync`) +
   per-system head-signals (`konserve-sync` `:on-key-update`) → projection spin with
   the **pure composite gate** → re-seat `[:external-refs ::workspace]` to
   branch-scoped conns. Makes `ygg/system` location-transparent. *Pure gate core +
   tests land first; live wiring sits on top (needs spindel←konserve-sync dep +
   yggdrasil-with-registry, dev via `:local/root`).*
4. **(later)** ephemeral convergent-ref primitive (presence) on spindel interval/delta.

## Decisive integration test (LANDED)

`test/org/replikativ/spindel/distributed/workspace_peer_integration_test.clj` — a
synthetic kb+msgs composite synced over a real two-peer http-kit pair (harness
lifted from datahike's wire test; datahike `:local/root` + `src-kabel` added to
spindel `:test`). The server registers both stores for remote access and exports
a checkout descriptor via `signal_sync`; the client replicates via `konserve-sync`
(KabelWriter `d/connect`) and `attach-descriptor!`. It asserts the workspace-peer
re-seats its `[:external-refs ::workspace]` checkout `:db → :fork` over the wire,
driven by the real descriptor + the real replicated branch pointers. 9 assertions.

Scope split, kept honest: this test proves the workspace-peer's *own* job — the
**checkout reflection** (which branch each system is on) — with marker systems.
Materializing branch **data** through a datahike conn is a datahike concern,
already proven by datahike's single-store fork wire test (deferred-index
reconstruction over the wire). A diagnostic confirmed, over this very harness,
that the gate fires (seated + ready) and the fork pointer replicates
(`client :branches = #{:db :fork}`).

Proven now at four levels: pure gate + fork-swap (unit), callback wiring (unit),
registry walker (konserve-sync unit), and composite checkout over a real two-peer
wire (this) — plus datahike's single-store data-over-wire test.
