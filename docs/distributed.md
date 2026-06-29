# Distributed Computing

Spindel integrates with
[distributed-scope](https://github.com/simm-is/distributed-scope) for
peer-to-peer distributed computing over kabel-WebSocket transport.
The integration lets you define functions that execute on a remote
peer with explicit boundary-crossing arguments, and convert between
spins and core.async channels.

The integration is optional — the `org.replikativ.spindel.distributed.*`
namespaces are only loaded if you require them. Spindel's core
reactive primitives work standalone.

## Files

- [`src/.../distributed/core.cljc`](../src/org/replikativ/spindel/distributed/core.cljc)
  — bridge functions (`spin↔chan`), context registry.
- [`src/.../distributed/macros.cljc`](../src/org/replikativ/spindel/distributed/macros.cljc)
  — `defn-spin-remote`, `spin-remote`.
- [`src/.../distributed/signal_sync.cljc`](../src/org/replikativ/spindel/distributed/signal_sync.cljc)
  — convergent signal replication (`export-signal!` / `subscribe-signal!` /
  `sync-signal!`) over kabel pub/sub.
- [`src/.../ygg_signal.cljc`](../src/org/replikativ/spindel/ygg_signal.cljc)
  — a yggdrasil system held as a signal value; `sync-opts` derives the
  convergent sync hooks from a system's CRDT protocols.
- [`src/.../distributed/workspace_peer.cljc`](../src/org/replikativ/spindel/distributed/workspace_peer.cljc)
  — pure gate + checkout/topology descriptor + single-writer lease +
  `fork-descriptor` (no transport deps).
- [`src/.../distributed/workspace_peer_sync.cljc`](../src/org/replikativ/spindel/distributed/workspace_peer_sync.cljc)
  — live wiring: `wire-topology!`, `fork-remote!`, `merge-fork-remote!`,
  `sync-system!` (konserve-sync + signal_sync glue).

## Defining Distributed Functions

```clojure
(require '[org.replikativ.spindel.distributed.macros :refer [defn-spin-remote spin-remote]]
         '[org.replikativ.spindel.distributed.core :as dist])

;; Define a function that runs on a remote peer
(defn-spin-remote fetch-page [server-id page-uuid]
  (spin-remote server-id [page-uuid]
    ;; This body executes on the server-id peer
    (let [db (get-database)]
      (query-page db page-uuid))))

;; Call from client
(spin
  (let [page (await (fetch-page server-peer-id my-page-uuid))]
    (render-page page)))
```

### Key concepts

- **Explicit argument vectors.** Variables that cross the network
  boundary must be declared in the `[...]` after `spin-remote`. The
  macro analyzes free variables in the body at compile time and
  errors on any reference outside the declared set.
- **Compile-time validation.** Free-variable analysis catches
  undeclared dependencies before they hit the wire as undefined
  references on the remote peer.
- **Context addressing.** A `[server-id context-id]` pair targets a
  specific execution context on the remote peer — useful when the
  peer hosts multiple forks of the same root context.

```clojure
;; Target a specific context on the remote peer
(defn-spin-remote process-in-fork [server-id context-id data]
  (spin-remote [server-id context-id] [data]
    (heavy-computation data)))
```

## Execution Context Registry

On the server side, register the execution contexts that should be
addressable by remote calls:

```clojure
(dist/register-context! :default my-execution-context)
(dist/register-context! :particle-1 (ctx/fork-context my-execution-context))
```

`register-context!` is keyed by a context-id; callers from other
peers use that key to address one of several contexts the server
maintains.

## Bridge Functions

For interop with raw core.async channels (e.g. when working alongside
kabel directly):

```clojure
;; Spin → Channel (for sending results)
(dist/spin->chan my-spin)

;; Channel → Spin (for receiving results)
(spin
  (let [result (await (dist/chan->spin response-channel))]
    (process result)))
```

`spin->chan` puts the spin's resolved value (or thrown error wrapped
in an ex-info) onto a fresh channel. `chan->spin` returns a spin that
suspends until the channel produces a value or closes.

## Signal Sync (convergent replication)

`signal_sync` replicates a signal's value across peers over a kabel
pub/sub topic. Every peer calls one of:

```clojure
(require '[org.replikativ.spindel.distributed.signal-sync :as ss])

;; Publish-only (server owns the topic):
(ss/export-signal! peer :topic my-signal)
;; Subscribe (read a remote signal into a local holder):
(def proxy (ss/subscribe-signal! peer :topic))   ; an atom kept in sync
;; Bidirectional convergent sync (both peers publish their δ AND apply others'):
(ss/sync-signal! peer :topic my-signal :owner? true ...)  ; exactly ONE peer is :owner? (the relay hub)
```

For an **ordinary** signal the value is shipped as-is (last-writer-wins).
For a **convergent** CRDT the sync is *δ-based and idempotent*: only the
operation crosses the wire (`:delta-fn`), the receiver applies it
(`:apply-delta-fn`), and an apply that adds nothing returns the receiver
`identical?` (no reactive tick, no re-publish — a mutually-synced network
never runs away). A late joiner is caught up by a serializable handshake
projection (`:state-fn`), since a CRDT *value* (carrying stores + a
join fn) is not itself wire-serializable.

The convergent hooks don't have to be written by hand — for a yggdrasil
system, `ygg-signal/sync-opts` derives them from the system's CRDT
protocols (`PConvergent → :merge-fn`, `PDeltaApply → :apply-delta-fn`
+ `:delta-fn` + `:clear-delta-fn`).

## Workspace Reflection & Cross-System Forking

A **workspace** is the set of yggdrasil systems a peer works with (a
registry of systems, optionally viewed as a composite). `workspace_peer`
reflects one peer's workspace onto another, and lifts yggdrasil's O(1)
copy-on-write fork across the network.

### The checkout / topology descriptor (pure data)

```clojure
{:branch  :main
 :owner   peer-id                       ; the single-writer lease (claim) — absent ⇒ read-only
 :systems {system-id {:store-id ..  :branch :main  :head <token>  :hlc ..
                      :topic <kw>          ; the system's konserve-sync store topic
                      :role  <kw>}}        ; :subscriber (default) | :bidirectional
 :descriptor-topic <kw>                 ; the signal_sync topic carrying THIS descriptor
 :fork-of {:branch :main                ; lineage anchor for a fork (see fork-descriptor):
           :heads {system-id <token>}}} ;   per-system base head = the merge-base/LCA
```

This descriptor is the unit of reflection: shippable over `signal_sync`,
replayable with `wire-topology!`.

### FOLLOW vs FORK — two directions of the same machinery

- **FOLLOW** (`workspace_peer` reseat): the server is authoritative for a
  room. It publishes a checkout descriptor; the client mirrors it,
  re-seating its local view (`::seated-workspace`) once the content syncs.
  The re-seat is **snapshot-isolated** — it flips only when *every* system's
  pinned head is local (the pure composite `gate`), so the client never
  observes a torn, half-synced state. The client doesn't fork — it mirrors
  whatever branch the server checked the room out to.
- **FORK** (`fork-remote!`): the client branches off for its *own* isolated,
  single-writer work, independent of the server.

```clojure
(require '[org.replikativ.spindel.distributed.workspace-peer :as wp]
         '[org.replikativ.spindel.distributed.workspace-peer-sync :as wps])

;; FOLLOW: wire a peer into a remote checkout's subscription topology.
(def peer (wp/make-workspace-peer {:ctx ctx :resolve-system-fn resolve}))
(wps/wire-topology! peer client-peer descriptor store-lookup
                    :signal-lookup signal-lookup)   ; dispatches per-system :role
```

`wire-topology!` dispatches on each system's `:role`:

- **`:subscriber`** (default) → one-way konserve-sync store **follow**
  (`attach-store!`): fetch content + branch-head updates that feed the gate.
  The right mode for durable (datahike) systems and isolated forks.
- **`:bidirectional`** → convergent live **sync** (`sync-system!` over the
  ygg-signal δ-path): both replicas converge via CRDT join. For convergent
  systems (G-Set, OR-Map, CDVCS) that should stay co-synced.

### The fork lifecycle

```clojure
;; FORK an already-followed remote checkout into a local writable branch.
(def fork-desc (wps/fork-remote! peer parent-descriptor :fork-1 self-id system-lookup))
;; … write on the fork branch (single-writer, isolated) …
;; MERGE it back into the parent branch (fail-safe on conflicts).
(wps/merge-fork-remote! fork-desc system-lookup)
```

- `wp/fork-descriptor` (pure) derives the fork descriptor: a fresh
  `fork-branch`, claims `self-id`, and anchors `:fork-of` to the parent
  heads (the merge-base). Because the store is content-addressed with
  structural sharing, a peer already following the parent transfers only
  the new **branch pointer** — no blocks (the O(1) distributed fork).
- `fork-remote!` `ygg/branch!`es each system at the parent head, claims the
  lease, and re-seats onto the writable fork. Isolated single-writer by
  design (continuous-bidirectional convergence is the `:bidirectional`
  role, a separate choice — it would contradict single-writer-per-branch).
- `merge-fork-remote!` checks out the parent branch and `ygg/merge!`s the
  **fork branch** back in (yggdrasil's `merge!` source is a branch keyword
  / snapshot-id, not a system). It is **fail-safe**: unless `:force` /
  `:strategy` is given it first collects per-system `ygg/conflicts` between
  the parent + fork snapshots and aborts the whole merge if any conflict
  (or an indeterminate, throwing detector) is found.

### Single-writer lease

A descriptor's `:owner` is the single-writer lease: `wp/writable?` /
`wp/peer-writable?` gate local writes, and `wp/claim` stamps it. No owner
⇒ read-only for everyone (fork to write, then claim). Ownership rides the
same `signal_sync`'d descriptor channel, so hand-off is just a new
descriptor.

## Running Distributed Tests

The distributed test suite uses `:test` alias, which pulls in
`distributed-scope` (and transitively, `kabel`):

```bash
clj -M:test
```

Test files in `test/org/replikativ/spindel/distributed/`:

| File | Coverage |
|------|----------|
| `bridge_test.cljc` | `spin↔chan` conversion edge cases (success, nil, error). |
| `macro_test.clj` | `defn-spin-remote` macro: free-variable analysis, argument-vector validation. |
| `integration_test.clj` | End-to-end with kabel WebSocket peers — two contexts, one remote call, result delivered. |
| `signal_sync_test.cljc` | `apply-incoming!` dispatch (δ / state / LWW), convergent join, CAS commit. |
| `bidirectional_sync_test.clj` | Two-writer / fan-in / late-joiner convergence over a real kabel socket. |
| `cross_system_sync_test.clj` | datahike + yggdrasil stores replicate over ONE wire / canonical serializer. |
| `convergent_sync_integration_test.clj`, `composite_join_test.clj` | convergent sync + composite join paths. |
| `workspace_peer_test.cljc`, `workspace_peer_sync_test.cljc` | pure gate / lease / `fork-descriptor` / `wire-topology!` `:role` dispatch / `fork-remote!` / `merge-fork-remote!` (mock-injected). |
| `workspace_peer_integration_test.clj` | workspace re-seat wiring. |
| `workspace_fork_e2e_test.clj` | fork→write→merge against a REAL yggdrasil datahike system (`branch!`/`checkout`/`merge!`). |
| `workspace_wire_topology_e2e_test.clj` | two-peer `:bidirectional` `wire-topology!` convergence over a real kabel socket. |

## See Also

- [Forking](forking.md) — fork-context, snapshot-context, and how
  context-id addressing relates to fork lineage.
- [SCI Integration](sci-integration.md) — sandboxed execution; can
  be combined with distributed scopes to run untrusted code on a
  remote peer.
- [distributed-scope](https://github.com/simm-is/distributed-scope)
  — the underlying RPC layer over kabel.
- [kabel](https://github.com/replikativ/kabel) — WebSocket transport.
