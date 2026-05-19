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
  — signal replication across peers.

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

## See Also

- [Forking](forking.md) — fork-context, snapshot-context, and how
  context-id addressing relates to fork lineage.
- [SCI Integration](sci-integration.md) — sandboxed execution; can
  be combined with distributed scopes to run untrusted code on a
  remote peer.
- [distributed-scope](https://github.com/simm-is/distributed-scope)
  — the underlying RPC layer over kabel.
- [kabel](https://github.com/replikativ/kabel) — WebSocket transport.
