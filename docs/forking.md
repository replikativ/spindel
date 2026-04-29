# Forking

Spindel supports **O(1) copy-on-write forking** of execution contexts. Forks share state with their parent via structural sharing and store mutations locally, enabling isolated execution branches, speculative computation, and checkpointing.

## Fork a Context

```clojure
(require '[org.replikativ.spindel.engine.context :as ctx]
         '[org.replikativ.spindel.engine.core :as ec]
         '[org.replikativ.spindel.signal :as sig])

(def ctx-main (ctx/create-execution-context))

;; Create signals in the main context
(binding [ec/*execution-context* ctx-main]
  (def counter (sig/signal 0))
  (swap! counter inc))   ;; counter = 1

;; Fork — O(1), creates an overlay
(def ctx-fork (ctx/fork-context ctx-main))
```

### Fork Options

```clojure
(ctx/fork-context parent-ctx
  :state-updates {...}     ;; initial overlay state
  :bindings {:key "val"}   ;; fork-local configuration (merged with parent)
  :metadata {:label "my-fork"}
  :process-id 42)          ;; override auto-assigned process ID
```

## Isolation

Forks and parents are fully isolated — mutations in one don't affect the other:

```clojure
;; Mutate in fork
(binding [ec/*execution-context* ctx-fork]
  (swap! counter inc)    ;; fork: counter = 2
  (swap! counter inc)    ;; fork: counter = 3
  @counter)              ;; => 3

;; Parent unchanged
(binding [ec/*execution-context* ctx-main]
  @counter)              ;; => 1
```

### Isolation Guarantees

| Operation | Parent sees? | Fork sees? |
|-----------|--------------|------------|
| Fork reads parent state | N/A | Yes (via fallback) |
| Fork mutates state | No | Yes (in overlay) |
| Parent mutates state | Yes | No (isolated) |
| Fork creates new state | No | Yes (in overlay) |

## Overlay Backend

Forked contexts use an **overlay backend** that:

1. **Shares parent state** via structural sharing (memory efficient)
2. **Stores mutations locally** in the overlay (copy-on-write)
3. **Falls back to parent** for reads of unmodified state

The fork itself is O(1) — only the overlay structure is created. State is copied lazily on first write to each key.

## What forks share with their parent

A fork is fully isolated for *state*, but a few resources are shared with
the parent context for performance:

- **Executor**: Both parent and fork submit work to the same executor
  (thread pool on JVM, event loop on CLJS). Concurrent forks compete for
  the same workers. If you need an isolated executor, create a fresh root
  context instead.
- **Drain thread / drain signal** (JVM): One background thread drains
  events for the parent and all of its forks.
- **External side effects**: HTTP requests, file I/O, console output,
  etc. are not isolated. Spins that observably do something to the
  outside world will do it from every fork that runs them.

If you need an external resource to fork along with the context, register
it under `[:external-refs]` and implement the `PForkable` protocol so
`fork-context` can ask it to copy itself.

## Fork and the spin cache

Spin results live on each `SpinNode` in the unified `:nodes` map. A fork:

- **Inherits the parent's cached results** through overlay read-through.
  If the parent has a clean `:result` for spin X, the fork sees the same
  result on first read — no re-execution.
- **Invalidates the fork's local copy** when a dependency is mutated
  inside the fork. Dirty propagation walks observers in the fork's
  overlay, leaving the parent's SpinNode untouched.
- **Recomputes on the fork's view** the next time the spin is invoked
  in the fork.

The parent's cache is never observed to be stale by the fork: either the
fork reads the parent's value (because the dependency is unchanged in the
fork too), or the fork has its own copy (because the dependency moved in
the fork).

## Snapshots

Snapshots create an immutable copy of a context's state. Unlike forks, snapshots are completely independent (no parent reference).

```clojure
;; Create immutable snapshot
(def snapshot (ctx/snapshot-context ctx-main))
```

### Snapshot Options

```clojure
(ctx/snapshot-context ctx-main
  :clean-in-flight? true    ;; mark in-flight spins as dirty (default: true)
  :include-pending? true)   ;; include pending events (default: true)
```

### Restore a Snapshot

Convert a snapshot back to a live context:

```clojure
(def ctx-restored (ctx/restore-snapshot snapshot))

(binding [ec/*execution-context* ctx-restored]
  @counter)  ;; => 1 (same as when snapshot was taken)
```

### Restore Options

```clojure
(ctx/restore-snapshot snapshot
  :drain-events? true)   ;; process pending events after restore (default: true)
```

## Serialization

Contexts can be serialized to EDN for checkpointing, distribution, or persistence:

```clojure
;; Serialize to EDN string
(def edn-str (ctx/serialize-context ctx-main))

;; Deserialize back to a live context
(def ctx-deserialized
  (-> (ctx/deserialize-context edn-str (ctx/get-executor ctx-main))
      ctx/restore-snapshot))
```

`serialize-context` creates a snapshot internally if the context isn't already a snapshot.

## Rebuild Execution State

After deserializing a context, continuations are lost (they're not serializable). The **rebuild** mechanism re-executes the model function to restore continuations:

```clojure
;; Macro version: prepare, execute, finalize
(def rebuilt-ctx
  (ctx/with-rebuild-context snapshot {}
    @(my-model-fn)))  ;; re-executes to rebuild continuations

;; Manual version for more control
(let [prep-ctx (ctx/prepare-rebuild-context snapshot
                 :initial-chain-head some-hash)
      _        (binding [ec/*execution-context* prep-ctx]
                 @(my-model-fn))
      final    (ctx/finalize-rebuild-context prep-ctx)]
  final)
```

In rebuild mode, spin bodies execute but return cached values. This rebuilds the dependency graph and continuations without changing computed results.

## Use Cases

### Speculative Computation

Try different approaches, keep the best:

```clojure
(defn try-strategies [ctx strategies]
  (let [forks (mapv (fn [s]
                      {:strategy s
                       :ctx (ctx/fork-context ctx)})
                    strategies)]
    ;; Run each strategy in its fork
    (doseq [{:keys [strategy ctx]} forks]
      (binding [ec/*execution-context* ctx]
        (apply-strategy strategy)))

    ;; Pick the best result
    (let [best (select-best forks)]
      (:ctx best))))
```

### Parallel Inference

Run multiple agents sharing common state:

```clojure
(defn create-agents [base-ctx n]
  (mapv (fn [i]
          (ctx/fork-context base-ctx
            :bindings {:agent-id i}
            :metadata {:label (str "agent-" i)}))
        (range n)))

;; Each agent operates independently
;; All share parent's base state (signals, cached spins)
;; Mutations isolated to each agent's overlay
```

### Checkpointing and Rollback

Save state and restore on failure:

```clojure
;; Save checkpoint
(def checkpoint (ctx/snapshot-context ctx-main))

;; Do risky work...
(try
  (binding [ec/*execution-context* ctx-main]
    (risky-operation!))
  (catch Exception e
    ;; Rollback by restoring checkpoint
    (def ctx-main (ctx/restore-snapshot checkpoint))))
```

### Deterministic Testing

Use simulation contexts for reproducible tests:

```clojure
(def test-ctx (ctx/create-simulation-context))

;; Virtual time mode — time advances explicitly
(binding [ec/*execution-context* test-ctx]
  ;; ... set up spins that use sleep/timeout ...

  ;; Advance time to trigger scheduled events
  (ctx/advance-time! test-ctx 1000)  ;; advance 1 second

  ;; Check results deterministically
  (assert (= 42 @my-spin)))
```

### Fork Lineage (Elle Compatibility)

Track fork lineage for distributed systems testing:

```clojure
(ctx/get-process-id ctx-fork)          ;; => 1
(ctx/get-parent-process-id ctx-fork)   ;; => 0
(ctx/get-fork-lineage ctx-fork)        ;; => [0 1]

(ctx/root-context? ctx-main)           ;; => true
(ctx/root-context? ctx-fork)           ;; => false
(ctx/fork-depth ctx-fork)              ;; => 1
```

## Context Lifecycle

```clojure
;; Create root context
(def ctx (ctx/create-execution-context))

;; Fork (shares drain thread with parent)
(def fork (ctx/fork-context ctx))

;; Stop root context (stops background drain thread)
(ctx/stop-context! ctx)
;; Safe no-op on forks — they share the parent's drain thread

;; Full shutdown (stops drain + closes executor)
(ctx/close-context! ctx)
;; Only use when certain no async work remains
```

## See Also

- [Getting Started](getting-started.md) — Basic tutorial
- [Concepts](concepts.md) — Execution context explained
- [SCI Integration](sci-integration.md) — Agent isolation with forked contexts
