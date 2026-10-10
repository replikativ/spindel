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
  :process-id 42           ;; override auto-assigned process ID
  :executor executor       ;; optional; otherwise shares the parent scheduler
  :mode :frozen            ;; pin untouched state instead of following parent
  :forkable-components #{}) ;; optional capability attenuation
```

### Fork-selected world components

Some world state is not an FRP signal and is not a mergeable substrate: an
interpreter heap, capability table, or other process-local realization. Register
such state with `org.replikativ.spindel.engine.component/register!`. It returns
a stable `ComponentRef`; resolving that reference in a context selects the
realization belonging to that world. Values implement `PForkable`, the same
forking protocol already used by fork-aware signals.

Components are fork-local and are copied automatically by `fork-context`.
Passing `:forkable-components` explicitly selects the IDs available in the
child, so a fork can attenuate capabilities instead of inheriting all of them.
Components are runtime state, not settlement units: durable Yggdrasil systems
and their merge/discard authority remain governed by `ForkHandle`. Portable
snapshots deliberately omit components; an embedding reconstructs transient
realizations from durable source, configuration, and capability descriptors.

Component forks are restricted to rollback-free process-local values. Because
component realization can happen before a child handle exists, it must not
acquire a worktree, database branch, or other resource needing compensation.
Those substrates remain Yggdrasil systems acquired and settled through
`ForkHandle`; a component may hold the transient interpreter or client view over
them. Registration requires an explicit forkable or shared declaration, so a
mutable host object cannot be shared accidentally.

Host callbacks are effects outside copy-on-write state and are isolated by
default. A child completion is cached in that child but cannot fire a callback
registered by another world. Savepoint sessions and inference deliberately attach the
engine-only `:causal-follow` authority to callback edges that must survive
particle resampling. The authority belongs to the edge rather than mutable world
bindings, so interpreted code cannot promote its own egress. Engine listeners
and duplicate pending callbacks are always fork-local.

## Isolation

A fork is **fully isolated from parent for its own writes** (fork→parent never leaks) and **parent-following on shared paths** (parent's writes are visible in the fork until the fork shadows that path). Overlay forks are deliberately not symmetric snapshots — that asymmetry is what makes them efficient for speculative-with-rebase / Elle-style branching.

```clojure
;; Mutate in fork
(binding [ec/*execution-context* ctx-fork]
  (swap! counter inc)    ;; fork: counter = 2
  (swap! counter inc)    ;; fork: counter = 3
  @counter)              ;; => 3

;; Parent unchanged by fork's writes
(binding [ec/*execution-context* ctx-main]
  @counter)              ;; => 1
```

### Isolation Guarantees

| Operation | Parent sees? | Fork sees? |
|-----------|--------------|------------|
| Fork reads parent state | N/A | Yes (via overlay fall-through) |
| Fork mutates state | **No** — always isolated to fork's overlay | Yes (in overlay) |
| Parent mutates state on a *shared* path | Yes | **Yes, until fork shadows that path** — overlay-fork is parent-following by design |
| Parent mutates state on a *fork-local* path | Yes | No (fork has its own value or `nil`) |
| Fork creates new state | No | Yes (in overlay) |

**Fork-local paths** (full isolation, no fall-through from parent): `:continuations`, `:world/components`, `:world/forkable-components`, `:engine/pending`, `:engine/draining?`, `:engine/delayed-spins`, `:engine/timer-handles`, plus any path added via the OverlayBackend's `local-paths` set.

**Shared paths** (overlay fall-through, parent-following on reads): everything else, including `:nodes`, `:subscriptions`, `:spin-tracking`, `:atoms`, and `:engine/cancelled-tokens`.

### Following is a workspace, not a coherent view

A following fork falls through to the parent **per path, until it touches the
path** — and a read inside a spin touches it: `track` and `await` record their
observer on the node, which copies the node into the child's overlay. After
that the child keeps its value while the parent moves on. Nothing is pushed:
a spin in the child is not re-run by a change in the parent. So one child can
see a signal it read before a parent change next to a spin the parent
recomputed after it (`a = 1` beside `d = 10·a = 20`).

That is the intended contract for an isolated agent that follows along and is
rebased explicitly (`merge-fork-from-parent!` for durable systems). Anything
that needs a consistent view of the parent — inference particles, MCMC
proposals, counterfactual worlds, a what-if — uses a frozen fork.
`fork_coherence_test.clj` pins both behaviours.

### Live what-ifs

To watch the parent *as it would be* with some signals changed, and keep
watching as it moves, use `world.what-if`:

```clojure
(require '[org.replikativ.spindel.world.what-if :as wi])

(def w (wi/what-if parent {price 120}))            ; overrides {signal value}
(def stop (wi/watch! w #(spin (margin (track price) (track cost)))
                     (fn [m] (println "margin if price were 120:" m))))
(wi/freeze w)   ; a frozen copy of the current view: a world of its own
(wi/stop! w)
```

A what-if's view is a frozen fork of the parent *now*, with the overrides
written in. When the parent changes a signal that a watched computation
read, the next view is derived from the parent once it has settled, and the
watches run again. Each view is one moment of the parent, never a mix, and
overridden signals keep their override. A what-if owns no history and is
never settled; `freeze` it to keep a moment.

If you need fully-isolated semantics on a shared path — a fork that does not
track parent's later writes while remaining a writable child — use
`(fork-context parent :mode :frozen)`. This materializes the parent's complete
fork-time view once and uses it as the immutable base of the child's writable
overlay. Use `snapshot-context` when the result itself should be an immutable,
parentless checkpoint. The cancellation interaction with
`:engine/cancelled-tokens` (a shared path) is discussed in the source comments
at `src/org/replikativ/spindel/effects/await.cljc` (search for
`cancellable-external-pair`).

## Overlay Backend

Forked contexts use an **overlay backend** that:

1. **Shares parent state** via structural sharing (memory efficient)
2. **Stores mutations locally** in the overlay (copy-on-write)
3. **Falls back to parent** for reads of unmodified state

The fork itself is O(1) — only the overlay structure is created. State is copied lazily on first write to each key.

## What forks share with their parent

A fork is fully isolated for *state*, but a few resources are shared with
the parent context for performance:

- **Executor by default**: Parent and fork submit work to the same executor
  (thread pool on JVM, event loop on CLJS). Concurrent forks compete for
  the same workers. Pass `:executor` to `fork-context`/`ygg/fork!` when the
  child should use a separately managed scheduler.
- **Drain thread / drain signal** (JVM): One background thread drains
  events for the parent and all of its forks.
- **External side effects**: HTTP requests, file I/O, console output,
  etc. are not isolated. Spins that observably do something to the
  outside world will do it from every fork that runs them.

If an external resource has Yggdrasil fork/merge semantics, register it with
`org.replikativ.spindel.yggdrasil/register!` and fork through that namespace's
`fork!`. The returned `ForkHandle` wraps the execution-context fork and is the
single settlement authority for all selected registered systems.

## Fork registered systems and settle them affinely

```clojure
(require '[org.replikativ.spindel.yggdrasil :as ygg])

(def world
  (ygg/fork! {:systems #{:kb :repo}
              :purpose :proposal
              :owner :run-42}))

;; Work in the isolated reactive context and its Yggdrasil branches.
(binding [ec/*execution-context* (:child-ctx world)]
  (perform-work!))

;; Settlement is mutually exclusive and exactly once.
(ygg/merge-fork! world)       ; or discard-fork! / transfer-fork!
```

The portable value from `fork-descriptor` contains world identity, ancestry,
owner, policy, and per-system branch/basis data. It never contains the live
contexts or affine token.

After the world is physically quiescent, trusted host code may split one open
whole-world settlement capability into disjoint per-system capabilities:

```clojure
(def parts
  (ygg/partition-fork!
   world
   [{:systems #{:repo} :owner :code-review}
    {:systems #{:kb}   :owner :knowledge-review}]))
```

Partitioning consumes `world`. Every descriptor-named system must occur exactly
once; overlaps and omissions are rejected. All returned handles retain the same
`:fork/id` because they govern one execution world, while each has a distinct
`:fork/settlement-id`. `fork-diff`, `fork-conflicts`, `merge-fork!`,
`discard-fork!`, and `merge-fork-from-parent!` operate only on that handle's
scope.

This divides settlement authority, not arbitrary runtime access: the handles
share the child execution context and are host capabilities, not sandbox values.
The system registry must also still match the creation descriptor; worlds with
uncheckpointed child-only systems are refused until those systems receive a
portable basis entry. A successful partition freezes registration in that child
world (including recursive partitions), closing the race between exhaustive
scope validation and later `register!`/`unregister!` calls. Settlement also fails
closed if a scoped system is removed or replaced in the parent; it is never
silently reclassified as child-only.

`merge-fork-from-parent!` temporarily leases the same affine authority as
`:advancing`. Transfer, partition, merge, and discard are rejected until the
advance completes. A read-only preflight failure reopens the handle; failure
after durable mutation begins leaves it `:incomplete` for explicit recovery.

## Copies: alternatives that settle at most once

`merge-fork!` and `discard-fork!` settle a fork exactly once; `partition-fork!`
splits that one settlement over disjoint systems, and every part settles. A
*copy* is the other split: `(ygg/copy-fork! handle k)` consumes an open handle
and returns `k` frozen forks of its world as it is now — alternatives that
share ONE settlement. The first member to `merge-fork!` settles the family:
its world merges into the copied world and that into the original parent.
Every other member can then only `discard-fork!`
(`::copy-family-settled`); discarding every copy of a world discards that
world. Copies of a member join the same family, so resampling a particle
twice still ends in at most one settlement.

```clojure
(let [w (ygg/fork!)
      [a b c] (ygg/copy-fork! w 3)]   ; w is consumed
  ... run a, b, c ...
  (ygg/merge-fork! b)                 ; b → w → parent
  (ygg/discard-fork! a)
  (ygg/discard-fork! c))
```

Whether a world may be copied depends on its systems. `register!` takes a
structural grade:

| Grade | Copy | Discard | Examples |
|---|---|---|---|
| `:unrestricted` (default) | yes | yes | datahike/git branches, CRDTs, drafts |
| `:relevant` | yes | only by compensating (`:compensate`) | posted ledger entries, audit trails |
| `:linear` | no — unless its linear operations are deferred (`:realize`) | no | legal numbers, period seals, sends |
| `:affine` | no | yes | live handles, streams |
| `:divisible` | split (not yet) | return (not yet) | budgets |

A system forked as `:kind :shared` counts as `:linear`. `copy-fork!` refuses
(`::copy-forbidden`, naming the systems) and leaves the handle open when a
system may not be copied. Two hooks carry the rest:

- `:compensate` runs before any fork holding the system is discarded, with
  `{:system-id :child-ctx :parent-ctx :fork-id}` — what a relevant system does
  instead of dropping state (e.g. post reversals). If it throws, the fork
  stays open.
- `:realize` runs when a fork holding the system merges into a world that is
  not itself a fork. A copy family merges through the copied world first, so
  a deferred linear operation — a gapless legal number — happens once, for the
  one world that settles, never for a discarded alternative.

Copy families settle synchronously (JVM); a member cannot be partitioned.

### Reconciled settlement: several copies land together

When copies did *different* work rather than competing alternatives — agents
each drafting their own invoices, say — several of them may settle together,
provided their contributions are disjoint:

```clojure
(ygg/family-review [a b c])   ; {:tier :trivial|:reviewable|:conflict
                              ;  :contributions [...] :conflicts [...]}
(ygg/settle-family! [a c])    ; the chosen members; discard the rest
```

A system that must not be merged as state (a legal book) settles by
**intents**: registered with `:intents`, it reports what a world did as
intents with a stable `:intent/id` and a `:footprint` (the keys it claims — a
bank line it matched, an order it billed), and its `:stamp` applies them to the
parent. Other systems merge as state; with a `:footprint` hook they report the
keys they changed, without one two members that both changed them conflict.
A convergent system never conflicts: its merges commute.

Settlement requires that no footprint key is claimed by two members (the same
intent in two members counts once). Otherwise `family-review` reports
`:conflict` and `settle-family!` throws `::family-conflict` without changing
anything — conflicts are data, for a person or an agent to decide, never
resolved by picking one side's state. Then each member's ordinary systems
merge into the copied world, it into its parent, and every intent — the copied
world's own first, then the members' by fork id — is stamped into that parent
at once, with `:final?` true when the parent is not a fork. A stamp that throws
leaves the family `:failed`; `settle-family!` retries it, so stamps must be
idempotent per intent.

The tiers are the ones dvergr's fork review and simmis' task routing use: a
`:trivial` family can settle automatically, a `:reviewable` one goes to an
agent or a person, a `:conflict` one needs a decision about which intents to
drop.

### Every world settles intent systems this way

An intent system is never merged as state, whatever the settlement: a plain
`merge-fork!` of a single world, the winner of an at-most-one family, and a
reconciled family all extract intents and stamp them into the parent. Each
world is autonomous — an agent books, numbers and reverses in its world as in
the root — and the parent decides what that becomes when it takes the world
in. The intents are also checked against what the parent itself claimed
since the fork (`:parent-footprint`): a bank line the parent matched
meanwhile makes the merge throw `::merge-conflict` without changing anything.
Settlement results carry `:stamps`, what each system's stamp returned (a
renumber map, say). A stamp that fails after a single merge stays pending in
the parent; `retry-stamps!` retries it.

Long-lived worlds settle as they go:

```clojure
(ygg/checkpoint! w)   ; stamp the intents so far, rebase the world, keep it open
```

A checkpoint stamps the world's intents into the parent and re-forks those
systems from the parent's new head, so the world continues with the settled
state and the next checkpoint (or the final merge) carries only what came
after. The parent's record stays current, and it can close a period once the
worlds with entries in it have checkpointed.

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

### Forking with an un-drained change

There is one subtlety when you fork while a signal change is still
**pending** (swapped but not yet drained). `fork-context` resets
`:engine/pending` to `[]`, so the fork drops that eager recompute trigger.
This is safe for the **reactive** programming model: a spin in the fork
that observes a stale-clean derived spin via `await`/`track` recomputes it
against the new value — the generation guard refuses the awaited spin's
stale fast-path. Spin recompute is driven by the per-spin `:dirty` flag
plus that generation guard, *not* by the pending queue, so quiescence
before forking is an **optimization, not a correctness requirement**.

The exception is the discouraged path: a raw `@deref` of a stale-clean
spin returns the cached value without recomputing (the
[don't-`@deref`-spins-outside-the-REPL rule](getting-started.md)) — and
across a fork that staleness is *permanent* (the parent eventually drains
and re-dirties; the fork dropped its copy of the pending event and won't).
Observe forked spins reactively (`await`/`track`), never with `@`.

### Cross-system / distributed fork

The same O(1) copy-on-write idea is lifted across peers over yggdrasil
branches by `fork-remote!` / `merge-fork-remote!`: branch off a *followed*
remote checkout into an isolated single-writer branch, write, then merge
back on demand via the `:fork-of` merge-base. See
[Distributed → Workspace Reflection & Cross-System Forking](distributed.md#workspace-reflection--cross-system-forking).

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

;; Fork (shares the executor and running flag with its parent)
(def fork (ctx/fork-context ctx))

;; Stop root context (no drain mutates state after it returns)
(ctx/stop-context! ctx)
;; Safe no-op on forks — they share the parent's running flag

;; Full shutdown (stops drain + closes executor)
(ctx/close-context! ctx)
;; Only use when certain no async work remains
```

## See Also

- [Getting Started](getting-started.md) — Basic tutorial
- [Concepts](concepts.md) — Execution context explained
- [Engine](engine.md) — Overlay-backend mechanics, fork-local vs shared paths, drain scheduling across forks, the full architectural picture
- [SCI Integration](sci-integration.md) — Agent isolation with forked contexts
