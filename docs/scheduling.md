# Scheduling and Execution Model

This document explains how spindel processes events, executes spins, and propagates reactive updates. Understanding this helps when reasoning about ordering guarantees, concurrency behavior, and what happens under the hood when a signal changes.

For the architectural side — state shape, deterministic addressing,
CPS / trampoline mechanics, overlay backend, memory invariants — see
[`engine.md`](engine.md).

## Overview

Spindel uses an **event-driven, single-drainer model**: all reactive work is driven by an event queue. Signal changes, spin completions, deferred deliveries, mailbox posts, and one-shot spin executions are enqueued as events and processed by a drain loop. Only one drain runs at a time per context, which provides the ordering guarantees that make glitch-free updates possible.

```
swap! signal       deliver! deferred    post! mailbox    @spin
   │                   │                   │             │
   │ :signal-change    │ :deferred-       │ :mailbox-    │ :spin-
   │                   │  delivery        │  post        │  execution
   ▼                   ▼                   ▼             ▼
   └───────────────────┴───────────────────┴─────────────┘
                              │
                              ▼
        :engine/pending queue   ◀── :spin-completion events
                                    (cascade from spin body resolution)
                              │
                              ▼
        drain-events! (CAS lock: :engine/draining?)
                              │
                              ▼
        process-event! per event (per-event try/catch)
```

On the JVM a background daemon thread runs this drain loop continuously. On ClojureScript the JS event loop fills the same role.

## Executors

The executor controls *where* spin code runs — which thread or scheduling mechanism executes a spin body.

### JVM executors

| Executor | When to use |
|----------|-------------|
| Virtual threads (default, JVM 21+) | Production. `virtual-thread-executor` returns a `PoolExecutor` wrapping `Executors/newVirtualThreadPerTaskExecutor` — each submitted task gets a fresh virtual thread; blocking is cheap. |
| `ForkJoinPoolExecutor` (default, JVM < 21) | Production. Work-stealing pool; uses `managedBlock` to create compensating threads when workers block on a `CountDownLatch`. Prevents deadlock during parallel observer dispatch. |
| `SynchronousExecutor` | Tests and simulation. Executes on the calling thread immediately; deterministic. `execute-after!` ignores the delay (time is controlled via `advance-time!`). |

The default executor is selected automatically:

```clojure
(create-execution-context)                 ; uses default-executor automatically
(create-execution-context :executor (fork-join-executor :parallelism 4))
(create-execution-context :executor (synchronous-executor))
```

All executors capture the relevant dynamic bindings at submission time and restore them inside the task — this is what makes the reactive context available on worker threads without explicit passing. JVM uses `capture-targeted-bindings` which grabs the four `bindings.cljc` vars plus `ec/*execution-context*` (5 vars total) and restores via `with-bindings`. CLJS uses `bindings/capture-bindings` (the same four vars) and restores via `bindings/restore-bindings`; `*execution-context*` follows naturally because the CLJS executor body runs in the same JS event-loop step.

### Delayed execution (`execute-after!`)

Both JVM executors delegate `execute-after!` to a **shared module-level** `ScheduledThreadPoolExecutor`: one daemon thread named `laufzeit-delay`, defined once via `defonce` in `engine/executor.cljc`. After the delay fires it calls back into the owning executor's `execute!` to run the spin-fn on the regular work pool. CLJS uses `js/setTimeout` with the requested delay directly. `comb/sleep`, `comb/timeout`, `comb/debounce`, and `comb/throttle` all route through `execute-after!`.

### ClojureScript executor

The `EventLoopExecutor` schedules work via `setTimeout 0`, yielding control to the browser/Node.js event loop between each task. This is the only executor available on ClojureScript.

## The Drain Thread

On the JVM, each root execution context owns a **background daemon drain thread**. It wakes instantly when new work arrives and returns to a zero-CPU wait when idle:

```
while @running:
    drain-signal.poll(1s)     ; blocks until signaled or 1s safety timeout
    if ctx still alive:
        drain-events!(ctx)
```

Wakeup is via a `LinkedBlockingQueue` (`drain-signal`). Anything that enqueues an event calls `trigger-drain!`, which does `.offer(:drain)` on the signal **and** also submits a `drain-events!` task to the executor — so the wake can race a pool worker. The 1-second poll is a safety net only; in practice the thread is woken immediately.

The drain thread holds a `WeakReference` to the context so that an abandoned context becomes GC-eligible and the registered `Cleaner` can stop the thread.

Forked contexts do not start their own drain threads. They share the parent's `drain-thread`, `drain-signal`, `drain-active`, `running`, and `executor` (all copied at fork construction in `engine/context.cljc`). The fork-local pieces are only `:engine/pending` and `:engine/draining?`, which live in the fork's overlay so the fork's events don't intermix with the parent's. `trigger-drain!` from a fork therefore both wakes the parent's drain-signal *and* submits a fork-tagged `drain-events!` to the executor — whichever entry point runs first claims the fork's draining lock and processes the fork's queue. See [`forking.md`](forking.md) for the full fork-resource-sharing table.

## The Drain Lock

`drain-events!` uses a CAS on `:engine/draining?` to ensure only one drain session runs at a time:

```
1. Check entry guard: if running=false, return immediately (context stopped)
2. Increment drain-active counter
3. CAS :engine/draining? false → true
   └─ fails: another drain is running, return (outer finally decrements drain-active)
   └─ succeeds: begin drain session
4. Loop:
   ├─ Check @running at top of each iteration; if false, exit with whatever's still in :pending
   └─ Dequeue next event; if none, exit loop
       └─ Wrap process-event! in try/catch:
           ├─ :spin-execution error → reject-fn the event's callback
           ├─ :spin-completion error → write {:variant :error :payload e} into each
           │                          waiting parent's :nodes entry
           └─ other event-types → log only
5. Release lock: CAS :engine/draining? true → false
6. Re-trigger: if :pending is non-empty, schedule another drain
   (events may have arrived in the gap between last dequeue and lock release)
7. Outer finally: decrement drain-active
```

The per-event try/catch is critical: without it, one bad event would abort the whole drain session and strand every other queued event until the next signal.

Multiple threads may call `trigger-drain!` simultaneously — they all submit drain tasks to the executor, but only one acquires the lock. The others see the lock taken, return zero, and let the active drainer process everything.

The **re-trigger** at step 6 handles the inevitable race window:

```
Thread A dequeues last event
                              Thread B enqueues new event
Thread A releases lock
Thread A checks :pending → non-empty → re-triggers
```

Without the re-trigger, the new event would sit unprocessed until the next wakeup (up to 1 second).

## Event Types

| Event | When enqueued | What drain does |
|-------|--------------|-----------------|
| `:signal-change` | `swap!` / `reset!` on a signal | Marks dependent spins dirty, resumes track continuations, processes batch completions |
| `:spin-completion` | Spin body finishes | Resumes `await` continuations in parent spins |
| `:spin-execution` | `deref` on an uncached spin | Claims execution slot, runs spin body on executor |
| `:deferred-delivery` | `deliver!` on a `Deferred` | Delivers value and inline-resumes waiting continuations |
| `:mailbox-post` | `post!` on a `Mailbox` | Delivers message and inline-resumes the first waiter |

## Glitch-Free Signal Propagation

Spindel prevents **glitches** — the situation where a spin observes a half-updated reactive graph. Consider:

```clojure
(def price (signal 100))
(def tax   (spin (let [{:keys [new]} (track price)] (* new 0.2))))
(def total (spin (+ (await tax) (let [{:keys [new]} (track price)] new))))
```

If `price` changes to 200 and `total` re-executes before `tax` does, it sees `tax=20` (stale) and `price=200` (fresh) — a glitch. Spindel prevents this with a **single-queue topological-dispatch** model:

### Topological observer dispatch

When a `:signal-change` event is processed, the engine:

0. Creates a fresh `Batch` record at `:engine/current-batch` carrying the signal-id, a monotonic `:generation` counter, a `:processed` atom of completed spin-ids, and a `:resumed-conts` atom of `[parent-id child-id generation]` triples — used to dedupe `:spin-completion` await-cont resumes within this batch.
1. Calls **`clear-all-await-continuations!`** — clears every ephemeral await continuation across all spins at the generation boundary. Without this, an `await` registered against a *previous* version of the signal would fire in this cycle alongside the new one, producing duplicate work.
2. Computes the observer set in **topological order** over the live observer graph (dependents always after dependencies). The graph is `signal.observers` — eagerly maintained: every `(track sig)` and `(await child)` registers the spin as an observer of its dep at the moment of the call, *not* at body-completion time (see [Dependency Tracking](#dependency-tracking-and-the-graph) below).
3. Filters out observers that are *descendants* of other observers in this batch (a descendant will be naturally re-resumed by its ancestor's completion event, so dispatching it directly here would cause duplicate work).
4. Escalates each remaining observer to its root await-ancestor (`find-root-await-ancestor`) — the spin that actually needs to resume in this batch. Suspended descendants on `await` chains anchor at the right level.
5. Resumes each observer's `track` continuation with the fresh signal value. Observers with `>1` entry are dispatched in parallel on the ForkJoinPool (JVM), using `CountDownLatch` + `managedBlock` to wait for all of them. CLJS always dispatches sequentially.

### Cascade events

While observer bodies execute, they may produce more events: `:spin-completion` when a body resolves, `:signal-change` if the body itself swaps a signal, etc. These all flow through the **single** `:engine/pending` queue and are drained naturally by the outer drain loop after the current event finishes. There is no separate "Phase 2" queue and no blocking wait — the redesign collapsed those into the unified FIFO. The drain logic lives in `engine/impl/simple.cljc` (`drain-events!`, `process-event!`); the earlier two-stage commit model used to deadlock on Deferred suspension and is fully gone.

The descendant-filtering + ancestor-escalation step preserves the no-glitch guarantee without a per-batch barrier: within one `:signal-change` dispatch all directly-affected observers resume against the fresh signal value, and downstream completions propagate via the same drain in FIFO order — no spin ever sees a partially-updated graph.

### Dynamically-discovered dependencies

Topological dispatch orders the graph *as it exists when the signal changes*. But a spin re-tracks its dependencies on every run (see [Dependency Tracking](#dependency-tracking-and-the-graph) below), so a conditional branch can establish a brand-new edge that only appears *after* the spin re-runs:

```clojure
(spin (if (= 42 (:new (track x)))
        (await k)   ;; edge to `k` exists only when x = 42
        0))
```

A topological sort built before re-execution cannot order `k` ahead of this spin — that edge did not exist yet. Correctness in this case does not come from the sort; it comes from `await` being demand-driven.

`await-spin` (`effects/await.cljc`) takes the **fast path** — return the child's cached result — only when the child has a cached result, is **not dirty**, and either we are not inside a `:signal-change` batch *or* the child was already processed in this batch (`:processed` set). Otherwise it takes the **slow path**: re-execute the child's body, which re-reads the child's own `track` / `await` dependencies recursively; the awaiting spin suspends on a continuation and resumes with the freshly-computed value.

Two independent guards keep this robust mid-propagation:

- **Dirty flag** — `mark-dirty!` BFS-marks the changed signal's transitive observers dirty, so awaiting any of them refuses the fast path.
- **Batch `:processed` set** — a spin newly pulled into the graph by a conditional `await` was never marked dirty, but it is also not in `:processed`, so the fast path is refused and the child is re-executed anyway.

So a dependency chain — including edges discovered *during* this propagation — is always walked in the true data-flow order of the current computation. The topological sort is a scheduling optimization that avoids redundant re-runs for the common static graph; it is not the correctness mechanism for dynamic dependencies. See `test/org/replikativ/spindel/continuation_glitch_test.clj` and [`concepts.md`](concepts.md#dynamic-dependencies).

## Dependency Tracking and the Graph

Spindel tracks dependencies automatically at runtime, on a **unified-subscription** model: observer registration happens *eagerly* at the moment the body calls `track` or `await`, not deferred to body completion.

During spin execution:

- `(track signal)` calls `ec/deps-track-signal!` which does two things atomically:
  1. Records `signal-id` in the spin's transient `[:spin-tracking spin-id :signals]` set (the diff baseline for this run).
  2. Registers the spin in `signal.observers` immediately, so a `swap!` that races the body completion is still seen.
- `(await child)` calls `ec/deps-track-spin!` symmetrically — records into `[:spin-tracking spin-id :spins]` and registers the parent in `child.observers` right away.

This **eager registration closes the "first-run signal-change gap"**: under the older lazy model, a signal mutated between the first `(track sig)` call and the body's resolve would not see the spin as an observer yet, and the spin would never re-run. Source comment in `track-signal-dep!` (engine/impl/simple.cljc) cites this directly.

When a spin completes, `record-deps!` runs in the body's resolve callback and does *not* add observers (they're already there). Its three responsibilities:

1. **Snapshot** the transient `:spin-tracking[spin-id]` set into `spin-node.deps` — the baseline for the *next* run's diff.
2. **Prune** the spin from any signal's / child's observer list that was present in the previous run's deps but absent from this one (conditional tracking: a `(when … (track sig))` that didn't enter the branch this time).
3. **Clear** the transient `:spin-tracking[spin-id]` entry.

All three happen in a single atomic `swap-state!` to keep the dep snapshot internally consistent.

Observer sets are used both for dirty propagation (a `:signal-change` event hands its observers to the dispatch loop above) and for topological ordering during signal-change processing.

The topological order is computed fresh on each signal change from the live observer graph — not cached — so it always reflects the current dependency structure.

## Spin Execution Flow

When you deref a spin:

```
1. Inside a drain thread? → throw ex-info ("would deadlock").
                            Use `spawn!` (fire-and-forget) or `await`
                            (spin-to-spin) instead.

2. Is the spin cached and clean?
   └─ yes → return cached result immediately (no work enqueued)
   └─ no  → enqueue :spin-execution event, block calling thread
            on a promise (JVM) / throw "not supported on CLJS"

3. drain-events! picks up :spin-execution
   └─ try-claim-execution!: atomically check if already running or cached
      └─ already cached (clean) → deliver result via callback
      └─ already running → add callbacks to pending-callbacks list
      └─ not running, not cached → claim (set :running?=true), execute spin body

4. Spin body runs on executor (worker thread or virtual thread)
   └─ effects (await/track) may suspend body → return ::incomplete
   └─ body completes → cache-result! + enqueue :spin-completion

5. :spin-completion enqueued
   └─ drain resumes all parent await continuations
   └─ pending-callbacks notified (other derefs waiting for same spin)
```

The `try-claim-execution!` CAS prevents duplicate execution when multiple `:spin-execution` events arrive for the same spin (e.g., concurrent derefs). Only the first succeeds; the rest add their callbacks to be notified on completion.

## Context Lifecycle

### Starting

`create-execution-context` starts the drain thread immediately. The thread is a daemon so it does not prevent JVM exit if the context is abandoned.

### Stopping

`stop-context!` shuts down cleanly in four steps:

1. `(reset! running false)` — signals the entry guard and all future drain calls to exit
2. `.offer(:stop)` on `drain-signal` — wakes the drain thread immediately
3. Polls `drain-active` down to 0 with `LockSupport/parkNanos 100000` (100µs intervals), bounded by a **5-second outer deadline** — a safety valve for a deadlocked spin body. Reaching it means a real bug worth investigating; the shutdown returns anyway so the caller doesn't hang.
4. `.join(drain-thread 200ms)` — waits for the daemon thread loop to actually terminate.

After step 3, the entry guard guarantees no new drain will ever enter active processing for this context. After step 4, the thread is fully exited.

`close-context!` calls `stop-context!` and additionally shuts down the executor.

### GC-based cleanup

If a context is abandoned without calling `stop-context!` (common in tests), Java's `Cleaner` automatically stops the drain thread when the context object is collected. The Cleaner registration uses phantom references, so it fires once the context has no more strong references — calling `(reset! running false)` and waking the drain thread.

Both root-context constructors register this Cleaner: `create-execution-context` (the normal entry point) and `deserialize-context` (when restoring a snapshot with a mutable backend). Earlier versions of `deserialize-context` spawned the drain thread without registering a Cleaner, leaking one daemon drain thread per call for the lifetime of the JVM.

This is a safety net, not a substitute for explicit cleanup. Use `stop-context!` in your lifecycle code.

## Fork Scheduling

The drain-thread + signal explanation [above](#the-drain-thread) covers what a fork shares with its parent (`drain-thread`, `drain-signal`, `drain-active`, `running`, `executor`) versus what stays fork-local (`:engine/pending`, `:engine/draining?` — both in the fork's overlay). For the full table of shared vs fork-local resources and the rationale, see [`forking.md`](forking.md).

The only thing worth re-stating here: a fork's `trigger-drain!` wakes the parent's drain-signal *and* submits to the shared executor, so reactive work in a fork drains on the same threads as the parent's work — but on fork-local state, so the two never block each other's queue progress.

## Platform Differences (JVM vs ClojureScript)

| Aspect | JVM | ClojureScript |
|--------|-----|---------------|
| Drain thread | Daemon thread, blocks on `LinkedBlockingQueue` | No drain thread; JS event loop |
| Executor | ForkJoinPool / virtual threads | `setTimeout 0` |
| Parallel observers | `CountDownLatch` + `managedBlock` | Always sequential (single-threaded) |
| `await-drain-complete!` | Blocks with `ForkJoinPool.managedBlock` + 100µs `parkNanos` | Returns current idle state, non-blocking |
| `@spin` deref | Blocks until complete | Not supported; use `run-spin!` callbacks |
