# Scheduling and Execution Model

This document explains how spindel processes events, executes spins, and propagates reactive updates. Understanding this helps when reasoning about ordering guarantees, concurrency behavior, and what happens under the hood when a signal changes.

## Overview

Spindel uses an **event-driven, single-drainer model**: all reactive work is driven by an event queue. Signal changes, spin completions, and deferred deliveries are all enqueued as events and processed by a drain loop. Only one drain runs at a time, which provides the ordering guarantees that make glitch-free updates possible.

```
Signal swap!
     │
     ▼
:engine/pending queue  ←─── :spin-completion events
     │                 ←─── :deferred-delivery events
     │                 ←─── :spin-execution events
     ▼
drain-events! (CAS lock: :engine/draining?)
     │
     ▼
process-event! per event
```

On the JVM a background daemon thread runs this drain loop continuously. On ClojureScript the JS event loop fills the same role.

## Executors

The executor controls *where* spin code runs — which thread or scheduling mechanism executes a spin body.

### JVM executors

| Executor | When to use |
|----------|-------------|
| Virtual threads (default, JVM 21+) | Production. Each task gets its own virtual thread; blocking is free. |
| `ForkJoinPoolExecutor` (default, JVM < 21) | Production. Work-stealing pool; uses `managedBlock` to create compensating threads when workers block on a `CountDownLatch`. Prevents deadlock during parallel observer dispatch. |
| `SynchronousExecutor` | Tests and simulation. Executes on the calling thread immediately; deterministic. |

The default executor is selected automatically:

```clojure
(create-execution-context)                 ; uses default-executor automatically
(create-execution-context :executor (fork-join-executor :parallelism 4))
(create-execution-context :executor (synchronous-executor))
```

All executors capture the current dynamic bindings (`*execution-context*`, `*spin-id*`, etc.) at submission time and restore them inside the task. This is what makes the reactive context available on worker threads without explicit passing.

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

Wakeup is via a `LinkedBlockingQueue` (`drain-signal`). Anything that enqueues an event calls `trigger-drain!`, which does `.offer(:drain)` — waking the thread within microseconds. The 1-second poll is a safety net only; in practice the thread is woken immediately.

Forked contexts do not start their own drain threads. They share the root's drain infrastructure: when a fork enqueues an event, `trigger-drain!` submits a `drain-events!` task to the executor, which the ForkJoinPool handles.

## The Drain Lock

`drain-events!` uses a CAS on `:engine/draining?` to ensure only one drain session runs at a time:

```
1. Check entry guard: if running=false, return immediately (context stopped)
2. Increment drain-active counter
3. CAS :engine/draining? false → true
   └─ fails: another drain is running, return (outer finally decrements drain-active)
   └─ succeeds: begin drain session
4. Loop: dequeue and process events until queue empty
   └─ after each event: check running flag, abort if context was stopped
5. Release lock: CAS :engine/draining? true → false
6. Re-trigger: if :pending is non-empty, schedule another drain
   (events may have arrived in the gap between last dequeue and lock release)
7. Outer finally: decrement drain-active
```

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

1. Computes the observer set in **topological order** over the live observer graph (dependents always after dependencies). The graph is `signal.observers` (eagerly maintained via the unified subscription model — see [`unified-subscription-design.md`](unified-subscription-design.md)).
2. Filters out observers that are *descendants* of other observers in this batch (a descendant will be naturally re-resumed by its ancestor's completion event, so dispatching it directly here would cause duplicate work).
3. Escalates each remaining observer to its root await-ancestor (`find-root-await-ancestor`) — the spin that actually needs to resume in this batch. Suspended descendants on `await` chains anchor at the right level.
4. Creates a `Batch` record at `:engine/current-batch` carrying the signal-id, generation counter, and a set of conts already resumed during the batch (to keep parallel dispatch idempotent).
5. Resumes each observer's `track` continuation with the fresh signal value. Observers with `>1` entry are dispatched in parallel on the ForkJoinPool (JVM), using `CountDownLatch` + `managedBlock` to wait for all of them.

### Cascade events

While observer bodies execute, they may produce more events: `:spin-completion` when a body resolves, `:signal-change` if the body itself swaps a signal, etc. These all flow through the **single** `:engine/pending` queue and are drained naturally by the outer drain loop after the current event finishes. There is no separate "Phase 2" queue and no blocking wait — the redesign collapsed those into the unified FIFO. See [`unified-subscription-design.md`](unified-subscription-design.md) for the full rationale (the two-stage commit model previously here was the source of the "Phase 2 deadlock on Deferred suspension" bug, now fixed).

The descendant-filtering + ancestor-escalation step preserves the no-glitch guarantee without a per-batch barrier: within one `:signal-change` dispatch all directly-affected observers resume against the fresh signal value, and downstream completions propagate via the same drain in FIFO order — no spin ever sees a partially-updated graph.

## Dependency Tracking and the Graph

Spindel tracks dependencies automatically at runtime. During spin execution:

- `(track signal)` calls `track-signal-dep!` → records `signal-id` in `[:spin-tracking spin-id :signals]`
- `(await child-spin)` calls `track-spin-dep!` → records `child-id` in `[:spin-tracking spin-id :spins]`

When a spin completes, `record-deps!` commits these tracking entries into the permanent graph atomically: it updates the `SpinNode`'s dependency set and registers the spin as an observer on each dependency's node. Observer sets are used both for dirty propagation and for topological ordering during signal-change processing.

The topological order is computed fresh on each signal change from the live graph — not cached — so it always reflects the current dependency structure.

## Spin Execution Flow

When you deref a spin:

```
1. Is the spin cached and clean?
   └─ yes → return cached result immediately (no work enqueued)
   └─ no  → enqueue :spin-execution event, block calling thread

2. drain-events! picks up :spin-execution
   └─ try-claim-execution!: atomically check if already running or cached
      └─ already cached (clean) → deliver result via callback
      └─ already running → add callbacks to pending-callbacks list
      └─ not running, not cached → claim (set :running?=true), execute spin body

3. Spin body runs on executor (worker thread or virtual thread)
   └─ effects (await/track) may suspend body → return ::incomplete
   └─ body completes → cache-result! + enqueue :spin-completion

4. :spin-completion enqueued
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
3. Polls `drain-active` down to 0 (100µs intervals) — waits for all in-flight `drain-events!` calls to exit their outermost finally block
4. `.join(drain-thread 200ms)` — waits for the daemon thread loop to actually terminate

After step 3, the entry guard guarantees no new drain will ever enter active processing for this context. After step 4, the thread is fully exited.

`close-context!` calls `stop-context!` and additionally shuts down the executor.

### GC-based cleanup

If a context is abandoned without calling `stop-context!` (common in tests), Java's `Cleaner` automatically stops the drain thread when the context object is collected. The Cleaner registration uses phantom references, so it fires once the context has no more strong references — calling `(reset! running false)` and waking the drain thread.

This is a safety net, not a substitute for explicit cleanup. Use `stop-context!` in your lifecycle code.

## Fork Scheduling

Forked contexts share the root's `executor` and `running` atom. They do not own a drain thread. When a fork enqueues an event, `trigger-drain!` submits a `drain-events!` task to the executor directly.

The fork's event queue and draining lock (`engine/pending`, `:engine/draining?`) are **fork-local** — they live in the fork's overlay backend and are isolated from the parent. A fork draining does not conflict with the parent draining.

```clojure
(def root (create-execution-context))
(def fork (fork-context root))

(binding [ec/*execution-context* fork]
  (swap! my-signal 42))   ; enqueues to fork's :engine/pending
                           ; triggers drain-events! on shared executor
                           ; drain lock is fork-local, never contends with root
```

## Platform Differences (JVM vs ClojureScript)

| Aspect | JVM | ClojureScript |
|--------|-----|---------------|
| Drain thread | Daemon thread, blocks on `LinkedBlockingQueue` | No drain thread; JS event loop |
| Executor | ForkJoinPool / virtual threads | `setTimeout 0` |
| Parallel observers | `CountDownLatch` + `managedBlock` | Always sequential (single-threaded) |
| `await-drain-complete!` | Blocks with `ForkJoinPool.managedBlock` + 100µs `parkNanos` | Returns current idle state, non-blocking |
| `@spin` deref | Blocks until complete | Not supported; use `run-spin!` callbacks |
