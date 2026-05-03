# Concepts

This guide explains how spindel's pieces fit together. Read this to build a mental model before diving into specific APIs.

## The Three Primitives

### Spin — Computation

A spin is a **cached reactive computation**. It runs a function body, caches the result, and automatically re-executes when dependencies change.

```clojure
(def doubled
  (spin
    (let [{:keys [new]} (track counter)]
      (* 2 new))))
```

Key properties:
- **Cached** — results stored in the runtime, returned on subsequent deref without re-execution
- **Reactive** — automatically re-executes when tracked signals or awaited spins change
- **Lazy** — re-execution only happens when the result is needed (deref)
- **Stateless** — spins don't hold internal state; all state lives in the execution context

### Signal — State

A signal is a **mutable reactive value**. It's like an atom that notifies dependent spins when it changes.

```clojure
(def counter (signal 0))

(swap! counter inc)  ;; All spins tracking `counter` are marked dirty
```

Key properties:
- **Atom-compatible** — supports `@`, `swap!`, `reset!`
- **Delta-tracking** — collections wrapped as deltaable automatically, providing structural change deltas
- **Fork-safe** — state stored in the execution context, isolated on fork

### Effect — Interaction

Effects are the mechanism through which spins interact with signals and other spins. There are three built-in effects:

| Effect | Purpose | Inside spin |
|--------|---------|-------------|
| `await` | Depend on another spin's result | `(await child-spin)` |
| `track` | Observe a signal reactively | `(track my-signal)` |
| `yield` | Emit a value in an async sequence | `(yield value)` |

Effects are **CPS breakpoints** — the `spin` macro transforms them into continuation-passing style so execution can suspend and resume.

## Execution Context

The execution context is the runtime environment that manages all state, dependency tracking, and scheduling. Every spindel operation requires a bound context:

```clojure
(def ctx (create-execution-context))

(binding [ec/*execution-context* ctx]
  ;; All spindel operations here
  )
```

### Why Dynamic Binding?

The context is bound dynamically (not captured) because:

1. **Fork-safety** — A forked context needs spins to use the fork's state, not the original's. Dynamic binding resolves at call-time.
2. **Concurrent spins** — Multiple spins in the same context execute on different threads, each needing the same context bound.
3. **Lightweight** — No need to pass context through every function call.

### What's Inside

The execution context contains:
- **Signal state** — current values, deltas, old snapshots
- **Spin cache** — cached results, dirty flags, running status
- **Dependency graph** — which spins depend on which signals/spins
- **Continuations** — suspended CPS continuations waiting to resume
- **Scheduling** — executor for spin execution, event queue for the engine
- **Batch state** — current batch for glitch-free propagation

## Dependency Graph

Spindel automatically builds a dependency graph as spins execute:

```clojure
(def a (signal 1))
(def b (signal 2))

(def sum  (spin (+ (:new (track a)) (:new (track b)))))
(def prod (spin (* (await sum) 10)))
```

This creates:

```
Signal a ──┐
           ├──→ Spin sum ──→ Spin prod
Signal b ──┘
```

### How Tracking Works

1. **Spin starts executing** — the runtime knows which spin is active via `*spin-id*`
2. **`track` called** — registers signal as dependency of current spin
3. **`await` called** — registers child spin as dependency of current spin
4. **Spin completes** — dependencies committed to the graph
5. **Signal changes** — runtime walks the graph to mark dependent spins dirty

Dependencies are **re-tracked on every execution**. If a spin conditionally tracks different signals, the graph updates accordingly.

## Glitch-Free Propagation

When a signal changes, spindel ensures **consistent** updates using topological ordering and batching.

### The Glitch Problem

Without protection, diamond dependencies cause glitches:

```
Signal x ──→ Spin A ──┐
    │                 ├──→ Spin C (sees inconsistent A and B)
    └────→ Spin B ──┘
```

If C observes A's new value but B's old value, it computes with inconsistent inputs.

### Spindel's Solution

1. **Topological sort** — the dependency graph produces a level ordering. Spins at the same level form an antichain (no dependencies between them).
2. **Batch processing** — signal changes are collected during Phase 1 (resuming track continuations). Completion events are deferred to Phase 2.
3. **Level-parallel execution** — within a level, independent spins can execute concurrently. Spins at deeper levels wait for shallower levels to complete.

```
Level 0: Signal x changes
Level 1: Spins A, B execute (parallel, no dependency between them)
Level 2: Spin C executes (sees consistent A and B)
```

### Batching Multiple Signals

Use `batch` to group signal changes into a single propagation:

```clojure
(batch
  (swap! signal-a inc)
  (swap! signal-b inc))
;; One propagation pass, not two
```

## CPS Transformation

The `spin` macro transforms its body using **partial CPS** (continuation-passing style). This is what enables non-blocking suspension at `await` and `track` calls.

### What the Macro Does

```clojure
;; You write:
(spin
  (let [x (await child)]
    (* x 2)))

;; The macro produces (conceptually):
(make-spin
  (fn [resolve reject]
    (await-handler child spin-id loc
      (fn [x]           ;; resolve continuation
        (resolve (* x 2)))
      reject)))
```

The CPS transformation:
1. Identifies **breakpoints** — calls to registered effects (`await`, `track`, `yield`)
2. Splits the body at each breakpoint into **continuations**
3. Wraps continuations as callbacks passed to effect handlers
4. Handles `try`/`catch`, `loop`/`recur`, `let`, `if`, `do`, `binding` across breakpoints

### Why Not Blocking?

If `await` blocked the thread (like `@`), you'd need one thread per suspended spin. With CPS:
- Suspension is **free** — just store the continuation
- Resumption runs on the executor's thread pool
- Thousands of concurrent spins with a small thread pool

## Caching

Every spin result is cached by address. The address is deterministic — generated from a hash chain based on source location.

### Address-Based Identity

```clojure
(spin ...)  ;; Address: hash(parent-address, source-location)
```

The deterministic addressing means:
- Same code path produces the same spin address
- Forked contexts replay the same address sequence
- Sequential spins at the same location get different addresses (hash chain advances)

### Invalidation

A spin's cache is invalidated (marked dirty) when:
- A tracked signal changes
- An awaited child spin's result changes

On next deref, the spin re-executes and caches the new result.

### Lazy Re-execution

Spins don't re-execute eagerly when marked dirty. They wait until their result is needed:

```clojure
(swap! counter inc)  ;; `doubled` marked dirty, but NOT re-executed
@doubled             ;; NOW it re-executes
```

This avoids unnecessary work when intermediate computations are dirty but never read.

## Next Steps

- [Getting Started](getting-started.md) — Hands-on tutorial
- [Effects](effects.md) — How `await`, `track`, and `yield` work in detail
- [Forking](forking.md) — Copy-on-write execution contexts
- [Scheduling](scheduling.md) — Event queue, drain loop, glitch-free propagation, and executors
