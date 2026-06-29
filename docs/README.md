# Spindel Documentation

This index organizes the documentation by topic. New to Spindel? Start
with **Getting Started**, then **Concepts**.

## Getting Started

- **[Main README](../README.md)** — project overview, install, quick start
- **[Getting Started](getting-started.md)** — first-spin tutorial: setup, signals, effects, running tests

## Core Concepts

- **[Concepts](concepts.md)** — the mental model: spins, signals, checkpoints, effects, the drain queue, caching, glitch-free propagation. Read this before the guides.
- **[Effects](effects.md)** — `await`, `track`, `yield`, deferred and mailbox synchronization
- **[Incremental](incremental.md)** — deltaable collections, typed delta algebra, the `Interval` three-state contract

## Guides

- **[Combinators](combinators.md)** — `parallel`, `race`, `sleep`, `timeout`, `debounce`, `throttle`, `accumulate`
- **[Custom Effects](custom-effects.md)** — register your own effects so they participate in spin macro expansion
- **[Atoms](atoms.md)** — fork-safe, runtime-backed atoms
- **[Forking](forking.md)** — O(1) copy-on-write contexts: `fork-context`, `snapshot-context`, `restore-snapshot`, serialization
- **[Pub/Sub](pubsub.md)** — `mult`, `pub`, buffers, async-sequence fan-out
- **[Distributed](distributed.md)** — `defn-spin-remote`, `spin-remote`, the spin↔channel bridge, distributed-scope integration; convergent signal sync; workspace reflection + cross-system forking (`wire-topology!`, `fork-remote!`/`merge-fork-remote!`)
- **[SCI Integration](sci-integration.md)** — sandboxed spin execution via the Small Clojure Interpreter

## Internals & Reference

- **[Engine](engine.md)** — the implementation deep-dive: state shape, deterministic addressing, CPS / trampoline, executors and the drain loop, glitch-free propagation, the overlay backend, memory invariants and GC
- **[Engine Formalism](engine-formalism.md)** — algebraic properties (`track` as comonad, `await` as monad, the delta algebra laws), flow-chart diagrams, and a correctness argument per reactive composition
- **[API Reference](api-reference.md)** — namespace-by-namespace listing of every public function and macro
