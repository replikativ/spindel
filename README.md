# Spindel

[![Clojars Project](https://img.shields.io/clojars/v/org.replikativ/spindel.svg)](https://clojars.org/org.replikativ/spindel)
[![CircleCI](https://circleci.com/gh/replikativ/spindel.svg?style=shield)](https://circleci.com/gh/replikativ/spindel)
[![Slack](https://img.shields.io/badge/slack-join_chat-brightgreen.svg)](https://clojurians.slack.com/archives/CB7GJAN0L)

**Reactive computation you can fork.**

Spindel is a reactive programming system for Clojure / ClojureScript in
which the *execution context* — every signal, every cached spin
result, every continuation — is a first-class value. Fork it in O(1),
let two branches diverge, then commit or discard. The same shape that
makes Datahike databases branchable, applied to running reactive
state.

```clojure
(require '[org.replikativ.spindel.core                :as s
                                                      :refer [spin signal track]]
         '[org.replikativ.spindel.incremental.interval :as iv]
         ;; For REPL determinism only — production reactive flows go
         ;; through render-spin! / spawn! and don't need this.
         '[org.replikativ.spindel.engine.impl.simple   :as engine])

(def root (s/create-execution-context))

;; A signal and a spin that tracks it.
(s/with-context root
  (def counter (signal 0))
  (def doubled (spin (* 2 (iv/get-new (track counter))))))

(s/with-context root
  @doubled                          ; => 0  (initial run)
  (swap! counter inc)
  ;; Signal changes drain asynchronously on a background thread.
  ;; `await-drain-complete!` blocks until the engine is idle so
  ;; the next read is deterministic.
  (engine/await-drain-complete! root)
  @doubled)                         ; => 2

;; Fork the whole reactive system. Mutations in the fork don't
;; reach the parent; reads fall through to parent's unchanged state.
(def fork (s/fork-context root))

(s/with-context fork
  (swap! counter inc)
  (engine/await-drain-complete! fork)
  @doubled)                         ; => 4   (fork sees its own counter)

(s/with-context root
  @doubled)                         ; => 2   (parent unchanged)
```

Most of the API surface ships through the convenience namespace
`org.replikativ.spindel.core` (aliased `s` above) — `spin`, `signal`,
`track`, `await`, the combinators (`parallel`, `race`, `timeout`, …),
fork-context, atoms, pub/sub. Two things require their own require:
`iv/get-new` (typed-interval accessor in `incremental.interval`)
and `await-drain-complete!` (the REPL barrier in `engine.impl.simple`
— production code rarely needs it).

## Why Spindel

1. **Fork the running reactive system, not just the code.**
   Execution contexts are values. Snapshot one, restore it later,
   serialize it across a network, or fork it for speculative
   computation — the engine guarantees O(1) forking via overlay
   backends with copy-on-write semantics. Forks share unmodified
   state structurally; mutations isolate. Compare to most FRP /
   signal libraries where the reactive graph is global mutable
   state.

2. **CPS + effects as the extension axis.**
   The `spin` macro is a partial-CPS transform with `track`, `await`,
   and `yield` registered as plug-in effects. Libraries register
   their own — `sample` / `observe` for probabilistic programming,
   custom suspension points for distributed RPC, IO bindings for
   web frameworks — and the new effects participate in spin
   expansion as first-class citizens. No core changes required.

3. **Typed delta algebra end-to-end.**
   Reactive combinators (`imap`, `ifilter`, `islice`, `ifor-each`,
   `ireduce`) emit algebra records carrying their composition laws
   inline (sequence / map / scalar). The DOM discharge consumes the
   typed shape directly — a 10 000-item virtual list only touches
   the items entering or exiting the visible window per scroll, the
   same shape end-to-end from the signal mutation through the DOM
   patch.

## Use Cases

- **Branching document editor** — [examples/versioned-editor](examples/src/examples/versioned_editor_demo.cljs)
  forks the entire document state per author, lets them iterate
  independently, then merges accepted changes back. Time-travel
  preview by clicking any DAG row. Real-world prototype for
  AI-coded document inference (see [simmis](https://github.com/simm-is)).
- **Virtual scroll over 10 000 items** —
  [examples/infinite-scroll](examples/src/examples/infinite_scroll_demo.cljs)
  with `islice` keeps a window over a long source; each scroll
  emits a single typed `:seq-diff` carrying the items entering and
  exiting, and the DOM discharge applies only that delta.
- **TODO MVC + block editor** — [examples/todo](examples/src/examples/todo_demo.cljs),
  [examples/block-editor](examples/src/examples/block_editor_demo.cljs)
  show the deltaable-collection pipeline end-to-end and the
  `ifor-each` macro for keyed lists.
- **Foreign-node integration** — [examples/tiptap](examples/src/examples/tiptap_demo.cljs)
  embeds a TipTap (ProseMirror) editor as a foreign subtree;
  Spindel manages the surrounding vnode tree, TipTap owns its
  subtree, and a signal feeds the live content back through Spindel.
- **Probabilistic programming**
  ([src/.../inference](src/org/replikativ/spindel/inference)) —
  `sample` / `observe` / `constrain` are registered as Spindel
  effects so inference programs are spins, MCMC kernels are forks,
  and trace addresses are deterministic by source-loc.
- **Distributed scopes** — [`defn-spin-remote`](src/org/replikativ/spindel/distributed/macros.cljc)
  lets you define a function that executes on a remote peer with
  explicit boundary-crossing arguments; pairs with
  [`distributed-scope`](https://github.com/simm-is/distributed-scope)
  for kabel-WebSocket transport.

## Status

Beta. JVM: **772 tests / 2606 assertions** passing; CLJS:
**363 tests / 1374 assertions** passing. Public API may evolve before
1.0; we'll call out breaking changes in CHANGELOG.

## Install

```clojure
;; deps.edn
{:deps {org.clojure/clojure {:mvn/version "1.12.0"}
        org.replikativ/spindel {:mvn/version "0.1.0"}}}
```

ClojureScript builds need `org.clojure/clojurescript` and
[shadow-cljs](https://github.com/thheller/shadow-cljs) (or
equivalent) — see [examples/shadow-cljs.edn](examples/shadow-cljs.edn)
for a working config.

## Documentation

| Guide | What it covers |
|-------|----------------|
| [Getting Started](docs/getting-started.md) | First-spin tutorial, signals, effects, running tests. |
| [Concepts](docs/concepts.md) | Mental model: spins, signals, runtime, glitch-free FRP. |
| [API Reference](docs/api-reference.md) | Namespace-by-namespace listing of every public function and macro. |
| [Effects](docs/effects.md) | `await`, `track`, `yield`, deferred and mailbox synchronization. |
| [Custom Effects](docs/custom-effects.md) | Register your own effects with `register-effect-by-symbol!`. |
| [Combinators](docs/combinators.md) | `parallel`, `race`, `sleep`, `timeout`, `debounce`, `throttle`, `accumulate`. |
| [Incremental](docs/incremental.md) | Deltaable collections, typed delta algebra, `Interval` 3-state contract. |
| [Atoms](docs/atoms.md) | Fork-safe runtime-backed atoms. |
| [Forking](docs/forking.md) | `snapshot-context`, `restore-snapshot`, `fork-context`, serialization. |
| [Scheduling](docs/scheduling.md) | Event queue, drain loop, executors, platform differences (JVM vs CLJS). |
| [Engine](docs/engine.md) | State shape, deterministic addressing, CPS / trampoline mechanics, overlay backend, memory invariants. The implementation deep-dive. |
| [Pub/Sub](docs/pubsub.md) | `mult`, `pub`, buffers, async-sequence-based fan-out. |
| [Distributed](docs/distributed.md) | `defn-spin-remote`, `spin-remote`, spin↔channel bridge, distributed-scope integration. |
| [SCI Integration](docs/sci-integration.md) | Sandboxed spin execution via the Small Clojure Interpreter. |

For contributor patterns and AI-assistant guidance (do's/don'ts when
modifying the engine, project-specific conventions), see
[CLAUDE.md](CLAUDE.md).

## Ecosystem

Spindel is part of [replikativ](https://github.com/replikativ), a set
of composable building blocks for branchable, immutable systems:

- **[datahike](https://github.com/replikativ/datahike)** — durable
  Datalog database with git-like branching. Pair with Spindel for
  reactive queries over branchable data.
- **[kabel](https://github.com/replikativ/kabel)** — WebSocket
  middleware for real-time transport.
- **[distributed-scope](https://github.com/simm-is/distributed-scope)**
  — peer-to-peer RPC over kabel; what `defn-spin-remote` builds on.
- **[hasch](https://github.com/replikativ/hasch)** — content-
  addressed hashing for stable structural identity, used internally
  by Spindel's deterministic addressing.
- **[yggdrasil](https://github.com/replikativ/yggdrasil)** —
  branchable memory model protocols spanning Git, ZFS, Datahike, and
  more. Spindel's `fork-context` shares the spirit; yggdrasil
  generalizes it to a cross-system protocol.
- **[partial-cps](https://github.com/simm-is/partial-cps)** — the
  CPS transformation engine that powers the `spin` macro.

## A 60-Second Mental Model

Three primitives that compose:

- A **signal** is a mutable, reactive source of values.
- A **spin** is a cached computation that runs `track` (to subscribe
  to a signal) or `await` (to subscribe to another spin's result).
  When a tracked dependency changes, the spin re-runs.
- An **execution context** holds every signal, every spin result,
  every continuation. It's a regular value: you can `fork-context`
  it (overlay-backed, O(1) copy-on-write), `snapshot-context` it
  (an immutable copy for checkpointing), or `serialize-context` /
  `deserialize-context` round-trip it over the wire.

A spin is *not* an asynchronous task — it's a *cached function* whose
re-execution is triggered by signal changes. Forking the context
gives you a private copy of all the cached results; the parent never
sees your fork's mutations.

For the full mental model, see [docs/concepts.md](docs/concepts.md).

## Running Tests

```bash
# JVM
clj -M:test

# ClojureScript (Node) — uses root shadow-cljs.edn :test target
npx shadow-cljs compile test     # or `watch test` for re-run on save
```

CLJS tests run via shadow-cljs's `:node-test` target (jsdom-backed
DOM tests included). See [docs/scheduling.md](docs/scheduling.md)
for the JVM / CLJS executor differences and the platform-specific
testing patterns.

## Critical Rules (or: the two things every new user trips over)

1. **Inside a spin body, use `(await x)` / `(track x)` — never
   `@x`.** The `spin` macro CPS-transforms `await` and `track` into
   continuation breakpoints; raw `@` deref blocks the thread,
   breaks the continuation chain, and silently produces wrong
   results. Outside spin bodies (REPL, tests), `@` is fine.

2. **Effects don't survive into closures.** `(spin (map #(await
   (fetch %)) items))` doesn't work — the macro only transforms its
   *lexical* body, and the function passed to `map` is opaque.
   Use `loop`/`recur` for sequential work, or nest `(spin …)` per
   item and use `(apply parallel child-spins)` for concurrent work.
   See [CLAUDE.md "CPS Transformation Limitations"](CLAUDE.md) for
   the long version.

## License

Copyright © 2024–2026 Christian Weilbach.

Licensed under the Apache License 2.0 (see [LICENSE](LICENSE)).
