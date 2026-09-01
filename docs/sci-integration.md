# SCI Integration

Spindel integrates with [SCI](https://github.com/babashka/sci) (Small Clojure Interpreter) for sandboxed execution of spindel code. This enables agent isolation, security sandboxing, and dynamic code evaluation while maintaining full access to spindel's reactive primitives.

SCI support is optional and is therefore not included in Spindel's published
POM. Applications using this integration must add the replikativ compatibility
distribution, which provides the forkable interpreter-world APIs:

```clojure
{:deps {org.replikativ/spindel {:mvn/version "<version>"}
        org.replikativ/sci {:mvn/version "0.15.59-replikativ.1"}}}
```

Do not put `org.replikativ/sci` and `org.babashka/sci` on the same classpath:
they provide the same `sci.*` namespaces, while only the replikativ coordinate
currently contains the forkable runtime required by this integration. Once
those changes are released upstream, this guide will return to the upstream
coordinate.

## Overview

SCI provides a safe subset of Clojure that runs in an interpreter. Spindel's SCI integration bridges the gap between native and interpreted contexts using a **BoundaryTask** wrapper pattern that propagates runtime bindings across the boundary.

Two APIs are provided:

| API | Namespace | Use case |
|-----|-----------|----------|
| **Functional** | `spindel.sci.boundary` | `make-spin` with CPS functions — simpler, lower overhead |
| **Macro** | `spindel.sci.macro` | Full `spin` macro with `await`/`track` — full language support |

For a forkable application world, `org.replikativ.spindel.sci.world` is the
canonical composition layer. It registers the interpreter as a world component
and returns a stable reference instead of making callers carry a parallel
`{:runtime ... :sci-ctx ...}` pair.

```clojure
(require '[org.replikativ.spindel.sci.world :as sci-world])

(def interpreter (sci-world/create! rt))

(binding [ec/*execution-context* rt]
  (sci-world/eval-string*
   interpreter
   "(def memory (atom []))"))

(def child (ctx/fork-context rt :mode :frozen))

;; The same reference now selects the child's forked SCI heap.
(binding [ec/*execution-context* child]
  (sci-world/eval-string* interpreter
                          "(swap! memory conj :child)"))
```

Suspended `spin` continuations carry an SCI continuation-context token. When
resumed in a descendant Spindel context, the token is retargeted to the paired
SCI component, so dynamic bindings and interpreter state continue in that
world. Parent and child may then resume the copied computation independently.
The macro/world APIs enable SCI's opt-in `:forkable` runtime mode themselves;
callers cannot accidentally construct a standard SCI runtime that lacks the
managed continuation world.

## Setup

### Functional API (Recommended for Simple Cases)

```clojure
(require '[org.replikativ.spindel.engine.context :as ctx]
         '[org.replikativ.spindel.engine.core :as ec]
         '[org.replikativ.spindel.sci.boundary :as boundary])
(require '[sci.core :as sci])

;; Create execution context
(def rt (ctx/create-execution-context))

;; Create SCI context with spindel support
(def sci-ctx
  (boundary/create-spindel-sci-context
    {:runtime rt}))

;; Evaluate spindel code in SCI
(binding [ec/*execution-context* rt]
  @(sci/eval-string* sci-ctx
     "(require '[spindel.spin :as spin])
      (spin/make-spin
        (fn [resolve reject]
          (resolve 42))
        :my-spin)"))
;; => 42
```

### Macro API (Full Language Support)

```clojure
(require '[org.replikativ.spindel.sci.macro :as macro])

;; Create SCI context with full spin macro support
(def sci-ctx
  (macro/create-spin-macro-context
    {:runtime rt}))

;; Use spin macro, await, track — everything works
(binding [ec/*execution-context* rt]
  @(sci/eval-string* sci-ctx
     "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
               '[org.replikativ.spindel.effects.await :refer [await]])
      (spin (+ 1 2))"))
;; => 3
```

## Creating Spins in SCI

### Functional API: `make-spin`

The functional API uses CPS (continuation-passing style) functions directly:

```clojure
;; In SCI context:
(sci/eval-string* sci-ctx
  "(require '[spindel.spin :as spin])

   ;; Synchronous spin
   (spin/make-spin
     (fn [resolve reject]
       (resolve (* 6 7)))
     :answer)")
```

The CPS function receives `resolve` and `reject` callbacks:
- Call `(resolve value)` to complete successfully
- Call `(reject error)` to complete with an error
- Return without calling either to indicate the spin is pending (async)

### Macro API: `spin` Macro

The macro API provides the full `spin` syntax with CPS transformation:

```clojure
(sci/eval-string* sci-ctx
  "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
            '[org.replikativ.spindel.effects.await :refer [await]])

   ;; Spin with await
   (spin
     (let [a (await child-spin-a)
           b (await child-spin-b)]
       (+ a b)))")
```

## Exposing Native Spins to SCI

Pass native spins via the `:native-spins` option. They are installed as ambient
capabilities: invoking one uses the caller's currently selected Spindel world,
so an inherited capability cannot mutate the parent by retaining its creation
runtime.

```clojure
(require '[org.replikativ.spindel.spin.cps :refer [spin]])

;; Create native spins
(binding [ec/*execution-context* rt]
  (def fetch-data (spin {:status :ok :data [1 2 3]}))
  (def process   (spin (+ 10 20))))

;; Expose to SCI
(def sci-ctx
  (macro/create-spin-macro-context
    {:runtime rt
     :native-spins {'fetch-data fetch-data
                    'process    process}}))

;; SCI code can await them
(binding [ec/*execution-context* rt]
  @(sci/eval-string* sci-ctx
     "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
               '[org.replikativ.spindel.effects.await :refer [await]])
      (spin
        (let [data (await fetch-data)]
          (:data data)))"))
;; => [1 2 3]
```

### Manual Wrapping

Use `wrap-spin-for-sci` only for an explicit cross-world task handle:

```clojure
(def wrapped (boundary/wrap-spin-for-sci my-native-spin rt))
;; wrapped implements IFn and IDeref
;; The task executes in rt; callbacks re-enter their caller's world.
```

## Bidirectional Interop

### Native to SCI

Native code can directly invoke SCI-created spins because SCI functions implement `IFn`:

```clojure
;; Create spin in SCI
(def sci-spin
  (binding [ec/*execution-context* rt]
    (sci/eval-string* sci-ctx
      "(require '[org.replikativ.spindel.spin.cps :refer [spin]])
       (spin (* 7 6))")))

;; Await from native code
(binding [ec/*execution-context* rt]
  @(spin (await sci-spin)))
;; => 42
```

### SCI to Native

Inherited capabilities follow the ambient world. Explicit task handles retain
their host world and restore the caller when they complete:

```
:native-spins → AmbientBoundaryTask → caller's selected world

explicit task → wrap-spin-for-sci → task's host world
                                    ↓ completion
                                caller's world
```

## Agent Isolation Pattern

For agent systems, create the interpreter as a component before forking:

```clojure
(require '[org.replikativ.spindel.engine.context :as ctx])

(def interpreter
  (sci-world/create! rt {:native-spins {'tool-1 tool-spin-1}}))

;; Create isolated agents
(def agent-a (ctx/fork-context rt :mode :frozen))
(def agent-b (ctx/fork-context rt :mode :frozen))

;; `interpreter` selects a distinct heap in rt, agent-a, and agent-b.
```

Create different roots when agents need different capability sets. Within one
root, `:forkable-components` can remove entire components from a child; SCI's
own namespace and class allowlists govern what code can do inside an inherited
interpreter.

### Isolation Guarantees

| Concern | Mechanism |
|---------|-----------|
| State isolation | `fork-context` — COW overlay per agent |
| Code sandboxing | SCI — only exposed functions available |
| API surface control | `:native-spins` — explicit allowlist |
| Binding propagation | `BoundaryTask` — automatic context threading |

## Runtime State Access

By default, SCI contexts cannot access runtime state directly. Enable with the `:expose-runtime-state?` option:

```clojure
(def sci-ctx
  (boundary/create-spindel-sci-context
    {:runtime rt
     :expose-runtime-state? true}))

;; SCI code can now access:
;; (require '[spindel.engine :as engine])
;; (engine/get-state [:signals sig-id])
;; (engine/swap-state! [:my-data] update-fn)
```

Only enable this when SCI code needs to inspect or modify runtime internals (e.g., debugging, admin tools).

## CPS in SCI

The macro API loads partial-cps into the SCI context automatically via `load-partial-cps!`. This enables:

- `spin` macro with full CPS transformation
- `await` effect for spin-to-spin dependencies
- `track` effect for signal observation (when `:expose-track?` is true, default)
- `loop`/`recur` with `await` inside loop bodies
- `try`/`catch` with proper CPS handling

```clojure
;; All of this works inside SCI:
(sci/eval-string* sci-ctx
  "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
            '[org.replikativ.spindel.effects.await :refer [await]]
            '[org.replikativ.spindel.effects.track :refer [track]])

   (spin
     (try
       (let [result (await some-spin)]
         (if (> result 10)
           (await (process-large result))
           result))
       (catch Exception e
         :fallback)))")
```

### Loading Partial-CPS Manually

If using the functional API and you need CPS support:

```clojure
(require '[org.replikativ.spindel.sci.core :as sci-core])

(def sci-ctx (sci/init {...}))
(sci-core/load-partial-cps! sci-ctx)
;; Now CPS transformation works in this SCI context
```

### Why partial-cps loads with a native runtime

`load-partial-cps!` does not interpret all three partial-cps files
uniformly inside SCI. The split matters:

- **`ioc.clj` and `async.cljc` are interpreted inside SCI.** They
  contain the CPS-transform machinery (the `async` macro and `invert`)
  that has to expand against SCI's symbol environment so user-written
  `spin` bodies inside SCI are transformed correctly.
- **`runtime.cljc` is injected as a native namespace** carrying the
  compiled `bound-fn`, `->thunk`, and `Thunk` defrecord from the host
  JVM's classloader.

The reason is identity. Every trampoline check —
`(instance? is.simm.partial_cps.runtime.Thunk x)` — runs against the
**compiled** `Thunk` class. If `runtime.cljc` were interpreted inside
SCI, `(deftype Thunk [f])` would produce a `sci.impl.deftype.SciType`
that is *not* an instance of the compiled class. The check would
silently always return false, the trampoline would never bounce a
Thunk, and any `recur` after a breakpoint inside a `loop` or
`dotimes` would hang forever. Keeping one canonical compiled `Thunk`
class fixes that.

This is invisible to end-user SCI code, but matters if you are
extending the loader (e.g. adding more native namespaces) or
debugging a "loop with effect hangs in SCI but works natively" bug.

## API Reference

### `spindel.sci.boundary`

#### `create-spindel-sci-context`

```clojure
(create-spindel-sci-context {:keys [runtime expose-runtime-state? native-spins]})
```

Create SCI context with spindel support (functional API).

| Option | Type | Default | Description |
|--------|------|---------|-------------|
| `:runtime` | ExecutionContext | (required) | Execution context |
| `:expose-runtime-state?` | boolean | `false` | Expose `get-state`/`swap-state!` |
| `:native-spins` | map | `{}` | `{symbol → spin}` — auto-wrapped |

#### `wrap-spin-for-sci`

```clojure
(wrap-spin-for-sci task runtime)
```

Wrap a native spin for use in SCI. Returns a `BoundaryTask` implementing `IFn` and `IDeref`.

#### `make-spin-for-sci`

```clojure
(make-spin-for-sci spin-fn spin-id runtime)
```

Create a spin from SCI context with proper bindings. Used internally by the SCI namespace binding for `make-spin`.

### `spindel.sci.macro`

#### `create-spin-macro-context`

```clojure
(create-spin-macro-context {:keys [runtime native-spins expose-track?]})
```

Create SCI context with full spin macro support.

| Option | Type | Default | Description |
|--------|------|---------|-------------|
| `:runtime` | ExecutionContext | (required) | Execution context |
| `:native-spins` | map | `{}` | `{symbol → spin}` — auto-wrapped |
| `:expose-track?` | boolean | `true` | Include `track` effect |

Exposed namespaces:
- `org.replikativ.spindel.spin.cps` — `spin` macro
- `org.replikativ.spindel.effects.await` — `await`, `await-handler`
- `org.replikativ.spindel.effects.track` — `track`, `track-handler` (if enabled)
- `org.replikativ.spindel.spin.core` — `make-spin`
- `org.replikativ.spindel.engine.core` — `*execution-context*`, `*spin-id*`, `with-context`, etc.
- `org.replikativ.spindel.engine.addressing` — `next-address!`
- `is.simm.partial-cps.async` — `invoke-continuation`, `*in-trampoline*`

#### `eval-spin`

```clojure
(eval-spin sci-ctx code-str)
```

Evaluate spin code in SCI context. Returns the Spin object (not dereferenced).

#### `eval-and-deref`

```clojure
(eval-and-deref sci-ctx code-str)
```

Evaluate spin code and immediately deref (blocking). Requires `*execution-context*` bound in calling thread.

### `spindel.sci.core`

#### `load-partial-cps!`

```clojure
(load-partial-cps! sci-ctx)
```

Load partial-cps source files into SCI context. Required for CPS transformation.

#### `common-classes`

```clojure
(common-classes)
```

Returns class allowlist map for SCI contexts (Var, IFn, Spin, Thunk, etc.).

## Limitations

- **Performance overhead**: SCI interpretation adds ~7x overhead vs native Clojure. Boundary crossing itself is negligible (~10ns).
- **Best practice**: Keep hot paths in native code; use SCI for orchestration, configuration, and agent logic.
- **Wrap once**: Create BoundaryTask wrappers once and reuse — don't re-wrap on every call.

## Performance

| Operation | Native | SCI | Overhead |
|-----------|--------|-----|----------|
| Simple arithmetic | ~100ns | ~700ns | ~7x |
| Function call | ~50ns | ~350ns | ~7x |
| `make-spin` creation | ~500ns | ~1us | ~2x |
| Boundary crossing | — | ~10ns | Negligible |

## See Also

- [Getting Started](getting-started.md) — Basic spindel tutorial
- [Effects](effects.md) — `await` and `track` in depth
- [Forking](forking.md) — Copy-on-write context forking
