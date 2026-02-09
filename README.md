# Spindel

**Incremental reactive computation system for Clojure/ClojureScript**

Spindel provides cached reactive spins with automatic dependency tracking, mutable signals with delta tracking, and a fork-safe runtime with copy-on-write memory semantics for deterministic execution.

## Features

- **Copy-on-write forking**: O(1) runtime forking with overlay backends, complete isolation, and serialization support
- **Automatic caching**: Every spin is cached by default, re-executing only when dependencies change
- **Dual perspective signals**: Signals expose both full state (`new`/`old`) and incremental deltas
- **Deltaable collections**: Track structural changes to vectors, maps, and sets
- **Fork-safe state primitives**: Atoms and signals stored in runtime, enabling checkpointing
- **Glitch-free FRP**: Topological ordering ensures consistent updates
- **Async sequences**: Generator-based lazy sequences with `yield`
- **Pub/sub system**: Fan-out (mult) and topic routing (pub) with backpressure
- **Effect system**: Extensible CPS transformation via protocol-based effect handlers
- **Cross-platform**: Portable Clojure/ClojureScript code (.cljc)

## Status

**Core functionality complete** - 634 CLJ / 241 CLJS tests passing. Spins, signals, runtime, effects, forking, sequences, pub/sub all working.

## Quick Start

### Dependencies

```clojure
;; deps.edn
{:deps {org.clojure/clojure {:mvn/version "1.12.0"}
        org.clojure/clojurescript {:mvn/version "1.11.132"}
        org.replikativ/spindel {:mvn/version "0.1.0"}}}
```

### Basic Usage

```clojure
;; Convenience entry point (re-exports core APIs)
(require '[org.replikativ.spindel.core :as s :refer [spin signal await track]])
(require '[org.replikativ.spindel.runtime.core :as rtc])

;; Or require individual namespaces for full control:
;; (require '[org.replikativ.spindel.runtime.context :as ctx])
;; (require '[org.replikativ.spindel.spin.cps :refer [spin]])
;; (require '[org.replikativ.spindel.signal :as sig])
;; (require '[org.replikativ.spindel.effects.await :refer [await]])
;; (require '[org.replikativ.spindel.effects.track :refer [track]])

;; Create execution context
(def context (s/create-execution-context))

;; Create a signal
(binding [rtc/*execution-context* context]
  (def counter (signal 0)))

;; Create a spin that depends on the signal
(binding [rtc/*execution-context* context]
  (def doubled
    (spin
      (let [{:keys [new]} (track counter)]
        (* 2 new)))))

;; Execute spin
(binding [rtc/*execution-context* context]
  @doubled)  ; => 0

;; Update signal - spin automatically re-executes
(binding [rtc/*execution-context* context]
  (swap! counter inc)
  @doubled)  ; => 2
```

## Core Concepts

### Spins

Spins are cached reactive computations that automatically track dependencies:

```clojure
(def my-spin
  (spin
    (let [a (await spin-a)
          b (await spin-b)]
      (+ a b))))
```

**Key point**: Use `await` inside spins, never `@` (deref blocks the thread and breaks CPS).

### Signals

Signals are mutable time-varying values with delta tracking:

```clojure
(def todos (sig/signal []))
(swap! todos conj {:text "Buy milk" :done false})

;; Inside a spin - dual perspective access
(spin
  (let [{:keys [new old deltas]} (track todos)]
    ;; new: current value
    ;; old: previous value
    ;; deltas: structural changes [{:delta :add :path [0] :value {...}}]
    (process-changes deltas)))
```

### Runtime

The runtime manages execution, dependency tracking, and scheduling:

```clojure
;; Create execution context (portable CLJ/CLJS)
(require '[org.replikativ.spindel.runtime.context :as ctx])
(def context (ctx/create-execution-context))

;; Use runtime via binding
(binding [rtc/*execution-context* context]
  ;; All operations here
  )
```

## Copy-on-Write Runtime Forking

Spindel's runtime supports **O(1) forking** with copy-on-write semantics, enabling:

- **Isolated execution branches**: Forks can evolve independently without interference
- **Speculative computation**: Try different paths, discard failures
- **Checkpointing**: Snapshot state, restore later
- **Parallel inference**: Run multiple computations sharing common state

### How Forking Works

```clojure
(require '[org.replikativ.spindel.runtime.context :as ctx])
(require '[org.replikativ.spindel.signal :as sig])

;; Create main context with a signal
(def ctx-main (ctx/create-execution-context))
(binding [rtc/*execution-context* ctx-main]
  (def counter (sig/signal 0))
  (swap! counter inc))  ; counter = 1

;; Snapshot the context (immutable copy)
(def snapshot (ctx/snapshot-context ctx-main))

;; Restore snapshot to create a fork
(def ctx-fork (ctx/restore-snapshot snapshot))

;; Mutations in fork don't affect parent
(binding [rtc/*execution-context* ctx-fork]
  (swap! counter inc)   ; fork: counter = 2
  (swap! counter inc))  ; fork: counter = 3

;; Parent unchanged
(binding [rtc/*execution-context* ctx-main]
  @counter)  ; => 1 (still 1!)
```

### Overlay Backends

Forked contexts use an **overlay backend** that:

1. **Shares parent state** via structural sharing (memory efficient)
2. **Stores mutations locally** in the overlay (copy-on-write)
3. **Falls back to parent** for reads of unmodified state

```clojure
;; Lightweight fork (O(1) - just creates overlay)
(def ctx-fork (ctx/fork-context ctx-main))

;; Fork inherits all parent state
;; Mutations stored in overlay, parent untouched
```

### Serialization

Contexts can be fully serialized for checkpointing or distribution:

```clojure
;; Serialize to EDN
(def serialized (ctx/serialize-context ctx-main))

;; Deserialize back to live context
(def ctx-restored (ctx/deserialize-context serialized))
```

### Isolation Guarantees

| Operation | Parent sees? | Fork sees? |
|-----------|--------------|------------|
| Fork reads parent state | N/A | Yes (via fallback) |
| Fork mutates state | No | Yes (in overlay) |
| Parent mutates state | Yes | No (isolated) |
| Fork creates new state | No | Yes (in overlay) |

## State Primitives

### Signals

Signals are the primary reactive state primitive:

```clojure
(require '[org.replikativ.spindel.signal :as sig])

;; Create signal with initial value
(def todos (sig/signal []))

;; Standard atom operations
(swap! todos conj {:text "Buy milk"})
(reset! todos [])
@todos  ; => []

;; Signals auto-wrap values as deltaable (for collections)
;; This enables automatic delta tracking
```

### Fork-Safe Atoms

For non-reactive state that still needs fork isolation:

```clojure
(require '[org.replikativ.spindel.atom :as atom])

;; Create runtime-stored atom
(def cache (atom/atom {}))

;; Standard atom API
(swap! cache assoc :key "value")
@cache  ; => {:key "value"}

;; Atoms are:
;; - Stored in runtime at [:atoms atom-id]
;; - Fork-safe (mutations isolated to fork)
;; - Auto-cleaned when GC'd (JVM only)
```

**Important**: Atoms don't capture runtime - they use `*execution-context*` dynamically.

## Incremental Collections (Deltaables)

Deltaable collections track **top-level structural changes** as deltas:

```clojure
(require '[org.replikativ.spindel.incremental.deltaable :as d])

;; Create deltaable vector
(def dv (d/deltaable-vector [1 2 3]))

;; Operations produce deltas
(def dv2 (conj dv 4))
(d/get-deltas dv2)
;; => [{:delta :add :path [3] :value 4}]

;; Multiple operations accumulate
(def dv3 (-> dv
             (conj 4)
             (assoc 0 10)))
(d/get-deltas dv3)
;; => [{:delta :add :path [3] :value 4}
;;     {:delta :update :path [0] :value 10 :old-value 1}]

;; Access underlying value
@dv3  ; => [10 2 3 4]
```

### Delta Format

```clojure
{:delta :add/:update/:remove
 :path [index-or-key]
 :value new-value
 :old-value old-value}  ; For :update only
```

### Deltaable Types

```clojure
;; Vector - tracks conj, assoc, pop
(d/deltaable-vector [1 2 3])

;; Map - tracks assoc, dissoc, update
(d/deltaable-map {:a 1 :b 2})

;; Set - tracks conj, disj
(d/deltaable-set #{:a :b :c})
```

### Dual Perspective in Spins

When you `track` a signal containing a deltaable collection:

```clojure
(def items (sig/signal (d/deltaable-vector [])))

(spin
  (let [{:keys [new old deltas]} (track items)]
    ;; Three ways to consume the change:

    ;; 1. State-based: just use current value
    (render-all new)

    ;; 2. Diff-based: compare old and new
    (when (not= (count new) (count old))
      (update-count-badge (count new)))

    ;; 3. Delta-based: process incremental changes
    (doseq [{:keys [delta path value]} deltas]
      (case delta
        :add (render-item-at path value)
        :remove (remove-item-at path)
        :update (update-item-at path value)))))
```

### Delta Transducers

For streaming delta processing:

```clojure
(require '[org.replikativ.spindel.incremental.combinators :as ic])

;; Transform deltas
(ic/map-delta (fn [d] (update d :value inc)))

;; Filter deltas
(ic/filter-delta (fn [d] (= :add (:delta d))))

;; Apply deltas to rebuild collection
(reduce d/apply-delta [] deltas)

;; Compact redundant operations (multiple updates to same path)
(d/compact-deltas deltas)
```

## Reactive Invalidation

### Dependency Tracking

Spindel automatically tracks dependencies when spins execute:

```clojure
(def signal-a (sig/signal 1))
(def signal-b (sig/signal 2))

(def my-spin
  (spin
    (let [a (:new (track signal-a))  ; Records dependency on signal-a
          b (:new (track signal-b))] ; Records dependency on signal-b
      (+ a b))))

;; Dependency graph now contains:
;; my-spin -> [signal-a, signal-b]
```

### Re-execution Flow

1. **Signal changes** via `swap!` or `reset!`
2. **Observers marked dirty** in dependency graph
3. **Topological sort** determines execution order
4. **Spins re-execute** when next dereferenced
5. **Cache updated** with new result

```clojure
;; Change signal-a
(swap! signal-a inc)  ; Now 2

;; my-spin is marked dirty but not re-executed yet (lazy)
;; On next deref:
@my-spin  ; Re-executes: (+ 2 2) => 4
```

### Topological Ordering (Glitch-Free)

When multiple signals change, observers execute in dependency order:

```clojure
(def x (sig/signal 1))
(def y (spin (:new (track x))))           ; depends on x
(def z (spin (+ (await y) (await y))))    ; depends on y

;; Execution order guaranteed: x -> y -> z
;; No glitches (z never sees inconsistent y)
```

## Async Sequences

Generate lazy async sequences using the `gen-aseq` macro:

```clojure
(require '[org.replikativ.spindel.seq.core :as seq-core :refer [gen-aseq yield]])

;; Simple generator
(def numbers
  (gen-aseq
    (yield 1)
    (yield 2)
    (yield 3)))

;; Consume with anext (returns [value rest-seq] or nil)
(spin
  (let [[v1 rest1] (await (seq-core/anext numbers))
        [v2 rest2] (await (seq-core/anext rest1))
        [v3 rest3] (await (seq-core/anext rest2))]
    [v1 v2 v3]))  ; => [1 2 3]
```

### Loop-Based Generation

```clojure
(def countdown
  (gen-aseq
    (loop [n 5]
      (when (pos? n)
        (yield n)
        (recur (dec n))))))

;; Generates: 5, 4, 3, 2, 1
```

### Integration with Spins

```clojure
(def processed
  (gen-aseq
    (loop [n 0]
      (when (< n 3)
        (let [result (await (fetch-data n))]  ; Can await spins!
          (yield (* 2 result))
          (recur (inc n)))))))
```

### Cold Semantics

Each consumer gets independent execution:

```clojure
(def gen (gen-aseq (yield (rand-int 100))))

;; Each anext starts fresh - different random numbers
@(seq-core/anext gen)  ; => [42 ...]
@(seq-core/anext gen)  ; => [17 ...] (different!)
```

## Pub/Sub System

Build reactive pipelines with fan-out and topic routing:

### Mult (Fan-Out)

Broadcast to multiple consumers:

```clojure
(require '[org.replikativ.spindel.pubsub.mult :as pubsub])

;; Source sequence
(def source (gen-aseq (yield 1) (yield 2) (yield 3)))

;; Create mult
(def m (pubsub/mult source))

;; Create taps (each receives ALL items)
(def tap1 (pubsub/tap m (pubsub/fixed-buffer 10)))
(def tap2 (pubsub/tap m (pubsub/fixed-buffer 10)))

;; Both tap1 and tap2 receive [1, 2, 3]
;; Producer waits for ALL taps before proceeding (backpressure)
```

### Pub (Topic Routing)

Route by topic:

```clojure
;; Source with different event types
(def events (gen-aseq
              (yield {:type :user :data "login"})
              (yield {:type :system :data "ping"})
              (yield {:type :user :data "click"})))

;; Create pub with topic function
(def p (pubsub/pub events :type))

;; Subscribe to topics
(def user-events (pubsub/sub p :user))
(def system-events (pubsub/sub p :system))

;; user-events receives: {:type :user :data "login"}, {:type :user :data "click"}
;; system-events receives: {:type :system :data "ping"}
```

### Buffer Types

```clojure
;; Fixed buffer - blocks when full
(pubsub/fixed-buffer 10)

;; Dropping buffer - drops newest when full
(pubsub/dropping-buffer 10)

;; Sliding buffer - drops oldest when full
(pubsub/sliding-buffer 10)

;; No buffer (rendezvous) - producer waits for each consumer
(pubsub/tap m nil)
```

## Rate Control Combinators

Control timing and flow of spin execution with rate control combinators:

```clojure
(require '[org.replikativ.spindel.spin.combinators :refer [debounce throttle sample relieve timeout accumulate]])
(require '[org.replikativ.spindel.incremental.interval :as iv])
```

### Basic Combinators

```clojure
;; Debounce - wait for quiet period before delivering
(spin
  (let [content (await (debounce (track content-signal) 300))]
    (render-preview content)))

;; Throttle - limit to max frequency (Hz)
(spin
  (let [pos (await (throttle (track mouse-signal) 60 (fn [_ new] new)))]
    (update-cursor pos)))

;; Sample - take value at fixed intervals
(spin
  (let [state (await (sample (track app-state) 5000))]
    (persist-to-server! state)))

;; Relieve - drop intermediate values, keep latest
(spin
  (let [focus-id (await (relieve (track focus-signal)))]
    (focus-element! focus-id)))

;; Timeout - race against deadline with fallback
(spin
  (let [data (await (timeout (fetch-remote-data) 100 cached-data))]
    (render data)))
```

### Delta Accumulation

When signals change faster than observers can process, use `accumulate` with `iv/merge-intervals` to preserve all deltas:

```clojure
;; Without accumulate - intermediate deltas may be lost
(spin
  (let [items (await (throttle (track items-signal) 10 (fn [_ new] new)))]
    ;; May miss some deltas if signal changes rapidly
    (process items)))

;; With accumulate - all deltas preserved via CRDT-like merging
(spin
  (let [iv (await (throttle (accumulate items-signal iv/merge-intervals) 10 (fn [_ new] new)))]
    ;; iv contains ALL deltas since last delivery
    (doseq [{:keys [delta path value]} (:deltas iv)]
      (case delta
        :add (render-item-at path value)
        :remove (remove-item-at path)
        :update (update-item-at path value)))))
```

The `merge-intervals` function is associative (CRDT-like), enabling accumulation without loss:
- Preserves original baseline (`old`) across accumulated intervals
- Concatenates and compacts deltas (removes redundant add+remove pairs)
- `merge(merge(a,b),c) = merge(a,merge(b,c))`

## Effect System

Effects extend the CPS transformation. Built-in effects:

- `await` - Read spin/deferred value, track dependency
- `track` - Read signal with dual perspective (new/old/deltas)
- `yield` - Yield value in async sequence generator

Libraries can register custom effects:

```clojure
(require '[org.replikativ.spindel.runtime.effects :as effects])

(effects/register-effect-by-symbol!
  'my.lib/sample
  (effects/sync-effect (fn [ctx args] ...))
  'my.lib/sample-adapter)
```

## Distributed Computing

Spindel integrates with [distributed-scope](https://github.com/simm-is/distributed-scope) for peer-to-peer distributed computing over WebSocket (kabel).

### Setup

Add distributed-scope to your dependencies:

```clojure
;; deps.edn
{:deps {org.replikativ/distributed-scope {:git/url "https://github.com/simm-is/distributed-scope"
                                   :git/sha "..."}}}
```

### Defining Distributed Functions

Use `defn-spin-remote` to define functions that execute across peers:

```clojure
(require '[org.replikativ.spindel.distributed.macros :refer [defn-spin-remote spin-remote]])
(require '[org.replikativ.spindel.distributed.core :as dist])

;; Define a function that runs on a remote peer
(defn-spin-remote fetch-page [server-id page-uuid]
  (spin-remote server-id [page-uuid]
    ;; This code executes on server-id
    (let [db (get-database)]
      (query-page db page-uuid))))

;; Call from client
(spin
  (let [page (await (fetch-page server-peer-id my-page-uuid))]
    (render-page page)))
```

### Key Concepts

- **Explicit argument vectors**: Variables crossing the network boundary must be declared
- **Compile-time validation**: Free variable analysis catches undeclared dependencies
- **Context addressing**: Target specific execution contexts on remote peers

```clojure
;; Target a specific context on the remote peer
(defn-spin-remote process-in-fork [server-id context-id data]
  (spin-remote [server-id context-id] [data]
    (heavy-computation data)))
```

### Execution Context Registry

Register contexts for remote addressing:

```clojure
;; On the server/peer
(require '[org.replikativ.spindel.distributed.core :as dist])

;; Register default context
(dist/register-context! :default my-execution-context)

;; Register forked context
(dist/register-context! :particle-1 (ctx/fork-context my-execution-context))
```

### Bridge Functions

Convert between spins and core.async channels (for kabel interop):

```clojure
;; Spin → Channel (for sending results)
(let [ch (dist/spin->chan my-spin)]
  ;; ch receives spin result when complete
  )

;; Channel → Spin (for receiving results)
(spin
  (let [result (await (dist/chan->spin response-channel))]
    (process result)))
```

## Architecture

```
User Code (spin macro)
        ↓
CPS Transformation (partial-cps + effect breakpoints)
        ↓
Effect System (await, track, yield - extensible)
        ↓
Runtime (7 fine-grained protocols)
        ↓
ExecutionContext + State Backend + Engine + Scheduler
        ↓
Overlay Backend (for forks) or Atoms Backend (for root)
```

**Key innovation**: All state in runtime (atom-backed, enables forking). Stateless spins access runtime via dynamic bindings.

## Project Structure

```
src/org/replikativ/spindel/
├── spin/                 # Spin, CPS transformation, combinators
├── effects/              # Effect system (await, track, yield)
├── runtime/              # Protocols, ExecutionContext, backends
├── state/                # Signals, fork-safe atoms, semaphores
├── sequence/             # Async sequence generation (gen-aseq)
├── pubsub/               # Pub/sub (buffer, mult, pub)
├── incremental/          # Delta-tracking collections
├── distributed/          # Remote spin invocation (core, macros)
├── dom/                  # Delta-direct DOM rendering
└── log.cljc              # Structured logging (Trove wrapper)
```

**40+ source files** total (all .cljc for CLJ/CLJS portability).

## Critical Rule: await vs @

**Inside spin bodies, ALWAYS use `await` or `track`, NEVER `@`**

```clojure
;; WRONG - blocks thread, breaks CPS
(spin (let [x @some-spin] ...))

;; CORRECT - CPS-transformed
(spin (let [x (await some-spin)] ...))
```

`@` is only for REPL convenience outside spins. Inside spins it blocks the thread and breaks the continuation chain.

## Running Tests

```bash
# Clojure tests
clj -M:test

# ClojureScript tests
npx shadow-cljs compile test && node target/test.js
```

### Test Logging

By default, logging is suppressed during tests for clean output. To enable logging for debugging:

```bash
# Enable all logging
SPINDEL_TEST_LOG=true clj -M:test

# From REPL
(require '[org.replikativ.spindel.test-config :as tc])
(tc/enable-test-logging!)        ; Enable at :debug level
(tc/enable-test-logging! :trace) ; Enable at specific level
(tc/disable-test-logging!)       ; Suppress again
```

## Logging

Spindel uses [Trove](https://github.com/taoensso/trove) for structured logging:

```clojure
(require '[org.replikativ.spindel.log :as log])

;; Configure logging (call once at startup)
(log/configure! {:min-level :info})  ; :trace :debug :info :warn :error :fatal

;; Structured logging with levels
(log/debug! {:event ::my-event :data {:key "value"}})
(log/info!  {:event ::startup :data {:port 8080}})
(log/warn!  {:event ::deprecated :data {:fn 'old-fn}})
(log/error! {:event ::failure :data {:error e}})
```

Log output format:
```
2026-02-07T10:30:00.000Z :info my.namespace
  data: {:port 8080}
```

## Dependencies

**Core**:
- Clojure 1.12.0
- ClojureScript 1.11.132
- `org.replikativ/hasch` - Content-addressed hashing
- `is.simm/partial-cps` - CPS transformation engine
- `org.replikativ/yggdrasil` - Data structure utilities
- `org.clojure/core.async` - Async primitives
- `com.taoensso/trove` - Structured logging
- `org.clojure/tools.analyzer.jvm` - Code analysis for CPS
- `riddley/riddley` - Code walking for macro expansion

## Examples

The `examples/` directory contains interactive demos showcasing spindel's incremental DOM rendering:

| Demo | Description |
|------|-------------|
| [TODO MVC](examples/public/todo-demo.html) | Classic TODO app with add/remove/toggle/filter - shows minimal DOM operations |
| [Block Editor](examples/public/block-editor-demo.html) | Hierarchical block editor with indent/outdent and keyboard navigation |
| [Infinite Scroll](examples/public/infinite-scroll-demo.html) | Virtual list with 10,000 items, only ~10 rendered - O(delta) scrolling |
| [TipTap Integration](examples/public/tiptap-demo.html) | Rich text editor integration using `foreign-node` primitive |

### Running Examples

```bash
cd examples
npm install
npm run watch:todo          # Or: watch:block-editor, watch:infinite-scroll, watch:tiptap
# Open http://localhost:8080/todo-demo.html
```

Or watch all demos at once:

```bash
npm run watch:all
# Open http://localhost:8080/
```

## Documentation

- [CLAUDE.md](CLAUDE.md) - Comprehensive development guide
- [doc/DOM_DESIGN.md](doc/DOM_DESIGN.md) - Delta-direct DOM rendering architecture
- [doc/INCREMENTAL_MODEL.md](doc/INCREMENTAL_MODEL.md) - Incremental computation model
- [doc/INTERVAL_INTEGRATION.md](doc/INTERVAL_INTEGRATION.md) - Interval-based delta tracking

## License

Apache License 2.0. See [LICENSE](LICENSE) for details.

## Authors

Christian Weilbach ([@whilo](https://github.com/whilo))
