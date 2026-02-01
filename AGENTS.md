# CLAUDE.md

This file provides guidance to Claude Code when working with the **Spindel** codebase.

## Project Overview

**Spindel** is an incremental reactive computation system for Clojure/ClojureScript featuring:

- **Cached reactive spins** with automatic dependency tracking (every spin is cached by default)
- **Mutable signals** with dual perspective (new value + old value + deltas)
- **Copy-on-write forking** with O(1) runtime forking via overlay backends
- **Fork-safe state primitives** - atoms and signals stored in runtime, enabling checkpointing
- **Deltaable collections** - vectors, maps, sets that track structural changes
- **Async sequences** - generator-based lazy sequences with `yield`
- **Pub/sub system** - fan-out (mult) and topic routing (pub) with backpressure
- **CPS execution** via partial-cps integration with effect handler extensibility
- **Glitch-free FRP** using topological ordering for consistent updates

**Status**: Core implementation complete (spins, signals, runtime, effects, forking, sequences, pub/sub). 337 CLJ / 149 CLJS tests passing.

## Architecture at a Glance

```
User Code (spin macro)
        ↓
CPS Transformation (partial-cps + effect breakpoints)
        ↓
Effect System (await, track, yield - extensible via PEffectHandler)
        ↓
Runtime (protocols: PGraph, PSpinLifecycle, PState, PEngine, etc.)
        ↓
ExecutionContext + State Backend + Engine + Scheduler/Executor
        ↓
Overlay Backend (for forks) or Atoms Backend (for root)
```

**Key innovation**: Protocol-based design with fine-grained protocols (7 runtime + additional) instead of monolithic interfaces. Runtime is a pure data structure (atom-backed state) enabling fork/checkpoint. Overlay backends provide O(1) forking with copy-on-write semantics.

## Core Abstractions

### 1. Spin (Stateless CPS Interface)

**File**: [src/is/simm/spindel/spin/core.cljc](src/is/simm/spindel/spin/core.cljc)

```clojure
(deftype Spin [spin-id spin-fn])
;; Implements:
;; - IFn: (spin resolve reject) → value | ::incomplete
;; - PSpin: (spin-id spin) → spin-id
;; - IDeref: @spin (REPL convenience only - DO NOT use inside spins!)
```

**Critical design**: Spins are **stateless** - no internal atoms. All state lives in runtime (enables forking).

**Access runtime via dynamic bindings**:
- `rtc/*execution-context*` - Current runtime instance
- `rtc/*spin-id*` - Current spin ID during execution

### 2. Signal (Mutable Time-Varying Values)

**File**: [src/is/simm/spindel/state/signal.cljc](src/is/simm/spindel/state/signal.cljc)

```clojure
(defrecord SignalRef [id initial-value])

;; Signal state in runtime at [:nodes signal-id]:
{:snapshot current-value           ; Wrapped with wrap-deltaable if applicable
 :old-snapshot previous-value
 :deltas [{:delta :add :path [2] :value todo3}]  ; Structural changes
 :deltaable? true                  ; Can track deltas?
 :observers #{spin-1 spin-2}}      ; Dependent spins
```

**Dual perspective pattern**: Every signal change provides both full state and incremental deltas.

**Auto-wrapping**: Signals automatically wrap collection values as deltaable, enabling automatic delta tracking without explicit wrapping.

### 3. Fork-Safe Atoms

**File**: [src/is/simm/spindel/state/atom.cljc](src/is/simm/spindel/state/atom.cljc)

For non-reactive state that still needs fork isolation:

```clojure
(require '[org.replikativ.spindel.state.atom :as atom])

;; Create runtime-stored atom
(def cache (atom/atom {}))

;; Standard atom API (100% compatible with clojure.core/atom)
(swap! cache assoc :key "value")
@cache  ; => {:key "value"}
```

**Key properties**:
- Stored in runtime at `[:atoms atom-id]`
- Fork-safe (mutations isolated to fork via overlay backend)
- Auto-cleaned when GC'd (JVM only, uses Cleaner API)
- **DO NOT capture runtime** - uses `*execution-context*` dynamically

### 4. Runtime (Execution Context)

**Files**:
- [src/is/simm/spindel/runtime/core.cljc](src/is/simm/spindel/runtime/core.cljc) - Facades + dynamic bindings
- [src/is/simm/spindel/runtime/protocols.cljc](src/is/simm/spindel/runtime/protocols.cljc) - Protocol definitions
- [src/is/simm/spindel/runtime/context.cljc](src/is/simm/spindel/runtime/context.cljc) - ExecutionContext (main API)
- [src/is/simm/spindel/runtime/impl/simple.cljc](src/is/simm/spindel/runtime/impl/simple.cljc) - Core implementation
- [src/is/simm/spindel/runtime/state_backend.cljc](src/is/simm/spindel/runtime/state_backend.cljc) - State backend abstraction

**Seven runtime protocols** (defined in `runtime/protocols.cljc`):
1. **PGraph** - Dependency graph (record-deps!, clear-deps!, ordered-observers)
2. **PDepsTracking** - Transient dependency recording during execution
3. **PSpinLifecycle** - Spin registration, caching, scheduling, dirty marking
4. **PContinuation** - Continuation management (add, remove, resume)
5. **PEngine** - Event ingress (enqueue!)
6. **PScheduler** - Scheduling strategy (get-executor, schedule-spin-execution!)
7. **PState** - General atomic state (swap-state!, get-state, cas-state!)

**Additional protocols** (in other namespaces):
- **PExecutor** - Execution location (execute!, execute-after!) - in `runtime/scheduler.cljc`
- **PSpin** - Spin ID accessor (spin-id) - in `spin/protocols.cljc`
- **PEffectHandler** - Effect handling - in `effects/core.cljc`

**Runtime creation**:
```clojure
(require '[org.replikativ.spindel.runtime.core :as rtc])

;; Atoms-based (portable CLJ/CLJS)
(def ctx (ctx/create-execution-context))
```

### 5. Effect System (CPS Extension Points)

**Files**:
- [src/is/simm/spindel/effects/core.cljc](src/is/simm/spindel/effects/core.cljc) - Effect protocol
- [src/is/simm/spindel/effects/reactive.cljc](src/is/simm/spindel/effects/reactive.cljc) - Built-in effects

**PEffectHandler protocol**:
```clojure
(defprotocol PEffectHandler
  (handle-effect [this runtime args resolve reject]))
```

**Built-in effects**:
- `await` - Read spin/deferred value, track dependency
- `track` - Read signal with dual perspective (new/old/deltas)
- `yield` - Yield value in async sequence generator (for `gen-aseq`)

**Extensibility**: Libraries register effects via symbol-based registration:
```clojure
(register-effect-by-symbol!
  'my.lib/sample
  (sync-effect (fn [ctx args] ...))
  'my.lib/sample-adapter)
```

The spin macro queries the effect registry at expansion time and installs breakpoints.

## Copy-on-Write Runtime Forking

Spindel's runtime supports **O(1) forking** with copy-on-write semantics via overlay backends.

### Forking API

**File**: [src/is/simm/spindel/runtime/context.cljc](src/is/simm/spindel/runtime/context.cljc)

```clojure
(require '[org.replikativ.spindel.runtime.context :as ctx])

;; Create main context
(def ctx-main (ctx/create-execution-context))

;; Snapshot (immutable copy of state)
(def snapshot (ctx/snapshot-context ctx-main))

;; Restore snapshot to create a fork
(def ctx-fork (ctx/restore-snapshot snapshot))

;; Or direct lightweight fork (O(1) - creates overlay)
(def ctx-fork (ctx/fork-context ctx-main))
```

### Isolation Guarantees

```clojure
;; Parent context with signal
(binding [rtc/*execution-context* ctx-main]
  (def counter (sig/signal 0))
  (swap! counter inc))  ; counter = 1

;; Fork and mutate
(def ctx-fork (ctx/restore-snapshot (ctx/snapshot-context ctx-main)))
(binding [rtc/*execution-context* ctx-fork]
  (swap! counter inc)   ; fork: counter = 2
  (swap! counter inc))  ; fork: counter = 3

;; Parent unchanged!
(binding [rtc/*execution-context* ctx-main]
  @counter)  ; => 1 (still 1!)
```

### Overlay Backend Behavior

| Operation | Parent sees? | Fork sees? |
|-----------|--------------|------------|
| Fork reads parent state | N/A | Yes (via fallback) |
| Fork mutates state | No | Yes (in overlay) |
| Parent mutates state | Yes | No (isolated) |
| Fork creates new state | No | Yes (in overlay) |

### Serialization

```clojure
;; Serialize context to EDN (for checkpointing/distribution)
(def serialized (ctx/serialize-context ctx-main))

;; Deserialize back to live context
(def ctx-restored (ctx/deserialize-context serialized))
```

### Use Cases

- **Speculative computation**: Try different paths, discard failures
- **Checkpointing**: Snapshot state, restore later
- **Parallel inference**: Run multiple computations sharing common state
- **Testing**: Fork before destructive operations

## Deltaable Collections

**Files**: `src/is/simm/spindel/incremental/deltaable.cljc`, `combinators.cljc`

Track top-level structural changes as deltas. Types: `deltaable-vector`, `deltaable-map`, `deltaable-set`.

```clojure
(def dv (-> (d/deltaable-vector [1 2]) (conj 3)))
(d/get-deltas dv)  ; => [{:delta :add :path [2] :value 3}]
```

See README.md for full documentation.

## Async Sequences & Pub/Sub

**Files**: `src/is/simm/spindel/sequence/`, `src/is/simm/spindel/pubsub/`

- `gen-aseq` + `yield` for lazy async sequences
- `mult` for fan-out, `pub` for topic routing
- Buffer types: `fixed-buffer`, `dropping-buffer`, `sliding-buffer`

See README.md for full documentation.

## CRITICAL: await vs @ in Spins

**⚠️ ALWAYS use `await` or `track` inside spin bodies, NEVER use `@` (deref) ⚠️**

This is a common footgun that breaks the CPS continuation chain.

### The Rule

Inside `(spin/spin ...)` bodies:
- ✅ **CORRECT**: `(await some-spin)` or `(track signal)`
- ❌ **WRONG**: `@some-spin` or `@signal`

Outside spin context (REPL, tests):
- ✅ **OK**: `@my-spin` - For getting final result only

### Why This Matters

- `@` (deref) **blocks the thread** - waits synchronously
- This **breaks the CPS continuation chain**
- Only `await` and `track` are **CPS-transformed** by the spin macro
- The spin macro doesn't see `@` calls, so they become blocking operations

### Examples

```clojure
;; ❌ WRONG - blocks thread, breaks CPS!
(spin/spin
  (let [result @some-spin]  ; BAD!
    (process result)))

;; ✅ CORRECT - CPS-transformed
(require '[org.replikativ.spindel.effects.reactive :refer [await track]])
(spin/spin
  (let [result (await some-spin)]  ; GOOD!
    (process result)))

;; ✅ CORRECT - for signals
(spin/spin
  (let [{:keys [new old delta]} (track some-signal)]  ; GOOD!
    (* 2 new)))

;; ✅ OK - outside spin context (REPL convenience)
(let [my-spin (spin/spin (+ 1 2))]
  @my-spin)  ; OK for getting final results
```

### Quick Reference

| Context | Spins/Deferred | Signals |
|---------|---------------|---------|
| Inside `spin/spin` | `(await x)` ✅ | `(track x)` ✅ |
| Inside `spin/spin` | `@x` ❌ | `@x` ❌ |
| Outside (REPL) | `@x` ✅ | `@x` ✅ |

## CRITICAL: CPS Transformation Limitations

**⚠️ The spin macro has similar limitations to core.async's `go` macro ⚠️**

The CPS transformation (via partial-cps) has important limitations that you must understand to write correct code.

### What DOESN'T Work

**CPS transformation does NOT work across function boundaries or in these constructs:**

❌ **`for`** - List comprehension that creates lazy sequences
❌ **Higher-order functions** - `map`, `filter`, `reduce` with effect calls in the function argument
❌ **Function boundaries** - Effects called inside functions passed as arguments

These constructs don't work because:
1. The spin macro only transforms code **lexically** within the spin body
2. It cannot see into function closures or lazy sequence generators
3. Effects in these contexts won't be CPS-transformed → runtime binding errors

### What DOES Work

✅ **`loop/recur`** - Direct recursion in spin body
✅ **Inline effect calls** - Effects called directly in the spin lexical scope
✅ **Nested spins** - Use `spin` macro again inside higher-order functions

### Examples

```clojure
;; ❌ WRONG - doseq doesn't work with effects
(spin
  (doseq [x data]
    (constrain (normal mu sigma) x)))  ; ERROR: effects not transformed!

;; ✅ CORRECT - use loop/recur instead
(spin
  (loop [remaining data]
    (when (seq remaining)
      (constrain (normal mu sigma) (first remaining))
      (recur (rest remaining)))))

;; ❌ WRONG - for comprehension doesn't work
(spin
  (for [x data]
    (await (fetch-spin x))))  ; ERROR: effects not transformed!

;; ✅ CORRECT - use loop/recur with accumulator
(spin
  (loop [remaining data
         results []]
    (if (empty? remaining)
      results
      (let [result (await (fetch-spin (first remaining)))]
        (recur (rest remaining)
               (conj results result))))))

;; ❌ WRONG - map with effects in function
(spin
  (map #(await (process-spin %)) items))  ; ERROR: effects in closure!

;; ✅ CORRECT - use sequence combinators or nested spins
(require '[org.replikativ.spindel.sequence.core :as seq])
(spin
  (seq/map-spins process-spin items))  ; Uses sequence combinators

;; ✅ ALSO CORRECT - explicit loop
(spin
  (loop [remaining items
         results []]
    (if (empty? remaining)
      results
      (let [result (await (process-spin (first remaining)))]
        (recur (rest remaining)
               (conj results result))))))
```

### Higher-Order Functions

When you need effects inside higher-order functions, you have two options:

**Option 1: Sequence Combinators** (preferred when available)
```clojure
(require '[org.replikativ.spindel.sequence.core :as seq])

(spin
  (seq/map-spins fetch-user user-ids))  ; CPS-aware combinator
```

**Option 2: Nested Spins** (when combinators don't exist)
```clojure
(spin
  (map (fn [user-id]
         (spin  ; ← New spin context
           (await (fetch-user user-id))))
       user-ids))
```

### Why These Limitations Exist

This is **identical to core.async's `go` macro limitations**:

- **Lexical transformation**: The macro can only transform code it can see at expansion time
- **Lazy sequences**: `for`, `doseq` create lazy sequences with hidden state machines
- **Function closures**: Functions passed to `map`/`filter` are opaque to the macro
- **CPS boundary**: Each effect needs to be a CPS breakpoint, but the macro can't insert breakpoints inside closures

### Workarounds

1. **Use `loop/recur`** for iteration with effects
2. **Use sequence combinators** from `spindel.sequence.core` (in progress)
3. **Nest `spin` macros** when you need effects in higher-order function arguments
4. **Avoid lazy sequences** inside spin bodies

### Future Work

We're expanding sequence combinators to make this easier:
- `seq/map-spins` - Map over sequence with spin creation
- `seq/filter-spins` - Filter with spin predicates
- `seq/reduce-spins` - Reduce with spin accumulation

But for now, **use `loop/recur` when you need iteration with effects**.

## CRITICAL: Runtime Access via Protocols Only

**⚠️ ALWAYS use runtime protocol methods, NEVER access runtime fields directly ⚠️**

This maintains the abstraction boundary and ensures code works across all runtime implementations.

### The Rule

When working with runtime state:
- ✅ **CORRECT**: `(rtp/get-state runtime [:spins tid])` or `(rtc/get-state [:spins tid])`
- ❌ **WRONG**: `(:state runtime)` or `@(:state runtime)`

### Why This Matters

- Direct field access **breaks the abstraction** - couples code to specific runtime implementations
- Protocol methods work across **all runtime types** (AtomsRuntime, SequentialRuntime, StmRuntime)
- Enables **future changes** to runtime internals without breaking code
- The runtime protocols are the **public API** - fields are implementation details

### Examples

```clojure
;; ❌ WRONG - direct field access
(let [state-atom (:state runtime)]
  (get-in @state-atom [:spins tid :result]))

;; ✅ CORRECT - use protocol methods
(rtp/get-state runtime [:spins tid :result])

;; ❌ WRONG - accessing internal structure
(swap! (:state runtime) assoc-in [:spins tid] value)

;; ✅ CORRECT - use protocol methods
(rtp/swap-state! runtime [:spins tid] (constantly value))
```

### Available Protocol Methods

- `rtp/get-state` - Read state at path
- `rtp/swap-state!` - Atomic update at path
- `rtp/swap-state-args!` - Atomic update with args
- `rtp/cas-state!` - Compare-and-set at path

Or use the facade functions in `runtime/core.cljc` which automatically use `*execution-context*`:
- `rtc/get-state`
- `rtc/swap-state!`
- etc.

## Key Design Principles

### 1. Stateless Spins = Fork-Safe Runtime

All state lives in the runtime atom/refs, never in spin objects:
- ✅ Enables forking (copy runtime = fork state)
- ✅ Enables checkpointing (save/restore runtime)
- ✅ Enables distributed execution (serialize runtime)

### 2. Protocol Granularity

Fine-grained protocols (7 runtime + additional) instead of monolithic interfaces:
- Implementations mix & match what they support
- High-level code calls through facades in `runtime/core.cljc`
- Enables experimentation without breaking old code

### 3. CPS as Universal Extension Point

Effects are the **only** way to extend spin execution:
- Spin macro doesn't hardcode semantics
- Libraries register symbols at load time
- Breakpoints installed at macro expansion
- Result: truly pluggable architecture

### 4. Caching = Incrementality

Every spin is cached by default (unlike Missionary):
- Automatic memoization + dependency tracking
- Re-execution only on signal changes
- No need to explicitly mark computations as incremental

### 5. Dual Perspective for Signals

Signals expose old/new values + deltas:
- State-based consumers: use `:new`
- Delta-based consumers: use `:deltas`
- Diff-based consumers: compare `:new` and `:old`
- Single mechanism serves all consumption patterns

## Glitch Prevention

Uses **topological sorting** (like Clara Rules and Missionary):
- Runtime maintains dependency graph of spins and signals
- When signals change, observers notified in topological order
- Spins execute in correct dependency order
- Ensures glitch-free updates without complex clock synchronization

**Implementation**: [src/is/simm/spindel/runtime/impl/atoms.cljc](src/is/simm/spindel/runtime/impl/atoms.cljc) `ordered-observers` function.

## Automatic Dependency Tracking

Spindel automatically tracks dependencies at runtime for incremental reactivity:

### How It Works

**Tracking Phase (During Execution):**
```clojure
(spin
  (let [x (track signal-1)      ; ← Automatically records dependency
        y (await spin-a)]       ; ← Automatically records dependency
    (* x y)))
```

- `track` calls `rtc/deps-track-signal!` to record signal dependency
- `await` calls `rtc/deps-track-spin!` to record spin dependency
- Dependencies stored in `[:tracking spin-id]` during execution

**Commit Phase (On Completion):**
```clojure
;; In spin resolve-fn (spin/core.cljc:113)
(rtc/graph-commit-deps! spin-id)
```

- Moves dependencies from `[:tracking spin-id]` to `[:graph spin-id]`
- Updates reverse indexes (signal → observers)
- Enables invalidation and topological ordering

### Graph Structure

```clojure
{:graph {spin-id {:signals #{sig-1 sig-2}      ; Signals observed
                  :spins #{spin-a spin-b}}}    ; Spins awaited
 :signals {sig-id {:observers #{spin-ids}}}    ; Reverse index
 :tracking {spin-id {:signals #{...}           ; Transient (pre-commit)
                     :spins #{...}}}}
```

### Protocols

**PDepsTracking** - Transient tracking during execution:
- `track-signal-dep!` - Record signal observation
- `track-spin-dep!` - Record spin await

**PGraph** - Committed dependency graph:
- `record-deps!` - Commit tracked deps to graph
- `clear-deps!` - Remove spin from graph
- `ordered-observers` - Topological order for glitch-free updates

### Use Cases

1. **Incremental Reactivity:** When signal changes, only re-execute dependent spins
2. **Glitch Prevention:** Execute observers in dependency order
3. **Content-Addressed Caching:** (Planned) Use dependency values for deduplication across forks

See [FORKING_DESIGN.md](FORKING_DESIGN.md) for how dependency tracking enables cross-fork computation sharing and [CODE_DEDUPLICATION_DESIGN.md](CODE_DEDUPLICATION_DESIGN.md) for multi-level content-addressed caching with JIT compilation support.

## Directory Structure

```
src/is/simm/spindel/
├── core.cljc                    # Main API (placeholder)
├── log.cljc                     # Structured logging via Trove
├── spin/
│   ├── core.cljc               # Spin deftype
│   ├── protocols.cljc          # PSpin protocol
│   ├── cps.cljc                # spin macro + CPS transformation
│   ├── continuation.cljc       # Continuation utilities
│   ├── result.cljc             # Result record type
│   ├── lifecycle.cljc          # Cancellation, cleanup, status
│   ├── combinators.cljc        # join, parallel, race, sleep
│   ├── error.cljc              # Error handling: attempt, absolve
│   └── sync.cljc               # Deferred synchronization
├── effects/
│   ├── core.cljc               # PEffectHandler protocol + registration
│   ├── await.cljc              # await effect (spins + deferred)
│   ├── track.cljc              # track effect (signals)
│   └── yield.cljc              # yield effect (sequence generation)
├── runtime/
│   ├── core.cljc               # Facades + dynamic bindings
│   ├── protocols.cljc          # 7 runtime protocols
│   ├── context.cljc            # ExecutionContext (main API)
│   ├── scheduler.cljc          # PExecutor + implementations
│   ├── state_backend.cljc      # State backend abstraction
│   ├── addressing.cljc         # Deterministic addressing
│   ├── bindings.cljc           # Dynamic binding management
│   ├── cache.cljc              # Content-addressed caching
│   ├── node_protocols.cljc     # Node-level protocols
│   ├── node_types.cljc         # SpinNode, SignalNode records
│   └── impl/
│       ├── atoms.cljc          # Atoms runtime (delegates to context)
│       └── simple.cljc         # Core implementation
├── sequence/
│   ├── core.cljc               # Async sequence generation
│   └── combinators.cljc        # Stream combinators
├── pubsub/
│   ├── buffer.cljc             # Fixed, sliding, dropping buffers
│   ├── mult.cljc               # Fan-out to multiple taps
│   ├── pub.cljc                # Topic-based routing
│   └── core.cljc               # Public API
├── state/
│   ├── atom.cljc               # Fork-safe runtime atoms
│   ├── signal.cljc             # Signal creation/manipulation
│   └── semaphore.cljc          # Semaphore primitive
└── incremental/
    ├── deltaable.cljc          # Delta-tracking collections
    └── combinators.cljc        # Delta-aware operations
```

**38 source files** (all .cljc for CLJ/CLJS portability).

## Current Implementation Status

### ✅ Implemented

- Full spin system with CPS transformation
- Signal system with dual perspective (new/old/deltas)
- Runtime protocols & implementations (atoms-based, portable)
- Effect system with extensibility (await, track, yield)
- Executor implementations (immediate, thread pool, event loop)
- Engine with topological ordering and event-based draining
- **Deltaable collections** (vector, map, set with delta tracking)
- **Fork-safe atoms** (runtime-stored, GC-cleaned)
- **Runtime forking** (snapshot, restore, fork with overlay backends)
- **Serialization** (serialize-context, deserialize-context)
- **Dependency tracking** (PDepsTracking, PGraph) for incremental reactivity
- **Async sequences** (gen-aseq, yield, cold semantics)
- **Pub/sub system** (buffer, mult, pub - core.async-style primitives over PAsyncSeq)
- **Test suite** (337 CLJ tests / 149 CLJS tests passing)
- **ClojureScript compatibility** (full cross-platform support)

### ❌ Not Yet Implemented

- **Content-addressed spin caching** (for cross-fork deduplication)
- **Benchmarks** (need to create)
- Some combinators (race, timeout partially done)

## Distributed Computing

Spindel integrates with [distributed-scope](https://github.com/simm-is/distributed-scope) for peer-to-peer distributed computing.

**Files**:
- [src/is/simm/spindel/distributed/core.cljc](src/is/simm/spindel/distributed/core.cljc) - Bridge functions (spin↔channel)
- [src/is/simm/spindel/distributed/macros.cljc](src/is/simm/spindel/distributed/macros.cljc) - `defn-spin-remote`, `spin-remote`

### Defining Distributed Functions

```clojure
(require '[org.replikativ.spindel.distributed.macros :refer [defn-spin-remote spin-remote]])
(require '[org.replikativ.spindel.distributed.core :as dist])

;; Define a function that runs on a remote peer
(defn-spin-remote fetch-page [server-id page-uuid]
  (spin-remote server-id [page-uuid]
    ;; This code executes on server-id peer
    (let [db (get-database)]
      (query-page db page-uuid))))

;; Call from client
(spin
  (let [page (await (fetch-page server-peer-id my-page-uuid))]
    (render-page page)))
```

### Key Concepts

- **Explicit argument vectors**: Variables crossing network boundary must be declared in `[...]`
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
(dist/register-context! :default my-execution-context)
(dist/register-context! :particle-1 (ctx/fork-context my-execution-context))
```

### Bridge Functions

Convert between spins and core.async channels (for kabel interop):

```clojure
;; Spin → Channel (for sending results)
(dist/spin->chan my-spin)

;; Channel → Spin (for receiving results)
(spin
  (let [result (await (dist/chan->spin response-channel))]
    (process result)))
```

### Testing Distributed Code

Distributed tests require the `:test` alias which includes distributed-scope:

```bash
clj -M:test
```

Test files are in `test/is/simm/spindel/distributed/`:
- `bridge_test.cljc` - Spin↔channel conversion tests
- `macro_test.clj` - `defn-spin-remote` macro tests
- `integration_test.clj` - End-to-end tests with kabel WebSocket peers

## Dependencies

**Key dependencies** from [deps.edn](deps.edn):

```clojure
{:deps
 {org.clojure/clojure {:mvn/version "1.12.0"}
  org.clojure/clojurescript {:mvn/version "1.11.132"}
  org.clojure/tools.analyzer.jvm {:mvn/version "1.3.2"}
  riddley/riddley {:mvn/version "0.2.0"}
  pangloss/pattern {:local/root "../pattern"}          ; Pattern matching
  com.taoensso/trove {:mvn/version "1.1.0"}           ; Structured logging
  org.replikativ/partial-cps {:local/root "../partial-cps"}  ; CPS transformation
  io.replikativ/hasch {:local/root "../hasch"}        ; Content hashing
  org.clojure/core.async {:mvn/version "1.6.681"}}}   ; Async primitives
```

**Critical local dependencies**:
- `../pattern` - Pattern matching library
- `../partial-cps` - CPS transformation engine
- `../hasch` - Content-addressable hashing for deduplication

## REPL-Driven Development

**You have direct access to a Clojure REPL** via repl-mcp tools. Use this aggressively for fast iteration.

**Start the REPL**:
```bash
clj -M:repl-mcp
```

**Use the REPL for**:
- Testing functions as you write them
- Interactive debugging
- Exploring the codebase
- Quick experiments

**Best practices**:
1. Write a function in source (Edit/Write tools)
2. Evaluate it in REPL immediately
3. Test with sample data
4. Fix issues, re-eval, repeat
5. Once working, move to next function
6. Write tests to prevent regressions

**Example workflow**:
```clojure
;; Load namespace
(require '[org.replikativ.spindel.spin.core :as spin] :reload)

;; Test function
(def ctx (create-runtime {:impl :atoms}))
(binding [rtc/*execution-context* ctx]
  (def t (spin/make-spin (fn [resolve reject] (resolve 42)) :test))
  @t)  ; => 42

;; Check state
(rtc/get-state [:spin-outputs :test])  ; => 42
```

## Development Approach

### Keep It Lean

**IMPORTANT**: Don't create compatibility layers or "make it work somehow". When refactoring is needed:
1. Analyze the situation
2. Propose clean refactoring options
3. Ask the user which approach to take
4. Implement cleanly

### Avoid Unnecessary Files

- **Don't create** documentation files (.md) unless explicitly requested
- **Don't create** example files unless explicitly requested
- **Focus on** core implementation and tests

### When to Ask vs When to Proceed

**Ask the user when**:
- Multiple refactoring approaches exist
- Design decision affects architecture
- Unclear requirements
- Trade-offs between approaches

**Proceed directly when**:
- Obvious bug fix
- Clear implementation spin
- Following established patterns in codebase
- Writing tests for existing functionality

## CRITICAL: Trampolines and *in-trampoline*

**⚠️ When resuming continuations from external contexts, ALWAYS bind `*in-trampoline*` to `false` ⚠️**

This is essential for proper CPS execution when re-entering the execution engine from outside.

### The Rule

When calling `cont/resume` to invoke continuations:
- ✅ **Set `*in-trampoline* = false`** when dispatching from external contexts
- ❌ **Keep default binding** when already inside CPS-transformed code

### When to Set *in-trampoline* = false

Bind `*in-trampoline*` to `false` when resuming continuations from:
- **Different threads** - futures, thread pools, CompletableFuture callbacks
- **Timer/delay callbacks** - setTimeout, ScheduledExecutorService
- **External library callbacks** - HTTP responses, database queries, file I/O
- **Event handlers** - UI events, message queue consumers
- **Any "re-entry"** into the CPS execution engine from outside

### Why This Matters

The `*in-trampoline*` dynamic var tracks whether we're already inside a trampoline loop:
- When `true`, `invoke-continuation` returns Thunks directly for the current trampoline to unwrap
- When `false`, `invoke-continuation` establishes its own trampoline to unwrap Thunks
- Without proper binding, Thunks accumulate without being executed → hangs/stack overflow

### Examples

```clojure
;; ✅ CORRECT - async callback from external context
(defn async-fetch [value]
  (spin/make-spin
    (fn [resolve reject]
      (future
        (try
          (Thread/sleep 10)
          ;; Re-entering execution engine from different thread
          (binding [async/*in-trampoline* false]
            (cont/resume resolve value))
          (catch Throwable t
            (binding [async/*in-trampoline* false]
              (cont/resume reject t))))))))

;; ✅ CORRECT - timer callback
(defn schedule-delayed [ms value resolve reject]
  (schedule-spin ms
    #(binding [async/*in-trampoline* false]
       (cont/resume resolve value))))

;; ❌ WRONG - inside CPS code (already in trampoline)
(defn wrapped-cps-fn [cont-r]
  (fn [_r _e]
    ;; Don't bind here - we're already inside the spin's trampoline
    (cont/resume cont-r nil)
    spin-core/incomplete))
```

### How Trampolines Work

CPS-transformed code (from `spin` macro) establishes a trampoline loop:
```clojure
(binding [*in-trampoline* true]
  (loop [result (cps-body)]
    (if (instance? Thunk result)
      (recur ((.-f result)))  ; Unwrap and continue
      result)))               ; Done
```

When we're already inside this loop, `*in-trampoline* = true`, so:
- `invoke-continuation` sees the binding
- Returns Thunks directly for the current loop to unwrap
- Avoids nested trampolines

When we dispatch from outside (different thread/callback), `*in-trampoline*` is unbound (or `false`):
- Must explicitly bind to `false` before calling `cont/resume`
- `invoke-continuation` establishes new trampoline
- Properly unwraps all Thunks before returning

### Quick Reference

| Context | Bind *in-trampoline*? | Reason |
|---------|----------------------|--------|
| Future/thread pool | `false` ✅ | Different thread = new dispatch |
| Timer callback | `false` ✅ | Event loop re-entry |
| External library callback | `false` ✅ | Outside CPS context |
| Inside CPS-transformed code | Keep default ❌ | Already in trampoline |
| Wrapped continuation in same spin | Keep default ❌ | Same execution context |

## Terminology

- **Spin** - Cached reactive computation unit (not "async")
- **Signal** - Mutable reactive source (standard FRP term)
- **await** - Suspend and track dependency (CPS-transformed)
- **track** - Read signal with dual perspective (CPS-transformed)
- **yield** - Emit value from async sequence generator (CPS-transformed)
- **Deltaable** - Collections that record operations as deltas
- **Runtime** - Execution context (atom-backed state)
- **ExecutionContext** - Main runtime abstraction (holds state backend, engine, scheduler)
- **Overlay Backend** - Copy-on-write state backend for forked contexts
- **Snapshot** - Immutable copy of runtime state (for checkpointing/forking)
- **Mult** - Fan-out primitive (one source → multiple consumers)
- **Pub** - Topic-based routing primitive (route by topic function)
- **Trampoline** - Loop that unwraps Thunk objects to prevent stack overflow in CPS code
- **gen-aseq** - Generator macro for lazy async sequences

## Integration Points

### With laufzeit/

1. **Dynamic binding instead of runtime threading**: Uses `*execution-context*` instead of passing runtime as first param to continuations
2. **Stateless spins**: spin-id parameter instead of internal state
3. **Finer-grained protocols**: 7 runtime protocols instead of monolithic interfaces
4. **Symbol-based effect registration**: Libraries can extend without modifying core
5. **Better separation**: Effects/runtime/spins are cleanly separated

### With partial-cps

**Local dependency**: `../partial-cps`

The spin macro in [src/is/simm/spindel/spin/cps.cljc](src/is/simm/spindel/spin/cps.cljc) uses partial-cps for CPS transformation:

1. Build breakpoints for registered effects (from effect-syntax-registry)
2. CPS-transform body via `org.replikativ.partial-cps.ioc/invert`
3. Wrap in Spin
4. Return result

### With pattern

**Local dependency**: `../pattern`

Used for pattern matching in various places (combinators, etc.).

## Common Patterns

See README.md for full usage examples. Quick reference:

```clojure
;; Create runtime and use binding
(def ctx (ctx/create-execution-context))
(binding [rtc/*execution-context* ctx]
  (def counter (sig/signal 0))
  (def my-spin (spin (let [{:keys [new]} (track counter)] (* 2 new))))
  @my-spin)  ; => 0

;; Fork runtime (O(1) with copy-on-write)
(def ctx-fork (ctx/fork-context ctx))

;; Access runtime state via protocols
(rtc/get-state [:signals sig-id])
(rtc/swap-state! [:signals sig-id] update-fn)
```

## Testing Strategy

**From laufzeit/ reference**:

1. **Test spin lifecycle**: Creation, execution, caching, cleanup
2. **Test dependency tracking**: Graph consistency, observer registration
3. **Test topological ordering**: Glitch-free updates
4. **Test signal updates**: Delta tracking, dual perspective
5. **Test effect system**: Custom effects, dispatch, error handling
6. **Test fork-safety**: Runtime forking, isolation
7. **Test executors**: Immediate, thread pool, event loop
8. **Test error propagation**: Cascading errors, recovery

**Use property-based testing** (test.check) for:
- Graph consistency invariants
- Delta tracking correctness
- Topological sort properties

### Cross-Platform Test Pattern (CLJ/CLJS)

**IMPORTANT**: When writing tests that need to work in both CLJ and CLJS, use the `async/done` pattern from `test-helpers.cljc`. **DO NOT** use blocking `@spin` (deref) in cross-platform tests - it only works on JVM.

**Required imports**:
```clojure
(:require #?(:clj [clojure.test :refer [deftest is testing]]
             :cljs [cljs.test :refer-macros [deftest is testing]])
          [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
          [org.replikativ.spindel.spin.cps :refer [spin]])
```

**Test pattern**:
```clojure
(deftest test-my-feature
  (testing "Feature works correctly"
    (async done                           ; done callback introduced by macro
      (with-ctx [_ctx]                    ; binds *execution-context* and *execution-context*
        (let [my-spin (spin (+ 1 2))]
          (run-spin! my-spin
                     (fn [result]         ; success callback
                       (is (= 3 result))
                       (done))            ; MUST call done!
                     (fn [error]          ; error callback
                       (is false (str "error: " error))
                       (done))))))))      ; MUST call done on all paths!
```

**Key rules**:
1. **Always use `async done`** - creates async test block, introduces `done` callback
2. **Always use `with-ctx`** - sets up runtime bindings for spin execution
3. **Always use `run-spin!`** - executes spin with callbacks and triggers event draining
4. **Always call `done`** - on EVERY code path (success, error, nested callbacks)
5. **Never use `@spin`** - blocking deref doesn't work in CLJS

**For JVM-only tests** (signals, blocking operations):
- Wrap entire test in `#?(:clj ...)` reader conditional
- Can use `@spin` deref since it blocks until complete
- Use `simple/drain-events!` for synchronous event processing

**Example reference**: See `test/is/simm/spindel/cross_platform_test.cljc` and `test/is/simm/spindel/runtime_impls_test.cljc`.

## Key Files to Reference

**For architecture understanding**:
- [CODEBASE_ANALYSIS.md](CODEBASE_ANALYSIS.md) - Comprehensive analysis
- [FORKING_DESIGN.md](FORKING_DESIGN.md) - Runtime forking and cross-fork deduplication design
- [CODE_DEDUPLICATION_DESIGN.md](CODE_DEDUPLICATION_DESIGN.md) - Content-addressed code caching and JIT compilation
- [UNISON_COMPARISON.md](UNISON_COMPARISON.md) - Comparison with Unison language runtime
- [laufzeit/CLAUDE.md](laufzeit/CLAUDE.md) - Previous implementation guidance
- [laufzeit/DESIGN.md](laufzeit/DESIGN.md) - Design rationale

**For implementation**:
- [src/is/simm/spindel/spin/core.cljc](src/is/simm/spindel/spin/core.cljc) - Spin
- [src/is/simm/spindel/runtime/protocols.cljc](src/is/simm/spindel/runtime/protocols.cljc) - Protocol definitions
- [src/is/simm/spindel/runtime/impl/atoms.cljc](src/is/simm/spindel/runtime/impl/atoms.cljc) - Reference implementation

## Important Design Decisions

- **Latest Wins Strategy**: When spins can't keep up with signal updates, only the latest snapshot is computed
- **Lazy by Default**: Spins don't execute until dereferenced
- **No Spin Abortion**: Let running spins complete, then recompute with latest
- **Delta Lifecycle**: Keep deltas for one generation (cleared on next update)
- **Automatic Caching**: Every spin is cached by default (incrementality by default)

## Debugging Tips

### Logging

Spindel uses [Trove](https://github.com/taoensso/trove) via `org.replikativ.spindel.log`.

```clojure
(require '[org.replikativ.spindel.log :as log])

(log/debug! {:id ::my-event :msg "Debug info" :data {:x 1}})
(log/info!  {:id ::startup :msg "Started"})
(log/error! {:id ::failure :msg "Failed" :error e})

;; Configure level (default: :info on JVM, nil on CLJS)
(log/configure! {:min-level :trace})
```

**Test logging**: Suppressed by default. Enable via:
```bash
SPINDEL_TEST_LOG=true clj -M:test
# Or from REPL: (tc/enable-test-logging!)
```

**Important**: `log!` macros require compile-time map literals.

### Inspect Runtime State

```clojure
(rtc/get-state [:graph])              ; Dependency graph
(rtc/get-state [:signals sig-id])     ; Signal state
(rtc/get-state [:spin-outputs spin-id]) ; Spin cache
(rtc/graph-ordered-observers sig-id)  ; Topological order
```

### Diagnose Hanging Tests

```bash
jstack $(pgrep -f "clojure.main" | head -1) | grep -A 20 "main\|pool-"
```

Look for: main thread blocked on `Object.wait()`, pool threads in `WAITING`, lock contention.

## Next Steps for Implementation

1. ~~**Write comprehensive test suite**~~ ✅ Done (337 CLJ / 149 CLJS tests)

2. **Create benchmarks**
   - Compare with Missionary
   - Measure overhead of caching
   - Measure fork performance
   - Test with real-world workloads

3. ~~**Test ClojureScript compatibility**~~ ✅ Done
   - Tests run in CLJS via shadow-cljs
   - Event loop executor working
   - Dynamic binding conveyance across async boundaries

4. **Implement missing combinators**
   - Complete race, timeout, sleep
   - Add retry, delay, etc.

5. **Document public API**
   - User-facing guide
   - API reference
   - Tutorial examples

6. **Content-addressed caching**
   - Cross-fork computation deduplication
   - JIT compilation support

## Contact Points in Code

When implementing specific features, start at these entry points:

- **Spin creation**: [src/is/simm/spindel/spin/cps.cljc](src/is/simm/spindel/spin/cps.cljc) `spin` macro
- **Signal creation**: [src/is/simm/spindel/state/signal.cljc](src/is/simm/spindel/state/signal.cljc) `signal` macro
- **Runtime creation**: [src/is/simm/spindel/runtime/context.cljc](src/is/simm/spindel/runtime/context.cljc) `create-execution-context`
- **Runtime forking**: [src/is/simm/spindel/runtime/context.cljc](src/is/simm/spindel/runtime/context.cljc) `snapshot-context`, `restore-snapshot`, `fork-context`
- **Effect registration**: [src/is/simm/spindel/effects/core.cljc](src/is/simm/spindel/effects/core.cljc) `register-effect-by-symbol!`
- **Dependency tracking**: [src/is/simm/spindel/runtime/impl/atoms.cljc](src/is/simm/spindel/runtime/impl/atoms.cljc) `record-deps!`
- **Topological sort**: [src/is/simm/spindel/runtime/impl/atoms.cljc](src/is/simm/spindel/runtime/impl/atoms.cljc) `ordered-observers`
- **Deltaable collections**: [src/is/simm/spindel/incremental/deltaable.cljc](src/is/simm/spindel/incremental/deltaable.cljc) `deltaable-vector`, `deltaable-map`, `deltaable-set`
- **Async sequences**: [src/is/simm/spindel/sequence/core.cljc](src/is/simm/spindel/sequence/core.cljc) `gen-aseq`, `yield`, `anext`
- **Pub/sub mult**: [src/is/simm/spindel/pubsub/mult.cljc](src/is/simm/spindel/pubsub/mult.cljc) `mult`, `tap`, `untap`
- **Pub/sub routing**: [src/is/simm/spindel/pubsub/pub.cljc](src/is/simm/spindel/pubsub/pub.cljc) `pub`, `sub`, `unsub`
- **Buffers**: [src/is/simm/spindel/pubsub/buffer.cljc](src/is/simm/spindel/pubsub/buffer.cljc) `fixed-buffer`, `dropping-buffer`, `sliding-buffer`
