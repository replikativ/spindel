# CLAUDE.md

> **Audience**: contributors and AI assistants making changes to
> Spindel. User docs live in [README.md](README.md) and
> [docs/](docs/) — `docs/concepts.md` for the mental model,
> `docs/engine.md` for the architectural deep-dive,
> `docs/scheduling.md` for the runtime dispatch model.
>
> This file is the contributor playbook: the rules that aren't worth
> putting in user docs but that will trip you (or an agent working
> on the engine) the first time. Read top-to-bottom before your
> first non-trivial change.

## Status

Beta. JVM: 772 tests / 2606 assertions; CLJS: 363 tests / 1374
assertions. Public API may evolve before 1.0.

For the architectural overview see
[`docs/engine.md`](docs/engine.md). For runtime dispatch / events /
executor / GC, see [`docs/scheduling.md`](docs/scheduling.md). For
the typed delta algebra, see [`docs/incremental.md`](docs/incremental.md).

---

## The Four CRITICAL Rules

These are the gotchas that have actually bitten people. Internalize
them; an agent that doesn't will produce subtly broken code that
passes type-check, sometimes passes a single test run, and fails
under load or in CLJS.

### Rule 1 — `(await x)` / `(track x)` inside spin bodies; never `@x`

Inside `(spin …)` bodies:

| Operation | Spin / Deferred | Signal |
|-----------|-----------------|--------|
| Correct   | `(await x)`     | `(track x)` |
| Wrong     | `@x`            | `@x` |

Outside spin bodies (REPL, tests), `@x` is fine.

**Why**: `@` (deref) blocks the calling thread. Inside a CPS-
transformed body that breaks the continuation chain — the spin
macro only inserts breakpoints at *registered effect* call sites,
which `await` / `track` are and `@` is not. On CLJS `@spin` simply
throws.

```clojure
;; ❌ blocks thread, breaks CPS, hangs on CLJS
(spin (let [result @some-spin] (process result)))

;; ✅ CPS-transformed
(spin (let [result (await some-spin)] (process result)))

;; ✅ track returns an Interval — read it with iv/get-new
(spin (let [iv (track some-signal)] (* 2 (iv/get-new iv))))
```

### Rule 2 — Effects don't survive into closures

The `spin` macro only CPS-transforms code it sees *lexically*.
Functions passed to `map` / `filter` / `reduce` and lazy-sequence
generators (`for`, `doseq`) hide their bodies from the macro, so
effects inside them stay as raw fn calls and blow up at runtime.

```clojure
;; ❌ closure body invisible to the macro
(spin (map #(await (fetch %)) items))

;; ❌ lazy-seq hides the awaits
(spin (for [x data] (await (fetch-spin x))))

;; ✅ explicit loop/recur — body is lexical
(spin
  (loop [remaining items, results []]
    (if (empty? remaining)
      results
      (recur (rest remaining)
             (conj results (await (fetch (first remaining))))))))

;; ✅ nest a (spin …) per item, splice with `parallel` for concurrency.
;;    Each (spin …) is its own CPS scope — the await inside the
;;    closure is lexical *within* that inner spin.
(require '[org.replikativ.spindel.spin.combinators :refer [parallel]])
(spin
  (let [child-spins (map (fn [x] (spin (await (fetch x)))) items)]
    (await (apply parallel child-spins))))
```

Same limitation as core.async's `go`. Three structural workarounds:
`loop`/`recur` for sequential effects, nested `(spin …)` per item
for concurrent, or async-sequence primitives in
`spindel.seq.{core,combinators}` for streaming. **No** automatic
`map-spins` / `filter-spins` exists — don't invent it.

### Rule 3 — Runtime access via protocols only; never the `:state` field

```clojure
;; ❌ direct field access — breaks across backend implementations
(get-in @(:state runtime) [:nodes spin-id :result])

;; ✅ protocol method via the runtime
(rtp/get-state runtime [:nodes spin-id :result])

;; ✅ facade that uses *execution-context* dynamically
(ec/get-state [:nodes spin-id :result])
```

The runtime protocols (`PState`, `PGraph`, `PSpinLifecycle`,
`PContinuation`, `PEngine`, `PScheduler`, `PDepsTracking`) are the
public engine API. Fields on the `ExecutionContext` record (the
`:backend`, `:state-atom`, etc.) are implementation details that
change shape between AtomBackend, OverlayBackend, and
ImmutableBackend.

Facade fns in `engine/core.cljc` (`ec/get-state`, `ec/swap-state!`,
`ec/cas-state!`) read `*execution-context*` dynamically — use these
when you have a current ctx; use the protocol forms when you
already have an explicit ctx in hand.

### Rule 4 — `pcps-async/*in-trampoline* false` when resuming from external threads

When invoking a continuation from outside the spin's own CPS
trampoline (a future / virtual-thread callback, a JS setTimeout, an
HTTP response, an event-listener), bind `*in-trampoline* false`
first:

```clojure
;; ✅ async callback from external thread
(future
  (try (Thread/sleep 10)
       (binding [pcps-async/*in-trampoline* false]
         (cont/resume resolve value))
       (catch Throwable t
         (binding [pcps-async/*in-trampoline* false]
           (cont/resume reject t)))))

;; ❌ inside CPS code — already in a trampoline; double-binding
;;    would establish a nested one and cap stack growth uselessly
(defn wrapped-cps-fn [r]
  (fn [_r _e]
    (cont/resume r nil)
    spin-core/incomplete))
```

| Re-entry context | Bind `*in-trampoline*`? | Why |
|------------------|------------------------|-----|
| `future` / thread pool | `false` ✅ | Different thread = new dispatch frame |
| `setTimeout` / timer | `false` ✅ | Event loop re-entry |
| HTTP / DB / file I/O callback | `false` ✅ | Outside CPS scope |
| Already inside a spin body | leave default | Outer trampoline pumps Thunks |

For the architectural explanation (Thunk, trampoline loop, the
breakpoint table), see [`docs/engine.md` § CPS Mechanics &
the Trampoline](docs/engine.md#3-cps-mechanics--the-trampoline).

---

## Cross-Platform Test Pattern (CLJ + CLJS)

For tests that must run in both JVM and CLJS, use the `async` /
`with-ctx` / `run-spin!` pattern from `test-helpers.cljc`. **Never**
use `@spin` (blocking deref) — it only works on JVM and throws on
CLJS.

```clojure
(ns my-test
  (:require #?(:clj  [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
            [org.replikativ.spindel.spin.cps :refer [spin]]))

(deftest test-my-feature
  (testing "feature"
    (async done                            ; done callback introduced by macro
      (with-ctx [_ctx]                     ; sets up *execution-context*
        (let [my-spin (spin (+ 1 2))]
          (run-spin! my-spin
            (fn [result]                   ; success callback
              (is (= 3 result))
              (done))                      ; MUST call done!
            (fn [error]                    ; error callback
              (is false (str "error: " error))
              (done))))))))                ; done on every code path
```

Rules:
1. `async done` creates the async test block; the macro introduces
   `done` as a callback.
2. `with-ctx` binds `*execution-context*` for the body.
3. `run-spin!` invokes the spin with the success/error callbacks and
   triggers event-draining.
4. **Always call `done`** on every code path — success, error,
   nested branches. Missing `done` makes the test hang.

For JVM-only tests that need blocking semantics (signals, drain
awaits), wrap the whole `deftest` in `#?(:clj …)` and use `@spin`
freely.

---

## Logging

Source files use `replikativ.logging` directly. No project-local
wrapper.

```clojure
(require '[replikativ.logging :as log])

(log/debug :engine/my-event {:spin-id sid :note "..."})
(log/info  :engine/startup  {})
(log/error :engine/failure  {:error e})
(log/trace :engine/enqueue-event {:event ev})
```

Shape: `(log/<level> <event-keyword> <data-map>)`. The event keyword
is a stable identifier you can filter on. `engine/impl/simple.cljc`
has hundreds of canonical call sites if you need patterns.

---

## Debugging Tips

### Inspect runtime state

```clojure
(ec/get-state [:nodes signal-or-spin-id])  ; signal / spin node
(ec/get-state [:continuations spin-id])    ; live conts
(ec/get-state [:subscriptions])            ; reverse index event-key → conts
(ec/get-state [:spin-tracking spin-id])    ; transient deps accumulator
(ec/get-state [:engine/pending])           ; FIFO event queue
(ec/get-state [:engine/current-batch])     ; non-nil during signal-change
```

### Diagnose hanging tests (JVM)

```bash
jstack $(pgrep -f "clojure.main" | head -1) | grep -A 20 "main\|pool-"
```

Look for: main thread blocked on `Object.wait()` (a promise that'll
never deliver), pool threads in `WAITING` (drain-signal stuck), or
lock contention on `engine/draining?`.

### Stress test for flakes

```bash
# Run a single namespace 50× to a file, then inspect — avoids slow
# inline grep and lost output.
for i in $(seq 1 50); do
  echo "=== RUN $i ===" && clj -X:test :nses '[my.ns]' 2>&1
done > /tmp/stress.log 2>&1
grep -E "FAIL|ERROR" /tmp/stress.log
```

---

## REPL Workflow

```bash
clj -M:repl    # nREPL + cider-nrepl, port written to .nrepl-port
```

External tooling (`clj-nrepl-eval`, `cider`, your editor) connects
to the port file. From the REPL, the standard tight loop:

1. Write a function in source.
2. `(require '[my.ns :reload])` and eval.
3. Test against a fresh context.
4. Fix, re-eval, repeat.
5. Once working, write a test to pin it.

```clojure
;; Fresh ctx in the REPL
(require '[org.replikativ.spindel.engine.context :as ctx]
         '[org.replikativ.spindel.engine.core :as ec])
(def ctx (ctx/create-execution-context))

;; Drive a spin
(binding [ec/*execution-context* ctx]
  (def s (spin (+ 1 2)))
  @s)  ; => 3
```

After a structural change (deps, macro), restart the REPL — `:reload`
won't pick up registered effects or macro-expansion-time data.

---

## Development Approach

### Keep it lean
- Don't create compatibility layers or "make it work somehow".
  When refactoring is needed: analyze, propose options, decide, then
  implement cleanly.
- Don't add error handling, fallbacks, or validation for scenarios
  that can't happen.
- Don't write docs unless explicitly asked. The `docs/` tree is the
  user-facing source; this file is for contributors.
- Three similar lines of code are better than a premature
  abstraction.

### Ask vs proceed

**Ask** when: multiple refactoring approaches exist; a design
decision affects architecture; requirements unclear; trade-offs
between approaches.

**Proceed** when: obvious bug fix; clear implementation following
established patterns; writing tests for existing functionality.

### Commits
Prefer one commit per logical change. Conventional-commits style
(`feat:` / `fix:` / `chore:` / `docs:` / `refactor:`). Don't `--amend`
existing commits unless explicitly asked; create a NEW commit.

---

## Directory Structure

```
src/org/replikativ/spindel/
├── core.cljc                    # Main API (re-exports)
├── atom.cljc                    # Fork-safe runtime atoms
├── signal.cljc                  # Signal creation/manipulation
├── semaphore.cljc               # Semaphore primitive
├── yggdrasil.cljc               # Tree structure utilities
├── spin/
│   ├── core.cljc                # Spin deftype, protocols, lifecycle
│   ├── cps.cljc                 # spin macro + CPS transformation
│   ├── combinators.cljc         # parallel, race, sleep, timeout, …
│   ├── supervisor.cljc          # Spin supervision trees
│   └── sync.cljc                # Deferred + Mailbox synchronization
├── effects/
│   ├── await.cljc               # await effect (spins + deferred + mailbox)
│   ├── track.cljc               # track effect (signals)
│   └── yield.cljc               # yield effect (sequence generation)
├── engine/
│   ├── core.cljc                # Facades + *execution-context*
│   ├── protocols.cljc           # 7 runtime protocols
│   ├── context.cljc             # ExecutionContext, fork/snapshot/serialize
│   ├── executor.cljc            # PExecutor (virtual / ForkJoin / EventLoop)
│   ├── state_backend.cljc       # Atom + Overlay + Immutable backends
│   ├── addressing.cljc          # Deterministic addressing; per-spin chain-head
│   ├── bindings.cljc            # Dynamic binding capture across async boundaries
│   ├── hash.cljc                # Fast murmur3 hashing
│   ├── nodes.cljc               # SpinNode, SignalNode records
│   ├── effects.cljc             # PEffectHandler protocol + registration
│   └── impl/
│       ├── simple.cljc          # Core event-loop / drain implementation
│       ├── graph.cljc           # Dependency graph operations
│       └── delayed.cljc         # Delayed evaluation utilities
├── seq/
│   ├── core.cljc                # gen-aseq, yield, PAsyncSeq
│   └── combinators.cljc         # first, rest, reduce, into, sequence,
│                                #   eduction, from-coll, iterate-async
├── pubsub/
│   ├── buffer.cljc              # fixed / sliding / dropping
│   ├── mult.cljc                # fan-out to multiple taps
│   ├── pub.cljc                 # topic-based routing
│   └── partitioned.cljc         # tap-partition / tap-all
├── incremental/
│   ├── algebra.cljc             # PDeltaAlgebra protocol + laws
│   ├── interval.cljc            # Interval (:old, :new, :deltas)
│   ├── sequence_algebra.cljc    # SequenceAlgebra (ifor-each output)
│   ├── map_algebra.cljc         # MapAlgebra
│   ├── permutation.cljc         # Permutation utilities
│   ├── combinators.cljc         # imap, ifilter, islice, ireduce, izip
│   ├── typed_combinators.cljc   # Typed-algebra-emitting combinators
│   ├── deltaable.cljc           # Delta-tracking collections (re-exports)
│   └── deltaable/
│       ├── protocols.cljc       # PDeltaable, PWrap/UnwrapDeltaable
│       ├── vector.cljc, map.cljc, set.cljc
├── dom/
│   ├── core.cljc                # vnode, text-node, fragment helpers
│   ├── elements.cljc            # el/div, el/span, … macros
│   ├── foreach.cljc             # ifor-each — typed seq-diff producer
│   ├── discharge.cljc           # PDischarge + apply-seq-diff! consumer
│   ├── browser.cljs             # Browser DOM discharge (CLJS only)
│   ├── render.cljc              # render-spin!, render-effect, mounting
│   ├── foreign.cljc             # foreign-node escape hatch
│   ├── fragment.cljc            # Keyed fragments
│   ├── addressing.cljc          # DOM-scope keyed addressing
│   ├── cache.cljc               # Per-element cache for refs / attrs
│   ├── router.cljc, ssr.cljc
├── distributed/                 # Optional: kabel-based distributed scopes
├── inference/                   # Optional: probabilistic programming
└── sci/                         # Optional: SCI sandbox integration
```

67 .cljc + 1 .cljs source files (cross-platform .cljc by default;
only `dom/browser.cljs` is CLJS-only because it touches the DOM).

---

## Terminology

- **Spin** — cached reactive computation (not "async task").
- **Signal** — mutable reactive source (standard FRP term).
- **await** — suspend and track a spin / deferred dependency; CPS
  breakpoint.
- **track** — read a signal with `Interval` perspective; CPS
  breakpoint.
- **yield** — emit from an async-sequence generator; CPS breakpoint.
- **Deltaable** — collection that records mutations as deltas.
- **Runtime / ExecutionContext** — the value that holds every
  signal / spin / continuation; forkable.
- **Overlay Backend** — copy-on-write state backend used by
  `fork-context`.
- **Snapshot** — immutable copy of a runtime's state.
- **Mult** — fan-out primitive (one source → multiple consumers).
- **Pub** — topic-based routing primitive.
- **Trampoline** — loop that pumps `Thunk` values to keep CPS-
  transformed `loop`/`recur` stack-safe.
- **gen-aseq** — generator macro for lazy async sequences.

---

## Contact Points in Code

Start here when changing a specific feature:

| Feature | File | Symbol |
|---------|------|--------|
| `spin` macro | `spin/cps.cljc` | `spin` (CLJ macro), `build-cps-fn` |
| Spin deref / completion | `spin/core.cljc` | `deref-spin`, `cache-result!` |
| Signal creation + mutation | `signal.cljc` | `signal`, `swap-signal*-explicit` |
| Runtime creation | `engine/context.cljc` | `create-execution-context` |
| Fork / snapshot / serialize | `engine/context.cljc` | `fork-context`, `snapshot-context`, `restore-snapshot`, `serialize-context` |
| Effect registration | `engine/effects.cljc` | `register-effect-by-symbol!` |
| Dependency tracking | `engine/impl/simple.cljc` | `deps-track-signal!`, `record-deps!` |
| Topological sort | `engine/impl/graph.cljc` | `ordered-observers` |
| Drain / event loop | `engine/impl/simple.cljc` | `drain-events!`, `process-event!` |
| Executors | `engine/executor.cljc` | `default-executor`, `execute-after!` |
| Deltaable collections | `incremental/deltaable.cljc` | `deltaable-vector` etc. |
| Typed delta algebra | `incremental/algebra.cljc` | `PDeltaAlgebra`, `empty-deltas` |
| Async sequences | `seq/core.cljc` | `gen-aseq`, `yield`, `anext` |
| Pub/sub mult | `pubsub/mult.cljc` | `mult`, `tap`, `untap` |
| DOM rendering | `dom/render.cljc` + `dom/discharge.cljc` | `render-spin!`, `apply-seq-diff!` |
