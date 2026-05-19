# Engine Architecture

This document explains how the Spindel engine works *inside*: the
state it holds, the addressing scheme that gives spins stable identity,
the CPS transformation that makes `spin` bodies pause-and-resume, the
overlay backend that makes forking O(1), and the memory invariants
that hold across all of it.

It's the companion to [`scheduling.md`](scheduling.md), which covers
*when* work runs (drain thread, event types, executors, topological
dispatch). `scheduling.md` is operational; this doc is architectural.
The two cross-reference each other.

If you're a new user, [`concepts.md`](concepts.md) is the place to
start — it gives the conceptual model without the implementation.

## 1. The Execution Context

An `ExecutionContext` is the runtime — a single Clojure value that
holds the entire state of a reactive system. You can `fork-context`
it, `snapshot-context` it, serialize it, restore it. Inside the value
is a state backend (atom-backed for roots, overlay-backed for forks)
keyed by paths:

```
ExecutionContext
├── :backend  → PStateBackend (AtomBackend or OverlayBackend)
│
├── Shared state (overlay falls through to parent)
│   :nodes
│     ├── <signal-id> → SignalNode {:snapshot :old-snapshot :deltas
│     │                             :deltaable? :observers :generation}
│     └── <spin-id>   → SpinNode   {:result :status :completed? :running?
│                                   :observers :deps :created-by
│                                   :created-spins}
│                                   ;; status is :clean | :dirty
│                                   ;; :orphaned? and :dom-scope are
│                                   ;; ad-hoc assoc'd, not defrecord fields
│   :spin-tracking
│     └── <spin-id> → {:signals #{sig-id…} :spins #{spin-id…}}
│         (transient — accumulates during body run, cleared at completion)
│   :subscriptions
│     └── <event-key> → {<spin-id> → #{cont-id…}}
│         (reverse index of :continuations for fast event dispatch)
│   :atoms
│     └── <atom-id> → {:value :watchers}
│   :pending-callbacks
│     └── <spin-id> → [{:resolve :reject} …]
│         (concurrent derefs waiting for one in-flight spin)
│   :addressing
│     ├── :chain-head        — global pre-binding fallback cursor
│     └── :chain-heads
│         └── <spin-id> → chain-head  (per-spin cursor; §2)
│   :engine/current-batch    — {:signal-id :generation :processed
│                               :resumed-conts} during :signal-change
│   :engine/batch-generation — monotonic generation counter
│   :engine/cancelled-tokens — #{token…} for cont-cancellation gate
│
└── Fork-local state (overlay does NOT fall through)
    :continuations
      └── <spin-id> → {<cont-id> → cont-map}
    :engine/pending          — [event…] FIFO queue
    :engine/draining?        — CAS lock for drain-events!
    :engine/delayed-spins    — sorted-map of timer-keyed spin-ids
    :engine/timer-handles    — {<spin-id> → handle} for cancellation
```

The fork-local set is defined in `engine/state_backend.cljc:97-110`:
`#{:continuations :engine/pending :engine/draining?
   :engine/delayed-spins :engine/timer-handles}`.

The split is deliberate. Reactive **graph state** (`:nodes`,
`:subscriptions`, `:spin-tracking`) is shared so a fork inherits its
parent's observer wiring for free — every signal that was tracked by
parent is still tracked by fork until the fork writes to that path.
Reactive **execution state** (`:continuations`, `:engine/pending`,
`:engine/draining?`) is fork-local so the fork can drain its own
events without contending with the parent's drain.

`:engine/cancelled-tokens` is the one shared path with subtle
fork behavior; see [§5](#5-overlay-backend).

In addition to the backend, an `ExecutionContext` carries five
non-state fields:

| Field | Purpose |
|-------|---------|
| `:fork-id` | Identifies this context. Roots are gensyms; forks include their parent's id. |
| `:executor` | `PExecutor` (virtual-thread pool / ForkJoinPool / EventLoopExecutor / SynchronousExecutor). Shared between root and forks. |
| `:running` | `atom` flag; set to `false` by `stop-context!`. Shared. |
| `:drain-thread` | JVM daemon thread that drains events. Shared with forks. |
| `:drain-signal` | `LinkedBlockingQueue` wake-up channel. Shared with forks. |

See [`scheduling.md` § The Drain Thread](scheduling.md#the-drain-thread)
for the JVM thread-sharing details, and [`forking.md`](forking.md)
for the complete fork-resource table.

## 2. Deterministic Addressing

Every spin has a stable identity derived from its **source location**,
not from object identity. The same `(spin …)` form in the same file
produces the same spin-id every time it expands — across re-runs of
its parent, across forks, across `serialize-context` /
`deserialize-context` round-trips.

This is what makes spin caching possible. When parent re-runs and
calls `(child-fn …)` which contains a `(spin …)` form inside, the
inner `spin` is *not* a new spin — it's the same spin as last time,
its cached result is still valid, no work is duplicated.

### Hash-chain addressing

Spin ids are minted by `addressing/next-address!`. It hashes:

```
new-spin-id = content-hash [source-loc, chain-head-cursor]
chain-head-cursor := new-spin-id   ; advance for the next call
```

`source-loc` is `{:file :line :column}` captured at *macro-expansion
time* (the `&form` metadata). `chain-head-cursor` is the previous
addressed value at the current call site.

The hash chain matters because the same `(spin …)` macro form can
expand in two different lexical contexts (recursive factories, helper
fns called from multiple parents) and still need distinct ids.

```clojure
(defn make-fork-spin [name]
  (spin (* 2 (track parent-counter))))  ; same source-loc

(spin
  (let [a (make-fork-spin :alice)        ; parent-cursor → α → id-α
        b (make-fork-spin :bob)]         ; α            → β → id-β
    [a b]))
```

Calling `make-fork-spin` twice from the same parent body produces
*two distinct ids* because the chain-head advances between calls.

### Per-spin chain-head

The chain-head cursor lives in execution-context state at
`[:addressing :chain-heads spin-id]`, **per spin**, not in a dynamic
var. The engine seeds the slot at body entry (`seed-body-chain-head!`)
and the await-cont map snapshots the cursor at suspend
(`:chain-head-snap`) so the engine can restore it at resume.

Three properties fall out of this design:

- **Stable across re-runs.** The cursor resets to its body-start
  value each time a spin re-runs, so the same body code addresses
  the same nested ids on every invocation. A `(spin …)` inside an
  `ifor-each` render-fn gets a different id per row (because the
  outer chain-head differs per row) but the same id across re-renders
  *of the same row*. Hence stable DOM addresses, no element
  duplication.
- **Fork-safe by inheritance.** `[:addressing :chain-heads spin-id]`
  is on the shared-path set, so a fork inherits the parent's cursor
  for any spin parent already addressed. Fork's writes (when its
  bodies run) go to its overlay; reads of any spin parent already
  ran fall through to parent's state.
- **No dynamic-var leak surface.** The cursor follows `fork-context`
  / `snapshot-context` automatically because it lives in ctx state.
  Earlier designs used a `*chain-head*` dynamic var that didn't
  survive snapshot/restore.

The fallback `[:addressing :chain-head]` (a single global cursor) is
used for top-level addressing at app boot, before any spin context
exists.

## 3. CPS Mechanics & the Trampoline

The `spin` macro turns ordinary Clojure into a **CPS-transformed**
(continuation-passing-style) function. The point is to make `track`
and `await` *suspendable* — when they hit an unresolved dependency,
the body pauses; when the dependency resolves, the body resumes from
exactly that point.

### What `(spin body)` expands to

After the spin macro runs, you have approximately:

```clojure
(let [ctx (current-execution-context)
      spin-id (next-address! ctx "spin" {:file …})]
  (make-spin
    (fn [resolve reject]            ; ← CPS function: 2-arg
      (try
        (if *in-trampoline*
          <cps-body>                ; already in a trampoline, return whatever
          (binding [*in-trampoline* true]
            (loop [r <cps-body>]    ; establish a trampoline
              (if (instance? Thunk r)
                (recur ((.-f r)))
                r))))
        (catch Throwable t (reject t))))
    spin-id))
```

The body is rewritten by `partial-cps/invert` so that every `track`
or `await` call becomes a **breakpoint** — a tail-call-like jump to
an effect handler that takes the rest-of-body slice as a continuation.

When the body resolves a value, it calls `resolve`. When it raises,
it calls `reject`. The runtime cares about that 2-arg shape.

### `Thunk` and the trampoline loop

A `Thunk` is the smallest possible "more work to do" marker:

```clojure
(deftype Thunk [f])    ; one field: a zero-arg fn
```

The trampoline is just:

```clojure
(loop [r <body-expr>]
  (if (instance? Thunk r)
    (recur ((.-f r)))     ; unwrap and call to get the next step
    r))                   ; non-Thunk → done
```

Why is this needed? CPS-transformed `loop`/`recur` produces nested
function calls. A million-iteration `loop` would consume a million
stack frames if every recur ran as a direct call. Instead, `recur`
after a CPS breakpoint returns a `Thunk` carrying the next iteration
as a thunk fn; the trampoline pumps Thunks in a flat loop and the
stack stays constant.

`Thunk` is intentionally minimal: identity check is `instance?` on a
single compiled class. (Keeping it a compiled deftype matters for
the SCI integration — see [`sci-integration.md`](sci-integration.md)
for the identity discussion.)

### `*in-trampoline*` — re-entry signaling

The dynamic var `pcps-async/*in-trampoline*` tells nested CPS code
whether a trampoline is *already* running above them:

- If `*in-trampoline*` is `true`, returning a `Thunk` is fine — the
  outer trampoline will pump it.
- If `*in-trampoline*` is `false`, returning a `Thunk` would lose it
  (nothing's pumping); the code must establish its own trampoline
  before invoking the continuation.

This matters at every **re-entry point** to CPS code from "outside":

- A future / virtual thread firing `(resolve value)` from another
  thread.
- A `js/setTimeout` callback in CLJS.
- A `Deferred`'s pending-callback chain.
- A Mailbox post.
- Cross-spin event delivery (`:spin-completion` from a child).

Each of those sites uses `pcps-async/invoke-continuation`:

```clojure
(defn invoke-continuation [cont-fn & args]
  (let [result (apply cont-fn args)]
    (if (instance? Thunk result)
      (if *in-trampoline*
        result                          ; outer trampoline pumps it
        (binding [*in-trampoline* true] ; establish a fresh trampoline
          (loop [r result]
            (if (instance? Thunk r)
              (recur ((.-f ^Thunk r)))
              r))))
      result)))
```

If you write a custom effect that resumes from an external context
(a thread pool callback, a network response), you bind
`*in-trampoline* false` first so `invoke-continuation` knows to
establish a fresh trampoline. [`custom-effects.md`](custom-effects.md)
has the recipe.

### Breakpoints — how `track` / `await` become CPS jumps

The macro builds a breakpoint table from the effect registry. For
each registered effect symbol (e.g. `track`, `await`, `yield` plus
any libraries register), it inserts a breakpoint definition:

```clojure
;; What (track sig) becomes, roughly:
(letfn [(resolve# [v#]
          (invoke-continuation <rest-of-body-as-cont> v#))
        (reject# [e#]
          (invoke-continuation <reject-cont> e#))]
  (track-handler sig <spin-id> <source-loc> resolve# reject#))
```

The handler receives both a `resolve` and a `reject` continuation —
the rest of the spin body, sliced at the breakpoint, wrapped in
trampoline-aware code. The handler does its work (subscribes to the
signal, returns the `Interval`, or suspends if the signal isn't
ready) and eventually calls one of the continuations.

Two different breakpoint shapes coexist in `spin/cps.cljc`:

- **Direct breakpoint**: known handler symbol called inline. Used
  for the built-in `track`, `await`, `yield` for speed.
- **Symbol-call breakpoint**: dispatches through
  `engine/effects/dispatch-symbol-call` with the call wrapped in a
  cancellation gate. Used for library-registered effects so they get
  cancel-token handling automatically.

The mechanics — what's known at macro expansion time, what runs at
body execution time, how the breakpoints integrate with partial-cps's
`invert` pass — is partial-cps's responsibility; see that repo's
docs and `is.simm.partial-cps.ioc/invert` for the deep treatment.

## 4. Lifecycle of a `swap! signal`

This section walks one concrete trace from a `swap!` call to the
DOM patch landing, threading together the pieces above and the
operational mechanics in [`scheduling.md`](scheduling.md).

Setup:

```clojure
(def counter (signal 0))
(def doubled (spin (* 2 (iv/get-new (track counter)))))
(render-spin! container doubled discharge)   ; mounted, observing
```

You call:

```clojure
(swap! counter inc)   ; from somewhere with *execution-context* bound
```

What happens, in order:

1. **Signal mutation.** `swap-signal*-explicit` updates
   `[:nodes <counter-id>]` atomically: writes the new snapshot,
   moves the previous value to `:old-snapshot`, captures any
   collected `:deltas`, bumps `:generation`.
2. **Event enqueue.** `(ec/enqueue-event! {:type :signal-change :id
   <counter-id>})` lands on `:engine/pending` (fork-local FIFO).
3. **Drain wake.** `trigger-drain!` does
   `.offer drain-signal :drain` AND submits a `drain-events!` task
   to the executor — race for whoever grabs the lock first
   (see [`scheduling.md` § The Drain Thread](scheduling.md#the-drain-thread)).
4. **Drain begins.** A drain thread / pool worker enters
   `drain-events!`, CASes `:engine/draining? false → true`, dequeues
   the `:signal-change` event.
5. **Batch starts.** `process-event!` creates `:engine/current-batch`
   with a fresh generation counter, clears all ephemeral await
   continuations (the generation-boundary sweep), and computes the
   ordered observer set for `<counter-id>` via topological sort over
   `signal.observers`.
6. **Resume `doubled`.** The engine finds `<doubled>`'s earliest
   `track` continuation in `:continuations`, seeds
   `[:addressing :chain-heads <doubled>]` from
   `cont.chain-head-snap`, restores `[:spin-tracking <doubled>]`
   from `cont.tracking-snap`, and calls `cont.resolve-fn` with the
   fresh `Interval` describing `counter`'s update.
7. **CPS body resumes.** Inside the trampoline established at
   step 6, the body slice runs from the `track` breakpoint forward.
   `iv/get-new` extracts the new value (`1`), the body computes
   `(* 2 1) = 2`, and the body's outer `resolve` callback fires.
8. **Commit + completion event.** The outer resolve calls
   `cache-result!` (writes `{:variant :ok :payload 2}` into
   `[:nodes <doubled> :result]`), then `record-deps!`
   ([`scheduling.md` § Dependency Tracking](scheduling.md#dependency-tracking-and-the-graph)),
   then enqueues `:spin-completion` for `<doubled>`.
9. **Discharge.** Because `render-spin!` registered its render-effect
   as `doubled`'s resolve callback wrapper, the render-effect fires
   synchronously *inside* step 8's resolve: the new vnode tree flows
   through the discharge layer, which applies the typed
   `SequenceAlgebra` / `MapAlgebra` deltas to the DOM (see
   [`incremental.md`](incremental.md)).
10. **Cascade.** The `:spin-completion` event in `:engine/pending`
    is processed next by the same drain loop. Any parent spin that
    `(await <doubled>)`'d gets its await continuation resumed (which
    may produce more cascade events — same FIFO, same drain).
11. **Drain ends.** Queue empty; CAS `:engine/draining? true →
    false`; if `:engine/pending` is non-empty (race window), the
    finally re-triggers another drain.

The trace touches:

- §1 state: `:nodes` (signal + spin update), `:engine/pending`
  (FIFO), `:engine/current-batch` (batch metadata), `:continuations`
  (cont resume), `:subscriptions` (find which spins await
  `:spin/complete`).
- §2 addressing: `:chain-heads` restoration at resume.
- §3 CPS: outer trampoline established once at body start; the
  resume `invoke-continuation` reuses it if `*in-trampoline*` is
  already true.
- [`scheduling.md` § Topological observer dispatch](scheduling.md#topological-observer-dispatch):
  the dispatch order, descendant filtering, ancestor escalation.

If `counter` had multiple direct observers, step 5 would dispatch
them in topological order, in parallel on JVM via
`ForkJoinPool/managedBlock` and a `CountDownLatch`. The discharge
side still runs serially per spin — the parallelism is between
*independent* observers, not within one render.

## 5. Overlay Backend

When you call `(fork-context root)` you get an `OverlayBackend`
wrapping an `overlay-atom` plus a pointer to the parent's backend.
All state lookups walk this two-level structure:

```
                              fork backend
                            ┌─────────────┐
read [:nodes 42]            │  overlay    │
       │                    │  (atom)     │
       ├──── path in local-paths? ──── yes → return overlay-only value
       │                    │             │   (no parent fallthrough)
       │                    └─────────────┘
       │
       └──── otherwise ────→ overlay[:nodes 42] ──── found → return overlay value
                                    │
                                    │ ::not-found
                                    ▼
                              parent backend
                            ┌─────────────┐
                            │  AtomBackend│ ─── return parent's value
                            │  or another │     (or nil)
                            │  Overlay    │
                            └─────────────┘
```

The local-paths set
(`engine/state_backend.cljc:97-110`):

```clojure
#{:continuations
  :engine/pending  :engine/draining?
  :engine/delayed-spins  :engine/timer-handles}
```

These never fall back to parent. Everything else does. That's the
mechanism behind the shared-vs-fork-local table in §1.

### Writes

A write at any path lands in the fork's overlay-atom. The parent's
state is never touched.

```
swap! [:nodes 42 :result] new-result
       │
       └──── overlay[:nodes 42] :       did the overlay already have this node?
              ├── no  → overlay[:nodes 42] :result = new-result
              │           (creates a new map at :nodes 42 in overlay;
              │            parent's :nodes 42 is unchanged)
              └── yes → overlay[:nodes 42] :result = new-result
                          (update in place)
```

This is why `fork-context` is O(1). No copying happens. The first
read of a path that's not in overlay traverses to parent. The first
write at a path puts a value in overlay. Subsequent reads of that
path see the overlay's value.

### Shared-path semantics for `:engine/cancelled-tokens`

A subtle variant: `:engine/cancelled-tokens` is a **shared path**
that holds a set. Both root and forks can read it (fall-through), and
both can write to it (the write goes to the fork's overlay, so a
fork's cancellation doesn't leak back to parent). The
`cancellable-external-pair` machinery in `effects/await.cljc` reads
this set through the cont's *current* execution context — so a
re-entry from fork's drain sees fork's cancellations, and from
parent's drain sees parent's. See the long comment above
`cancellable-external-pair` in `effects/await.cljc` for the design.

### Snapshot vs fork

`snapshot-context` is similar in spirit but uses `ImmutableBackend`:
the entire backend is a frozen value, no overlay, no parent pointer,
no pending queue (snapshots don't drain). `restore-snapshot`
constructs a new `AtomBackend` from a snapshot's state, starting a
fresh drain thread. Use snapshot when you need full isolation;
fork when you want cheap divergence with shared graph state.

## 6. Memory Invariants & GC

### SpinNode lifecycle flags

A `SpinNode` carries the following status state:

| Field | Type | Meaning |
|-------|------|---------|
| `:completed?` | bool | The body has resolved at least once (cache is non-empty). |
| `:running?` | bool | A body slice is in flight *right now* — including suspended on a track/await/deferred. Cleared only by `cache-result!`. |
| `:status` | `:clean` \| `:dirty` | Marked `:dirty` when a dependency changed since the last cache; the next deref / signal-change will re-execute. Reset to `:clean` after re-execution. Tested via the `PCacheable` protocol methods `clean?` / `dirty?` rather than direct keyword access. |
| `:orphaned?` | bool, ad-hoc assoc'd | Optional. The Spin Java/JS object has been GC'd but live continuations exist; preserve the node so signal events keep firing. Not a `defrecord` field — added by `try-gc-cleanup-spin!` via `assoc`. |

Two surprises worth knowing:

- **`:running?` does NOT clear on suspension.** A spin awaiting a
  Deferred for 10 seconds is `:running? true` the whole time, even
  though no thread is computing. This lets `await-drain-complete!`
  and `@spin` accurately detect "work still in flight" without a
  Phase 2 wait.
- **`:status :dirty` is independent of `:completed?`.** A spin can
  be completed (cache populated) AND dirty (cache stale because a
  tracked signal changed). Deref then re-runs the body to refresh.

### Eager observer registration (recap)

Every `(track sig)` immediately registers the spin in
`signal.observers`. Every `(await child)` immediately registers the
parent in `child.observers`. Body completion via `record-deps!`
*prunes* unused observers but doesn't add — see
[`scheduling.md` § Dependency Tracking](scheduling.md#dependency-tracking-and-the-graph).

### GC safety net: `Spin` object collected mid-life

A `Spin` Java/JS object can become unreachable from user code while
the engine still has live continuations for that spin. Example:

```clojure
;; let-bound spin — leaves user scope after this expression
(let [my-spin (spin (track sig))]
  (my-spin identity identity))
;; my-spin is GC-eligible HERE, but the engine still has its
;; track-continuation registered against sig.
```

The continuation closes over the CPS body slice and the resolve atom
— not over the `Spin` object itself. So functionally the spin can
still react to signal changes. But the JVM `Cleaner` (or CLJS
`FinalizationRegistry`) fires on the now-unreachable `Spin` and asks
the engine to clean up.

`try-gc-cleanup-spin!` therefore checks whether any **live signal
continuations** exist for the spin id before tearing down:

```
Cleaner fires on Spin <spin-id>
       │
       ▼
try-gc-cleanup-spin!:
  - if there are still observers OR live signal-continuations:
      mark :orphaned? true, keep node and continuations
  - else:
      full-cleanup-spin!  (remove from :nodes, :continuations,
                           :subscriptions, observer lists, etc.)
      recursively let dep spins be eligible too
```

Signal continuations count; spin-completion continuations don't (a
parent awaiting a child holds the child via its `:awaited-spin`
strong reference, so a real-leaf orphan is detectable). This is
what keeps `(let [s (spin (track sig))] (s identity identity))`-style
let-bound reactive code alive even when the user has no remaining
strong reference.

### Cleaner-context lifecycle

The drain thread itself is registered with the JVM `Cleaner` /
CLJS `FinalizationRegistry` against the `ExecutionContext` object.
If user code abandons the context without calling `stop-context!`
(common in tests), the Cleaner fires on context GC and calls
`(reset! running false)` + offers `:stop` to `drain-signal`, so
the daemon thread exits.

Both `create-execution-context` and `deserialize-context` register
this Cleaner. Earlier `deserialize-context` did not, leaking one
daemon thread per call.

This is a safety net only — explicit `stop-context!` / `close-context!`
in your lifecycle code is the right way. See
[`scheduling.md` § Context Lifecycle](scheduling.md#context-lifecycle)
for the explicit-shutdown sequence.

---

## See Also

- [`concepts.md`](concepts.md) — the conceptual model without the
  implementation
- [`scheduling.md`](scheduling.md) — drain thread, event types,
  executors, topological dispatch
- [`forking.md`](forking.md) — `fork-context` / `snapshot-context`
  / `restore-snapshot` API and the full fork-resource table
- [`incremental.md`](incremental.md) — typed delta algebra, deltaable
  collections, `Interval` three-state contract
- [`custom-effects.md`](custom-effects.md) — writing your own
  effects, `*in-trampoline*` re-entry rules
- [`sci-integration.md`](sci-integration.md) — Thunk identity and
  the SCI sandbox
- partial-cps repo — `invert`, `Thunk`, the underlying CPS
  transformation
