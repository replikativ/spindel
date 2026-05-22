# Engine Architecture

This document explains how the Spindel engine works *inside*: the state
it holds, the addressing scheme that gives spins stable identity, the
CPS transformation that makes `spin` bodies pause-and-resume, the
executors and drain loop that decide *when* work runs, the overlay
backend that makes forking O(1), and the memory invariants that hold
across all of it.

It assumes the model from [`concepts.md`](concepts.md) — signals,
spins, `track`/`await`, checkpoints, the drain queue — and does not
re-teach it. For the algebra, flow diagrams, and correctness laws, see
[`engine-formalism.md`](engine-formalism.md).

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
│         (reverse index of the continuation tables for fast event
│          dispatch)
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
    :track-subscriptions
      └── <spin-id> → {<cont-id> → cont-map}
          (comonadic, persistent track continuations)
    :await-conts
      └── <spin-id> → {<cont-id> → cont-map}
          (monadic await continuations)
    :engine/pending          — [event…] FIFO queue
    :engine/draining?        — CAS lock for drain-events!
    :engine/delayed-spins    — sorted-map of timer-keyed spin-ids
    :engine/timer-handles    — {<spin-id> → handle} for cancellation
```

**Two continuation tables, not one.** A *continuation* is the reified
"rest of the body" past a `track` or `await` call. The continuation map
is split into two structures keyed by the comonad/monad distinction:

- `:track-subscriptions[spin-id]` — the **track** continuations, which
  are comonadic and persistent: a track cont watches a signal and
  re-runs the body slice on every change, so it is never reaped at a
  generation boundary.
- `:await-conts[spin-id]` — the **await** continuations, which are
  monadic: they advance a suspended body when an awaited child (or an
  external resource) completes. Some are ephemeral (reaped at the
  generation boundary), some persistent (a reactive child re-completes).

Each continuation still carries a `:kind` (`:track`, `:await-reactive`,
`:await-once`, `:external-await`) and an `:order` — and `:order` is a
single monotone insertion sequence *across both tables*, so the
relative order of a track cont and an await cont in the same body is
well-defined. `add-continuation!` routes a new cont to the right table
by its `:kind`.

The fork-local set is defined in `engine/state_backend.cljc:97-110`:
`#{:track-subscriptions :await-conts :engine/pending :engine/draining?
   :engine/delayed-spins :engine/timer-handles}`.

The split is deliberate. Reactive **graph state** (`:nodes`,
`:subscriptions`, `:spin-tracking`) is shared so a fork inherits its
parent's observer wiring for free — every signal that was tracked by
parent is still tracked by fork until the fork writes to that path.
Reactive **execution state** (the two continuation tables,
`:engine/pending`, `:engine/draining?`) is fork-local so the fork can
drain its own events without contending with the parent's drain.

`:engine/cancelled-tokens` is the one shared path with subtle
fork behavior; see [§8](#8-overlay-backend).

In addition to the backend, an `ExecutionContext` carries five
non-state fields:

| Field | Purpose |
|-------|---------|
| `:fork-id` | Identifies this context. Roots are gensyms; forks include their parent's id. |
| `:executor` | `PExecutor` (virtual-thread pool / ForkJoinPool / EventLoopExecutor / SynchronousExecutor). Shared between root and forks. |
| `:running` | `atom` flag; set to `false` by `stop-context!`. Shared. |
| `:drain-thread` | JVM daemon thread that drains events. Shared with forks. |
| `:drain-signal` | `LinkedBlockingQueue` wake-up channel. Shared with forks. |

The thread-sharing details are in [§4](#4-executors-and-the-drain-loop);
[`forking.md`](forking.md) has the complete fork-resource table.

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
and every continuation snapshots the cursor at suspend as part of its
`:slice-state` map (`{:bindings :chain-head :tracking}`) so the engine
can restore it at resume.

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

## 4. Executors and the Drain Loop

Spindel uses an **event-driven, single-drainer model**: all reactive
work is driven by an event queue. Signal changes, spin completions,
deferred deliveries, mailbox posts, and one-shot spin executions are
enqueued as events and processed by a drain loop. Only one drain runs
at a time per context — that is the ordering guarantee glitch-free
updates rest on.

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

On the JVM a background daemon thread runs the drain loop; on
ClojureScript the JS event loop fills the same role.

### Executors

The executor controls *where* spin code runs — which thread or
scheduling mechanism executes a spin body.

| Executor | When to use |
|----------|-------------|
| Virtual threads (default, JVM 21+) | Production. `virtual-thread-executor` returns a `PoolExecutor` wrapping `Executors/newVirtualThreadPerTaskExecutor` — each task gets a fresh virtual thread; blocking is cheap. |
| `ForkJoinPoolExecutor` (default, JVM < 21) | Production. Work-stealing pool; uses `managedBlock` to create compensating threads when workers block on a `CountDownLatch`, preventing deadlock during parallel observer dispatch. |
| `SynchronousExecutor` | Tests and simulation. Executes on the calling thread immediately; deterministic. `execute-after!` ignores the delay (time is controlled via `advance-time!`). |
| `EventLoopExecutor` (ClojureScript) | The only CLJS executor. Schedules work via `setTimeout 0`, yielding to the browser/Node.js event loop between tasks. |

The default executor is selected automatically:

```clojure
(create-execution-context)                 ; default-executor
(create-execution-context :executor (fork-join-executor :parallelism 4))
(create-execution-context :executor (synchronous-executor))
```

All executors capture the relevant dynamic bindings at submission
time and restore them inside the task — this is what makes the
reactive context available on worker threads without explicit
passing. JVM uses `capture-targeted-bindings` (the four `bindings.cljc`
vars plus `ec/*execution-context*`, 5 vars) and restores via
`with-bindings`. CLJS uses `bindings/capture-bindings` (the same four
vars) and `bindings/restore-bindings`; `*execution-context*` follows
naturally because the CLJS executor body runs in the same JS
event-loop step.

**Delayed execution.** Both JVM executors delegate `execute-after!` to
a **shared module-level** `ScheduledThreadPoolExecutor`: one daemon
thread named `laufzeit-delay`, defined once via `defonce` in
`engine/executor.cljc`. After the delay fires it calls back into the
owning executor's `execute!` to run the spin-fn on the regular work
pool. CLJS uses `js/setTimeout` directly. `comb/sleep`, `comb/timeout`,
`comb/debounce`, and `comb/throttle` all route through `execute-after!`.

### The drain thread

On the JVM, each root execution context owns a **background daemon
drain thread**. It wakes instantly when new work arrives and returns
to a zero-CPU wait when idle:

```
while @running:
    drain-signal.poll(1s)     ; blocks until signaled or 1s safety timeout
    if ctx still alive:
        drain-events!(ctx)
```

Wakeup is via a `LinkedBlockingQueue` (`drain-signal`). Anything that
enqueues an event calls `trigger-drain!`, which does `.offer(:drain)`
on the signal **and** also submits a `drain-events!` task to the
executor — so the wake can race a pool worker. The 1-second poll is a
safety net only; in practice the thread is woken immediately.

The drain thread holds a `WeakReference` to the context so that an
abandoned context becomes GC-eligible and the registered `Cleaner`
can stop the thread.

Forked contexts do not start their own drain threads. They share the
parent's `drain-thread`, `drain-signal`, `drain-active`, `running`,
and `executor` (all copied at fork construction in
`engine/context.cljc`). The fork-local pieces are only
`:engine/pending` and `:engine/draining?`, which live in the fork's
overlay so the fork's events don't intermix with the parent's. A
fork's `trigger-drain!` therefore both wakes the parent's drain-signal
*and* submits a fork-tagged `drain-events!` to the executor — whichever
entry point runs first claims the fork's draining lock and processes
the fork's queue. The two never block each other's queue progress.
See [`forking.md`](forking.md) for the full fork-resource table.

### The drain lock

`drain-events!` uses a CAS on `:engine/draining?` to ensure only one
drain session runs at a time:

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

The per-event try/catch is critical: without it, one bad event would
abort the whole drain session and strand every other queued event
until the next signal.

Multiple threads may call `trigger-drain!` simultaneously — they all
submit drain tasks to the executor, but only one acquires the lock.
The others see the lock taken, return zero, and let the active drainer
process everything.

The **re-trigger** at step 6 handles the inevitable race window:

```
Thread A dequeues last event
                              Thread B enqueues new event
Thread A releases lock
Thread A checks :pending → non-empty → re-triggers
```

Without the re-trigger, the new event would sit unprocessed until the
next wakeup (up to 1 second).

### Event types

| Event | When enqueued | What drain does |
|-------|--------------|-----------------|
| `:signal-change` | `swap!` / `reset!` on a signal | Marks dependent spins dirty, resumes track continuations, processes batch completions |
| `:spin-completion` | Spin body finishes | Resumes `await` continuations in parent spins |
| `:spin-execution` | `deref` on an uncached spin | Claims execution slot, runs spin body on executor |
| `:deferred-delivery` | `deliver!` on a `Deferred` | Delivers value and inline-resumes waiting continuations |
| `:mailbox-post` | `post!` on a `Mailbox` | Delivers message and inline-resumes the first waiter |

## 5. Glitch-Free Signal Propagation

Spindel prevents **glitches** — the situation where a spin observes a
half-updated reactive graph. Consider:

```clojure
(def price (signal 100))
(def tax   (spin (let [{:keys [new]} (track price)] (* new 0.2))))
(def total (spin (+ (await tax) (let [{:keys [new]} (track price)] new))))
```

If `price` changes to 200 and `total` re-runs before `tax` does, it
sees `tax=20` (stale) and `price=200` (fresh) — a glitch. Spindel
prevents this with a **single-queue topological-dispatch** model.

### Topological observer dispatch

When a `:signal-change` event is processed, the engine:

0. Creates a fresh `Batch` record at `:engine/current-batch` carrying
   the signal-id, a monotonic `:generation` counter, a `:processed`
   atom of completed spin-ids, and a `:resumed-conts` atom of
   `[parent-id child-id generation]` triples — used to dedupe
   `:spin-completion` await-cont resumes within this batch.
1. Calls **`clear-all-await-continuations!`** — clears every ephemeral
   await continuation across all spins at the generation boundary.
   Without this, an `await` registered against a *previous* version of
   the signal would fire in this cycle alongside the new one,
   producing duplicate work.
2. Computes the observer set in **topological order** over the live
   observer graph (dependents always after dependencies). The graph is
   `signal.observers` — eagerly maintained: every `(track sig)` and
   `(await child)` registers the spin as an observer of its dep at the
   moment of the call, *not* at body-completion time (see
   [§7](#7-dependency-tracking-and-the-graph)).
3. Filters out observers that are *descendants* of other observers in
   this batch (a descendant will be naturally re-resumed by its
   ancestor's completion event, so dispatching it directly here would
   cause duplicate work).
4. Escalates each remaining observer to its root await-ancestor
   (`find-root-await-ancestor`) — the spin that actually needs to
   resume in this batch. Suspended descendants on `await` chains
   anchor at the right level.
5. Resumes each observer's `track` continuation with the fresh signal
   value. Observers with `>1` entry are dispatched in parallel on the
   ForkJoinPool (JVM), using `CountDownLatch` + `managedBlock` to wait
   for all of them. CLJS always dispatches sequentially. The discharge
   side still runs serially per spin — the parallelism is between
   *independent* observers, not within one render.

### Cascade events

While observer bodies execute, they may produce more events:
`:spin-completion` when a body resolves, `:signal-change` if the body
itself swaps a signal, etc. These all flow through the **single**
`:engine/pending` queue and are drained naturally by the outer drain
loop after the current event finishes. There is no separate "Phase 2"
queue and no blocking wait — the unified subscription model collapsed
those into one FIFO. The drain logic lives in `engine/impl/simple.cljc`
(`drain-events!`, `process-event!`).

The descendant-filtering + ancestor-escalation step preserves the
no-glitch guarantee without a per-batch barrier: within one
`:signal-change` dispatch all directly-affected observers resume
against the fresh signal value, and downstream completions propagate
via the same drain in FIFO order — no spin ever sees a
partially-updated graph.

### Dynamically-discovered dependencies

Topological dispatch orders the graph *as it exists when the signal
changes*. But a spin re-tracks its dependencies on every run (see
[§7](#7-dependency-tracking-and-the-graph)), so a conditional branch
can establish a brand-new edge that only appears *after* the spin
re-runs:

```clojure
(spin (if (= 42 (:new (track x)))
        (await k)   ;; edge to `k` exists only when x = 42
        0))
```

A topological sort built before the spin re-runs cannot order `k`
ahead of this spin — that edge did not exist yet. Correctness in this
case does not come from the sort; it comes from `await` being
demand-driven.

`await-spin` (`effects/await.cljc`) takes the **fast path** — return
the child's cached result — only when the child has a cached result,
is **not dirty**, and either we are not inside a `:signal-change`
batch *or* the child was already processed in this batch (`:processed`
set). Otherwise it takes the **slow path**: re-run the child's body,
which re-reads the child's own `track` / `await` dependencies
recursively; the awaiting spin suspends on a continuation and resumes
with the freshly-computed value.

Two independent guards keep this robust mid-propagation:

- **Dirty flag** — `mark-dirty!` BFS-marks the changed signal's
  transitive observers dirty, so awaiting any of them refuses the fast
  path.
- **Batch `:processed` set** — a spin newly pulled into the graph by a
  conditional `await` was never marked dirty, but it is also not in
  `:processed`, so the fast path is refused and the child is re-run
  anyway.

So a dependency chain — including edges discovered *during* this
propagation — is always walked in the true data-flow order of the
current computation. The topological sort is a scheduling optimization
that avoids redundant re-runs for the common static graph; it is not
the correctness mechanism for dynamic dependencies. See
`test/org/replikativ/spindel/continuation_glitch_test.clj` and
[`concepts.md`](concepts.md#5-the-drain-queue--how-a-change-actually-travels).

## 6. Lifecycle of a `swap! signal`

This section walks one concrete trace from a `swap!` call to the DOM
patch landing, threading together the pieces above.

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
3. **Drain wake.** `trigger-drain!` does `.offer drain-signal :drain`
   AND submits a `drain-events!` task to the executor — race for
   whoever grabs the lock first ([§4](#4-executors-and-the-drain-loop)).
4. **Drain begins.** A drain thread / pool worker enters
   `drain-events!`, CASes `:engine/draining? false → true`, dequeues
   the `:signal-change` event.
5. **Batch starts.** `process-event!` creates `:engine/current-batch`
   with a fresh generation counter, clears all ephemeral await
   continuations (the generation-boundary sweep), and computes the
   ordered observer set for `<counter-id>` via topological sort over
   `signal.observers`.
6. **Resume `doubled`.** The engine finds `<doubled>`'s earliest
   `track` continuation in `:track-subscriptions`, then resumes it via
   `resume-body!` in `:track` mode: it restores the continuation's
   `:slice-state` — seeding `[:addressing :chain-heads <doubled>]` from
   `:slice-state :chain-head` and `[:spin-tracking <doubled>]` from
   `:slice-state :tracking` — and calls the continuation's `:resolve-fn`
   with the fresh `Interval` describing `counter`'s update.
7. **CPS body resumes.** Inside the trampoline established at step 6,
   the body slice runs from the `track` breakpoint forward.
   `iv/get-new` extracts the new value (`1`), the body computes
   `(* 2 1) = 2`, and the body's outer `resolve` callback fires.
8. **Commit + completion event.** The outer resolve calls
   `cache-result!` (writes `{:variant :ok :payload 2}` into
   `[:nodes <doubled> :result]`), then `record-deps!`
   ([§7](#7-dependency-tracking-and-the-graph)), then enqueues
   `:spin-completion` for `<doubled>`.
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
11. **Drain ends.** Queue empty; CAS `:engine/draining? true → false`;
    if `:engine/pending` is non-empty (race window), the finally
    re-triggers another drain.

If `counter` had multiple direct observers, step 5 would dispatch
them in topological order, in parallel on JVM via
`ForkJoinPool/managedBlock` and a `CountDownLatch`.

## 7. Dependency Tracking and the Graph

Spindel builds its dependency graph automatically at runtime, on a
**unified-subscription** model: observer registration happens *eagerly*
at the moment the body calls `track` or `await`, not deferred to body
completion.

During spin execution:

- `(track signal)` calls `ec/deps-track-signal!` which does two things
  atomically:
  1. Records `signal-id` in the spin's transient
     `[:spin-tracking spin-id :signals]` set (the diff baseline for
     this run).
  2. Registers the spin in `signal.observers` immediately, so a
     `swap!` that races the body completion is still seen.
- `(await child)` calls `ec/deps-track-spin!` symmetrically — records
  into `[:spin-tracking spin-id :spins]` and registers the parent in
  `child.observers` right away.

This **eager registration closes the "first-run signal-change gap"**:
under an older lazy model, a signal mutated between the first
`(track sig)` call and the body's resolve would not see the spin as an
observer yet, and the spin would never re-run.

When a spin completes, `record-deps!` runs in the body's resolve
callback and does *not* add observers (they're already there). Its
three responsibilities:

1. **Snapshot** the transient `:spin-tracking[spin-id]` set into
   `spin-node.deps` — the baseline for the *next* run's diff.
2. **Prune** the spin from any signal's / child's observer list that
   was present in the previous run's deps but absent from this one
   (conditional tracking: a `(when … (track sig))` that didn't enter
   the branch this time).
3. **Clear** the transient `:spin-tracking[spin-id]` entry.

All three happen in a single atomic `swap-state!` to keep the dep
snapshot internally consistent.

Observer sets are used both for dirty propagation (a `:signal-change`
event hands its observers to the dispatch loop) and for topological
ordering during signal-change processing. The topological order is
computed fresh on each signal change from the live observer graph —
not cached — so it always reflects the current dependency structure.

### Spin execution flow (deref of a cold spin)

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

The `try-claim-execution!` CAS prevents duplicate execution when
multiple `:spin-execution` events arrive for the same spin (e.g.
concurrent derefs). Only the first succeeds; the rest add their
callbacks to be notified on completion.

## 8. Overlay Backend

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

The local-paths set (`engine/state_backend.cljc:97-110`):

```clojure
#{:track-subscriptions  :await-conts
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

## 9. Memory Invariants & GC

### SpinNode lifecycle flags

A `SpinNode` carries the following status state:

| Field | Type | Meaning |
|-------|------|---------|
| `:completed?` | bool | The body has resolved at least once (cache is non-empty). |
| `:running?` | bool | A body slice is in flight *right now* — including suspended on a track/await/deferred. Cleared only by `cache-result!`. |
| `:status` | `:clean` \| `:dirty` | Marked `:dirty` when a dependency changed since the last cache; the next deref / signal-change will re-run the body. Reset to `:clean` after the re-run. Tested via the `PCacheable` protocol methods `clean?` / `dirty?` rather than direct keyword access. |
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
*prunes* unused observers but doesn't add — see [§7](#7-dependency-tracking-and-the-graph).

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
      full-cleanup-spin!  (remove from :nodes, both continuation
                           tables, :subscriptions, observer lists, etc.)
      recursively let dep spins be eligible too
```

Signal continuations count; spin-completion continuations don't (a
parent awaiting a child holds the child via its `:awaited-spin`
strong reference, so a real-leaf orphan is detectable). This is
what keeps `(let [s (spin (track sig))] (s identity identity))`-style
let-bound reactive code alive even when the user has no remaining
strong reference.

### Context lifecycle

`create-execution-context` starts the drain thread immediately. The
thread is a daemon, so it does not prevent JVM exit if the context is
abandoned.

`stop-context!` shuts down cleanly in four steps:

1. `(reset! running false)` — signals the entry guard and all future
   drain calls to exit.
2. `.offer(:stop)` on `drain-signal` — wakes the drain thread
   immediately.
3. Polls `drain-active` down to 0 with `LockSupport/parkNanos 100000`
   (100µs intervals), bounded by a **5-second outer deadline** — a
   safety valve for a deadlocked spin body. Reaching it means a real
   bug worth investigating; the shutdown returns anyway so the caller
   doesn't hang.
4. `.join(drain-thread 200ms)` — waits for the daemon thread loop to
   actually terminate.

`close-context!` calls `stop-context!` and additionally shuts down the
executor.

**GC-based cleanup.** If a context is abandoned without calling
`stop-context!` (common in tests), the drain thread itself is
registered with the JVM `Cleaner` / CLJS `FinalizationRegistry`
against the `ExecutionContext` object. The Cleaner fires once the
context has no more strong references — calling `(reset! running
false)` and offering `:stop` to `drain-signal`, so the daemon thread
exits. Both `create-execution-context` and `deserialize-context`
register this Cleaner (an earlier `deserialize-context` did not,
leaking one daemon thread per call). This is a safety net only —
explicit `stop-context!` / `close-context!` in your lifecycle code is
the right way.

## Platform Differences (JVM vs ClojureScript)

| Aspect | JVM | ClojureScript |
|--------|-----|---------------|
| Drain thread | Daemon thread, blocks on `LinkedBlockingQueue` | No drain thread; JS event loop |
| Executor | ForkJoinPool / virtual threads | `setTimeout 0` |
| Parallel observers | `CountDownLatch` + `managedBlock` | Always sequential (single-threaded) |
| `await-drain-complete!` | Blocks with `ForkJoinPool.managedBlock` + 100µs `parkNanos` | Returns current idle state, non-blocking |
| `@spin` deref | Blocks until complete | Not supported; use `run-spin!` callbacks |

---

## See Also

- [`concepts.md`](concepts.md) — the conceptual model without the
  implementation
- [`engine-formalism.md`](engine-formalism.md) — the rigorous
  companion: laws, algebra, correctness arguments
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
