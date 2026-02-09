# Effects

Effects are the mechanism through which spins interact with the outside world — other spins, signals, and async sequences. The `spin` macro recognizes effect calls as CPS breakpoints, transforming them into non-blocking suspension points.

## Built-in Effects

### `await` — Spin-to-Spin Dependency

`await` suspends the current spin until a child spin, deferred, or mailbox produces a value. It also registers a dependency so the parent re-executes when the child changes.

```clojure
(require '[org.replikativ.spindel.effects.await :refer [await]])

(spin
  (let [x (await child-spin)
        y (await other-spin)]
    (+ x y)))
```

**Supported types:**

| Type | Behavior |
|------|----------|
| Spin | Awaits completion, tracks dependency. Fast path if already cached. |
| Deferred | Suspends until value delivered via `deliver!` |
| Mailbox | Suspends until message posted via `post!` |
| SignalRef | **Error** — use `track` instead |

**Fast path**: If the awaited spin is already completed and cached, `await` returns the cached value immediately without suspending.

**Reactive re-execution**: When an awaited child spin changes (e.g., because one of its tracked signals changed), the parent is marked dirty and re-executes on next deref.

**Cancellation check**: `await` checks if the current spin has been cancelled. If so, it throws `::spin-cancelled` instead of proceeding.

### `track` — Signal-to-Spin Dependency

`track` reads a signal's current value and registers a reactive dependency. The spin re-executes when the signal changes.

```clojure
(require '[org.replikativ.spindel.effects.track :refer [track]])

(spin
  (let [{:keys [new old deltas]} (track my-signal)]
    ;; new: current value
    ;; old: value at previous execution
    ;; deltas: structural changes (for deltaable collections)
    (process new)))
```

**Return value**: An `Interval` with three perspectives:

```clojure
;; Map destructuring
(let [{:keys [new old deltas]} (track sig)] ...)

;; Sequential destructuring
(let [[new-val old-val deltas] (track sig)] ...)

;; Just the current value
(let [val @(track sig)] ...)
```

| Field | Description |
|-------|-------------|
| `:new` | Current signal value |
| `:old` | Value at previous spin execution (nil on first run) |
| `:deltas` | Structural changes since last run (for deltaable collections) |

**Delta format** (for deltaable collections):

```clojure
[{:delta :add    :path [idx-or-key] :value v}
 {:delta :update :path [idx-or-key] :value v :old-value old-v}
 {:delta :remove :path [idx-or-key] :value v}]
```

**Cancellation check**: Like `await`, `track` checks cancellation before proceeding.

### `yield` — Async Sequence Generation

`yield` emits a value in an async sequence generator. Only usable inside `gen-aseq`.

```clojure
(require '[org.replikativ.spindel.seq.core :refer [gen-aseq yield]])

(def numbers
  (gen-aseq
    (yield 1)
    (yield 2)
    (yield 3)))
```

Each `yield` suspends the generator until the consumer requests the next value via `anext`. See [async sequences in Getting Started](getting-started.md) for consumption patterns.

**`yield` outside `gen-aseq`**: Throws an error. The yield handler is only bound inside `gen-aseq` bodies.

## Async Sequences

### `gen-aseq`

Generate a lazy async sequence:

```clojure
(def countdown
  (gen-aseq
    (loop [n 5]
      (when (pos? n)
        (yield n)
        (recur (dec n))))))
```

**Cold semantics**: Each consumer (via `anext`) gets independent execution. Multiple consumers see independent sequences.

**Spin integration**: You can `await` spins inside `gen-aseq`:

```clojure
(def processed
  (gen-aseq
    (loop [n 0]
      (when (< n 3)
        (let [result (await (fetch-data n))]
          (yield (* 2 result))
          (recur (inc n)))))))
```

### `for` — Async Sequence Comprehension

Like `clojure.core/for` but for async sequences, with spindel effect support:

```clojure
(require '[org.replikativ.spindel.seq.core :as seq-core])

(spin
  (let [aseq (seq-core/for [x [1 2 3]
                            :when (odd? x)]
               (await (async-double x)))]
    ;; Consume with anext
    (loop [s aseq acc []]
      (if-let [[v rest] (await (seq-core/anext s))]
        (recur rest (conj acc v))
        acc))))
;; => [2 6]
```

Supports all `for` modifiers: `:let`, `:when`, `:while`, and multiple bindings.

### Consuming Async Sequences

Use `anext` to consume one element at a time:

```clojure
(require '[org.replikativ.spindel.seq.core :as seq-core])

(spin
  ;; anext returns [value rest-seq] or nil (end of sequence)
  (let [[v1 rest1] (await (seq-core/anext my-seq))
        [v2 rest2] (await (seq-core/anext rest1))]
    [v1 v2]))
```

Collect into a vector:

```clojure
(spin
  (await (seq-core/into [] my-seq)))
```

## Synchronization Primitives

### Deferred — One-Shot Value

A deferred is a single-assignment value that multiple spins can await:

```clojure
(require '[org.replikativ.spindel.spin.sync :refer [deferred deliver!]])

(def d (deferred))

;; In a spin — suspends until delivered
(spin
  (let [value (await d)]
    (process value)))

;; From external code (future, callback, etc.)
(deliver! d 42)
```

- **Exactly-once**: Only the first `deliver!` succeeds
- **Multiple readers**: Many spins can await the same deferred
- **Fork-safe**: State stored in the execution context

**Internal vs external delivery**:
- `(d value)` — deliver from within the same execution context (internal)
- `(deliver! d value)` — deliver from external threads (enqueues event, safe)

### Mailbox — Message Queue

A mailbox is a FIFO queue for message passing between spins:

```clojure
(require '[org.replikativ.spindel.spin.sync :refer [mailbox post!]])

(def mbx (mailbox))

;; Consumer spin — blocks until message available
(spin
  (loop []
    (let [msg (await mbx)]
      (process msg)
      (recur))))

;; Producer — post messages
(post! mbx {:type :task :data "work"})
```

- **Multiple messages**: Unlike deferred, accepts many values
- **FIFO order**: Messages delivered in posting order
- **Multiple consumers**: Each message goes to one consumer only
- **Fork-safe**: State stored in the execution context

### Never — Infinite Wait

A spin that never completes, useful with `race` and `timeout`:

```clojure
(require '[org.replikativ.spindel.spin.sync :refer [never]])

;; Wait for either result or cancellation
(spin
  (await (race
    (do-work)
    (never))))  ;; race cancels never when do-work completes
```

## Custom Effects

You can register custom effects that the `spin` macro recognizes as CPS breakpoints.

### Registration

```clojure
(require '[org.replikativ.spindel.engine.effects :as effects])

;; Register a synchronous effect
(effects/register-effect-by-symbol!
  'my.ns/my-effect                          ;; fully-qualified symbol
  (reify effects/PEffectHandler
    (handle-effect [_ context args resolve reject]
      (try
        (let [result (do-something (:value args))]
          (resolve result))
        (catch Exception e
          (reject e)))))
  'my.ns/my-adapter)                        ;; adapter: (fn [args-vec] args-map)
```

The adapter function converts the positional arguments from the call site into a map:

```clojure
(defn my-adapter [args]
  {:value (first args)})
```

### Using Custom Effects

Once registered, use the effect inside spins:

```clojure
(spin
  (let [result (my.ns/my-effect some-value)]
    (process result)))
```

The `spin` macro detects `my.ns/my-effect` as a registered breakpoint and transforms it into a CPS call to your handler.

### Direct Handlers

For performance, you can register a **direct handler** — a function called directly instead of going through protocol dispatch:

```clojure
(effects/register-effect-by-symbol!
  'my.ns/my-effect
  :direct                                    ;; marker, not PEffectHandler
  'my.ns/my-adapter
  'my.ns/my-direct-handler)                  ;; (fn [value spin-id loc resolve reject] ...)
```

Direct handlers receive arguments already adapted, plus spin context. The built-in `await` and `track` use direct handlers for performance.

## See Also

- [Getting Started](getting-started.md) — Basic tutorial
- [Concepts](concepts.md) — CPS transformation explained
- [Combinators](combinators.md) — `parallel`, `race`, `timeout`, and more
- [Incremental](incremental.md) — Delta tracking for `track` results
