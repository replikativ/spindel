# Getting Started

This guide walks you through building a working reactive system with spindel, from setup to signal-driven re-execution.

## Dependencies

Add spindel to your `deps.edn`:

```clojure
{:deps {org.clojure/clojure    {:mvn/version "1.12.0"}
        org.replikativ/spindel {:mvn/version "0.1.0"}}}
```

For ClojureScript, also add:

```clojure
{:deps {org.clojure/clojurescript {:mvn/version "1.11.132"}
        org.replikativ/spindel    {:mvn/version "0.1.0"}}}
```

## Require Namespaces

Spindel provides a convenience namespace that re-exports core APIs:

```clojure
(require '[org.replikativ.spindel.core :as s :refer [spin signal await track]]
         '[org.replikativ.spindel.engine.core :as ec])
```

Or require individual namespaces for full control:

```clojure
(require '[org.replikativ.spindel.engine.context :as ctx]
         '[org.replikativ.spindel.engine.core :as ec]
         '[org.replikativ.spindel.spin.cps :refer [spin]]
         '[org.replikativ.spindel.signal :as sig :refer [signal]]
         '[org.replikativ.spindel.effects.await :refer [await]]
         '[org.replikativ.spindel.effects.track :refer [track]])
```

## Create an Execution Context

Every spindel program starts with an execution context. The context manages state, dependency tracking, and scheduling:

```clojure
(def context (s/create-execution-context))
```

All spindel operations require a bound execution context. Bind it using `binding`:

```clojure
(binding [ec/*execution-context* context]
  ;; spindel operations here
  )
```

## First Signal

Signals are mutable reactive values — like atoms that trigger re-execution when changed:

```clojure
(binding [ec/*execution-context* context]
  (def counter (signal 0)))
```

Signals support the standard atom API:

```clojure
(binding [ec/*execution-context* context]
  @counter          ;; => 0
  (swap! counter inc)
  @counter          ;; => 1
  (reset! counter 0)
  @counter)         ;; => 0
```

## First Spin

Spins are cached reactive computations. Create one with the `spin` macro:

```clojure
(binding [ec/*execution-context* context]
  (def doubled
    (spin
      (let [{:keys [new]} (track counter)]
        (* 2 new)))))
```

Key points:
- `track` reads a signal and registers a reactive dependency
- `track` returns an interval with `:new` (current value), `:old` (previous value), and `:deltas`
- The spin body re-executes automatically when tracked signals change

Deref the spin to get its current value:

```clojure
(binding [ec/*execution-context* context]
  @doubled)  ;; => 0
```

## Signal Updates Drive Re-execution

When you update a signal, all spins that track it are marked dirty and re-execute on next deref:

```clojure
(binding [ec/*execution-context* context]
  (swap! counter inc)   ;; counter = 1
  @doubled              ;; => 2 (re-executed: (* 2 1))

  (swap! counter inc)   ;; counter = 2
  @doubled)             ;; => 4 (re-executed: (* 2 2))
```

Re-execution is **lazy** — spins don't re-execute until their result is needed.

## Spin-to-Spin Dependencies with `await`

Use `await` inside a spin to depend on another spin:

```clojure
(binding [ec/*execution-context* context]
  (def tripled
    (spin
      (let [d (await doubled)]
        (* 3 d)))))

;; Dependency chain: counter -> doubled -> tripled
(binding [ec/*execution-context* context]
  @tripled              ;; => 12 (counter=2, doubled=4, tripled=12)

  (reset! counter 10)
  @tripled)             ;; => 60 (counter=10, doubled=20, tripled=60)
```

## Batching Signal Updates

When updating multiple signals, use `batch` to collect all changes into a single reactive propagation:

```clojure
(binding [ec/*execution-context* context]
  (def x (signal 0))
  (def y (signal 0))

  (def sum
    (spin
      (+ (:new (track x))
         (:new (track y))))))

;; Without batch: each swap! triggers a separate propagation
;; With batch: one propagation after both updates
(binding [ec/*execution-context* context]
  (s/batch
    (swap! x inc)
    (swap! y inc))
  @sum)  ;; => 2
```

## Cleanup

When you're done with a context, stop it to clean up background threads:

```clojure
(s/stop-context! context)
```

For test code or scripts, use `close-context!` to also shut down the executor:

```clojure
(require '[org.replikativ.spindel.engine.context :as ctx])
(ctx/close-context! context)
```

## Common Mistakes

### Using `@` Instead of `await` Inside Spins

```clojure
;; WRONG — blocks the thread, breaks CPS, no dependency tracking
(spin (let [x @some-spin] ...))

;; CORRECT — CPS-transformed, tracks dependency, non-blocking
(spin (let [x (await some-spin)] ...))
```

`@` (deref) is only for use **outside** spins (e.g., at the REPL or in non-reactive code). Inside spins, always use `await` for spins and `track` for signals.

### Using `@` Instead of `track` for Signals

```clojure
;; WRONG — reads value but doesn't register reactive dependency
(spin (let [x @my-signal] ...))

;; CORRECT — registers dependency, spin re-executes on signal change
(spin (let [{:keys [new]} (track my-signal)] ...))
```

### Forgetting to Bind Execution Context

```clojure
;; WRONG — throws "No execution context bound"
@my-spin

;; CORRECT
(binding [ec/*execution-context* context]
  @my-spin)
```

## Complete Example

```clojure
(require '[org.replikativ.spindel.core :as s :refer [spin signal await track]]
         '[org.replikativ.spindel.engine.core :as ec])

;; Setup
(def ctx (s/create-execution-context))

(binding [ec/*execution-context* ctx]
  ;; State
  (def items (signal []))
  (def filter-text (signal ""))

  ;; Derived computation
  (def filtered-items
    (spin
      (let [all   (:new (track items))
            query (:new (track filter-text))]
        (if (empty? query)
          all
          (filterv #(clojure.string/includes? (:name %) query) all)))))

  (def item-count
    (spin
      (count (await filtered-items))))

  ;; Use it
  (swap! items conj {:name "Apple"})
  (swap! items conj {:name "Banana"})
  (swap! items conj {:name "Avocado"})

  (println "All items:" @item-count)        ;; => 3

  (reset! filter-text "A")
  (println "Filtered:" @item-count)         ;; => 2 (Apple, Avocado)

  (reset! filter-text "Av")
  (println "Filtered:" @item-count))        ;; => 1 (Avocado)

;; Cleanup
(s/stop-context! ctx)
```

## Next Steps

- [Concepts](concepts.md) — Understand the mental model
- [Effects](effects.md) — Deep dive into `await`, `track`, and `yield`
- [Combinators](combinators.md) — `parallel`, `race`, `timeout`, and more
- [Incremental](incremental.md) — Delta-tracking collections
- [API Reference](api-reference.md) — Complete function listing
