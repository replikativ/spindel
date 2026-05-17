# Custom Effects

Spindel ships with three built-in CPS effects: `await`, `track`, and
`yield`. Libraries (and applications) can register their own effects so
they participate in spin macro expansion just like the built-ins.

This guide walks through registering a custom effect end-to-end. If you're
just *using* effects, see [Effects](effects.md) instead.

## What an effect is

An effect is a symbol that the `spin` macro recognizes during CPS
transformation. When the macro sees a call to that symbol in a spin body,
it splits the body at that call site, captures the rest as a
*continuation*, and dispatches the call to a handler. The handler is free
to suspend, do async work, and later invoke the continuation with a value.

This is exactly the mechanism `await` uses: `(await some-spin)` doesn't
return immediately; it registers a continuation, lets the rest of the
runtime drive `some-spin` to completion, and only then resumes the
spin body.

## Anatomy of an effect

Every effect has three pieces:

| Piece | Role |
|-------|------|
| **Symbol** | The fully-qualified name users call in spin bodies. |
| **Handler** | A function `(fn [ctx args resolve reject])` that does the work. |
| **Adapter** | Converts the call's argument list into the awaitable map the handler expects. |

The handler receives:

- `ctx` — the current execution context.
- `args` — the arguments after adapter conversion.
- `resolve`, `reject` — continuations to invoke once the effect produces a value (or fails).

The handler may invoke `resolve` synchronously (effect produces a value
immediately) or stash the continuations somewhere and invoke them later
(asynchronous effect — the spin suspends until then).

## Register an effect

Use `engine.effects/register-effect-by-symbol!`:

```clojure
(require '[org.replikativ.spindel.engine.effects :as eff])

(defn my-effect-handler
  "Handle (my-effect x) calls inside spin bodies."
  [ctx {:keys [awaitable]} resolve reject]
  ;; awaitable is whatever (my-effect ...) was called with
  (try
    (resolve (do-the-work awaitable))
    (catch Throwable t (reject t))))

(eff/register-effect-by-symbol!
  'my.lib/my-effect              ; symbol to recognize
  my-effect-handler              ; handler
  'eff/one-arg->awaitable-map)   ; adapter (built-in for single-arg effects)
```

After this call, any spin body that uses `my.lib/my-effect` will have it
treated as a CPS breakpoint:

```clojure
(require '[my.lib :refer [my-effect]])

(s/spin
  (let [v (my-effect 42)]
    (* 2 v)))
```

## Direct vs symbol-call dispatch

Spindel supports two flavors:

- **Symbol-call dispatch** (default): the breakpoint resolves the
  registered handler at runtime via the effect registry. Slightly slower,
  but allows users to override built-ins by registering their symbol
  before the original library loads.
- **Direct dispatch**: the breakpoint hard-codes a function reference at
  macro-expansion time. Faster, no runtime lookup. Use for performance-
  critical effects where overrideability isn't needed.

To register a direct-dispatch effect, pass the direct handler symbol as a
fourth argument:

```clojure
(eff/register-effect-by-symbol!
  'my.lib/my-effect
  my-effect-handler
  'eff/one-arg->awaitable-map
  'my.lib/my-effect-handler-direct)
```

The direct symbol must resolve to a `(fn [arg spin-id ns resolve reject] …)`
function — same shape as the registry-dispatch handler but with the
arguments already destructured.

## Adapters

The adapter normalizes the call form into a map. For single-argument
effects, use the built-in:

```clojure
'eff/one-arg->awaitable-map
;; turns (my-effect x) into {:awaitable x}
```

For multi-argument effects, write a tiny adapter:

```clojure
(defn ^:no-doc two-args->awaitable-map [args]
  (let [[a b] args] {:a a :b b}))

(eff/register-effect-by-symbol!
  'my.lib/two-arg-effect
  my-handler
  'my.lib/two-args->awaitable-map)
```

## Async effects

If your effect needs to wait on an async source — a remote call, a
JavaScript Promise, an external event — store the `resolve` and `reject`
continuations and call them later. Be sure to bind
`pcps-async/*in-trampoline*` to `false` when you do, so the continuation
sees a fresh trampoline:

```clojure
(require '[is.simm.partial-cps.async :as pcps-async])

(defn async-effect-handler [ctx {:keys [awaitable]} resolve reject]
  (some-async-api/run
    awaitable
    (fn [value]
      (binding [pcps-async/*in-trampoline* false]
        (resolve value)))
    (fn [error]
      (binding [pcps-async/*in-trampoline* false]
        (reject error)))))
```

See [`engine.bindings`](../src/org/replikativ/spindel/engine/bindings.cljc)
for how dynamic bindings are captured and restored across the suspension.

### Sync vs async return values

`handle-effect` is a link in the CPS chain — its **return value** is
threaded back through the trampoline. Returning the wrong thing breaks
loops:

| handler shape | return value semantics |
|---|---|
| **Truly async** (registers callbacks, returns immediately) | Return `nil` — propagates harmlessly. |
| **Synchronous-resolve** (calls `resolve` inline before returning) | Return whatever the `resolve` call returned. |

The latter case is the one that bites. When a synchronous-resolve
handler's `resolve` continuation hits a `recur` (inside a `loop` or
`dotimes`), the continuation returns a partial-cps trampoline `Thunk`.
That Thunk has to propagate back up to the enclosing spin-macro
trampoline so it can be bounced; if `handle-effect` swallows it
(returning a hard-coded `nil`), the trampoline chain breaks and the
spin hangs. This was the source of the original
`(loop … (observe …) (recur …))` hang in agent-authored inference
models — fixed by having `engine.effects/async-effect`'s
`handle-effect` propagate `(effect-fn …)` instead of `nil`. The
rule generalises to any custom effect handler: **return the
continuation's value, not a sentinel**.

```clojure
;; CORRECT — propagates Thunks from recur-after-effect
(reify eff/PEffectHandler
  (handle-effect [_ context args resolve reject]
    (effect-fn context args resolve reject)))

;; WRONG — silently breaks loops with effects in them
(reify eff/PEffectHandler
  (handle-effect [_ context args resolve reject]
    (effect-fn context args resolve reject)
    nil))                                       ; ← drops the Thunk
```

## Usage guidance

A few things to keep in mind:

- **Effects are a CPS-transform thing.** They only work when called inside
  a `spin` (or `gen-aseq`) body. Calling an effect from regular Clojure
  code throws — there is no continuation to resolve into.
- **Effects can register dependencies.** `await` calls
  `(deps-track-spin! …)` as a side effect so the spin re-runs when the
  awaited spin's value changes. Custom effects can do the same with
  `engine.core/deps-track-signal!` / `deps-track-spin!`.
- **Effects are global.** Registration is a process-wide side effect. Pick
  fully-qualified symbols and avoid colliding with other libraries.

## See also

- [Effects](effects.md) — using `await`, `track`, `yield`.
- [`engine.effects`](../src/org/replikativ/spindel/engine/effects.cljc) — implementation reference.
- The built-in effects in
  [`effects/await.cljc`](../src/org/replikativ/spindel/effects/await.cljc),
  [`effects/track.cljc`](../src/org/replikativ/spindel/effects/track.cljc),
  and [`effects/yield.cljc`](../src/org/replikativ/spindel/effects/yield.cljc)
  serve as worked examples.
