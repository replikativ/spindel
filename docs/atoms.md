# Fork-Safe Atoms

Spindel provides a runtime-backed atom that is **API-compatible with
`clojure.core/atom`** but stores its state inside the execution context. The
benefit: atoms participate in fork isolation, snapshot/restore, and
serialization just like signals do.

```clojure
(require '[org.replikativ.spindel.core :as s])

(s/with-context ctx
  (let [cache (s/atom [])]
    (swap! cache conj :hello)
    @cache))                                ;; => [:hello]
```

## When to use Spindel atoms vs `clojure.core/atom`

Use `s/atom` whenever the atom needs to:

- be visible to a forked context (and isolated from it on mutation)
- survive a `snapshot-context` / `restore-snapshot` round-trip
- be serialized along with the context
- be cleaned up automatically when the calling code drops its reference

Use `clojure.core/atom` for ephemeral runtime helpers that have nothing to
do with the reactive context — for instance, a one-shot accumulator inside
a private function. Plain Clojure atoms are NOT fork-safe: writes happen
on a single shared cell regardless of which context is bound.

## API

```clojure
(s/atom initial-value)
(s/atom initial-value :meta {…})
```

`s/atom` reads the dynamically bound `*execution-context*` at call time. To
construct an atom for a specific context, use `s/create-atom`:

```clojure
(s/create-atom initial-value :meta {…})
```

The returned object implements `IDeref`, `IAtom`, and `IRef` exactly like
`clojure.core/atom`:

```clojure
@a                          ;; deref current value
(swap! a f & args)          ;; atomic update
(reset! a v)                ;; replace
(add-watch a key callback)  ;; classic watch
(remove-watch a key)
```

## Fork isolation

Each fork sees its own copy of any atom that has been mutated in the fork:

```clojure
(s/with-context root
  (def cache (s/atom #{})))

(swap! cache conj :a)            ;; root: #{:a}

(let [child (s/fork-context root)]
  (s/with-context child
    (swap! cache conj :b)        ;; fork: #{:a :b}
    @cache))                     ;; => #{:a :b}

(s/with-context root
  @cache)                        ;; root: #{:a} — fork's :b is invisible
```

Reads fall through to the parent until the fork mutates the atom; the
mutation triggers the overlay backend's copy-on-write at the entity level.

## Garbage collection

Each atom registers a finalizer (`Cleaner` on the JVM,
`FinalizationRegistry` in browsers that support it) so that when nothing
references the atom value anymore, its `[:atoms id]` entry is dropped from
the runtime state map. You don't have to track lifetimes manually.

In CLJS environments without `FinalizationRegistry` (very old browsers),
the entry persists for the lifetime of the context. Drop the context to
reclaim.

## Watches and forks

A watcher is **side-effecting egress** (notify/publish), so it is stored at the
**fork-local** `[:listeners id]` path and fired synchronously at the swap commit
site. Two consequences:

- A watcher added in a fork only fires for mutations **within that fork**; the
  parent does not see it.
- A fork does **not** inherit the parent's watchers, so a fork's (speculative)
  mutation never fires the parent's watcher — it can't leak fork-private state out
  through the parent's egress. A fork that wants to egress adds its own watcher.

The same `[:listeners id]` mechanism backs `add-watch` on spindel **signals**
(`SignalRef`) too — one fork-correct watch mechanism for both reference types.

Listeners are closures, so they are **dropped on `serialize-context`** (like
continuations); re-establish them by re-adding watches after `restore-snapshot` /
`deserialize-context`.

## Atoms inside spin bodies

Atoms work the same inside spins:

```clojure
(s/with-context ctx
  (let [counter (s/atom 0)
        bumper  (s/spin
                  (let [x (s/await some-spin)]
                    (swap! counter inc)
                    x))]
    @bumper
    @counter))
```

Atoms are **not reactive**: signals are the right primitive when a value
should drive re-execution of dependent spins. Atoms are for non-reactive
state that nevertheless needs fork isolation.

## See also

- [Forking](forking.md) — the broader story of context isolation.
- [Concepts](concepts.md) — signals vs atoms vs spins.
