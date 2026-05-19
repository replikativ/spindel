# Spindel Examples

Five browser demos that exercise spindel's incremental DOM rendering
end-to-end. Each demo has an HTML page in `public/` and a ClojureScript
namespace in `src/examples/`.

| Demo | What it shows |
| --- | --- |
| `todo_demo` | TODO MVC. Add / remove / toggle / filter items with `d/deltaable-vector` + `ifilter`; per-row updates flow as `:update` deltas through `ifor-each`. |
| `block_editor_demo` | Hierarchical block editor. `:focused` / `:collapsed` / `:hidden` live on each block, so every interaction emits per-block `:update` deltas. `:ref` registers the live DOM element of each row and a focus-spin focuses the currently focused block reactively. |
| `infinite_scroll_demo` | 10 000-item virtual list with `islice`. Scroll → only the entering/exiting items hit the DOM; the visible window is one `:seq-diff` per change. |
| `tiptap_demo` | TipTap (ProseMirror) integration via `foreign-node`. Spindel manages the parent, TipTap owns the editor subtree; signal feedback loops keep a live HTML preview in sync. |
| `versioned_editor_demo` | Branching document with diff overlay. The canonical end-to-end demo of the typed delta algebra and the cleanest in-repo style reference. |

The `examples.shared.logging-discharge` namespace wraps the real
`browser/make-dom-discharge` and logs every `PDischarge` call into an
atom; the todo and infinite-scroll demos use it to show DOM ops in a
side panel.

## Running

```bash
cd examples
npm install
npx shadow-cljs watch examples
# open http://localhost:8080/
```

`shadow-cljs.edn` defines both a combined `:examples` build and one
per-demo build for standalone use.

## House style

These conventions hold across the demos. Pick them up before adding new
examples; reach for `versioned_editor_demo` as the reference when in
doubt.

### 1. One top-level spin per page

The page's reactive root is a single `(spin …)` that takes signal
*refs* as args and returns the full vnode tree. Helper renderers are
plain functions of values, not spins. `block_editor` adds a second
side-effect-only spin (`make-focus-spin`) for focus management;
`infinite_scroll` and `todo` add a `make-stats-spin` for the
diagnostic panel. These auxiliary spins have no vnode output —
they're kicked once with `(focus-spin identity identity)` and
self-schedule from there via `track`.

### 2. Read intervals with `iv/get-new`

`track` returns an `Interval`. Read its `:new` value via
`(iv/get-new iv)`. The `Interval` deftype also implements `IDeref`
(`@iv`) and `ILookup` (`(:new iv)`); they're all equivalent, but
`iv/get-new` is the searchable, namespaced spelling that the demos
converged on.

```clojure
(spin
  (let [items (iv/get-new (track items-sig))
        mode  (iv/get-new (track filter-sig))]
    (render items mode)))
```

### 3. `ifor-each` must be the sole child of its container

`apply-seq-diff!` (`dom/discharge.cljc:418-497`) walks
`(range size-after)` and passes those indices straight into
`insert-child!` / `move-child!` against the parent — they're
interpreted as positions in `parent.childNodes`. With any sibling
DOM nodes preceding the fragment the indices skew by the sibling
count and the diff corrupts on update. Until the discharge takes
an `:offset`, always wrap `ifor-each` in its own `<div>` / `<ul>`
and put headings, footers, separators *outside* that wrapper.

```clojure
(el/div {:class "page"}
  (el/h2 "Title")                 ; sibling of .list-wrapper, NOT of fragment
  (el/div {:class "list-wrapper"} ; fragment's only parent
    (ifor-each :id items render-row)))
```

### 4. `:ref` for DOM identity

Reach for `:ref` when you need a stable handle to a real DOM element
that survives reconciliation (focus, IME state, third-party JS owning
the subtree). `:ref` fires once on mount with the element and once on
unmount with `nil`; it does NOT re-fire when the vnode's attributes
change (in-place reconciliation reuses the element).

`block_editor` uses `:ref` to populate a `block-id → el` registry that
its focus-spin reads. `tiptap_demo` uses `foreign-node`, which sets
`:ref` for you to drive `:on-mount` / `:on-unmount`.

### 5. `binding [ec/*execution-context* runtime]` for outside-spin writes

Event handlers and other callbacks invoked outside any spin body need
to bind the execution context before mutating a signal:

```clojure
(.addEventListener btn "click"
  (fn [_]
    (binding [ec/*execution-context* runtime]
      (swap! todos-signal conj new-todo))))
```

`ec/make-handler` does this binding for you and is the canonical
wrapper for DOM event listeners that need to drive reactive state.
Inline vnode attrs (`:on-click`, `:on-input`) handled via
`browser/set-attribute!` already run in the right context — no
explicit `binding` needed there.

### 6. No `js/setTimeout` delays as patches

If a panel has to re-render when state changes, drive it reactively —
either via a `track` inside a spin (signals) or `add-watch` +
`queueMicrotask` (plain atoms whose updates are too fast to track
per-mutation, like the discharge's op-log). `js/setTimeout` is not a
synchronisation primitive; if a callback fires "before the DOM is
ready", you have an ordering bug to fix, not a delay to insert.

## Anti-patterns to avoid

- **`@` deref inside spin bodies on a `Spin` / `Deferred`.** It blocks
  the thread and bypasses CPS. Use `await` for spins and `track` for
  signals.
- **Higher-order functions / `for` / `map` with effects in the
  closure.** The spin macro CPS-transforms its *lexical* body; effects
  inside a function passed to `map` aren't visible. Use `loop`/`recur`
  for sequential work, or nest a `(spin …)` per item and splice the
  resulting Spins into `(apply parallel child-spins)` for concurrent
  work. See `CLAUDE.md` "CPS Transformation Limitations" for the
  detailed treatment.
- **Imperative DOM access via `querySelector`** when `:ref` would
  give you the element for free.
- **Plain-vector signals where `d/deltaable-vector` is appropriate.**
  Without deltaable wrapping, `reset!` is the only mutation path and
  the signal emits `:deltas nil` — combinators downstream fall back
  to full recompute on the source.
