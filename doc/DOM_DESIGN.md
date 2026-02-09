# Spindel DOM: Delta-Direct Rendering

## Design Document v2.0

### Overview

Spindel DOM is a **delta-direct rendering system** that maps reactive data changes directly to DOM mutations without virtual DOM diffing. It uses **tree-based addressing** and **slot-based caching** to achieve true O(delta) updates.

**Core Principle:** DOM elements are macros that capture source location. Combined with parent address and slot index, each element gets a unique address. The element caches its previous state at that address and produces deltas when children change.

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                           SPIN                                       │
│                                                                       │
│   ┌─────────────────┐        track         ┌──────────────────────┐ │
│   │  Data Signals   │ ───────────────────▶ │   Interval           │ │
│   │  (deltaable)    │                      │ {old new deltas}     │ │
│   └─────────────────┘                      └──────────┬───────────┘ │
│                                                       │              │
│                                                       ▼              │
│   ┌─────────────────────────────────────────────────────────────────┐│
│   │                 DOM Element Macros                              ││
│   │                                                                 ││
│   │  • Capture source location at compile time                     ││
│   │  • Compute tree address: hash(source-loc, parent-addr, slot)   ││
│   │  • Cache children per slot at address                          ││
│   │  • Compare prev vs new, produce deltas                         ││
│   │  • Pass address context to children via ctx bindings           ││
│   │                                                                 ││
│   │  el/div, el/span, el/ul, etc. → MACROS (not functions)        ││
│   │  ifor-each → keyed iteration with KeyedFragment                ││
│   │                                                                 ││
│   └─────────────────────────────────────────────────────────────────┘│
│                              │                                       │
│                              ▼                                       │
│   ┌─────────────────────────────────────────────────────────────────┐│
│   │              VNode with Deltas                                  ││
│   │                                                                 ││
│   │  {:tag :div                                                    ││
│   │   :attrs (deltaable-map {...})                                 ││
│   │   :children [vnode1, vnode2, ...]                              ││
│   │   :deltas [{:delta :add :path [2] :value vnode3}]}             ││
│   │                                                                 ││
│   │  Deltas flow through from signals → combinators → elements     ││
│   └─────────────────────────────────────────────────────────────────┘│
│                              │                                       │
└──────────────────────────────┼───────────────────────────────────────┘
                               │
                               ▼ apply deltas directly
                 ┌─────────────────────────────┐
                 │         Real DOM            │
                 │                             │
                 │  No diffing needed!         │
                 │  Deltas specify exact ops   │
                 └─────────────────────────────┘
```

---

## Tree-Based Addressing

### The Problem with Chain-Based Addressing

The existing `engine/addressing.cljc` uses hash-chain addressing where each address depends on all prior execution. This is wrong for DOM because:

1. **Siblings are independent** - adding a sibling shouldn't affect other siblings
2. **Conditionals appear/disappear** - skipped code shouldn't affect later addresses
3. **Functions are called multiple times** - same source-loc, different data

### Tree-Based Solution

Each element's address is computed from:
```clojure
address = hash([source-loc, parent-addr, slot-index])
```

- **source-loc**: Captured at macro expansion time `{:file :line :column}`
- **parent-addr**: Retrieved from execution context bindings
- **slot-index**: Position in parent's children (0, 1, 2, ...)

This gives **stable addresses**:
- Adding a sibling doesn't change other siblings' addresses
- Conditionals have stable slot positions (nil or value)
- Function calls inherit parent context, making nested elements unique

### Context Bindings for Address Propagation

Use ExecutionContext's `:bindings` map (fork-safe, inherited by child forks):

```clojure
;; In execution context bindings:
{:dom/parent-addr <keyword>      ; Current parent's address
 :dom/current-slot <integer>}    ; Current slot index (set by parent for each child)
```

Parent element sets these before evaluating each child:

```clojure
(defn div* [source-loc attrs child-thunks]
  (let [my-addr (compute-tree-address source-loc
                                       (get-binding :dom/parent-addr)
                                       (get-binding :dom/current-slot))]
    ;; Evaluate children with updated context
    (let [children
          (vec (map-indexed
                 (fn [idx child-thunk]
                   (with-bindings {:dom/parent-addr my-addr
                                   :dom/current-slot idx}
                     (child-thunk)))
                 child-thunks))]
      ;; Compare with cached, produce deltas
      ...)))
```

---

## Slot-Based Caching

Each parent element caches its children **by slot**, not by flattened index:

```clojure
;; Cache structure at parent's address:
{:slot-0 {:type :single :value <vnode-or-nil>}
 :slot-1 {:type :keyed :items {key1 <vnode> key2 <vnode>}}
 :slot-2 {:type :single :value <vnode-or-nil>}}
```

### Slot Types

| Type | Description | Source |
|------|-------------|--------|
| `:nil` | Slot is empty (conditional returned nil) | `(when false ...)` |
| `:single` | Slot contains one vnode | `(el/span "x")` |
| `:keyed` | Slot contains keyed list | `(ifor-each :id f items)` |

### Reconciliation

```clojure
(defn reconcile-slot [prev-slot new-result]
  (let [new-type (classify-result new-result)]
    (case [(:type prev-slot) new-type]
      ;; nil → single: add
      [:nil :single] {:delta :add :value new-result}

      ;; single → nil: remove
      [:single :nil] {:delta :remove :old-value (:value prev-slot)}

      ;; single → single: update if changed
      [:single :single] (when (not= (:value prev-slot) new-result)
                          {:delta :update :old-value (:value prev-slot)
                                          :value new-result})

      ;; keyed → keyed: propagate fragment's internal deltas
      [:keyed :keyed] (let [fragment new-result]
                        (:deltas fragment))

      ;; Type changes: remove old, add new
      ...)))
```

---

## KeyedFragment Type

`ifor-each` returns a `KeyedFragment` to distinguish keyed lists from regular vnodes:

```clojure
(defrecord KeyedFragment [items deltas])

;; ifor-each returns:
(->KeyedFragment
  [<li-1> <li-2> <li-3>]           ; Current vnodes
  [{:delta :add :path [2] :value <li-3>}])  ; Internal deltas
```

The parent element recognizes `KeyedFragment` and:
1. Stores items in `:keyed` slot
2. Propagates internal deltas with adjusted indices
3. Flattens items into final children vector

---

## Element Macros

### Macro Structure

```clojure
#?(:clj
   (defmacro div [& args]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}
           [attrs children] (parse-args args)]
       ;; Wrap each child in a thunk for deferred evaluation
       `(div* ~source-loc ~attrs
              [~@(map (fn [child] `(fn [] ~child)) children)]))))

(defn div* [source-loc attrs child-thunks]
  (let [ctx (ec/*execution-context*)
        parent-addr (get-in ctx [:bindings :dom/parent-addr])
        current-slot (get-in ctx [:bindings :dom/current-slot])
        my-addr (compute-tree-address source-loc parent-addr current-slot)]

    ;; Get previous cache
    (let [prev-cache (ec/get-state [:dom/cache my-addr])

          ;; Evaluate children with context bindings
          new-children
          (vec (map-indexed
                 (fn [idx child-thunk]
                   (let [child-ctx (update ctx :bindings merge
                                           {:dom/parent-addr my-addr
                                            :dom/current-slot idx})]
                     (binding [ec/*execution-context* child-ctx]
                       (child-thunk))))
                 child-thunks))

          ;; Reconcile slots
          {slots :slots deltas :deltas}
          (reconcile-children prev-cache new-children)

          ;; Update cache
          _ (ec/swap-state! [:dom/cache my-addr] (constantly slots))

          ;; Build vnode with deltas
          flat-children (flatten-slots slots)]

      (make-vnode-with-deltas :div attrs flat-children deltas))))
```

### Child Thunks

Children are wrapped in thunks (`(fn [] child-expr)`) so that:
1. Parent controls evaluation order
2. Parent can set context bindings before each child evaluates
3. Slot index is known before child runs

---

## Delta Flow

### From Signal to DOM

```
Signal change
    ↓
track produces Interval{old, new, deltas}
    ↓
ifor-each processes deltas incrementally
    ↓
Returns KeyedFragment{items, deltas}
    ↓
Parent element reconciles slot
    ↓
Produces delta {:delta :add :path [slot-flat-index] :value vnode}
    ↓
VNode carries deltas to discharge
    ↓
Discharge applies delta directly to DOM
```

### Delta Format

```clojure
;; Attribute delta
{:delta :add|:update|:remove
 :path [:class]            ; Attribute name
 :value "new-class"
 :old-value "old-class"}   ; For :update

;; Children delta
{:delta :add|:update|:remove
 :path [2]                 ; Flattened child index
 :value <vnode>
 :old-value <vnode>}       ; For :update/:remove
```

---

## Conditional Rendering

Conditionals work naturally with slot-based caching:

```clojure
(el/div
  (el/span "always")          ;; slot 0: always present
  (when show-modal            ;; slot 1: nil or modal vnode
    (el/div {:class "modal"}
      "Modal content")))
```

| `show-modal` | Slot 0 | Slot 1 | Delta |
|--------------|--------|--------|-------|
| `false` | `<span>` | `nil` | (initial) |
| `true` | `<span>` | `<div.modal>` | `{:delta :add :path [1] ...}` |
| `false` again | `<span>` | `nil` | `{:delta :remove :path [1] ...}` |

The modal has stable address `hash([modal-src-loc], div-addr, 1)` regardless of whether it's rendered.

---

## Function Components

Functions that return DOM work correctly because of address inheritance:

```clojure
(defn user-card [user]
  (el/div {:class "card" :key (:id user)}
    (el/span (:name user))
    (when (:admin user)
      (el/span {:class "badge"} "Admin"))))

;; Usage in ifor-each
(el/ul
  (ifor-each :id user-card users-iv))
```

When `ifor-each` calls `user-card` for each user:
1. It sets `:dom/parent-addr` to ifor-each's address + user's key
2. `el/div` inside `user-card` computes address from that parent
3. Each user gets unique addresses for all nested elements

---

## Implementation Roadmap

### Phase 1: Tree Addressing Module

**File:** `src/is/simm/spindel/dom/addressing.cljc`

```clojure
(ns org.replikativ.spindel.dom.addressing
  "Tree-based addressing for DOM elements.")

(defn compute-tree-address
  "Compute address from source-loc, parent address, and slot index."
  [source-loc parent-addr slot-index]
  ...)

(defn get-parent-addr
  "Get parent address from execution context bindings."
  [ctx]
  (get-in ctx [:bindings :dom/parent-addr]))

(defn get-current-slot
  "Get current slot index from execution context bindings."
  [ctx]
  (get-in ctx [:bindings :dom/current-slot]))

(defn with-child-context
  "Execute thunk with child context (parent-addr and slot set)."
  [ctx parent-addr slot-index thunk]
  ...)
```

### Phase 2: Slot Caching

**File:** `src/is/simm/spindel/dom/cache.cljc`

```clojure
(ns org.replikativ.spindel.dom.cache
  "Slot-based caching for DOM elements.")

(defrecord SlotCache [slots])

(defn get-slot-cache
  "Get cached slots for an address."
  [addr]
  ...)

(defn update-slot-cache!
  "Update cached slots for an address."
  [addr new-slots]
  ...)

(defn reconcile-children
  "Compare prev cache with new children, produce deltas."
  [prev-cache new-children]
  ...)
```

### Phase 3: KeyedFragment

**File:** `src/is/simm/spindel/dom/fragment.cljc`

```clojure
(ns org.replikativ.spindel.dom.fragment
  "KeyedFragment for ifor-each results.")

(defrecord KeyedFragment [items deltas])

(defn keyed-fragment?
  "Check if x is a KeyedFragment."
  [x]
  (instance? KeyedFragment x))

(defn flatten-fragment
  "Flatten KeyedFragment items into vector."
  [fragment]
  (:items fragment))
```

### Phase 4: Element Macros

**File:** `src/is/simm/spindel/dom/elements.cljc` (rewrite)

Convert all element functions to macros:

```clojure
;; Before (function):
(defn div [& args]
  (apply element :div args))

;; After (macro + implementation):
#?(:clj
   (defmacro div [& args]
     (let [source-loc (capture-source-loc &form)]
       `(div* ~source-loc ~@(wrap-children args)))))

(defn div* [source-loc attrs child-thunks]
  ...)
```

### Phase 5: Update ifor-each

**File:** `src/is/simm/spindel/dom/foreach.cljc` (update)

Make `ifor-each` return `KeyedFragment` and set proper addressing context:

```clojure
(defn ifor-each* [source-loc key-fn render-fn source-iv]
  (let [my-addr (compute-tree-address source-loc ...)
        ...]
    ;; For each item, set context with item's key as part of address
    (let [items (map-indexed
                  (fn [idx item]
                    (let [item-key (key-fn item)
                          item-addr (keyed-child-address my-addr item-key)]
                      (with-child-context item-addr 0
                        (render-fn item))))
                  (iv/get-new source-iv))]
      (->KeyedFragment items deltas))))
```

### Phase 6: Update Discharge

**File:** `src/is/simm/spindel/dom/discharge.cljc` (update)

Handle deltas directly instead of diffing:

```clojure
(defn discharge-vnode!
  "Apply vnode's deltas to DOM."
  [discharge vnode]
  (when-let [deltas (:deltas vnode)]
    (let [el (get-element discharge vnode)]
      (doseq [delta deltas]
        (apply-delta! discharge el delta)))))
```

### Phase 7: Remove Old Diffing Code

**Files to modify:**
- `src/is/simm/spindel/dom/render.cljc` - Remove `diff-vdom`, `diff-attrs`, `diff-children`

The render layer becomes simpler: just apply deltas from vnodes.

### Phase 8: Update Tests

**Files:**
- Update `test/is/simm/spindel/dom/core_test.cljc`
- Update `test/is/simm/spindel/dom/render_test.cljc`
- Add `test/is/simm/spindel/dom/addressing_test.cljc`
- Add `test/is/simm/spindel/dom/cache_test.cljc`

---

## Files to Create

| File | Purpose |
|------|---------|
| `dom/addressing.cljc` | Tree-based address computation |
| `dom/cache.cljc` | Slot-based caching |
| `dom/fragment.cljc` | KeyedFragment record |

## Files to Modify

| File | Changes |
|------|---------|
| `dom/elements.cljc` | Convert to macros |
| `dom/foreach.cljc` | Return KeyedFragment, set context |
| `dom/discharge.cljc` | Apply deltas directly |
| `dom/render.cljc` | Remove diffing, simplify |
| `dom/core.cljc` | Add `:deltas` field to vnodes |

## Files to Remove/Deprecate

The following code becomes unnecessary:
- `diff-vdom` in render.cljc
- `diff-attrs` in render.cljc
- `diff-children` in render.cljc
- `collect-nodes-with-deltas` in discharge.cljc (deltas are on vnodes directly)

---

## Example: Complete Flow

```clojure
(def todos (sig/signal [{:id 1 :text "Buy milk" :done false}]))

(el/div {:class "app"}                    ;; addr: A
  (el/h1 "Todos")                         ;; slot 0, addr: hash([h1], A, 0)
  (el/ul                                  ;; slot 1, addr: hash([ul], A, 1)
    (ifor-each :id todo-item todos-iv)))  ;; addr: hash([ifor], ul-addr, 0)

(defn todo-item [todo]
  (el/li {:key (:id todo)}                ;; addr: hash([li], ifor-addr+key, 0)
    (el/span (:text todo))))              ;; slot 0, addr: hash([span], li-addr, 0)
```

**Add todo `{:id 2 :text "Write code"}`:**

1. Signal produces delta `{:delta :add :path [1] :value {...}}`
2. `track` returns Interval with delta
3. `ifor-each` processes delta:
   - Only calls `todo-item` for new item
   - Returns `KeyedFragment{items: [li-1, li-2], deltas: [{:delta :add :path [1] :value li-2}]}`
4. `el/ul` reconciles slot 0:
   - Prev: KeyedFragment with 1 item
   - New: KeyedFragment with 2 items
   - Propagates delta from fragment
5. `el/div` sees slot 1 updated, but the delta is already computed
6. Discharge applies `{:delta :add :path [1] :value li-2}` to ul element

**Result:** Only the new `<li>` is created and inserted. No diffing anywhere.

---

## Migration Notes

### Breaking Changes

1. **Elements are now macros** - Can't pass to higher-order functions directly
   ```clojure
   ;; Won't work:
   (map el/div items)

   ;; Use instead:
   (map (fn [item] (el/div item)) items)
   ;; Or:
   (ifor-each :id (fn [item] (el/div ...)) items-iv)
   ```

2. **Context required** - DOM elements must run within an execution context
   ```clojure
   (binding [ec/*execution-context* ctx]
     (el/div ...))
   ```

3. **ifor-each returns KeyedFragment** - Not a vector of vnodes

### Compatibility

- Browser discharge (`dom/browser.cljs`) - Works unchanged (applies deltas to DOM)
- Mock discharge (`dom/discharge.cljc`) - Works unchanged (logs operations)
- Existing vnodes - Structure unchanged, just adds `:deltas` field

---

## References

- `src/is/simm/spindel/engine/context.cljc` - ExecutionContext with bindings
- `src/is/simm/spindel/engine/addressing.cljc` - Chain-based addressing (for spins)
- `src/is/simm/spindel/incremental/combinators.cljc` - Interval-based combinators
- `src/is/simm/spindel/incremental/interval.cljc` - Interval abstraction
