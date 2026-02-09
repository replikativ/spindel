# Interval-Based Incremental Programming Model

## Integration Design for Signals, Combinators, and DOM

This document outlines how the interval abstraction unifies signals, incremental combinators, and DOM rendering into a cohesive programming model.

---

## Current State (Before Integration)

### Three Separate Abstractions

1. **SignalDeltaView** (`signal.cljc`)
   - Returned by `track` effect
   - Has `:new`, `:old`, `:delta` keys
   - Wraps snapshot values from signals

2. **Deltaable Collections** (`incremental/deltaable.cljc`)
   - Track structural changes via deltas
   - Operations like `conj`, `assoc` produce `:add`, `:update`, `:remove` deltas
   - Must call `d/get-deltas` to extract deltas

3. **VDom Diffing** (`dom/render.cljc`)
   - Compares old/new vdom trees
   - Produces synthetic deltas for discharge
   - Separate diff-attrs/diff-children logic

### The Problem

```clojure
;; Current approach - manual unpacking everywhere
(spin
  (let [{:keys [new old delta]} (track todos)  ; SignalDeltaView
        ;; 'new' is a deltaable collection
        deltas (d/get-deltas new)               ; Must extract deltas separately
        source-iv (iv/as-interval new)]         ; Must coerce to interval
    ;; Now we can use interval combinators
    (->> source-iv
         (ifilter :active)
         (imap :hours)
         (ireduce + 0))))
```

---

## Proposed Unified Model

### Core Insight: Everything is an Interval

The interval abstraction `(old, new, deltas)` can unify all three:

```
Signal Change      →  Interval
Deltaable Collection  →  Interval
VDom Update       →  Interval
```

### The Programming Model

```clojure
;; GOAL: This should "just work" with automatic delta propagation
(spin
  (let [todos-iv (track todos)]  ; Returns Interval directly!
    (->> todos-iv
         (ifilter :active)       ; Processes deltas incrementally
         (imap :hours)           ; Propagates deltas
         (ireduce + 0))))        ; O(delta) sum
```

---

## Integration Points

### 1. Track Effect Returns Interval

**Change**: `track` returns an `Interval` instead of `SignalDeltaView`.

```clojure
;; BEFORE (current)
(defn- get-track-value [signal-ref]
  (let [detailed (sig/get-signal-detailed signal-ref)
        value (sig/get-new detailed)]
    (if (satisfies? sig/PSignalDeltaView value)
      value
      detailed)))  ; Returns SignalDeltaView

;; AFTER (proposed)
(defn- get-track-value [signal-ref]
  (let [node (sig/get-signal-state signal-ref)
        old-snapshot (:old-snapshot node)
        new-snapshot (:snapshot node)
        deltas (:deltas node)]
    (iv/->Interval old-snapshot new-snapshot deltas)))  ; Returns Interval!
```

**Benefits**:
- No manual coercion with `iv/as-interval`
- Combinators work directly on tracked values
- Delta chain preserved from signal through entire pipeline

### 2. SignalNode Already Has What We Need

Looking at `engine/nodes.cljc`:

```clojure
(defrecord SignalNode [snapshot          ; Current value
                       old-snapshot      ; Previous value  ← We have old!
                       deltas            ; Structural changes ← We have deltas!
                       deltaable?        ; Can track deltas?
                       observers])       ; Set of observer node IDs
```

The signal system already tracks `old-snapshot` and `deltas` - we just need to expose them as an Interval!

### 3. Interval-Based DOM Rendering

The for-each combinator for DOM already exists (`dom/foreach.cljc`). With intervals:

```clojure
;; DOM rendering with intervals
(spin
  (let [todos-iv (track todos)]
    (el/div {:class "app"}
      (el/h1 "Todo List")
      (el/ul
        ;; ifor-each works on intervals, returns interval of vnodes
        (iv/get-new
          (ifor-each :id render-todo todos-iv))))))
```

**Key insight**: The vdom elements ARE the interval's `:new` value. Deltas tell us what changed for efficient DOM updates.

---

## Implementation Plan

### Phase 1: Update Track to Return Interval

```clojure
;; In effects/track.cljc
(require '[org.replikativ.spindel.incremental.interval :as iv])

(defn- get-track-value [signal-ref]
  (let [node (sig/get-signal-state signal-ref)]
    (iv/->Interval
      (:old-snapshot node)
      (:snapshot node)
      (:deltas node))))
```

**Backward compatibility**: The Interval type already supports:
- `@interval` → returns `:new` value (like `@signal-delta-view`)
- `(:new interval)` → works via ILookup
- `(:old interval)` → works via ILookup
- `(:deltas interval)` → works via ILookup

### Phase 2: Ensure Deltaable Values Flow Through

When a signal contains a deltaable collection, the deltas should flow:

```clojure
;; Signal swap produces deltas
(swap! todos conj {:id 4 :text "New"})

;; The deltaable's deltas are captured in SignalNode
;; and exposed through the Interval returned by track
```

This is already happening in `swap-signal*-explicit`:
```clojure
(let [deltas (d/get-deltas new-value)
      clean-value (d/clear-deltas new-value)]
  (nt/->signal-node clean-value old-value deltas ...))
```

### Phase 3: Combinator Pipeline

With track returning intervals, the pipeline flows naturally:

```clojure
(spin
  (let [todos-iv (track todos)]    ; Interval with old/new/deltas
    (->> todos-iv
         (ifilter :active)          ; Uses cached old, processes deltas
         (imap :hours)              ; Transforms deltas
         (ireduce + 0))))           ; O(delta) accumulation
```

Each combinator:
1. Gets its address from source location
2. Retrieves previous output from `[:incremental address]`
3. Uses `prev.new` as `our.old`
4. Processes input deltas incrementally
5. Stores new output at address
6. Returns interval for downstream

### Phase 4: DOM Integration

```clojure
;; The render spin produces interval-wrapped vdom
(def app-spin
  (spin
    (let [todos-iv (track todos)
          active-iv (ifilter :active todos-iv)
          rendered-iv (ifor-each :id render-todo active-iv)]
      ;; Return the vdom (new value of the interval)
      (el/div {:class "app"}
        (el/ul (iv/get-new rendered-iv))))))

;; render-spin! subscribes to the spin
(render-spin! container app-spin discharge)
```

The DOM diffing in `render.cljc` can leverage the deltas:

```clojure
;; If vdom is an Interval, use its deltas directly
(defn update-render! [render-state new-vdom-or-interval]
  (if (iv/interval? new-vdom-or-interval)
    ;; Fast path: use deltas from interval
    (let [deltas (iv/get-deltas new-vdom-or-interval)
          new-vdom (iv/get-new new-vdom-or-interval)]
      (apply-deltas-to-dom discharge deltas)
      (assoc render-state :current-vdom new-vdom))
    ;; Slow path: diff old/new vdom
    (let [diffed-vdom (diff-vdom current-vdom new-vdom discharge)]
      ...)))
```

---

## The Unified Mental Model

```
┌─────────────────────────────────────────────────────────────────┐
│                         SIGNAL LAYER                             │
│                                                                   │
│   Signal contains deltaable collection                           │
│   swap!/reset! produces deltas automatically                     │
│   SignalNode stores: snapshot + old-snapshot + deltas            │
│                                                                   │
│   (swap! todos conj {:id 4})                                     │
│   ;; Produces: {:delta :add :path [3] :value {:id 4}}            │
│                                                                   │
└────────────────────────────┬──────────────────────────────────────┘
                             │ track effect
                             ▼
┌─────────────────────────────────────────────────────────────────┐
│                      INTERVAL LAYER                              │
│                                                                   │
│   track returns Interval(old-snapshot, snapshot, deltas)         │
│                                                                   │
│   (let [todos-iv (track todos)]                                  │
│     todos-iv  ; #Interval{:old [...] :new [...] :deltas [...]}   │
│                                                                   │
└────────────────────────────┬──────────────────────────────────────┘
                             │ incremental combinators
                             ▼
┌─────────────────────────────────────────────────────────────────┐
│                    COMBINATOR LAYER                              │
│                                                                   │
│   Each combinator:                                               │
│   - Caches result at [:incremental address]                      │
│   - Uses prev.new as our.old                                     │
│   - Processes deltas incrementally (O(delta))                    │
│   - Returns Interval for downstream                              │
│                                                                   │
│   (->> todos-iv (ifilter :active) (imap :hours) (ireduce + 0))   │
│                                                                   │
└────────────────────────────┬──────────────────────────────────────┘
                             │ DOM rendering
                             ▼
┌─────────────────────────────────────────────────────────────────┐
│                       DOM LAYER                                  │
│                                                                   │
│   ifor-each produces Interval of vnodes                          │
│   Deltas drive efficient DOM updates                             │
│                                                                   │
│   (el/ul (iv/get-new (ifor-each :id render-todo todos-iv)))      │
│                                                                   │
│   :add delta → appendChild                                       │
│   :remove delta → removeChild                                    │
│   :update delta → update element                                 │
│                                                                   │
└─────────────────────────────────────────────────────────────────┘
```

---

## Key Benefits

1. **Single Abstraction**: Interval unifies signal views, deltaable collections, and vdom updates

2. **Automatic Propagation**: Deltas flow through the entire pipeline without manual extraction

3. **True O(delta)**: Each layer processes only what changed

4. **Natural Clojure Feel**: Code looks like normal Clojure with threading macros

5. **Fork-Safe**: All state in runtime, intervals are immutable values

6. **Backward Compatible**: Interval supports `@`, `(:key ...)`, destructuring

---

## Example: Full Reactive Pipeline

```clojure
(ns my-app
  (:require [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.incremental.combinators :refer [ifilter imap ireduce ifor-each]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.render :as render]))

(def todos (sig/signal []))

(def remaining-hours
  (spin
    (let [todos-iv (track todos)]
      ;; Pipeline: filter active → extract hours → sum
      ;; Each step is O(delta) on re-execution
      (iv/get-new
        (->> todos-iv
             (ifilter :active)
             (imap :hours)
             (ireduce + 0))))))

(def todo-app
  (spin
    (let [todos-iv (track todos)
          hours-iv (track remaining-hours)]  ; Depend on derived spin
      (el/div {:class "app"}
        (el/h1 "Todos")
        (el/p (str "Remaining: " (iv/get-new hours-iv) " hours"))
        (el/ul
          (iv/get-new
            (ifor-each :id
              (fn [{:keys [id text done hours]}]
                (el/li {:key id :class (when done "done")}
                  (el/span text)
                  (el/span (str " (" hours "h)"))))
              todos-iv)))))))

;; Mount and run
(render/render-spin! container todo-app discharge)

;; Updates propagate automatically with O(delta) efficiency
(swap! todos conj {:id 4 :text "New task" :active true :hours 2})
;; → Only the new item is rendered, sum updates incrementally
```

---

## Next Steps

1. **Update track effect** to return Interval instead of SignalDeltaView
2. **Add tests** for the integrated pipeline
3. **Update DOM render** to use interval deltas when available
4. **Document** the unified programming model
