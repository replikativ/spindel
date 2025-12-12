# Hierarchical Incremental Rendering Design

## Problem Statement

Building a block editor (like Notion/Roam) requires efficient incremental updates for:
1. **Hierarchical visibility** - only show expanded subtrees
2. **Computed properties** - depth, has-children depend on structure
3. **External context** - focus, selection are separate from block data
4. **Order changes** - siblings can be reordered, blocks can move between parents

Current approach uses `mapv` which is O(n) on every change. We want O(delta).

## Data Model

```clojure
;; Flat storage with parent pointers (like a database)
{:blocks [{:id 1 :parent-id nil :order 0 :content "Root"}
          {:id 2 :parent-id 1   :order 0 :content "Child 1"}
          {:id 3 :parent-id 1   :order 1 :content "Child 2"}
          {:id 4 :parent-id 2   :order 0 :content "Grandchild"}]
 :collapsed #{3}  ; block 3 is collapsed
 :focus 2}        ; block 2 is focused
```

## Derived Data

1. **children-map**: `{parent-id -> [child-ids sorted by order]}`
2. **depth-map**: `{id -> depth}`
3. **has-children-map**: `{id -> boolean}`
4. **visible-list**: `[ids in DFS order, respecting collapsed]`
5. **render-data**: `[{:block block :depth d :focused? f :collapsed? c :has-children? h}]`

## Design: Incremental Index Maintenance

### Core Idea

Maintain **derived indexes** as signals that update incrementally when the source changes.
Each index has a `maintain` function that processes deltas.

### Index: children-map

```clojure
(defn maintain-children-map [prev-map delta]
  (case (:delta delta)
    :add
    (let [{:keys [id parent-id order]} (:value delta)]
      (update prev-map parent-id
              (fnil conj (sorted-set-by :order))
              {:id id :order order}))

    :remove
    (let [{:keys [id parent-id]} (:old-value delta)]
      (update prev-map parent-id disj {:id id :order (:order (:old-value delta))}))

    :update
    (let [old (:old-value delta)
          new (:value delta)]
      (cond-> prev-map
        ;; Remove from old parent
        (not= (:parent-id old) (:parent-id new))
        (update (:parent-id old) disj {:id (:id old) :order (:order old)})

        ;; Add to new parent (or update order in same parent)
        true
        (update (:parent-id new)
                (fn [children]
                  (-> (or children (sorted-set-by :order))
                      (disj {:id (:id old) :order (:order old)})
                      (conj {:id (:id new) :order (:order new)}))))))))

(def children-map-signal
  (spin
    (let [{:keys [new old deltas]} (track blocks-signal)
          prev @(track-self)]  ; self-reference for incremental
      (if (and prev deltas)
        (reduce maintain-children-map prev deltas)
        (build-children-map new)))))
```

### Problem: `track-self` Doesn't Exist

We need a way for a spin to access its previous value. Options:

**Option A: Explicit accumulator signal**
```clojure
(def children-map-signal (signal {}))

(def children-map-maintainer
  (spin
    (let [{:keys [deltas]} (track blocks-signal)
          prev @children-map-signal]
      (reset! children-map-signal
        (if deltas
          (reduce maintain-children-map prev deltas)
          (build-children-map @blocks-signal))))))
```

**Option B: New `scan` combinator** (like RxJS scan)
```clojure
(def children-map-signal
  (scan blocks-signal
        {}  ; initial
        (fn [prev-map blocks-interval]
          (if-let [deltas (:deltas blocks-interval)]
            (reduce maintain-children-map prev-map deltas)
            (build-children-map (:new blocks-interval))))))
```

**Option C: Use existing `accumulate` combinator**
We just built this! It accumulates intervals. Could adapt for state accumulation:

```clojure
(def children-map-signal
  (spin
    (let [blocks-iv (accumulate blocks-signal iv/merge-intervals)]
      ;; blocks-iv has ALL deltas since last read
      ;; But we need to maintain state, not just merge intervals
      ...)))
```

### Proposed: `derive` - Incremental Derived Signal

A new primitive that creates a derived signal with incremental maintenance:

```clojure
(defn derive
  "Create a derived signal that maintains state incrementally.

   Args:
     source - Source signal to derive from
     init-fn - (source-value) -> initial-state
     update-fn - (prev-state delta) -> new-state

   Returns: A signal-like value that can be tracked"
  [source init-fn update-fn]
  ...)

;; Usage
(def children-map
  (derive blocks-signal
    build-children-map              ; init from full value
    maintain-children-map))         ; update from delta

(def depth-map
  (derive children-map              ; chain derivations!
    build-depth-map
    maintain-depth-map))
```

### Index: depth-map

```clojure
(defn maintain-depth-map [depth-map children-map delta]
  ;; When a block moves to new parent, update its depth and all descendants
  (case (:delta delta)
    :add
    (let [{:keys [id parent-id]} (:value delta)
          parent-depth (get depth-map parent-id -1)]
      (assoc depth-map id (inc parent-depth)))

    :remove
    (let [{:keys [id]} (:old-value delta)]
      ;; Remove this block and all descendants
      (reduce dissoc depth-map (tree-descendants children-map id)))

    :update
    (let [{old-parent :parent-id old-id :id} (:old-value delta)
          {new-parent :parent-id} (:value delta)]
      (if (= old-parent new-parent)
        depth-map  ; no depth change
        ;; Recalculate depth for moved subtree
        (let [new-depth (inc (get depth-map new-parent -1))
              old-depth (get depth-map old-id)]
          (reduce (fn [dm id]
                    (update dm id + (- new-depth old-depth)))
                  depth-map
                  (cons old-id (tree-descendants children-map old-id))))))))
```

### Index: visible-list

This is the trickiest because it's an ordered traversal.

```clojure
(defn maintain-visible-list [prev-list children-map collapsed delta]
  ;; This is complex because:
  ;; 1. Adding a block may insert it anywhere in the list
  ;; 2. Moving a block may move an entire subtree
  ;; 3. Collapsing removes a subtree from visibility

  ;; For now, let's say: if structural delta, recompute
  ;; Only optimize for collapse/expand
  ...)
```

**Insight**: Maybe `visible-list` shouldn't be incrementally maintained at all.
It's a DFS traversal that's O(visible), not O(all). If visible << all, it's fast.

### Alternative: Skip visible-list, Use Recursive Rendering

```clojure
(defn render-children [parent-id]
  (spin
    (let [children (get @(track children-map) parent-id)
          collapsed? (contains? @(track collapsed-signal) parent-id)]
      (when-not collapsed?
        (ifor-each :id children
          (fn [{:keys [id]}]
            (render-block id)))))))

(defn render-block [block-id]
  (spin
    (let [block (get-by-id @(track blocks-signal) block-id)
          depth (get @(track depth-map) block-id)
          focused? (= block-id @(track focus-signal))
          has-children? (seq (get @(track children-map) block-id))]
      (el/div {:class (str "block" (when focused? " focused"))
               :style (str "padding-left: " (* depth 24) "px")}
        (render-content block)
        (render-children block-id)))))

;; Root
(defn render-editor []
  (spin
    (el/div {:class "editor"}
      (render-children nil))))  ; nil = root parent
```

**This is Option E from above** - recursive rendering that mirrors tree structure.

## Evaluation

| Approach | Complexity | Fits Spindel? | DOM Efficiency |
|----------|------------|---------------|----------------|
| Flat list + mapv | O(n) always | Yes | Relies on vdom diff |
| Derived indexes | O(delta) maintain | Needs `derive` | O(delta) with ifor-each |
| Recursive render | O(visible) | Yes (nested spins) | Natural subtree updates |
| Full datalog | O(delta) | Overkill | O(delta) |

## Recommendation

**Short term**: Use recursive rendering (Option E)
- Works with existing primitives
- Natural fit for tree data
- Collapse/expand is just conditional rendering
- No new primitives needed

**Medium term**: Add `derive` combinator for derived indexes
- Enables O(delta) maintenance of any derived state
- Composable (depth-map derives from children-map)
- Useful beyond block editors

**Long term**: Consider structural deltas for trees
- `:move` delta type for subtree moves
- Tree-aware diff/patch

## Next Steps

1. Refactor block-editor-demo to use recursive rendering
2. Verify nested spins work correctly
3. Measure performance vs mapv approach
4. If needed, implement `derive` combinator

## Open Questions

1. Can a spin return another spin? (nested reactivity)
2. How does `ifor-each` interact with nested spins?
3. Should we have a `track-key` for map signals (only trigger on specific key)?
4. How do we handle focus/scroll when structure changes?

---

## Investigation Findings

### Nested Spins Work for Computation

From `nested_spin_invalidation_test.clj`:
- Parent spins can create child spins that capture closure values
- When parent re-executes, child closures are updated
- Creator-child tracking ensures proper invalidation propagation

### DOM Rendering Expects VNodes, Not Spins

From `dom/render.cljc`:
- `render-spin!` expects the spin to return vdom (vnodes with deltas)
- `ifor-each` render functions return vnodes directly
- There's no automatic "await nested spin" in the DOM layer

### `ifor-each` Limitations

From `dom/foreach.cljc`:
- Tracks items by key for cache lookup
- Handles `:add`, `:remove`, `:update` deltas
- Does NOT handle pure reordering (same keys, different positions)
- When indent moves a block, `visible-blocks` order changes but keys stay same

---

## Practical Path Forward

### Phase 1: Incremental Derived Indexes (Low Risk)

Add derived index maintenance **outside** the render, then use in render:

```clojure
;; Incrementally maintained indexes
(def children-by-parent
  (atom {}))  ; {parent-id -> sorted-vec-of-children}

(def depth-by-id
  (atom {}))  ; {id -> depth}

;; Listener that maintains indexes when blocks change
(add-watch blocks-signal ::index-maintenance
  (fn [_ _ old-blocks new-blocks]
    ;; Update children-by-parent and depth-by-id incrementally
    ...))

;; Render still uses mapv, but lookups are O(1)
(spin
  (let [{:keys [new]} (track blocks-signal)
        focus-id @(track focus-signal)
        collapsed @(track collapsed-signal)
        ;; visible-blocks is still O(visible), uses children-by-parent
        visible (visible-blocks-fast new @children-by-parent collapsed)]
    (el/div {:class "blocks"}
      (mapv (fn [block]
              (render-block block
                            (get @depth-by-id (:id block))
                            (has-children? @children-by-parent (:id block))
                            (contains? collapsed (:id block))
                            (= (:id block) focus-id)))
            visible))))
```

**Benefit**: O(1) lookups instead of O(n) scans for depth/children
**Limitation**: Still O(n) render calls, relies on vdom diff

### Phase 2: Fine-Grained Context Signals

Create signals for each piece of derived context:

```clojure
;; Each block's render context as a signal (lazily created)
(defn get-block-context-signal [block-id]
  (or (get @context-signals block-id)
      (let [ctx-sig (spin
                      {:depth (get @(track depth-signal) block-id)
                       :focused? (= block-id @(track focus-signal))
                       :collapsed? (contains? @(track collapsed-signal) block-id)
                       :has-children? (seq (get @(track children-signal) block-id))})]
        (swap! context-signals assoc block-id ctx-sig)
        ctx-sig)))

;; Each block renders with its own context signal
(ifor-each :id visible-blocks
  (fn [block]
    (let [ctx @(get-block-context-signal (:id block))]  ; <-- Problem: can't await in render-fn
      (render-block block ctx))))
```

**Problem**: `ifor-each` render function can't await spins. It must return vnode synchronously.

### Phase 3: Component Spins (New Primitive Needed)

We need a way to embed a spin within the vdom that:
1. Is evaluated when the parent vdom is rendered
2. Has its own reactive scope (re-renders independently)
3. Produces vdom that integrates into the parent's DOM tree

```clojure
;; Hypothetical: spin-component that embeds reactive vdom
(defn render-block-component [block-id]
  (spin-component  ; <-- New primitive
    (let [block (get-by-id @(track blocks-signal) block-id)
          ctx @(track (get-block-context-signal block-id))]
      (el/div {:class (str "block" (when (:focused? ctx) " focused"))}
        (:content block)
        ;; Recursive: children are also spin-components
        (when-not (:collapsed? ctx)
          (el/div {:class "children"}
            (ifor-each :id (get @(track children-signal) block-id)
              (fn [{:keys [id]}]
                (render-block-component id)))))))))

;; Root
(spin
  (el/div {:class "editor"}
    (ifor-each :id (get @(track children-signal) nil)
      (fn [{:keys [id]}]
        (render-block-component id)))))
```

**This is the "fully incremental" solution** but requires new primitives.

---

## Recommendation: Start with Phase 1

Phase 1 gives immediate benefits with minimal risk:
1. O(1) depth/children lookups instead of O(n) tree traversal per block
2. No new primitives needed
3. Render is still O(visible) but with fast constant factors
4. `mapv` still works, vdom diffing handles attribute changes efficiently

After Phase 1, measure performance. If still too slow:
- Phase 2 requires solving "await in render function" problem
- Phase 3 requires `spin-component` primitive

---

## Implementation Plan for Phase 1

1. **Create index maintenance module**
   ```
   src/is/simm/uis/block_editor/indexes.cljs
   ```
   - `children-by-parent-atom`: `{parent-id -> [{:id :order} ...]}`
   - `depth-by-id-atom`: `{id -> depth}`
   - `maintain-indexes!`: watch blocks-signal, update atoms on change

2. **Update `visible-blocks`**
   - Use `children-by-parent` for O(1) child lookup
   - No longer scans all blocks per level

3. **Update render**
   - Use `depth-by-id` for O(1) depth lookup
   - Use `children-by-parent` for O(1) has-children check

4. **Measure**
   - Before/after with 1000 blocks
   - Profile where time is spent
