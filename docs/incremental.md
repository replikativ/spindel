# Incremental Collections

Spindel tracks structural changes to collections as **deltas**, enabling O(delta) updates instead of O(n) re-computation. This is the foundation for efficient reactive UIs and incremental data processing.

## Deltaable Collections

Deltaable collections wrap standard Clojure vectors, maps, and sets with top-level change tracking.

```clojure
(require '[org.replikativ.spindel.incremental.deltaable :as d])
```

### Creating Deltaable Collections

```clojure
;; Vector
(def dv (d/deltaable-vector [1 2 3]))

;; Map
(def dm (d/deltaable-map {:a 1 :b 2}))

;; Set
(def ds (d/deltaable-set #{:x :y :z}))
```

### Operations Produce Deltas

Standard Clojure operations on deltaable collections produce delta records:

```clojure
(def dv (d/deltaable-vector [1 2 3]))

(def dv2 (conj dv 4))
(d/get-deltas dv2)
;; => [{:delta :add :path [3] :value 4}]

(def dv3 (assoc dv 0 10))
(d/get-deltas dv3)
;; => [{:delta :update :path [0] :value 10 :old-value 1}]

(def dv4 (pop dv))
(d/get-deltas dv4)
;; => [{:delta :remove :path [2] :value 3}]
```

### Supported Operations by Type

| Operation | Vector | Map | Set |
|-----------|--------|-----|-----|
| `conj` | add at end | add key | add member |
| `assoc` | update at index | add/update key | — |
| `dissoc` | — | remove key | — |
| `disj` | — | — | remove member |
| `pop` | remove last | — | — |
| `update` | — | update key | — |

### Delta Format

```clojure
{:delta    :add/:update/:remove  ;; operation type
 :path     [index-or-key]        ;; location
 :value    new-value             ;; the new value
 :old-value old-value}           ;; only for :update
```

### Accessing Deltas

```clojure
(d/get-deltas dv2)     ;; get accumulated deltas
(d/has-deltas? dv2)    ;; true if non-empty deltas
(d/clear-deltas dv2)   ;; return copy with deltas cleared
@dv2                   ;; get underlying raw value
(d/unwrap dv2)         ;; also gets raw value
```

### Signal Auto-Wrapping

Signals automatically wrap collections as deltaable when you use standard operations:

```clojure
(def items (signal []))

(binding [ec/*execution-context* ctx]
  (swap! items conj {:name "Alice"})   ;; auto-wrapped as deltaable
  (swap! items conj {:name "Bob"}))

;; Inside a spin, track gives you deltas:
(spin
  (let [{:keys [new old deltas]} (track items)]
    ;; deltas: [{:delta :add :path [1] :value {:name "Bob"}}]
    ))
```

## Intervals

An `Interval` packages the old value, new value, and deltas from a signal change. It's what `track` returns.

```clojure
(require '[org.replikativ.spindel.incremental.interval :as iv])
```

### Structure

```clojure
{:old    previous-value    ;; value at last spin execution
 :new    current-value     ;; value now
 :deltas [delta-records]}  ;; structural changes
```

### Creating Intervals

```clojure
(iv/interval 42)                 ;; static (no old, no deltas)
(iv/interval old-val new-val)    ;; with old and new
(iv/interval old new deltas)     ;; with explicit deltas
```

### Querying Intervals

```clojure
(iv/changed? interval)   ;; true if old != new
(iv/static? interval)    ;; true if no old and no deltas
(iv/interval? x)         ;; type check
```

### Destructuring

Intervals support both map and sequential destructuring:

```clojure
;; Map destructuring
(let [{:keys [new old deltas]} (track sig)] ...)

;; Sequential destructuring
(let [[new-val old-val deltas] (track sig)] ...)

;; Deref for just the current value
@(track sig)  ;; => current value
```

### Merging Intervals

`merge-intervals` combines two intervals, preserving the oldest baseline and concatenating deltas:

```clojure
(def iv1 (iv/interval :a :b [{:delta :add :path [0] :value :b}]))
(def iv2 (iv/interval :b :c [{:delta :update :path [0] :value :c :old-value :b}]))

(iv/merge-intervals iv1 iv2)
;; => {:old :a, :new :c, :deltas [compacted-deltas...]}
```

This is **associative**: `merge(merge(a,b),c) = merge(a,merge(b,c))`. Used by `accumulate` to preserve deltas under rate control.

## Incremental Combinators

Transform intervals incrementally — O(delta) work instead of O(n).

```clojure
(require '[org.replikativ.spindel.incremental.combinators :as ic])
```

### `ifilter` — Incremental Filter

Filter a collection incrementally. Items entering or leaving the filtered set generate appropriate deltas:

```clojure
(spin
  (let [items (track items-signal)
        active (ic/ifilter :active? items)]
    ;; active is an Interval with filtered deltas
    ;; On each signal change, only processes changed items
    @active))
```

### `imap` — Incremental Map

Transform items incrementally:

```clojure
(spin
  (let [items (track items-signal)
        names (ic/imap :name items)]
    @names))  ;; => vector of names, updated incrementally
```

### `ireduce` — Incremental Reduce

Maintain a running reduction. Supports enter/exit functions for items being added or removed:

```clojure
;; Simple sum (default exit: subtraction)
(spin
  (let [prices (track prices-signal)
        total (ic/ireduce + 0 prices)]
    @total))

;; Custom enter/exit
(spin
  (let [items (track items-signal)
        summary (ic/ireduce
                  (fn [acc item] (assoc acc (:id item) item))  ;; rf
                  {}                                            ;; init
                  (fn [acc item] (assoc acc (:id item) item))  ;; enter
                  (fn [acc item] (dissoc acc (:id item)))      ;; exit
                  items)]
    @summary))
```

### `ifor-each` — Keyed Transformation

Transform items by key, only re-transforming changed items:

```clojure
(spin
  (let [items (track items-signal)
        rendered (ic/ifor-each
                   :id                                    ;; key function
                   (fn [item] (render-item item))         ;; transform
                   items)]
    @rendered))
```

### `islice` — Windowed View

Maintain a window into a collection for virtual scrolling:

```clojure
(spin
  (let [all-items (track items-signal)
        visible (ic/islice [start-idx end-idx] all-items)]
    ;; Only processes items entering/leaving the window
    @visible))
```

## Delta Transducers

For streaming delta processing:

```clojure
;; Transform delta values
(d/map-delta (fn [d] (update d :value str/upper-case)))

;; Filter deltas
(d/filter-delta (fn [d] (= :add (:delta d))))

;; Remove deltas (inverse of filter)
(d/remove-delta (fn [d] (= :remove (:delta d))))

;; Keep (transform + filter)
(d/keep-delta (fn [d] (when (= :add (:delta d)) (update d :value inc))))

;; Apply deltas to rebuild a collection
(reduce d/apply-delta [] deltas)

;; Compact redundant operations
(d/compact-deltas deltas)
;; Optimizations:
;;   - Multiple updates to same path → keep last
;;   - Add then remove → cancel out
;;   - Remove then add → convert to update
```

### Transduce

```clojure
(d/transduce-deltas
  (comp (d/filter-delta #(= :add (:delta %)))
        (d/map-delta #(update % :value str/upper-case)))
  []
  deltas)
```

## Pattern: Track + Process Deltas

The typical pattern for incremental processing:

```clojure
(def items (signal (d/deltaable-vector [])))

(spin
  (let [{:keys [new old deltas]} (track items)]
    (if (empty? deltas)
      ;; First run or non-deltaable: full computation
      (full-render new)
      ;; Subsequent runs: incremental update
      (doseq [{:keys [delta path value old-value]} deltas]
        (case delta
          :add    (insert-at-path path value)
          :remove (remove-at-path path)
          :update (update-at-path path value old-value))))))
```

## See Also

- [Effects](effects.md) — `track` returns intervals
- [Combinators](combinators.md) — `accumulate` with `merge-intervals`
- [Getting Started](getting-started.md) — Basic signal usage
