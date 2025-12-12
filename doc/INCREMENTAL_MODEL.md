# Spindel's Incremental Programming Model: Algebraic Foundations and Design

## Abstract

This document formalizes Spindel's incremental reactive programming model, connecting it to established theory in incremental computation, differential λ-calculus, and self-adjusting computation. We describe how **Intervals** serve as the central abstraction unifying signals, combinators, and DOM rendering into a coherent algebraic framework with O(δ) complexity guarantees.

## 1. Core Abstraction: The Interval

### 1.1 Definition

An **Interval** `I` represents a segment of change in a value over time:

```
I = ⟨old, new, δ⟩
```

Where:
- `old`: Value at the start of the interval (baseline)
- `new`: Value at the end of the interval (current state)
- `δ`: Sequence of structural changes (deltas) that transform `old` → `new`

### 1.2 Interval Type (Implementation)

```clojure
(deftype Interval [old-value new-value deltas]
  PInterval
  (get-old [_] old-value)
  (get-new [_] new-value)
  (get-deltas [_] deltas)
  (commit [_] (Interval. new-value new-value nil)))
```

### 1.3 Algebraic Properties

**Identity Interval**: `I₀ = ⟨v, v, []⟩` — no change occurred

**Commit Operation**: `commit(⟨old, new, δ⟩) = ⟨new, new, []⟩`
- Advances the baseline, clears deltas
- Corresponds to "acknowledging" a change

**Coercion**: Any value can be lifted to an Interval:
```
as-interval(v) = ⟨nil, v, nil⟩   // Static interval (no history)
```

## 2. Delta Algebra

### 2.1 Delta Grammar

Deltas are first-class structural change descriptors:

```
δ ::= {:delta :add,    :path p, :value v}
    | {:delta :remove, :path p, :old-value v}
    | {:delta :update, :path p, :value v, :old-value v'}
```

Where `p` is a path (index for vectors, key for maps).

### 2.2 Delta Application (Patch)

The `apply-delta` function reconstructs state:

```
patch : Collection × Delta → Collection

patch(c, {:delta :add, :path [i], :value v}) = insert(c, i, v)
patch(c, {:delta :remove, :path [i]}) = remove(c, i)
patch(c, {:delta :update, :path [i], :value v}) = assoc(c, i, v)
```

**Fundamental Property**:
```
∀ I = ⟨old, new, δ⟩ : fold(patch, old, δ) = new
```

This is the **patch-diff consistency** property from incremental λ-calculus.

### 2.3 Delta Composition

Deltas can be composed (compacted):

```
add(i, v) ∘ remove(i) = ∅           // Cancel
remove(i) ∘ add(i, v) = update(i, v) // Upgrade to update
update(i, v₁) ∘ update(i, v₂) = update(i, v₂)  // Keep latest
```

This forms a partial monoid structure where composition may annihilate.

## 3. Combinators as Derivatives

### 3.1 Connection to Incremental λ-Calculus

In the [Incremental λ-Calculus](https://dl.acm.org/doi/abs/10.1145/2666356.2594304) (Cai et al., PLDI 2014), a program `f : A → B` has a **derivative**:

```
∂f : A × ΔA → ΔB
```

The derivative maps (base value, change) to output change, satisfying:

```
f(a ⊕ da) = f(a) ⊕ ∂f(a, da)
```

Where `⊕` is the "patch" operation.

### 3.2 Spindel's Interval Combinators as Derivatives

Our combinators implement this pattern implicitly:

```clojure
(defn filter* [source-loc pred source]
  ;; Input: Interval ⟨old-coll, new-coll, deltas⟩
  ;; Output: Interval ⟨old-filtered, new-filtered, filtered-deltas⟩
  (with-incremental-cache source-loc
    (fn [prev-output]
      (let [source-iv (as-interval source)
            our-old (when prev-output (get-new prev-output))]
        (if (and our-old (seq (get-deltas source-iv)))
          ;; INCREMENTAL: ∂filter(old, δ) → δ'
          (process-deltas-incrementally ...)
          ;; FULL RECOMPUTE: filter(new-coll)
          (filterv pred (get-new source-iv)))))))
```

The key insight: **prev-output.new becomes current.old**, forming the derivative chain.

### 3.3 Enter/Exit Semantics for Filter

Filter has special semantics because elements can **enter** or **exit** the filtered set:

```
∂filter(pred):
  :add(v)    → if pred(v) then :add(v) else ∅
  :remove(v) → if pred(v) then :remove(v) else ∅
  :update(old→new) →
    | pred(old) ∧ pred(new)  → :update(old→new)  // Stay in
    | ¬pred(old) ∧ pred(new) → :add(new)         // ENTER
    | pred(old) ∧ ¬pred(new) → :remove(old)      // EXIT
    | otherwise              → ∅                  // Stay out
```

This is the **differential filter** operation.

### 3.4 Map as a Functor

Map is simpler—it's a functor that lifts `f` to deltas:

```
∂map(f):
  :add(v)         → :add(f(v))
  :remove(v)      → :remove(f(v))
  :update(old→new) → :update(f(old)→f(new))
```

### 3.5 Reduce with Enter/Exit

Incremental reduce requires an **inverse** (exit function):

```
∂reduce(rf, enter, exit):
  :add(v)    → acc := enter(acc, v)
  :remove(v) → acc := exit(acc, v)
  :update(old→new) → acc := enter(exit(acc, old), new)
```

For `(reduce + 0)`, enter is `+` and exit is `-`.

**Constraint**: Exit must be the inverse of enter for correctness:
```
exit(enter(acc, v), v) = acc
```

This is why not all reductions can be incrementalized (e.g., `min` requires O(n) recomputation on removal).

## 4. Addressing and Caching

### 4.1 The Addressing Problem

Each combinator needs a stable identity to cache its previous output. We use **source location addressing**:

```
address = hash(file, line, column)
```

Captured via macros:

```clojure
(defmacro ifilter [pred source]
  (let [source-loc {:file *file* :line (:line (meta &form)) ...}]
    `(filter* ~source-loc ~pred ~source)))
```

### 4.2 Cache-Transfer Style (CTS)

This is related to [Cache-Transfer Style](https://link.springer.com/chapter/10.1007/978-3-030-17184-1_20) (Giarrusso et al., 2019), where incremental programs explicitly thread cache tuples.

Spindel stores caches in the runtime state:
```
[:incremental address] → previous Interval
```

This enables:
1. **Fork-safety**: Cache lives in runtime, not closures
2. **Deterministic replay**: Same source-loc → same cache

### 4.3 Relation to Adapton

[Adapton](https://dl.acm.org/doi/abs/10.1145/2666356.2594324) (Hammer et al., PLDI 2014) uses a **demanded computation graph (DCG)** where:
- Thunks track dependencies
- Dirty-marking propagates changes
- Memoization reuses unchanged results

Spindel differs in:
1. **Push-based**: Signals push changes to observers (vs. Adapton's pull/demand)
2. **Explicit deltas**: Changes are first-class values (vs. dirty bits)
3. **Topological ordering**: Glitch-free updates via dependency sort

## 5. Signals as Time-Varying Values

### 5.1 FRP Foundation

Signals in Spindel are **discrete-time behaviors**:

```
Signal[A] ≈ Time → A
```

But with incremental access:

```
track : Signal[A] → Interval[A]
```

The `track` effect returns an Interval containing the signal's:
- Previous snapshot (old)
- Current snapshot (new)
- Accumulated deltas

### 5.2 Dual Perspective

Signals maintain both **state-based** and **delta-based** views:

```clojure
(defrecord SignalNode
  [snapshot       ; Current value
   old-snapshot   ; Previous value
   deltas         ; Structural changes
   observers])    ; Dependent spins
```

This enables consumers to choose their preferred access pattern:
- **State-based**: Just use `:new` — simple, always correct
- **Delta-based**: Use `:deltas` — O(δ) but requires correct handling
- **Diff-based**: Compare `:old` and `:new` — middle ground

## 6. DOM Rendering Integration

### 6.1 Delta-Direct Rendering

Traditional virtual DOM:
```
render(state) → vdom → diff(old_vdom, new_vdom) → patches → DOM
```

Spindel's delta-direct:
```
render(Interval) → vdom_with_deltas → discharge(deltas) → DOM
```

The key insight: **deltas flow through the entire pipeline**, eliminating the diff step.

### 6.2 Keyed Collections (ifor-each)

```clojure
(ifor-each :id items
  (fn [item] (el/li (:text item))))
```

This creates a **KeyedFragment** that:
1. Has its own tree address (from source-loc)
2. Caches rendered vnodes by key
3. Only re-renders changed items
4. Produces output deltas for parent element

### 6.3 Element Slot Reconciliation

Each element tracks children by **slot**:

```
Element:
  address: (hash source-loc parent-addr slot-index)
  children: Vector[Slot]

Slot:
  :single → single VNode
  :keyed  → KeyedFragment with internal deltas
```

When a slot's content changes, the element:
1. Compares old vs new slot content
2. Generates delta for changed slot
3. Propagates to discharge

### 6.4 Lifecycle as Category Morphisms

DOM elements form a category where:
- Objects: DOM states (trees of elements)
- Morphisms: Patches (delta applications)

The rendering pipeline is a functor:
```
F : Interval[State] → Interval[DOM]
```

Preserving composition:
```
F(δ₁ ∘ δ₂) = F(δ₁) ∘ F(δ₂)
```

## 7. Complexity Analysis

### 7.1 O(δ) Guarantee

For a collection of size `n` with `k` changes:

| Operation | Traditional | Spindel |
|-----------|-------------|---------|
| Filter    | O(n)        | O(k)    |
| Map       | O(n)        | O(k)    |
| Reduce    | O(n)        | O(k)*   |
| For-Each  | O(n)        | O(k)    |
| DOM Diff  | O(n)        | O(k)    |

*Reduce requires invertible aggregation

### 7.2 When Incrementality Fails

Full recomputation occurs when:
1. No previous cache exists (initial run)
2. No deltas provided (non-deltaable source)
3. Predicate/function changed (rare in practice)

## 8. Relation to Other Systems

### 8.1 Incremental λ-Calculus (Cai et al.)

[A Theory of Changes for Higher-Order Languages](https://dl.acm.org/doi/abs/10.1145/2666356.2594304)

Spindel implements the core ILC insight: programs can be **differentiated** to produce change propagators. Our Interval is their "change structure", our combinators are derivatives.

**Difference**: ILC is a compile-time transformation; Spindel is a runtime library with macro-captured addressing.

### 8.2 Differential Dataflow (McSherry et al.)

[Differential Dataflow](https://github.com/TimelyDataflow/differential-dataflow) uses **differences** (multisets of (data, time, diff)) for streaming computation.

**Similarity**: Both use explicit change representations for O(δ) updates.

**Difference**: DD is for distributed streaming; Spindel is for UI/single-node reactive programming.

### 8.3 Adapton (Hammer et al.)

[Adapton: Composable, Demand-Driven Incremental Computation](https://dl.acm.org/doi/abs/10.1145/2666356.2594324)

**Similarity**: Both cache intermediate results keyed by call site.

**Difference**:
- Adapton is demand-driven (lazy), Spindel is push-based (eager)
- Adapton uses dirty-marking, Spindel propagates explicit deltas
- Spindel's runtime forking enables speculative computation

### 8.4 Self-Adjusting Computation (Acar et al.)

[Self-Adjusting Computation](https://www.cs.cmu.edu/~rwh/papers/sac/jacm.pdf) maintains a dynamic dependency graph that re-executes affected subcomputations.

**Similarity**: Both track dependencies for selective re-execution.

**Difference**: SAC re-executes; Spindel transforms deltas without re-execution (for incrementalizable operations).

### 8.5 Fixing Incremental Computation (Arntzenius & Krishnaswami)

[Fixing Incremental Computation](https://arxiv.org/abs/1811.06069) extends ILC to handle recursive definitions (fixpoints), crucial for Datalog.

**Relevance**: Spindel's `spin` can express recursive reactive dependencies, though we haven't formalized fixpoint derivatives yet.

### 8.6 React/Virtual DOM

React's reconciliation is O(n) tree diffing with O(k) heuristics via keys.

Spindel eliminates diffing entirely by threading deltas through the render pipeline.

## 9. Formal Model (Sketch)

### 9.1 Types

```
Interval A = { old: Maybe A, new: A, deltas: List (Delta A) }

Delta A = Add (Path, A) | Remove (Path, A) | Update (Path, A, A)

Signal A = { current: Interval A, observers: Set SpinId }

Combinator : Interval A → Interval B
```

### 9.2 Laws

**Patch Consistency**:
```
∀ I : Interval A.
  I.old ≠ nil ∧ I.deltas ≠ nil ⟹
  fold patch I.old I.deltas = I.new
```

**Derivative Correctness**:
```
∀ f : A → B, da : ΔA, a : A.
  f (patch a da) = patch (f a) (∂f a da)
```

**Combinator Chaining**:
```
(g ∘ f)(I) = g(f(I))
// Deltas compose through the pipeline
```

### 9.3 Denotational Semantics (Informal)

```
⟦track s⟧ = Interval(s.old, s.new, s.deltas)

⟦ifilter p I⟧ =
  let old' = filter p I.old
      new' = filter p I.new
      δ' = ∂filter(p, I.deltas)
  in Interval(old', new', δ')

⟦imap f I⟧ =
  let old' = map f I.old
      new' = map f I.new
      δ' = map (∂f) I.deltas
  in Interval(old', new', δ')
```

## 10. Future Directions

### 10.1 Formalization

- Prove derivative correctness for all combinators
- Mechanize in Coq/Agda for verified incremental computation
- Explore connection to [differential logical relations](https://www.sciencedirect.com/science/article/abs/pii/S0304397521005569)

### 10.2 Optimization

- Delta compaction across pipeline stages
- Batching multiple signal changes before propagation
- JIT compilation of hot combinator chains

### 10.3 Extensions

- Incremental fixpoints for recursive queries (Datalog-style)
- Probabilistic/sampling combinators with delta semantics
- Distributed delta propagation across network boundaries

## 11. Conclusion

Spindel's incremental programming model provides:

1. **Unified abstraction**: Intervals carry (old, new, deltas) through the entire reactive pipeline
2. **O(δ) complexity**: Combinators process only changes, not full collections
3. **Compositional design**: Combinators chain naturally, each with its own derivative
4. **Practical implementation**: Macro-based addressing, runtime caching, fork-safe state

The model connects to established theory—ILC derivatives, Adapton memoization, differential dataflow—while providing a practical, ergonomic API for building incremental reactive applications.

## References

1. Cai, Y., Giarrusso, P., Rendel, T., Ostermann, K. (2014). [A Theory of Changes for Higher-Order Languages](https://dl.acm.org/doi/abs/10.1145/2666356.2594304). PLDI 2014.

2. Hammer, M., Khoo, Y., Hicks, M., Foster, J. (2014). [Adapton: Composable, Demand-Driven Incremental Computation](https://dl.acm.org/doi/abs/10.1145/2666356.2594324). PLDI 2014.

3. Giarrusso, P., Régis-Gianas, Y., Schuster, P. (2019). [Incremental λ-Calculus in Cache-Transfer Style](https://link.springer.com/chapter/10.1007/978-3-030-17184-1_20). ESOP 2019.

4. Arntzenius, M., Krishnaswami, N. (2019). [Fixing Incremental Computation: Derivatives of Fixpoints](https://arxiv.org/abs/1811.06069). ESOP 2019.

5. Acar, U. A. (2005). [Self-Adjusting Computation](https://www.cs.cmu.edu/~rwh/papers/sac/jacm.pdf). PhD Thesis, CMU.

6. McSherry, F., Murray, D., Isaacs, R., Isard, M. (2013). Differential Dataflow. CIDR 2013.

7. Hammer, M., Dunfield, J., Headley, K., Labich, N., Foster, J., Hicks, M., Van Horn, D. (2015). [Incremental Computation with Names](https://arxiv.org/abs/1503.07792) (Nominal Adapton). OOPSLA 2015.

8. Dal Lago, U., Gavazzo, F., Yoshimizu, A. (2021). [Differential Logical Relations](https://www.sciencedirect.com/science/article/abs/pii/S0304397521005569). TCS 2021.
