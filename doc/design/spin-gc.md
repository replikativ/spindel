# Spin Garbage Collection Design

## Problem

When a `Spin` object goes out of scope and is garbage-collected, its runtime
state remains in the `ExecutionContext` state atom. Without cleanup this is a
memory leak. A spin leaves state in 8 locations:

| Path | Content |
|------|---------|
| `[:nodes spin-id]` | SpinNode (result, status, deps, observers, created-by/spins) |
| `[:spins-meta spin-id]` | Metadata (`{:provides #{}}`) |
| `[:spin-outputs spin-id]` | Cached value for non-blocking await |
| `[:spin-tracking spin-id]` | Transient dep tracking (usually cleared after commit) |
| `[:continuations spin-id]` | Track/await continuations |
| `[:subscriptions event-key spin-id]` | Event subscription entries |
| `[:pending-callbacks spin-id]` | Duplicate execution callbacks |
| `[:await-dependents child-id]` | Entries where this spin appears as parent |

The existing `cleanup-spin!` / `graph-clear-deps!` is **partial**: it clears
deps, continuations, and subscriptions but leaves the node, meta, and outputs
behind.

## Constraints

1. **Spins are stateless**: The `Spin` deftype has only `spin-id` and `spin-fn`.
   It does not capture the `ExecutionContext` (by design, for fork safety).
2. **Dynamic binding unavailable during GC**: Cleaner/FinalizationRegistry
   callbacks run on GC threads where `*execution-context*` is not bound.
3. **Indirect references via dependency graph**: Other spins reference a spin by
   ID through the dependency graph, not by object reference. The GC cannot see
   these.
4. **Overlay forks**: Forked contexts share parent state via read-through.
   Cleanup in the parent must not break forks that still need the data.
5. **Cross-platform**: Must work on JVM (Cleaner API) and CLJS
   (FinalizationRegistry + WeakRef).

## Current State

| Platform | Spin cleanup | Atom cleanup |
|----------|-------------|-------------|
| JVM | **Disabled** (Cleaner registered but `run()` was no-op, removed) | **Works** (captures runtime in Cleaner closure) |
| CLJS | **Broken** (FinalizationRegistry calls `graph-clear-deps!` but only if `*execution-context*` is bound, which it almost never is during GC) | **Not implemented** |

## Design

### Tier 1: Per-spin GC cleanup via WeakRef-to-context

On spin creation, register a cleanup callback that holds:
- `spin-id` (value — no reference issues)
- A `WeakReference` (JVM) / `WeakRef` (CLJS) to the `ExecutionContext`

When the Spin object is GC'd:
1. Dereference the WeakRef to get the context.
2. If context is already GC'd → no-op (entire state atom is gone).
3. If context is alive, attempt cleanup via `try-gc-cleanup-spin!`.

```clojure
;; JVM — in make-spin
(let [weak-ctx (java.lang.ref.WeakReference. execution-context)
      sid spin-id]
  (.register @spin-cleaner reactive-spin
    (reify Runnable
      (run [_]
        (when-let [ctx (.get weak-ctx)]
          (try-gc-cleanup-spin! ctx sid))))))

;; CLJS — in make-spin
(when spin-registry
  (let [weak-ctx (js/WeakRef. execution-context)]
    (.register spin-registry reactive-spin
      #js {:spin-id spin-id :weak-ctx weak-ctx})))
```

The CLJS FinalizationRegistry callback becomes:

```clojure
(js/FinalizationRegistry.
  (fn [held-value]
    (let [spin-id (.-spin_id held-value)
          weak-ctx (.-weak_ctx held-value)]
      (when-let [ctx (.deref weak-ctx)]
        (try-gc-cleanup-spin! ctx spin-id)))))
```

### Tier 2: Observer-aware cleanup with cascading

A spin's state cannot be removed if other spins still observe it. The Spin
object being GC'd means no user code holds it, but the dependency graph may
still reference it by ID.

```
(def s (signal 0))
(def a (spin (:new (track s))))  ;; a tracks s
(def b (spin (* 2 (await a))))   ;; b observes a

;; User drops `a` but keeps `b` and `s`
;; Spin A object is GC'd, but b→a dependency means a's state must stay
```

**Rule**: A spin's state is safe to remove when:
1. Its Spin object is GC'd (no user-code reference), AND
2. It has no observers (`(:observers node)` is empty)

#### `try-gc-cleanup-spin!`

```clojure
(defn try-gc-cleanup-spin!
  "Called from GC callback. Attempts full cleanup if safe, otherwise marks
   the spin as orphaned for deferred cleanup."
  [ctx spin-id]
  (binding [rtc/*execution-context* ctx]
    (let [node (rtc/get-state [:nodes spin-id])]
      (when node  ;; may already be cleaned
        (if (empty? (:observers node))
          ;; No observers → full cleanup + cascade to dependencies
          (let [dep-spin-ids (get-in node [:deps :spins])]
            (full-cleanup-spin! spin-id)
            ;; Cascade: check if any dependency is now cleanable
            (doseq [dep-id dep-spin-ids]
              (let [dep-node (rtc/get-state [:nodes dep-id])]
                (when (and dep-node
                           (:orphaned? dep-node)
                           (empty? (:observers dep-node)))
                  (full-cleanup-spin! dep-id)))))
          ;; Has observers → mark orphaned, defer cleanup
          (rtc/swap-state! [:nodes spin-id]
            #(assoc % :orphaned? true)))))))
```

When a spin is fully cleaned, it is removed from its dependencies' observer
lists. This may make a dependency observer-free. If that dependency is also
orphaned, it cascades.

#### `full-cleanup-spin!`

Removes all 8 state locations atomically:

```clojure
(defn full-cleanup-spin!
  "Remove all runtime state for a spin. Must be called with *execution-context* bound."
  [spin-id]
  (let [ctx (rtc/current-execution-context)]
    (rtp/swap-state! ctx []
      (fn [state]
        (let [node (get-in state [:nodes spin-id])
              deps (when node (np/get-deps node))
              signal-deps (:signals deps #{})
              spin-deps (:spins deps #{})]
          (-> state
              ;; 1. Unregister from signal observers
              (as-> s (reduce (fn [s sid]
                                (if-let [n (get-in s [:nodes sid])]
                                  (update-in s [:nodes sid] np/remove-observer spin-id)
                                  s))
                              s signal-deps))
              ;; 2. Unregister from spin observers
              (as-> s (reduce (fn [s tid]
                                (if-let [n (get-in s [:nodes tid])]
                                  (update-in s [:nodes tid] np/remove-observer spin-id)
                                  s))
                              s spin-deps))
              ;; 3. Remove the spin node itself
              (update :nodes dissoc spin-id)
              ;; 4. Remove metadata
              (update :spins-meta dissoc spin-id)
              ;; 5. Remove cached output
              (update :spin-outputs dissoc spin-id)
              ;; 6. Remove continuations
              (update :continuations dissoc spin-id)
              ;; 7. Remove pending callbacks
              (update :pending-callbacks dissoc spin-id)
              ;; 8. Clean subscriptions
              (update :subscriptions
                (fn [subs]
                  (persistent!
                    (reduce-kv (fn [acc ek m]
                                 (let [m' (dissoc m spin-id)]
                                   (if (seq m') (assoc! acc ek m') acc)))
                               (transient {}) subs))))
              ;; 9. Clean await-dependents (remove this spin as parent)
              (update :await-dependents
                (fn [deps]
                  (persistent!
                    (reduce-kv (fn [m child-id parents]
                                 (let [parents' (disj parents spin-id)]
                                   (if (seq parents')
                                     (assoc! m child-id parents')
                                     m)))
                               (transient {}) deps))))))))))
```

### Overlay Fork Safety

When fork spin B awaits/tracks parent spin A, `graph-commit-deps!` writes to
`[:nodes spin-a-id :observers]` to add B. This is a **write** that triggers
copy-on-write: the fork gets its own copy of spin A's node in its overlay.
After COW, parent and fork are independent for that node.

Therefore: **parent cleanup of a spin never breaks forks** because:

1. If a fork actively uses the spin → COW already copied it to the overlay.
   Parent cleanup removes the parent's copy; fork's overlay copy is unaffected.
2. If a fork doesn't use the spin → the fork doesn't care.
3. If a fork holds a reference to the Spin object → the object is NOT GC'd
   (the fork's reference prevents collection). The parent's cleaner won't fire
   until all references everywhere are dropped.

The only read-through case is `[:spin-outputs spin-id]` via `@spin` (deref),
but if the fork holds a reference to the Spin object (required for deref),
the cleaner can't fire.

### Snapshot / Restore Interaction

Snapshots capture the full state atom as an immutable value. Spin state in the
snapshot is just data — the Spin objects that reference it are gone. This is
intentional: snapshots preserve the computation state for later restoration.

- The `:orphaned?` flag is **live context metadata** and should be stripped
  during `serialize-context` (closures can't be serialized anyway). On
  `restore-snapshot`, all spins start un-orphaned.
- When a spin re-executes after restore, `register-spin!` creates/updates its
  node and a new Spin object is created with a fresh Cleaner/FinalizationRegistry
  registration. GC tracking resumes automatically.
- Spin nodes that are never re-executed after restore remain as cold cached
  state. This is correct — they represent the snapshot's computation results.
  A future optimization could sweep stale un-accessed nodes, but it's not
  required for correctness.

### Signal and Atom Cleanup

This design focuses on **spin** cleanup. Signals and atoms have different
lifecycles:

- **Signals**: Created by user, persist until explicitly removed. No automatic
  GC (user manages signal lifetime).
- **Atoms**: Already have working JVM Cleaner that captures the runtime.
  CLJS atoms should get the same WeakRef-based treatment.

### Error Handling

GC callbacks must never throw:
- Wrap all cleanup in try/catch
- Log errors at debug level (not user-visible)
- Silently skip if context is in an inconsistent state (e.g., shutting down)

### Thread Safety

- `full-cleanup-spin!` uses a single atomic `swap-state! []` — thread-safe.
- The `:orphaned?` flag is set via `swap-state!` — thread-safe.
- Multiple GC callbacks running concurrently is safe because each operates on
  different spin-ids and all state mutations are atomic.
- Edge case: a spin is being cleaned while another spin is being executed that
  depends on it. The atomic swap ensures the cleanup either sees the observers
  or doesn't. If it sees observers, cleanup is deferred. If it doesn't see
  them (observer registration hasn't committed yet), the executing spin will
  re-register on its next execution.

## Validation

### Test: JVM spin state cleanup

```clojure
(deftest test-spin-gc-cleanup
  (let [ctx (ctx/create-execution-context)]
    (binding [rtc/*execution-context* ctx]
      ;; Create a spin, capture its ID
      (let [spin-id (atom nil)]
        (let [s (spin 42)]
          (reset! spin-id (tp/spin-id s))
          @s)  ;; force execution, populate all state
        ;; s is now out of scope
        ;; Force GC
        (System/gc)
        (Thread/sleep 200)
        ;; Verify state is cleaned up
        (is (nil? (rtc/get-state [:nodes @spin-id])))
        (is (nil? (rtc/get-state [:spin-outputs @spin-id])))
        (is (nil? (rtc/get-state [:spins-meta @spin-id])))))))
```

### Test: Deferred cleanup with observers

```clojure
(deftest test-spin-gc-deferred-when-observed
  (let [ctx (ctx/create-execution-context)]
    (binding [rtc/*execution-context* ctx]
      (let [parent-id (atom nil)
            child (let [p (spin 42)]
                    (reset! parent-id (tp/spin-id p))
                    (spin (* 2 (await p))))]
        @child
        ;; p (parent) is out of scope but child observes it
        (System/gc)
        (Thread/sleep 200)
        ;; Parent should be orphaned but NOT cleaned (child observes it)
        (is (some? (rtc/get-state [:nodes @parent-id])))
        (is (:orphaned? (rtc/get-state [:nodes @parent-id])))
        ;; Now drop child
        )
      ;; child is now out of scope
      (System/gc)
      (Thread/sleep 200)
      ;; Both should be cleaned via cascade
      ;; (check via snapshot of state keys)
      )))
```

### Test: Overlay fork isolation

```clojure
(deftest test-spin-gc-fork-isolation
  (let [ctx (ctx/create-execution-context)]
    (binding [rtc/*execution-context* ctx]
      (let [s (spin 42)]
        @s
        ;; Fork and use the spin in the fork
        (let [fork-ctx (ctx/fork-context ctx)]
          (binding [rtc/*execution-context* fork-ctx]
            ;; await triggers COW of the spin's node into fork overlay
            (let [f (spin (await s))]
              @f)))
        ;; Now drop s from parent scope
        ;; (fork-ctx and its spins are also out of scope)
        ))
    ;; After all scopes exit, force GC
    (System/gc)
    (Thread/sleep 200)
    ;; Verify parent context is clean
    ;; (spin state should be removed from parent)
    ))
```

### Test: CLJS spin state cleanup

Use `async done` pattern with `js/setTimeout` to allow GC to run between
operations. CLJS GC timing is non-deterministic, so tests should be structured
as "eventually consistent" checks with reasonable timeouts.

### Test: No residual garbage after bulk operations

```clojure
(deftest test-no-residual-after-bulk
  (let [ctx (ctx/create-execution-context)]
    (binding [rtc/*execution-context* ctx]
      ;; Create and deref 1000 spins
      (dotimes [_ 1000]
        @(spin 42))
      ;; Force GC
      (System/gc)
      (Thread/sleep 500)
      ;; Check runtime state size
      (let [nodes (rtc/get-state [:nodes])
            outputs (rtc/get-state [:spin-outputs])
            meta (rtc/get-state [:spins-meta])]
        ;; Should have 0 spin nodes (no signals, no persistent spins)
        (is (zero? (count (filter #(= :spin (:type (val %))) nodes))))
        (is (zero? (count outputs)))
        (is (zero? (count meta)))))))
```

## Implementation Plan

1. Add `:orphaned?` field to SpinNode (default `false`)
2. Implement `full-cleanup-spin!` in `runtime/impl/simple.cljc`
3. Implement `try-gc-cleanup-spin!` in `spin/core.cljc`
4. Update JVM `make-spin` to register Cleaner with WeakReference to context
5. Update CLJS `make-spin` to register FinalizationRegistry with WeakRef to context
6. Update CLJS `spin-registry` callback to use WeakRef instead of dynamic binding check
7. Update `register-cleanup!` helper to accept optional context parameter
8. Write CLJ tests with `System/gc` + sleep to verify cleanup
9. Write CLJS tests with `js/setTimeout` to verify cleanup
10. Run full test suite to verify no regressions
