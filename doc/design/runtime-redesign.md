# Runtime Redesign: Batch State & Level-Parallel Execution

**Status:** Implemented (Steps 1-5 complete, Step 6 deferred — see §6.1)
**Date:** 2026-02-05
**Branch:** `feature/ephemeral-await-design1`

## 1. Motivation

The current runtime has three interrelated problems:

1. **Batch state uses dynamic bindings** that are fragile across thread boundaries.
   Async children on the thread pool may capture stale or dead batch queues.

2. **Polling for async completion** (`Thread/sleep 1` in a loop up to 100ms) is
   inefficient, non-portable to CLJS, and can miss or timeout.

3. **Sequential observer resumption** leaves parallelism on the table. Independent
   branches of the FRP dependency graph are processed one at a time.

These are symptoms of a single root cause: the batch mechanism is coupled to
thread-local state instead of being a first-class data structure in the runtime.

## 2. Background: What the Batch Mechanism Does

### 2.1 The Glitch Problem

When a signal changes, multiple spins may observe it. Without coordination, a
dependent spin could see a mix of old and new values:

```
        signal-S (changes 1 → 2)
       /        \
    spin-A    spin-B    (both track S)
       \        /
        spin-C          (awaits both A and B)
```

If A completes before B is even resumed, C's await for A fires with new-A but
C still sees old-B. This is a **glitch**.

### 2.2 How the Batch Prevents Glitches

The signal-change handler runs in two phases:

**Phase 1 (Push):** Resume all track continuations in topological order.
Each observer re-executes from its track breakpoint. Completion events are
**deferred** to a batch queue instead of being processed immediately.

**Phase 2 (Drain):** Process all deferred completion events. By this point,
all observers have been notified. Dependents that resume see consistent state.

### 2.3 The Two Reactive Primitives

- **`track`** (signal → spin): Persistent continuation. Resumes on every signal
  change. The spin is an **observer** of the signal.

- **`await`** (spin → spin): Ephemeral continuation. Parent suspends until child
  completes. Parent is a **dependent** of the child.

Track continuations are pushed (Phase 1). Await continuations are pulled
(Phase 2, when completion events are processed).

### 2.4 Current Implementation

```clojure
;; 4 dynamic bindings coordinate batching:
(binding [*completion-queue*       (atom [])        ; deferred events
          *batch-generation*       (inc-gen!)        ; dedup key
          *resumed-continuations*  (atom #{})        ; [parent child gen] triples
          *processed-spins*        (atom #{})]       ; fast-path cache
  ;; Phase 1: resume observers sequentially
  (doseq [spin-id observers]
    (resume-track-continuation! ...))
  ;; Phase 2: drain completion queue + poll for async children
  (loop [empty-checks 0]
    ...
    (Thread/sleep 1)
    (recur (inc empty-checks))))
```

Problems:
- Bindings must be captured/restored across thread boundaries
- Async children on thread pool may post to dead queue after batch ends
- Polling with arbitrary 100ms timeout
- Sequential Phase 1 misses parallelism opportunity

## 3. Design: Batch as Context State

### 3.1 Core Idea

Replace dynamic bindings with a **Batch data structure** stored in
`:engine/current-batch` in the execution context's state. Any thread with
access to the context can find and interact with the current batch.

### 3.2 Batch Data Structure

```clojure
{:engine/current-batch
  {:id             <unique-id>
   :generation     <monotonic-counter>
   :signal-id      <signal that triggered this batch>
   :observers      #{spin-id ...}       ; expected observer completions
   :completed      <atom #{}>           ; observers that have completed
   :resumed-conts  <atom #{}>           ; [parent child gen] dedup triples
   :processed      <atom #{}>           ; spins with fresh cache in batch
   :events         <BlockingQueue>      ; completion events (JVM)
                                        ; or (atom []) + callback (CLJS)
  }}
```

### 3.3 Completion Event Routing

```clojure
(defn enqueue-completion-event! [context spin-id]
  (if-let [batch (get-state context [:engine/current-batch])]
    ;; Route to batch's event queue
    (do
      #?(:clj  (.put (:events batch) {:type :spin-completion :id spin-id})
         :cljs (swap! (:events batch) conj {:type :spin-completion :id spin-id}))
      ;; Track observer completion
      (when (contains? (:observers batch) spin-id)
        (swap! (:completed batch) conj spin-id)))
    ;; Not in batch - enqueue directly to engine
    (enqueue-event! context {:type :spin-completion :id spin-id})))
```

Key property: **no dynamic binding needed**. The batch is found via context
state, which is the same atom regardless of which thread accesses it.

### 3.4 Accessing Batch State (replaces binding reads)

Code that currently reads `*completion-queue*`, `*batch-generation*`, etc.
instead reads from context state:

```clojure
;; Current (fragile):
(when-let [queue *completion-queue*]
  (swap! queue conj event))

;; Proposed (robust):
(when-let [batch (get-state context [:engine/current-batch])]
  (.put (:events batch) event))

;; Current:
(let [generation *batch-generation*
      dedup-key [parent-id child-id generation]]
  (contains? @*resumed-continuations* dedup-key))

;; Proposed:
(let [batch (get-state context [:engine/current-batch])
      generation (:generation batch)
      dedup-key [parent-id child-id generation]]
  (contains? @(:resumed-conts batch) dedup-key))
```

### 3.5 Await Fast-Path During Batch

The await effect currently checks `*completion-queue*` and `*processed-spins*`
to decide whether to use the fast path (resolve from cache) or slow path
(register continuation and suspend):

```clojure
;; Current:
(let [in-batch-mode? (some? simple/*completion-queue*)
      spin-processed? (when-let [ps simple/*processed-spins*]
                        (contains? @ps awaited-spin-id))]
  ...)

;; Proposed:
(let [batch (get-state context [:engine/current-batch])
      in-batch-mode? (some? batch)
      spin-processed? (when batch
                        (contains? @(:processed batch) awaited-spin-id))]
  ...)
```

## 4. Design: No-Polling Batch Completion

### 4.1 JVM: BlockingQueue

```clojure
(import '[java.util.concurrent LinkedBlockingQueue])

;; Phase 2: drain batch events, blocking on queue when empty
(loop []
  ;; Drain all currently available events
  (loop []
    (when-let [event (.poll (:events batch))]
      (process-event! context event)
      (recur)))
  ;; All observers done? If so, final drain and exit
  (if (= (:observers batch) @(:completed batch))
    ;; Final drain of any cascading events
    (loop []
      (when-let [event (.poll (:events batch))]
        (process-event! context event)
        (recur)))
    ;; Not all observers done - block until next event arrives
    (do
      (.take (:events batch))  ; blocks, zero CPU, wakes on .put()
      ;; event is consumed by .take(), need to process it
      ;; actually, use .poll() in inner loop after .take() returns
      ;; simpler: put event back or restructure
      (recur))))
```

Cleaner version using `.take()` directly:

```clojure
(loop []
  ;; Block until an event arrives (zero CPU while waiting)
  (let [event (.take (:events batch))]
    (process-event! context event)
    ;; Drain any additional available events (non-blocking)
    (loop []
      (when-let [e (.poll (:events batch))]
        (process-event! context e)
        (recur)))
    ;; Check if all observers have completed
    (if (= (:observers batch) @(:completed batch))
      ;; Final non-blocking drain for cascading events
      (loop []
        (when-let [e (.poll (:events batch))]
          (process-event! context e)
          (recur)))
      ;; More observers pending - wait for next event
      (recur))))
```

Properties:
- **Zero polling**: `.take()` blocks the thread with zero CPU usage
- **Instant wake**: `.put()` from a worker thread wakes the blocked thread
- **No timeout**: Waits as long as needed (bounded by observer completion)
- **Cascading support**: Inner `.poll()` loop drains synchronous cascades

### 4.2 CLJS: Callback-Based

On CLJS, there's no thread pool and no blocking. Everything runs on the
single event loop. Async work uses `setTimeout(0)` (microtasks).

```clojure
(defn process-batch-cljs! [context batch callback]
  (let [check! (fn check! []
                 ;; Drain all available events
                 (let [events @(:events batch)]
                   (reset! (:events batch) [])
                   (doseq [e events]
                     (process-event! context e)))
                 ;; Check if done
                 (if (= (:observers batch) @(:completed batch))
                   ;; Final drain and callback
                   (let [remaining @(:events batch)]
                     (reset! (:events batch) [])
                     (doseq [e remaining]
                       (process-event! context e))
                     (callback))
                   ;; Schedule next check after microtasks drain
                   (js/setTimeout check! 0)))]
    (check!)))
```

This is **not polling** in the traditional sense - `setTimeout(0)` yields to
the event loop, allowing pending microtasks (child spin completions) to run
before we check again.

### 4.3 Portable Interface

```clojure
(defprotocol PBatchQueue
  (batch-put! [q event])
  (batch-drain! [q] "Non-blocking drain of all available events")
  (batch-await! [q] "Block/yield until at least one event available"))

;; JVM implementation: wraps LinkedBlockingQueue
;; CLJS implementation: wraps atom + setTimeout callback
```

## 5. Design: Level-Parallel Execution

### 5.1 The Insight

The FRP dependency graph is a DAG. A topological sort produces **levels**
where all spins within a level are independent (form an antichain):

```
Level 0: signal-S                     (source)
Level 1: spin-A, spin-B, spin-D      (independent observers)
Level 2: spin-C                       (depends on A and B)
Level 3: spin-E                       (depends on C and D)
```

Within each level, all spins can execute **in parallel**. Between levels,
there is a strict ordering constraint (barrier).

This is Bulk Synchronous Parallel (BSP) applied to FRP propagation.

### 5.2 Phase 1: Parallel Track Resumption

```clojure
;; Current: sequential
(doseq [spin-id observers]
  (resume-track-continuation! context spin-id signal-id))

;; Proposed: parallel on thread pool
(let [latch (CountDownLatch. (count observers))]
  (doseq [spin-id observers]
    (execute! executor
      (fn []
        (binding [ec/*execution-context* context
                  ec/*spin-id* spin-id
                  pcps-async/*in-trampoline* false]
          (try
            (resume-track-continuation! context spin-id signal-id)
            (finally
              (.countDown latch)))))))
  ;; Wait for all observers to be resumed (not completed - just resumed)
  (.await latch))
```

Note: this waits for all resumptions to **start**, not complete. Observers
that spawn async children will post to the batch queue when done.

### 5.3 Why This Is Safe

When A and B resume concurrently on different threads:

| Operation | Thread Safety | Reason |
|-----------|--------------|--------|
| Read signal state | Safe | Atomic deref |
| Write spin tracking | Safe | `swap!` with retry on different paths |
| Create child spins | Safe | `swap!` on shared `:nodes` map |
| Enqueue to batch | Safe | `LinkedBlockingQueue.put()` is thread-safe |
| Mark spin dirty/running | Safe | `swap!` on per-spin node |
| Register continuation | Safe | `swap!` on `:continuations` map |
| Track signal dependency | Safe | `swap!` on `:spin-tracking` |

The state backend (`AtomBackend`) uses `swap!` for all writes, which provides
atomic compare-and-swap with automatic retry. Different spins write to
different paths in the state map, so contention is low.

### 5.4 What About `*spin-id*`?

`*spin-id*` MUST remain a dynamic binding because multiple spins execute
concurrently in the same context. Each thread binds its own `*spin-id*`
via `binding` before executing a spin body. This provides thread-local
isolation without any shared mutable state.

This is already how `parallel` works - each child spin runs on the thread
pool with its own `*spin-id*` binding.

### 5.5 Phase 2: Completion Processing

Phase 2 processes completion events from the batch queue. These events
may trigger more work (await continuations resume, which may spawn more
spins). The cascading completions form the **next levels** of the DAG.

```
Phase 1: resume A, B, D in parallel
  → A completes (posts to batch)
  → B completes (posts to batch)
  → D completes (posts to batch)

Phase 2, round 1: process A-completion, B-completion, D-completion
  → C's await for A fires, C's await for B fires → C resumes
  → C completes (posts to batch)

Phase 2, round 2: process C-completion
  → E's await for C fires, E's await for D fires → E resumes
  → E completes (posts to batch)

Phase 2, round 3: process E-completion
  → no more dependents → batch done
```

Future optimization: within Phase 2, independent completions could also
be processed in parallel. For now, sequential processing is simpler and
sufficient (Phase 1 parallelism is the bigger win).

### 5.6 Performance Characteristics

For a graph with N independent observers:

| Metric | Current | Proposed |
|--------|---------|----------|
| Phase 1 latency | O(sum of N resumptions) | O(max of N resumptions) |
| Phase 2 wait | O(100ms) polling worst case | O(actual completion time) |
| CPU during wait | Busy-loop (wastes cycles) | Blocked (zero CPU) |
| Thread usage | 1 (drain thread) | 1 + N (drain + thread pool) |
| CLJS behavior | Busy-loop (bad) | Yield to event loop (correct) |

## 6. Design: Fork Event Draining

### 6.1 Current Problem

Forked contexts share the parent's drain thread, but have their own event
queue. The parent's drain thread only processes the parent's events. Fork
events are **never drained**, causing 7 test failures (30s timeouts).

### 6.2 Solution: Synchronous Draining for Forks

Forks are used for simulation (create fork, execute spins, collect results,
discard). They don't need background reactivity.

```clojure
(defn restore-snapshot [snapshot-ctx & {:keys [drain-events?]}]
  ;; ... existing restore logic ...
  ;; Mark as synchronous-drain context
  (let [restored (assoc snapshot-ctx
                   :backend atom-backend
                   :drain-mode :synchronous  ; NEW
                   :running nil              ; no background thread
                   :drain-thread nil)]       ; no background thread
    (when drain-events?
      (drain-events! restored nil))
    restored))
```

When events are enqueued in a synchronous-drain context, they are drained
immediately on the calling thread:

```clojure
(defn enqueue-event! [context event]
  (swap-state-args! context [:engine/pending] conj [event])
  (case (:drain-mode context)
    :synchronous (drain-events! context nil)  ; immediate, on calling thread
    (trigger-drain! context (:executor context))))  ; async, on thread pool
```

### 6.3 Fork Context Creation

`fork-context` should also create synchronous-drain contexts by default:

```clojure
(defn fork-context [parent-ctx & opts]
  ;; ... existing fork logic ...
  (->ExecutionContext
    fork-id
    overlay-backend
    parent-ctx
    (:executor parent-ctx)
    merged-bindings
    fork-metadata
    nil    ; no drain thread control (was: share parent's)
    nil    ; no drain thread (was: share parent's)
    :synchronous))  ; NEW: drain mode
```

## 7. Dynamic Bindings: Before and After

### 7.1 Bindings Removed (moved to batch state)

| Binding | Current Purpose | New Location |
|---------|----------------|--------------|
| `*completion-queue*` | Defer completion events | `(:events batch)` in context |
| `*batch-generation*` | Dedup key | `(:generation batch)` in context |
| `*resumed-continuations*` | Prevent duplicate resumptions | `(:resumed-conts batch)` in context |
| `*processed-spins*` | Await fast-path | `(:processed batch)` in context |

### 7.2 Bindings Retained

| Binding | Reason |
|---------|--------|
| `*execution-context*` | Identifies which fork to write to. Essential for concurrent spins in different forks. |
| `*spin-id*` | Identifies which spin is executing. Essential because multiple spins run concurrently in the same context (thread pool). Cannot be a context singleton. |
| `pcps-async/*in-trampoline*` | CPS library internal. Controls whether to establish new trampoline loop on resumption. |

### 7.3 Context `:bindings` Field (unchanged)

The `:bindings` field on ExecutionContext remains a fork-level immutable
config map. Used for:
- `:execution-mode` (`:rebuild` or nil)
- User-defined fork config (HTTP clients, random seeds, etc.)

This is NOT the place for per-spin state because multiple spins share
the same context and would clobber each other.

## 8. Signal Change Processing: Complete Flow

### 8.1 Before (current)

```
1. Dequeue :signal-change event on drain thread
2. Create completion-queue atom
3. Increment batch generation
4. Bind 4 dynamic vars
5. FOR EACH observer (sequential):
     Resume track continuation
     Spin body executes on drain thread
     If sync: completion goes to *completion-queue*
     If async: child on thread pool, captures binding
6. LOOP (poll up to 100ms):
     Drain *completion-queue* atom
     Process completions
     Sleep 1ms, check again
7. Unbind dynamic vars
```

### 8.2 After (proposed)

```
1. Dequeue :signal-change event on drain thread
2. Create Batch in context state (:engine/current-batch)
     - BlockingQueue for events (JVM) / atom + callback (CLJS)
     - Set of expected observer spin-ids
     - Atoms for dedup state
3. Phase 1: Resume observers IN PARALLEL
     FOR EACH observer:
       Submit to thread pool:
         Bind *execution-context*, *spin-id*
         Resume track continuation
         Spin body executes on pool thread
         Completion event → batch queue (via context state lookup)
     Wait for all resumptions to be dispatched
4. Phase 2: Process batch events (NO POLLING)
     LOOP:
       .take() on batch queue (blocks until event arrives, zero CPU)
       Process event (may cascade more events)
       .poll() to drain any synchronous cascades
       IF all observers completed → final drain, exit
5. Clear batch from context state
```

## 9. Affected Code Locations

### 9.1 Files to Modify

| File | Changes |
|------|---------|
| `engine/impl/simple.cljc` | Remove 4 dynamic vars. Rewrite signal-change handler with Batch. Rewrite Phase 2 with BlockingQueue. Add parallel Phase 1. |
| `effects/await.cljc` | Replace `*completion-queue*`/`*processed-spins*` reads with context state lookup. |
| `spin/core.cljc` | `enqueue-completion-event!` reads batch from context state. |
| `engine/context.cljc` | Add `:drain-mode` to ExecutionContext. Change fork/restore to use synchronous draining. |
| `engine/scheduler.cljc` | Simplify binding capture (fewer vars to propagate). |

### 9.2 Files Unchanged

| File | Why |
|------|-----|
| `effects/track.cljc` | Track handler doesn't interact with batch state directly. |
| `spin/combinators.cljc` | Parallel combinator uses `enqueue-completion-event!` which is updated. |
| `signal.cljc` | Signal `batch` macro is orthogonal (collects signal IDs, not engine batching). |
| `engine/core.cljc` | `*spin-id*` and `*execution-context*` unchanged. |

## 10. Migration Plan

### Step 1: Introduce Batch data structure

Add `Batch` record/map and `PBatchQueue` protocol. Write portable
implementations (BlockingQueue for JVM, atom+callback for CLJS).
Unit test the queue in isolation.

### Step 2: Wire batch into signal-change handler

Replace `*completion-queue*` with batch in context state. Keep Phase 1
sequential for now. Replace polling Phase 2 with BlockingQueue drain.
Run full test suite - should fix the polling fragility.

### Step 3: Update await fast-path

Replace `*processed-spins*` and `*completion-queue*` reads in
`effects/await.cljc` with context state lookups. Remove remaining
dynamic bindings.

### Step 4: Fix fork draining

Add `:drain-mode :synchronous` to forked/restored contexts.
Implement synchronous `enqueue-event!` path.
Should fix the 7 failing parallel tests.

### Step 5: Parallel Phase 1

Change sequential `doseq` over observers to parallel dispatch on
thread pool with `CountDownLatch` barrier. This is the performance
win but depends on Steps 1-4 being stable.

### Step 6: Clean up

Remove unused binding capture/restore code for the 4 removed vars.
Simplify scheduler binding propagation.
Update tests that relied on binding state.

## 11. Invariants

These must hold at all times:

1. **Glitch-freedom**: No dependent spin observes a mix of old and new
   values from the same signal-change generation.

2. **Batch atomicity**: All observer completions within a batch are
   processed before the batch ends. No orphaned events.

3. **Causal ordering**: If spin-A's completion triggers spin-B's
   execution, B sees A's result (not a stale cache).

4. **Fork isolation**: Writes in a fork don't affect the parent.
   Events in a fork are processed in the fork's context.

5. **No polling**: The system never busy-waits. It either blocks
   (JVM) or yields to the event loop (CLJS).

6. **Thread safety**: All shared state is accessed via atomic
   operations (`swap!`, `compare-and-set!`, `BlockingQueue`).

## 12. Open Questions

1. **Nested signal changes during batch**: If a resumed observer
   changes another signal, this enqueues a new `:signal-change` event.
   Currently processed after the current batch ends (sequential drain).
   With parallel Phase 1, the new event is enqueued to the engine's
   pending queue, not the batch queue, so ordering is preserved.

2. **Batch timeout**: Should there be a safety timeout on batch
   completion? If an observer's child hangs, the drain thread blocks
   forever. Consider a configurable timeout with error reporting.

3. **Phase 2 parallelism**: Independent completion events could be
   processed in parallel (future optimization). Requires careful
   analysis of `propagate-await-dirty!` thread safety.

4. **CLJS testing**: The CLJS callback-based batch completion needs
   thorough testing with `EventLoopExecutor` and `SynchronousExecutor`.

5. **Rebuild mode interaction**: Rebuild mode re-executes spin bodies
   for side effects. This happens outside batch context and should
   not be affected, but needs verification.
