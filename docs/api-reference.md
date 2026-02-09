# API Reference

Namespace-by-namespace listing of all public functions and macros.

## `spindel.core`

Convenience re-export namespace. All functions below are also available from their originating namespaces.

### Macros

| Macro | Description |
|-------|-------------|
| `(spin & body)` | Create a cached reactive spin with CPS transformation |
| `(signal initial-value)` | Create a reactive signal with deterministic ID |
| `(batch & body)` | Batch signal updates into a single propagation |
| `(gen-aseq & body)` | Generate a lazy async sequence using `yield` |
| `(for [bindings body])` | Async sequence comprehension with spindel effects |

### Effects

| Function | Description |
|----------|-------------|
| `(await spin-or-deferred)` | Suspend until value available, track dependency |
| `(track signal-ref)` | Read signal with dual perspective (new/old/deltas) |
| `(yield value)` | Emit value in async sequence (inside `gen-aseq`) |

### Runtime

| Function | Description |
|----------|-------------|
| `(create-execution-context & opts)` | Create root execution context |
| `(fork-context parent & opts)` | Create O(1) forked context |
| `(snapshot-context ctx & opts)` | Create immutable snapshot |
| `(restore-snapshot ctx & opts)` | Restore snapshot to live context |
| `(stop-context! ctx)` | Stop background drain thread |
| `(serialize-context ctx)` | Serialize to EDN |
| `(deserialize-context edn executor)` | Deserialize from EDN |

### Combinators

| Function | Description |
|----------|-------------|
| `(parallel & spins)` | Execute concurrently, return vector of results |
| `(race & spins)` | Return first to complete, cancel losers |
| `(sleep ms)` / `(sleep ms val)` | Complete after delay |
| `(timeout spin ms fallback)` | Race against deadline |
| `(debounce source ms)` | Wait for quiet period |
| `(throttle source hz merge-fn)` | Limit frequency |
| `(sample source ms)` | Poll at fixed interval |
| `(relieve source)` | Drop intermediate values |
| `(accumulate signal merge-fn)` | Delta-preserving accumulation |

### Sync

| Function | Description |
|----------|-------------|
| `(deferred)` | Create single-assignment deferred value |
| `(deliver! d value)` | Deliver value from external context |
| `(mailbox)` | Create FIFO message queue |
| `(post! mbx msg)` | Post message from external context |
| `(never)` | Spin that never completes |

### Deltaable

| Function | Description |
|----------|-------------|
| `(deltaable-vector v)` | Create delta-tracking vector |
| `(deltaable-map m)` | Create delta-tracking map |
| `(deltaable-set s)` | Create delta-tracking set |

### Pub/Sub

| Function | Description |
|----------|-------------|
| `(mult source)` | Create fan-out mult |
| `(tap mult buffer)` | Create tap on mult |
| `(untap mult tap)` | Remove tap |
| `(pub source topic-fn)` | Create topic-routed pub |
| `(sub pub topic & opts)` | Subscribe to topic |
| `(unsub pub topic sub)` | Unsubscribe |
| `(fixed-buffer n)` | Fixed-size buffer |
| `(dropping-buffer n)` | Dropping buffer |
| `(sliding-buffer n)` | Sliding buffer |

---

## `spindel.engine.core`

Core engine bindings and state access functions.

### Dynamic Vars

| Var | Description |
|-----|-------------|
| `*execution-context*` | Current execution context (bind via `with-context` or `binding`) |
| `*spin-id*` | Current spin ID during execution |
| `*worker-id*` | Worker ID inside engine workers |
| `*yield-handler*` | Yield handler for async sequence generation |

### Context Binding

| Function | Description |
|----------|-------------|
| `(with-context ctx & body)` | Bind execution context for body (macro on CLJ, fn on CLJS) |
| `(current-execution-context)` | Return bound context (throws if unbound) |
| `(execution-context-bound?)` | Check if context is bound |

### State Access

| Function | Description |
|----------|-------------|
| `(get-state path)` | Non-transactional read at path |
| `(swap-state! path f)` | Atomically update state at path |
| `(swap-state-args! path f & args)` | Atomically update with extra args |
| `(cas-state! path old new)` | Compare-and-set at path |

### Spin Operations

| Function | Description |
|----------|-------------|
| `(spin-register! spin-id meta)` | Register spin with runtime |
| `(spin-mark-dirty! spin-id)` | Mark spin as dirty |
| `(spin-cache-result! spin-id result)` | Cache result |
| `(spin-current-result spin-id)` | Get cached result |
| `(spin-result-clean? spin-id)` | Check if cached result is clean |
| `(spin-result-dirty? spin-id)` | Check if cached result is dirty |
| `(current-spin-id)` | Get current spin ID |
| `(spin-is-cancelled?)` | Check if current spin is cancelled |

### Dependency Tracking

| Function | Description |
|----------|-------------|
| `(deps-track-signal! spin-id signal-id)` | Record signal dependency |
| `(deps-track-spin! parent child)` | Record spin dependency |
| `(graph-commit-deps! spin-id)` | Commit tracked dependencies |
| `(graph-clear-deps! spin-id)` | Clear spin from graph |
| `(graph-ordered-observers signal-id)` | Get ordered observer list |

### Continuation Operations

| Function | Description |
|----------|-------------|
| `(continuation-add! spin-id cont)` | Add continuation (auto-captures bindings) |
| `(continuation-remove! spin-id cont-id)` | Remove continuation |
| `(continuation-earliest spin-id signal-id)` | Get earliest continuation |
| `(continuation-resume! spin-id cont resume-fn)` | Resume continuation |

### Scheduling

| Function | Description |
|----------|-------------|
| `(get-executor)` | Get executor for spin scheduling |
| `(schedule-spin-execution! spin-fn)` | Schedule spin for execution |
| `(schedule-delayed-execution! ms spin-fn)` | Schedule after delay |
| `(enqueue-event! event)` | Enqueue engine event |
| `(make-handler ctx handler-fn)` | Create auto-binding event handler |

---

## `spindel.engine.context`

Execution context lifecycle management. See [Forking](forking.md) for usage guide.

### Creation

| Function | Description |
|----------|-------------|
| `(create-execution-context & opts)` | Create root context |
| `(fork-context parent & opts)` | Create O(1) fork with overlay |
| `(create-simulation-context & opts)` | Create deterministic test context |

### Lifecycle

| Function | Description |
|----------|-------------|
| `(stop-context! ctx)` | Stop drain thread (no-op on forks) |
| `(close-context! ctx)` | Stop drain + close executor |

### Accessors

| Function | Description |
|----------|-------------|
| `(root-context? ctx)` | True if root (no parent) |
| `(fork-depth ctx)` | Fork depth (0 for root) |
| `(get-fork-id ctx)` | Fork ID |
| `(get-parent-ctx ctx)` | Parent context (nil for root) |
| `(get-metadata ctx)` | Fork metadata |
| `(get-executor ctx)` | Executor |
| `(get-bindings ctx)` | Fork-local bindings |

### Execution Mode

| Function | Description |
|----------|-------------|
| `(get-execution-mode ctx)` | Get mode (nil, :normal, :rebuild) |
| `(set-execution-mode ctx mode)` | Return new context with mode set |
| `(rebuild-mode? ctx)` | True if in rebuild mode |

### Snapshot & Serialization

| Function | Description |
|----------|-------------|
| `(snapshot-context ctx & opts)` | Create immutable snapshot |
| `(restore-snapshot ctx & opts)` | Restore to live context |
| `(serialize-context ctx)` | Serialize to EDN string |
| `(deserialize-context edn executor)` | Deserialize from EDN |

### Rebuild

| Function | Description |
|----------|-------------|
| `(prepare-rebuild-context ctx & opts)` | Prepare for rebuild |
| `(finalize-rebuild-context ctx & opts)` | Finalize after rebuild |
| `(with-rebuild-context ctx opts & body)` | Execute body in rebuild mode |

### Virtual Time

| Function | Description |
|----------|-------------|
| `(get-time-mode ctx)` | :virtual or :real |
| `(set-time-mode! ctx mode)` | Set time mode |
| `(current-time ctx)` | Current time (virtual or real) |
| `(advance-time! ctx ms)` | Advance virtual time, process events |

### Fork Lineage

| Function | Description |
|----------|-------------|
| `(get-process-id ctx)` | Elle-compatible process ID |
| `(get-parent-process-id ctx)` | Parent's process ID |
| `(get-fork-lineage ctx)` | Vector of process IDs root→current |

---

## `spindel.signal`

Reactive signals with delta tracking.

| Function/Macro | Description |
|----------------|-------------|
| `(signal initial-value)` | Create signal with deterministic ID (macro) |
| `(batch & body)` | Batch signal updates (macro) |
| `(deref-signal sig)` | Non-reactive deref |
| `(get-signal-value sig)` | Read current value |
| `(get-signal-state sig)` | Get full signal state |
| `(get-signal-detailed sig)` | Get value as Interval |
| `(clear-signal-deltas! sig)` | Clear consumed deltas |
| `(swap-signal-changed? sig f & args)` | Swap and return changed? |
| `(signal-interval value)` | Create Interval from value |
| `(ensure-signal-initialized! sig)` | Initialize signal in runtime |

Signals implement `IDeref` (`@`), `IAtom` (`swap!`, `reset!`).

---

## `spindel.atom`

Fork-safe atoms stored in the execution context.

| Function | Description |
|----------|-------------|
| `(atom initial-value & opts)` | Create atom (uses `*execution-context*`) |
| `(create-atom initial-value & opts)` | Create atom with explicit context |

Atoms implement `IDeref` (`@`), `IAtom` (`swap!`, `reset!`), `IRef` (`add-watch`, `remove-watch`).

---

## `spindel.semaphore`

Fork-safe semaphores for concurrent access control.

| Function | Description |
|----------|-------------|
| `(semaphore max-permits)` | Create semaphore (uses `*execution-context*`) |
| `(create-semaphore ctx max-permits)` | Create with explicit context |
| `(acquire sem)` | Returns spin completing on permit acquisition |
| `(release sem)` | Release permit, wake next waiter |
| `(holding sem spin)` | Execute spin with permit (auto-release) |

Semaphores implement `IDeref` (`@sem` returns available permits).

---

## `spindel.spin.core`

Spin type, lifecycle, and error handling.

### Spin Type

| Function | Description |
|----------|-------------|
| `(make-spin spin-fn)` | Create spin with generated ID |
| `(make-spin spin-fn spin-id)` | Create spin with explicit ID |
| `(register-cleanup! obj cleanup-fn)` | Register GC cleanup |

### Result Type

| Function | Description |
|----------|-------------|
| `(ok value)` | Create success result |
| `(error err)` | Create error result |
| `(ok? result)` | True if success |
| `(error? result)` | True if error |
| `(unwrap result)` | Get value or throw |
| `(match result ok-fn err-fn)` | Pattern match on result |

### Error Handling

| Function | Description |
|----------|-------------|
| `(attempt spin)` | Capture errors as functions |
| `(absolve spin)` | Unwrap captured errors |
| `(cancel-spin! spin)` | Cancel spin and observers |
| `(spin-cancelled? spin)` | Check if cancelled |
| `(spin-failed? spin)` | Check if failed |
| `(cleanup-spin! spin)` | Manually remove from runtime |
| `(abort-spin-chain! spin-id err)` | Abort spin and observers |

### CPS Helpers

| Function | Description |
|----------|-------------|
| `(resume cont-fn value)` | Resume continuation (handles trampolining) |

### Constants

| Constant | Description |
|----------|-------------|
| `incomplete` | Sentinel for suspended spin |
| `spin-cancelled` | Cancellation marker |

---

## `spindel.spin.cps`

CPS transformation macros.

| Macro | Description |
|-------|-------------|
| `(spin & body)` | Create cached reactive spin with CPS transformation |
| `(effect & body)` | Create effect-only spin (for side effects, returns nil) |

---

## `spindel.spin.combinators`

Spin composition and rate control. See [Combinators](combinators.md).

| Function | Description |
|----------|-------------|
| `(parallel & spins)` | Execute concurrently, return vector |
| `(race & spins)` | First to complete wins |
| `(sleep ms)` / `(sleep ms val)` | Time delay |
| `(timeout spin ms fallback)` | Deadline with fallback |
| `(debounce source ms)` | Quiet period |
| `(throttle source hz merge-fn)` | Max frequency |
| `(sample source ms)` | Fixed interval polling |
| `(relieve source)` | Drop intermediate values |
| `(accumulate signal merge-fn)` | Delta-preserving accumulation |

---

## `spindel.spin.sync`

Synchronization primitives.

| Function | Description |
|----------|-------------|
| `(deferred)` | Create single-assignment deferred |
| `(create-deferred ctx)` | Create with explicit context |
| `(deliver! d value)` | Deliver from external context |
| `(mailbox)` | Create FIFO message queue |
| `(create-mailbox ctx)` | Create with explicit context |
| `(post! mbx msg)` | Post from external context |
| `(never)` | Spin that never completes |

---

## `spindel.effects.await`

| Function | Description |
|----------|-------------|
| `(await spin-or-deferred)` | Suspend until value available |
| `(await-handler awaitable spin-id loc resolve reject)` | Direct handler |
| `(reactive-spin? x)` | True if x is a Spin |

---

## `spindel.effects.track`

| Function | Description |
|----------|-------------|
| `(track signal-ref)` | Read signal with dual perspective |
| `(track-handler trackable spin-id loc resolve reject)` | Direct handler |
| `(signal-ref? x)` | True if x is a SignalRef |

---

## `spindel.effects.yield`

| Function | Description |
|----------|-------------|
| `(yield value)` | Emit value in async sequence |

---

## `spindel.engine.effects`

Effect registration system.

| Function | Description |
|----------|-------------|
| `(register-effect-by-symbol! sym handler adapter)` | Register effect |
| `(register-effect-by-symbol! sym handler adapter direct-sym)` | Register with direct handler |
| `(get-effect-syntax)` | Get effect registry map |
| `(dispatch-symbol-call ctx sym args spin-id loc resolve reject)` | Dispatch effect |
| `(check-cancellation! spin-id)` | Check/throw if cancelled |
| `(one-arg->awaitable-map args)` | Standard adapter: `(effect x)` to `{:awaitable x}` |
| `(type-error effect-name expected actual)` | Create type error |

### Protocol: `PEffectHandler`

```clojure
(handle-effect [this context args resolve reject])
```

---

## `spindel.seq.core`

Async sequence generation and consumption.

| Function/Macro | Description |
|----------------|-------------|
| `(gen-aseq & body)` | Generate lazy async sequence (macro) |
| `(for [bindings body])` | Async comprehension (macro) |
| `(yield value)` | Emit value in gen-aseq |
| `(anext seq)` | Get next `[value rest]` or nil |
| `(into coll seq)` | Collect all into collection |

---

## `spindel.incremental.deltaable`

Delta-tracking collections. See [Incremental](incremental.md).

| Function | Description |
|----------|-------------|
| `(deltaable-vector v)` | Wrap vector |
| `(deltaable-map m)` | Wrap map |
| `(deltaable-set s)` | Wrap set |
| `(deltaable-value v)` | Wrap simple value |
| `(get-deltas x)` | Get accumulated deltas |
| `(has-deltas? x)` | True if non-empty deltas |
| `(clear-deltas x)` | Return copy with deltas cleared |
| `(wrap-deltaable x)` | Wrap as deltaable (shallow) |
| `(unwrap-deltaable x)` | Unwrap to plain collection |
| `(unwrap x)` | Get raw value |
| `(apply-delta coll delta)` | Apply single delta to collection |
| `(compact-deltas deltas)` | Remove redundant operations |
| `(merge-deltas & seqs)` | Concatenate delta sequences |
| `(transduce xf init deltas)` | Transduce deltas |
| `(map f)` | Delta transducer: transform values |
| `(filter pred)` | Delta transducer: filter with enter/exit |
| `(remove pred)` | Delta transducer: inverse filter |
| `(keep f)` | Delta transducer: transform + filter |

---

## `spindel.incremental.interval`

Interval abstraction for incremental computation.

| Function | Description |
|----------|-------------|
| `(interval new)` / `(interval old new)` / `(interval old new deltas)` | Create interval |
| `(interval? x)` | Type check |
| `(as-interval x)` | Coerce to interval |
| `(as-interval-with-old prev current)` | Coerce with previous baseline |
| `(changed? iv)` | True if old != new |
| `(static? iv)` | True if no old and no deltas |
| `(derive-interval prev-output new deltas)` | Create derived interval |
| `(merge-intervals acc new)` | Merge intervals (associative) |

### Protocol: `PInterval`

```clojure
(get-old this)     ;; baseline value
(get-new this)     ;; current value
(get-deltas this)  ;; delta sequence
(has-deltas? this) ;; true if pending
(commit this)      ;; end interval (new→old, clear deltas)
```

---

## `spindel.incremental.combinators`

Incremental operations on intervals.

| Macro | Description |
|-------|-------------|
| `(ifilter pred source)` | Incremental filter |
| `(imap f source)` | Incremental map |
| `(ireduce rf init source)` | Incremental reduce |
| `(ireduce rf init enter exit source)` | Reduce with custom enter/exit |
| `(ifor-each key-fn transform source)` | Keyed per-item transformation |
| `(islice window source)` | Windowed view for virtual scroll |

---

## `spindel.pubsub.mult`

Fan-out broadcasting. See [Pub/Sub](pubsub.md).

| Function | Description |
|----------|-------------|
| `(mult source-aseq)` | Create mult |
| `(tap mult)` / `(tap mult buffer)` / `(tap mult buffer close?)` | Create tap |
| `(untap mult tap)` | Remove tap |
| `(mult-pump mult)` | Get pump spin |
| `(mult-closed? mult)` | True if source exhausted |
| `(tap-closed? tap)` | True if tap closed |

---

## `spindel.pubsub.pub`

Topic-based routing.

| Function | Description |
|----------|-------------|
| `(pub source topic-fn)` / `(pub source topic-fn buf-fn)` | Create pub |
| `(sub pub topic)` / `(sub pub topic buffer)` / `(sub pub topic buffer close?)` | Subscribe |
| `(unsub pub topic tap)` | Unsubscribe |
| `(unsub-all pub)` | Unsubscribe all topics |
| `(pub-closed? pub)` | True if source exhausted |

---

## `spindel.pubsub.buffer`

Buffer implementations.

| Function | Description |
|----------|-------------|
| `(fixed-buffer n)` | Blocks when full |
| `(dropping-buffer n)` | Never blocks, drops new |
| `(sliding-buffer n)` | Never blocks, drops oldest |
| `(full? buf)` | True if at capacity |
| `(buffer-empty? buf)` | True if no items |
| `(unblocking? buf)` | True if never blocks |

### Protocol: `PBuffer`

```clojure
(full? buffer)      ;; capacity check
(add! buffer item)  ;; enqueue
(remove! buffer)    ;; dequeue oldest
(close-buf! buffer) ;; cleanup
```

---

## `spindel.sci.boundary`

SCI integration — functional API. See [SCI Integration](sci-integration.md).

| Function | Description |
|----------|-------------|
| `(create-spindel-sci-context opts)` | Create SCI context with spindel support |
| `(wrap-spin-for-sci task runtime)` | Wrap native spin as BoundaryTask |
| `(make-spin-for-sci spin-fn id runtime)` | Create spin from SCI context |

### Options for `create-spindel-sci-context`

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `:runtime` | ExecutionContext | required | Execution context |
| `:expose-runtime-state?` | boolean | `false` | Expose state access |
| `:native-spins` | map | `{}` | `{sym → spin}` auto-wrapped |

---

## `spindel.sci.macro`

SCI integration — full macro support.

| Function | Description |
|----------|-------------|
| `(create-spin-macro-context opts)` | Create SCI context with spin macro |
| `(eval-spin sci-ctx code-str)` | Evaluate, return Spin |
| `(eval-and-deref sci-ctx code-str)` | Evaluate and deref |

### Options for `create-spin-macro-context`

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `:runtime` | ExecutionContext | required | Execution context |
| `:native-spins` | map | `{}` | `{sym → spin}` auto-wrapped |
| `:expose-track?` | boolean | `true` | Include track effect |

---

## `spindel.sci.core`

SCI support utilities.

| Function | Description |
|----------|-------------|
| `(load-partial-cps! sci-ctx)` | Load CPS runtime into SCI |
| `(common-classes)` | Standard class allowlist for SCI |

---

## `spindel.distributed.core`

Distributed computing bridge.

### Spin/Channel Conversion

| Function | Description |
|----------|-------------|
| `(spin->chan spin)` | Convert spin to core.async channel |
| `(chan->spin ch)` | Convert channel to spin |

### Context Registry

| Function | Description |
|----------|-------------|
| `(register-context! id ctx)` | Register context for remote access |
| `(unregister-context! id)` | Remove context |
| `(get-context id)` | Look up context |
| `(list-contexts)` | List registered IDs |

### Remote Spin Registry

| Function | Description |
|----------|-------------|
| `(register-remote-spin! name factory)` | Register remote spin factory |
| `(get-remote-spin name)` | Look up factory |

### Peer Management

| Function | Description |
|----------|-------------|
| `(set-system-peer! peer)` | Set kabel peer |
| `(get-system-peer)` | Get current peer |

### Response Handling

| Function | Description |
|----------|-------------|
| `(register-response-handler! id callback)` | Register response callback |
| `(unregister-response-handler! id)` | Remove handler |
| `(get-response-handler id)` | Look up handler |
| `(handle-response! response)` | Dispatch response |

---

## `spindel.distributed.macros`

Distributed function definition.

| Macro | Description |
|-------|-------------|
| `(defn-spin-remote name [params] & body)` | Define distributed function |
| `(spin-remote scope [explicit-args] & body)` | Execute body on remote peer |

`scope` is either a `peer-id` or `[peer-id context-id]`.

All free variables in `spin-remote` body must be declared in the explicit args vector (compile-time validation).
