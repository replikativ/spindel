# Unified subscription design

This is the design that the `experiment/unified-subscription-model` branch
lands. It supersedes the earlier two-stage commit (transient `:spin-tracking`
→ committed `:nodes:deps`) that caused the first-run signal-change gap and
the related Phase 2 deadlock on `Deferred` suspension.

## The principle

**An active subscription is the single source of truth for "X observes Y."**
Observer registration is *eager* — it happens at the moment a body calls
`(track sig)` or `(await child)`, not at body completion. The committed
deps snapshot (`spin.deps`) is kept only as a *diff baseline* so that a
spin which stops tracking some signal between runs gets cleanly
unsubscribed from those signals.

## Engine state shape (after the experiment)

The engine state lives in the backend (`AtomBackend` for root contexts,
`OverlayBackend` for forks, `ImmutableBackend` for snapshots). Some
state is **fork-local** (no fall-through to parent); the rest is
**shared** (overlay fall-through). The `ExecutionContext` defrecord
also carries a small number of per-context fields outside the backend.

### Backend state keys

```
{:nodes {                                                   ; SHARED
   signal-id -> SignalNode{:snapshot :old-snapshot :deltas :generation
                           :deltaable? :observers #{spin-ids}}
                                                            ;   ↑ eager
   spin-id   -> SpinNode{:result :status :completed? :running?
                         :deps {:signals #{} :spins #{}}    ;   diff cache only
                         :observers #{parent-spin-ids}      ;   eager
                         :created-by :created-spins
                         :chain-head}}                      ;   per-spin addressing cursor
                                                            ;   (SpinNodes may also carry an ad-hoc
                                                            ;   :dom-scope when the spin was
                                                            ;   constructed inside DOM scope —
                                                            ;   not a defrecord field)
 :continuations {spin-id -> {cont-id -> cont}}              ; FORK-LOCAL — primary cont store
 :subscriptions {event-key -> {spin-id -> #{cont-ids}}}     ; SHARED — reverse index of conts
 :spin-tracking {spin-id -> {:signals #{} :spins #{}}}      ; SHARED — transient body-run accumulator
 :pending-callbacks {spin-id -> [...]}                      ; SHARED — collapses concurrent
                                                            ;   derefs of an in-flight spin
                                                            ;   into one execution + fan-out
 :atoms {atom-id -> {:value … :watchers #{}}}               ; SHARED — fork-safe runtime atoms

 ;; Engine namespace — drain machinery and timer / event-loop state.
 :engine/pending          [events…]                          ; FORK-LOCAL — single FIFO drain queue
 :engine/current-batch    {:generation :signal-id :resumed-conts :processed}
                                                            ; SHARED — per-signal-change metadata
 :engine/draining?        bool                               ; FORK-LOCAL — drain lock
 :engine/delayed-spins    (sorted-map t -> #{spin-ids})      ; FORK-LOCAL — virtual-time timer queue
 :engine/timer-handles    {spin-id -> handle}                ; FORK-LOCAL — JS-side timers
 :engine/virtual-time     long                               ; SHARED — simulation clock
 :engine/time-mode        :wall|:virtual                     ; SHARED — clock source selection
 :engine/cancelled-tokens #{cancel-tokens}                   ; SHARED — cont cancellation set
                                                            ;   (see §Cont cancellation)

 :addressing {:chain-head <global fallback>}                 ; SHARED — global chain-head only
}                                                           ;   per-spin chain-head is on the SpinNode
```

### ExecutionContext fields (outside the backend)

```
{:fork-id       <unique fork id>
 :backend       <PStateBackend impl — AtomBackend / OverlayBackend / ImmutableBackend>
 :parent-ctx    <parent ExecutionContext or nil>
 :executor      <thread pool / event loop>
 :bindings      <fork-local config, merged with parent's bindings>
 :metadata      <fork metadata: :process-id :fork-depth …>
 :running       <atom: drain-thread liveness>
 :drain-thread  <Thread or nil>
 :drain-signal  <LinkedBlockingQueue (JVM) or nil>
 :drain-active  <atom: count of in-flight drain calls>}
```

Indexes that were removed in this experiment:
- `:spin-outputs`     — wrote-only redundant copy of spin result; nothing
                        read it. Result lives on `:nodes[id]:result`.
- `:await-dependents` — pre-fix eager registration of "parent awaits child"
                        relations. Same set semantics as `child.observers`,
                        which is now eagerly maintained.
- per-batch `:events` queue — was used by Phase 2's `batch-take!` blocking
                        wait. Phase 2 is gone; cascade events flow through
                        the main `:engine/pending` queue and are drained
                        naturally.

## Invariants

For every state transition (committed atomically via `swap-state!`):

- **I1.** `signal.observers` = `(keys (:subscriptions [[:signal sig-id]]))`.
  Both grow when `track-signal-dep!` runs at `(track sig)`. Both shrink
  when a cont is removed (resume truncation / `clear-deps!` /
  `full-cleanup-spin!`).

- **I2.** `spin.observers` = `(keys (:subscriptions [[:spin/complete tid]]))`,
  with the same lifecycle.

- **I3.** `spin.deps` is the snapshot of `spin.tracking` taken at the LAST
  completed body resolve. It is *not* a dispatch primary; it exists only
  so `record-deps!` can compute which signals/spins were tracked in a
  previous run but not in this one, and unregister the spin from their
  observer lists.

- **I4.** `spin.tracking[spin-id]` is non-empty only between body
  invocation (Spin.invoke Case 2 / resume-single-observer /
  re-execute-dirty-parent) and `record-deps!` (called from the body's
  outer resolve). It is also cleared by `clear-deps!` / `full-cleanup-spin!`.

- **I5.** `:running?` on a SpinNode is true from body invocation until
  `cache-result!` fires (body resolution). It does NOT clear on
  suspension — a body suspended on `(await deferred)` is still in-flight.
  This lets `await-drain-complete!` / `deref` correctly detect "work in
  progress" without a Phase 2 wait.

## Lifecycle of a body run

```
Spin.invoke (cache miss) →
  mark-running!                                    ; :running? := true
  invalidate-created-spins!                        ; recursively clear-deps!
  bind *chain-head*, *spin-id*
  spin-fn called
    body executes ─ may suspend at any (track …) or (await …)

  (track sig) →
    base-snap := :spin-tracking[spin-id]
    tracking-snap := base-snap with signal-id conj'd onto :signals  ← Stage 2 fix
    cont := {…, :tracking-snap}
    continuation-add! cont                         ; updates :continuations
                                                   ; AND :subscriptions
    deps-track-signal! spin-id signal-id           ; transient + eager observer
    resume resolve interval                        ; synchronous CPS step

  (await child) →
    deps-track-spin! parent-id child-id            ; transient + eager observer
    case dispatch (Spin / Deferred / Mailbox / fn):
      Spin slow-path:
        cont := await-cont-map (with tracking-snap, chain-head-snap,
                                :awaited-spin strong-ref)
        continuation-add!
        bind child-ctx with awaited spin's DOM scope,
             *spin-id* := awaited-spin-id,
             *chain-head* := (atom (body-start-chain-head awaited-spin-id)),
             *in-trampoline* := false
        call .-spin-fn directly (NOT Spin.-invoke — slow path needs to
          inject child-resolve / child-reject, which -invoke doesn't
          expose. Because -invoke is bypassed, the slow path seeds
          *chain-head* explicitly with the awaited spin's
          body-start cursor; otherwise the child body would inherit
          the parent's chain-head and its vnode addresses would
          shift on every parent re-run from a different track-cont,
          breaking discharge's by-address element lookup.)
        child may complete sync (resume parent inline) or suspend
      Deferred:
        (deferred resolve reject)                  ; resolve held by external

  body completes via resolve →
    cache-result! :ok value                         ; sets :completed? :running? :status
    graph-commit-deps! → record-deps!:
      diff old spin.deps vs spin.tracking
      remove observers for signals/spins dropped between runs
      spin.deps := spin.tracking
      clear spin.tracking
    enqueue-completion-event!                       ; :spin-completion → :engine/pending
    fire user resolve callbacks
```

## Lifecycle of a signal change

```
swap! sig new-value →
  signal node updated (snapshot, generation++)
  enqueue :signal-change → :engine/pending
  trigger-drain!

drain-events! → process-event! :signal-change:
  create batch {:generation :signal-id :resumed-conts :processed}
  observers := ordered-observers sig-id           ; topo sort over signal.observers
                                                   ; (eagerly maintained, includes
                                                   ; first-run-not-yet-committed spins)
  clear-all-await-continuations! at generation boundary
  for each observer in topo order (parallel on JVM for >1):
    earliest cont with [:signal sig-id]
    resume-single-observer! observer cont:
      remove conts with order > cont.order        ; truncation
      re-track skipped signal-ids                 ; preserves accumulator
      mark dirty + :running? true
      invalidate-created-spins!
      bind *chain-head* (atom seeded with cont.chain-head-snap)
      restore :spin-tracking from cont.tracking-snap
      resume-continuation! cont (calls cont.resolve-fn with fresh value)
  clear :engine/current-batch
  drain continues processing cascade events
```

No Phase 2 blocking wait. Cascade `:spin-completion` events enqueue
through the same `:engine/pending` queue and are processed in FIFO order
by the outer drain loop. The single-queue design makes the engine immune
to "wait queue doesn't pump the other queue" deadlocks.

## What this fixes

- **First-run signal-change gap**: a spin in `(track A) → (await x)` where
  A changes during the first suspend now correctly receives the change.
  `signal.observers` is eagerly maintained, so the resume-from-track path
  fires the cont. Body resumes from after the track, runs to completion
  with the fresh A value.

- **Phase 2 deadlock on Deferred**: gone. Observers that suspend on a
  Deferred no longer trap the drain into a `batch-take!` that the
  Deferred's eventual delivery can't reach.

- **`await-drain-complete!` returning early**: fixed by the `:running?`
  semantics change. A body suspended on a Deferred reports as in-flight,
  so the test harness's drain wait sees the work as pending until the
  Deferred resolves and the body completes.

## Cont cancellation (orphaned external callbacks)

When `resume-single-observer!` (or `re-execute-dirty-parent!`) truncates
conts whose `:resolve-fn` had been passed into an external resource —
Deferred's `:pending`, Mailbox's waiters, plain-fn callback registrations
— those resolve closures are still held by the resource. When the
resource later fires, both the OLD body slice and the NEW body slice
(registered by the parent re-run) advance to their respective
outer-resolves. Pure-functional bodies are merely wasteful; bodies
with side effects (DOM mutations, message dispatch, atom swaps)
fire those side effects twice.

**Fix** (stage 4, landed with the Option A redesign):
`effects/await.cljc::cancellable-external-pair` wraps the parent body's
resolve/reject in a cancellation gate. Each call mints a fresh
`cancel-token` (UUID); the wrapped closure resolves
`(ec/current-execution-context)` *at call time* and checks whether
the token is in that context's `:engine/cancelled-tokens` set. The
associated engine cont owns the token via `:cancel!`, which takes
the engine context as a parameter and `swap-state!`'s the token
into that context's set.

**Why this is fork-safe (fork→parent direction):**
`:engine/cancelled-tokens` is regular context state, not a
closure-captured volatile. Reads in a fork that has not yet written
to the path fall through to parent (so a fork inherits parent's
current cancellation set — correct). Once a fork writes, its
overlay holds its own value at the path and shadows parent for
subsequent reads in that fork. The wrapped closure, invoked by
fork's drain, reads fork's view; the same closure invoked by
parent's drain reads parent's view. Cancellations made BY a fork
therefore do **not** leak back into the parent — pinned by
`fork-isolated-cancellation` in `cont_cancellation_test.cljc`.

A precise note on the divergence mechanism: `:engine/cancelled-tokens`
is a depth-1 path, so the OverlayBackend takes its "shallow shared
path" branch (`(swap! overlay-atom update-in path f)`), not the
entity-CoW branch that applies to depth-≥2 shared paths like
`[:nodes spin-id …]`. Practically that means a fork's first write
does NOT pre-copy parent's value into the overlay — fork's `swap!`
sees `nil` and starts a fresh set containing just the fork's token.
After that first write, parent's pre-fork tokens are no longer
visible in fork (the overlay shadows the parent). For the
fork→parent guarantee this is fine; for parent→fork it has a
consequence — see the note below.

Note on the OTHER direction — parent→fork: parent's cancellations
made AFTER the fork was created propagate into the fork while the
fork hasn't written to the cancelled-tokens path yet (reads fall
through). This is the OverlayBackend's parent-following contract
by design — overlay forks track parent's evolving state (signal
observer graph, continuation registry, etc.) precisely because
that's what makes them useful for speculative-with-rebase /
Elle-distributed-consistency-style branching. A cancellation is
a fact about the shared continuation graph, so applying it to
anyone observing that graph is consistent.

**Latent edge case (not currently exercised in production):** the
shallow-path swap means fork's first write does not copy parent's
pre-fork tokens; subsequent reads in fork see only fork-written
tokens. If parent cancelled a cont *before* the fork was created
AND that cont's wrapped resolve closure made it into fork's
gate.:pending at fork time AND fork later cancels a different
cont, the parent-pre-fork closure firing inside fork's drain would
no longer see the parent's pre-fork token and would fire when it
should remain silenced. The existing fork-isolation test does not
exercise this sequence (it cancels in fork only). Cleanest future
fix is to extend OverlayBackend's atomic write path to copy parent's
value into the overlay on first write for shared depth-1 paths
(mirroring the depth-≥2 entity-CoW logic). For workloads that
want fully isolated cancellation today, use `snapshot-context`
instead of `fork-context` — a snapshot is a new root with
`ImmutableBackend`, no parent, no fall-through.

Compare to a `volatile!` captured in the closure (the original
stage-4 design): the volatile is a single mutable object shared by
every fork that inherits the cont, defeating fork isolation —
cancellation by one fork silently disables the same await in the
parent and sibling forks. The state-backed token approach removes
the shared mutable.

**Self-cleaning:** the wrapped closure / `post-inline!`
skip-cancelled-waiter path drops their own token from
`:engine/cancelled-tokens` after firing (or after being skipped).
External resources deliver each consumer's closure at most once,
so once a closure has been dispatched the token has no other
firing path. The set's steady-state size is bounded by the count
of cancelled closures that *never* get delivered (e.g. an
abandoned Deferred) — a tiny constant in practice.

**Where `:cancel!` fires:** only at TRUNCATION sites, where the
spin stays alive and re-runs (so a new cont may race with the
orphaned external closure).

Active sites (fire `:cancel!`):
- `resume-single-observer!`  — truncates conts with order > resumed
- `re-execute-dirty-parent!` — same truncation pattern
- `add-continuation!`        — cancels a cont being displaced by a
                               re-await at the same deterministic
                               cont-id

Teardown sites (do NOT fire `:cancel!`):
- `clear-all-await-continuations!` — generation boundary cleanup; the
                                     spin is already completed and not
                                     running, no new cont will compete
- `clear-deps!`                    — invalidation; teardown path
- `full-cleanup-spin!`             — GC; teardown path

The teardown-site exclusion was added after a regression hunt
against a ~27% flake rate in async tests: the JVM Cleaner thread
invoking `full-cleanup-spin!` had been firing `:cancel!` on
legitimately in-flight resolves whose Spin object was GC'd by the
test before the deferred delivered, silently silencing the
resolve. Restricting `:cancel!` to truncation sites where the spin
stays alive eliminated the flake.

Awaits on a Spin (slow path) do not need this treatment: the child's
completion enqueues a `:spin-completion` event whose dispatch looks up
the parent cont in `:subscriptions[[:spin/complete child-id]]`; if the
cont has been removed, the lookup returns nil and the dispatch is a
no-op. The cancellation infrastructure exists only for external
resources that hold raw resolve closures (no engine indirection).

Tests in `engine/cont_cancellation_test.cljc`:
- `no-double-side-effect-after-track-resume-mid-deferred-await` —
  pins the original orphaned-callback fix.
- `no-mailbox-message-loss-after-track-resume-mid-mailbox-await` —
  pins the Mailbox cancellation fix below.
- `fork-isolated-cancellation` — pins the Option A fork-isolation
  guarantee. Forks the context after the parent suspended on
  `(await gate)`, cancels in the fork (via signal change), delivers
  the gate in BOTH parent and fork, asserts the body's side effect
  fired exactly once in each — proving the cancellation didn't bleed
  across fork boundaries.

## Mailbox cancellation (D1-A)

The cancellation gate alone is sufficient for Deferred: a Deferred
delivers a single value to ALL pending resolves, so an orphaned
gate-no-op'd closure is harmless — the new closure (registered by
the parent's re-run) also receives the value and the body advances
correctly.

Mailbox is different. A producer's `post-inline!` consumes EXACTLY
ONE waiter per `post` from `state-atom.waiters`. If the consumed
waiter's wrapped resolve is cancelled (gate flipped), it no-ops —
but the message is gone from the queue. The next legitimate waiter
(registered by the parent's re-run) waits forever. Silent message
loss.

**Fix (D1-A from the design discussion, landed):**

1. `cancellable-external-pair` now returns the cancel-token as a
   third return value: `[wr wj cancel-token]`.

2. New dynamic var `engine/core.cljc::*external-await-cancel-token*`
   carries the token from `await-handler`'s Mailbox dispatch branch
   into the Mailbox 2-arity call site. The dispatch branch binds
   the var:
   ```
   (binding [ec/*external-await-cancel-token* cancel-token]
     (awaitable wr wj))
   ```

3. Mailbox 2-arity (`spin/sync.cljc`) reads the var when adding a
   waiter to `state-atom.waiters` and stores it on the waiter
   struct: `{:spin-id … :cancel-token … :resolve …}`.

4. `post-inline!` (`engine/impl/simple.cljc`) reads
   `:engine/cancelled-tokens` once per call from the current
   context, and adds a `cond` branch to its skip-cancelled-waiter
   loop: if the waiter's `:cancel-token` is in the set, recur with
   the same `msg` to try the next waiter (or push to `:queue` if no
   more waiters). The message is NOT consumed.

The dynamic var lives in `engine.core` rather than `effects.await`
to avoid a require cycle from `spin/sync.cljc` to
`effects/await.cljc`. Sync.cljc already requires engine.core for
`*spin-id*`.

Deferred and plain-fn awaits ignore the var (don't bind it; nil
default). They don't need it because their resource semantics
deliver to all pending closures (Deferred) or don't pop from a
waiter list at all (plain-fn).

## Open follow-ups

- The `:engine/current-batch` field could potentially be folded into a
  thread-local; the current shared-state form is convenient for forks
  but every readers does so within the signal-change handler call stack.
