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

```
{:nodes {
   signal-id -> SignalNode{:snapshot :old-snapshot :deltas :generation
                            :observers #{spin-ids}}        ; ← eager
   spin-id   -> SpinNode{:result :status :completed? :running?
                          :deps {:signals #{} :spins #{}}   ; ← diff cache
                          :observers #{parent-spin-ids}     ; ← eager
                          :created-by :created-spins
                          :dom-scope}}
 :continuations {spin-id -> {cont-id -> cont}}              ; primary cont store
 :subscriptions {event-key -> {spin-id -> #{cont-ids}}}     ; reverse index of conts
 :spin-tracking {spin-id -> {:signals #{} :spins #{}}}      ; transient body-run accumulator
 :pending-callbacks {spin-id -> [...]}                      ; deref / spawn coordination
 :engine/pending [events...]                                ; single FIFO drain queue
 :engine/current-batch {:generation :signal-id :resumed-conts :processed}
                                                            ; per-signal-change metadata
 :engine/draining? bool
 :addressing {…}                                            ; chain-head etc.
 :bindings {…}}
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
        run child-spin-fn (may complete sync, may suspend)
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

**Why this is fork-safe:** `:engine/cancelled-tokens` is regular
context state, not a closure-captured volatile. Fork creation's
overlay starts empty; reads fall through to parent (so a fork
inherits parent's cancellations — correct). Fork's first write to
the set triggers copy-on-write and the parent / fork sets diverge.
The wrapped closure, invoked by a drain in fork's context (which
binds `*execution-context*` to fork's context), reads fork's set.
The same closure, invoked by parent's drain, reads parent's set.
Cancellations in one fork do **not** leak across fork boundaries.

Compare to a `volatile!` captured in the closure (the original
stage-4 design): the volatile is a single mutable object shared by
every fork that inherits the cont, defeating fork isolation —
cancellation by one fork silently disables the same await in the
parent and sibling forks. The state-backed token approach removes
the shared mutable.

**Trade-off — slow leak:** `:engine/cancelled-tokens` grows
monotonically over a context's lifetime; one entry per cancellation
forever. For a long-running app this is a slow memory leak bounded
by total cancellation count (not by concurrent in-flight awaits).
Documented as an open follow-up below. A future improvement could
pair token lifetime with cont lifetime by removing the token when
the cont is removed.

Every cont-removal site in `engine/impl/simple.cljc` calls
`:cancel!` on every removed cont before dissociating, passing the
engine context:

- `resume-single-observer!`            — truncates conts with order > resumed
- `re-execute-dirty-parent!`           — same truncation pattern
- `clear-all-await-continuations!`     — generation boundary cleanup
- `clear-deps!`                        — invalidation
- `full-cleanup-spin!`                 — GC
- `add-continuation!`                  — cancels a cont being displaced
                                         by a re-await at the same
                                         deterministic cont-id

Awaits on a Spin (slow path) do not need this treatment: the child's
completion enqueues a `:spin-completion` event whose dispatch looks up
the parent cont in `:subscriptions[[:spin/complete child-id]]`; if the
cont has been removed, the lookup returns nil and the dispatch is a
no-op. The cancellation infrastructure exists only for external
resources that hold raw resolve closures (no engine indirection).

Tests in `engine/cont_cancellation_test.cljc`:
- `no-double-side-effect-after-track-resume-mid-deferred-await` —
  pins the original orphaned-callback fix.
- `fork-isolated-cancellation` — pins the Option A fork-isolation
  guarantee. Forks the context after the parent suspended on
  `(await gate)`, cancels in the fork (via signal change), delivers
  the gate in BOTH parent and fork, asserts the body's side effect
  fired exactly once in each — proving the cancellation didn't bleed
  across fork boundaries.

## Open follow-ups

- **Cancel-token leak.** `:engine/cancelled-tokens` is append-only —
  one entry per cancellation, forever, for the context's lifetime.
  A long-running context accumulates the set indefinitely. Bound by
  total cancellations, not by in-flight count. Mitigation: pair token
  lifetime with cont lifetime by removing the token from the set when
  the cont is finally removed from `:continuations`. The subtlety: if
  the wrapped closure fires *after* the cont is removed AND the token
  is removed, the closure must default to "cancelled" (otherwise an
  arbitrarily-delayed external callback could resurrect a dead body
  slice). Safest design is to flip the predicate: track *active*
  (uncancelled) tokens, default unknown tokens to cancelled.

- **Mailbox waiter consumption hole.** Stage 4's cancellation gate
  makes the wrapped resolve a no-op when invoked, but the orphaned
  waiter is still in `mailbox.state-atom.waiters`. `post-inline!`
  consumes the message by invoking the (now no-op) wrapped resolve,
  then returns. The next legitimate waiter (registered by the
  parent's re-run body slice) waits for a new message. Net effect on
  Mailbox: silent message loss after a track-resume mid-await. Fix
  paths: (a) `:cancel!` actively removes the waiter from
  `state-atom`; (b) `post-inline!` reads `:engine/cancelled-tokens`
  for a token stored on the waiter struct and re-queues the message
  when the wrapped resolve was cancelled; (c) the wrapped resolve
  returns a sentinel. All three require coupling Mailbox internals
  to the await wrap. Deferred to a follow-up branch.

- **`add-continuation!` cancel-on-overwrite ordering.** Currently
  fires `:cancel!` outside the atomic `swap-state!` (captured via
  an outer atom). The cancel is idempotent under swap-retry so this
  is safe; moving it inside the swap-fn for stylistic consistency
  is a minor cleanup.

- `mark-not-running!` is now unreferenced by production code (only the
  snapshot-restore in `context.cljc` still resets `:running?` to false
  on in-flight spins after a snapshot is restored, which is unrelated).
  Can be removed after a deprecation cycle.
- The `:engine/current-batch` field could potentially be folded into a
  thread-local; the current shared-state form is convenient for forks
  but every readers does so within the signal-change handler call stack.
- Stronger lifecycle hygiene for `*applied-vnodes*` (already a documented
  TODO in `dom/render.cljc`).
