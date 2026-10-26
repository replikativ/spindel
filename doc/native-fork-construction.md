# Native fork construction ownership

A completed `ForkHandle` owns a child world and its settlement capability.
Constructing that handle can itself allocate native resources: an isolated
repository workspace, database branch or convergent branch. A later constructor
or descriptor can fail before a handle exists. Those acquisitions still need an
owner. This is separate from world funding, savepoints and proposal settlement.

## Invariants

1. The source world remains usable when construction fails. A failed copy does
   not consume its source.
2. Every acknowledged native acquisition belongs to either the construction
   owner, a completed handle, or a receiver that accepted an atomic handoff.
3. Acknowledged resources unwind in reverse acquisition order. Successful cleanup
   is recorded before proceeding and is not repeated.
4. An unacknowledged allocation is uncertain. A thrown checkout can also have
   acquired resources after the branch ACK. Neither outcome is treated as absent.
   The uncertain checkout retains its branch dependency until reconciliation;
   other independent acknowledged acquisitions may still unwind.
5. An uncertain disposal is not automatically replayed. A privileged host must
   reconcile the adapter and explicitly attest disposal, absence, or safe retry.
6. A provisional child with work in flight retains its native resources.
   If construction may have activated queued child work, even later quiescence
   is insufficient: suspended deferred/timer bodies may resume. An activation
   receipt keeps all native resources until explicit HOST cancellation/join
   attestation. Zero-activation failures can clean automatically after quiescence.
   No child stop, shared executor shutdown, or guessed join is performed.
7. No child wallet exists before scope admission. Recovering a partial native
   construction never returns a wallet or refunds the source world.
8. The cleanup journal and callbacks are host lifecycle state. They are not
   copied into semantic state, native adapter directives, or captured CPS bindings.

## Construction extent

`fork!` establishes an opaque construction owner before the first registered
system constructor. The context builder brackets synchronous native hooks and
reports the provisional context before following registrations or queued work.
The native branch hook reports the branch ACK before checkout. On the JVM that
registrar uses a non-inheritable thread-local extent restored in `finally`;
asynchronous CLJS post-pass work carries its registrar explicitly.

After descriptors and handle authority are installed, the owner transfers its
resources to the completed handle and drops its native references. A pure
preflight refusal happens before acquisition. Arbitrary custom hook side effects
that are never registered are outside this native acquisition contract.

## Failure and recovery

Construction first attempts cleanup of known resources. If all acquisitions are
settled, the original error is propagated. Otherwise an incomplete-construction
error preserves the original cause and redacted receipt diagnostics. Without a
receiver, its `:construction/owner` retains the opaque recovery capability.

A host `:on-fork-failure` callback can atomically store a candidate owner and
return true. The candidate becomes active only after acceptance; the original
capability then becomes stale. Decline or a thrown callback leaves the original
owner active. A callback must only store ownership during handoff, not start
cleanup or publish the failed construction as a usable world.

A world scope keeps such owners separately from completed handles and funded
children. `recover!` joins native cleanup; an unresolved receipt keeps recovery
pending rather than pretending success. A failed copy offers completed copies
and any partial construction together to `:on-copy-failure`. Acceptance claims
all of them in one callback. The source remains owned in its original position.

An activation receipt can be resolved only after an actual lifetime proof. For
example, a host may know that its only one-shot producer completed, all resulting
work joined, and no timer or callback can wake the provisional child again. The
quiescence predicate alone cannot supply that proof. Successful construction
transfers active work ownership to the complete handle as before.

Privileged native reconciliation is intentionally not an agent tool. The host
must establish what happened at the adapter before using
`resolve-uncertain!`. A timestamp, missing reply, or guessed resource absence is
not proof. This mechanism does not provide durable restart recovery by itself.
