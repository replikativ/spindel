# Historical worlds and savepoint boundaries

A historical world is not a branch name selected on the parent. It is a new
owned workspace at an immutable historical base. `ygg/fork!` with `:snapshots`
uses Yggdrasil's positively advertised `overlay-at` contract rather than
inferring isolation from Snapshotable or Branchable protocol satisfaction.
Some adapters have logical checkout on one connection; others satisfy a branch
protocol with no-op methods. Neither is permission to share a writable parent.

All requested systems are capability-checked before context construction.
Known unsupported policies refuse before another selected system allocates a
workspace. The historical child is an owned Overlay, whose native lifetime
remains with the ordinary affine ForkHandle. Its canonical base-ref is the
descriptor's base; a later parent head is not substituted as its merge basis.

The current historical fork-value hook is synchronous and JVM-first. CLJS
historical requests explicitly refuse before invoking a constructor. A future
awaited construction path can extend support; a CPS operation must never be
stored as if it were a system. Ordinary asynchronous convergent fork support
is unchanged by this boundary.

## Settlement completion

Native overlay disposal may return a genuine asynchronous operation. Merge,
skip-disposal and discard paths consume that completion before reporting
settlement success. A held disposal keeps the ForkHandle pending; rejection
after mutation retains incomplete ownership rather than reopening the handle
or fabricating success. There is no timeout-to-success conversion.

This waits for the native protocol's reported completion, not every possible
unreported action inside a backend. In particular Datahike's native release
API returns nil: it must not be passed to a channel-only bridge or promoted to
a new universal remote-shutdown receipt. Supporting native adapters separately
own their precise connection/branch/worktree cleanup and report uncertainty.

## Portability remains a stronger law

The savepoint law is `hydrate(persist(sp), v) ~ resume(fork(sp), v)` within the
declared captured scope. Correct historical isolation is necessary, not
sufficient, for that law.

Geschichte's logical snapshot identifies a committed tree; an ordinary physical
fork can additionally retain dirty worktree/index changes. Full portable
workspace fidelity therefore needs an explicit retained capture image, not a
changed logical commit ID, an automatic user commit or today's parent copied
as a substitute for yesterday. Conversation boundaries and external effects
belong to the embedding's contract. Snapshot vectors alone do not establish
coherent multi-system capture or all-or-nothing cross-store publication.

Regression obligations: parent unchanged through historical creation/disposal,
requested child/base/descriptor agreement, actual owned-resource disposal,
unsupported refusal before allocation, and held/rejected disposal acknowledgment.
