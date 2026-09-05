# Inference Worlds

Spindel's inference combinators execute probabilistic programs as `Spin`
values. Pure models can keep the default `:world-policy :fresh`. A model that
reads or changes registered room systems can request canonical worlds:

```clojure
(smc-infer model 32
  {:world-policy :fork
   :world-opts {:systems #{:knowledge :repository}}
   :resample-threshold 0.5})
```

Each initial particle is a frozen `ygg/fork!` of the ambient execution
context. At resampling, each selected ancestor is forked again. Selecting one
ancestor three times therefore produces three independently writable child
worlds, not three aliases to one context.

This makes inference a composition of existing Spindel operations:

```text
ambient world
  -> fork N frozen particles
  -> run until a probabilistic checkpoint
  -> score and select ancestors
  -> fork each selected ancestor
  -> resume
  -> project values and traces into an EmpiricalMeasure
  -> discard the speculative world tree
```

The `EmpiricalMeasure` retains result and trace projections in parentless,
immutable contexts. It therefore retains neither the resampling ancestry nor
writable settlement authority. On successful completion,
all particle `ForkHandle`s are consumed newest-generation first. Construction
and resampling failures are also cleaned up automatically because no affected
particle is running at those boundaries.

## Reusable finite world scopes

The lifecycle above is not specific to probabilities. The
`org.replikativ.spindel.world.scope` namespace owns a finite family of
canonical forks for any bounded algorithm such as MCTS or a simulation
campaign. A scope provides fork construction, composable activity leases,
atomic lease exchange, quiescence, cancellation hand-back, reverse-order
discard, and portable descriptors. Once quiescence is published, admission is
closed permanently.

The algorithm remains responsible for its computations and ends each activity
lease only after that computation has actually stopped. A live `ForkHandle`
never leaves the scope; fork callers receive a child execution context and a
portable descriptor, but no settlement authority. The scope never interprets
a particle, tree node, Run, reward, or proposal. In particular, a search policy
may share immutable statistics for a transposition, but it must not share a
writable context or affine `ForkHandle`.

SMC now uses this generic scope through compatibility functions in its
coordinator. This is an extraction of the existing ownership protocol, not a
second world abstraction: Yggdrasil still owns substrate forks and settlement,
while the execution context still owns reactive runtime state.

## Failure and recovery

Model failures are fail-fast. Spindel cooperatively cancels sibling particles,
tracks their terminal callbacks, and discards their worlds automatically once
they are quiescent. The thrown exception also contains actionable process-local
recovery operations:

```clojure
(:world/recovery (ex-data error))
;; => {:status :open
;;     :manager <process-local capability>
;;     :await-quiescent <CPS operation>
;;     :cancel! <host function>
;;     :discard! <host function>
;;     :descriptors [<portable fork descriptors> ...]}
```

Descriptors are safe durable/audit projections. The manager, operations, and
its live handles are process-local capabilities. A supervising host can await
quiescence and retry cleanup if automatic settlement encountered a recoverable
preflight failure. Cleanup is idempotent, concurrent callers share one result,
and a read-only preflight failure permits a later retry; failures after mutation
remain terminal for explicit substrate recovery.

## State placement

Particle-local program state belongs in the particle `ExecutionContext`:
signals, Spindel atoms, continuations, trace, score, and checkpoint state all
fork with the world. The manager contains only host lifecycle capabilities for
the entire inference execution. Durable application records should store fork
descriptors, not contexts or handles.

The optional top-level `:executor` is used by every particle and forwarded to
its canonical fork. Without it, world-backed inference shares the ambient
world's executor, preserving scheduler ownership. The legacy `:fresh` policy
keeps its existing inference-local shared executor behavior.

## Resources are not copied authority

Forking a Kontor ledger or another registered system creates a hypothetical
branch of its state. It does not grant duplicate authority to spend external
compute, tokens, money, or network capacity. Effects that consume real
resources need an explicit host capability and an affine split/reservation
policy. Simulations can instead receive stubbed effects, cheaper models, or a
forked accounting scenario.

## Recursive SCI interpreters

SCI code can construct another Spindel+SCI interpreter inside a child world,
provided the host explicitly injects the constructor, evaluator, and world
fork capabilities. The inner interpreter executes `Spin` values against the
child runtime, and the parent retains settlement authority. Raw `sci.core`
does not need to be exposed to untrusted Dvergr programs; recursive
self-programming is a curated capability, not ambient reflection. The world
API gives SCI opaque IDs backed by a host registry. Raw `ForkHandle` records
contain mutable affine authority and must never cross the sandbox boundary.

PGAS ancestor scoring still uses legacy snapshot particles, so Spindel rejects
`:world-policy :fork` together with `:pgas-ancestor-sampling?`. That combination
can be enabled once auxiliary scoring particles also use canonical worlds.
