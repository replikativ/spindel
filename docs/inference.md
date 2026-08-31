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

The `EmpiricalMeasure` retains result and trace projections in its contexts;
it does not retain writable settlement authority. On successful completion,
all particle `ForkHandle`s are consumed newest-generation first. Construction
and resampling failures are also cleaned up automatically because no affected
particle is running at those boundaries.

## Failure and recovery

Model failures are fail-fast. Sibling particles may still be executing when
the first failure reaches the caller, so Spindel cannot safely discard their
worlds at that instant. The thrown exception therefore contains:

```clojure
(:world/recovery (ex-data error))
;; => {:status :open
;;     :manager <process-local capability>
;;     :descriptors [<portable fork descriptors> ...]}
```

Descriptors are safe durable/audit projections. The manager and its live
handles are process-local capabilities. A supervising host can wait for or
cancel sibling execution and then call
`inference.coordinator/discard-particle-worlds!`. The cleanup operation is
idempotent and concurrent callers share one settlement result.

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
self-programming is a curated capability, not ambient reflection.
