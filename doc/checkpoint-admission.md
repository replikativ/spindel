# Exact repository checkpoint admission

`yggdrasil/fork!` accepts a HOST-selected `:checkpoints` map from registered
system IDs to portable checkpoint origin descriptors. It creates an isolated
ordinary workspace at that physical repository state. Programs use the existing
filesystem and database interfaces; there is no second retrieval API.

```clojure
{:checkpoints
 {"workspace" {:version 1
               :kind :datahike
               :commit checkpoint-uuid
               :source {:store store-uuid :repository repository-uuid}}}}
```

This differs from `:snapshots`, which selects logical version history. A physical
checkpoint includes dirty, staged and untracked files, repository refs, schema
and repository attributes. The logical merge base remains the checkpoint's
logical HEAD. The two policies cannot select the same system in one request.

## Admission sequence

1. Check the whole map's shape, system selection, policy overlap and execution
   platform. All selected adapters must positively support checkpoint overlays
   and read-only checkpoint validation.
2. Validate every origin against its effective source system, without allocating
   a workspace, writer or cleanup lease. Each synchronous validation must return
   the same portable descriptor.
3. Construct the child through the existing native acquisition owner. Every
   checkpoint constructor repeats its authoritative source checks before
   allocation; preflight is not a cached authority or an availability guarantee.
4. Return a normal `ForkHandle`. Its system descriptor keeps `:kind :overlay`
   and existing settlement guards, with an additional `:checkpoint` provenance
   field. Merge and discard use ordinary overlay settlement.

Malformed, foreign-source, unsupported and already unavailable origins detected
in preflight allocate nothing. Later IO failures still require the normal
construction recovery contract. Validation does not replace authorization.

The engine's `PForkable` hook is synchronous. This first bridge therefore rejects
checkpoint policies on CLJS before allocation, even if the underlying adapter
supports an async checkpoint workspace. A future asynchronous engine hook can
extend that boundary without storing CPS operations as signal values. Async
HOST Run admission on the JVM already works through the existing bridge.

## One admission, not inherited authority

The option is not installed in child bindings or semantic state. An ordinary
recursive fork inherits its immediate parent's current edits. It does not replay
the original checkpoint. The admitting host must keep checkpoint policy separate
from reusable delegation capabilities and model/tool permissions.

A copy means alternatives of the source world's current state. `copy-fork!`
therefore refuses a nonempty or malformed checkpoint option; use `fork!` for
historical selection. Ordinary copies of a checkpoint-origin world preserve its
subsequent edits.

A world scope refuses checkpoint policies in reusable `:fork-opts` defaults.
Pass the option to the individual `scope/fork!` invocation instead. A later
ordinary fork in that same scope then uses its actual source state.

## Retention and evaluation

An origin descriptor is neither a GC pin nor a permission. The admitting host
must acquire retention before preflight and retain it across construction,
execution, uncertain cleanup, and any promised evidence lifetime. Successful
validation does not transfer or create retention. Spindel does not infer this
ownership from a system-name string.

For evaluation, checkpoint identity belongs in the environment/setup basis so
results identify the initial repository state available to execution. Clean-fixture evaluations must still isolate
other cases, authoring files and gold. Selecting an author's full repository is
not a substitute for fixture isolation. Setup stages inputs after the world has
been selected; it must not reset a canonical connection or replace a world-owned
connection behind its settlement handle.
