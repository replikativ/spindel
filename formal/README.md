# Formal model of the v2 engine

A machine-checked model of the engine in `src/org/replikativ/spindel/v2/`, written in the
[ansatz](https://github.com/replikativ/ansatz) DSL and checked by its kernel when a namespace
loads. It is not part of the spindel jar (`build.clj` packages `src/` only).

| Part | Where | What it states |
|------|-------|----------------|
| Headline statements | `src/spindel/v2/top.clj`, `systop.clj` | `inv` = p3m ∧ svb ∧ inv-i9 ∧ inv-i10-slice ∧ i3; `inv-empty`, `inv-step` (every item keeps `inv`), `reach-inv` (every world reachable from the empty world satisfies it); layer 2: `sys-reach-inv` (every reachable system satisfies sinv ∧ pinv ∧ cinv ∧ qsinv ∧ qpinv ∧ jinv) |
| Layer 1: one world | `src/spindel/v2/` up to `hm18.clj` | the transition system of `docs/engine-v2-spec.md` (`world-step`) and its invariants; the bundle chain p3b ⊂ … ⊂ p3m, `step-p3m`: every item keeps it |
| Copy-on-write | `src/spindel/v2/cow.clj` | a fork, a copy on access and a write of one world leave every other world's view unchanged |
| Layer 2: worlds | `src/spindel/v2/sys.clj`, `skip.clj` | forks, savepoints, instances, merge and release as operations on a system of worlds; every live world keeps `inv` |
| Oracle | `test/spindel/v2/oracle.clj`, `oracle/` | replays commit logs recorded from the engine through the model and compares every committed state |

`notes/LAYER2.md` is the design note for layer 2 with its open points. The other notes are working
material of the proof campaign.

## Running

From this directory (ansatz comes from Clojars; the proofs need a large stack, set in the alias):

```bash
clojure -M:test -n spindel.v2.oracle-test     # engine logs against the model, about 3 minutes
clojure -M:test -n spindel.v2.sys-test        # layer 2; loads all of layer 1, longer
clojure -M:test                               # everything, tens of minutes
```

New log samples are generated from the engine by `test/spindel/v2/oracle/gen/` (run from the
repository root).
