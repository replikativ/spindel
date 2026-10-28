# Lifetime reference model

This is the executable acceptance oracle for Part 4 of
`docs/engine-formalism.md` (implementation-plan step A3). It models T1–T38 and T20q
as immutable EDN state transitions, independently of `src/`. Independent
L1–L25 scans and finite-trace TL monitors check every explored edge,
including refusals. Logical copied rows are expanded; physical O(1) attach
cost and implementation lockstep are outside this model.

From the repository root, run the regression and generative checks:

```sh
clojure -J-Xmx1g \
  -Sdeps '{:paths ["test"] :deps {org.clojure/test.check {:mvn/version "1.1.1"}}}' \
  -M -m org.replikativ.spindel.lifetime.run13-check regressions
```

Omit `regressions` to include the sequential exhaustive profiles and four
single-pass capped broad profiles. A nonzero exit means a failed check.
Where JVM slots are required, prefix the command with
`~/Development/spindel-work/bin/slot.sh lifetime`.

The `*-check` namespaces deliberately do not match CI's `-test$` pattern.
Witnesses are classpath resources under `witnesses/`; `index.edn` explicitly
lists the historical artifacts to replay. Old violation metadata records the
original finding; replay checks current behavior. The F49 artifact now requires
precise refusals with unchanged states. Run-1 examples, M1 and V01 also have
assertions in `bfs_check.clj`.

Reports print to stdout. Set `LIFETIME_OUTPUT_DIR` to retain EDN reports in a
chosen directory; the default writes no artifacts. Each BFS report records its
bounds, limits, frontier and stop reason. Only `:exhausted` with no depth cuts
establishes exhaustive coverage of that finite profile. Capped prefixes do not
establish liveness; conditional progress monitors require a fair maximal suffix.

Run-6 witnesses F50 and F51 check the corrected seal/abort and pending-start
cancellation rules. Run-7 artifacts under `witnesses/run7/` exercise P1q
readiness, refusals, permits, arrivals held behind the fence, and rollback.
P1q traces are compared with P1 traces whose T21 readiness update executes
zero work steps. Atomic T20q refusals discard their tentative coordinator
record after rollback and preserve the input state, as other refusals do.
Permit refusals at T22 retain the fence until an explicit T25.

The earlier F52–F59 counterexamples are retained as regression witnesses.
Run 13 covers unwinding run retirement and physical slice exit. Its small
profiles exhaust; the broad profiles remain capped searches.

`verified/` is a separate proof experiment and is not loaded by these checks.
