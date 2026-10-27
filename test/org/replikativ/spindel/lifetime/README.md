# Lifetime reference model

This is the executable acceptance oracle for Part 4 of
`docs/engine-formalism.md` (implementation-plan step A3). It models T1–T37
as immutable EDN state transitions, independently of `src/`. Independent
L1–L24 scans and finite-trace TL monitors check every explored edge,
including refusals. Logical copied rows are expanded; physical O(1) attach
cost and implementation lockstep are outside this model.

From the repository root, run the regression and generative checks:

```sh
clojure -J-Xmx1g \
  -Sdeps '{:paths ["test"] :deps {org.clojure/test.check {:mvn/version "1.1.1"}}}' \
  -M -m org.replikativ.spindel.lifetime.bfs-check regressions
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

The current specification admits the counterexamples in
[`run6-F50.edn`](witnesses/run6-F50.edn) and
[`run6-F51.edn`](witnesses/run6-F51.edn). Their normative checks remain red;
a green A3 acceptance result requires specification fixes.

`verified/` is a separate proof experiment and is not loaded by these checks.
