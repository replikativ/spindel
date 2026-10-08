# Structural savepoint performance

This work measures foerster's inference workloads against Spindel's structural
savepoint branch. The measurements below were taken before the branch was
rebased onto `e3a4f7c` (concurrent spin-id minting): baseline `b6ba2f3`,
implementation commits as listed at the end. All changes apply to arbitrary
worlds, including worlds with registered systems and resource authorities.
Foerster's inference source is unchanged.

## Evidence and decisions

The W3 JVM Flight Recorder profile reproduces the original hotspot report.
From the first sampled foerster choose handler onward, 18,829 execution samples
give the following inclusive, overlapping shares:

| Path | Baseline share | After share |
| --- | ---: | ---: |
| Savepoint publish, including its handler | 36.0% | 35.8% |
| Overlay writes | 25.9% | 26.4% |
| World scope, including fork and settlement callbacks | 21.3% | 21.4% |
| Savepoint fork | 16.6% | 16.6% |
| foerster random | 12.1% | 12.6% |
| Overlay reads | 9.9% | 9.6% |
| Overlay materialization | 4.5% | 4.3% |
| Slice restore | 4.1% | 4.2% |
| Slice capture | 2.3% | 2.6% |
| Claim | 3.0% | 2.4% |

These are stack membership counts, not independent costs. In particular,
scope's inclusive cost does not imply that activity leases consume a fifth
of runtime: begin/end activity together account for approximately 0.6%, while
scope fork and release contain substrate work and callback execution.
The after recording contains 18,173 runtime samples. The overall hotspot
shape remains similar; these changes do not remove the cost of publishing,
capturing and restoring every handled occurrence.

Inspection confirms that every consumed occurrence previously retained a
claimed token in `:savepoint/pending`. The inline-resume stack-safety test runs
5,000 occurrences, so it also serves as a retention regression. A pending map
should scale with live suspensions, rather than the number of past sites.

A separate counter probe uses the fixed-seed suite's models (100 MH moves,
one chain; SMC with five particles and 40 steps). All 1,968 dispatched MH
savepoints were consumed by handler return (49 latent, 1,919 observed).
All 196 dispatched SMC latent sites were consumed by return; 160 of 200
observed sites remained pending and 40 were already consumed. These count
observable consumption at return, including any concurrent consumption;
replay's selected anchor is decided directly and does not publish again.
Thus held sites are real and lazy publication must support both lifecycles.
The same probe counted 80 cache hits / 420 misses for MH and 3 hits / 28 misses
for SMC. The probe's atom updates are excluded from timing measurements.

Frozen forks previously materialized their source overlay on every fork,
even when that source was an unchanged anchor. Full-state transactions also
reconstructed unchanged views. Persistent state roots can identify revisions
without introducing counters or requiring callers to invalidate caches.

## Pending-entry retirement

A claim removes its entry in the same atomic pending-map update that selects
the winner. A volatile result is overwritten on every invocation of the
update function, including retries; only the committed invocation determines
whether the operation won. This works with inherited overlay paths and does
not depend on path CAS, which overlays cannot provide for shared state.

Handles identify an occurrence by its captured continuation, in addition to
its address. This preserves affinity when a consumed explicit address is
published again: the old handle cannot claim or fork the replacement. Forks
retain the continuation identity but have independent pending maps. Removing
an inherited entry replaces the whole pending map in that world, so the
parent entry cannot reappear through overlay fallback.

Publication checks address collisions inside its atomic insertion. Closing
still sets the session flag before scanning pending state; publication still
inserts before checking that flag. Handler failure, abandon, cancellation,
executor scheduling, slice restoration, resource grants, and copy settlement
keep their existing behavior.

## Materialized-view reuse

Each overlay retains one cached materialized view, keyed by the identities of
the overlay root and the materialized parent root. An unchanged frozen parent
therefore needs no repeated entity merge. Following overlays still dereference
their parent on every request; a parent write changes its root identity and
invalidates descendants recursively. Single-path, two-path and whole-state
writes all change the same persistent overlay root, so there is no separate
invalidation path to forget.

Concurrent callers may replace the cache with an older pair, but every lookup
checks both current input identities before reuse. A cache populated during
an unsuccessful whole-state CAS attempt is likewise safe. The cache is
process-local, stores only one input pair and view, and is absent from state
serialization. It does not replace the real parent context or fork lineage.
It can retain one previous revision until the next view request or backend
collection; it does not retain a growing list of historical revisions.

## Scope bookkeeping

A quiescence check first reads whether leases or fork operations remain.
When work remains it has nothing to publish and returns without a speculative
CAS or callback allocation. When the last operation ends, it still uses the
existing atomic transition and rechecks admission, pending forks and readers.
Cancellation cleanup is also reached through that final transition. Existing
validator-driven retry tests exercise concurrent admission during quiescence.

## Why publication remains eager

The handler can pass a handle to another thread before returning. That thread
may resume, fork or abandon it, and `close!` may scan simultaneously. Handlers
can also inspect runtime state, snapshot it, or fork a context directly.
Keeping an entry only in a publishing thread's local variable would make
those observers disagree about whether the site exists. A shared mutable
claim cell copied into a frozen fork would break fork independence.

Lazy publication remains an option, but needs a general world-state boundary:
an atomically registered local entry visible to all state observers, an
immutable pending-map projection at every fork/snapshot boundary, and an
atomic transfer between local and materialized ownership. Optimizing only
`savepoint/fork` is insufficient because `fork-context` is also public.
The current changes remove retained history and repeated reconstruction
without adding a second publication/claim state machine.

## Measurement and validation

Commands run one JVM at a time, with at most a 3 GiB heap. Benchmarks use the
existing fixed seeds and models; W1-only and W3-only scripts are derived from
`experiments/comparison/clj/bench.clj` by retaining definitions before
`(def results ...)`, printing `(w1)` or `(w3)`, and shutting down the JVM.

```sh
cd /home/christian-weilbach/Development/foerster-struct
clojure -J-Xmx3g -Sdeps '{:deps {org.replikativ/spindel {:local/root "/home/christian-weilbach/Development/spindel-struct"}}}' -M -i bench_suite.clj
clojure -J-Xmx3g -Sdeps '{:deps {org.replikativ/spindel {:local/root "/home/christian-weilbach/Development/spindel-struct"}}}' -M -i experiments/comparison/clj/w3_only.clj
clojure -J-Xmx3g -Sdeps '{:deps {org.replikativ/spindel {:local/root "/home/christian-weilbach/Development/spindel-struct"}}}' -M -i experiments/comparison/clj/w1_only.clj
```

JFR uses `-J-XX:StartFlightRecording=filename=/tmp/struct-w3-before.jfr,settings=profile`;
after the workload exits, samples are exported with
`JAVA_TOOL_OPTIONS=-Xmx3g jfr print --events jdk.ExecutionSample --stack-depth 60 ...`.
Profiled runs are kept separate from ordinary timing comparisons.

The small suite's result column is byte-identical before and after removing
only its millisecond timing column:

| Workload | Before | After | Time reduction | Unchanged result |
| --- | ---: | ---: | ---: | ---: |
| SMC, 200 particles × 300 steps | 3,699 ms | 3,366 ms | 9.0% | -446.47875278183875 |
| RMH golf, 4 × 2,000 moves | 4,387 ms | 3,625 ms | 17.4% | 1.782472200992522 |
| PGibbs, 50 particles × 30 sweeps × 100 steps | 33,959 ms | 31,124 ms | 8.3% | -0.1201366747151433 |

Full W3 uses four chains of 22,000 moves, including the 2,000 discarded
burn-in moves per chain. Its second run takes 35.330498805 s before and
33.743552909 s after: **401.483 → 383.449 µs/move** (amortized wall time
over 88,000 moves), a 4.49% time reduction
(1.047× throughput). The first runs take 41.343513051 s and 39.968956622 s.
These are individual warm runs, not confidence intervals; the small suite's
larger MH reduction should not be extrapolated to full W3.

All W3 summaries are byte-identical after removing only `:first_s` and
`:warm_s`: a mean `2.228239291249281`, sd `0.057462537295592385`, ESS
`482.84464353818095`, R-hat `1.009740762347968`; b mean
`-0.2554560641805122`, sd `0.006562979049192186`, ESS `551.1627888150167`,
R-hat `1.00828249252018`.

W1 runs T=300, with a warm-up at seed 99 followed by ten seeds for N=100
and five seeds for N=1000. Times below are medians:

| Particles | Before seconds | After seconds | Before µs/step | After µs/step | Particle-steps/s before → after |
| --- | ---: | ---: | ---: | ---: | ---: |
| 100 | 1.855481760 | 1.721815679 | 61.849 | 57.394 | 16,168.3 → 17,423.5 |
| 1,000 | 19.538375953 | 18.446406887 | 65.128 | 61.488 | 15,354.4 → 16,263.3 |

Time reductions are 7.20% and 5.59%, respectively. Evidence-error statistics
are byte-identical after removing only `:median_s` and `:steps_per_s`: N=100
mean `-0.22339483904351595`, sd `0.7159124893333946`; N=1000 mean
`0.06078169289033895`, sd `0.182198227132052`.

The baseline JFR W3 first/warm runs take 59.774808686/51.775114238 s.
The after recording takes 56.355789283/49.905720180 s, with the same summaries.
Its overhead is substantial, so those times are not substituted for the
unprofiled baseline.

Targeted validation: 109 tests / 677 assertions, zero failures or errors,
covering savepoints, portable savepoints, scopes and retry races, overlay
whole-state transactions, execution contexts, lost wakeups, traces and reuse.

Full Spindel JVM suite: **1,169 tests / 4,893 assertions, zero failures or
errors**. Formatting passes (`clojure -J-Xmx3g -M:format`).

Spindel ClojureScript CI release compiles successfully (320 files), then
Node passes **457 tests / 1,702 assertions, zero failures or errors**.
The compiler emits dependency warnings; none prevents the build. The command
invokes shadow directly in a single JVM, avoiding a separate shadow server:

```sh
clojure -J-Xmx3g -M:cljs -m shadow.cljs.devtools.cli release ci
node --max-old-space-size=1024 out/ci-tests.js
```

Existing npm dependencies from the sibling Spindel checkout were exposed by
a temporary `node_modules` symlink, removed after the test process exited.

Full foerster JVM suite against this checkout, run once after implementation
and Spindel validation: **200 tests / 3,253 assertions, zero failures or
errors**. Foerster production and test source have no changes.

```sh
cd /home/christian-weilbach/Development/foerster-struct
clojure -J-Xmx3g -Sdeps '{:deps {org.replikativ/spindel {:local/root "../spindel-struct"}}}' -M:test
```

The full JVM suite includes `durable-restart-test`, which normally launches
a writer JVM while the reader test JVM is alive. To obey the one-JVM limit,
the writer runs and exits first. A temporary test fixture supplies its actual
exit status/stdout/stderr and its store path to the original test; all three
original assertions still run in a separate reader JVM with cold caches.
No repository test is altered or omitted. The full runner uses an additional
alias whose main options load `/tmp/struct-serial-restart.clj` before calling
the normal `cognitect.test-runner`; all `:test` paths, dependencies and options
remain active.

Raw logs and recordings from this session are retained under `/tmp`:
`struct-suite-{before,after}.log`, `struct-w3-{before,after}-unprofiled.log`,
`struct-w1-{before,after}.log`, `struct-w3-{before,after}.jfr`,
`struct-w3-{before,after}-samples.txt`, `struct-probe.log`,
`struct-targeted.log`, `struct-spindel-full.log`, `struct-cljs-build.log`,
`struct-cljs-tests.log`, and `struct-foerster-full.log`.

Implementation commits as measured (before the rebase):

- `acc0af8`: retire consumed entries and enforce occurrence affinity.
- `8028d9a`: cache materialized views by persistent state roots.
- `960550b`: skip quiescence transitions while work remains.

After the rebase onto `e3a4f7c` they are `bced983`, `326ad59` and `0518bd2`;
the timings were not repeated on the rebased commits. The rebased branch
passes the full JVM suite (1,172 tests / 4,982 assertions).

## Remaining options

1. General lazy pending-state projection, with race tests for local-to-world
   transfer, direct context forks, snapshots, close, failure and copy refusal.
2. Reduce CPS/callback allocation around world construction and settlement,
   retaining the same asynchronous substrate and resource-authority contract.
   Inclusive scope samples are dominated by these paths, not lease maps.
3. Reduce capture/restore and addressing allocations without weakening slice
   restoration: a handler may change bindings or address state before resume.
4. Rewind or recycle worlds only after proving the absence of in-flight
   engine coordination. This requires a separate design; it is not implied by
   reaching a savepoint.
