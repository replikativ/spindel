# A3 — lifetime lockstep harness and benchmark gates

Branch: `test/lifetime-lockstep`; starting revision: `af0bd82`.
Runtime source is unchanged from main `06ce205`. The reference model and its
invariant/transition semantics are unchanged.

## Harness

`test/org/replikativ/spindel/lifetime/lockstep.clj` is a JVM check entry point,
excluded from the `-test$` discovery pattern. `lockstep_smoke_test.clj` is in CI.
Every walk gets a fresh synchronous execution context. A registered test-only CPS
checkpoint stores a continuation outside the engine's dependency tables; commands
resume that continuation with `*in-trampoline* false`. Scripted `await` and `track`
are lexical calls inside `spin`, including nested spin creation.

`project` reads runtime nodes exclusively through `rtp/get-state`. Script structural ids name distinct source sites through `addressing/next-id`;
`scripted-spin` uses the same CPS compiler and public `make-spin` construction as
the spin macro. A shared factory cursor cannot represent independent symbolic
source sites first visited in different forks. Native addresses are associated
with script structural ids at creation. Comparison reuses
`model/canonical`; it does not invent another fresh-id equivalence. Cold host
spin templates are excluded until invocation or lexical creation, matching T1.
Lexical creation is read from both `created-by` and parents' `created-spins`, since
host re-registration on main overwrites the former.
Signal creation includes a nonreactive read to materialize main's lazy handle.
Deltaable signal snapshots are unwrapped before comparison.

The enabled state comparison is **read-visible entity kind, completion and result**.
PState includes following-fork read-through; expected entity visibility therefore
uses the model's `read-source`. Physical local/inherited storage is not observable
through this protocol and remains an explicit C2 gap. Every absent component is
projected as `:absent`, rather than synthesized from the model. Component switches
also control comparison: enabling an unimplemented projection makes the check red.

L12 checks the projected data subset, including detection of non-data values.
This is not a claim that main satisfies full L12. Other L predicates are gated by
an explicit dependency table because their lifetime rows do not exist on main.
Owners, scopes, reasons, dirty certification, run histories, obligations, tokens,
registry, lineage, pins, waiters, cross-world indexes, queue protocol, admission,
cuts, capabilities and saga records are disabled. Later implementation steps must
supply their projection and enable their comparisons and dependent predicates.

| Action | Current driver | Extension step |
| --- | --- | --- |
| T1 | Host and lexical spin creation; structural handle re-registration | Ownership B1 |
| T2 | Unkeyed signals, materialized by read | Atom driver B2; keyed signals B6 |
| T4 | Nonblocking invocation, success/error callbacks | Scope B1; host filters D1 |
| T5 | Local `await-once` and `track` inside scripted bodies | Obligations B2; foreign D1 |
| T7 | Scripted values and errors | Run lifetime B3; queue boundary D1 |
| T11 | `cancel-spin!` by entity handle | Run generation and cascades B3 |
| T19 | Following yggdrasil fork with no external systems | Registry C1; bundles C2 |
| signal-write | Public signal reset | Cross-world messages D1 |
| T3 | Not yet | B6 |
| T6, T8, unsubscribe | Not yet | B2 |
| T9, T10, T15 | Not yet | B3 |
| T12 / T13 | Not yet | B1 / B4 |
| T14 | Not yet | C2 |
| T16–T18 | Not yet; deterministic Cleaner ingress probe only | B5 |
| T20–T25 | Not yet; frozen/following API probe only | E1–E3 |
| T26–T30 | Not yet as model microsteps; atomic merge/discard and stamp-failure probes | E1, F2 |
| T31 / T32–T33 | Not yet | F2 / F1 |
| T34–T37 and native/thread/arrival events | Not yet | D1, with host registration B2 |

The GC probe injects the exact `:gc-cleanup` event through `rtp/enqueue!`, without
source changes or private backend access. It cannot establish JVM unreachability
or emulate missing incarnation tokens, so it does not claim T16/T17 coverage.

The corpus reads every `run*.edn` file, including F50/F51 beyond `index.edn`, and
replays each supported prefix. Unsupported middle actions stop a walk with a step
and reason; they are never silently deleted. Exhaustive supported subprofiles use
a finite filtered alphabet, not the full reference-model proof alphabet. All edges
are replayed as walks. Model-generated test.check choice vectors feed both original
model walks and walks choosing from the supported alphabet. Seeds are fixed.
First divergences retain the exact prefix; the report minimizes each distinct
signature by deletion to a fixed point. This is single-deletion minimality, not a
claim of global shortestness or temporal/liveness coverage.

## Benchmarks and gates

`fork_bench.clj` measures public fork+discard with 1k and 5k strongly retained live
siblings, and with a parent containing exactly 10k entities: 8k materialized signals, 1k
spins parked on deferreds, and their 1k runtime-atom backing rows. Assertions
verify the entity total and parked run count before measurement. Fixture creation/teardown are outside measured time and
calling-thread allocation. Parent-size comparison uses the 1k-sibling empty-parent
fixture, so the sibling population is held constant.

`enum_bench.clj` performs 100k fork→run→discard cycles and 100k create/complete
cycles, each in one root. It records retained JVM heap and protocol-readable table
counts at 10k and 100k, plus segment and overall throughput. Each heap measurement
starts with three full-GC requests and 200 ms between requests, then requests
GC every 500 ms until the protocol-readable table counts stay unchanged for three
samples. A 30 s deadline reports an unstable measurement as a failed measurement
gate. This prevents a Cleaner backlog from being mistaken for a leak. GC
checkpoints are excluded from throughput; their wait time and stability are saved.

`lifetime_gates.clj` runs the four existing lifecycle shapes with warmup and three
samples (median time), the fork fixtures and both enumeration walks. Reports
include source tree/revision, host, JVM, heap and measurement protocol. Measurement
requires the exclusive lock and exactly `-Xmx3g`.

`lifetime_gate_rules.cljc` compares complete reports and rejects mismatched
measurement metadata. It applies the plan's thresholds without exempting main:
10% lifecycle time, 64 extra bytes/spin, 1.5× sibling fork scaling, 5% retained heap
growth, and 10% throughput loss. The plan supplies no numerical noise allowance
for parent-size growth; the script reports and tests its literal ratio limit 1.0.
Absolute scaling and heap gates apply even when comparing a baseline to itself.

## Running

The `:test` alias sets `:main-opts`; override them for the standalone checker:

```sh
~/Development/spindel-work/bin/slot.sh a3-check clojure -J-Xmx1g \
  -Sdeps '{:aliases {:a3 {:main-opts []}}}' -M:test:bench:a3 \
  -m org.replikativ.spindel.lifetime.lockstep /tmp/a3-lockstep.edn

~/Development/spindel-work/bin/slot.sh a3-smoke clojure -J-Xmx1g \
  -X:test :nses '[org.replikativ.spindel.lifetime.lockstep-smoke-test]'

~/Development/spindel-work/bin/exclusive.sh a3-bench clojure -J-Xmx3g \
  -M:bench -m org.replikativ.spindel.lifetime-gates measure \
  dev/org/replikativ/spindel/baselines/main-06ce205.edn

~/Development/spindel-work/bin/exclusive.sh a3-gates clojure -J-Xmx3g \
  -M:bench -m org.replikativ.spindel.lifetime-gates check baseline.edn candidate.edn

bb -cp dev -m org.replikativ.spindel.lifetime-gates-check
```

The standalone oracle exits nonzero for observed divergences or the supplied
model's known red normative witnesses. A green smoke test is not acceptance of
the unsupported lifetime contract.

## Harness regressions found during construction

The first smoke run failed signal creation: main creates a lazy signal handle,
whereas T2 creates a world row. The driver now realizes the handle by a public
nonreactive read. This changed no runtime or model semantics.

The initial full check also exposed harness bugs, rather than new engine bugs:

- A single factory trace address aliased different symbolic entities first
  created in different worlds. `symbolic-script-addresses-survive-fork-order`
  pins the fix using distinct deterministic script source sites.
- Host handle re-registration clears main's `created-by`. Creator membership
  must also consult `created-spins`. A following fork may hide its parent's
  creator node with its own local copy, so the projection takes the union of
  creator memberships read through PState across all driver contexts.
  `lexical-row-survives-host-handle-registration` and
  `following-cold-row-after-host-registration` cover both cases. This union is
  observed runtime data, not model-derived ownership.
- A minimization signature that omitted the expected refusal could shrink a
  token-spin mismatch into an unknown-handle refusal. The signature now retains
  both refusal types and uses only the unequal portions of state comparisons.
  `minimization-preserves-the-refusal-type` pins this distinction.
- Some model audit deliveries omit the entity id, and cached deliveries omit
  their value. `model-deliveries` interprets these from the preceding obligation
  and cached row. `cancellation-event-provenance` covers the omitted id.

Fail-before evidence is retained in the initial smoke/check outputs under
`~/Development/spindel-work/impl/a3/`: `smoke-first.log`, `lockstep.edn`, and the
pre-fix `check-summary.edn`. The construction-time files are evidence, not a new
reference-model fixture or a waiver of discrepancies. Runtime tests also inject a
corrupt projection and enable an unavailable component to verify that comparisons
fail closed. Gate mutation replaces threshold comparison with unconditional pass;
eight boundary assertions then fail, versus all 15 passing with the real rules.

## Coverage and discrepancies on main

The final standalone run exits **1**, as an oracle reporting discrepancies should.
The smoke suite passes **11 tests / 23 assertions**. The 125 replay attempts have
12 passes, 82 unsupported-prefix stops and 31 divergent prefixes. Of 87 historical
witnesses, 4 pass, 70 stop at unsupported actions and 13 diverge. The four complete
passes are the run2–run5 `witness-host-readthrough` artifacts. This is not 87
accepted witnesses. Every individual status, checked prefix length and skip reason
is stored in `dev/org/replikativ/spindel/baselines/lockstep-main-06ce205.edn`.

The one-spin supported subprofile exhausts 5 states / 5 edges; source-only exhausts
3 states / 2 edges. Settlement/shared-cut profiles stop at missing transitions.
Ten seeded model-generator walks of up to 20 choices and ten walks choosing
from the supported model alphabet with the same choice vectors are included. Neither search nor these finite traces establish liveness.

The committed oracle artifact lists all 17 distinct minimized signatures as
`D00`–`D16`, with exact EDN actions, expected/actual differences and classification.
Its signatures omit equal state portions, but preserve both expected and actual
refusal types. The following table classifies every signature; abbreviated traces
refer to spin numbers and world 0 unless stated otherwise.

| IDs | Minimal trace / finding | Classification |
| --- | --- | --- |
| D00, D03, D08, D16 | Invoke → complete, with optional host handle; value is delivered inside T7 rather than separate T8 | Harness boundary limitation, D1 |
| D01, D15 | Two invokers → complete; both deliveries precede the model T8 | Harness boundary limitation, D1 |
| D06 | Invoke → scripted error; rejection precedes model T8 | Harness boundary limitation, D1 |
| D04, D07, D12 | Invoke → cancel; main caches a cancelled result, model retains a dirty noncompleted row | Known B3 gap; checkpoint-only egress is also a harness limitation |
| D09 | Invoke parent → create/invoke child → cancel parent; owner cancellation differs | Known B1/B3 gap |
| D13 | Invoke parent → create cold child → cancel parent; child survives main cancellation | Known B1/B3 gap |
| D14 | Invoke parent → await child → cancel child; terminal cache differs | Known B3 gap |
| D02 | Invoke → await child → fork → cancel parent; inherited copies and cancellation differ | Known B1/B3/C2/D1 gaps |
| D05 | Invoke → await child → fork → cancel child; inherited child sees parent cancellation | Known C2/D1 gap, alongside B3 terminal-cache behavior |
| D11 | D02 with an additional cold lexical child; owner release differs | Known B1/B3/C2/D1 gaps |
| D10 | Reuse one model token for different entities; model refuses, main has no corresponding token parameter | Harness limitation, B5; not evidence of a new native refusal bug |

The synchronous main API combines model microsteps. The harness deliberately
reports those delivery-boundary mismatches instead of pretending T7 and T8 were
separately driven. A checkpoint itself is not an engine await obligation, so
absence of callback egress when cancelling a checkpoint-only run is not a native
cancellation regression. State differences and owner/copy behavior remain visible.
The token mismatch is retained as an explicit diagnostic; the driver cannot yet
represent the target negative token API. These limitations must be resolved before
claiming full transition acceptance; they are not waived by the green smoke test.

The independent failing-stamp probe has the minimal API trace
`register failing stamp → fork → merge`. Main throws `::ygg/stamp-failed`, leaves
the handle **`:merged`**, and leaves **one pending stamp**. This is the known F2
settlement gap. Empty-system merge/discard are idempotent in the API probes.
Frozen/following reads return 1/2 after the parent changes from 1 to 2. The GC
notification probe deterministically removes a completed node.

The unchanged reference model independently reports its existing normative
counterexamples: F50 violates **L16** (open admission after settlement sealing),
and F51 violates **L10** (one foreign obligation has pending-start and cancelling
phases). These are known specification/model triage items, not new runtime bugs.
No model change was made to turn them green.

## Recorded baseline and gate results

`dev/org/replikativ/spindel/baselines/main-06ce205.edn` was measured once under
`exclusive.sh a3-bench-and-suite`, with `-J-Xmx3g`, on **maturana**, Linux amd64,
8 processors, Java **25.0.1**. Heap limit: **3,221,225,472 B**. Runtime base:
`06ce205`; source tree: `b1a9ec1ad9e9108de54a9dc9953f80008a640452`.
Benchmark revision: `e40cd50` (test/dev changes only); measurement began
2026-10-27 10:58:50 UTC. The baseline stores all raw samples, checksums, heap
checkpoints, GC stability and gate results.

| Lifecycle | µs/spin (median of 3) | B/spin |
| --- | ---: | ---: |
| L0 | 283.382 | 52,723.997 |
| L-child | 558.820 | 255,218.219 |
| L2-await | 79.192 | 71,553.491 |
| L2-track | 129.514 | 76,396.691 |

| Fork+discard fixture | µs/fork | B/fork |
| --- | ---: | ---: |
| 1k live worlds, empty parent | 440.242 | 33,784.416 |
| 5k live worlds, empty parent | 485.926 | 55,340.984 |
| 1k live worlds, 10k parent entities / 1k parked runs | 159.446 | 33,683.368 |

The populated fixture verifies 9k node rows plus 1k runtime atom rows, including
1k running/parked spins. Each fork sample measures 1k operations after 200 warmups.
Fixture order/JIT effects are visible in the timings; these three points do not
constitute an asymptotic proof about parent size.

| 100k enumeration | Heap at 10k, B | Heap at 100k, B | Ratio | cycles/s overall |
| --- | ---: | ---: | ---: | ---: |
| fork→run→discard | 39,325,168 | 38,887,240 | 0.988864 | 3,082.488 |
| spin create/complete | 42,872,456 | 87,263,608 | **2.035424** | 7,540.877 |

All four GC samples stabilized in 2.7–3.1 s. The sampled node, atom, continuation,
subscription, spin-tracking and incremental tables are empty at each checkpoint.
This does not establish that every other engine index is empty.

**16 gate checks pass; 2 fail on main.** Fork time scaling is 1.103772× (passes),
but fork allocation scaling is **1.638062× > 1.5×** (fails). Parent-size ratios
pass the stated literal comparison. Spin retained heap grows **103.542%**, above
the 5% allowance (fails). Fork retained heap passes. Lifecycle and throughput
relative gates compare the recorded baseline with itself; their passes establish
the reference point, not an independent performance regression result.

The benchmark measurement command exits 0 because it successfully records data;
the separate stored-baseline gate comparison prints **FAIL** for the two conditions
above and exits **1** (`gates-main.log`). The gates were not adjusted to accept main.

## Validation and open items

- Final lockstep smoke: **11 tests, 23 assertions, 0 failures/errors**
  (`final-oracle.log`). Corruption and unavailable-component tests verify a red
  oracle, rather than just checking successful execution.
- Standalone check: **exit 1**, with the reported discrepancies and known F50/F51
  normative failures; `lockstep-final.edn` records all replay attempts.
- Gate rule tests: **2 tests, 15 assertions, 0 failures/errors**, run with Babashka.
  Threshold mutation: **8 failures**, demonstrating sensitivity to regressions.
- Benchmarks: completed once, exclusively, `-Xmx3g`; raw baseline recorded.
  Stored-baseline gate comparison: **exit 1**, 16 passes / 2 failures.
- Full JVM suite: **1,450 tests, 72,438 assertions, 0 failures/errors**, **exit 0**.
  Run once after the benchmark under the same exclusive reservation; output was
  captured to `jvm.log` and inspected for failures/errors and final counts.
- CLJS: `slot.sh a3-cljs env JAVA_TOOL_OPTIONS=-Xmx1g ... compile ci` followed by
  `node out/ci-tests.js`: **539 tests, 2,027 assertions, 0 failures/errors**, exit 0.
- Cljfmt **0.9.2**, through Babashka: all seven new code files pass. `git diff
  --check` passes. Neither `src/` nor any reference-model file was changed.

Admission initially waited on other sessions. A mistakenly invoked `:test` alias
probe was stopped during discovery; the standalone command now explicitly clears
that alias's main options. An interrupted queued wrapper needed an explicit TERM
to its verified A3-owned host process; no process belonging to another session was
stopped and no other session's lock was removed. The eventual benchmark/full-suite
reservation completed normally.

Open acceptance work is explicit in the support/component tables: full scopes,
ownership, run generations, obligation/token protocols, registry, world messages,
cuts and saga records require B1–F2. In particular, the current microstep boundary
and negative-token diagnostics are **harness limitations**, not newly established
engine bugs. Main already fails the fork allocation and spin retention gates;
future implementation steps must not treat recording this baseline as permission
to ignore either absolute gate. The supplied af0bd82 model retains F50/F51 failures; newer read-only spec work
now lists Run 7/8 follow-ups. Incorporating those model changes is outside A3.


## Retention diagnosis and final disposition

The measured spin-retention failure is an existing-main correctness finding,
classified **new Spindel bug** beyond the defects explicitly listed in plan §0.
A source-verified retained index is a likely contributor: `seed-body-chain-head!`
inserts one `[:addressing :chain-heads spin-id]` entry and one
`[:addressing :occurrences spin-id]` entry at body entry. `full-cleanup-spin!`
removes the node, metadata, continuations and subscriptions, but never removes
those per-spin addressing entries. Both maps therefore grow across distinct spins
in a retained root even after their nodes are cleaned. The fork-enumeration root
does not acquire the child worlds' per-spin addressing entries, consistent with
its flat heap measurement. Attribution of the entire heap increase to these maps
is an **inference**, not a heap-dump result.

The minimal native reproducer is `create spin → invoke to completion → inject
:gc-cleanup through PEngine`, then compare node and addressing-row counts via
PState. A one-spin diagnostic plus timed smoke rerun was queued through `slot.sh`
with `-Xmx1g`, but was **blocked by shared admission** and never launched. Its
wrapper was stopped; no runtime result or smoke timing is claimed for that extra
probe. The reproducer is retained at
`~/Development/spindel-work/impl/a3/retention-diagnostic.clj` for a later admitted
slot. The already completed smoke runs, full JVM/CLJS suites and exclusive 100k
measurements are unaffected. No benchmark was repeated or gate relaxed while
investigating this finding. A later B3/B5 cleanup change should add addressing
counts to the census and pin removal of these auxiliary rows.

Commits before this report/data commit:

- `f114cb5` — `test: add partial lifetime lockstep oracle`
- `e40cd50` — `perf: add lifetime fork and enumeration benchmark gates`
- `7914b48` — `test: tighten lockstep projection and trace minimization`

No push or amend. Source and model semantics remain unchanged. The requested
baseline and full-suite run completed; only the additional causal probe remains
unrun. All remaining lifetime acceptance gaps are explicit above.
