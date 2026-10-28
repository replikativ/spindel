# Engine memory v2: versioned world storage

Status: design candidate. The lifetime semantics in
[engine-formalism.md](engine-formalism.md) remain authoritative. This file
specifies a physical representation and its refinement obligations. No runtime
API is changed by this draft.

## Goal and unit of publication

One model transition (§4.4, including its Rule L closure) is the smallest
published unit. A successful transition has one linearization point for all
worlds it changes. A refused transition publishes nothing. User code,
callbacks, native operations and executor dispatch run only after commit.
T20–T25 also use their coordinator fences and cut protocol; a storage CAS
alone does not supply their admission or physical-return guarantees.

The engine may stage any number of edits within a transition. It may combine
consecutive model transitions only when no host read, fork, callback, user code,
foreign world, or model-visible event can observe the intermediate state.
This is an optimization to prove per path, not the default transaction rule.

A transaction returns a committed outbox of deliveries and commands. The
outbox is part of the committed version; dispatch after publication may be
repeated and must claim each obligation/event before invoking user code.
Retries of the state builder cannot perform effects.

## Physical layout

```text
WorldHandle
  id, store -> StoreHead, executor
  external handle arena

StoreHead (one per connected world lineage in the first implementation)
  epoch, world-id -> WorldVersion, registry, cut/admission state

WorldVersion
  status, admission, parent id or pinned basis,
  local shadow roots of versioned tables, queue/outbox
  entity index, run index, obligation index, scope index
  derived indexes: by-debtor, by-creditor, ownership children,
                   ready/graph order, token and foreign-dependency links

Versioned table
  immutable published root -> rows
  private builder: transient/editable nodes with an edit token; never reachable
                   from a published WorldVersion
```

Entity, run, obligation and scope rows follow §4.1.2. Source rows own the
logical value; derived indexes hold IDs and may be rebuilt. A continuation
belongs to its obligation. Process-local closures and timer handles live in the
owning world's arena, keyed by row ID; fork copy rules install only the
descriptors/continuations the model permits. This arena cannot confer a
retention reason absent a semantic row.

The first implementation uses Clojure's persistent hash maps and their
transient builders for ID-indexed tables. An ordered structure may serve ready
queues, topological rank, or range indexes. `persistent-sorted-set` is a
candidate for those ordered indexes and its editable-node/seal contract is a
pattern for ownership; it is not assumed to be the entity table. A custom
hashed or segmented directory must beat the hash-map baseline on the engine's
actual transitions, including single-row updates and forked reads.

## Builder, freeze and publication

1. Read one committed store head. All worlds and following ancestors read by
   the transition come from that revision. Retries rebuild from a new head.
2. Validate admission and the action's preconditions against that view.
3. Stage row/index edits in a builder. A touched shared path is copied once;
   a node created by this builder may be edited in place. Maintain a worklist
   of changed entity IDs and apply Rule L until it reaches its fixpoint. Do
   not scan all worlds or all entities for ordinary reclamation.
4. Seal edited tables and form new immutable `WorldVersion` values for the
   touched worlds. A seal may be O(changed paths), never O(world size). Lazy
   serialization/materialization is allowed; lazy logical mutation of a
   published version is not.
5. Replace the affected world entries in one immutable `StoreHead` and CAS
   the store head. On a failed CAS, discard the draft and retry from the new
   head. The builder and validation must be pure. The successful CAS is the
   only point at which new rows, indexes and outbox become visible, including
   foreign debtor retention and creditor obligations together.
6. Dispatch the outbox after the CAS. A delivery first claims its
   semantic slot in another transition. Native effects use stable IDs and the
   existing durable settlement records where required.

The reference model has actions that write another world's rows in the same
transition: T5/T6 foreign dependency admission and release, signal
notifications to foreign creditors, T19 inherited-debtor bundles, and cut
coordination. A local commit followed by a message is not equivalent to that
model: a concurrent release could observe the creditor obligation without its
debtor-side retention row. The single store root covers this case directly.
Its cost is an extra registry path per commit and CAS contention among active
worlds, even when their rows are disjoint. Measure both. If contention is
material, a later per-world-head design needs an atomic multi-world descriptor
or a formally revised foreign-action protocol before it can replace this one.

A storage node may be reused in place only while owned exclusively by the current
builder and unreachable from any published version. A published node is
immutable. Reference counts, if used, count *explicit engine ownership* of
roots/nodes; they never replace the edit-token rule or decide logical entity
liveness. JVM/JS host aliases are not visible to an engine-owned counter.
Dropping a count releases physical storage only; Rule L decides semantic
retention. An epoch or edit-token implementation is the safe baseline, and a
node-reference-count variant must beat it in paired measurements.

In particular, a thread may have read the old head immediately before another
thread replaces it. An internal count of world heads can now say "one owner"
while that reader still holds the old Java/JS object. Destructive reuse of a
previously published node therefore requires an explicit reader pin/hazard
protocol (including public snapshots) or is forbidden. The initial design
forbids it. Counts may help reclaim nodes or select among private builder
buffers, but do not authorize mutation of a published node.

This follows the useful part of the local
`../../persistent-sorted-set/doc/CONCURRENCY.md` contract: editable nodes are
single-writer, `persistent!` seals them, and publication is a separate
happens-before edge. Lean-style uniqueness reuse is a candidate optimization
for nodes whose internal ownership is provably unique, not a requirement for
correctness.

## Forks and reads

- **Root:** reads one committed store head. A transition may use a mutable builder,
  but no reader or fork sees it.
- **Frozen fork:** pins one committed basis root and starts an empty local
  shadow table. Its untouched reads use that basis forever. Freezing a
  following child must also pin the versions of its read-through ancestors
  from the same store head; a pointer to the child's version alone still
  reaches live parents.
  Fork creation and physical attach are independent of parent entity count,
  though pinning a following ancestor chain costs O(lineage depth).
- **Following fork:** untouched entity reads resolve through the parent's
  version in the *current committed store head*. Local writes shadow whole
  entity rows; tombstones hide parent rows. A transaction uses one store head,
  so its multi-row decision is internally consistent. Later transactions may
  see a newer parent version, as the contract permits. A foreign action also
  validates and publishes the debtor-side row in the same store CAS.
- **Inherited parked work:** T19/T23 share one immutable bundle root and
  install world-local execution/obligation descriptors according to the copy
  rule. Physical attach must not enumerate every copied row. Foreign debtor
  bundles are aggregated per debtor world.
- **Queues and egress:** each world has its own queue/outbox and claim records.
  Parent host callbacks and native claims are never copied as executable
  child callbacks. Cross-world dependencies use the model's pending-start,
  admitted and cancelling phases.

A fork taken during a body sees the last committed version. Any row whose
truth changed before that fork must already have been committed by its model
transition. Unprocessed notifications may be dropped only when the committed
state contains sufficient staleness evidence to reconstruct their effect.

## Observable transitions

| Transition | Required atomic contents before control escapes |
| --- | --- |
| Signal write | value/generation and notification or staleness evidence |
| T1/T2/T4 | entity, owner/run, token touch, caller obligation |
| T5 | obligation, continuation, indexes, debtor retention, parked state |
| T6 | slot claim, one-shot removal or standing update, run status |
| T7/T8/T9 | result/generation fence, completion event, delivery claim, successor run as specified by each separate transition |
| T10/T11/T13/T34/T36 | retirement, Rule L cascade, index/queue pruning, cancellation outbox |
| T16/T17/T18 | host token changes affect idle-cache retention only |
| T19/T20–T25 | pinned basis, copy evidence, admission/fence, child publication |
| T26–T33 | durable-capability/record boundary and recovery IDs |

Pure planning inside these transitions is private. Calls into arbitrary spin
code or external code are always outside a private builder. A statically
non-parking body can use direct execution after T4 publication and before T7,
while any engine API it calls still enters its own transition.

## Refinement and performance gates

A representation adapter projects each committed `StoreHead` to the
reference model's rows. Check L1–L25 after every successful transition and
unchanged state after refusal. Replay the complete staged lockstep traces;
do not hide unsupported edges by shortening a trace. In particular:

- L3/TL7: release reaches Rule L's fixpoint in one commit.
- L5/TL1/TL2/TL5: obligation slots are claimed once, never silently lost or
  resurrected by late delivery.
- L9/TL6/TL13: fork writes stay local and a cut pins one coherent basis.
- L13/TL16: physical storage and following-fork retention remain bounded.
- TL4/TL17: host GC changes only idle caches, never a wanted run.
- TL15/O12: callback execution uses the obligation's world and egress policy.

Check both JVM and CLJS publication/handoff behavior. Benchmark the same
matched reactive graphs and the existing lifetime gates: root, following and
frozen forks, large-parent paths, creation/retirement, world-size scaling,
allocation and retained heap. Compare a persistent-map builder, an edit-token
hash-map builder and (only if warranted) a custom table or explicit node-count
variant. Require semantic parity before judging speed.

An exploratory REPL probe put and removed 100 rows per two publications on the
JVM. Repeated persistent-map updates used about 52 KB and 8 microseconds per
cycle; a transient hash-map builder used about 7 KB and 4.4 microseconds. A
naive 256-bucket segmented table used about 123 KB and 46 microseconds. The
probe is not an engine benchmark, but it rejects the segmented layout as a
default and shows that the available transient map deserves the first full
transition benchmark. For single-row transactions the transient setup costs
more than direct persistent updates; the builder may choose the direct path.

A separate 200,000-commit REPL probe of a single scalar update measured about
62 ns for a local atom and 147 ns for the same update through a one-world
registry atom on this JVM. That isolates the extra registry path, not the cost
of an actual engine transition or multi-threaded contention. The decisive
comparison is a paired end-to-end workload on the replacement engine.

## Implementation sequence

1. Build the semantic transaction kernel against one `StoreHead`, projecting
   complete rows to the formal model after every transition. Start with B2
   obligations and Rule L, then B3 run generations, B4 scopes/cuts, and B5
   idle-cache GC. Preserve the existing runtime protocols at the API edge.
2. Implement T5/T6/T19 foreign edits as one store publication. Prove refusal
   leaves the old head intact; check stale callbacks and duplicate deliveries
   against the model. Test following and frozen fork views at every publication.
3. Attach the kernel to spin execution and callbacks only after the lockstep
   traces cover its transition set. Run the matched Missionary graphs and
   concurrent fork workloads before removing the old engine. A faster kernel
   alone is insufficient if CPS dispatch and host egress dominate afterward.
