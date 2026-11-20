# Readable preservation proofs for the v2 model: options and the target layout

Status: agreed design, 2026-11-19; stage 3 under way (§5c: `gl`; §5d: `g9`; §5e: contexts declared per part; §5f: `g8`; §5g: forwarding inferred). It is the plan for making the layer-1 preservation proofs (`inv-step`)
readable; the staging is in section 5. Stage 0 is this note and the README section "How the step proof
works". The numbers describe the model as of the restructure (PR #304, e04b1a9) and were measured
without changing it: a static read of the sources with a small s-expression reader (the appendix says what
each measurement counted). They are syntactic approximations; section 5 lists the REPL experiments that
would confirm them.

## Summary

The proof that every reachable world satisfies `inv` has a simple core that the current code hides. A step
is a raw transition followed by Rule R. Both are built from 39 primitive table edits. `inv` is a conjunction
of about 45 parts on top of a base invariant. Each part survives each edit for one of four reasons:

1. **Frame:** the edit does not change what the part reads.
2. **Local obligation:** a short argument at that edit.
3. **Deferred within a step:** the part is broken for a named set of ids inside the step and repaired
   before the step ends.
4. **Companions:** the argument uses other parts of the input world, and the dependencies form a DAG.

### Terminology: deferred within a step

One world-step is a transaction. `inv` holds at commit: before the step and after it. No one observes a
world in the middle of a step (the engine commits whole steps, no other world sees a half-done one, and the
oracle compares committed states only). Inside the step a part may be violated for named ids and restored
before the step ends, like a constraint declared `DEFERRABLE INITIALLY DEFERRED`, or an `ON DELETE CASCADE`
that deletes row by row and is consistent again only when the cascade has finished. The exemption set of a
part (for example `g8`'s escape list, the runs of the pending cancel jobs) is the set of pending deferred
violations; it is empty at commit. The literature analogue is seL4's `invs_except`. Deferral is per part
and per transition, not one global relaxed invariant (section 3, option D).

Earlier drafts called this "temporary break and repair". The lemmas that open and close a deferred
violation are still called *break* and *repair* lemmas.

The code expresses this through a source-level copier, which reruns the base proof once per part. The
copier is sound, but most of the hand-written proof text is plumbing:

- Of the 331 `override!` forms, an estimated half re-prove a whole call chain only to pass one fact down
  to the edit that needs it: a guard, a lookup result, membership in a table, or a companion invariant.
- The 94 `patch!` forms rewrite proof terms as text.
- 969 of the 1,357 (primitive, part) cells are declared frames by hand, as `nil`.

**Recommendation:** combine three options and stage them:

- **(B) Views:** each part declares what it reads, so frames come for free.
- **(D) Exemption forms:** deferred violations get a uniform API with break and repair lemmas.
- **(A+) A generic step tree with full call-site context:** the tree is proved once over an abstract part.
  Its leaf obligations receive the path condition and the companions, so the plumbing overrides disappear.

A part then reads as a table of the few edits that matter to it, plus the transitions where it is
deferred.

---

## 1. The proof idea

**In words.** `reach-inv` is induction on `Reach1`. `inv-empty` covers the empty world and `inv-step`
covers a step, so all the work is in `inv-step`.

The step (`engine.clj:3440-3447`) is defined as follows.

- `world-step w it = finish (raw w it)`.
- `raw = post ∘ raw0g`. `raw0` does a case split over the 49 constructors of `Item` (T1-T22 plus host
  operations). `post` cancels the losers of an accepted await.
- `finish` runs Rule R on the result if the item was accepted, and returns the input world otherwise.
- Rule R is `rr-loop` over rounds, where a round is `rule-r-filter ∘ normalize`.

Every transition is glue around **primitive edits**:

- Glue: case splits on a lookup or a guard, sequencing, `nat-fold` over a list, and loops bounded by fuel
  (the cancel cascade, normalization, Rule R's rounds, the fin loop).
- Primitive edits: insert, delete or update one row of one table; mark, unmark, remove or insert an edge;
  bump the allocator; `set-pins`, `set-released` and `set-pending-act`; Rule R's `filter-world`.

There are 39 such primitives, with 154 call sites in the 220 lemmas of the base proof.

`inv` is `Base ∧ P1 ∧ … ∧ Pn`. `Base = inv-sample`: exact pending counts, edges reference existing rows of
the right kind, and ids are unique and below the allocator. The `Pi` are the parts, about 45 of them,
including helper parts. A part is preserved by the step for four kinds of reasons:

1. **Frame:** the edit does not change what the part reads. This covers about 68-71% of the (edit, part)
   cells.
2. **Local obligation:** the edit changes what the part reads, and a short argument shows that the part
   still holds. The argument uses the base, the part itself, the facts on the path to the edit (the guard
   that was checked, the row that was found) and companion parts of the input world.
3. **Deferred within a step:** an edit breaks the part for a named set of ids (the *exemption*), and a
   later edit in the same step repairs it. A loop carries the exemption as a ghost (for example, the
   escape list of I8 is the set of runs of the pending cancel jobs). The loop's termination (P4) empties
   it. In the code read so far, the repair always happens inside the composite that made the break: a raw
   transition (T14's local part, T12, the cancel cascade) or one round of Rule R (`g10`'s demotions).
4. **Companions:** a part's argument may use other parts of the *input* world. These dependencies form a
   DAG, so the conjunction is inductive even though no single part is inductive on its own. The 13-link
   chain `p3b ⊂ … ⊂ p3m` is one linearization of this DAG.

```
 reach-inv ── induction on Reach1 ──▶ inv-empty , inv-step
                                                   │
             inv w  =  Base w ∧ P1 w ∧ … ∧ Pn w     │  (conjunction; parts use earlier parts: DAG)
                                                   ▼
 world-step w it = finish (raw w it)
        ┌───────────────┴────────────────┐
   raw = post ∘ raw0g                rule-r = rr-loop (rounds)
   raw0: case on 49 items            round = rule-r-filter ∘ normalize
        │                                   │
        └──────────── composites ───────────┘   220 lemmas of the base proof (edits/step/rule/engine)
                 glue: case on lookup/guard · sequence · fold · fuel loop
                          │
                 39 primitive edits (154 call sites)
                          │
      for each part P and each edit e (one cell of a 39 × ~45 matrix):
        frame        view_P (e w) = view_P w                       ≈ 68–71 % of the cells
        obligation   Base w ∧ path ∧ C w ∧ P w → P (e w)           ≈ 23–29 %
        break        P[X] w → P[X ∪ {k}] (e w)       ┐ deferred within a step,
        repair       P[X ∪ {k}] w ∧ fact(k) → P[X] (e' w)  ┘ ghost X in loops
```

The companion DAG, read off the premises of the `step-<part>` theorems (`rule-r-safe` is P3, Rule R's
filter is safe; every part takes it, and it is derived from the `ri` parts of `p3b`). A simplified
picture; the README's table "Companions" lists the exact premises:

```
 ga ──┬──▶ gl, gr0, g8, aha                  (activations: acts-alive for Rule R, P4 for cascades)
      ├──▶ g7 ──┬──▶ gy ──┐
      │         ├──▶ gd ◀─┼── g10r ◀── p3b (all of ga, inv-rank, gl, g9, ri)
      │         ├──▶ ar   │
      │         └─────────┴──▶ v14 ◀── inv-rank
      └────────────────────────▶ hmk ◀── gd, g7, gy, g10r, inv-rank, v14
 p3la (everything above, plus ar and ekb) ──▶ h3
 no companions: inv-rank, g9, mdb, esb, gw, g1, g5, gso, ekb, svb
```

---

## 2. Why the current proofs are hard to follow

### 2.1 The mechanism

A bundle is `B w = inv-sample w && B-rest w`. Its step theorem comes from the copier (`inv.copier`,
`mk-bundle` ff.). The copier re-elaborates the whole `inv-sample` proof of the step: the 220 lemmas of
`edits`/`step`/`rule`/`engine` whose statement mentions `inv-sample`. In each copy it replaces
`inv-sample` with `B` and renames every callee to its copy. The four commands that control the copy are:

| Command | What it does | Count |
|---|---|---|
| `prim!` | the rest part under one primitive; `nil` means a frame | 410 forms (1,357 cells after `doseq` expansion, 969 of them `nil`) |
| `lcopy!` | copy the closure of a root | 209 |
| `override!` | replace one copied lemma with a hand proof | 331–337 (31 bundles, 134 distinct lemmas) |
| `patch!` | rewrite a source proof (as an s-expression) before copying it | 94 (some are `doseq` over *all* source theorems) |

The result is about 10,000 of the 16,119 kernel theorems, and an estimated 200–300 s of the 8-minute
load.

### 2.2 An override: `gl` through T14's local part

The base proof of `cancel-run-local` (`rule.clj:675`) is a five-line composition:

```clojure
(exact (inv-cancel-debtor rep _ r (inv-cleanup-set _ (:id r) _ (inv-cancel-res _ r
         (inv-cancel-acts _ (:id r) (inv-run-upd w (:id r) run-cancel-row run-cancel-row-id h)))))))
```

For `gl` (I10, task part: "a task without a result has an alive run"), the copy fails. The first edit
kills run `r`, so `r`'s task now violates `gl` until `debtor-side` gives the task its result. The
override `gl-cancel-run-local-o` (`inv/copier.clj` ~1365) is 30 lines that re-walk the composite. The
idea in it is three lemmas:

- **Break:** `glx-kill` turns `gl w` into `glx r.of (run-upd …)`. The exempt form `glx k` allows task `k`
  to be without a result and without a run.
- **Repair:** in each branch of `cancel-debtor` and `debtor-side`, one of these applies:
  - `gl-task-done-x`: the task gets `err ::cancelled`.
  - `gl-of-glx-comp`: the owner is a computation, so no task is exempt.
  - `gl-of-glx-find`: there is no such task.
- **Transport:** in between, `glx-kw` keeps the view (`cancel-mid-kw`: the activations, resources and
  cleanup edits do not touch the run and task keys).

The override is correct, but the reader has to reconstruct the break and repair structure from a proof
script. The same composite is overridden by 8 bundles, and `inv-dispatch-raw` by 11.

### 2.3 A patch: `g8` and the companion `ga`

To keep I8 through the cancel cascades, `g8` needs P4: the cascade's worklist empties. P4 needs the
companion `ga` (`casc-done-ga`). The base proof never carries `ga`, so `inv/i8.clj` does two things:

- `g8-add-ga` rewrites `raw0-inv`'s statement to take `(= (ga w) true)`, and `g8-ga-calls` rewrites 22
  call sites in its proof text so that `hga` is passed on (`(t12-inv w _ _ _ h)` becomes
  `(t12-inv w _ _ _ hga h)`, …).
- 15 overrides (`t14-inv`, `t-cancel-inv`, `t16-inv`, `t12-inv`, `raw-inv`, …) re-prove each transition
  between `raw0` and the cascade, only to forward `hga`.

`g8-patch` also rewrites the proof of *every* source theorem, replacing calls such as
`(inv-run-upd w x run-wake …)` with `(g8-run-upd x8s w x run-wake … run-wake-rkey …)`. This supplies the
fact that `run-wake` keeps the run key. Nothing the kernel checks for `g8` exists as text that a reader
could open.

### 2.4 An exemption list: `g8`'s escape list

The bundle is `g8 xs`, and I8 is `g8 []`. Closing a scope subtree (`close-local`) makes the alive runs of
tasks owned by the closed scopes violate I8. `g8-close-local` puts them on the escape list:
`g8 xs w → g8 (xs ++ owned-runs w sub) (close-local w sub)`. These runs are exactly the cancel jobs that
the cascade queues next.

The cascade's loop invariant is `g8 (base ++ cj js) w`, where `cj js` is the runs of the pending cancel
jobs (`g8-cascade`, `inv/i8.clj` ~1280). Each job discharges its own run. When P4 empties the worklist,
`g8-cascade-done` returns `g8 base`. This is a clean idea: ghost state equal to the pending work. It is
the same pattern as `glx k`, `hmk hxm`, `h3 xm`, `g5 xd` ("finality sites discharge in the same commit")
and `g10 gxz gkz` ("computations demoted later in the same round", "runs being retired").

### 2.5 Diagnosis, with numbers

**The base proof only carries the facts that `inv-sample` needs.** A guard that was checked (`cur-closed`
is false), a row that was found (`run-find w rid = some r`), membership (`r ∈ runs`), "this id is not a
computation id", or a companion (`ga`, `g7`, `gd`): each is dropped at the call site, because `inv-run-upd`
does not take it. A part that needs such a fact at one leaf has to override every lemma from the item down
to that leaf.

A classification of the 331 overrides by statement and dependencies (measurement E8, a heuristic):

| Kind | Count | Meaning |
|---|---|---|
| adds a premise and calls another override of the same bundle | 96 | plumbing: forwards a fact down the chain |
| same statement and calls another override | 66 | plumbing parents (e.g. `t4-top-inv` around `t4-inv`) |
| adds a premise and is self-contained | 80 | a leaf needs a local fact (42 distinct lemmas) |
| same statement and self-contained | 87 | content: break and repair, or reasoning over several edits (50 distinct lemmas) |

`g8`'s 51 overrides are three ideas plus plumbing:

- **Owners must be open (26 overrides):** a new task, source or link must not get a closed scope as its
  owner. This comes from the guards `cur-closed = false`, `root-ok-if` and `scope-open-at root`.
- **Revival (9 overrides):** a run that becomes alive again (park, take, arm, await) was alive before.
- **Termination (15 overrides):** the cascade empties the escape list, which needs `ga`.

One override (`t-detach-inv`) does not fit these three.

`hmk`'s 45 overrides include 13 that only pass the fact "x is not a computation id" to a leaf. That fact
follows from id uniqueness in `Base` and the fact that x is a source, activation or link id.

**There is no notion of what a part reads.** Of the 1,357 (primitive, part) cells, 921 (68%) are disjoint
at table level: the edit writes no table that the part reads (measurement E3). Another 42 are frames because
the edit keeps the part's key projection. The remaining 316 cells are real obligations. Today every frame
is a hand-written `nil` entry, and the kernel checks it again for every copy.

At the composite level, table granularity does not separate much. The large transitions (T12, T14 and
others with cascades) touch nearly every table, so a large part such as `gl` or `g8` is touched by about
50 of the 56 item-level transitions (measurements E4, E5). Small parts are touched by few:
`g1` (scope parents) and `ch` are each touched by 17 of 56. So views pay off at the leaves, and in
explaining which transitions matter to a small part.

**The structure follows the history.** The link names (`p3b`…`p3m`) and bundle names (`ga`, `gl`, `g9`,
`gd`, `v14`, …) record the order of the proof campaign. The README's tables make them findable, but the
companion DAG appears only in theorem premises.

---

## 3. Options

Each option is grounded in `gl` (few overrides), `g8` and `hmk` (override-heavy), `ga` and `gd` (patches,
companions), and `g9` (per-call-site resource lemmas).

### (A) One generic preservation theorem (`GPrim Q`, as in `notes/generic-preservation.md`)

Prove the tree once over an abstract rest part `Q` and a structure of obligations. A part supplies one
instance, and its step theorem is an application.

- **Effect:** removes the copier, the roughly 10,000 copies and an estimated 200–300 s of load. Every
  checked proof exists as source text. The prototype: 47 generic lemmas; `pgl : GPrim gl-rest` from
  `gl`'s 19 primitive fields; 46 of 46 of `gl`'s copies restated and proved by `exact (gq-… gl-rest pgl …)`.
- **`g9`:** the per-call-site resource lemmas (`g9-res-upd-q` at `res-cancel-row` and at
  `res-set-phase rp-fired`) force fields per call site, not per primitive. There are 154 call sites and 58
  distinct (update primitive, row function) pairs, so the obligation structure has roughly 90–150 leaf
  fields (estimate).
- **Overrides:** they become composite-level fields with generic defaults. For `g8` that is 51 fields
  supplied by hand, unchanged. The plumbing remains plumbing, now as field proofs.
- **Patches:** they become a companion context `C`, which the note leaves for its stage 3.
- **Readability:** better than today (no text rewriting, and the tree is read once). Without the
  extension in (A+), each part still carries its plumbing.

### (A+) The generic tree with full call-site context

This is (A) with one change: a leaf field receives everything that is in scope at its call site in the
generic proof:

- the base of the world at that point;
- the **path condition**: the guards that held and the lookup equations from the `cases` that led there
  (for example `run-find w rid = some r`, `run-alive r = true`, `cur-closed w st = false`);
- membership of the rows involved;
- the companion context `C` (the ancestors of the part in the DAG).

```lean
-- one leaf class: T14's local part kills run r
o-run-upd-cancel : ∀ w r, r ∈ w.runs → run-alive r = true → Base w → C w → Q w →
                   Q (run-upd w r.id run-cancel-row)
```

The generic proof always passes these facts. A part that does not need them ignores them, and its default
instance ignores them too. Each plumbing pattern above then becomes a leaf argument:

- **Guards (`g8`'s 26 overrides):** the leaf "insert a task with owner o" receives the guard on its path.
- **Revival (`g8`'s 9):** the leaf receives `r ∈ runs` and `run-alive r`.
- **"Not a computation id" (`hmk`'s 13):** the leaf receives the find equation of the source or
  activation, and derives the fact from `Base`.
- **`ga` (`g8`'s 15 and the patch):** `ga` is in `C`.
- **`g9`:** its per-call-site lemmas are the fields for those two leaves.

Estimate: plumbing (about 160 overrides) and patches (94) disappear. What remains is about 80 leaf proofs
that use a local fact (now ordinary fields) and about 50 distinct composite-level fields with real content.

**A caveat.** A path condition is a fact about the world in which it was tested. A leaf that runs after
further edits receives it for an earlier world. Carrying it forward is a frame argument (B) when the fact's
view is untouched in between. This is what the helper bundles `ch`, `ka`, `na` and `kx` do today. In
(A+), such a fact becomes a small view-stable predicate that the generic tree carries with its frame.

**How the leaf contexts are produced.** Either by hand, by writing the generic tree directly over an
abstract part (a VCG-style lemma per composite), or by the copier, which would emit leaf statements from
the local context at each call site. The second needs the hypothesis types in scope at the call site,
which means elaborating, not just reading s-expressions. This is the main technical unknown (R2 in
section 5).

### (B) Views and stability: each part declares what it reads

Each part `Q` gets three things:

- a **view** `view_Q : World → V_Q` with `Q w = Q' (view_Q w)`;
- a **rely** `R_Q`, a reflexive and transitive relation on views under which `Q` is stable
  (`R_Q (view w) (view w') → Q w → Q w'`). Equality is the simplest rely; a monotone order is the general
  one.
- a frame lemma that follows from the two.

An edit whose effect on the view stays within `R_Q` is free. A matrix of 39 edits × parts records only the
non-free cells. This is the Event-B / Dafny discipline (section 3E).

The model already does this, but as an idiom for each bundle separately:

- `gl` uses `kw = (rkeys runs, tkeys tasks, next-id)`, where `RKey = (id, of, alive)` and
  `TKey = (id, run, done)`. `gl-rest-kw` is its frame. The `extra-args` entry
  `'inv-run-upd ['(fn [r] (Eq.refl (rkey r))) 4]` discharges the column-level side condition "f keeps the
  key" by `rfl` at every call site.
- `g8` uses `kw8` (runs, task (id, owner), scope (id, open), source (id, owner, open)); `g9` uses
  `RK9 = (id, mode, resources)`.
- `gd`'s frames are monotone, not equalities: `cmono` allows edits that keep or clear `C.run`, do not lower
  the epoch, and keep or clear `done-epoch`. `hmk` chose a strict `<` so that "every epoch step is a frame".
  Both are rely relations.
- The base itself does this: `defframes` in `edits.clj` (`pending-exact` "reads only comps' id/pending and
  edges' creditor/marked").

What (B) adds:

- Views become a declared, uniform part of every part.
- Frame cells disappear from the source: they are derived from "edit e writes only table T" (one `rfl`
  lemma per edit) and a key lemma per table (`rkeys-upd`, `tkeys-upd`, …).
- Each part's namespace starts with its non-frame table.

Examples:

- **`ch`** ("computation cx exists", a helper used inside T11): today 8 proof cells and 25 `nil` cells.
  With the view `ids of comps`, every cell is a frame except `comp-ins`. Even the edge edits that change a
  creditor's `pending` keep the ids.
- **`gl`, `g8`:** the views are already shared. `rkeys` appears in `gl`, `g8`, `g10` (with epoch) and `ar`
  (`arrk`), so a lemma about how a composite moves `rkeys` serves all of them (see (C)).

Limits:

- (B) alone does nothing for plumbing or deferred violations.
- At composite level, table-level footprints spare few transitions for large parts (section 2.5).
- Column-level footprints need the row functions' effects. They are syntactically recoverable for the
  `RowT.mk` row functions, but not for `fn` literals.

### (C) Transition contracts and view summaries

State each transition's net effect as a relation and prove the parts against it. Done fully, this removes
the intermediate worlds: the break inside T14 would happen in T14's contract proof, which is
part-independent, and no exemption would be needed for it. Writing full contracts for the cascade and
Rule R amounts to their functional specification, which is a large effort and close to the content of
P2/P4.

The light form pays off now: **view summaries**, the net effect of a hot composite on a shared view. The
model already has some:

- `kw8-cancel-run-local`: on `kw8`, T14's local part only lowers the alive bit of `r`.
- `cancel-mid-kw`, `kw-retire-with`, `kw8-debtor-side`.

The hot composites, ranked by how many bundles override them, are:

| Composite | Bundles overriding it |
|---|---|
| `inv-dispatch-raw` | 11 |
| `inv-spawn-rows` | 10 |
| `inv-cancel-run-local`, `inv-take-park`, `inv-start-raw` | 8 each |
| `inv-retire-one`, `inv-complete-raw`, `t12-inv`, `inv-await-raw`, `inv-arm-park` | 7 each |

A summary per (hot composite, shared view family) gives each part a one-line reason at that composite.
`notes/hm13-contracts.edn` shows that contracts are already the working tool during the proof campaigns.
(C) is compatible with everything else: a summary is a lemma that field proofs use.

### (D) Exemption forms as a first-class pattern

Every part that is ever deferred within a step gets a uniform API:

- an exempt form `Q[X]`, with `Q = Q[∅]` and `Q[X] → Q[X ∪ Y]` (monotone);
- **break lemmas** `Q[X] w → Q[X ∪ {k}] (e w)`, and **repair lemmas** `Q[X ∪ {k}] w → fact k → Q[X] (e' w)`;
- for loops, the ghost is a function of the worklist (`cj js` for `g8`, the pending fires for `g5`).

The model has the forms (`g8 xs`, `glx k`, `hmk hxm`, `h3 xm`, `g5 xd`, `g10 gxz gkz`, `grx`, `mdk`,
`gnf`) and many break and repair lemmas (`g8-close-local`, `glx-kill`, `gl-task-done-x`, `g8-cascade`). They
are not uniform: the exemptions are bundle parameters for some parts and separate predicates (`glx`) for
others, and naming varies.

(D) is mostly naming, statement normalization and documentation. Each part file gets a section "where `Q`
is deferred within a step", one entry per composite, written as "break at …, repair at …". This is what the
content overrides (about 50 distinct lemmas) encode.

The literature analogue is seL4's `_except` invariants (`invs_except`: the invariant minus one object or
queue, used between two kernel operations). In database terms (section "Terminology" above) `Q[X]` is the
constraint with the deferred violations `X` pending; commit requires `X = ∅`.

(D) also answers the question "can intermediate states be first-class?". A single weaker "in-transition
invariant" with an exemption set, plus a theorem that Rule R restores the full invariant, does **not** fit
this model. The breaks happen and are repaired *inside raw transitions* (T14, T12, the cascade), or inside
one round of Rule R (`g10`'s demotions). They are not left from the raw transition for Rule R to repair,
and each part has its own exemption type: task ids, run ids, computation ids or member ids. The exemption
is therefore per part and per transition, not global.

### (E) Related approaches

- **Event-B / Rodin.** One invariant-preservation obligation per (event, invariant). The generator omits it
  when the event assigns no variable that the invariant mentions. This is option (B) at variable
  granularity, and the "matrix with only the non-trivial cells" layout proposed here.
- **TLA+ / TLAPS.** `Inv ∧ Next ⇒ Inv'`, split by action and by conjunct, with `UNCHANGED` as the frame.
  Hierarchical proofs whose top levels read like section 1.
- **Ivy, IC3/PDR.** Invariants as conjunctions that are *inductive relative to* other conjuncts, checked
  per action, with counterexamples to induction. This is the companion DAG; "relative inductiveness" is the
  name to use for it.
- **seL4 (Isabelle, l4v).** Per-function Hoare triples; the `wp` tactic for composition; `crunch`, which
  proves invariant and frame lemmas automatically by walking definitions (the closest analogue of the
  copier); and `_except` invariants for intermediate states. Lesson: their preservation proofs scale to
  hundreds of invariants × functions because frames are automatic and nontrivial triples are named per
  function. They are readable mainly through naming conventions and per-function lemma lists, not through
  structure.
- **Dafny / dynamic frames (Kassios 2006).** `reads` clauses on predicates, `modifies` clauses on methods,
  and framing derived from their disjointness. This is (B).
- **Rely-guarantee (Jones 1983), Iris and separation logic.** *Stable* assertions under a rely; the frame
  rule `{P} c {Q} ⊢ {P * R} c {Q * R}`. The rely view of (B) explains `gd`'s and `hmk`'s monotone frames.
- **Lean 4.** `Std.Do` with `mvcgen` (2025): Hoare triples and VC generation for programs written in a
  monad. Veil (CAV 2025): Ivy-style transition-system verification in Lean. Both are pointers; I have not
  checked their current state. The ansatz DSL has neither.
- **A deep embedding** (the principled long-term variant). Write the transitions as data, in a small
  program language of edits, `ite`, lookup-bind, `fold` and loops. Give it an interpreter
  (`run : Prog → World → World`), a footprint function, and a `wp` with a soundness theorem proved once.
  Obligations would then be *computed* with their path conditions, frames discharged by footprint, and
  the matrix printable. It is the cleanest end state, but it requires restating `engine.clj`/`rule.clj` as
  programs plus refinement proofs `run prog-T = T`. It is not recommended now.

### Compatibility

- (A+) contains (A). (B) and (D) are orthogonal to (A) and make it smaller:
  - (B) supplies default leaf fields, so a part writes only its non-frame cells.
  - (D) gives the composite-level fields a uniform shape.
- (C) is a library of lemmas used by field proofs. It needs nothing from the others.
- (B) and (D) can be done inside the current copier world, as declarative front-ends and renames, before
  any change to the proof engine.
- The deep embedding replaces (A)/(A+) and makes (B) automatic, but it is a model rewrite.

---

## 4. Recommended layout: (B) + (D) + (A+), with (C) where it pays

### 4.1 Namespace tree

```
spindel.v2.top                    reach-inv, inv-step, inv (unchanged statements)
spindel.v2.inv.parts              the parts as a DAG: list, companions, inv-step assembly
                                  (p3b … p3m kept as abbreviations; old step-p3* restated)
spindel.v2.pres.core              Base, View/Frame, Leaf C Q, Over C Q L, PartProof, defpart
spindel.v2.pres.frames            per-edit "writes only table T" lemmas; per-table key lemmas
                                  (rkeys-upd …); default leaf from a view
spindel.v2.pres.tree.*            the generic step tree, once, over an abstract part:
    .edits   .rule   .cascade   .items   .step
                                  each composite lemma is stated as
                                  Leaf C Q → Over C Q L → Base ∧ C ∧ Q → Q (T …)
                                  and ends with `step-pres`
spindel.v2.pres.summaries         view summaries of hot composites ((C))
spindel.v2.inv.<part>             one per invariant part, fixed layout (4.4)
spindel.v2.inv.members.*          h-mem2 (h3): same layout; its many stages become sections
```

`inv.copier` survives only until the last bundle is converted (staging, section 5).

### 4.2 Key definitions and theorems

Lean-like notation; the DSL forms are the `a/structure` and `a/theorem` analogues. Following the
prototype, the obligation structures live in `Type` and their instances are `a/defn`.

```lean
def Base (w : World) : Bool := inv-sample w

/-- A part's view and frame: Q reads only `view`. -/
structure Frame (Q : World → Bool) (V : Type) where
  view  : World → V
  frame : ∀ w w', view w' = view w → Q w' = Q w      -- or a rely: R (view w) (view w') → Q w → Q w'

/-- Leaf obligations: one field per call-site class, with that site's context.
    ≈ 90–150 fields (estimate: 154 call sites, 58 (update primitive, row function) pairs). -/
structure Leaf (C Q : World → Bool) : Type where
  run-upd-cancel : ∀ w r, r ∈ w.runs → run-alive r → Base w → C w → Q w → Q (run-upd w r.id run-cancel-row)
  task-ins-spawn : ∀ w st r owner, tok-run w st = some r → sclosed w owner = false → …
                     → Base w → C w → Q w → Q (spawn-rows w owner inputs loc)
  …

/-- Composite points where some part is broken mid-transition (≈ 50 fields), each with a default
    proved once from the leaves. -/
structure Over (C Q : World → Bool) (L : Leaf C Q) : Type where
  cancel-run-local : ∀ w r rep, r ∈ w.runs → Base w → C w → Q w → Q (cancel-run-local w r rep)
  run-cascade      : ∀ w js, Base w → C w → Q w → Q (run-cascade w js)
  complete-body    : …
  …
def Over.default (L : Leaf C Q) : Over C Q L      -- the generic tree's own proofs

structure PartProof (C Q : World → Bool) : Type where
  leaf : Leaf C Q
  over : Over C Q leaf

/-- The one generic step theorem (pres.tree.step). -/
theorem step-pres (KC : CarryC C) (P : PartProof C Q) :
  ∀ w it, Base w → C w → Q w → rule-r-safe (raw w it).world → Q (world-step w it).world

/-- Defaults: a leaf of an edit that keeps the view is a frame. -/
theorem leaf-of-view (F : Frame Q V) (keeps : EditKeeps F.view) (own : OwnLeaves C Q) : Leaf C Q
```

`CarryC C` says that the companion context survives the intermediate worlds. It is assembled from the
companions' own `PartProof`s, since every companion is an earlier part of the DAG. This is the note's
stage 3 and the least certain piece (R4).

`defpart`, a Clojure macro in `pres.core`, turns a table into a `PartProof`:

- every leaf that is not listed is a frame, proved from `Frame` and the edit's footprint lemma;
- every override point that is not listed takes `Over.default`;
- it then states `step-<part> := step-pres …`.

The table is what a reader reads.

### 4.3 How a reader navigates

`reach-inv` → `inv-step` (`top`) → the parts table in `inv.parts` (one row per part: spec item, view,
companions, step theorem) → `step-gl := step-pres gl-ctx gl-proof` → the `defpart gl` table → one cell,
for example `retire-local ↦ gl-retire-local-o` → `retire-rest`, a 30-line lemma about clearing the
task's run and deleting the dead run row.

To see *how* T13 is put together, read `pres.tree` once (`gen-retire-local`). To see *why* `gl` survives
T13, read the one cell. Today the second question takes the generated copy (which is not in the source),
the override, and the patch of `inv-job-apply` that passes membership facts down.

### 4.4 What a part file looks like, and what changes cost

Every part file has the same six sections:

1. **The part:** `Q`, its spec item, a statement in words.
2. **View and rely:** `view_Q`, the frame lemma.
3. **Exempt form** (if any): `Q[X]`, monotonicity, and the break and repair lemmas.
4. **Obligation table:** only the leaves that write the view; each has a lemma and a one-line reason.
5. **Deferred within a step:** only the composites where `Q` is broken mid-step; each is "break at …,
   repair at …".
6. **Companions and assembly:** `defpart`.

The costs of changes:

- **A new part:** the six sections. Today an average part has about 8.6 non-frame leaf proofs
  (388 cells over 45 parts) and, after (A+), an estimated 0–5 composite entries. There is no copier run;
  the step theorem is an application.
- **A new primitive edit:** a new leaf field.
  - Parts whose view the edit does not write get it automatically from the edit's footprint lemma.
  - Parts whose view it writes need a real proof: exactly the cells a human must think about.
  - Today a new primitive is a `prim!` in all 51 bundles plus a copier rerun.
- **A new transition:** one generic lemma in `pres.tree`, written once. New call sites become new leaf
  fields, defaulted by frames for most parts.

### 4.5 Worked example 1: `gl` (I10, task part)

```clojure
(ns spindel.v2.inv.i10-task      ; today: bundle gl in inv.copier
  "I10, task part. In words: (a) every run's `of` is below the allocator; (b) a run R of a task K is
  K.run; (c) a task without a result has an alive run.")

;; 2. View: run keys (id, of, alive), task keys (id, run, done), the allocator.   (kw, gl-rest-kw)
;; 3. Exempt form: glx k — (c) may fail for task k.   glx-kw (frame)
;;    break  glx-kill            a run made done: only its task r.of may lack a run
;;    repair gl-task-done-x      the task gets its result;  gl-of-glx-comp: r.of is a computation;
;;           gl-of-glx-find      there is no task r.of
(defpart gl
  :rest gl-rest :view kw :frame gl-rest-kw :exempt glx :companions [ga]
  :leaf {run-upd/wake    run-wake-rkey          ; resume (Z#50): key kept -> frame by lemma
         run-upd/park    gl-run-upd-up          ; alive goes up: (c) only gains witnesses
         run-upd/kill    glx-kill               ; BREAK (cancel, complete)
         task-upd/result gl-task-done-x         ; REPAIR
         new-run-of/comp gl-comp-run-o          ; `of` is a computation, not a task (comp-has on the path)
         bump            gl-rest-bump           ; (a) is monotone in the allocator
         filter-world    gl-filter-world-o}     ; Rule R keeps alive runs (normalized; uses ga's acts-alive)
  :over {cancel-run-local gl-cancel-run-local-o ; T14 local: break at run-upd, repair in debtor-side
         complete-raw     gl-complete-raw-o     ; T12: break at run-upd, repair at complete-task
         retire-local     gl-retire-local-o     ; T13: clear the task's run, delete the dead run (retire-rest)
         spawn-rows       gl-spawn-rows-o})     ; T4: new task + its alive run, inserted together
```

What disappears compared with today:

- the 32 `prim!` lines, which become 7 leaf entries; the rest are frames;
- 4 of the 9 overrides, which were plumbing:
  - `t12-inv` forwarded `res-tag-ok`, a guard on the path;
  - `inv-retire-one` forwarded membership and `run-alive`;
  - `inv-start-raw` and `inv-dispatch-raw` forwarded `comp-has` (today through the helper bundle `ch`);
- a fifth override, `inv-new-run-of`, becomes a leaf entry;
- the 6 patches (`up-patch`, `run-wake-rkey`, `inv-job-apply`, `raw0-inv`, `t5-inv`, `t11-inv`), which
  supplied key lemmas at call sites or forwarded facts.

The `ch` bundle disappears as well. Its fact, that computation `c` exists, is tested on the path at the
input world. Its view (the computation ids) carries it to the leaf after `cancel-pred` and `cut-suffix`,
because neither writes that view: a (B) frame. The proofs that stay are the same
lemmas as today; they move into the table.

### 4.6 Worked example 2: `g8` (I8, closed scopes)

```clojure
(ns spindel.v2.inv.i8
  "I8: a closed scope owns no alive run (of its tasks) and no open source.")
;; 2. View: kw8 = run keys, task (id, owner), scope (id, open), source (id, owner, open).  g8-of-kw
;; 3. Exempt form: g8 xs, the ESCAPE LIST: alive runs of tasks owned by closed scopes that are
;;    allowed for now. Ghost: in the cascade, xs = base ++ runs of the pending cancel jobs.
;;    break  g8-close-local      closing a subtree appends owned-runs (they are the next cancel jobs)
;;    repair g8-job-cancel       a cancel job kills its run
;;    loop   g8-cascade          invariant g8 (base ++ cj js) through every job
;;    exit   g8-cascade-done     P4 (casc-done-ga, needs companion ga): js = [] at the end
(defpart g8
  :rest g8-rest :view kw8 :frame g8-of-kw :exempt [x8s] :companions [ga]
  :leaf {task-ins/owner   g8-owner-open      ; a new task's owner is not closed: guard on the path
                                             ;   (cur-closed = false — model-only, P10 open!; root open;
                                             ;    detach-ok; a computation owner)
         source-ins/owner g8-owner-open      ; same, for sources and links
         run-upd/revive   g8-run-upd-up      ; park/take/arm/await: the run was alive (r ∈ runs, alive)
         source-upd/close g8-source-close    ; a source closes
         task-upd/detach  g8-task-owner      ; a new owner that is an open scope (detach-ok)
         run-del          g8-rest-run-del
         scope-del        g8-rest-scope-del}
  :over {run-cascade      g8-run-cascade-ga})  ; break (close-local inside close/retire jobs), repair
                                               ; (cancel jobs), loop invariant with its ghost, and P4
```

Of the 51 overrides, under (A+) these remain:

- the cascade field, with its ghost. The break (`close-local`, applied inside the close and retire jobs)
  and its repair both happen inside the cascade, so a single composite field holds them;
- possibly `t-detach` and `inv-serve-or` (to be checked).

The 26 creation overrides become two leaf entries whose path condition carries the guard. The 9 revival
overrides become one leaf with `r ∈ runs ∧ run-alive r`. The 15 `ga` overrides and the `g8-add-ga` patch
disappear into `C = ga`. The source-text patch `g8-patch` (wake, consume, close, detach rows) becomes four
leaf entries.

Estimate: 51 overrides and 3 patches become about 10 table entries and 1–3 composite entries.

A side benefit is that the dependency on the model-only guard `cur-closed` (P10, open) becomes one visible
cell of the I8 table. Today it is buried in 26 plumbing overrides.

For `hmk` (45 overrides), the same treatment turns the 13 "not a computation id" overrides into one fact
that the generic leaves derive from `Base` and the find equation. The remaining content is the fire and
dispatch reasoning and the `gd`/`g7` companions.

---

## 5. Effort, staging, regression, risks

Estimates assume one person working on this full time, with wide error bars (a factor of 2).

| Stage | What | Breaks nothing because | Estimate |
|---|---|---|---|
| 0 | Docs only: section 1 into the README; the companion DAG; per-part obligation tables generated from the copier's atoms (renames, overrides, patches) | no proof changes | 2–3 days |
| 1 | (B)+(D) inside the copier: a declared view and frame per part (most exist: `kw`, `kw8`, `glx-kw`, …); `defpart` as a front-end that *emits today's* `prim!`/`override!` calls; uniform exempt names and break/repair docs | same generated theorems | 1–2 weeks |
| 2 | (A) on the clean part of the tree; convert the 11 bundles without overrides or patches (`ch`, `edb`, `gnf`, `gox`, `kc`, `kx`, `mdk`, `na`, `neb`, `vr`; `gx` has none); measure load | each converted bundle restates its old names | ~1 week (note's estimate) |
| 3 | (A+) leaf contexts: leaf fields with path conditions; convert `gl` and `g9`, then `g8`, `hmk`, `g7`, `gd`; their plumbing overrides are deleted | old statements restated | 2–4 weeks (main unknown) |
| 4 | Companions `C` and `CarryC`; delete the patches (`g8-add-ga`, `gd-add-hyps`, …) | old statements restated | 1–2 weeks |
| 5 | `inv.parts` as a DAG; `p3b`…`p3m` and `step-p3*` become restatements | `top` statements byte-identical | 2–3 days |
| 6 | (C) view summaries for the hot composites, as field proofs are rewritten | additive | ongoing |

Stages 0–1 alone give most of the *explanation* benefit and no load-time benefit. Stages 2–4 give the
structural benefit: no generated theorems, no text rewriting, and about 250 fewer override and patch forms.

**Regression check at every stage:**

1. A statement dump (name → elaborated type) of every theorem that is hand-written or referenced from
   outside the copier, taken before and after. Every surviving name must have an identical statement.
2. Every generated copy that is still referenced is restated and proved from the generic instance, as in
   the prototype's `check-bundle!`, until nothing references it.
3. `top`'s `inv`, `inv-step` and `reach-inv`, and `layer2.top`'s `sys-reach-inv`, must be unchanged.
4. The oracle tests are unaffected, since no definition changes; run them anyway.
5. Load time is measured per stage.

**Risks and unknowns, and the experiment that settles each:**

| # | Risk | Experiment |
|---|---|---|
| R1 | A `Leaf` structure with 90–150 dependent fields (plus `Over` with about 50) may be slow to elaborate or project in the ansatz DSL, and instances in `Type` lose proof irrelevance | a synthetic structure with 150 fields of the leaf shape; time the instance and 200 projections; also try a `Prop`-valued conjunction encoding |
| R2 | Leaf contexts: can field statements be generated (the hypothesis types at each call site), or must the generic tree be written by hand? | hand-write the generic `cancel-run-local` and `complete-body` with full-context leaves; check that `gl`'s and `g9`'s overrides of them become field proofs; then try extracting the local context at a call site from the elaborator |
| R3 | Every composite overridden by *any* part must be a field, and the generic parents must call the field, not the default; the field list may grow | compute the union of override targets per stage (134 today, about 50 content); keep it as a checked list |
| R4 | Companions through intermediate worlds (`CarryC`): the DAG has depth 4 (`ga`→`g7`→`gd`→`hmk`) | convert `gd` (companions `g7`, `g10r`) on T6 and T12 first |
| R5 | Exemption ghosts change *inside* loops (`g8`'s `cj js`, `g10`'s `gxz`), which a fixed-`Q` tree cannot express | keep them as `Over` fields (hand proofs, as today); check that no *leaf* needs a ghost update besides the break edits |
| R6 | The footprint numbers (68% table-disjoint, 316 real cells, 50 content overrides) are syntactic approximations | after the copier loads, try `rfl` or `simp only [defs]` on `view (e w) = view w` for every predicted-frame cell (921), and count failures |
| R7 | The load-time gain is extrapolated from a 47-lemma slice | stage 2 measures it on 11 bundles |
| R8 | (D)'s "no global in-transition invariant" claim rests on reading `g8`, `gl`, `g5`, `g10`, `hmk`, `h3` | check the remaining bundles' docstrings for a break that Rule R repairs (none seen) |

---

## 5a. Stage 1: what landed, and what it showed

**What landed.** Three pieces, all front ends that emit the copier calls of before:

- `spindel.v2.pres.frames`: one footprint lemma per primitive edit, `writes-<edit>` (the edited world
  is the input world with only the written fields replaced; 39 lemmas, `rfl` except the `match`-defined
  edge edits and the checked insert, which go by cases), and `defview`, which states a part's view as
  `<rest>-frame-<field>` for every field the part does not read (`rfl`). `frame-term` composes the two
  into the proof of a frame cell.
- `defpart` in `inv.copier`: a part declares `:reads` and the cells that need an argument; every other
  primitive's cell is generated (`prim!` with the generated frame proof). Converted: `gl`, `g1`, `g8`
  (with the fixed comment block of section 4.4: the part, view, exempt form, cells, deferred within a
  step, companions) and 24 more parts whose cells were a plain list of `nil` frames (`g9`, `g7`, `mdb`,
  `esb`, `aha`, `svb`, `gy`, `g10`, `gw`, `g5`, `gso`, `gd`, `vq`, `hmk`, `ar`, `ekb`, `h3`, `gcy`,
  `mb`, `gos`, `gc`, `gk`, `grel`, `gst`).
- `spindel.v2.pres.exempt`: `defexempt` records a part's exempt form (the ids it holds, its empty
  instance at commit) and aliases the lemmas that open and close deferred violations under uniform
  names `<part>-exempt-<role>[-<site>]`. With aliases: `gl`, `g8`, `grx`; recorded without aliases:
  `g5`, `g10`, `hmk`, `h3` (their lemmas do not fall into break/repair one to one; see below).

**Frames, measured.** The views were measured in the kernel, not read off the source (risk R6): for
each of the 51 bundles' rest predicates and each of the 15 World fields, `rest (set-f w v) = rest w` was
tried by `rfl`; a field where it fails is read. Against those views:

- every one of the 876 `nil` cells left in the source at that point is a table-level frame, except
  Rule R's filter for `grel`, which became one too once the filter got its footprint (it does not write
  `cleanup`, `pins`, `pending-act`, `released`, `next-id`). The static estimate of 42 "overlapping but a
  frame" cells (E3) was an artifact of over-approximated reads; at table level there are none.
- 53 cells were proved by hand although they are table-level frames: the edge edits `mark-edge`,
  `unmark-edge`, `remove-edge` in 16 parts and `insert-edge-checked` in two. They are frames in
  substance; `rfl` does not see it only because the edits are defined by `match` / `if`, which the
  footprint lemmas handle once.
- After the conversion the source has 424 `nil` cells instead of 969 (545 fewer, all in the converted
  parts) and 25 hand-written edge-frame lemmas instead of 61; the 36 that went are restated, with
  their names and statements, by `frame-theorem!` from the view. `override!` (337) and `patch!` (94)
  are untouched: stage 1 does not change what the composites do.
- Eager generation can add a cell the copy never uses: one here, `g1-run-ins-fresh` (`g1` has no run
  insert in its closure). For the 24 parts not converted, mostly helper bundles with small closures, it
  would add up to 10 unused cells each (`gr0`, `nz`), which is why they keep their lists.

**Exemption forms, checked (R8, and a correction to option D).** Of the bundle parameters, two kinds
must be told apart:

- *Exemption sets*, weaker as they grow and empty at commit: `g8 x8s` (run ids), `glx k` (one task
  id, a predicate beside the bundle), `grx xr` (run ids), `g5 xd` (debtor ids), `g10 gxz gkz`
  (computation ids, run ids), `hmk hxm` (debtor ids), `h3 xm` (computation, debtor and member ids).
- *Focus parameters*, stronger as they grow, which carry a fact about given ids through one composite:
  `gnf nids` (no marker in nids), `mdk mkm` (marked edges on these debtors are dep edges), `gy y`
  (computation y is no tombstone; `inv` uses `gy 0`), `ch cx`, `ka`, `na`, and the other helper bundles.
  Section 3 (D) listed `gnf` and `mdk` among the exemption forms; they are not.

No exemption opened in a raw transition is left for Rule R, as option D assumed. The reason is
structural: a copied lemma keeps the bundle parameters fixed from its input world to its output world,
so `raw-<part>` and each Rule R round lemma start and end at the same exemption set (the empty one in
`inv`); a deferred violation cannot outlive the composite that opened it. Inside, the sets change only
in overrides (the breaks and repairs) and loop invariants (`g8-cascade`'s ghost).
`g5` and `h3` do not have one break and one repair lemma per site: `g5` discharges a whole finality
site through an escape predicate (`jw`, `jw-fire-edge`, `jw-fin-fold`), `h3` removes exemptions with
`h3-undo-*` lemmas; their uniform names wait for stage 3, where these become composite-level fields.

**Regression.** See the stage-1 PR: statement fingerprints of every theorem before and after, theorem
counts, load time, the full test suite.

## 5b. Stage 2: the generic tree, and the rule for stage 3

**What landed** (`spindel.v2.pres.tree`). The composite lemmas the converted parts need are checked once,
over an abstract rest part `Q`:

- `Leaf Q`: one field per primitive edit the tree reaches, in the bare shape (Base and `Q` of the input
  world give `Q` of the edited world), chunked into structures of at most 20 fields (R1, below).
- `Over Q P`: one field per composite of the tree that some bundle overrides (R3; `over-targets`,
  checked against the copier's `override!` calls by `pres/tree_test.clj`). `over-default` fills every
  field with the generic proof (the `gqd-` copy), proved once from the leaves.
- `gq` (parameters `Q`, `P : Leaf Q`, `O : Over Q P`): the tree, copied once; its leaves call `Leaf`, its
  override points call `Over`.
- `restate!`: a part builds its `Leaf` instance from its primitive cells and restates every lemma the
  copier used to generate for it, under the old name and statement, as an application of the `gq-`
  lemma with `over-default`.

Converted: `edb`, `gnf`, `kc`, `kx`, `mdk`, `neb`. Not converted, and why:

- `vr`, `na`, `gox`: their primitive cells take a bundle-specific side condition at the call site (the
  copier's extra args: a key-preserving row function for `comp-upd`, `act-upd`, `run-upd`), so a bare
  leaf `forall f, ...` cannot be instantiated from their cells. This is obstacle 1 of
  `generic-preservation.md`: such leaves are per call site (primitive applied to the row function used
  there). It is the same kind of extension as the call-site context below.
- `ch`: it lives in `inv.copier`, which the tree namespace loads after; moving it is a separate change.
- `gx`: not override-free; it shares four overrides with `ga` (`inv-fill-slot`, `inv-fire-dep`,
  `inv-fire-wait-act`, `inv-resume`).

**R1, measured** (synthetic leaves of the full A+ shape: membership, an alive row, a guard, Base, `C`,
`Q`; one JVM at 1 GB):

| fields | Type structure: create / instance / 200 projections | Prop conjunction: def / instance / 200 projections |
|---|---|---|
| 25 | 0.59 / 0.20 / 1.6 s | 0.11 / 0.16 / 4.4 s |
| 50 | 1.9 / 0.41 / 1.2 s | 0.31 / 0.58 / 11.1 s |
| 100 | 8.9 / 1.5 / 1.3 s | 1.0 / 2.2 / 35.9 s |
| 150 | out of heap after 51 s | 5.3 / 10.7 / 146 s |
| 150 as 6 structures of 25 + an outer one | 5.5 / 5.8 / 1.6 s | |

A flat structure grows roughly quadratically; a projection out of a nested conjunction costs in
proportion to its depth. Hence Type-valued structures in chunks.

**The stage-3 extension rule.** Leaves are written in the bare shape now. Call-site context is added
without changing a signature: a contextual leaf is a *new* field whose default is derived from the bare
one (`fun ctx => bare-field`, ignoring the context), and the tree calls the contextual field at the sites
that have the context. Existing instances keep working unchanged; a part that needs the context
overrides the default. The same rule adds the companion context `C` (stage 4) and per-call-site leaves
for bundle-specific side conditions (`vr`, `na`, `gox` above).

**R2 moves to stage 3**: how the context of a call site is obtained (hand-written generic composites, or
an ansatz hook that reports the local context at a term position). Its input: of the 46 primitive call
sites in the composites of the 11 candidate parts, 24 have path facts in scope (a hypothesis introduced
by `cases`, `case` or `have` above the call; counted from the source text):

| composite | primitive | facts in scope |
|---|---|---|
| `inv-await-step` | `inv-insert-edge-checked` | `hd`, `[false` |
| `inv-await-step` | `inv-comp-upd` | `hd`, `[true` |
| `inv-await-step` | `inv-insert-edge-checked` | `hd`, `[true` |
| `inv-await-step` | `inv-comp-upd` | `hd`, `[true` |
| `inv-await-step` | `inv-edge-upd` | `hd`, `[true` |
| `inv-clear-comp-run` | `inv-comp-upd` | `hc`, `hr` |
| `inv-clear-task-run` | `inv-task-upd` | `hc`, `hr` |
| `inv-consume-entry` | `inv-edge-upd` | `hf`, `hr` |
| `inv-consume-entry` | `inv-remove-edge` | `hf`, `hr` |
| `inv-debtor-side` | `inv-task-upd` | `hc` |
| `inv-demand-reactive` | `inv-comp-upd` | `hc`, `hi`, `hv` |
| `inv-demote` | `inv-drop-edges` | `hf`, `hi` |
| `inv-demote-epoch` | `inv-comp-upd` | `b` |
| `inv-demote-finish` | `inv-comp-del-unref` | `hf`, `hk` |
| `inv-demote-finish` | `inv-drop-edges` | `hf`, `hk` |
| `inv-demote-finish` | `inv-comp-upd` | `hf`, `hk` |
| `inv-dep-consumed` | `inv-edge-upd` | `hf` |
| `inv-dep-consumed` | `inv-remove-edge` | `hf` |
| `inv-fill-slot` | `inv-act-upd` | `hm` |
| `inv-fire-observe` | `inv-edge-upd` | `hs` |
| `inv-fire-wait` | `inv-remove-edge` | `hc` |
| `inv-insert-edge-checked` | `insert-edge-fresh-inv-sample` | `hk` |
| `inv-raise-loop` | `inv-comp-upd` | `[cons`, `u`, `f`, `ih` |
| `inv-react-add` | `inv-insert-edge-checked` | `hk` |

**Measurements.** The tree has 16 leaves (in 1 chunk), 39 `Over` fields (2 chunks) and 59 composite lemmas
(`gqd-` defaults and `gq-`), elaborated once in 2.6 s. The six parts' 228 generated copies (`edb` 22,
`gnf` 58, `kc` 47, `kx` 47, `mdk` 11, `neb` 43) are now restatements, proved by applying the generic
lemmas; three cells were added where a part's copy never needed them (`edb-close-scope-id`,
`edb-comp-del-unref`, `mdk-close-scope-id`). Load time, measured back to back: the namespaces this stage
touches (the tree, `inv.idle`, `inv.base`, `inv.i1-runs`, `inv.members.dispatch`,
`completion.drained`) took 57.9 s before and 59.9 s after, tree included; the whole model went from 441 s
to 549 s, but the unchanged namespaces account for 106 s of that (host load). For these helper parts the
tree does not pay yet: their copies were small, and the one-time cost of the tree is about what they
saved. The gain the note estimates comes with the chain parts, whose copies are large (stage 3).
Statements: all 16,496 theorems of stage 1 have identical fingerprints; 172 are new (the tree, the six
`Leaf` instances, the three cells).

## 5c. Stage 3 on `gl`: the generic tree by open recursion, and how a part gets its facts

**Result.** `gl` goes through the generic tree. Its 9 overrides and 6 patches are gone from the copier;
what is left is a table of 3 site entries and 6 entries for its own composite proofs, and every lemma the
copier used to generate for it (176) is restated under its old name and statement. Getting there needed a
change to stage 2's tree, not only new fields: the two total structures `Leaf` and `Over` cannot carry a
part that breaks its invariant inside a transition. The tree is now written by *open recursion*: each
composite's generic lemma takes its callees' statements as hypotheses. The facts the base proof drops are
declared once in the tree, per callee (N), and passed at the call sites by the tree's own proofs (H).
Generating them from the elaborator (T) was measured and is not worth it.

### What stage 2's tree could not do

Stage 2's `Leaf Q` had one field per primitive in the bare shape, among them `inv-run-upd`,
`inv-task-upd` and `inv-run-del`. A Lean structure is total, so a part must prove every field. `gl`
cannot: a run update in general may kill a run (T14, T12), and the copier fed `gl` a key-preservation
proof at every call site (its extra argument) that the bare field does not have. Per-call-site fields
(the §5b rule) fix the shape but not the break: at T14's `run-upd … run-cancel-row` the part is false
until the same composite repairs it, so no statement of that leaf, with any context, holds for `gl`.
Such a leaf may only be reached through a composite the part overrides.

`Over Q P` did not allow that either. `over-default` filled every field with the stage-2 default copy
(`gqd-`), which re-proves each override point from the leaves. `inv-job-apply`, `inv-cascade` and
`inv-run-cascade` are `Over` fields whose default reaches `inv-cancel-run-local` through `gqd-`, so a
part that overrides `cancel-run-local` but takes the default of `job-apply` still needs the break leaf.
The default of an outer override point has to call the part's proof of the inner one: open recursion.

### The tree now (`spindel.v2.pres.tree`)

```
pres-x : ∀ Q, x's binders, (S c over Q, for every lemma c that x's proof calls) → S x over Q
```

`S c over Q` is c's statement with `inv-sample` replaced by `gp Q` (Base and Q). The proof of `pres-x`
is x's base proof, with each callee replaced by its hypothesis; 189 of them, generated from the source
text of `edits`/`step`/`rule`/`engine`. A part restates each lemma the copier generated for it as one
application, `pres-x` applied to the part's own lemma for each callee (`restate!`), bottom up. A part's
own proof of a composite replaces the generic one at that node (`part!` `:over`). There is no `Leaf` or
`Over` structure, no default copy, and no list of override points: any node can be overridden, and a part
proves exactly the callees of the nodes it takes from the tree.

Two kinds of callee need more than the base lemma's statement:

- **Sites.** An update primitive is one hypothesis per row function: `run-upd` at `run-wake` and at
  `run-tick` are different hypotheses, with f fixed. A part proves each site it reaches, by default from
  its cell and the bundle's extra argument (for `gl`, `rfl` on the run key at every site but three).
  `t-finally-enter` names its row function only through unification; its tree source states it,
  generalized over the finalizer it pushes (`site-gen`).
- **Contexts.** Facts the base proof checks on the path and drops. They are declared per callee, as
  premises a part may use there (`contexts`); the tree's proofs pass them at the call sites (`passes`:
  an argument inserted at a call; `sources`: a tree proof that differs from the base proof, for a node
  that must take a context to pass it on). A part that does not need a context drops it with
  `ctx-<x>`, proved once. That is the §5b default rule, as a hypothesis type instead of a field.

`gl` needed contexts only on composites, never on a primitive leaf: what its leaves need is a fact about
the row function (a site), and what its composites need is a fact from the path.

### `gl` before and after

| | before (copier) | after (tree) |
|---|---|---|
| cells | `defpart GL` (view, 10 cells, frames) | unchanged |
| run updates | extra argument `rfl`; `up-patch` on `park-if`, `take-park`; patch of `resume` | 3 site entries (`run-wake`, `run-park-row`, `run-tick-park`); every other site from the extra argument |
| own proofs | overrides of `cancel-run-local`, `complete-raw`, `retire-local`, `spawn-rows` (4 one-line wrappers of the `-o` lemmas) | `:over` entries naming the `-o` lemmas; the old names become aliases |
| new runs | overrides of `start-raw`, `new-run-of` | two hand lemmas (unchanged statements) as `:over` entries |
| plumbing | overrides of `t12-inv`, `inv-retire-one`, `inv-dispatch-raw`; patches of `inv-job-apply`, `raw0-inv`, `t5-inv`, `t11-inv` | none in `gl`; in the tree: 7 contexts, 6 passes, 2 sources, shared by every part |
| generated | 176 copies (`lcopy!`, 15 roots) | 169 restatements, 4 aliases, 2 hand lemmas, 1 restated primitive |

The table (`spindel.v2.inv.i10-task`):

```clojure
(tree/part! GL
  :sites '{[inv-run-upd run-wake]      (gl-run-upd w x run-wake hf run-wake-rkey h0)  ; resume: key kept, by lemma
           [inv-run-upd run-park-row]  (gl-run-upd-up …)                                ; park: alive goes up
           [inv-run-upd run-tick-park] (gl-run-upd-up …)}                               ; take, parked: same
  :over '{inv-cancel-run-local gl-cancel-run-local-o   ; T14 local: break glx-kill, repair in debtor-side
          inv-complete-raw     gl-complete-raw-o       ; T12: break glx-kill, repair at complete-task
          inv-retire-local     gl-retire-local-o       ; T13: retire-rest
          inv-spawn-rows       gl-spawn-rows-o         ; T4: a task and its alive run, together
          inv-start-raw        gl-start-raw            ; T5: a new run of an existing computation
          inv-new-run-of       gl-new-run-of})         ; T11: same
```

The tree's side, every line with its reason (`contexts`, `passes`):

| callee | context | passed at |
|---|---|---|
| `cancel-run-local` | `r ∈ runs` | `job-apply`: `run-find` found it |
| `retire-local` | `r ∈ runs`, `run-alive r = false` | `job-apply`: found; `retirable` means done |
| `complete-raw` | `r ∈ runs`, result tag not none | `t12` (`tok-facts`, the tag guard), `retire-one` (found; an err result) |
| `start-raw`, `new-run-of` | `comp-has w c.id` | `t5` (`comp-find` found it), `dispatch-raw` |
| `t12-inv` (own) | `res-tag-ok tag` | `raw0`: the refusal guard |
| `dispatch-raw` (own) | `comp-has w c.id` | `t11`; carried through `cancel-pred`, `cut-suffix`, `consume-entry` by `ch` |

Against the success criteria: 9 overrides and 6 patches became 3 site entries and 6 own-proof entries.
Of the six, four are content (two deferred violations, T13's retire, T4's insert); `start-raw` and
`new-run-of` are two three-line adapters of one lemma, `gl-comp-run-o`. Merging them into one entry needs
a context on `add-run-scope` and a new lemma; not done. Every context premise is one line with a reason.
No statement changed.

`ch` does not disappear (§4.5 predicted it would). Its fact, `comp-has w c.id`, is not a table-level frame
of `cancel-pred` and `cut-suffix`: both write the comps table (`comp-upd`, the pending resync of
`drop-edges`). It survives because they keep the computation ids, a column-level frame whose proof is
`ch`'s copy. `ch` stays a copier bundle; the tree's `dispatch-raw` uses its lemmas. Converting `ch` to
the tree would put it between the generic lemmas of `cut-suffix` and of `dispatch-raw`; small, not done.

### N, H, T compared (on `gl`'s and `g9`'s call sites and the 24 of §5b)

- **N (statements from the overrides).** The difference between an override's statement and its base
  lemma's, computed for every override of `gl` and `g9`: 7 contexts for `gl`, 3 for `g9`, each one or two
  premises. They are shared: `g9`'s context at `cancel-run-local` is `gl`'s (`r ∈ runs`). No context
  had to be widened when it was used.
- **H (the tree passes them).** 6 call-site insertions and 2 tree proofs (`t12`, `dispatch-raw`, whose
  own statements take the context), plus one source for `t-finally-enter`'s row function. Written once,
  in the tree, for every part; before, `gl` and `g9` each carried the same `job-apply` patch.
- **T (from the elaborator).** Replacing the call by `?_` and printing the state (`refine'`,
  `trace_state`; no ansatz change needed) gives the local context at a call site. Over 39 sites: 91 path
  hypotheses (2.3 per site, at most 10), 86 characters per site. For `gl`'s 8 context sites, 0 contain the
  needed fact as stated; 6 contain a raw fact it follows from by one lemma (`run-find w rid = some r` for
  `r ∈ runs`, plus a variable `rid` the callee does not have); 2 lack it altogether, because it was
  established in a caller one level up (`t12`'s tag guard comes from `raw0`; `dispatch-raw`'s computation
  from `t11`, carried through three edits). The hypotheses carry the base proof's local names (`hf`,
  `ha`, `hc`) and print projections as field indices (`c.11`, `w.14`), so a generated statement changes
  when the base proof is renamed or restructured. T is a development aid (print the context at a call
  site, to choose a context), not a generator.

### `g9`: are per-primitive leaves too coarse?

Yes, and per call site is finer than needed. `g9`'s two resource lemmas (`g9-res-upd-q` at
`res-cancel-row` and at `res-set-phase rp-fired`) are the only two `resource-upd` sites of the step, with
different row functions; one hypothesis per (primitive, row function) separates them. For `gl` and `g9`
no (primitive, row function) pair needs different proofs at different sites (`run-tick` has 13 sites,
all `rfl` on both keys). `g9` on the tree would be: 2 site
entries, own proofs at `cancel-run-local` (`g9-cancel-mid`, using the shared context), `ack-raw` and
`arm-park`; new contexts `arm-park` (`r ∈ runs`, not unwinding) and `t17` (own: not in a cleanup slice),
one pass in `raw0`. Its 4 overrides and 4 patches go; not converted here.

### The generic tree as real source (prototype: `notes/real-source-proto.clj`)

`src-cancel-run-local` is T14's local part written by hand over Q, its five callees as named hypotheses
(`kill`, `acts`, `res`, `cleanup`, `debtor`); its proof is the base proof's five lines with those names.
`inv-cancel-run-local-derived` restates the base lemma (same statement) from it with Q the trivial part.
Findings:

- The derivation is not free. `gp triv w` is `inv-sample w && true`, which is not `inv-sample w` by
  definition (`Bool.and` is stuck on its first argument), so each callee's base lemma is wrapped
  (`triv-up`/`triv-down`): 5 lambdas, 12 lines for a 5-line lemma. Putting Q first in `gp` would make the
  trivial part definitional, but then every part's restatement (`gl w` is `inv-sample w && gl-rest w`)
  needs the wrapping instead.
- For someone editing `rule.clj`: the transition's proof moves to the generic lemma, written with
  hypothesis names instead of lemma names, and its hypothesis list must name every callee with its
  statement (the 5-line proof gets a 6-line signature). Adding a callee means adding a hypothesis, and a
  wrapper in the derived base lemma. Today the editor writes the base proof only, and the tree follows.
- Load (one JVM, warm): the generated `pres-cancel-run-local` checks in 13 ms, the hand-written one in
  10 ms; the base lemma in 6 ms, the derived one in 7 ms. Across the tree, real source would save the
  generation of the 189 generic lemmas (7.5 s, the whole cost of the tree namespace) and add a signature
  per composite to the source.

Recommendation: keep the base proof as the source and the generic lemmas generated, as now. The generated
`pres-` lemmas are mechanical (callee to hypothesis), checked once, and printable (`tree/pres-form`), and
everything a reader needs to decide is in the tree's three declared tables. Real source pays only if the
base proof itself is to be read as the generic one, which no reader asked for.

### Gate

- **Statements** (name-independent fingerprints of every theorem, stage 2 against this stage): 16,496
  identical, 0 changed. 172 removed: the stage-2 tree's internals (`gq-*`, `gqd-*` and their equation
  lemmas, the `p-<part>` Leaf instances, `over-default`) and three cells stage 2 added where a part's copy
  never used them (`edb-close-scope-id`, `edb-comp-del-unref`, `mdk-close-scope-id`); nothing references
  any of them. 197 new: 189 `pres-*`, 5 `ctx-*`, `gp-sample`, `gp-parts`, `gp`'s equation lemma.
  `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-p3m`, `mv-refinement`
  unchanged; `inv` is a definition, its source untouched.
- **Load**, two runs back to back (one JVM each, 1 GB): the namespaces this stage touches took 63.4 s
  before and 65.7 s after: `inv.copier` 15.4 → 11.4 s (gl's copies gone), `pres.tree` 1.8 → 10.3 s (it
  now covers the whole step: 189 generic lemmas instead of 59 composites twice), `inv.i10-task` 0.6 s,
  the five stage-2 parts' namespaces 46.0 → 43.5 s. The untouched namespaces went 315.9 → 295.6 s (host
  load); the whole model 379 → 361 s. The tree is a one-time cost of about 8.5 s; `gl` alone saved 4 s
  of copies, so it pays once two or three more chain parts move (their copies are larger).
- **Suite**: `clojure -M:test`, 288 tests, 208,300 assertions, 0 failures, 0 errors (the oracle on samples
  1–60 included; stage 2: 286 tests, the tree test now has three).

### Revised plan for the rest of stage 3

The tree by open recursion makes stage 3 a per-part table plus tree lines; stage 4 (companions) becomes
the same mechanism: a companion is a context, carried through intermediate worlds by the companion's own
restated lemmas, as `ch` carries `comp-has` here.

| part | what it needs | estimate |
|---|---|---|
| `g9` | 2 sites, 3 own proofs, 2 contexts, 1 pass (above) | ½ day |
| `g8` | contexts at the insert composites (owner open: `cur-closed`, `root-ok-if`, `scope-open-at`); revival (9 overrides) needs a context *on a site* (`run-upd` of a run that is a live row), which the tree does not have yet: a site context, keyed by (primitive, row function), about a day; `ga` (15 overrides, `g8-add-ga`) as a companion context on the cascade, carried by `ga`'s restated lemmas | 4–6 days |
| `hmk` | 13 "not a computation id" overrides become contexts at the source, activation and link composites; companions `gd`, `g7`, `gy`, `g10r`, `v14` as contexts | 3–5 days |
| `g7`, `gd` | companions (`ga`; `g7`, `g10r`) as contexts; `gd`'s `cmono` frames as sites | 2–3 days each |

About 2½–3½ weeks with stage 4 folded in; the main risk is now carrying companions through the cascade
(R4), not the shape of the leaves (R1, R2 are settled: no structures, and contexts are declared, not
generated). Revised in §5d: `g9` as estimated; `g8` needs contexts declared per part first.

### What the earlier sections got wrong

- §4.2, §5b: `Leaf` and `Over` as total structures, with `Over.default` from the leaves, cannot carry a
  part that breaks its invariant inside a composite; the tree is open recursion (above). R1's structure
  sizes no longer matter.
- §4.5: `ch` does not disappear (a column-level frame, not a table-level one). Of `gl`'s overrides, the
  plumbing ones were `t12`, `retire-one` and `dispatch-raw` (3); four more were one-line wrappers of
  content lemmas; `start-raw` stays content like `new-run-of`. `gl`'s "7 leaf entries" are 3 sites:
  `bump` is a cell, `run-upd/kill` and `task-upd/result` are inside the overridden composites,
  `filter-world` is in `gl`'s own Rule R proof, which the tree does not cover.
- §3 (A): `g9` needs fields per (primitive, row function), not per call site.
- §2.5, §3 (A+): the path facts `gl` needs sit on composites, not on primitive leaves; a primitive leaf
  needs facts about its row function. "Contextual leaves" are contextual callees, of either kind.
- §5b's 24 sites: the "facts in scope" column counted case-split tokens; the elaborator shows 0–10
  hypotheses per site (above).

## 5d. Stage 3, continued: `g9` on the tree, and why `g8` needs per-part contexts

**Result.** `g9` goes through the tree (`spindel.v2.inv.i9-res`): its 4 overrides, 4 patches and the
`lcopy!` of `step-inv` are gone; its table has 2 site entries and 3 own-proof entries, and all 187
names the copier generated for it keep their statements (185 restated or aliased, 2 hand lemmas).
`g8` was not converted: the tree's shared contexts cannot carry it (below), and the change it needs is a
redesign of how contexts are declared, which this stage was told not to start.

### `g9` before and after

| | before (copier) | after (tree) |
|---|---|---|
| resource updates | patches of `inv-res-cancel` and `t18-inv` (`g9-res-upd-q` at the call) | 2 site entries: `resource-upd` at `res-cancel-row` and at `res-set-phase rp-fired` |
| own proofs | overrides of `cancel-run-local`, `ack-raw`, `arm-park` | `:over` entries: `g9-cancel-run-local`, `g9-ack-raw-o` (the old name an alias), `g9-arm-park` |
| plumbing | override of `t17-inv`; patches of `inv-job-apply`, `raw0-inv` | none in `g9`; in the tree: 1 context (`arm-park`), 1 own context (`t17`: raw0's guard `fin-shut`), 2 passes |
| generated | 187 copies (`lcopy!` of `inv-cancel-debtor`, `step-inv`) | 184 restatements, 1 alias, 2 hand lemmas |

The estimate of §5c held: 2 sites, 3 own proofs, 2 contexts, 1 pass (2 counting the pass into `arm-park`).
`g9-cancel-run-local` and `g9-arm-park` are three-line adapters: the content is `g9-cancel-mid` and
`g9-arm-o`, followed by the generic debtor side and the generic park.

### The tree extension: own contexts are opt-in (superseded by §5e)

§5c's `:own?` contexts (`t12`, `dispatch-raw`) were global: every part restated those nodes with the
context premise. `gl` needed that; `g9` did not, and its `t12-g9` and `g9-dispatch-raw` would have
changed statement. The same held for the new `t17` context: `gl`'s `t17-gl` would have gained `g9`'s
premise. So:

- An own context names its facts (`:own [hc]`): the tree takes x's base proof, adds the premises to
  its statement and the names to its first `intros`, and the passes do the rest. `t12`'s hand-written
  source is gone this way (its pass uses a new one-line lemma `tag-ok-res`); `dispatch-raw` keeps its
  source (it carries `comp-has` through three edits with `ch`).
- A part takes x's own context only when it needs it: `takes?` is true when one of x's callees takes a
  context in that part (an overridden callee that is not `:bare`, or an own context taken in turn).
  `gl` takes `t12` and `dispatch-raw`, `g9` takes `t17`, neither takes the other's.
- Every other part keeps x's bare statement, proved from `pres-<x>-bare`: x's base proof over Q, every
  callee bare. Callers that pass the context get the part's bare lemma through `ctx-<x>` (dropped), now
  generated for own contexts as well.

Three own nodes give three `pres-<x>-bare` and three more `ctx-` lemmas. Every converted part
(`edb`, `gnf`, `kc`, `kx`, `mdk`, `neb`, `gl`, `g9`) goes through with identical statements.

### `g8`: what the shared contexts cannot carry

`tree/contexts` holds one premise list per callee, in base vocabulary, and every part that overrides the
callee takes all of it. Read against `g8`'s 51 overrides and the bundles still to come (`g7`, `gd`), that
model breaks in two ways:

1. **Parts need different facts at the same callee.** A part's own lemma must take exactly the shared
   list, so the second part to need a different fact changes the first part's lemma:

   | callee | `gl` | `g9` | `g8` | `g7` | `gd` |
   |---|---|---|---|---|---|
   | `complete-raw` | row, tag not none | | no activation of the run, `ga` | | `gd-cce`/`gd-u1` |
   | `arm-park` | | row, not unwinding | row, alive | row, alive | |
   | `dispatch-raw` (own) | `comp-has` | | `ga`, `comp-has` | `awake` | |
   | `t12` (own) | `res-tag-ok` | | `ga` | | |
   | `new-run-of` | `comp-has` | | owner not closed (`tclosed`) | | |

   Taking the union does not help: `gl-complete-raw-o` would have to take `ga`, and the opt-in of own
   contexts is per node, not per fact (`t12`: `gl` takes `res-tag-ok`, `g8` takes `ga`).
2. **The facts are in the part's vocabulary.** `g8`'s owner facts are `sclosed`/`tclosed` over its key
   lists, `gd`'s are `gd-cce`, the await revival needs `g8`'s helper bundle `ka`; all are defined after
   the tree. Restating them in base vocabulary adds a predicate and a bridge lemma per fact, for a
   statement only one part reads.

Both point to the same change: **contexts belong to the part**, not to the callee. A part's table would
declare its contexts (premises in its own vocabulary, at the nodes that need them), its own contexts
(the guard or companion it takes at a transition), and its passes; the tree would generate, for that
part only, the variant `pres-<x>@<part>` of each node on a path between a fact's source and its use,
from the base proof and the part's passes, and use the shared `pres-<x>` everywhere else. That subsumes
the opt-in above (a part declares what it takes) and keeps the shared lemmas bare. It is a narrower
copier: per part, only the nodes on its context paths are regenerated, from a table instead of
hand-written overrides and text patches.

Three smaller extensions `g8` needs in any design:

- **Gated continuations.** raw0 calls `c0-gate w b o h (t1-body-inv ...)`; `g8`'s T1/T-create-link/
  T-append need the gate's fact `root-ok-if b w`, so the continuation becomes `fn [hc0] ...` and
  `c0-gate`'s premise `inv (:world o)` becomes `root-ok-if b w -> inv (:world o)` (today `g8-ga-calls`
  and the `c0-gate-inv` override). A pass that wraps an argument, not one that inserts one.
- **Composite sites.** `serve-or` takes a row function `keep` and its key proof; `g8` needs `x8k (keep s)
  = x8k s` (today an extra argument of the copier at `serve-or`). The tree would dispatch `serve-or`
  per `keep` like an update primitive, and `source-upd`/`scope-upd` as well (the `g8-patch` rows:
  consume, close, detach; `stream-set-tail (:next-id w)` needs `site-gen`).
- **Contexts on sites.** The revival sites (`run-upd` at `run-tick-park` and `run-park-row`) need
  "every row with this id is alive", passed from `take-park`/`park-if` through the edits before them
  (as §5c planned).

R4 (companions) was not reached, and is not what stops `g8`. Carrying `ga` would be an own context on
the 17 nodes between raw and the cascade (`raw`, `raw0g`, `raw0`, `t14`, `t-cancel`, `t16`,
`t-close-scope`, `t15-full`, `t-slice-exit`, `t-release-world`, `t12`, `t11`, `dispatch-raw`,
`cancel-pred`, `complete-raw`, `retire-one`, `t-retire-local`), passed with `ga`'s own lemmas
(`ga-ack-raw` at T15, `ga-run-upd-free` at T-slice-exit, `ga-retire-pre`, `raw0g-ga`, ...): the
mechanism `g9`'s `t17` uses, with `t-retire-local` (both parts through one fold, `nat-fold-pres2`) and
`t-slice-exit` (three steps to the run's freedom) as sources. Not tried: in the shared table it collides
with `gl`'s own contexts at `t12` and `dispatch-raw` (1. above) before the first pass is checked.

The I8 table under per-part contexts would show the model-only guard `cur-closed` (P10) as one row:

```clojure
:own '{t4-inv [hcc (= (cur-closed w st) false)] ...}   ; raw0's body-shut guard; P10: a run's current scope is open
```

### Revised plan

| step | what | estimate |
|---|---|---|
| per-part contexts | contexts, own contexts and passes in `part!`; per-part path variants; `gl`'s and `g9`'s contexts move into their tables (no statement changes); gated continuations, composite sites, `source-upd`/`scope-upd` sites, site contexts | 3–4 days |
| `g8` | about 12 contexts, 20 own-context rows (`ga` 17, `cur-closed`, `root-ok-if`, `ka`), 35 passes, 8 sites, 2–3 own proofs (the cascade with its ghost, `t-detach`), Rule R by hand as now | 3–4 days |
| `hmk` | 13 "not a computation id" facts as contexts (base vocabulary: `comp-has` is false); companions `gd`, `g7`, `gy`, `g10r`, `v14` as own contexts | 3–4 days |
| `g7`, `gd` | 29 and 22 overrides, mostly the same transitions as `g8` (parks, dispatch, await, T12) with their own facts; `gd`'s `cmono` frames as sites | 2 days each |

About 2½–3 weeks, as §5c's total, with the redesign first instead of per-part workarounds.

### Gate (`g9`)

- **Statements** (name-independent fingerprints of every theorem, f87fb4f against this stage): 16,691
  identical, none missing. 2 changed, both internals of the tree: `pres-raw0` (its call of `t17` now
  passes raw0's guard) and `pres-t17` (it takes the guard and passes it to `arm-park`); nothing outside
  the tree's restatements references a `pres-` lemma. 8 new: `pres-t12-bare`, `pres-t17-bare`,
  `pres-dispatch-raw-bare`, `ctx-t12`, `ctx-t17`, `ctx-dispatch-raw`, `ctx-arm-park`, `tag-ok-res`.
  Every old `g9` and `gl` name has its old statement (`t12-g9` and `g9-dispatch-raw` stay bare,
  `t17-g9` keeps `fin-shut`). `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`,
  `step-p3m`, `mv-refinement` unchanged; `inv` is a definition, its source untouched.
- **Load**, two runs back to back (one JVM each, 1 GB): the namespaces this stage touches took 64.7 s
  before and 64.7 s after: `inv.copier` 14.6 → 8.2 s (g9's copies gone), `pres.tree` 13.2 → 14.5 s
  (3 bare lemmas, 4 context defaults), `inv.i9-res` 0.8 s, `inv.i10-task` 0.9 → 1.0 s, `inv.base`
  36.1 → 40.1 s. The untouched namespaces went 392.5 → 572.5 s (host load); the whole model 457 → 637 s.
- **Suite**: `clojure -M:test`, 290 tests, 208,315 assertions, 0 failures, 0 errors (the oracle on
  samples 1–60 included; two new tree tests: own contexts are opt-in, g9 is not copied).

### What the earlier sections got wrong

- §5c: contexts as one shared list per callee. It held for `gl` and `g9` (they share `r ∈ runs` at
  `cancel-run-local`), but not once two parts need different facts at the same callee, or facts in their
  own vocabulary (above). Own contexts as global premises changed other parts' statements.
- §4.6: "the creation overrides become two leaf entries whose path condition carries the guard": the
  guards sit on transitions (own contexts at T1, T4, raw0's `c0-gate`), and reach the insert composites
  through about ten passes; not two entries.
- §5c, R4: the first obstacle for companions is where they are declared, before how they are carried.

## 5e. Stage 3: contexts belong to the part

**Result.** §5d's proposal, implemented: the tree has no shared `contexts` or `passes` tables any more.
A part's table declares the facts it takes from the path and the terms that pass them; the tree
generates the part's own generic lemma `pres-<x>@<part>` for the nodes on those paths, and every other
node uses the shared `pres-<x>`, which is now the base proof over Q with bare callees. `gl` and `g9`
moved their facts into their tables with no statement changing. The opt-in logic of §5d (`takes?`,
`pres-<x>-bare`, the `ctx-<x>` defaults) is gone with the shared table.

### The table

| key | what | `gl` | `g9` |
|---|---|---|---|
| `:ctx` | x or [p F] -> facts the part's own proof (or site entry) takes there | 5 | 2 |
| `:own` | x -> facts a generated node takes from above, named | `t12` (refusal guard), `dispatch-raw` (the computation exists) | `t17` (`fin-shut`) |
| `:pass` | caller -> callee -> the terms passed, over the caller's locals | 6 callers, 7 terms | 3 callers |
| `:src` | x -> the part's proof of x (base vocabulary) | `dispatch-raw` (carries `comp-has` with `ch`) | |
| `:gates` | a gate node whose continuation takes its fact | | |

A reader of `inv.i10-task` or `inv.i9-res` now sees every fact the part takes from the path, with its
reason, in the part's file. The variants are few: `gl` 7 (`job-apply`, `raw0`, `t12`, `retire-one`, `t5`,
`t11`, `dispatch-raw`), `g9` 3 (`job-apply`, `raw0`, `t17`). `raw0`'s variant (the item dispatcher) is
the largest; it is generated per part that passes a guard into a transition.

A missing pass is an error at restatement that names the caller, the callee and the part ("x calls c,
which takes facts in this part: give x a :pass for it").

### Extensions for `g8`

- **Gates** (`tree/gates`): `c0-gate`'s continuation premise becomes `root-ok-if b w -> inv (:world o)`
  for a part that takes the gate (`:gates {c0-gate-inv hc0}`); the gated proof is one line longer than
  the base one, and every call's continuation in that part's variants becomes `(fn [hc0 :- _] ...)`, so
  the part's passes into T1, T-create-link, T-link-realize and T-append can use `hc0`. Checked on a toy
  part in `tree_test` (`raw0`'s gated variant elaborates for any Q).
- **More sites**: `source-upd`, `scope-upd` and `serve-or` (at its `keep`) are dispatched per row
  function, like `run-upd`. A part's default at a composite site is its restated lemma of the composite;
  with a `:sites` entry for every row function (`g8`: `x8k` kept) the composite is not restated at all.
  `link-demand-raw`'s row function, left to unification by the base proof, is named in `tree/sources`.
- **Contexts on sites**: `:ctx {[p F] [facts]}` adds premises to that site's hypothesis in the part's
  variants (its `:sites` entry takes them as `h0..`), and callers pass them like any other.

### Gate (PR A)

- **Statements** (name-independent fingerprints, f87fb4f against this stage): 16,663 identical. 25
  changed, all shared generic lemmas `pres-*` (now bare, or calling the new sites); 5 missing, the
  `ctx-*` defaults of the shared contexts of §5c; 11 new: the part lemmas (`pres-x@gl`: 7, `pres-x@g9`:
  3) and `tag-ok-res`. Nothing outside the tree's restatements references a `pres-` or `ctx-` lemma
  (#314's `pres-*-bare` and the other `ctx-*` go too). Every name of `edb`, `gnf`, `kc`, `kx`, `mdk`,
  `neb`, `gl`, `g9` keeps its statement. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`,
  `l5-safety-total`, `step-p3m`, `mv-refinement` unchanged.
- **Load**, back to back: the namespaces this stage touches took 79.6 s before and 104.0 s after:
  `inv.copier` 12.9 → 6.4 s, `pres.tree` 11.7 → 11.8 s, `inv.i10-task` 0.8 → 7.3 s and `inv.i9-res`
  6.7 s (each part now generates its own `raw0`, the item dispatcher: about 6 s per part that passes a
  guard into a transition), `inv.base` 29.6 → 42.0 s, `inv.idle` 12.3 → 13.6 s, `inv.i1-runs` 10.6 →
  14.1 s. The untouched namespaces went 365 → 467 s (host load); the whole model 445 → 571 s. The
  per-part `raw0` is the cost of moving the guards into the parts.
- **Suite**: `clojure -M:test`, 290 tests, 208,308 assertions, 0 failures, 0 errors (oracle samples 1–60
  included; the tree test checks the part lemmas, a gate on a toy part, and gl/g9).

## 5f. Stage 3: `g8` on the tree

**Result.** `g8` goes through the tree, on per-part contexts (§5e). Its 51 overrides, 3 patches
(`g8-patch` over every source, `g8-add-ga` on raw0 and raw0g) and 7 `lcopy!` calls are gone; `inv.i8`
Part H is its table. All `g8` names keep their statements; one hand lemma that no longer has a caller
(`g8-take-park-o`) and the T11 key lemmas of the old dispatch override are deleted.

| | before (copier) | after (tree) |
|---|---|---|
| overrides / patches / `lcopy!` | 51 / 3 / 7 | 0 / 0 / 0 |
| own proofs (`:over`) | (overrides) | 7: the cascade (break, repair, ghost escape list, exit by P4), `add-run-scope`, `spawn-rows`, `stream-rows` (two inserts with different owners), `start-raw`, `new-run-of` (a computation's run), T13's retire fold (`nat-fold-pres2`, `g8` with `ga`) |
| sites | `g8-patch`, extra arguments | 12: a run dies (T12), is made parked (take, await: with a context), wakes; a task's owner changes (detach: with a context; Rule R; T14's cancel result); a source is consumed, closes, is orphaned; `serve-or` at its two `keep`s |
| `:ctx` / `:own` / `:pass` | (overrides) | 11 / 37 / 62 terms at 45 callers; `:gates` 1 (C0), `:src` 1 (T11's dispatch, `ga` and `ch`) |
| part lemmas `pres-x@g8` | | 47 |

R4 worked as planned: `ga` is an own fact of 17 nodes from raw to the cascades, passed with `ga`'s own
lemmas (`ga-ack-raw`, `ga-run-upd-free`, `ga-retire-pre`, `raw0g-ga`, `ga-zero-handles`, ...); one new
bridge lemma (`slice-exit-free`, the exiting run has no activation). The helper bundle `ka` (the
awaiting run stays alive) is carried the same way through the await, with its copier lemmas.

The P10 guard is one group of rows in the table: raw0's `body-shut` refusal gives `cur-closed w st =
false` to T4 and T1, and T1 carries it to its two creations (four rows, one comment). Every other fact
`g8` takes is a projection of a transition's own guard, by a one-line lemma next to the table
(`root-ok-of-true`, `x8-new-source`, `x8-link-open`, `detach-open`, `await-ok-normal`, `take-park-ok`).

Found on the way, in the tree:

- A bundle's extra argument on an inserted row (`scope-ins-fresh`, whose row must be open) cannot be
  passed at a callee in general (the row is abstract there); `scope-ins-fresh` is now dispatched per
  row, like an update primitive per row function, and T-open-scope's row (whose parent is a local)
  is generalized by `site-gen`. A cell with an extra argument at an undispatched callee is an error.
- An own fact's name must not clash with a name the base proof binds (`ho` in T1-stream's
  `readopt-source` case); the table uses distinct names.

### Readability, measured

**Source lines** (`inv.i8`; code lines, then comment lines, counted per top-level form):

| before (copier) | code | comments | after (tree) | code | comments |
|---|---|---|---|---|---|
| 51 overrides | 541 | 5 | the table (`part!`) | 142 | 14, and 27 code lines with a reason at the end |
| 3 patches (`g8-patch`, `g8-add-ga`, `g8-ga-calls`) and the `serve-or` extra argument | 45 | 1 | own proofs (6; 5 were override bodies, 42 lines) | 40 | 0 |
| 7 `lcopy!` | 7 | 3 | bridge lemmas (7, guard projections) | 26 | 3 |
| helpers only the old overrides used (11) | 85 | 2 | `restate!` (4) | 4 | 5 |
| **total** | **678** | **11** | **total** | **212** | **22** (+27 inline) |

Not counted: `park-overrides` (65 lines at the end of `inv.i8`), the six former park and await
proofs kept as a template for the copier bundles `gd` and `ar`, which rename them (`gd-from-g8`,
`ar-from-g8`); they go when those parts move to the tree.

**Passes and own facts.** The table has 74 pass terms (at 62 caller-callee entries) and 37 own rows.

- 30 of the 74 terms forward a fact the caller declared itself, by its name (`hga` 19 times, `hc0` 5,
  `hcc` 2, `hro`, `ho`, `hk`, `hal`). 25 of them have the same statement at the call (the callee's
  fact, its binders replaced by the call's arguments, is the caller's fact); 5 more need unification
  (the 4 gated `hc0`, where the call leaves the gate's flag to unification) or a definitional step
  (`hal` at `arm-park`, `run-alive` of the armed run).
- 44 carry a real fact: a guard projection (`bool-and-right`, `root-ok-true`, `detach-open`, ...), a
  lookup (`tok-facts`, `find-comp-has`), or a lemma that carries a fact through edits (`ga-ack-raw`,
  `take-park-ok`, the `ka` chain).
- 12 of the 37 own rows only forward (`raw0g`, `raw0`, `t14`, `t-cancel`, `t16`, `t-close-scope`,
  `t11`, `cancel-pred`, `cancel-losers`, `dispatch-raw`, `t-link-realize`, `park-if`); the other 25 use
  the fact in a real term.

**Proposed inference rule (not implemented).** When node x calls c, c takes fact P in the part, and x
has no :pass for c: if every argument of the call is a binder of x, x takes P (its binders renamed to
the call's arguments) as an own fact under a fresh name and passes it; its callers repeat. An
explicit :pass (a real term) stops the propagation. A declared own fact with the same statement is
reused, not added again. This is H made automatic for the forwarding case, with no local context
needed: the facts are premises of x's statement, not hypotheses of its proof. Under it, `g8`'s table
would drop the 25 syntactic forwards (30 with unification at the gate) and the 12 forwarding own rows:
74 → 44–49 pass terms, 37 → 25 own rows, about 142 → 112 code lines. The `ga` chain would read as
four rows: the cascade takes `ga`, `raw` takes it, and T15, T-slice-exit, T-release-world, T12,
complete-raw and retire-one say how it is carried; the 12 nodes between them would be inferred.

**Load.** In PR A (§5e) the touched namespaces went 79.6 → 104.0 s, while the untouched ones went
365 → 467 s (host load, +28%); at that factor the touched ones would have been about 102 s. The part
that is not host load is `raw0`: a part that passes a guard into a transition needs its own variant of
`raw0`, the item dispatcher (49 items, the guard checks and a `simp only` per branch), and that
variant costs about 6 s, once per part (`gl`, `g9`; `g8` adds one, gated). The variants cannot share
the shared `pres-raw0`: their passes use the hypotheses raw0's branches introduce (`hc`, `ht`), which
exist only inside its proof. They could share work if `raw0`'s proof were split per item (one lemma
per branch, `raw0` a dispatch over them): a part's variant would then regenerate only the branches it
passes into (`g9`: one, `gl`: one, `g8`: about 15), and the rest would stay shared. That is a change to
the base proof in `engine.clj`, not done here.

### Gate (`g8`)

- **Statements** (name-independent fingerprints): against PR A (§5e), 16,686 identical; 2 changed, both
  shared generic lemmas (`pres-add-run-scope`, `pres-t-open-scope`: `scope-ins-fresh` is now a site);
  11 missing, the deleted helpers of the old T11 and take overrides (`g8-take-park-o`, `comp-has-find8`,
  `tasks-sdel-fold`, `t8ks-retire-with`, `t8ks-close-with`, `t8ks-job`, `t8ks-cascade`,
  `t8ks-cancel-pred`, `kw8-consume-entry`, `kw8-cut-suffix`, `tclosed-kw8`; nothing references them);
  57 new: 47 `pres-x@g8`, 7 bridge lemmas, `g8-new-run-of-comp`, `g8-cancel-losers` (restated; the old
  raw override never copied it) and `g8-run-cascade` (the copier's name of the overridden cascade, an
  alias). Against f87fb4f every surviving name is identical (16,650; the 27 changed are `pres-*`).
  `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-p3m`,
  `mv-refinement` unchanged.
- **Load**, back to back against PR A: touched namespaces 112.6 → 117.0 s: `inv.i8` 11.1 → 15.1 s (47
  part lemmas, `raw0`'s gated variant among them, instead of 51 overrides and a patched copy),
  `pres.tree` 11.5 → 11.9 s, `inv.comp-facts` 10.3 → 11.1 s, `inv.alive-runs` 8.1 → 8.9 s, the rest
  within ±1 s. Untouched 369 → 344 s (host load); whole model 482 → 461 s.
- **Suite**: `clojure -M:test`, 291 tests, 208,317 assertions, 0 failures, 0 errors (oracle samples 1–60
  included; the tree test also checks that `g8` is not copied and that `ga` reaches the cascades).
- **Found by the gate**: `gd` and `ar` (copier bundles) built six of their overrides by renaming `g8`'s
  (`gd-from-g8`, `ar-from-g8`). Those six forms are kept, unchanged, as `park-overrides` at the end of
  `inv.i8`, and both read them from there.

## 5g. Stage 3: forwarding is inferred

**Result.** The rule proposed in §5f is in the tree (`tree/infer`): when node x calls c, c takes fact P in
the part, x has no :pass for c, and every argument of the call that P mentions is a binder of x, then x
takes P (with the call's arguments) under a fresh name, or reuses its own fact with that statement, and
passes it; x's callers repeat, to a fixpoint. An explicit :pass stops it, and so does a call whose
arguments are not x's binders (an intermediate world): there the part writes the term.

| `g8`'s table | before | after |
|---|---|---|
| own rows | 37 | 27 (10 inferred: `raw0`, `raw0g`, `t14`, `t-cancel`, `t16`, `t-close-scope`, `cancel-pred`, `cancel-losers`, `park-if`, `t-link-realize`) |
| pass entries / terms | 62 / 74 | 42 / 54 |
| code lines of `part!` | 142 | 121 (14 comment lines, 27 inline reasons, unchanged) |

`gl` and `g9` lose no rows: their passes are real terms, and `g9`'s `raw0 -> t17 [hc]` forwards raw0's
local guard (a `cases` hypothesis), not a declared fact, which the rule does not see. The 10 forwards
left in `g8`'s table are the gated `hc0` (the gate's flag is left to unification by raw0's call), `hal`
at `arm-park` (a definitional step), and terms in entries that also carry a real term (a pass entry is
written whole).

The `ga` chain now reads as the facts that matter: the cascade takes `ga` (:ctx), `raw` takes it, and
T15, T-slice-exit, T-release-world, T12, complete-raw, retire-one and T11's dispatch say how it is
carried; the 10 nodes between are inferred.

### Gate (forwarding)

- **Statements** (name-independent fingerprints, against `g8` on the tree, §5f): 16,745 identical, none
  changed, missing or new. The inferred own facts and passes are the declared ones they replace, so
  every part lemma keeps its statement. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`,
  `l5-safety-total`, `step-p3m`, `mv-refinement` unchanged.
- **Load**, back to back: touched namespaces 41.6 → 42.5 s (`pres.tree` 11.3 → 10.4 s, `inv.i8` 17.4 →
  19.6 s, `inv.i10-task` 6.8 → 6.4 s, `inv.i9-res` 6.1 s); the inference runs once per part. Untouched
  472 → 528 s (host load: another gate ran alongside the second measure); whole model 513 → 570 s.
- **Suite**: `clojure -M:test`, 291 tests, 208,319 assertions, 0 failures, 0 errors (the tree test also
  checks that `raw0` forwards `ga` by inference, not by a declared row).

## 5h. Stage 3: raw0 is cut by item

**Result.** `raw0`, the item dispatcher, was the largest part lemma: a part that passed one guard into
one transition (`gl`: T12's refusal guard; `g9`: T17's `fin-shut`; `g8`: the body-shut and C0 guards)
got its own copy of the whole 49-way `cases`. The tree now cuts raw0's base proof by item
(`tree/raw0-split`): one lemma per item, `raw0-<item>-inv`, whose proof is that item's branch (found by
counting the goals its tactics open and close; `rename_i`'s names become the item's fields), each
checked for `inv-sample`; `raw0-inv` is proved by dispatching to them (`tree/sources`). The base proof
in the model is unchanged and still the one a reader reads; the branch lemmas are generated.

A part's pass into a transition is now written at the branch (`raw0-complete-inv {t12-inv ...}`), and
the part gets its own lemma for that branch only:

| part | before | after |
|---|---|---|
| `gl` | `pres-raw0@gl` (49 branches) | `pres-raw0-complete@gl`; the dispatcher is shared |
| `g9` | `pres-raw0@g9` | `pres-raw0-arm@g9`; the dispatcher is shared |
| `g8` | `pres-raw0@g8` | `pres-raw0@g8` (it forwards `ga` to every branch, inferred) and 15 branch lemmas, the ones that call T1, T4, T-create-link, T-append, T-link-realize (the guards) or a cascade (`ga`) |

### Gate (raw0 split)

- **Statements** (name-independent fingerprints, against §5g): 16,741 identical; 2 changed, both
  generic lemmas of the tree (`pres-raw0`, `pres-raw0@g8`: their premises are now the branch lemmas'
  hypotheses, one per item, instead of the transitions'); 2 missing, `pres-raw0@gl` and `pres-raw0@g9`
  (the dispatcher is shared now); 262 new: the 49 `raw0-<item>-inv`, their 49 generic lemmas
  `pres-raw0-<item>`, 17 branch part lemmas (`g8` 15, `gl` 1, `g9` 1), and the copier's 147
  restatements of the branches (`raw0-<item>-g8`, `-gl`, `-g9`). `inv-step`, `reach-inv`,
  `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-p3m`, `mv-refinement` unchanged.
- **Load**, back to back (the first measure ran beside another gate's suite, so compare the parts
  with §5g's second measure as well): `inv.i10-task` 13.5 → 1.2 s (§5g: 6.4 s) and `inv.i9-res` 9.2 →
  0.9 s (§5g: 6.1 s), the cost of a whole dispatcher per part gone; `inv.i8` 16.5 → 11.4 s (§5g:
  19.6 s); `pres.tree` 19.3 → 9.5 s (§5g: 10.4 s; the 49 branch checks take about 1 s). Touched 58.6 →
  22.9 s; untouched 586 → 463 s (host load); whole model 645 → 486 s.
- **Suite**: `clojure -M:test`, 292 tests, 208,375 assertions, 0 failures, 0 errors (the tree test also
  checks the 49 branches, that `gl` and `g9` share the dispatcher, and that a gate-only part gets
  exactly the 6 gated branches). Rebased on #318, with oracle samples 1–62: 295 tests, 208,383 assertions, 0 failures, 0 errors.

## 5i. Stage 3: `g7` and its companions on the tree; parameterised parts

**Result.** `g7` (I7, the idle shape) and its companion bundles `awo awc awr` (the awaiting or
dispatched computation is awake, its run rows its own) and `kdb kc0 kl0 kd0` (demote's cascade kills
every alive run of C) go through the tree. `edb` already did. The copier's overrides, patches and
`lcopy!` calls for these bundles are gone; `inv.idle` Part C is `g7`'s table.

**Parameterised parts.** A bundle with parameters is the part Q := (B p) for fixed p, as stage 1
found for the copier: every restated lemma takes p first and keeps it fixed from input to output
world. `restate!`, the sites and the cells already applied the parameters (`g8`'s `x8s`); `awo` (2)
and `kdb` (3) needed no other change. A parameter that changes inside a composite stays content:
`g7`'s own proofs instantiate `awo` at `(:id c) 0` (T11, reactivation) or `(:of r) (:id r)` (the
await) and carry it with `awo`'s restated lemmas.

**Tree extensions.**
- **A computation edit is a site per row function** (`inv-comp-upd` is dispatched). Its arguments
  are the site's parameters (`site-gen`, named as the binders of the function's id lemma), so a part
  states each function once: `[inv-comp-upd (comp-start-row rid)]`. A row function left to
  unification (`_`) is read off its id lemma, as the copier's `fix-f` did (`tree/fill-rows`).
- **Inserts are sites per row or edge** (`inv-comp-ins-fresh`, `insert-edge-fresh-inv-sample`,
  `inv-insert-edge-checked`). A bundle's extra argument that is rfl only at a concrete row (`g7`'s
  `edge-new-ok` of a wait or observe edge, `:idle r = false` of a new computation) then
  elaborates. Three base proofs leave the inserted edge to unification; `tree/sources` names it
  (take-park, react-add, await-step).
- **`tree/site-keys` and `tree/row-sites`**: a part's sites for a family of row functions, one rule
  each (what the copier's patches did: `g7`'s waking rows, its run ends; `awo`'s no-sleep rows;
  `kdb`'s run ends).

| | before (copier) | after (tree) |
|---|---|---|
| `g7`: overrides / patches / `lcopy!` | 29 / 2 (all sources; raw0) / 3 | 0 / 0 / 0 |
| `awo`, `kdb`: patches / `lcopy!` | 2 / 3 call sites (11 roots) | 0 / 0 |
| `g7`'s own proofs (`:over`) | (overrides) | 21: the inserted dep edge (`edge-new-ok`), T7's tracking edge, T4/T5's new runs, reactivation, T11's dispatch, the T6 await, demote, normalization |
| `g7`'s sites | `g7-patch` | 15 (8 waking computation rows, 4 run ends, resume; schedule/finalize and take: a run enters a slice or parks, with a context) |
| `:ctx` / `:own` / `:pass` | (overrides) | 5 / 2 / 9 callers |
| part lemmas `pres-x@g7` | | 9 |

8 overrides become table rows: schedule and finalize (the found run's rows satisfy `rq`, `enter-q`),
take and arm (the run is a row and alive, as `g8`), T-take, T17, T6 and T11 (the dispatched
computation is awake, `t11-awake`). `raw0`'s patch for T7 is one pass (`raw0-track-inv {t7-inv
[hc]}`). `inv.alive-runs` (`ar`) renamed three of `g7`'s overrides; it now reads those proofs from
`inv.idle`'s source.

### Gate (`g7`)

- **Statements** (name-independent fingerprints, against #320): 16,971 identical; 34 changed, all
  generic lemmas of the tree (27 shared `pres-*` and 7 `pres-*@g8`: computation edits and inserts are
  now sites, so their hypotheses are per row function); none missing; 63 new: 49 `raw0-<item>-g7`
  (the copier restated `raw0` whole), 9 `pres-x@g7`, and 5 lemmas (`g7-run-upd-q`, `rq-of-mem`,
  `enter-q`, `tick-park-q`, `t11-awake`). Every `g7`, `awo`, `kdb`, `edb` name keeps its statement;
  `await-ok-normal` moved from `inv.i8` to `inv.idle` unchanged. `inv-step`, `reach-inv`,
  `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-p3m`, `mv-refinement` unchanged.
- **Load**, back to back: touched namespaces 47.8 → 49.7 s (`pres.tree` 11.4 → 16.8 s: more sites
  per generic lemma; `inv.idle` 13.6 → 14.6 s; `inv.i8` 14.2 → 10.4 s; `inv.alive-runs` 8.7 →
  7.8 s). Untouched 487 → 621 s and whole model 535 → 670 s: host load (another session's JVMs ran
  during the second measure).
- **Suite**: `clojure -M:test`, 296 tests, 208,399 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that `g7`, `awo` and `kdb` have no overrides or patches, the
  generic computation sites, and that T6, T-take, T17, T11, schedule and finalize are table rows).

## 5j. Stage 3: `gd` and `hkw` on the tree

**Result.** `gd` (computation facts: `C.run`, done-epoch) and its companion `hkw hkc hke` (T11's
predecessor keeps the epoch) go through the tree; `inv.comp-facts` Part C is `gd`'s table. The
`gd-add-hyps` patches of `raw0`, `raw0g`, `raw` and `t8-obs` are own facts: `g7` and `g10r` from
the step's input, declared at `raw`, `raw0g`, `raw0` and `t8-obs`, and inferred at `raw0`'s
branches (T6, T22, T8, T12). `gd` no longer reads `inv.i8/park-overrides`: take, arm, T-take, T17
and the await's post take the same facts as in `g8`'s table (the parked run is alive; `ka` through
the wiring); `ar` still reads the template.

| | before (copier) | after (tree) |
|---|---|---|
| `gd`: overrides / patches / `lcopy!` | 23 (+6 from `g8`'s template) / 5 / 3 | 0 / 0 / 0 |
| `hkw`: patches / `lcopy!` | 1 / 3 | 0 / 0 |
| `gd`'s own proofs (`:over`) | (overrides) | 18: new runs (T4, T5, T11), T11's dispatch, T12's completion, reactivation, the await's pre-step and T6's raw step, the host await, T8 |
| `gd`'s sites | `gd-patch` (every computation and run edit) | every computation and run site, by one rule each (monotone in `gd`'s keys; by lemma where the row function changes them); parks with a context |
| `:ctx` / `:own` / `:pass` | (overrides) | 6 / 8 / 6 callers |
| part lemmas `pres-x@gd` | | 16 |

### Gate (`gd`)

- **Statements** (name-independent fingerprints, against #321): 17,068 identical, none changed or
  missing; 65 new: 49 `raw0-<item>-gd` and 16 `pres-x@gd`. Every `gd` and `hkw` name keeps its
  statement. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-p3m`,
  `mv-refinement` unchanged.
- **Load**, back to back, one JVM at a time: touched namespaces 21.6 → 24.0 s (`inv.comp-facts` 8.4 →
  5.6 s; `pres.tree` 7.9 → 10.9 s and `inv.idle` 5.3 → 7.6 s, whose code this PR barely changes:
  host noise); untouched 325 → 345 s; whole model 346 → 369 s.
- **Suite**: `clojure -M:test`, 297 tests, 208,410 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that `gd` and `hkw` have no overrides or patches and that `g7` and
  `g10r` reach `raw0`'s branches).

## 5k. Stage 3: `hmk` and `hsw` on the tree

**Result.** `hmk hxm` (h-mark: a marked edge's debtor is strongly waiting, or exempt) and its
companion `hsw hsc` go through the tree; `inv.marks` Part C is `hmk`'s table, `inv.marks-step`
keeps T2's and T12's own proofs. The `hmk-add-hyps` patches of `raw0`, `raw0g` and `raw` are own
facts (`gd`, `g7`, `ga`, `g10r` from the step's input, inferred at `raw0`'s branches). The five
names `inv.marks-step` redirected by hand (`hmk-write-raw-x`, `hmk-complete-raw-x`,
`hmk-complete-body-x`, `hmk-retire-one`, `hmk-t-retire-local`) are `:over` entries; the copier's
names of four of them are now aliases.

"Not a computation id" (§5b) is a fact in the table, not 15 overrides: the source and link chain
(close, append, link-realize; close-raw, close-source(0), detach-source, realize-link,
link-next-raw, append-raw, deliver-res, fire-task-cancelled), resume and fill-slot take it as an
own fact, the transitions pass it from their source row (`hk-src-not-comp`), and each edit passes
it to the next through the edits that keep the computation rows (`hk-has-*`, or rfl at the edited
world). `finalize-debtor` (its fuel loop is an induction) and `drop-act` take it as a context.

| | before (copier) | after (tree) |
|---|---|---|
| `hmk`: overrides / hand renames / patches / `lcopy!` | 45 / 5 / 4 / 8 call sites (45 roots) | 0 / 0 / 0 / 0 |
| `hsw`: patches / `lcopy!` | 1 / 1 | 0 / 0 |
| `hmk`'s own proofs (`:over`) | (overrides) | 35: the fire chain, finalization's loop, T7's track, revoke-roots, reactivation, detach, T11's strong computation, T3's creation, T2, T12, the retire fold |
| `hmk`'s sites | `hmk-patch` | every computation site, one rule (a waiting row stays waiting; by lemma where the row function changes the keys) |
| `:ctx` / `:own` / `:pass` | (overrides) | 8 / 14 / 13 callers |
| part lemmas `pres-x@hmk` | | 24 |

### Gate (`hmk`)

- **Statements** (name-independent fingerprints, against #322): 17,133 identical, none changed or
  missing; 77 new: 49 `raw0-<item>-hmk`, 24 `pres-x@hmk`, and 4 aliases (`hmk-write-raw`,
  `hmk-complete-raw`, `hmk-complete-body`, `t-retire-local-hmk`: the copier's names of the hand
  lemmas `inv.marks-step` redirected to). Every `hmk` and `hsw` name keeps its statement, the 15
  former overrides among them. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`,
  `l5-safety-total`, `step-p3m`, `mv-refinement` unchanged.
- **Load**, back to back, one JVM at a time: touched namespaces 19.6 → 18.3 s (`inv.marks` 9.5 →
  6.2 s, `inv.marks-step` 10.1 → 12.1 s: it now restates what the copier generated lazily); untouched
  359 → 450 s (host load: other sessions' JVMs); whole model 379 → 468 s.
- **Suite**: `clojure -M:test`, 298 tests, 208,426 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that `hmk` and `hsw` have no overrides or patches and that the
  "not a computation id" chain is generated).

## 5l. Stage 4, group 1: `gy`, `gcy`, `g1` and `gw` on the tree

**Result.** Stage 4 moves the bundles still on the copier to the tree, group by group, and then
deletes the copier. Group 1 is the tombstone part `gy` (`inv.tomb`) and the three scope parts:
`gcy` (`inv.acyclic`), `g1` (`inv.i1-scopes`) and `gw` (`inv.i11`). No tree change was needed.

| | before (copier): overrides / patches / `lcopy!` | after (tree) |
|---|---|---|
| `gy` | 24 (in two form lists, 4 call sites) / 4 (`gy-patch` over every source; `raw`, `raw0g`, `raw0`) / 3 | 24 own proofs; sites by two rules (a run that ends or leaves its slice, a computation edit that clears the flag) and resume; `:ctx` 2, `:own` 4, `:pass` 1 |
| `gcy` | 3 / 2 / 3 | 4 own proofs, `:ctx` 1, `:pass` 2 |
| `g1` | 3 / 2 / 2 | 5 own proofs (two were hand renames), `:ctx` 1, `:pass` 2 |
| `gw` | 3 / 0 / 3 | 3 own proofs |

- **`gy`'s companion `g7`** (the awaiting or tracking run is alive) is an own fact of `raw`, `raw0g`,
  `raw0` and T7's branch, and a context of T7 and T6; T6's branch takes it by inference. T7 also
  takes `raw0`'s guard (not in a cleanup slice), passed at the branch. That replaces the three
  `add-premise` patches.
- **"The parent is a scope"** (`g1`, `gcy`): `add-run-scope` takes it as a context, and T5's start and
  T11's new run pass `rfl` (parent 0). That replaces the `add-hp` patches. `g1`'s hand renames of
  `remove-if-empty` and `add-run-scope` are `:over` entries.
- The part lemmas are few: `gy` 5 (`raw`, `raw0g`, `raw0`, and the branches of T6 and T7), `g1` and
  `gcy` 2 each (`start-raw`, `new-run-of`), `gw` none.

**What the plan got wrong.** It counted `gy` as 4 overrides: `inv.tomb` holds 24 override forms in
two lists and registers them in loops. All 24 are content (dep edges, new runs, parked runs, the
demotion's tombstone, normalization) and stay as own proofs.

### Gate (group 1)

- **Statements** (name-independent fingerprints, against #323): 17,210 identical, none changed or
  missing; 205 new: 196 `raw0-<item>-<part>` (49 per part; the copier restated `raw0` whole) and 9
  part lemmas `pres-x@<part>`. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`,
  `l5-safety-total`, `step-p3m`, `mv-refinement` unchanged.
- **Load**, back to back, one JVM at a time: touched namespaces 26.5 → 16.2 s (`inv.tomb` 7.4 →
  6.3 s, `inv.acyclic` 6.3 → 3.2 s, `inv.i1-scopes` 6.3 → 3.1 s, `inv.i11` 6.5 → 3.6 s); untouched
  394 → 529 s and whole model 421 → 545 s (host load: other sessions' JVMs during the second measure).
- **Suite**: `clojure -M:test`, 299 tests, 208,439 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that the
  four parts have no overrides or patches and where `gy`, `g1` and `gcy` take their facts).

## 5m. Stage 4, group 2: `mdb`, `esb` and the companion `na` on the tree

**Result.** The first half of `inv.base`: `mdb` (marks sit on dep edges), `esb` (edge-separated
ids: every stored reference is an existing non-edge row) and the companion `na nax` (no activation
names run `nax`) go through the tree. The companions `mdk` and `kx` already did (§5b).

| | before (copier): overrides / patches / `lcopy!` | after (tree) |
|---|---|---|
| `mdb` | 2 / 0 / 2 | 2 own proofs (T2's write and `mark-from`, both through `mdk`) |
| `esb` | 12 / 4 (`esb-patch` over every source; `job-apply`, `t5`, `t11`) / 2 | 12 own proofs; sites by two rules (a run row, a cleanup row whose stored refs only shrink); `:ctx` 5, `:pass` 3 |
| `na` | 0 / 0 / 2 | no table: every lemma is generated |

- **`esb`'s three patches that passed a fact** are three `:pass` rows: `job-apply` passes "the run is
  a row" to T14's local part, T5 and T11 pass "the computation exists" to the start and the
  dispatch (the same facts as `gl`, §5c).
- **`esb-patch`** (run and cleanup edits whose stored refs shrink) is two site rules.
- **One of the 12 overrides was never checked**: `esb-cleanup-set-o`, a wrapper that the rename of
  `inv-cleanup-set` to the hand lemma `esb-cleanup-set` made unreachable. The copier evaluates an
  override only when a copy needs it, so the name never existed in the environment. It is deleted;
  the hand lemma is the `:over` entry.

**Tree extension.** `inv-act-upd` and `inv-cleanup-upd` are dispatched per row function, like the
other update primitives. `na`'s (and `aha`'s) extra argument on an activation edit, "the row function
keeps the activation's run", is `rfl` only at a concrete row function (`act-fill`,
`act-set-members`); `esb` proves `cleanup-drop` by its own lemma. The plan listed the cleanup
dispatch under group 7 (`inv-cleanup-upd`'s extra argument in the completion parts); `esb` needs it
already, as a site.

### Gate (group 2)

- **Statements** (name-independent fingerprints, against group 1): 17,409 identical; 6 changed, all
  generic lemmas of the tree (`pres-ack-raw`, `pres-await-post` and its `@g8` and `@gd`,
  `pres-fill-slot` and its `@hmk`: activation and cleanup edits are now sites, so their hypotheses
  are per row function); none missing; 101 new: 98 `raw0-<item>-<part>` (`mdb`, `esb`) and 3 part
  lemmas (`pres-job-apply@esb`, `pres-t5@esb`, `pres-t11@esb`). `inv-step`, `reach-inv`,
  `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-p3m`, `mv-refinement` unchanged.
- **Load**, one JVM at a time. The base measure is group 1's second one, taken under host load, so
  the totals are not comparable: `inv.base` 49.4 → 21.5 s (27.0 s in group 1's first, quiet
  measure), `pres.tree` 7.3 → 11.9 s (9.1 s there); untouched 488 → 411 s, whole model 545 → 444 s.
- **Suite**: `clojure -M:test`, 300 tests, 208,451 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that `mdb`,
  `esb` and `na` have no overrides or patches, the activation and cleanup sites, and where `esb`
  takes its facts).

## 5n. Stage 4, group 3: `aha` and `svb` on the tree

**Result.** The second half of `inv.base`: `aha` (every activation's run exists and is alive) and
`svb` (an observe edge's seen is at most its debtor's version) go through the tree. `inv.base` has
no copier override, patch or `lcopy!` left.

| | before (copier): overrides / patches / `lcopy!` | after (tree) |
|---|---|---|
| `aha` | 12 / 5 (`aha-patch` over every source; `job-apply`, `raw0`, `raw`, `raw0g`) / 2 | 5 own proofs, 3 sites, `:ctx` 4, `:own` 5, `:pass` 7 callers; 12 part lemmas |
| `svb` | 11 / 4 (`svb-patch` over every source; `react-add`, `take-park`, `settle-edge`) / 2 | 9 own proofs, sites by two rules and T8's observe edge, `:ctx` 4, `:pass` 3 callers; 4 part lemmas |

**Overrides that were plumbing are rows now.** 9 of the 23 overrides were the base proof with a
fact passed to one callee, and the tree generates them:

- `aha`: T12 (`ga` gives "the token's run is free"), `retire-one`, T6 and `await-raw`, T-take, T17
  and `arm-park` (the run is an alive row; the same pass terms as in `g8`'s table). `await-raw`
  takes its facts by inference. The companion `ga` is an own fact from `raw` down to T12, where
  the three `add-premise` patches were.
- `svb`: `fire-edge` and `settle-edge` pass "the found edge is the world's" (`kx-of-mem`);
  `fire-dep` takes it by inference.

The 14 own proofs left are content: an activation goes with its run or names an alive one (`aha`);
a new or rewritten edge has seen its debtor's version (`svb`).

**T8's observe edge** (`svb-patch`'s third rule) is a site with a context: the site takes "the new
edge has seen its debtor's version" and T8 passes `obs-sok`. The two patches that named an edge the
base proof leaves to unification (`react-add`, `take-park`) were already `tree/sources`.

**Tree changes.**
- `inv-edge-upd` is dispatched per row function (`svb`'s extra argument, "the row function keeps
  the edge's key", is `rfl` only at a concrete one).
- A bug this exposed: a site's hypothesis is the primitive's statement with the row function
  substituted, and a variable bound inside the primitive's binder types (`forall [e :- EdgeRow]`
  in `inv-edge-upd`'s) captured the same name in the row function (`edge-rearm … (:debtor e)`).
  `site-binders` renames such bound variables apart.
- A row function's lemma in a site rule is written with `_` for its arguments (`hv-lemma`): the
  site's world binder is renamed in the entry, so an argument that mentions the caller's world
  (`stream-set-tail (:next-id w)`) must be left to unification.

### Gate (group 3)

GATE-G3

## 6. Key pieces to read: the whole proof in 14 stops, in reading order (current names)

1. `inv`, `inv-step`, `Reach1`, `reach-inv` (`top.clj`): the headline and its four-line induction.
2. `World` (`state.clj:137`), `Item` (`step.clj:206`): the state (15 fields: 11 row tables, `pins`,
   `pending-act`, `released`, `next-id`) and the 49 items.
3. `world-step`, `raw`, `post`, `finish` (`engine.clj:3439-3447`), `raw0` (`engine.clj:3325`), `rule-r`
   and `rule-r-round` (`rule.clj:1347-1354`): what a step is.
4. `inv-sample`, `inv-parts`, `inv-intro` (`edits.clj:680`, `1214`): the base every part sits on.
5. `step-inv` (`engine.clj:3787`) → `raw0-inv` (`3449`) → `inv-cancel-run-local` (`rule.clj:675`) →
   `inv-run-upd`: the base proof from the item to one primitive.
6. `filter-safe-of-refs` (`inv/copier.clj:3004`), `step-rule-r-safe` (`inv/base.clj:2133`): P3, Rule R's
   filter is safe; the shared premise of every part.
7. `p3b`, `step-p3b` (`inv/base.clj:2112-2146`): how parts are assembled with their companions.
8. `step-gl` (`inv/i10_task.clj`): one part's step theorem: refusal, then raw, then Rule R, with the
   companion `ga`.
9. `gl-rest`/`l10k`, `kw`, `gl-rest-kw` (`inv/copier.clj:77`, `1097`): a part, its view and its frame.
10. `glx`, `glx-kill`, `gl-task-done-x` (`inv/copier.clj`), `gl-cancel-run-local-o` (`inv/i10_task.clj`): a
    violation deferred within a step: its break and its repair.
11. `mk-bundle`, `prim-form`, `copy-subst`, `lcopy!` (`inv/copier.clj:188-293`): how a part reuses the
    base proof today. This is the piece the generic tree replaces.
12. `g8-close-local`, `g8-cascade`, `g8-cascade-done` (`inv/i8.clj:891`, ~1280-1305), `casc-done-ga`
    (`inv/acts.clj:1354`): an exemption as ghost state in a loop, emptied by P4.
13. `step-p3m`, `l5-safety-total` (`inv/members/step.clj:916`, `927`): the end of the chain and what it
    buys (L5's safety half). Read the `inv.members.bundle` docstring for `h3`, the most complex part.
14. `notes/generic-preservation.md` and its prototype: `GPrim`, `gq`, `pgl`, which this layout extends.

In the target layout, stops 5 and 11 become `pres.tree` (read once), stops 7–8 become `inv.parts` and
`step-pres`, and stops 9–10 become sections 2–5 of each part file.

---

### Appendix: measurements

All static, on the sources at e04b1a9: a small s-expression reader (Python) over `formal/src`, expanding
the `doseq` forms around `prim!`/`override!`/`patch!` and the `deftable`/`defsetter` wrappers. The reader
and its outputs were not checked in; each item says what was counted, so it can be redone. Section 5's
R6 lists the kernel-checked version of the frame count.

- **E1, the copier's forms.** 331 `override!` forms over 31 bundles and 134 distinct lemmas (a plain text
  count of `(override! ` gives 337; E1 counted the forms it could attribute to a named bundle). The most overridden: `inv-dispatch-raw` 11,
  `inv-spawn-rows` 10, `inv-cancel-run-local`/`inv-take-park`/`inv-start-raw` 8. Primitive cells
  (`prim!` after `doseq` expansion): 1,357, of which 969 are `nil` and 388 are proofs; 39 distinct
  primitives.
- **E3, reads and writes.** For each bundle, the World fields its rest predicate reads (keywords and
  table accessors, followed through the `a/defn`s it calls); for each primitive, the fields its edit
  writes (setters and table edits, followed the same way). Cells: 875 disjoint and a frame, 46 disjoint
  but given a proof (the edge edits `mark-edge`, `unmark-edge`, `remove-edge` are defined by `match`,
  which `rfl` does not reduce: frames in substance), 42 overlapping but a frame (a column-level key is
  kept), and 316 overlapping with a proof.
- **E4, E5, transitions touching a part.** The 56 item-level transitions (`t*-inv`) and the tables or
  columns each one writes, against each part's reads. Large parts are touched by 39–52 of 56; `g1` and
  `ch` by 17.
- **E6, E8, overrides by added premises.** An override's statement compared with the source lemma's:
  176 add a premise, 153 do not (2 unclassified). Combined with whether the override calls another
  override of the same bundle, this gives the plumbing versus content estimate of section 2.5.
- **E7, the overrides of `g8`, `hmk`, `gl`, `g9`, `gd` and `g7`**, with their added premises, read by
  hand (the grouping of `g8`'s 51 in section 2.5).
- **E10, call sites.** 154 primitive call sites in 103 composites; 58 distinct (update primitive, row
  function) pairs.
