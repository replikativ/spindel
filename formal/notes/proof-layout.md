# Readable preservation proofs for the v2 model: options and the target layout

Status: agreed design, 2026-11-19. It is the plan for making the layer-1 preservation proofs (`inv-step`)
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
8. `step-gl` (`inv/copier.clj:1866`): one part's step theorem: refusal, then raw, then Rule R, with the
   companion `ga`.
9. `gl-rest`/`l10k`, `kw`, `gl-rest-kw` (`inv/copier.clj:77`, `1097`): a part, its view and its frame.
10. `glx`, `glx-kill`, `gl-task-done-x`, `gl-cancel-run-local-o` (`inv/copier.clj` ~1304-1400): a
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
