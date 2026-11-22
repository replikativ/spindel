# Readable preservation proofs for the v2 model: options and the target layout

> **Names (2026-11).** The naming pass replaced the kernel names used throughout this note
> (README.md, "Old kernel names"; the full map is `notes/renames.edn`). The names below were
> substituted mechanically, so they are current. What the sections say ABOUT names is historical
> where it describes the old scheme: the copier's name rule (`inv-<x>` to a prefix, `<x>-inv` to a
> suffix), bundle prefixes that differ from the predicate, `-o` overrides, and counts of lemmas by
> old prefix. Read those passages as a record of the stage they describe. The last section,
> "The naming pass", describes the current scheme.

Status: done through stage 4 (§5l–§5y: every part is on the generic tree and the copier is deleted; totals in §5y). Earlier status line: agreed design, 2026-11-19; stage 3 under way (§5c: `i10-task`; §5d: `i9-res`; §5e: contexts declared per part; §5f: `i8-closed`; §5g: forwarding inferred). It is the plan for making the layer-1 preservation proofs (`inv-step`)
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
part (for example `i8-closed`'s escape list, the runs of the pending cancel jobs) is the set of pending deferred
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

**In words.** `reach-inv` is induction on `WorldReach`. `inv-empty` covers the empty world and `inv-step`
covers a step, so all the work is in `inv-step`.

The step (`engine.clj:3440-3447`) is defined as follows.

- `world-step w it = then-rule-r (raw w it)`.
- `raw = then-cancel-losers ∘ host-guarded-transition`. `transition` does a case split over the 49 constructors of `Item` (T1-T22 plus host
  operations). `then-cancel-losers` cancels the losers of an accepted await.
- `then-rule-r` runs Rule R on the result if the item was accepted, and returns the input world otherwise.
- Rule R is `rule-r-loop` over rounds, where a round is `rule-r-filter ∘ normalize`.

Every transition is glue around **primitive edits**:

- Glue: case splits on a lookup or a guard, sequencing, `nat-fold` over a list, and loops bounded by fuel
  (the cancel cascade, normalization, Rule R's rounds, the fin loop).
- Primitive edits: insert, delete or update one row of one table; mark, unmark, remove or insert an edge;
  bump the allocator; `set-pins`, `set-released` and `set-pending-act`; Rule R's `filter-world`.

There are 39 such primitives, with 154 call sites in the 220 lemmas of the base proof.

`inv` is `Base ∧ P1 ∧ … ∧ Pn`. `Base = well-formed`: exact pending counts, edges reference existing rows of
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
   transition (T14's local part, T12, the cancel cascade) or one round of Rule R (`i10-current-exempt`'s demotions).
4. **Companions:** a part's argument may use other parts of the *input* world. These dependencies form a
   DAG, so the conjunction is inductive even though no single part is inductive on its own. The 13-link
   chain `chain-start ⊂ … ⊂ chain` is one linearization of this DAG.

```
 reach-inv ── induction on WorldReach ──▶ inv-empty , inv-step
                                                   │
             inv w  =  Base w ∧ P1 w ∧ … ∧ Pn w     │  (conjunction; parts use earlier parts: DAG)
                                                   ▼
 world-step w it = finish (raw w it)
        ┌───────────────┴────────────────┐
   raw = post ∘ host-guarded-transition                rule-r = rule-r-loop (rounds)
   transition: case on 49 items            round = rule-r-filter ∘ normalize
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
filter is safe; every part takes it, and it is derived from the `round-facts` parts of `chain-start`). A simplified
picture; the README's table "Companions" lists the exact premises:

```
 acts-parked ──┬──▶ i10-task, i1-runs, i8-closed, act-runs-alive                  (activations: acts-alive for Rule R, P4 for cascades)
      ├──▶ i7-idle ──┬──▶ tombs-dormant ──┐
      │         ├──▶ comp-facts ◀─┼── i10-current ◀── chain-start (all of acts-parked, i12-ranks, i10-task, i9-res, round-facts)
      │         ├──▶ alive-run-latest   │
      │         └─────────┴──▶ i14-ordered ◀── i12-ranks
      └────────────────────────▶ marks-waiting ◀── comp-facts, i7-idle, tombs-dormant, i10-current, i12-ranks, i14-ordered
 chain-to-edge-kinds (everything above, plus alive-run-latest and edge-kinds) ──▶ current-members
 no companions: i12-ranks, i9-res, marks-on-dep, refs-not-edges, root-scope-reserved, i1-scopes, i5-dep-final, i1-detached-closed, edge-kinds, i5-seen
```

---

## 2. Why the current proofs are hard to follow

### 2.1 The mechanism

A bundle is `B w = well-formed w && B-rest w`. Its step theorem comes from the copier (`inv.copier`,
`mk-bundle` ff.). The copier re-elaborates the whole `well-formed` proof of the step: the 220 lemmas of
`edits`/`step`/`rule`/`engine` whose statement mentions `well-formed`. In each copy it replaces
`well-formed` with `B` and renames every callee to its copy. The four commands that control the copy are:

| Command | What it does | Count |
|---|---|---|
| `prim!` | the rest part under one primitive; `nil` means a frame | 410 forms (1,357 cells after `doseq` expansion, 969 of them `nil`) |
| `lcopy!` | copy the closure of a root | 209 |
| `override!` | replace one copied lemma with a hand proof | 331–337 (31 bundles, 134 distinct lemmas) |
| `patch!` | rewrite a source proof (as an s-expression) before copying it | 94 (some are `doseq` over *all* source theorems) |

The result is about 10,000 of the 16,119 kernel theorems, and an estimated 200–300 s of the 8-minute
load.

### 2.2 An override: `i10-task` through T14's local part

The base proof of `cancel-run-local` (`rule.clj:675`) is a five-line composition:

```clojure
(exact (well-formed-cancel-debtor rep _ r (well-formed-cleanup-set _ (:id r) _ (well-formed-cancel-res _ r
         (well-formed-cancel-acts _ (:id r) (well-formed-run-upd w (:id r) run-cancel-row run-cancel-row-id h)))))))
```

For `i10-task` (I10, task part: "a task without a result has an alive run"), the copy fails. The first edit
kills run `r`, so `r`'s task now violates `i10-task` until `debtor-side` gives the task its result. The
override `i10-task-cancel-run-local-hand` (`inv/copier.clj` ~1365) is 30 lines that re-walk the composite. The
idea in it is three lemmas:

- **Break:** `i10-task-exempt-kill` turns `i10-task w` into `i10-task-exempt r.of (run-upd …)`. The exempt form `i10-task-exempt k` allows task `k`
  to be without a result and without a run.
- **Repair:** in each branch of `cancel-debtor` and `debtor-side`, one of these applies:
  - `i10-task-task-done-x`: the task gets `err ::cancelled`.
  - `i10-task-of-i10-task-exempt-comp`: the owner is a computation, so no task is exempt.
  - `i10-task-of-i10-task-exempt-find`: there is no such task.
- **Transport:** in between, `i10-task-exempt-frame` keeps the view (`cancel-mid-frame`: the activations, resources and
  cleanup edits do not touch the run and task keys).

The override is correct, but the reader has to reconstruct the break and repair structure from a proof
script. The same composite is overridden by 8 bundles, and `well-formed-dispatch-raw` by 11.

### 2.3 A patch: `i8-closed` and the companion `acts-parked`

To keep I8 through the cancel cascades, `i8-closed` needs P4: the cascade's worklist empties. P4 needs the
companion `acts-parked` (`cascade-done-acts-parked`). The base proof never carries `acts-parked`, so `inv/i8.clj` does two things:

- `g8-add-ga` rewrites `well-formed-transition`'s statement to take `(= (acts-parked w) true)`, and `g8-ga-calls` rewrites 22
  call sites in its proof text so that `hga` is passed on (`(well-formed-t12-complete w _ _ _ h)` becomes
  `(well-formed-t12-complete w _ _ _ hga h)`, …).
- 15 overrides (`well-formed-t14-cancel`, `well-formed-t14-host-cancel`, `well-formed-t16-close-scope`, `well-formed-t12-complete`, `well-formed-raw`, …) re-prove each transition
  between `transition` and the cascade, only to forward `hga`.

`g8-patch` also rewrites the proof of *every* source theorem, replacing calls such as
`(well-formed-run-upd w x run-wake …)` with `(i8-closed-run-upd x8s w x run-wake … run-wake-run-key …)`. This supplies the
fact that `run-wake` keeps the run key. Nothing the kernel checks for `i8-closed` exists as text that a reader
could open.

### 2.4 An exemption list: `i8-closed`'s escape list

The bundle is `i8-closed xs`, and I8 is `i8-closed []`. Closing a scope subtree (`close-local`) makes the alive runs of
tasks owned by the closed scopes violate I8. `i8-closed-close-local` puts them on the escape list:
`i8-closed xs w → i8-closed (xs ++ owned-runs w sub) (close-local w sub)`. These runs are exactly the cancel jobs that
the cascade queues next.

The cascade's loop invariant is `i8-closed (base ++ cj js) w`, where `cj js` is the runs of the pending cancel
jobs (`i8-closed-cascade`, `inv/i8.clj` ~1280). Each job discharges its own run. When P4 empties the worklist,
`i8-closed-cascade-done` returns `i8-closed base`. This is a clean idea: ghost state equal to the pending work. It is
the same pattern as `i10-task-exempt k`, `marks-waiting hxm`, `current-members xm`, `i5-dep-final xd` ("finality sites discharge in the same commit")
and `i10-current-exempt gxz gkz` ("computations demoted later in the same round", "runs being retired").

### 2.5 Diagnosis, with numbers

**The base proof only carries the facts that `well-formed` needs.** A guard that was checked (`cur-closed`
is false), a row that was found (`run-find w rid = some r`), membership (`r ∈ runs`), "this id is not a
computation id", or a companion (`acts-parked`, `i7-idle`, `comp-facts`): each is dropped at the call site, because `well-formed-run-upd`
does not take it. A part that needs such a fact at one leaf has to override every lemma from the item down
to that leaf.

A classification of the 331 overrides by statement and dependencies (measurement E8, a heuristic):

| Kind | Count | Meaning |
|---|---|---|
| adds a premise and calls another override of the same bundle | 96 | plumbing: forwards a fact down the chain |
| same statement and calls another override | 66 | plumbing parents (e.g. `well-formed-t4-spawn-top` around `well-formed-t4-spawn`) |
| adds a premise and is self-contained | 80 | a leaf needs a local fact (42 distinct lemmas) |
| same statement and self-contained | 87 | content: break and repair, or reasoning over several edits (50 distinct lemmas) |

`i8-closed`'s 51 overrides are three ideas plus plumbing:

- **Owners must be open (26 overrides):** a new task, source or link must not get a closed scope as its
  owner. This comes from the guards `cur-closed = false`, `root-open-if` and `scope-open-at root`.
- **Revival (9 overrides):** a run that becomes alive again (park, take, arm, await) was alive before.
- **Termination (15 overrides):** the cascade empties the escape list, which needs `acts-parked`.

One override (`well-formed-t-detach`) does not fit these three.

`marks-waiting`'s 45 overrides include 13 that only pass the fact "x is not a computation id" to a leaf. That fact
follows from id uniqueness in `Base` and the fact that x is a source, activation or link id.

**There is no notion of what a part reads.** Of the 1,357 (primitive, part) cells, 921 (68%) are disjoint
at table level: the edit writes no table that the part reads (measurement E3). Another 42 are frames because
the edit keeps the part's key projection. The remaining 316 cells are real obligations. Today every frame
is a hand-written `nil` entry, and the kernel checks it again for every copy.

At the composite level, table granularity does not separate much. The large transitions (T12, T14 and
others with cascades) touch nearly every table, so a large part such as `i10-task` or `i8-closed` is touched by about
50 of the 56 item-level transitions (measurements E4, E5). Small parts are touched by few:
`i1-scopes` (scope parents) and `comp-exists` are each touched by 17 of 56. So views pay off at the leaves, and in
explaining which transitions matter to a small part.

**The structure follows the history.** The link names (`chain-start`…`chain`) and bundle names (`acts-parked`, `i10-task`, `i9-res`,
`comp-facts`, `i14-ordered`, …) record the order of the proof campaign. The README's tables make them findable, but the
companion DAG appears only in theorem premises.

---

## 3. Options

Each option is grounded in `i10-task` (few overrides), `i8-closed` and `marks-waiting` (override-heavy), `acts-parked` and `comp-facts` (patches,
companions), and `i9-res` (per-call-site resource lemmas).

### (A) One generic preservation theorem (`GPrim Q`, as in `notes/generic-preservation.md`)

Prove the tree once over an abstract rest part `Q` and a structure of obligations. A part supplies one
instance, and its step theorem is an application.

- **Effect:** removes the copier, the roughly 10,000 copies and an estimated 200–300 s of load. Every
  checked proof exists as source text. The prototype: 47 generic lemmas; `pgl : GPrim i10-task-rest` from
  `i10-task`'s 19 primitive fields; 46 of 46 of `i10-task`'s copies restated and proved by `exact (gq-… i10-task-rest pgl …)`.
- **`i9-res`:** the per-call-site resource lemmas (`i9-res-res-upd-q` at `res-cancel-row` and at
  `res-set-phase rp-fired`) force fields per call site, not per primitive. There are 154 call sites and 58
  distinct (update primitive, row function) pairs, so the obligation structure has roughly 90–150 leaf
  fields (estimate).
- **Overrides:** they become composite-level fields with generic defaults. For `i8-closed` that is 51 fields
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

- **Guards (`i8-closed`'s 26 overrides):** the leaf "insert a task with owner o" receives the guard on its path.
- **Revival (`i8-closed`'s 9):** the leaf receives `r ∈ runs` and `run-alive r`.
- **"Not a computation id" (`marks-waiting`'s 13):** the leaf receives the find equation of the source or
  activation, and derives the fact from `Base`.
- **`acts-parked` (`i8-closed`'s 15 and the patch):** `acts-parked` is in `C`.
- **`i9-res`:** its per-call-site lemmas are the fields for those two leaves.

Estimate: plumbing (about 160 overrides) and patches (94) disappear. What remains is about 80 leaf proofs
that use a local fact (now ordinary fields) and about 50 distinct composite-level fields with real content.

**A caveat.** A path condition is a fact about the world in which it was tested. A leaf that runs after
further edits receives it for an earlier world. Carrying it forward is a frame argument (B) when the fact's
view is untouched in between. This is what the helper bundles `comp-exists`, `awaiting-run-alive`, `no-act-of-run` and `edge-debtor-kept` do today. In
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

- `i10-task` uses `i10-task-view = (run-keys runs, task-keys tasks, next-id)`, where `RunKey = (id, of, alive)` and
  `TaskKey = (id, run, done)`. `i10-task-rest-frame` is its frame. The `extra-args` entry
  `'well-formed-run-upd ['(fn [r] (Eq.refl (run-key r))) 4]` discharges the column-level side condition "f keeps the
  key" by `rfl` at every call site.
- `i8-closed` uses `i8-closed-view` (runs, task (id, owner), scope (id, open), source (id, owner, open)); `i9-res` uses
  `I9ResRunKey = (id, mode, resources)`.
- `comp-facts`'s frames are monotone, not equalities: `cmono` allows edits that keep or clear `C.run`, do not lower
  the epoch, and keep or clear `done-epoch`. `marks-waiting` chose a strict `<` so that "every epoch step is a frame".
  Both are rely relations.
- The base itself does this: `defframes` in `edits.clj` (`pending-exact` "reads only comps' id/pending and
  edges' creditor/marked").

What (B) adds:

- Views become a declared, uniform part of every part.
- Frame cells disappear from the source: they are derived from "edit e writes only table T" (one `rfl`
  lemma per edit) and a key lemma per table (`run-keys-upd`, `task-keys-upd`, …).
- Each part's namespace starts with its non-frame table.

Examples:

- **`comp-exists`** ("computation cx exists", a helper used inside T11): today 8 proof cells and 25 `nil` cells.
  With the view `ids of comps`, every cell is a frame except `comp-ins`. Even the edge edits that change a
  creditor's `pending` keep the ids.
- **`i10-task`, `i8-closed`:** the views are already shared. `run-keys` appears in `i10-task`, `i8-closed`, `i10-current-exempt` (with epoch) and `alive-run-latest`
  (`arrk`), so a lemma about how a composite moves `run-keys` serves all of them (see (C)).

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

- `i8-closed-view-cancel-run-local`: on `i8-closed-view`, T14's local part only lowers the alive bit of `r`.
- `cancel-mid-frame`, `i10-task-view-t13-retire-with-subtree`, `i8-closed-view-debtor-side`.

The hot composites, ranked by how many bundles override them, are:

| Composite | Bundles overriding it |
|---|---|
| `well-formed-dispatch-raw` | 11 |
| `well-formed-spawn-rows` | 10 |
| `well-formed-cancel-run-local`, `well-formed-take-park`, `well-formed-start-raw` | 8 each |
| `well-formed-retire-one`, `well-formed-complete-raw`, `well-formed-t12-complete`, `well-formed-await-raw`, `well-formed-arm-park` | 7 each |

A summary per (hot composite, shared view family) gives each part a one-line reason at that composite.
`notes/hm13-contracts.edn` shows that contracts are already the working tool during the proof campaigns.
(C) is compatible with everything else: a summary is a lemma that field proofs use.

### (D) Exemption forms as a first-class pattern

Every part that is ever deferred within a step gets a uniform API:

- an exempt form `Q[X]`, with `Q = Q[∅]` and `Q[X] → Q[X ∪ Y]` (monotone);
- **break lemmas** `Q[X] w → Q[X ∪ {k}] (e w)`, and **repair lemmas** `Q[X ∪ {k}] w → fact k → Q[X] (e' w)`;
- for loops, the ghost is a function of the worklist (`cj js` for `i8-closed`, the pending fires for `i5-dep-final`).

The model has the forms (`i8-closed xs`, `i10-task-exempt k`, `marks-waiting hxm`, `current-members xm`, `i5-dep-final xd`, `i10-current-exempt gxz gkz`, `i1-runs-exempt`, `mark-targets-dep`,
`markers-gone`) and many break and repair lemmas (`i8-closed-close-local`, `i10-task-exempt-kill`, `i10-task-task-done-x`, `i8-closed-cascade`). They
are not uniform: the exemptions are bundle parameters for some parts and separate predicates (`i10-task-exempt`) for
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
one round of Rule R (`i10-current-exempt`'s demotions). They are not left from the raw transition for Rule R to repair,
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
  rule `{P} c {Q} ⊢ {P * R} c {Q * R}`. The rely view of (B) explains `comp-facts`'s and `marks-waiting`'s monotone frames.
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
                                  (chain-start … chain kept as abbreviations; old step-p3* restated)
spindel.v2.pres.core              Base, View/Frame, Leaf C Q, Over C Q L, PartProof, defpart
spindel.v2.pres.frames            per-edit "writes only table T" lemmas; per-table key lemmas
                                  (run-keys-upd …); default leaf from a view
spindel.v2.pres.tree.*            the generic step tree, once, over an abstract part:
    .edits   .rule   .cascade   .items   .step
                                  each composite lemma is stated as
                                  Leaf C Q → Over C Q L → Base ∧ C ∧ Q → Q (T …)
                                  and ends with `step-pres`
spindel.v2.pres.summaries         view summaries of hot composites ((C))
spindel.v2.inv.<part>             one per invariant part, fixed layout (4.4)
spindel.v2.inv.members.*          h-mem2 (current-members): same layout; its many stages become sections
```

`inv.copier` survives only until the last bundle is converted (staging, section 5).

### 4.2 Key definitions and theorems

Lean-like notation; the DSL forms are the `a/structure` and `a/theorem` analogues. Following the
prototype, the obligation structures live in `Type` and their instances are `a/defn`.

```lean
def Base (w : World) : Bool := well-formed w

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
companions, step theorem) → `step-i10-task := step-pres gl-ctx gl-proof` → the `defpart i10-task` table → one cell,
for example `retire-run ↦ i10-task-retire-run-hand` → `retire-rest`, a 30-line lemma about clearing the
task's run and deleting the dead run row.

To see *how* T13 is put together, read `pres.tree` once (`gen-retire-local`). To see *why* `i10-task` survives
T13, read the one cell. Today the second question takes the generated copy (which is not in the source),
the override, and the patch of `well-formed-job-apply` that passes membership facts down.

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

### 4.5 Worked example 1: `i10-task` (I10, task part)

```clojure
(ns spindel.v2.inv.i10-task      ; today: bundle i10-task in inv.copier
  "I10, task part. In words: (a) every run's `of` is below the allocator; (b) a run R of a task K is
  K.run; (c) a task without a result has an alive run.")

;; 2. View: run keys (id, of, alive), task keys (id, run, done), the allocator.   (i10-task-view, i10-task-rest-frame)
;; 3. Exempt form: i10-task-exempt k — (c) may fail for task k.   i10-task-exempt-frame (frame)
;;    break  i10-task-exempt-kill            a run made done: only its task r.of may lack a run
;;    repair i10-task-task-done-x      the task gets its result;  i10-task-of-i10-task-exempt-comp: r.of is a computation;
;;           i10-task-of-i10-task-exempt-find      there is no task r.of
(defpart i10-task
  :rest i10-task-rest :view i10-task-view :frame i10-task-rest-frame :exempt i10-task-exempt :companions [acts-parked]
  :leaf {run-upd/wake    run-wake-run-key          ; resume (Z#50): key kept -> frame by lemma
         run-upd/park    i10-task-run-upd-up          ; alive goes up: (c) only gains witnesses
         run-upd/kill    i10-task-exempt-kill               ; BREAK (cancel, complete)
         task-upd/result i10-task-task-done-x         ; REPAIR
         new-run-of/comp i10-task-comp-run-hand          ; `of` is a computation, not a task (comp-has on the path)
         bump            i10-task-rest-bump           ; (a) is monotone in the allocator
         filter-world    i10-task-filter-world-hand}     ; Rule R keeps alive runs (normalized; uses acts-parked's acts-alive)
  :over {cancel-run-local i10-task-cancel-run-local-hand ; T14 local: break at run-upd, repair in debtor-side
         complete-raw     i10-task-complete-raw-hand     ; T12: break at run-upd, repair at complete-task
         retire-run     i10-task-retire-run-hand     ; T13: clear the task's run, delete the dead run (retire-rest)
         spawn-rows       i10-task-spawn-rows-hand})     ; T4: new task + its alive run, inserted together
```

What disappears compared with today:

- the 32 `prim!` lines, which become 7 leaf entries; the rest are frames;
- 4 of the 9 overrides, which were plumbing:
  - `well-formed-t12-complete` forwarded `res-tag-ok`, a guard on the path;
  - `well-formed-retire-one` forwarded membership and `run-alive`;
  - `well-formed-start-raw` and `well-formed-dispatch-raw` forwarded `comp-has` (today through the helper bundle `comp-exists`);
- a fifth override, `well-formed-new-run-of`, becomes a leaf entry;
- the 6 patches (`up-patch`, `run-wake-run-key`, `well-formed-job-apply`, `well-formed-transition`, `well-formed-t5-start`, `well-formed-t11-dispatch`), which
  supplied key lemmas at call sites or forwarded facts.

The `comp-exists` bundle disappears as well. Its fact, that computation `c` exists, is tested on the path at the
input world. Its view (the computation ids) carries it to the leaf after `cancel-pred` and `cut-suffix`,
because neither writes that view: a (B) frame. The proofs that stay are the same
lemmas as today; they move into the table.

### 4.6 Worked example 2: `i8-closed` (I8, closed scopes)

```clojure
(ns spindel.v2.inv.i8
  "I8: a closed scope owns no alive run (of its tasks) and no open source.")
;; 2. View: i8-closed-view = run keys, task (id, owner), scope (id, open), source (id, owner, open).  i8-closed-of-view
;; 3. Exempt form: i8-closed xs, the ESCAPE LIST: alive runs of tasks owned by closed scopes that are
;;    allowed for now. Ghost: in the cascade, xs = base ++ runs of the pending cancel jobs.
;;    break  i8-closed-close-local      closing a subtree appends owned-runs (they are the next cancel jobs)
;;    repair i8-closed-job-cancel       a cancel job kills its run
;;    loop   i8-closed-cascade          invariant i8-closed (base ++ cj js) through every job
;;    exit   i8-closed-cascade-done     P4 (cascade-done-acts-parked, needs companion acts-parked): js = [] at the end
(defpart i8-closed
  :rest i8-closed-rest :view i8-closed-view :frame i8-closed-of-view :exempt [x8s] :companions [acts-parked]
  :leaf {task-ins/owner   g8-owner-open      ; a new task's owner is not closed: guard on the path
                                             ;   (cur-closed = false — model-only, P10 open!; root open;
                                             ;    detach-ok; a computation owner)
         source-ins/owner g8-owner-open      ; same, for sources and links
         run-upd/revive   i8-closed-run-upd-up      ; park/take/arm/await: the run was alive (r ∈ runs, alive)
         source-upd/close i8-closed-source-close    ; a source closes
         task-upd/detach  i8-closed-task-owner      ; a new owner that is an open scope (detach-ok)
         run-del          i8-closed-rest-run-del
         scope-del        i8-closed-rest-scope-del}
  :over {run-cascade      i8-closed-run-cascade-acts-parked})  ; break (close-local inside close/retire jobs), repair
                                               ; (cancel jobs), loop invariant with its ghost, and P4
```

Of the 51 overrides, under (A+) these remain:

- the cascade field, with its ghost. The break (`close-local`, applied inside the close and retire jobs)
  and its repair both happen inside the cascade, so a single composite field holds them;
- possibly `t-detach` and `well-formed-serve-or` (to be checked).

The 26 creation overrides become two leaf entries whose path condition carries the guard. The 9 revival
overrides become one leaf with `r ∈ runs ∧ run-alive r`. The 15 `acts-parked` overrides and the `g8-add-ga` patch
disappear into `C = acts-parked`. The source-text patch `g8-patch` (wake, consume, close, detach rows) becomes four
leaf entries.

Estimate: 51 overrides and 3 patches become about 10 table entries and 1–3 composite entries.

A side benefit is that the dependency on the model-only guard `cur-closed` (P10, open) becomes one visible
cell of the I8 table. Today it is buried in 26 plumbing overrides.

For `marks-waiting` (45 overrides), the same treatment turns the 13 "not a computation id" overrides into one fact
that the generic leaves derive from `Base` and the find equation. The remaining content is the fire and
dispatch reasoning and the `comp-facts`/`i7-idle` companions.

---

## 5. Effort, staging, regression, risks

Estimates assume one person working on this full time, with wide error bars (a factor of 2).

| Stage | What | Breaks nothing because | Estimate |
|---|---|---|---|
| 0 | Docs only: section 1 into the README; the companion DAG; per-part obligation tables generated from the copier's atoms (renames, overrides, patches) | no proof changes | 2–3 days |
| 1 | (B)+(D) inside the copier: a declared view and frame per part (most exist: `i10-task-view`, `i8-closed-view`, `i10-task-exempt-frame`, …); `defpart` as a front-end that *emits today's* `prim!`/`override!` calls; uniform exempt names and break/repair docs | same generated theorems | 1–2 weeks |
| 2 | (A) on the clean part of the tree; convert the 11 bundles without overrides or patches (`comp-exists`, `no-dep-edges-of`, `markers-gone`, `open-scopes-have-runs-exempt`, `edge-kind-kept`, `edge-debtor-kept`, `mark-targets-dep`, `no-act-of-run`, `run-gone`, `i14-validity-rule-r`; `acts-parked-exempt` has none); measure load | each converted bundle restates its old names | ~1 week (note's estimate) |
| 3 | (A+) leaf contexts: leaf fields with path conditions; convert `i10-task` and `i9-res`, then `i8-closed`, `marks-waiting`, `i7-idle`, `comp-facts`; their plumbing overrides are deleted | old statements restated | 2–4 weeks (main unknown) |
| 4 | Companions `C` and `CarryC`; delete the patches (`g8-add-ga`, `gd-add-hyps`, …) | old statements restated | 1–2 weeks |
| 5 | `inv.parts` as a DAG; `chain-start`…`chain` and `step-p3*` become restatements | `top` statements byte-identical | 2–3 days |
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
| R2 | Leaf contexts: can field statements be generated (the hypothesis types at each call site), or must the generic tree be written by hand? | hand-write the generic `cancel-run-local` and `complete-body` with full-context leaves; check that `i10-task`'s and `i9-res`'s overrides of them become field proofs; then try extracting the local context at a call site from the elaborator |
| R3 | Every composite overridden by *any* part must be a field, and the generic parents must call the field, not the default; the field list may grow | compute the union of override targets per stage (134 today, about 50 content); keep it as a checked list |
| R4 | Companions through intermediate worlds (`CarryC`): the DAG has depth 4 (`acts-parked`→`i7-idle`→`comp-facts`→`marks-waiting`) | convert `comp-facts` (companions `i7-idle`, `i10-current`) on T6 and T12 first |
| R5 | Exemption ghosts change *inside* loops (`i8-closed`'s `cj js`, `i10-current-exempt`'s `gxz`), which a fixed-`Q` tree cannot express | keep them as `Over` fields (hand proofs, as today); check that no *leaf* needs a ghost update besides the break edits |
| R6 | The footprint numbers (68% table-disjoint, 316 real cells, 50 content overrides) are syntactic approximations | after the copier loads, try `rfl` or `simp only [defs]` on `view (e w) = view w` for every predicted-frame cell (921), and count failures |
| R7 | The load-time gain is extrapolated from a 47-lemma slice | stage 2 measures it on 11 bundles |
| R8 | (D)'s "no global in-transition invariant" claim rests on reading `i8-closed`, `i10-task`, `i5-dep-final`, `i10-current-exempt`, `marks-waiting`, `current-members` | check the remaining bundles' docstrings for a break that Rule R repairs (none seen) |

---

## 5a. Stage 1: what landed, and what it showed

**What landed.** Three pieces, all front ends that emit the copier calls of before:

- `spindel.v2.pres.frames`: one footprint lemma per primitive edit, `writes-<edit>` (the edited world
  is the input world with only the written fields replaced; 39 lemmas, `rfl` except the `match`-defined
  edge edits and the checked insert, which go by cases), and `defview`, which states a part's view as
  `<rest>-frame-<field>` for every field the part does not read (`rfl`). `frame-term` composes the two
  into the proof of a frame cell.
- `defpart` in `inv.copier`: a part declares `:reads` and the cells that need an argument; every other
  primitive's cell is generated (`prim!` with the generated frame proof). Converted: `i10-task`, `i1-scopes`, `i8-closed`
  (with the fixed comment block of section 4.4: the part, view, exempt form, cells, deferred within a
  step, companions) and 24 more parts whose cells were a plain list of `nil` frames (`i9-res`, `i7-idle`, `marks-on-dep`,
  `refs-not-edges`, `act-runs-alive`, `i5-seen`, `tombs-dormant`, `i10-current-exempt`, `root-scope-reserved`, `i5-dep-final`, `i1-detached-closed`, `comp-facts`, `i14-validity-raw`, `marks-waiting`, `alive-run-latest`, `edge-kinds`, `current-members`, `scope-parents-acyclic`,
  `l2-measure`, `open-scopes-have-runs`, `cleanup-runs-exist`, `host-roots-revoked`, `stays-released`, `task-unheld-scope-absent`).
- `spindel.v2.pres.exempt`: `defexempt` records a part's exempt form (the ids it holds, its empty
  instance at commit) and aliases the lemmas that open and close deferred violations under uniform
  names `<part>-exempt-<role>[-<site>]`. With aliases: `i10-task`, `i8-closed`, `i1-runs-exempt`; recorded without aliases:
  `i5-dep-final`, `i10-current-exempt`, `marks-waiting`, `current-members` (their lemmas do not fall into break/repair one to one; see below).

**Frames, measured.** The views were measured in the kernel, not read off the source (risk R6): for
each of the 51 bundles' rest predicates and each of the 15 World fields, `rest (set-f w v) = rest w` was
tried by `rfl`; a field where it fails is read. Against those views:

- every one of the 876 `nil` cells left in the source at that point is a table-level frame, except
  Rule R's filter for `stays-released`, which became one too once the filter got its footprint (it does not write
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
- Eager generation can add a cell the copy never uses: one here, `i1-scopes-run-ins-fresh` (`i1-scopes` has no run
  insert in its closure). For the 24 parts not converted, mostly helper bundles with small closures, it
  would add up to 10 unused cells each (`i1-runs`, `nz`), which is why they keep their lists.

**Exemption forms, checked (R8, and a correction to option D).** Of the bundle parameters, two kinds
must be told apart:

- *Exemption sets*, weaker as they grow and empty at commit: `i8-closed x8s` (run ids), `i10-task-exempt k` (one task
  id, a predicate beside the bundle), `i1-runs-exempt xr` (run ids), `i5-dep-final xd` (debtor ids), `i10-current-exempt gxz gkz`
  (computation ids, run ids), `marks-waiting hxm` (debtor ids), `current-members xm` (computation, debtor and member ids).
- *Focus parameters*, stronger as they grow, which carry a fact about given ids through one composite:
  `markers-gone nids` (no marker in nids), `mark-targets-dep mkm` (marked edges on these debtors are dep edges), `tombs-dormant y`
  (computation y is no tombstone; `inv` uses `tombs-dormant 0`), `comp-exists cx`, `awaiting-run-alive`, `no-act-of-run`, and the other helper bundles.
  Section 3 (D) listed `markers-gone` and `mark-targets-dep` among the exemption forms; they are not.

No exemption opened in a raw transition is left for Rule R, as option D assumed. The reason is
structural: a copied lemma keeps the bundle parameters fixed from its input world to its output world,
so `raw-<part>` and each Rule R round lemma start and end at the same exemption set (the empty one in
`inv`); a deferred violation cannot outlive the composite that opened it. Inside, the sets change only
in overrides (the breaks and repairs) and loop invariants (`i8-closed-cascade`'s ghost).
`i5-dep-final` and `current-members` do not have one break and one repair lemma per site: `i5-dep-final` discharges a whole finality
site through an escape predicate (`jw`, `jw-fire-edge`, `jw-fin-fold`), `current-members` removes exemptions with
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

Converted: `no-dep-edges-of`, `markers-gone`, `edge-kind-kept`, `edge-debtor-kept`, `mark-targets-dep`, `run-gone`. Not converted, and why:

- `i14-validity-rule-r`, `no-act-of-run`, `open-scopes-have-runs-exempt`: their primitive cells take a bundle-specific side condition at the call site (the
  copier's extra args: a key-preserving row function for `comp-upd`, `act-upd`, `run-upd`), so a bare
  leaf `forall f, ...` cannot be instantiated from their cells. This is obstacle 1 of
  `generic-preservation.md`: such leaves are per call site (primitive applied to the row function used
  there). It is the same kind of extension as the call-site context below.
- `comp-exists`: it lives in `inv.copier`, which the tree namespace loads after; moving it is a separate change.
- `acts-parked-exempt`: not override-free; it shares four overrides with `acts-parked` (`well-formed-fill-slot`, `well-formed-fire-dep`,
  `well-formed-fire-wait-act`, `well-formed-resume`).

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
for bundle-specific side conditions (`i14-validity-rule-r`, `no-act-of-run`, `open-scopes-have-runs-exempt` above).

**R2 moves to stage 3**: how the context of a call site is obtained (hand-written generic composites, or
an ansatz hook that reports the local context at a term position). Its input: of the 46 primitive call
sites in the composites of the 11 candidate parts, 24 have path facts in scope (a hypothesis introduced
by `cases`, `case` or `have` above the call; counted from the source text):

| composite | primitive | facts in scope |
|---|---|---|
| `well-formed-await-step` | `well-formed-insert-edge-checked` | `hd`, `[false` |
| `well-formed-await-step` | `well-formed-comp-upd` | `hd`, `[true` |
| `well-formed-await-step` | `well-formed-insert-edge-checked` | `hd`, `[true` |
| `well-formed-await-step` | `well-formed-comp-upd` | `hd`, `[true` |
| `well-formed-await-step` | `well-formed-edge-upd` | `hd`, `[true` |
| `well-formed-clear-comp-run` | `well-formed-comp-upd` | `hc`, `hr` |
| `well-formed-clear-task-run` | `well-formed-task-upd` | `hc`, `hr` |
| `well-formed-consume-entry` | `well-formed-edge-upd` | `hf`, `hr` |
| `well-formed-consume-entry` | `well-formed-remove-edge` | `hf`, `hr` |
| `well-formed-debtor-side` | `well-formed-task-upd` | `hc` |
| `well-formed-demand-reactive` | `well-formed-comp-upd` | `hc`, `hi`, `hv` |
| `well-formed-demote` | `well-formed-drop-edges` | `hf`, `hi` |
| `well-formed-demote-epoch` | `well-formed-comp-upd` | `b` |
| `well-formed-demote-finish` | `well-formed-comp-del-unref` | `hf`, `hk` |
| `well-formed-demote-finish` | `well-formed-drop-edges` | `hf`, `hk` |
| `well-formed-demote-finish` | `well-formed-comp-upd` | `hf`, `hk` |
| `well-formed-dep-consumed` | `well-formed-edge-upd` | `hf` |
| `well-formed-dep-consumed` | `well-formed-remove-edge` | `hf` |
| `well-formed-fill-slot` | `well-formed-act-upd` | `hm` |
| `well-formed-fire-observe` | `well-formed-edge-upd` | `hs` |
| `well-formed-fire-wait` | `well-formed-remove-edge` | `hc` |
| `well-formed-insert-edge-checked` | `well-formed-insert-edge-fresh` | `hk` |
| `well-formed-raise-loop` | `well-formed-comp-upd` | `[cons`, `u`, `f`, `ih` |
| `well-formed-react-add` | `well-formed-insert-edge-checked` | `hk` |

**Measurements.** The tree has 16 leaves (in 1 chunk), 39 `Over` fields (2 chunks) and 59 composite lemmas
(`gqd-` defaults and `gq-`), elaborated once in 2.6 s. The six parts' 228 generated copies (`no-dep-edges-of` 22,
`markers-gone` 58, `edge-kind-kept` 47, `edge-debtor-kept` 47, `mark-targets-dep` 11, `run-gone` 43) are now restatements, proved by applying the generic
lemmas; three cells were added where a part's copy never needed them (`edb-close-scope-id`,
`edb-comp-del-unref`, `mdk-close-scope-id`). Load time, measured back to back: the namespaces this stage
touches (the tree, `inv.idle`, `inv.base`, `inv.i1-runs`, `inv.members.dispatch`,
`completion.drained`) took 57.9 s before and 59.9 s after, tree included; the whole model went from 441 s
to 549 s, but the unchanged namespaces account for 106 s of that (host load). For these helper parts the
tree does not pay yet: their copies were small, and the one-time cost of the tree is about what they
saved. The gain the note estimates comes with the chain parts, whose copies are large (stage 3).
Statements: all 16,496 theorems of stage 1 have identical fingerprints; 172 are new (the tree, the six
`Leaf` instances, the three cells).

## 5c. Stage 3 on `i10-task`: the generic tree by open recursion, and how a part gets its facts

**Result.** `i10-task` goes through the generic tree. Its 9 overrides and 6 patches are gone from the copier;
what is left is a table of 3 site entries and 6 entries for its own composite proofs, and every lemma the
copier used to generate for it (176) is restated under its old name and statement. Getting there needed a
change to stage 2's tree, not only new fields: the two total structures `Leaf` and `Over` cannot carry a
part that breaks its invariant inside a transition. The tree is now written by *open recursion*: each
composite's generic lemma takes its callees' statements as hypotheses. The facts the base proof drops are
declared once in the tree, per callee (N), and passed at the call sites by the tree's own proofs (H).
Generating them from the elaborator (T) was measured and is not worth it.

### What stage 2's tree could not do

Stage 2's `Leaf Q` had one field per primitive in the bare shape, among them `well-formed-run-upd`,
`well-formed-task-upd` and `well-formed-run-del`. A Lean structure is total, so a part must prove every field. `i10-task`
cannot: a run update in general may kill a run (T14, T12), and the copier fed `i10-task` a key-preservation
proof at every call site (its extra argument) that the bare field does not have. Per-call-site fields
(the §5b rule) fix the shape but not the break: at T14's `run-upd … run-cancel-row` the part is false
until the same composite repairs it, so no statement of that leaf, with any context, holds for `i10-task`.
Such a leaf may only be reached through a composite the part overrides.

`Over Q P` did not allow that either. `over-default` filled every field with the stage-2 default copy
(`gqd-`), which re-proves each override point from the leaves. `well-formed-job-apply`, `well-formed-cascade` and
`well-formed-run-cascade` are `Over` fields whose default reaches `well-formed-cancel-run-local` through `gqd-`, so a
part that overrides `cancel-run-local` but takes the default of `job-apply` still needs the break leaf.
The default of an outer override point has to call the part's proof of the inner one: open recursion.

### The tree now (`spindel.v2.pres.tree`)

```
pres-x : ∀ Q, x's binders, (S c over Q, for every lemma c that x's proof calls) → S x over Q
```

`S c over Q` is c's statement with `well-formed` replaced by `gp Q` (Base and Q). The proof of `pres-x`
is x's base proof, with each callee replaced by its hypothesis; 189 of them, generated from the source
text of `edits`/`step`/`rule`/`engine`. A part restates each lemma the copier generated for it as one
application, `pres-x` applied to the part's own lemma for each callee (`restate!`), bottom up. A part's
own proof of a composite replaces the generic one at that node (`part!` `:over`). There is no `Leaf` or
`Over` structure, no default copy, and no list of override points: any node can be overridden, and a part
proves exactly the callees of the nodes it takes from the tree.

Two kinds of callee need more than the base lemma's statement:

- **Sites.** An update primitive is one hypothesis per row function: `run-upd` at `run-wake` and at
  `run-tick` are different hypotheses, with f fixed. A part proves each site it reaches, by default from
  its cell and the bundle's extra argument (for `i10-task`, `rfl` on the run key at every site but three).
  `t-finally-enter` names its row function only through unification; its tree source states it,
  generalized over the finalizer it pushes (`site-gen`).
- **Contexts.** Facts the base proof checks on the path and drops. They are declared per callee, as
  premises a part may use there (`contexts`); the tree's proofs pass them at the call sites (`passes`:
  an argument inserted at a call; `sources`: a tree proof that differs from the base proof, for a node
  that must take a context to pass it on). A part that does not need a context drops it with
  `ctx-<x>`, proved once. That is the §5b default rule, as a hypothesis type instead of a field.

`i10-task` needed contexts only on composites, never on a primitive leaf: what its leaves need is a fact about
the row function (a site), and what its composites need is a fact from the path.

### `i10-task` before and after

| | before (copier) | after (tree) |
|---|---|---|
| cells | `defpart GL` (view, 10 cells, frames) | unchanged |
| run updates | extra argument `rfl`; `up-patch` on `park-if`, `take-park`; patch of `resume` | 3 site entries (`run-wake`, `run-park-row`, `run-tick-park`); every other site from the extra argument |
| own proofs | overrides of `cancel-run-local`, `complete-raw`, `retire-run`, `spawn-rows` (4 one-line wrappers of the `-o` lemmas) | `:over` entries naming the `-o` lemmas; the old names become aliases |
| new runs | overrides of `start-raw`, `new-run-of` | two hand lemmas (unchanged statements) as `:over` entries |
| plumbing | overrides of `well-formed-t12-complete`, `well-formed-retire-one`, `well-formed-dispatch-raw`; patches of `well-formed-job-apply`, `well-formed-transition`, `well-formed-t5-start`, `well-formed-t11-dispatch` | none in `i10-task`; in the tree: 7 contexts, 6 passes, 2 sources, shared by every part |
| generated | 176 copies (`lcopy!`, 15 roots) | 169 restatements, 4 aliases, 2 hand lemmas, 1 restated primitive |

The table (`spindel.v2.inv.i10-task`):

```clojure
(tree/part! GL
  :sites '{[well-formed-run-upd run-wake]      (i10-task-run-upd w x run-wake hf run-wake-run-key h0)  ; resume: key kept, by lemma
           [well-formed-run-upd run-park-row]  (i10-task-run-upd-up …)                                ; park: alive goes up
           [well-formed-run-upd run-tick-park] (i10-task-run-upd-up …)}                               ; take, parked: same
  :over '{well-formed-cancel-run-local i10-task-cancel-run-local-hand   ; T14 local: break i10-task-exempt-kill, repair in debtor-side
          well-formed-complete-raw     i10-task-complete-raw-hand       ; T12: break i10-task-exempt-kill, repair at complete-task
          well-formed-retire-run     i10-task-retire-run-hand       ; T13: retire-rest
          well-formed-spawn-rows       i10-task-spawn-rows-hand         ; T4: a task and its alive run, together
          well-formed-start-raw        i10-task-start-raw            ; T5: a new run of an existing computation
          well-formed-new-run-of       i10-task-new-run-of})         ; T11: same
```

The tree's side, every line with its reason (`contexts`, `passes`):

| callee | context | passed at |
|---|---|---|
| `cancel-run-local` | `r ∈ runs` | `job-apply`: `run-find` found it |
| `retire-run` | `r ∈ runs`, `run-alive r = false` | `job-apply`: found; `retirable` means done |
| `complete-raw` | `r ∈ runs`, result tag not none | `t12` (`tok-facts`, the tag guard), `retire-one` (found; an err result) |
| `start-raw`, `new-run-of` | `comp-has w c.id` | `t5` (`comp-find` found it), `dispatch-raw` |
| `well-formed-t12-complete` (own) | `res-tag-ok tag` | `transition`: the refusal guard |
| `dispatch-raw` (own) | `comp-has w c.id` | `t11`; carried through `cancel-pred`, `cut-suffix`, `consume-entry` by `comp-exists` |

Against the success criteria: 9 overrides and 6 patches became 3 site entries and 6 own-proof entries.
Of the six, four are content (two deferred violations, T13's retire, T4's insert); `start-raw` and
`new-run-of` are two three-line adapters of one lemma, `i10-task-comp-run-hand`. Merging them into one entry needs
a context on `add-run-scope` and a new lemma; not done. Every context premise is one line with a reason.
No statement changed.

`comp-exists` does not disappear (§4.5 predicted it would). Its fact, `comp-has w c.id`, is not a table-level frame
of `cancel-pred` and `cut-suffix`: both write the comps table (`comp-upd`, the pending resync of
`drop-edges`). It survives because they keep the computation ids, a column-level frame whose proof is
`comp-exists`'s copy. `comp-exists` stays a copier bundle; the tree's `dispatch-raw` uses its lemmas. Converting `comp-exists` to
the tree would put it between the generic lemmas of `cut-suffix` and of `dispatch-raw`; small, not done.

### N, H, T compared (on `i10-task`'s and `i9-res`'s call sites and the 24 of §5b)

- **N (statements from the overrides).** The difference between an override's statement and its base
  lemma's, computed for every override of `i10-task` and `i9-res`: 7 contexts for `i10-task`, 3 for `i9-res`, each one or two
  premises. They are shared: `i9-res`'s context at `cancel-run-local` is `i10-task`'s (`r ∈ runs`). No context
  had to be widened when it was used.
- **H (the tree passes them).** 6 call-site insertions and 2 tree proofs (`t12`, `dispatch-raw`, whose
  own statements take the context), plus one source for `t-finally-enter`'s row function. Written once,
  in the tree, for every part; before, `i10-task` and `i9-res` each carried the same `job-apply` patch.
- **T (from the elaborator).** Replacing the call by `?_` and printing the state (`refine'`,
  `trace_state`; no ansatz change needed) gives the local context at a call site. Over 39 sites: 91 path
  hypotheses (2.3 per site, at most 10), 86 characters per site. For `i10-task`'s 8 context sites, 0 contain the
  needed fact as stated; 6 contain a raw fact it follows from by one lemma (`run-find w rid = some r` for
  `r ∈ runs`, plus a variable `rid` the callee does not have); 2 lack it altogether, because it was
  established in a caller one level up (`t12`'s tag guard comes from `transition`; `dispatch-raw`'s computation
  from `t11`, carried through three edits). The hypotheses carry the base proof's local names (`hf`,
  `ha`, `hc`) and print projections as field indices (`c.11`, `w.14`), so a generated statement changes
  when the base proof is renamed or restructured. T is a development aid (print the context at a call
  site, to choose a context), not a generator.

### `i9-res`: are per-primitive leaves too coarse?

Yes, and per call site is finer than needed. `i9-res`'s two resource lemmas (`i9-res-res-upd-q` at
`res-cancel-row` and at `res-set-phase rp-fired`) are the only two `resource-upd` sites of the step, with
different row functions; one hypothesis per (primitive, row function) separates them. For `i10-task` and `i9-res`
no (primitive, row function) pair needs different proofs at different sites (`run-tick` has 13 sites,
all `rfl` on both keys). `i9-res` on the tree would be: 2 site
entries, own proofs at `cancel-run-local` (`i9-res-cancel-mid`, using the shared context), `ack-raw` and
`arm-park`; new contexts `arm-park` (`r ∈ runs`, not unwinding) and `t17` (own: not in a cleanup slice),
one pass in `transition`. Its 4 overrides and 4 patches go; not converted here.

### The generic tree as real source (prototype: `notes/real-source-proto.clj`)

`src-cancel-run-local` is T14's local part written by hand over Q, its five callees as named hypotheses
(`kill`, `acts`, `res`, `cleanup`, `debtor`); its proof is the base proof's five lines with those names.
`inv-cancel-run-local-derived` restates the base lemma (same statement) from it with Q the trivial part.
Findings:

- The derivation is not free. `gp triv w` is `well-formed w && true`, which is not `well-formed w` by
  definition (`Bool.and` is stuck on its first argument), so each callee's base lemma is wrapped
  (`triv-up`/`triv-down`): 5 lambdas, 12 lines for a 5-line lemma. Putting Q first in `gp` would make the
  trivial part definitional, but then every part's restatement (`i10-task w` is `well-formed w && i10-task-rest w`)
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
  any of them. 197 new: 189 `pres-*`, 5 `ctx-*`, `gp-well-formed`, `gp-parts`, `gp`'s equation lemma.
  `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-chain`, `mv-refinement`
  unchanged; `inv` is a definition, its source untouched.
- **Load**, two runs back to back (one JVM each, 1 GB): the namespaces this stage touches took 63.4 s
  before and 65.7 s after: `inv.copier` 15.4 → 11.4 s (i10-task's copies gone), `pres.tree` 1.8 → 10.3 s (it
  now covers the whole step: 189 generic lemmas instead of 59 composites twice), `inv.i10-task` 0.6 s,
  the five stage-2 parts' namespaces 46.0 → 43.5 s. The untouched namespaces went 315.9 → 295.6 s (host
  load); the whole model 379 → 361 s. The tree is a one-time cost of about 8.5 s; `i10-task` alone saved 4 s
  of copies, so it pays once two or three more chain parts move (their copies are larger).
- **Suite**: `clojure -M:test`, 288 tests, 208,300 assertions, 0 failures, 0 errors (the oracle on samples
  1–60 included; stage 2: 286 tests, the tree test now has three).

### Revised plan for the rest of stage 3

The tree by open recursion makes stage 3 a per-part table plus tree lines; stage 4 (companions) becomes
the same mechanism: a companion is a context, carried through intermediate worlds by the companion's own
restated lemmas, as `comp-exists` carries `comp-has` here.

| part | what it needs | estimate |
|---|---|---|
| `i9-res` | 2 sites, 3 own proofs, 2 contexts, 1 pass (above) | ½ day |
| `i8-closed` | contexts at the insert composites (owner open: `cur-closed`, `root-open-if`, `scope-open-at`); revival (9 overrides) needs a context *on a site* (`run-upd` of a run that is a live row), which the tree does not have yet: a site context, keyed by (primitive, row function), about a day; `acts-parked` (15 overrides, `g8-add-ga`) as a companion context on the cascade, carried by `acts-parked`'s restated lemmas | 4–6 days |
| `marks-waiting` | 13 "not a computation id" overrides become contexts at the source, activation and link composites; companions `comp-facts`, `i7-idle`, `tombs-dormant`, `i10-current`, `i14-ordered` as contexts | 3–5 days |
| `i7-idle`, `comp-facts` | companions (`acts-parked`; `i7-idle`, `i10-current`) as contexts; `comp-facts`'s `cmono` frames as sites | 2–3 days each |

About 2½–3½ weeks with stage 4 folded in; the main risk is now carrying companions through the cascade
(R4), not the shape of the leaves (R1, R2 are settled: no structures, and contexts are declared, not
generated). Revised in §5d: `i9-res` as estimated; `i8-closed` needs contexts declared per part first.

### What the earlier sections got wrong

- §4.2, §5b: `Leaf` and `Over` as total structures, with `Over.default` from the leaves, cannot carry a
  part that breaks its invariant inside a composite; the tree is open recursion (above). R1's structure
  sizes no longer matter.
- §4.5: `comp-exists` does not disappear (a column-level frame, not a table-level one). Of `i10-task`'s overrides, the
  plumbing ones were `t12`, `retire-one` and `dispatch-raw` (3); four more were one-line wrappers of
  content lemmas; `start-raw` stays content like `new-run-of`. `i10-task`'s "7 leaf entries" are 3 sites:
  `bump` is a cell, `run-upd/kill` and `task-upd/result` are inside the overridden composites,
  `filter-world` is in `i10-task`'s own Rule R proof, which the tree does not cover.
- §3 (A): `i9-res` needs fields per (primitive, row function), not per call site.
- §2.5, §3 (A+): the path facts `i10-task` needs sit on composites, not on primitive leaves; a primitive leaf
  needs facts about its row function. "Contextual leaves" are contextual callees, of either kind.
- §5b's 24 sites: the "facts in scope" column counted case-split tokens; the elaborator shows 0–10
  hypotheses per site (above).

## 5d. Stage 3, continued: `i9-res` on the tree, and why `i8-closed` needs per-part contexts

**Result.** `i9-res` goes through the tree (`spindel.v2.inv.i9-res`): its 4 overrides, 4 patches and the
`lcopy!` of `step-well-formed` are gone; its table has 2 site entries and 3 own-proof entries, and all 187
names the copier generated for it keep their statements (185 restated or aliased, 2 hand lemmas).
`i8-closed` was not converted: the tree's shared contexts cannot carry it (below), and the change it needs is a
redesign of how contexts are declared, which this stage was told not to start.

### `i9-res` before and after

| | before (copier) | after (tree) |
|---|---|---|
| resource updates | patches of `well-formed-res-cancel` and `well-formed-t18-resource-fire` (`i9-res-res-upd-q` at the call) | 2 site entries: `resource-upd` at `res-cancel-row` and at `res-set-phase rp-fired` |
| own proofs | overrides of `cancel-run-local`, `ack-raw`, `arm-park` | `:over` entries: `i9-res-cancel-run-local`, `i9-res-ack-raw-hand` (the old name an alias), `i9-res-arm-park` |
| plumbing | override of `well-formed-t17-arm`; patches of `well-formed-job-apply`, `well-formed-transition` | none in `i9-res`; in the tree: 1 context (`arm-park`), 1 own context (`t17`: transition's guard `arm-refused`), 2 passes |
| generated | 187 copies (`lcopy!` of `well-formed-cancel-debtor`, `step-well-formed`) | 184 restatements, 1 alias, 2 hand lemmas |

The estimate of §5c held: 2 sites, 3 own proofs, 2 contexts, 1 pass (2 counting the pass into `arm-park`).
`i9-res-cancel-run-local` and `i9-res-arm-park` are three-line adapters: the content is `i9-res-cancel-mid` and
`i9-res-arm-hand`, followed by the generic debtor side and the generic park.

### The tree extension: own contexts are opt-in (superseded by §5e)

§5c's `:own?` contexts (`t12`, `dispatch-raw`) were global: every part restated those nodes with the
context premise. `i10-task` needed that; `i9-res` did not, and its `i9-res-t12-complete` and `i9-res-dispatch-raw` would have
changed statement. The same held for the new `t17` context: `i10-task`'s `i10-task-t17-arm` would have gained `i9-res`'s
premise. So:

- An own context names its facts (`:own [hc]`): the tree takes x's base proof, adds the premises to
  its statement and the names to its first `intros`, and the passes do the rest. `t12`'s hand-written
  source is gone this way (its pass uses a new one-line lemma `tag-ok-res`); `dispatch-raw` keeps its
  source (it carries `comp-has` through three edits with `comp-exists`).
- A part takes x's own context only when it needs it: `takes?` is true when one of x's callees takes a
  context in that part (an overridden callee that is not `:bare`, or an own context taken in turn).
  `i10-task` takes `t12` and `dispatch-raw`, `i9-res` takes `t17`, neither takes the other's.
- Every other part keeps x's bare statement, proved from `pres-<x>-bare`: x's base proof over Q, every
  callee bare. Callers that pass the context get the part's bare lemma through `ctx-<x>` (dropped), now
  generated for own contexts as well.

Three own nodes give three `pres-<x>-bare` and three more `ctx-` lemmas. Every converted part
(`no-dep-edges-of`, `markers-gone`, `edge-kind-kept`, `edge-debtor-kept`, `mark-targets-dep`, `run-gone`, `i10-task`, `i9-res`) goes through with identical statements.

### `i8-closed`: what the shared contexts cannot carry

`tree/contexts` holds one premise list per callee, in base vocabulary, and every part that overrides the
callee takes all of it. Read against `i8-closed`'s 51 overrides and the bundles still to come (`i7-idle`, `comp-facts`), that
model breaks in two ways:

1. **Parts need different facts at the same callee.** A part's own lemma must take exactly the shared
   list, so the second part to need a different fact changes the first part's lemma:

   | callee | `i10-task` | `i9-res` | `i8-closed` | `i7-idle` | `comp-facts` |
   |---|---|---|---|---|---|
   | `complete-raw` | row, tag not none | | no activation of the run, `acts-parked` | | `comp-facts-cce`/`comp-facts-u1` |
   | `arm-park` | | row, not unwinding | row, alive | row, alive | |
   | `dispatch-raw` (own) | `comp-has` | | `acts-parked`, `comp-has` | `awake` | |
   | `t12` (own) | `res-tag-ok` | | `acts-parked` | | |
   | `new-run-of` | `comp-has` | | owner not closed (`tclosed`) | | |

   Taking the union does not help: `i10-task-complete-raw-hand` would have to take `acts-parked`, and the opt-in of own
   contexts is per node, not per fact (`t12`: `i10-task` takes `res-tag-ok`, `i8-closed` takes `acts-parked`).
2. **The facts are in the part's vocabulary.** `i8-closed`'s owner facts are `sclosed`/`tclosed` over its key
   lists, `comp-facts`'s are `comp-facts-cce`, the await revival needs `i8-closed`'s helper bundle `awaiting-run-alive`; all are defined after
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

Three smaller extensions `i8-closed` needs in any design:

- **Gated continuations.** transition calls `require-root-open w b o h (well-formed-t1-create-source ...)`; `i8-closed`'s T1/T-create-link/
  T-append need the gate's fact `root-open-if b w`, so the continuation becomes `fn [hc0] ...` and
  `require-root-open`'s premise `inv (:world o)` becomes `root-open-if b w -> inv (:world o)` (today `g8-ga-calls`
  and the `well-formed-require-root-open` override). A pass that wraps an argument, not one that inserts one.
- **Composite sites.** `serve-or` takes a row function `keep` and its key proof; `i8-closed` needs `i8-closed-source-key (keep s)
  = i8-closed-source-key s` (today an extra argument of the copier at `serve-or`). The tree would dispatch `serve-or`
  per `keep` like an update primitive, and `source-upd`/`scope-upd` as well (the `g8-patch` rows:
  consume, close, detach; `stream-set-tail (:next-id w)` needs `site-gen`).
- **Contexts on sites.** The revival sites (`run-upd` at `run-tick-park` and `run-park-row`) need
  "every row with this id is alive", passed from `take-park`/`park-if` through the edits before them
  (as §5c planned).

R4 (companions) was not reached, and is not what stops `i8-closed`. Carrying `acts-parked` would be an own context on
the 17 nodes between raw and the cascade (`raw`, `host-guarded-transition`, `transition`, `t14`, `t14-host-cancel`, `t16`,
`t-close-scope`, `t15-resource-ack`, `t-slice-exit`, `t21-release-world`, `t12`, `t11`, `dispatch-raw`,
`cancel-pred`, `complete-raw`, `retire-one`, `t28-retire-local`), passed with `acts-parked`'s own lemmas
(`acts-parked-ack-raw` at T15, `acts-parked-run-upd-free` at T-slice-exit, `acts-parked-retire-pre`, `acts-parked-host-guarded-transition`, ...): the
mechanism `i9-res`'s `t17` uses, with `t28-retire-local` (both parts through one fold, `nat-fold-pres2`) and
`t-slice-exit` (three steps to the run's freedom) as sources. Not tried: in the shared table it collides
with `i10-task`'s own contexts at `t12` and `dispatch-raw` (1. above) before the first pass is checked.

The I8 table under per-part contexts would show the model-only guard `cur-closed` (P10) as one row:

```clojure
:own '{well-formed-t4-spawn [hcc (= (cur-closed w st) false)] ...}   ; transition's create-in-scope-refused guard; P10: a run's current scope is open
```

### Revised plan

| step | what | estimate |
|---|---|---|
| per-part contexts | contexts, own contexts and passes in `part!`; per-part path variants; `i10-task`'s and `i9-res`'s contexts move into their tables (no statement changes); gated continuations, composite sites, `source-upd`/`scope-upd` sites, site contexts | 3–4 days |
| `i8-closed` | about 12 contexts, 20 own-context rows (`acts-parked` 17, `cur-closed`, `root-open-if`, `awaiting-run-alive`), 35 passes, 8 sites, 2–3 own proofs (the cascade with its ghost, `t-detach`), Rule R by hand as now | 3–4 days |
| `marks-waiting` | 13 "not a computation id" facts as contexts (base vocabulary: `comp-has` is false); companions `comp-facts`, `i7-idle`, `tombs-dormant`, `i10-current`, `i14-ordered` as own contexts | 3–4 days |
| `i7-idle`, `comp-facts` | 29 and 22 overrides, mostly the same transitions as `i8-closed` (parks, dispatch, await, T12) with their own facts; `comp-facts`'s `cmono` frames as sites | 2 days each |

About 2½–3 weeks, as §5c's total, with the redesign first instead of per-part workarounds.

### Gate (`i9-res`)

- **Statements** (name-independent fingerprints of every theorem, f87fb4f against this stage): 16,691
  identical, none missing. 2 changed, both internals of the tree: `pres-transition` (its call of `t17` now
  passes transition's guard) and `pres-t17-arm` (it takes the guard and passes it to `arm-park`); nothing outside
  the tree's restatements references a `pres-` lemma. 8 new: `pres-t12-bare`, `pres-t17-bare`,
  `pres-dispatch-raw-bare`, `ctx-t12`, `ctx-t17`, `ctx-dispatch-raw`, `ctx-arm-park`, `tag-ok-res`.
  Every old `i9-res` and `i10-task` name has its old statement (`i9-res-t12-complete` and `i9-res-dispatch-raw` stay bare,
  `i9-res-t17-arm` keeps `arm-refused`). `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`,
  `step-chain`, `mv-refinement` unchanged; `inv` is a definition, its source untouched.
- **Load**, two runs back to back (one JVM each, 1 GB): the namespaces this stage touches took 64.7 s
  before and 64.7 s after: `inv.copier` 14.6 → 8.2 s (i9-res's copies gone), `pres.tree` 13.2 → 14.5 s
  (3 bare lemmas, 4 context defaults), `inv.i9-res` 0.8 s, `inv.i10-task` 0.9 → 1.0 s, `inv.base`
  36.1 → 40.1 s. The untouched namespaces went 392.5 → 572.5 s (host load); the whole model 457 → 637 s.
- **Suite**: `clojure -M:test`, 290 tests, 208,315 assertions, 0 failures, 0 errors (the oracle on
  samples 1–60 included; two new tree tests: own contexts are opt-in, i9-res is not copied).

### What the earlier sections got wrong

- §5c: contexts as one shared list per callee. It held for `i10-task` and `i9-res` (they share `r ∈ runs` at
  `cancel-run-local`), but not once two parts need different facts at the same callee, or facts in their
  own vocabulary (above). Own contexts as global premises changed other parts' statements.
- §4.6: "the creation overrides become two leaf entries whose path condition carries the guard": the
  guards sit on transitions (own contexts at T1, T4, transition's `require-root-open`), and reach the insert composites
  through about ten passes; not two entries.
- §5c, R4: the first obstacle for companions is where they are declared, before how they are carried.

## 5e. Stage 3: contexts belong to the part

**Result.** §5d's proposal, implemented: the tree has no shared `contexts` or `passes` tables any more.
A part's table declares the facts it takes from the path and the terms that pass them; the tree
generates the part's own generic lemma `pres-<x>@<part>` for the nodes on those paths, and every other
node uses the shared `pres-<x>`, which is now the base proof over Q with bare callees. `i10-task` and `i9-res`
moved their facts into their tables with no statement changing. The opt-in logic of §5d (`takes?`,
`pres-<x>-bare`, the `ctx-<x>` defaults) is gone with the shared table.

### The table

| key | what | `i10-task` | `i9-res` |
|---|---|---|---|
| `:ctx` | x or [p F] -> facts the part's own proof (or site entry) takes there | 5 | 2 |
| `:own` | x -> facts a generated node takes from above, named | `t12` (refusal guard), `dispatch-raw` (the computation exists) | `t17` (`arm-refused`) |
| `:pass` | caller -> callee -> the terms passed, over the caller's locals | 6 callers, 7 terms | 3 callers |
| `:src` | x -> the part's proof of x (base vocabulary) | `dispatch-raw` (carries `comp-has` with `comp-exists`) | |
| `:gates` | a gate node whose continuation takes its fact | | |

A reader of `inv.i10-task` or `inv.i9-res` now sees every fact the part takes from the path, with its
reason, in the part's file. The variants are few: `i10-task` 7 (`job-apply`, `transition`, `t12`, `retire-one`, `t5`,
`t11`, `dispatch-raw`), `i9-res` 3 (`job-apply`, `transition`, `t17`). `transition`'s variant (the item dispatcher) is
the largest; it is generated per part that passes a guard into a transition.

A missing pass is an error at restatement that names the caller, the callee and the part ("x calls c,
which takes facts in this part: give x a :pass for it").

### Extensions for `i8-closed`

- **Gates** (`tree/gates`): `require-root-open`'s continuation premise becomes `root-open-if b w -> inv (:world o)`
  for a part that takes the gate (`:gates {well-formed-require-root-open hc0}`); the gated proof is one line longer than
  the base one, and every call's continuation in that part's variants becomes `(fn [hc0 :- _] ...)`, so
  the part's passes into T1, T-create-link, T-link-realize and T-append can use `hc0`. Checked on a toy
  part in `tree_test` (`transition`'s gated variant elaborates for any Q).
- **More sites**: `source-upd`, `scope-upd` and `serve-or` (at its `keep`) are dispatched per row
  function, like `run-upd`. A part's default at a composite site is its restated lemma of the composite;
  with a `:sites` entry for every row function (`i8-closed`: `i8-closed-source-key` kept) the composite is not restated at all.
  `link-demand-raw`'s row function, left to unification by the base proof, is named in `tree/sources`.
- **Contexts on sites**: `:ctx {[p F] [facts]}` adds premises to that site's hypothesis in the part's
  variants (its `:sites` entry takes them as `h0..`), and callers pass them like any other.

### Gate (PR A)

- **Statements** (name-independent fingerprints, f87fb4f against this stage): 16,663 identical. 25
  changed, all shared generic lemmas `pres-*` (now bare, or calling the new sites); 5 missing, the
  `ctx-*` defaults of the shared contexts of §5c; 11 new: the part lemmas (`pres-x@i10-task`: 7, `pres-x@i9-res`:
  3) and `tag-ok-res`. Nothing outside the tree's restatements references a `pres-` or `ctx-` lemma
  (#314's `pres-*-bare` and the other `ctx-*` go too). Every name of `no-dep-edges-of`, `markers-gone`, `edge-kind-kept`, `edge-debtor-kept`, `mark-targets-dep`,
  `run-gone`, `i10-task`, `i9-res` keeps its statement. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`,
  `l5-safety-total`, `step-chain`, `mv-refinement` unchanged.
- **Load**, back to back: the namespaces this stage touches took 79.6 s before and 104.0 s after:
  `inv.copier` 12.9 → 6.4 s, `pres.tree` 11.7 → 11.8 s, `inv.i10-task` 0.8 → 7.3 s and `inv.i9-res`
  6.7 s (each part now generates its own `transition`, the item dispatcher: about 6 s per part that passes a
  guard into a transition), `inv.base` 29.6 → 42.0 s, `inv.idle` 12.3 → 13.6 s, `inv.i1-runs` 10.6 →
  14.1 s. The untouched namespaces went 365 → 467 s (host load); the whole model 445 → 571 s. The
  per-part `transition` is the cost of moving the guards into the parts.
- **Suite**: `clojure -M:test`, 290 tests, 208,308 assertions, 0 failures, 0 errors (oracle samples 1–60
  included; the tree test checks the part lemmas, a gate on a toy part, and i10-task/i9-res).

## 5f. Stage 3: `i8-closed` on the tree

**Result.** `i8-closed` goes through the tree, on per-part contexts (§5e). Its 51 overrides, 3 patches
(`g8-patch` over every source, `g8-add-ga` on transition and host-guarded-transition) and 7 `lcopy!` calls are gone; `inv.i8`
Part H is its table. All `i8-closed` names keep their statements; one hand lemma that no longer has a caller
(`g8-take-park-o`) and the T11 key lemmas of the old dispatch override are deleted.

| | before (copier) | after (tree) |
|---|---|---|
| overrides / patches / `lcopy!` | 51 / 3 / 7 | 0 / 0 / 0 |
| own proofs (`:over`) | (overrides) | 7: the cascade (break, repair, ghost escape list, exit by P4), `add-run-scope`, `spawn-rows`, `stream-rows` (two inserts with different owners), `start-raw`, `new-run-of` (a computation's run), T13's retire fold (`nat-fold-pres2`, `i8-closed` with `acts-parked`) |
| sites | `g8-patch`, extra arguments | 12: a run dies (T12), is made parked (take, await: with a context), wakes; a task's owner changes (detach: with a context; Rule R; T14's cancel result); a source is consumed, closes, is orphaned; `serve-or` at its two `keep`s |
| `:ctx` / `:own` / `:pass` | (overrides) | 11 / 37 / 62 terms at 45 callers; `:gates` 1 (C0), `:src` 1 (T11's dispatch, `acts-parked` and `comp-exists`) |
| part lemmas `pres-x@i8-closed` | | 47 |

R4 worked as planned: `acts-parked` is an own fact of 17 nodes from raw to the cascades, passed with `acts-parked`'s own
lemmas (`acts-parked-ack-raw`, `acts-parked-run-upd-free`, `acts-parked-retire-pre`, `acts-parked-host-guarded-transition`, `acts-parked-zero-handles`, ...); one new
bridge lemma (`slice-exit-free`, the exiting run has no activation). The helper bundle `awaiting-run-alive` (the
awaiting run stays alive) is carried the same way through the await, with its copier lemmas.

The P10 guard is one group of rows in the table: transition's `create-in-scope-refused` refusal gives `cur-closed w st =
false` to T4 and T1, and T1 carries it to its two creations (four rows, one comment). Every other fact
`i8-closed` takes is a projection of a transition's own guard, by a one-line lemma next to the table
(`root-ok-of-true`, `i8-closed-source-ok-new-source`, `i8-closed-source-ok-link-open`, `detach-open`, `await-ok-normal`, `take-park-ok`).

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
proofs kept as a template for the copier bundles `comp-facts` and `alive-run-latest`, which rename them (`gd-from-g8`,
`ar-from-g8`); they go when those parts move to the tree.

**Passes and own facts.** The table has 74 pass terms (at 62 caller-callee entries) and 37 own rows.

- 30 of the 74 terms forward a fact the caller declared itself, by its name (`hga` 19 times, `hc0` 5,
  `hcc` 2, `hro`, `ho`, `hk`, `hal`). 25 of them have the same statement at the call (the callee's
  fact, its binders replaced by the call's arguments, is the caller's fact); 5 more need unification
  (the 4 gated `hc0`, where the call leaves the gate's flag to unification) or a definitional step
  (`hal` at `arm-park`, `run-alive` of the armed run).
- 44 carry a real fact: a guard projection (`bool-and-right`, `root-ok-true`, `detach-open`, ...), a
  lookup (`tok-facts`, `find-comp-has`), or a lemma that carries a fact through edits (`acts-parked-ack-raw`,
  `take-park-ok`, the `awaiting-run-alive` chain).
- 12 of the 37 own rows only forward (`host-guarded-transition`, `transition`, `t14`, `t14-host-cancel`, `t16`, `t-close-scope`,
  `t11`, `cancel-pred`, `cancel-losers`, `dispatch-raw`, `t-link-realize`, `park-if`); the other 25 use
  the fact in a real term.

**Proposed inference rule (not implemented).** When node x calls c, c takes fact P in the part, and x
has no :pass for c: if every argument of the call is a binder of x, x takes P (its binders renamed to
the call's arguments) as an own fact under a fresh name and passes it; its callers repeat. An
explicit :pass (a real term) stops the propagation. A declared own fact with the same statement is
reused, not added again. This is H made automatic for the forwarding case, with no local context
needed: the facts are premises of x's statement, not hypotheses of its proof. Under it, `i8-closed`'s table
would drop the 25 syntactic forwards (30 with unification at the gate) and the 12 forwarding own rows:
74 → 44–49 pass terms, 37 → 25 own rows, about 142 → 112 code lines. The `acts-parked` chain would read as
four rows: the cascade takes `acts-parked`, `raw` takes it, and T15, T-slice-exit, T-release-world, T12,
complete-raw and retire-one say how it is carried; the 12 nodes between them would be inferred.

**Load.** In PR A (§5e) the touched namespaces went 79.6 → 104.0 s, while the untouched ones went
365 → 467 s (host load, +28%); at that factor the touched ones would have been about 102 s. The part
that is not host load is `transition`: a part that passes a guard into a transition needs its own variant of
`transition`, the item dispatcher (49 items, the guard checks and a `simp only` per branch), and that
variant costs about 6 s, once per part (`i10-task`, `i9-res`; `i8-closed` adds one, gated). The variants cannot share
the shared `pres-transition`: their passes use the hypotheses transition's branches introduce (`hc`, `ht`), which
exist only inside its proof. They could share work if `transition`'s proof were split per item (one lemma
per branch, `transition` a dispatch over them): a part's variant would then regenerate only the branches it
passes into (`i9-res`: one, `i10-task`: one, `i8-closed`: about 15), and the rest would stay shared. That is a change to
the base proof in `engine.clj`, not done here.

### Gate (`i8-closed`)

- **Statements** (name-independent fingerprints): against PR A (§5e), 16,686 identical; 2 changed, both
  shared generic lemmas (`pres-add-run-scope`, `pres-t-open-scope`: `scope-ins-fresh` is now a site);
  11 missing, the deleted helpers of the old T11 and take overrides (`g8-take-park-o`, `comp-has-find8`,
  `tasks-sdel-fold`, `t8ks-retire-with`, `t8ks-close-with`, `t8ks-job`, `t8ks-cascade`,
  `t8ks-cancel-pred`, `kw8-consume-entry`, `kw8-cut-suffix`, `tclosed-kw8`; nothing references them);
  57 new: 47 `pres-x@i8-closed`, 7 bridge lemmas, `i8-closed-new-run-of-comp`, `i8-closed-cancel-losers` (restated; the old
  raw override never copied it) and `i8-closed-run-cascade` (the copier's name of the overridden cascade, an
  alias). Against f87fb4f every surviving name is identical (16,650; the 27 changed are `pres-*`).
  `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-chain`,
  `mv-refinement` unchanged.
- **Load**, back to back against PR A: touched namespaces 112.6 → 117.0 s: `inv.i8` 11.1 → 15.1 s (47
  part lemmas, `transition`'s gated variant among them, instead of 51 overrides and a patched copy),
  `pres.tree` 11.5 → 11.9 s, `inv.comp-facts` 10.3 → 11.1 s, `inv.alive-runs` 8.1 → 8.9 s, the rest
  within ±1 s. Untouched 369 → 344 s (host load); whole model 482 → 461 s.
- **Suite**: `clojure -M:test`, 291 tests, 208,317 assertions, 0 failures, 0 errors (oracle samples 1–60
  included; the tree test also checks that `i8-closed` is not copied and that `acts-parked` reaches the cascades).
- **Found by the gate**: `comp-facts` and `alive-run-latest` (copier bundles) built six of their overrides by renaming `i8-closed`'s
  (`gd-from-g8`, `ar-from-g8`). Those six forms are kept, unchanged, as `park-overrides` at the end of
  `inv.i8`, and both read them from there.

## 5g. Stage 3: forwarding is inferred

**Result.** The rule proposed in §5f is in the tree (`tree/infer`): when node x calls c, c takes fact P in
the part, x has no :pass for c, and every argument of the call that P mentions is a binder of x, then x
takes P (with the call's arguments) under a fresh name, or reuses its own fact with that statement, and
passes it; x's callers repeat, to a fixpoint. An explicit :pass stops it, and so does a call whose
arguments are not x's binders (an intermediate world): there the part writes the term.

| `i8-closed`'s table | before | after |
|---|---|---|
| own rows | 37 | 27 (10 inferred: `transition`, `host-guarded-transition`, `t14`, `t14-host-cancel`, `t16`, `t-close-scope`, `cancel-pred`, `cancel-losers`, `park-if`, `t-link-realize`) |
| pass entries / terms | 62 / 74 | 42 / 54 |
| code lines of `part!` | 142 | 121 (14 comment lines, 27 inline reasons, unchanged) |

`i10-task` and `i9-res` lose no rows: their passes are real terms, and `i9-res`'s `transition -> t17 [hc]` forwards transition's
local guard (a `cases` hypothesis), not a declared fact, which the rule does not see. The 10 forwards
left in `i8-closed`'s table are the gated `hc0` (the gate's flag is left to unification by transition's call), `hal`
at `arm-park` (a definitional step), and terms in entries that also carry a real term (a pass entry is
written whole).

The `acts-parked` chain now reads as the facts that matter: the cascade takes `acts-parked` (:ctx), `raw` takes it, and
T15, T-slice-exit, T-release-world, T12, complete-raw, retire-one and T11's dispatch say how it is
carried; the 10 nodes between are inferred.

### Gate (forwarding)

- **Statements** (name-independent fingerprints, against `i8-closed` on the tree, §5f): 16,745 identical, none
  changed, missing or new. The inferred own facts and passes are the declared ones they replace, so
  every part lemma keeps its statement. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`,
  `l5-safety-total`, `step-chain`, `mv-refinement` unchanged.
- **Load**, back to back: touched namespaces 41.6 → 42.5 s (`pres.tree` 11.3 → 10.4 s, `inv.i8` 17.4 →
  19.6 s, `inv.i10-task` 6.8 → 6.4 s, `inv.i9-res` 6.1 s); the inference runs once per part. Untouched
  472 → 528 s (host load: another gate ran alongside the second measure); whole model 513 → 570 s.
- **Suite**: `clojure -M:test`, 291 tests, 208,319 assertions, 0 failures, 0 errors (the tree test also
  checks that `transition` forwards `acts-parked` by inference, not by a declared row).

## 5h. Stage 3: transition is cut by item

**Result.** `transition`, the item dispatcher, was the largest part lemma: a part that passed one guard into
one transition (`i10-task`: T12's refusal guard; `i9-res`: T17's `arm-refused`; `i8-closed`: the create-in-scope-refused and C0 guards)
got its own copy of the whole 49-way `cases`. The tree now cuts transition's base proof by item
(`tree/raw0-split`): one lemma per item, `raw0-<item>-inv`, whose proof is that item's branch (found by
counting the goals its tactics open and close; `rename_i`'s names become the item's fields), each
checked for `well-formed`; `well-formed-transition` is proved by dispatching to them (`tree/sources`). The base proof
in the model is unchanged and still the one a reader reads; the branch lemmas are generated.

A part's pass into a transition is now written at the branch (`well-formed-transition-complete {well-formed-t12-complete ...}`), and
the part gets its own lemma for that branch only:

| part | before | after |
|---|---|---|
| `i10-task` | `pres-transition@i10-task` (49 branches) | `pres-transition-complete@i10-task`; the dispatcher is shared |
| `i9-res` | `pres-transition@i9-res` | `pres-transition-arm@i9-res`; the dispatcher is shared |
| `i8-closed` | `pres-transition@i8-closed` | `pres-transition@i8-closed` (it forwards `acts-parked` to every branch, inferred) and 15 branch lemmas, the ones that call T1, T4, T-create-link, T-append, T-link-realize (the guards) or a cascade (`acts-parked`) |

### Gate (transition split)

- **Statements** (name-independent fingerprints, against §5g): 16,741 identical; 2 changed, both
  generic lemmas of the tree (`pres-transition`, `pres-transition@i8-closed`: their premises are now the branch lemmas'
  hypotheses, one per item, instead of the transitions'); 2 missing, `pres-transition@i10-task` and `pres-transition@i9-res`
  (the dispatcher is shared now); 262 new: the 49 `raw0-<item>-inv`, their 49 generic lemmas
  `pres-raw0-<item>`, 17 branch part lemmas (`i8-closed` 15, `i10-task` 1, `i9-res` 1), and the copier's 147
  restatements of the branches (`raw0-<item>-g8`, `-gl`, `-g9`). `inv-step`, `reach-inv`,
  `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-chain`, `mv-refinement` unchanged.
- **Load**, back to back (the first measure ran beside another gate's suite, so compare the parts
  with §5g's second measure as well): `inv.i10-task` 13.5 → 1.2 s (§5g: 6.4 s) and `inv.i9-res` 9.2 →
  0.9 s (§5g: 6.1 s), the cost of a whole dispatcher per part gone; `inv.i8` 16.5 → 11.4 s (§5g:
  19.6 s); `pres.tree` 19.3 → 9.5 s (§5g: 10.4 s; the 49 branch checks take about 1 s). Touched 58.6 →
  22.9 s; untouched 586 → 463 s (host load); whole model 645 → 486 s.
- **Suite**: `clojure -M:test`, 292 tests, 208,375 assertions, 0 failures, 0 errors (the tree test also
  checks the 49 branches, that `i10-task` and `i9-res` share the dispatcher, and that a gate-only part gets
  exactly the 6 gated branches). Rebased on #318, with oracle samples 1–62: 295 tests, 208,383 assertions, 0 failures, 0 errors.

## 5i. Stage 3: `i7-idle` and its companions on the tree; parameterised parts

**Result.** `i7-idle` (I7, the idle shape) and its companion bundles `comp-awake-owns-run awc awr` (the awaiting or
dispatched computation is awake, its run rows its own) and `alive-runs-listed kc0 kl0 kd0` (demote's cascade kills
every alive run of C) go through the tree. `no-dep-edges-of` already did. The copier's overrides, patches and
`lcopy!` calls for these bundles are gone; `inv.idle` Part C is `i7-idle`'s table.

**Parameterised parts.** A bundle with parameters is the part Q := (B p) for fixed p, as stage 1
found for the copier: every restated lemma takes p first and keeps it fixed from input to output
world. `restate!`, the sites and the cells already applied the parameters (`i8-closed`'s `x8s`); `comp-awake-owns-run` (2)
and `alive-runs-listed` (3) needed no other change. A parameter that changes inside a composite stays content:
`i7-idle`'s own proofs instantiate `comp-awake-owns-run` at `(:id c) 0` (T11, reactivation) or `(:of r) (:id r)` (the
await) and carry it with `comp-awake-owns-run`'s restated lemmas.

**Tree extensions.**
- **A computation edit is a site per row function** (`well-formed-comp-upd` is dispatched). Its arguments
  are the site's parameters (`site-gen`, named as the binders of the function's id lemma), so a part
  states each function once: `[well-formed-comp-upd (comp-start-row rid)]`. A row function left to
  unification (`_`) is read off its id lemma, as the copier's `fix-f` did (`tree/fill-rows`).
- **Inserts are sites per row or edge** (`well-formed-comp-ins-fresh`, `well-formed-insert-edge-fresh`,
  `well-formed-insert-edge-checked`). A bundle's extra argument that is rfl only at a concrete row (`i7-idle`'s
  `edge-new-ok` of a wait or observe edge, `:idle r = false` of a new computation) then
  elaborates. Three base proofs leave the inserted edge to unification; `tree/sources` names it
  (take-park, react-add, await-step).
- **`tree/site-keys` and `tree/row-sites`**: a part's sites for a family of row functions, one rule
  each (what the copier's patches did: `i7-idle`'s waking rows, its run ends; `comp-awake-owns-run`'s no-sleep rows;
  `alive-runs-listed`'s run ends).

| | before (copier) | after (tree) |
|---|---|---|
| `i7-idle`: overrides / patches / `lcopy!` | 29 / 2 (all sources; transition) / 3 | 0 / 0 / 0 |
| `comp-awake-owns-run`, `alive-runs-listed`: patches / `lcopy!` | 2 / 3 call sites (11 roots) | 0 / 0 |
| `i7-idle`'s own proofs (`:over`) | (overrides) | 21: the inserted dep edge (`edge-new-ok`), T7's tracking edge, T4/T5's new runs, reactivation, T11's dispatch, the T6 await, demote, normalization |
| `i7-idle`'s sites | `g7-patch` | 15 (8 waking computation rows, 4 run ends, resume; schedule/finalize and take: a run enters a slice or parks, with a context) |
| `:ctx` / `:own` / `:pass` | (overrides) | 5 / 2 / 9 callers |
| part lemmas `pres-x@i7-idle` | | 9 |

8 overrides become table rows: schedule and finalize (the found run's rows satisfy `rq`, `enter-q`),
take and arm (the run is a row and alive, as `i8-closed`), T-take, T17, T6 and T11 (the dispatched
computation is awake, `t11-dispatch-awake`). `transition`'s patch for T7 is one pass (`well-formed-transition-track {well-formed-t7-track
[hc]}`). `inv.alive-runs` (`alive-run-latest`) renamed three of `i7-idle`'s overrides; it now reads those proofs from
`inv.idle`'s source.

### Gate (`i7-idle`)

- **Statements** (name-independent fingerprints, against #320): 16,971 identical; 34 changed, all
  generic lemmas of the tree (27 shared `pres-*` and 7 `pres-*@i8-closed`: computation edits and inserts are
  now sites, so their hypotheses are per row function); none missing; 63 new: 49 `raw0-<item>-g7`
  (the copier restated `transition` whole), 9 `pres-x@i7-idle`, and 5 lemmas (`i7-idle-run-upd-q`, `rq-of-mem`,
  `enter-q`, `tick-park-q`, `t11-dispatch-awake`). Every `i7-idle`, `comp-awake-owns-run`, `alive-runs-listed`, `no-dep-edges-of` name keeps its statement;
  `await-ok-normal` moved from `inv.i8` to `inv.idle` unchanged. `inv-step`, `reach-inv`,
  `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-chain`, `mv-refinement` unchanged.
- **Load**, back to back: touched namespaces 47.8 → 49.7 s (`pres.tree` 11.4 → 16.8 s: more sites
  per generic lemma; `inv.idle` 13.6 → 14.6 s; `inv.i8` 14.2 → 10.4 s; `inv.alive-runs` 8.7 →
  7.8 s). Untouched 487 → 621 s and whole model 535 → 670 s: host load (another session's JVMs ran
  during the second measure).
- **Suite**: `clojure -M:test`, 296 tests, 208,399 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that `i7-idle`, `comp-awake-owns-run` and `alive-runs-listed` have no overrides or patches, the
  generic computation sites, and that T6, T-take, T17, T11, schedule and finalize are table rows).

## 5j. Stage 3: `comp-facts` and `dispatch-epoch-kept` on the tree

**Result.** `comp-facts` (computation facts: `C.run`, done-epoch) and its companion `dispatch-epoch-kept hkc hke` (T11's
predecessor keeps the epoch) go through the tree; `inv.comp-facts` Part C is `comp-facts`'s table. The
`gd-add-hyps` patches of `transition`, `host-guarded-transition`, `raw` and `t8-observe` are own facts: `i7-idle` and `i10-current` from
the step's input, declared at `raw`, `host-guarded-transition`, `transition` and `t8-observe`, and inferred at `transition`'s
branches (T6, T22, T8, T12). `comp-facts` no longer reads `inv.i8/park-overrides`: take, arm, T-take, T17
and the await's post take the same facts as in `i8-closed`'s table (the parked run is alive; `awaiting-run-alive` through
the wiring); `alive-run-latest` still reads the template.

| | before (copier) | after (tree) |
|---|---|---|
| `comp-facts`: overrides / patches / `lcopy!` | 23 (+6 from `i8-closed`'s template) / 5 / 3 | 0 / 0 / 0 |
| `dispatch-epoch-kept`: patches / `lcopy!` | 1 / 3 | 0 / 0 |
| `comp-facts`'s own proofs (`:over`) | (overrides) | 18: new runs (T4, T5, T11), T11's dispatch, T12's completion, reactivation, the await's pre-step and T6's raw step, the host await, T8 |
| `comp-facts`'s sites | `gd-patch` (every computation and run edit) | every computation and run site, by one rule each (monotone in `comp-facts`'s keys; by lemma where the row function changes them); parks with a context |
| `:ctx` / `:own` / `:pass` | (overrides) | 6 / 8 / 6 callers |
| part lemmas `pres-x@comp-facts` | | 16 |

### Gate (`comp-facts`)

- **Statements** (name-independent fingerprints, against #321): 17,068 identical, none changed or
  missing; 65 new: 49 `raw0-<item>-gd` and 16 `pres-x@comp-facts`. Every `comp-facts` and `dispatch-epoch-kept` name keeps its
  statement. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-chain`,
  `mv-refinement` unchanged.
- **Load**, back to back, one JVM at a time: touched namespaces 21.6 → 24.0 s (`inv.comp-facts` 8.4 →
  5.6 s; `pres.tree` 7.9 → 10.9 s and `inv.idle` 5.3 → 7.6 s, whose code this PR barely changes:
  host noise); untouched 325 → 345 s; whole model 346 → 369 s.
- **Suite**: `clojure -M:test`, 297 tests, 208,410 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that `comp-facts` and `dispatch-epoch-kept` have no overrides or patches and that `i7-idle` and
  `i10-current` reach `transition`'s branches).

## 5k. Stage 3: `marks-waiting` and `done-epoch-below` on the tree

**Result.** `marks-waiting hxm` (h-mark: a marked edge's debtor is strongly waiting, or exempt) and its
companion `done-epoch-below hsc` go through the tree; `inv.marks` Part C is `marks-waiting`'s table, `inv.marks-step`
keeps T2's and T12's own proofs. The `hmk-add-hyps` patches of `transition`, `host-guarded-transition` and `raw` are own
facts (`comp-facts`, `i7-idle`, `acts-parked`, `i10-current` from the step's input, inferred at `transition`'s branches). The five
names `inv.marks-step` redirected by hand (`marks-waiting-write-raw-x`, `marks-waiting-complete-raw-x`,
`marks-waiting-complete-body-x`, `marks-waiting-retire-one`, `marks-waiting-t28-retire-local-hand`) are `:over` entries; the copier's
names of four of them are now aliases.

"Not a computation id" (§5b) is a fact in the table, not 15 overrides: the source and link chain
(close, append, link-realize; close-raw, close-source(0), detach-source, realize-link,
link-next-raw, append-raw, deliver-res, fire-task-cancelled), resume and fill-slot take it as an
own fact, the transitions pass it from their source row (`hk-source-not-comp`), and each edit passes
it to the next through the edits that keep the computation rows (`hk-has-*`, or rfl at the edited
world). `t10-finalize-debtor` (its fuel loop is an induction) and `drop-act` take it as a context.

| | before (copier) | after (tree) |
|---|---|---|
| `marks-waiting`: overrides / hand renames / patches / `lcopy!` | 45 / 5 / 4 / 8 call sites (45 roots) | 0 / 0 / 0 / 0 |
| `done-epoch-below`: patches / `lcopy!` | 1 / 1 | 0 / 0 |
| `marks-waiting`'s own proofs (`:over`) | (overrides) | 35: the fire chain, finalization's loop, T7's track, revoke-roots, reactivation, detach, T11's strong computation, T3's creation, T2, T12, the retire fold |
| `marks-waiting`'s sites | `hmk-patch` | every computation site, one rule (a waiting row stays waiting; by lemma where the row function changes the keys) |
| `:ctx` / `:own` / `:pass` | (overrides) | 8 / 14 / 13 callers |
| part lemmas `pres-x@marks-waiting` | | 24 |

### Gate (`marks-waiting`)

- **Statements** (name-independent fingerprints, against #322): 17,133 identical, none changed or
  missing; 77 new: 49 `raw0-<item>-hmk`, 24 `pres-x@marks-waiting`, and 4 aliases (`marks-waiting-write-raw`,
  `marks-waiting-complete-raw`, `marks-waiting-complete-body`, `marks-waiting-t28-retire-local`: the copier's names of the hand
  lemmas `inv.marks-step` redirected to). Every `marks-waiting` and `done-epoch-below` name keeps its statement, the 15
  former overrides among them. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`,
  `l5-safety-total`, `step-chain`, `mv-refinement` unchanged.
- **Load**, back to back, one JVM at a time: touched namespaces 19.6 → 18.3 s (`inv.marks` 9.5 →
  6.2 s, `inv.marks-step` 10.1 → 12.1 s: it now restates what the copier generated lazily); untouched
  359 → 450 s (host load: other sessions' JVMs); whole model 379 → 468 s.
- **Suite**: `clojure -M:test`, 298 tests, 208,426 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that `marks-waiting` and `done-epoch-below` have no overrides or patches and that the
  "not a computation id" chain is generated).

## 5l. Stage 4, group 1: `tombs-dormant`, `scope-parents-acyclic`, `i1-scopes` and `root-scope-reserved` on the tree

**Result.** Stage 4 moves the bundles still on the copier to the tree, group by group, and then
deletes the copier. Group 1 is the tombstone part `tombs-dormant` (`inv.tomb`) and the three scope parts:
`scope-parents-acyclic` (`inv.acyclic`), `i1-scopes` (`inv.i1-scopes`) and `root-scope-reserved` (`inv.i11`). No tree change was needed.

| | before (copier): overrides / patches / `lcopy!` | after (tree) |
|---|---|---|
| `tombs-dormant` | 24 (in two form lists, 4 call sites) / 4 (`gy-patch` over every source; `raw`, `host-guarded-transition`, `transition`) / 3 | 24 own proofs; sites by two rules (a run that ends or leaves its slice, a computation edit that clears the flag) and resume; `:ctx` 2, `:own` 4, `:pass` 1 |
| `scope-parents-acyclic` | 3 / 2 / 3 | 4 own proofs, `:ctx` 1, `:pass` 2 |
| `i1-scopes` | 3 / 2 / 2 | 5 own proofs (two were hand renames), `:ctx` 1, `:pass` 2 |
| `root-scope-reserved` | 3 / 0 / 3 | 3 own proofs |

- **`tombs-dormant`'s companion `i7-idle`** (the awaiting or tracking run is alive) is an own fact of `raw`, `host-guarded-transition`,
  `transition` and T7's branch, and a context of T7 and T6; T6's branch takes it by inference. T7 also
  takes `transition`'s guard (not in a cleanup slice), passed at the branch. That replaces the three
  `add-premise` patches.
- **"The parent is a scope"** (`i1-scopes`, `scope-parents-acyclic`): `add-run-scope` takes it as a context, and T5's start and
  T11's new run pass `rfl` (parent 0). That replaces the `add-hp` patches. `i1-scopes`'s hand renames of
  `remove-if-empty` and `add-run-scope` are `:over` entries.
- The part lemmas are few: `tombs-dormant` 5 (`raw`, `host-guarded-transition`, `transition`, and the branches of T6 and T7), `i1-scopes` and
  `scope-parents-acyclic` 2 each (`start-raw`, `new-run-of`), `root-scope-reserved` none.

**What the plan got wrong.** It counted `tombs-dormant` as 4 overrides: `inv.tomb` holds 24 override forms in
two lists and registers them in loops. All 24 are content (dep edges, new runs, parked runs, the
demotion's tombstone, normalization) and stay as own proofs.

### Gate (group 1)

- **Statements** (name-independent fingerprints, against #323): 17,210 identical, none changed or
  missing; 205 new: 196 `raw0-<item>-<part>` (49 per part; the copier restated `transition` whole) and 9
  part lemmas `pres-x@<part>`. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`,
  `l5-safety-total`, `step-chain`, `mv-refinement` unchanged.
- **Load**, back to back, one JVM at a time: touched namespaces 26.5 → 16.2 s (`inv.tomb` 7.4 →
  6.3 s, `inv.acyclic` 6.3 → 3.2 s, `inv.i1-scopes` 6.3 → 3.1 s, `inv.i11` 6.5 → 3.6 s); untouched
  394 → 529 s and whole model 421 → 545 s (host load: other sessions' JVMs during the second measure).
- **Suite**: `clojure -M:test`, 299 tests, 208,439 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that the
  four parts have no overrides or patches and where `tombs-dormant`, `i1-scopes` and `scope-parents-acyclic` take their facts).

## 5m. Stage 4, group 2: `marks-on-dep`, `refs-not-edges` and the companion `no-act-of-run` on the tree

**Result.** The first half of `inv.base`: `marks-on-dep` (marks sit on dep edges), `refs-not-edges` (edge-separated
ids: every stored reference is an existing non-edge row) and the companion `no-act-of-run nax` (no activation
names run `nax`) go through the tree. The companions `mark-targets-dep` and `edge-debtor-kept` already did (§5b).

| | before (copier): overrides / patches / `lcopy!` | after (tree) |
|---|---|---|
| `marks-on-dep` | 2 / 0 / 2 | 2 own proofs (T2's write and `mark-from`, both through `mark-targets-dep`) |
| `refs-not-edges` | 12 / 4 (`esb-patch` over every source; `job-apply`, `t5`, `t11`) / 2 | 12 own proofs; sites by two rules (a run row, a cleanup row whose stored refs only shrink); `:ctx` 5, `:pass` 3 |
| `no-act-of-run` | 0 / 0 / 2 | no table: every lemma is generated |

- **`refs-not-edges`'s three patches that passed a fact** are three `:pass` rows: `job-apply` passes "the run is
  a row" to T14's local part, T5 and T11 pass "the computation exists" to the start and the
  dispatch (the same facts as `i10-task`, §5c).
- **`esb-patch`** (run and cleanup edits whose stored refs shrink) is two site rules.
- **One of the 12 overrides was never checked**: `esb-cleanup-set-o`, a wrapper that the rename of
  `well-formed-cleanup-set` to the hand lemma `refs-not-edges-cleanup-set` made unreachable. The copier evaluates an
  override only when a copy needs it, so the name never existed in the environment. It is deleted;
  the hand lemma is the `:over` entry.

**Tree extension.** `well-formed-act-upd` and `well-formed-cleanup-upd` are dispatched per row function, like the
other update primitives. `no-act-of-run`'s (and `act-runs-alive`'s) extra argument on an activation edit, "the row function
keeps the activation's run", is `rfl` only at a concrete row function (`act-fill`,
`act-set-members`); `refs-not-edges` proves `cleanup-drop` by its own lemma. The plan listed the cleanup
dispatch under group 7 (`well-formed-cleanup-upd`'s extra argument in the completion parts); `refs-not-edges` needs it
already, as a site.

### Gate (group 2)

- **Statements** (name-independent fingerprints, against group 1): 17,409 identical; 6 changed, all
  generic lemmas of the tree (`pres-ack-raw`, `pres-await-post` and its `@i8-closed` and `@comp-facts`,
  `pres-fill-slot` and its `@marks-waiting`: activation and cleanup edits are now sites, so their hypotheses
  are per row function); none missing; 101 new: 98 `raw0-<item>-<part>` (`marks-on-dep`, `refs-not-edges`) and 3 part
  lemmas (`pres-job-apply@refs-not-edges`, `pres-t5-start@refs-not-edges`, `pres-t11-dispatch@refs-not-edges`). `inv-step`, `reach-inv`,
  `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-chain`, `mv-refinement` unchanged.
- **Load**, one JVM at a time. The base measure is group 1's second one, taken under host load, so
  the totals are not comparable: `inv.base` 49.4 → 21.5 s (27.0 s in group 1's first, quiet
  measure), `pres.tree` 7.3 → 11.9 s (9.1 s there); untouched 488 → 411 s, whole model 545 → 444 s.
- **Suite**: `clojure -M:test`, 300 tests, 208,451 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that `marks-on-dep`,
  `refs-not-edges` and `no-act-of-run` have no overrides or patches, the activation and cleanup sites, and where `refs-not-edges`
  takes its facts).

## 5n. Stage 4, group 3: `act-runs-alive` and `i5-seen` on the tree

**Result.** The second half of `inv.base`: `act-runs-alive` (every activation's run exists and is alive) and
`i5-seen` (an observe edge's seen is at most its debtor's version) go through the tree. `inv.base` has
no copier override, patch or `lcopy!` left.

| | before (copier): overrides / patches / `lcopy!` | after (tree) |
|---|---|---|
| `act-runs-alive` | 12 / 5 (`aha-patch` over every source; `job-apply`, `transition`, `raw`, `host-guarded-transition`) / 2 | 5 own proofs, 3 sites, `:ctx` 4, `:own` 5, `:pass` 7 callers; 12 part lemmas |
| `i5-seen` | 11 / 4 (`svb-patch` over every source; `react-add`, `take-park`, `settle-edge`) / 2 | 9 own proofs, sites by two rules and T8's observe edge, `:ctx` 4, `:pass` 3 callers; 4 part lemmas |

**Overrides that were plumbing are rows now.** 9 of the 23 overrides were the base proof with a
fact passed to one callee, and the tree generates them:

- `act-runs-alive`: T12 (`acts-parked` gives "the token's run is free"), `retire-one`, T6 and `await-raw`, T-take, T17
  and `arm-park` (the run is an alive row; the same pass terms as in `i8-closed`'s table). `await-raw`
  takes its facts by inference. The companion `acts-parked` is an own fact from `raw` down to T12, where
  the three `add-premise` patches were.
- `i5-seen`: `fire-edge` and `settle-edge` pass "the found edge is the world's" (`edge-debtor-kept-of-mem`);
  `fire-dep` takes it by inference.

The 14 own proofs left are content: an activation goes with its run or names an alive one (`act-runs-alive`);
a new or rewritten edge has seen its debtor's version (`i5-seen`).

**T8's observe edge** (`svb-patch`'s third rule) is a site with a context: the site takes "the new
edge has seen its debtor's version" and T8 passes `obs-slice-holder-ok`. The two patches that named an edge the
base proof leaves to unification (`react-add`, `take-park`) were already `tree/sources`.

**Tree changes.**
- `well-formed-edge-upd` is dispatched per row function (`i5-seen`'s extra argument, "the row function keeps
  the edge's key", is `rfl` only at a concrete one).
- A bug this exposed: a site's hypothesis is the primitive's statement with the row function
  substituted, and a variable bound inside the primitive's binder types (`forall [e :- EdgeRow]`
  in `well-formed-edge-upd`'s) captured the same name in the row function (`edge-rearm … (:debtor e)`).
  `site-binders` renames such bound variables apart.
- A row function's lemma in a site rule is written with `_` for its arguments (`hv-lemma`): the
  site's world binder is renamed in the entry, so an argument that mentions the caller's world
  (`stream-set-tail (:next-id w)`) must be left to unification.

### Gate (group 3)

- **Statements** (name-independent fingerprints, against group 2): 17,510 identical; 6 changed, all
  shared generic lemmas of the tree (`pres-await-step`, `pres-consume-entry`, `pres-dep-consumed`,
  `pres-edge-set-phase`, `pres-fire-observe`, `pres-track-raw`: an edge edit is now a site); none
  missing; 114 new: 98 `raw0-<item>-<part>` (`act-runs-alive`, `i5-seen`) and 16 part lemmas (`pres-x@act-runs-alive` 12,
  `pres-x@i5-seen` 4). Every `act-runs-alive` and `i5-seen` name keeps its statement, the 9 former plumbing overrides
  among them. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`,
  `step-chain`, `mv-refinement` unchanged.
- **Load**, one JVM at a time, against group 2's measure: `inv.base` 21.5 → 15.2 s (27.0 s before
  stage 4), `pres.tree` 11.9 → 10.7 s; untouched 411 → 435 s, whole model 444 → 461 s.
- **Suite**: `clojure -M:test`, 300 tests, 208,468 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that `act-runs-alive`
  and `i5-seen` have no overrides or patches, where they take their facts, and the five edge sites).

## 5o. Stage 4, group 4: `i10-current-exempt`, `i10-current-transport` and `i10-current` on the tree; part lemmas take the part's parameters

**Result.** I10's run part `i10-current-exempt gxz gkz` (one current run per computation; exempt computations and
runs), its transport companion `i10-current-transport` (four parameters, two of them predicates) and `i10-current` (`i10-current-exempt` at
empty exempt lists) go through the tree. `inv.i10` has no copier override, patch or `lcopy!` left.

| | before (copier): overrides / patches / `lcopy!` | after (tree) |
|---|---|---|
| `i10-current-exempt` | 17 / 7 (`g10-patch` over every source; the four one-job cascades, T11, T12) / 29 | 16 own proofs; sites by one rule (4 computation row functions) and 5 run and task rows; `:ctx` 9, `:pass` 7 callers; 7 part lemmas |
| `i10-current-transport` | 0 / 1 / 8 | 1 site (the epoch step) |
| `i10-current` | 1 / 1 / 1 | 1 own proof (T5's start), `:ctx` 1, `:pass` 1; 1 part lemma |

`retire-one` was the base proof with two facts passed and is generated. The other 16 own proofs
are content: the cascade under its job condition and every caller that establishes it, T4, T11,
T12, demotion and the normalization round.

**The job condition is a context.** `job-ok gxz gkz w j` (a cancel job's run is no current run of a
kept computation) is what `i10-current-exempt` takes at `job-apply` and the cascade. The four cascades of one
retire or close job (T16, T15, the slice exit, the world's release) and `retire-one` pass it by
computation (`Eq.refl true`), where four `casc-patch` patches were.

**Tree changes.**
- **Part lemmas take the part's parameters.** `i10-current-exempt`'s facts name its parameters (the exempt
  lists), and a part lemma `pres-x@<part>` was stated over Q only. The part lemmas of a
  parameterised part now take the parameters as binders after Q, and `restate!` passes them; the
  shared `pres-x` are untouched. This completes Q := (B p) of §5i: the part's facts are in the
  part's vocabulary, parameters included.
- **A cascade's job list is named** (`tree/sources`): the base proofs of the four one-job cascades
  and of `retire-one` leave the job list (and sometimes the world) to unification, and
  `Eq.refl true` does not elaborate against an unknown list. The same kind of source as a row
  function left to unification.

**`i10-current`.** Its lemmas for `transition`'s transitions stay the wrappers of `i10-current-exempt`'s at empty lists
(`wrap-g10r!`, unchanged names `<x>-g10-r`). The tree needs a rest part to instantiate Q, so
`i10-current-rest` is new: `i10-current-exempt-rest` at empty lists, and `i10-current w` unfolds to `gp i10-current-rest w`.

### Gate (group 4)

- **Statements** (name-independent fingerprints, against group 3): 17,539 identical; none missing;
  91 changed, all part lemmas of the three parameterised parts already on the tree, which now take
  the part's parameters after Q (`pres-x@i8-closed` 62, `pres-x@marks-waiting` 24, `pres-x@tombs-dormant` 5; nothing outside
  the tree names a part lemma); 58 new: 49 `raw0-<item>-g10r`, 8 part lemmas (`pres-x@i10-current-exempt` 7,
  `pres-t5-start@i10-current`) and the unfolding equation of `i10-current-rest`. Every `i10-current-exempt`, `i10-current-transport` and `i10-current` name
  keeps its statement. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`,
  `step-chain`, `mv-refinement` unchanged.
- **Load**, one JVM at a time, against group 3's measure: `inv.i10` 20.7 → 12.8 s, `pres.tree`
  10.7 → 10.2 s; untouched 412 → 381 s, whole model 461 → 423 s (the host's load moves the
  untouched figure by more than the change does).
- **Suite**: `clojure -M:test`, 301 tests, 208,484 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that
  `i10-current-exempt`, `i10-current-transport` and `i10-current` have no overrides or patches and that `i10-current-exempt`'s part lemmas take its lists).

## 5p. Stage 4, group 5a: `i5-dep-final`, `owner-count-at-most` and `i1-detached-closed` on the tree

**Result.** I5's part `i5-dep-final x5d` (`inv.i5`) and the two owner parts of `inv.i1-owners` (`owner-count-at-most`, the
owner count of normalization, and `i1-detached-closed`, the source owners) go through the tree. Neither namespace
has a copier override, patch or `lcopy!` left. Group 5 of the plan is cut in two: the run parts of
`inv.i1-runs` (`i1-runs-exempt`, `i1-runs`, `run-retirable`, `run-gone`) follow as 5b, because `i1-runs` reuses `i1-runs-exempt`'s lemmas at the
empty list, which the tree has no form for yet.

| | before (copier): overrides / patches / `lcopy!` | after (tree) |
|---|---|---|
| `i5-dep-final` | 21 / 4 / 2 | 20 own proofs, `:ctx` 3, `:pass` 3 callers; 4 part lemmas |
| `owner-count-at-most` | 0 / 2 (over every source) / 1 | 4 sites |
| `i1-detached-closed` | 7 / 2 (over every source) / 2 | 7 own proofs, 3 sites, `:ctx` 3, `:pass` 2 callers; 2 part lemmas |

- **`i5-dep-final`.** `fire-dep` and `fire-edge` were plumbing for the companion edge-debtor-kept (the fired edge is the
  world's), as in `i5-seen`, and are generated. The other 19 overrides are content.
- **One patch became an own proof.** `i5-dep-final`'s write takes the guard's source row as an extra binder
  (`i5-dep-final-write-raw … s`), so its statement is not the base statement with facts added, and T2's
  patch (pass the row and the two guard facts) has no table form. `i5-dep-final-t2-write` is written out: T2's
  base proof (7 lines) with that call. The name and statement are the copier's.
- **`owner-count-at-most` and `i1-detached-closed`.** The plan expected the helper symbols the patches renamed (`src-detach*`,
  `tcr*`, `src-close*`, …) to need `:src`. They are plain sites: each was a row lemma at one row
  function.

**Tree changes.** Three more callees are dispatched: `well-formed-source-ins-fresh` and
`well-formed-task-ins-fresh` per inserted row, `well-formed-edge-set-phase` per phase. `i5-dep-final` and `i1-detached-closed` take an
extra argument there that is `rfl` only at a concrete row or phase. `i8-closed` already took a fact at
every inserted source ("its owner is not closed"), keyed by the callee; such a `:ctx` or `:pass`
row keyed by a dispatched callee itself now holds at every site of it, and a site with facts and
no `:sites` entry gets the part's cell at the site's premises. `i8-closed`'s table is unchanged.

**Order.** The copier evaluated an override when first used; the tree restates eagerly, so an own
proof stands after everything its callees need: `i5-dep-final-serve-or` after `fire-edge`, `i5-dep-final-dispatch-raw`
after the cascade's lemmas.

### Gate (group 5a)

- **Statements** (name-independent fingerprints, against group 4): 17,669 identical; none missing;
  19 changed, all generic lemmas of the tree whose proof calls a newly dispatched callee (11 shared
  `pres-x`: `append-raw`, `consume-entry`, `create-link-in-run`, `create-source-in-run`, `fire-wait-act`,
  `invalidate`, `link-next-raw`, `spawn-rows`, `stream-rows`, `t-create-link-top`, `t1-top`; 6
  `pres-x@i8-closed` and 2 `pres-x@marks-waiting` among the same); 104 new: 98 `raw0-<item>-<part>` (`i5-dep-final`, `i1-detached-closed`)
  and 6 part lemmas (`pres-x@i5-dep-final` 4, `pres-x@i1-detached-closed` 2). Every `i5-dep-final`, `owner-count-at-most` and `i1-detached-closed` name keeps its
  statement. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-chain`,
  `mv-refinement` unchanged.
- **Load**, one JVM at a time, against group 4's measure: `inv.i5` 11.1 → 7.1 s, `inv.i1-owners`
  9.4 → 4.7 s, `pres.tree` 10.2 → 11.2 s. The untouched namespaces read 392 → 453 s in this run:
  the host was under load from another session, so the whole-model figure says nothing here.
- **Suite**: `clojure -M:test`, 302 tests, 208,500 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that `i5-dep-final`,
  `owner-count-at-most` and `i1-detached-closed` have no overrides or patches and where `i5-dep-final` and `i1-detached-closed` pass their facts).

## 5q. Stage 4, group 5b: the run parts `i1-runs-exempt`, `i1-runs`, `run-retirable` on the tree

**Result.** I1's run parts (`inv.i1-runs`) go through the tree: `i1-runs-exempt x1r` (resource owners and run
entities, with exempt runs), `i1-runs` (`i1-runs-exempt` at the empty list, the step's part) and the cascade
companion `run-retirable` (`run-gone` was on the tree already). The namespace has no copier override, patch or
`lcopy!` left.

| | before (copier): overrides / patches / `lcopy!` | after (tree) |
|---|---|---|
| `i1-runs-exempt` | 3 / 2 (over every source) / 4 | 3 own proofs, 4 sites, `:ctx` 2, `:pass` 1 caller; 1 part lemma |
| `i1-runs` | 5 / 7 (3 over every source; T12, `transition`, `host-guarded-transition`, `raw` for acts-parked) / 5 | 9 own proofs, 4 sites, `:ctx` 7, `:own` 4, `:pass` 4 callers; 9 part lemmas |
| `run-retirable` | 0 / 1 (over every source) / 1 | 2 sites |

`i1-runs`'s 9 own proofs are its 5 overrides and 4 hand lemmas the copier took as cells (`arm-raw`,
`ack-raw`, `complete-raw`, `retire-one`). The four patches that added the companion acts-parked as a
premise from `raw` down to T12 are four `:own` rows, as for `act-runs-alive` (§5n).

**Tree change: a part at fixed parameters.** `i1-runs` is `i1-runs-exempt []` and uses `i1-runs-exempt`'s lemmas: the copier
gave every cell `i1-runs` took from `i1-runs-exempt` the extra argument `(List.nil Nat)` in first position. The
tree refused an extra argument on a callee it does not dispatch. It now reads one in first
position as a parameter instantiation and passes the cell applied to it
(`(i1-runs-exempt-close-local (List.nil Nat))`). No wrapper theorems are needed.

**Follow-up, not done here.** `i10-current` is `i10-current-exempt [] []` and has a wrapper theorem per transition
(`wrap-g10r!`, names `<x>-g10-r`, §5o). The same mechanism could replace those wrappers with
`i10-current-exempt`'s lemmas at the two empty lists. That removes names other namespaces use, so it belongs to
the naming pass.

### Gate (group 5b)

- **Statements** (name-independent fingerprints, against group 5a): all 17,792 identical; none
  changed, none missing; 59 new: 49 `raw0-<item>-gr0` and 10 part lemmas (`pres-x@i1-runs` 9,
  `pres-job-apply@i1-runs-exempt`). `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`,
  `step-chain`, `mv-refinement` unchanged.
- **Load**, one JVM at a time, against group 5a's measure: `inv.i1-runs` 11.2 → 6.7 s, `pres.tree`
  11.2 → 8.6 s. The whole model read 476 → 340 s: group 5a's measure was taken under host load, so
  the untouched figure (454 → 324 s) is the host's, not the change's.
- **Suite**: `clojure -M:test`, 303 tests, 208,517 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that the
  four run parts have no overrides or patches and that `i1-runs`'s cells are `i1-runs-exempt`'s at the empty list).

## 5r. Stage 4, group 6: `open-scopes-have-runs-exempt`, `open-scopes-have-runs`, `i14-validity-raw`, `i14-validity-rule-r` and `l2-measure` on the tree

**Result.** The open-scopes parts (`completion.open-scopes`: `open-scopes-have-runs-exempt`, `open-scopes-have-runs`), I14's two parts
(`inv.i14`: `i14-validity-raw`, `i14-validity-rule-r`) and the measure bundle (`progress.measures`: `l2-measure`) go through the tree. None
of the three namespaces has a copier override, patch or `lcopy!` left.

| | before (copier): overrides / patches / `lcopy!` | after (tree) |
|---|---|---|
| `open-scopes-have-runs-exempt` | 0 / 0 / 2 | restated |
| `open-scopes-have-runs` | 5 / 1 / 2 | 5 own proofs, `:ctx` 1, `:pass` 1 caller; 1 part lemma |
| `i14-validity-raw` | 5 / 1 (`wake-patch` over every source) / 1 | 5 own proofs, sites by one rule (4 waking row functions) |
| `i14-validity-rule-r` | 0 / 0 / 4 | restated |
| `l2-measure` | 8 / 5 (one over every source) / 2 | 8 own proofs; sites by one rule (8 row functions) and the take's park; `:ctx` 4, `:own` 3, `:pass` 4 callers; 4 part lemmas |

- **`i14-validity-raw`'s `wake-patch` is a site rule**, as planned: a computation edit by a waking row function
  goes through `i14-validity-raw-comp-wake` with the row function's lemma `<f>-dom14`.
- **`l2-measure`'s added binders are own facts.** Three patches added the hypothesis "the parking run is
  not the tracked one" as a binder of `await-post`, `await-raw` and `take-park` and passed it down.
  They are three `:own` rows; a trailing binder and a premise before the inv premise are the same
  statement. The patch of `transition` (pass T17's guard) is a `:pass` row at `well-formed-transition-arm`.

**Tree change.** `well-formed-run-ins-fresh` is dispatched per inserted row: `l2-measure` takes an extra argument
there that is `rfl` at a concrete row. One shared lemma changes (`pres-add-run-scope`).

### Gate (group 6)

- **Statements** (name-independent fingerprints, against group 5b): 17,850 identical; none
  missing; 1 changed, the shared `pres-add-run-scope` (the inserted run row is a site); 152 new: 147
  `raw0-<item>-<part>` (`open-scopes-have-runs`, `i14-validity-raw`, `l2-measure`) and 5 part lemmas (`pres-x@l2-measure` 4, `pres-job-apply@open-scopes-have-runs`).
  Every `open-scopes-have-runs-exempt`, `open-scopes-have-runs`, `i14-validity-raw`, `i14-validity-rule-r` and `l2-measure` name keeps its statement. `inv-step`, `reach-inv`,
  `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-chain`, `mv-refinement` unchanged.
- **Load**, one JVM at a time, against group 5b's measure: `completion.open-scopes` 9.0 → 3.8 s,
  `inv.i14` 13.9 → 9.7 s, `progress.measures` 11.3 → 6.7 s, `pres.tree` 8.6 → 10.2 s. Untouched
  namespaces read 297 → 350 s (host load; the figure moves by this much between runs).
- **Suite**: `clojure -M:test`, 304 tests, 208,533 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that the
  five parts have no overrides or patches and where `l2-measure` takes its facts).

## 5s. Stage 4, group 7a: `stays-released`, `cleanup-runs-exist` and `task-unheld-scope-absent` on the tree

**Result.** Three of the completion parts go through the tree: `stays-released` (`completion.quiet`), `cleanup-runs-exist`
(`completion.quiet-world`) and `task-unheld-scope-absent` (`completion.stable`). `markers-gone` (`completion.drained`) was on
the tree already. Group 7 of the plan is cut in two: `host-roots-revoked` (`completion.quiet`) follows as 7b,
because its patches thread a premise (`world-released w = false`) through many nodes and add a
per-row-function argument at six primitives.

| | before (copier): overrides / patches / `lcopy!` | after (tree) |
|---|---|---|
| `stays-released` | 1 / 0 / 2 | 1 own proof |
| `cleanup-runs-exist` | 5 / 0 / 2 | 4 own proofs, `:ctx` 2 |
| `task-unheld-scope-absent` | 4 / 3 / 2 | 4 own proofs, 2 sites, `:ctx` 3, `:pass` 1 caller; 1 part lemma |

Nine of the ten overrides are content. The tenth, `cleanup-runs-exist`'s `gc-cleanup-set-x`, was never evaluated
(nothing reached it; the own proofs call the hand lemma `cleanup-runs-exist-cleanup-set`) and is deleted. `task-unheld-scope-absent`'s two patches at one call each are sites (the row lemmas
`task-unheld-scope-absent-task-tcr` and `task-unheld-scope-absent-task-tcl`); its patch of `transition` is a `:pass` row at `well-formed-transition-complete`.

### Gate (group 7a)

- **Statements** (name-independent fingerprints, against group 6): all 18,003 identical; none
  changed, none missing; 148 new: 147 `raw0-<item>-<part>` (`stays-released`, `cleanup-runs-exist`, `task-unheld-scope-absent`) and
  `pres-transition-complete@task-unheld-scope-absent`. `gc-cleanup-set-x` is not among the 18,003: the copier never evaluated
  it. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`, `step-chain`,
  `mv-refinement` unchanged.
- **Load**, one JVM at a time, against group 6's measure: `completion.quiet` 15.7 → 7.3 s (`host-roots-revoked` is
  still copied there), `completion.quiet-world` 10.0 → 3.6 s, `completion.stable` 8.4 → 1.7 s;
  untouched 345 → 359 s, whole model 380 → 372 s.
- **Suite**: `clojure -M:test`, 305 tests, 208,541 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that
  `stays-released`, `cleanup-runs-exist` and `task-unheld-scope-absent` have no overrides or patches).

## 5t. Stage 4, group 7b: `host-roots-revoked` on the tree

**Result.** `host-roots-revoked` (`completion.quiet`), the last completion part, goes through the tree.
`completion.quiet` has no copier override, patch or `lcopy!` left (876 → 860 lines).

| | before (copier) | after (tree) |
|---|---|---|
| overrides | 4 | 6 own proofs (the same 4; `host-roots-revoked-await-wire` and `host-roots-revoked-await-raw`, see below) |
| patches | 14 `gk-patch!` calls and 2 rules over every source (the premise `world-released w = false` in front of 27 nodes; `hz-patch` at the row edits) | sites: 11 row functions by one rule, the three creations; `:ctx` 9; `:own` 5; `:pass` 23 callers (15 of them transition arms) |
| bundle extra arguments | 34 (4 cells, 3 creations and 27 threaded nodes taking the local name `hr0`) | 4 (the cells) |
| `lcopy!` | 2 | restated |

- **The threaded premise is inferred.** The copier listed the 27 theorems between a transition arm and a
  creation (`gk-threaded`) and added the premise to each. The table states the fact once, at the
  three creations and at handle-new's three row edits (`:ctx`), and where it comes from (15 `:pass`
  rows at transition's arms). The tree's forwarding finds the nodes in between: 28 of the 33 own-fact
  nodes are inferred, and they are the copier's 27 plus the T8 and T22 chain.
- **The inserted edges are one fact.** Six patches each rewrote one call to pass "this edge is no
  host root" in a different form. In the table the two edge insertions take the fact
  `host-free w e` at every site (`:ctx`), and the six callers pass it (`:pass`).
- **`hz-patch` is a site rule**: a row edit by one of 11 functions goes to the cell with the
  function's proof that a zero count stays zero (or to the `-open` cell with the guard).

**What the plan got wrong.**
- *The premise order was not a problem.* The copier put the added premise first, the tree puts a
  fact just before the inv premise. No threaded node has another premise, so every statement is the
  same.
- *`well-formed-await-wire` cannot take an own fact.* Its statement is `forall acc, inv ... -> ...`, with no
  inv premise at the top, and the tree inserts a fact before the inv premise. `host-roots-revoked` therefore keeps
  `host-roots-revoked-await-wire` (the base induction with the fact in front, as the copier generated it) and its
  one caller `host-roots-revoked-await-raw` as own proofs: 12 lines that are the base proofs again. A tree rule "a
  statement with no top-level inv premise takes its facts in front" (in `insert-before-inv`,
  `with-own` and the position of a pass) would remove both; it is not done here.
- *Two nodes pass the guard by computation.* `well-formed-stream-rows` and `well-formed-append-raw` insert a row
  into an already edited world, so the fact at the creation is about that world and forwarding
  does not apply (the argument is not a binder). They take the guard of the world before as an own
  fact and pass it as it is; `world-released` of the edited world reduces to it.

No tree change.

### Gate (group 7b)

- **Statements** (name-independent fingerprints, against group 7a): all 18,151 identical; none
  changed, none missing; 99 new: 49 `raw0-<item>-gk` and 50 part lemmas `pres-x@host-roots-revoked` (the nodes that
  take or pass the guard, and the six that pass `host-free`). `inv-step`, `reach-inv`, `inv-empty`,
  `sys-reach-inv`, `l5-safety-total`, `step-chain`, `mv-refinement` unchanged.
- **Load**, one JVM at a time, against group 7a's measure. The host was loaded during this measure:
  untouched namespaces read 365 → 525 s (×1.44), `completion.quiet` 7.3 → 13.1 s (×1.8); alone in a
  REPL `completion.quiet` loads in 8.4 s, and in the next measure (§5u, a quieter host) in 7.4 s.
  So `host-roots-revoked` on the tree loads as fast as the copy did, not faster: 50 part lemmas and 49 transition
  branches replace 138 copied proofs.
- **Suite**: `clojure -M:test`, 306 tests, 208,554 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that `host-roots-revoked` has no overrides or patches, that the guard goes from
  transition's arm to the row, and that it stops at transition).

## 5u. Stage 4: the part definitions move to `pres.part` (before group 8)

**Why.** The three parts that are left before the members (`acts-parked` and `acts-parked-exempt` in `inv.acts`, `comp-exists` in
`inv.copier`) are defined in namespaces that load before the tree, because the tree required
`inv.copier`. It required it only for the machinery in its Part B: the base proof as data
(`source-theorems`), the bundle record (`mk-bundle`), the primitive cells (`prim!`), the names and
statements of a part's lemmas (`copy-name`, `copy-form`), the front end (`defpart`, `frame!`) and
the copier (`lcopy!`, `override!`, `patch!`). The tree uses no theorem of `inv.copier` or
`inv.acts`.

**What.** That machinery is now `spindel.v2.pres.part` (264 lines, moved unchanged;
`inv.copier` 2813 → 2584 lines). The tree requires `pres.part`. No theorem, bundle or function is
renamed; nothing else moves. The namespaces that call the machinery get one more require line
(36 files); twelve references to a private var, in seven files, change their namespace.

The plan's alternative was to move the lemmas instead: `acts-parked`/`acts-parked-exempt`'s copied lemmas and everything
after them out of `inv.acts` (about 1000 of its 1356 lines), and the same for `comp-exists` in
`inv.copier`. Moving the machinery is the smaller change, and stage 4's last step asks for this
namespace anyway. With it, `inv.acts` and `inv.copier` can load after the tree, so group 8
converts `acts-parked`, `acts-parked-exempt` and `comp-exists` where they are.

Generated theorems are now evaluated in `pres.part` instead of `inv.copier`. `pres.part` refers the
same model namespaces except `inv.acts` and `inv.copier`'s own content; no generated form needed
them.

### Gate (the move)

- **Statements** (name-independent fingerprints, against group 7b): all 18,250 identical; none
  changed, none missing, none new. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`,
  `l5-safety-total`, `step-chain`, `mv-refinement` unchanged.
- **Load**, one JVM at a time, against group 7b's measure (which ran on a loaded host): `inv.copier`
  8.9 → 9.9 s, `pres.tree` 13.7 → 12.3 s, `pres.part` 0.1 s; untouched 516 → 393 s, whole model
  538 → 415 s. The move changes no load time beyond the noise.
- **Suite**: `clojure -M:test`, 306 tests, 208,554 assertions, 0 failures, 0 errors (oracle samples
  1–62), the same counts as group 7b.

## 5v. Stage 4, group 8a: `acts-parked`, `acts-parked-exempt`, `comp-exists` and `awaiting-run-alive` on the tree

**Result.** With the part definitions in `pres.part` (§5u), `inv.acts` and `inv.copier` load after
the tree, and their parts are converted where they are: `acts-parked` and `acts-parked-exempt` (`inv.acts`), `comp-exists`
(`inv.copier`) and `awaiting-run-alive` (`inv.i8`, `i8-closed`'s companion). `inv.acts`' private copier, the first one
written and a duplicate of the shared machinery, is deleted (1356 → 1233 lines). `alive-run-latest`
(`inv.alive-runs`), the last part of the plan's group 8, follows as 8b.

| | before (copier) | after (tree) |
|---|---|---|
| `acts-parked` | 21 overrides (4 of them written once for `acts-parked` and `acts-parked-exempt`: `override-both!`), 3 `copy!` roots | 21 own proofs, no `:ctx`, `:own` or `:pass` |
| `acts-parked-exempt` | the same 4 overrides, 6 `copy!` roots | 4 own proofs, restated |
| `comp-exists` | 3 `lcopy!` | restated |
| `awaiting-run-alive` | 1 patch over every source (`ka-patch`), 3 `lcopy!` | 1 site (`[well-formed-run-upd run-wake]`), restated |

- **`acts-parked` needs no fact from the path.** Seven of its own proofs take a hypothesis (the resumed
  activation is its run's only one; the completing run has no activation; the parking run is in
  the table and holds the slice). Each is called only by other own proofs, which prove it on
  the spot, so the table has no `:ctx`, `:own` or `:pass` row and `acts-parked` has no part lemma.
- **The four proofs shared by `acts-parked` and `acts-parked-exempt`** stay written once, as templates (`$name`, `%G`:
  `pres.part/inst`), and are checked for both parts (`both!`).
- **Three copier calls in `inv.members.await-wire`** asked `inv.acts`' copier for lemmas `acts-parked-exempt`
  already had. They did nothing and are deleted.

**What the plan got wrong.** The plan expected `acts-parked`/`acts-parked-exempt` to need their lemmas moved to a later
namespace, and their "own private mini-copier" to need replacing by tree features. Neither: after
§5u the conversion is the standard recipe, and the load of `inv.acts` goes from 11.4 s to 2.7 s because the 138 copies for `acts-parked` become restatements.

No tree change.

### Gate (group 8a)

- **Statements** (name-independent fingerprints, against §5u): all 18,250 identical; none changed,
  none missing; 49 new, the `raw0-<item>-ga`. No part lemma: `acts-parked`, `acts-parked-exempt`, `comp-exists` and `awaiting-run-alive` use the
  shared `pres-x` only. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`, `l5-safety-total`,
  `step-chain`, `mv-refinement` unchanged.
- **Load**, one JVM at a time, against §5u's measure: `inv.acts` 11.4 → 2.7 s, `inv.copier`
  9.9 → 4.7 s, `inv.i8` 12.3 → 16.2 s, `inv.members.await-wire` 4.7 → 6.2 s; untouched 377 → 351 s,
  whole model 415 → 381 s.
- **Suite**: `clojure -M:test`, 307 tests, 208,587 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that the four parts have no overrides or patches and that `acts-parked`
  has no part lemma).

## 5w. Stage 4, group 8b: `alive-run-latest` on the tree; `i8-closed`'s park templates go

**Result.** `alive-run-latest` (`inv.alive-runs`: an alive run of a computation is its `C.run`) is a part of the
tree. With it the last reader of `inv.i8/park-overrides` is gone, and that map (`i8-closed`'s former
proofs of the parks and the await, kept as templates that `comp-facts` and `alive-run-latest` renamed into their own
vocabulary) is deleted: `inv.i8` 2066 → 1985 lines, `inv.alive-runs` 949 → 909.

| | before (copier) | after (tree) |
|---|---|---|
| overrides | 23: 14 written out, 6 renamed from `i8-closed`'s templates, 3 renamed from `i7-idle`'s source | 10 own proofs |
| patches | 1 over every source (`ar-patch`), 3 that add `i7-idle` and `acts-parked` to transition, host-guarded-transition, raw | 7 sites, 3 `:own` rows |
| `lcopy!` | 3 | restated |

- **Thirteen overrides were plumbing** and are rows now. `t13-retire-with-subtree` and `retire-run` only
  carried "the retired run is a row and dead" down to the clear: inferred from the clear's `:ctx`.
  `job-apply`, T5 and T11 only produced a fact from their own locals: one `:pass` each. `park-if`
  and `take-park` only chose the run edit's lemma: two sites with their `:ctx`. The six templates
  (take, arm, T17, T6, the await and its post) are the `:own` and `:pass` rows `i8-closed` and `comp-facts`
  already have for the same facts.
- **The three proofs renamed from `i7-idle`'s source are written out** (`alive-run-latest-normalize-round`,
  `alive-run-latest-normalize-loop`, `alive-run-latest-normalize`, 22 lines): a reader of `alive-run-latest` no longer needs `inv.idle`'s source
  and a renaming function to see them. They are not rows because the loop's induction carries
  `acts-alive` through idle's `round-bound`, which is an argument, not a forwarded fact.
- **raw0 hands each fact to one branch.** `i7-idle` is needed at T5 only (a startable computation has
  no alive run) and `acts-parked` at T11 only (the predecessor's cascade). `well-formed-transition`, `well-formed-host-guarded-transition` and
  `well-formed-raw` take both, in the copier's order, so their statements are the old ones; the T5 branch
  takes `i7-idle` and the T11 branch `acts-parked`, each inferred from its transition's `:own` row. `alive-run-latest` has its
  own lemma for those two branches and the dispatcher, and uses the shared one for the other 47.
- `ar-run-ins-NONE`, a deliberately missing cell name for fresh runs, is gone: every caller of
  that edit is one of `alive-run-latest`'s own proofs, and the tree reports a reached site without a cell itself.

**What the plan got wrong.** The scouting asked whether the tree lets transition pass a different fact to
each arm and expected that to need design. It does not: passes are keyed by callee, the arms are
separate callees since §5h, and forwarding infers both. It also expected the template proofs to
be written out as `alive-run-latest`'s own (about 60 lines); they are rows instead, as are seven more overrides the
scouting counted as content.

No tree change.

### Gate (group 8b)

- **Statements** (name-independent fingerprints, against §5v): all 18,299 identical; none changed,
  none missing; 67 new: the 49 `raw0-<item>-ar` and 18 part lemmas `pres-x@alive-run-latest` (raw, host-guarded-transition, transition
  and its T5 and T11 branches, T5, T11, job-apply, retire-run, t13-retire-with-subtree, park-if, take-park,
  arm-park, T-take, T17, T6, await-raw, await-post). Every `alive-run-latest` name keeps its statement, the 13
  former plumbing overrides among them. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`,
  `l5-safety-total`, `step-chain`, `mv-refinement` unchanged.
- **Load**, one JVM at a time, against §5v's measure: `inv.alive-runs` 14.3 → 6.1 s, `inv.i8`
  16.2 → 12.8 s; untouched 350 → 316 s, whole model 381 → 335 s (the host was quieter: untouched
  namespaces moved by up to ±8 s each).
- **Suite**: `clojure -M:test`, 308 tests, 208,595 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that `alive-run-latest` has no overrides or patches and that `i7-idle` and `acts-parked`
  reach exactly transition's T5 and T11 branches).
- Copier call forms left in `formal/src`: `lcopy!` 50, `override!` 6, `patch!` 2.

## 5x. Stage 4, group 9: the member parts `current-members`, `edge-kinds` and `members-round-frame` on the tree; no copier call is left

**Result.** The last three copier bundles, all in `inv.members`, are parts of the tree: `current-members xm`
(h-mem2, `inv.members.bundle`), `edge-kinds` (edge kinds, `inv.members.cascade`) and `members-round-frame` (the frame
bundle of the normalization pass, `inv.members.step`). After this no namespace calls `lcopy!`,
`override!` or `patch!`.

| | before (copier) | after (tree) |
|---|---|---|
| `current-members` | 1 patch over every source (`h3-patch2`, six rules), 3 overrides, 30 `lcopy!` forms (58 roots) | sites: the same six rules as rows of the table; 3 own proofs; 12 `restate!` |
| `edge-kinds` | 3 overrides, 2 `lcopy!` | 1 site; restated |
| `members-round-frame` | 1 patch over every source (`fb-patch`, three rules), 1 `lcopy!` | sites: three rules; restated |
| parts already on the tree (`i7-idle`, `act-runs-alive`, `comp-facts`, `alive-run-latest`, `marks-waiting`, `i10-task`, `comp-awake-owns-run`, `awaiting-run-alive`, and `edge-kinds` after its own namespace) | 16 `lcopy!` forms in the await namespaces, `react` and `raw` (45 calls) | deleted: each added nothing |

- **`edge-kinds`'s three overrides were one fact.** They re-proved react-add, await-step and take-park
  only to hand the inserted edge's kind to the insertion. For a constructor term that is `rfl` (the
  bundle's extra argument, which the tree applies at every insertion site by default); the await's
  edge depends on the dep test and needs the lemma `edge-kinds-await-edge`: one site.
- **`current-members` and `members-round-frame` keep nothing in general.** Their cells for an arbitrary row edit do not exist
  (the `-NONE` names); a row function that keeps what the part reads goes through the part's `-m`
  form. That was a source patch with one rule per table; it is `tree/row-sites` with the same
  rule. A site without a rule still has no cell, and is reached only from the part's own proofs.
- **`current-members`'s own proofs stay registered where they are proved** (`swap!` on the bundle's lemma
  map, in `fires`, `track-take` and `cascade`): 23 composite lemmas over three namespaces,
  most with `marks-waiting`, `i10-current-exempt` and `edge-kinds` of the input as extra hypotheses, all called only from other
  own proofs. The three former overrides are registered the same way. They are not `:over` rows:
  an `:over` row is known from the table on, and its copier name becomes an alias when the lemma
  has another name (§5k). Here the names differ for all of them (`current-members-x`, not `hm3-x`), so `:over`
  would add 26 alias theorems, and the lemmas restated before a proof exists would have to be
  re-ordered. The naming pass can fold them into the table.
- **The "materialize the closure" calls are gone.** The await namespaces asked nine bundles for
  lemmas at load, before use, because the copier generated lazily and a later namespace must not
  depend on a REPL's earlier calls. Measured (every `restate!` call logged with the number of
  lemmas it adds): 45 of those calls add nothing, since each part restates its whole closure in
  its own namespace, and so do 7 of `current-members`'s. They are deleted; the 12 calls that remain (all
  `current-members`'s, which has no whole closure) each add at least one lemma.
- `inv.marks-step` still reads the source of `progress.l5` to re-prove 17 `es-nm` lemmas for
  `hk-ek` by renaming (`ek-tr`). That is not the copier (no bundle, no closure, no override); it
  uses only the source reader, which stays. Removing it means either writing the 17 proofs out a
  second time (about 130 lines) or stating the l5 lemmas once over an abstract relation with the
  five closure properties both relations have. The second is the right fix and is a change to
  `progress.l5`'s statements, so it is left for a separate PR.

**What the plan got wrong.** It expected `current-members` to need hand renames turned into table rows, as
`marks-waiting` did, and two PRs. The renames are the bundle record, which stays; the rest is the standard
recipe and one PR. It listed `edge-kind-kept` as a part to convert: `edge-kind-kept` was restated from the tree already.
It did not expect most `lcopy!` calls in the members to be dead.

**One pitfall again** (§5n): a row rule's lemma applied to the row function's arguments must
leave them to unification (`_`) when a caller's variable has the name of one of the site's
binders (`fm-act-fill w x _ _` at `(act-fill x v)`).

No tree change.

### Gate (group 9)

- **Statements** (name-independent fingerprints, against §5w): all 18,366 identical; none changed,
  none missing; 49 new, the `raw0-<item>-ekb` (`edge-kinds` now restates raw by item). No part lemma:
  `current-members`, `edge-kinds` and `members-round-frame` have sites only. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`,
  `l5-safety-total`, `step-chain`, `mv-refinement` unchanged.
- **Load**, one JVM at a time, against §5w's measure, on a loaded host (another session's JVMs:
  untouched namespaces 278 → 422 s, a factor 1.52): the twelve touched member namespaces
  57 → 85 s, a factor 1.50. No measurable change; in the REPL the members load as before.
- **Suite**: `clojure -M:test`, 309 tests, 208,605 assertions, 0 failures, 0 errors (oracle samples
  1–62; the tree test also checks that `current-members`, `edge-kinds` and `members-round-frame` have no overrides, patches or part
  lemmas).
- Copier call forms left in `formal/src`: none.

## 5y. Stage 4, last PR: the copier is deleted; the programme's totals

**Result.** `pres.part` no longer contains the copier: `lcopy!`, `lcopy-try!`, `override!`,
`patch!`, `closure`, `copy-one-form`, `source-of`, `subst-forms` and `app-of?` are deleted, and
the bundle record loses its `:overrides` and `:patches` maps (264 → 216 lines). What stays is what
the tree uses: the base proof as data (`source-theorems`), the bundle record (`mk-bundle`), the
cells (`prim!`, `defpart`, `frame!`), `copy-name` and `copy-form` (a base lemma's name and
statement for a part) and `inst`. Three users changed: the tree computes the closure of
`step-well-formed` itself instead of through a probe bundle; `inv.i1-runs` reads a base lemma's source
directly; `inv.idle`'s `fix-f` (the copier's reading of an implicit row function, which the tree
does in `fill-rows`) is deleted. The README's "How the code expresses it" describes the tree.

**Totals of the programme** (before stage 1: the model at e04b1a9, PR #304; after: this PR).

| | before stage 1 | after stage 4 |
|---|---|---|
| `override!` forms | 337 | 0 |
| `patch!` forms | 94 | 0 |
| `lcopy!` forms | 209 | 0 |
| part tables (`tree/part!`) / restatement calls (`tree/restate!`) | 0 / 0 | 41 / 240 |
| kernel theorems | 16,119 | 18,415 |
| source lines of `formal/src` | 77,485 | 77,302 |
| whole-model load, one JVM | about 473 s | 335 s (§5w's measure) to 360 s (this PR's), on a host other sessions also use |

- **The theorem count went up, not down.** 1,907 of the 18,415 are the tree's own: 486 generic
  lemmas (239 shared `pres-x`, 247 part lemmas `pres-x@part`), the 49 `raw0-<item>-inv`, and 1,372
  `raw0-<item>-<part>` (49 for each of the 28 parts that restate the raw step; the copier had one
  `raw0-<part>` each). The model also grew in the meantime (oracle samples 61 and 62 and their
  transitions). What changed is what a generated theorem is: a restatement is one application of
  a generic lemma, not a re-check of the base proof's text, so the count no longer measures work.
  The plan's estimate that "about 10,000 of the 16,119 theorems are copies" that would disappear
  was wrong in that sense: the names and statements were kept on purpose (every later proof uses
  them), so the copies became restatements.
- **Source lines are about the same.** The copier's overrides were proofs; about a third became
  table rows, the rest are the parts' own proofs, now plain theorems. The tree and its tables
  (617 + the tables) replace the copier's machinery and patches.
- **Load time** is host-bound; the per-PR gates give the touched namespaces against the untouched
  ones. The whole-model figure moved between 335 s and 508 s
  across stage 4's gates with other sessions' JVMs on the host (the same sources: untouched
  namespaces ×1.5), so the 113 to 138 s below the baseline is an estimate, not a quiet-host measurement.

**Not done, and why.**
- *The tree rule for a forall-wrapped statement* (§5t; it would remove `host-roots-revoked-await-wire` and
  `host-roots-revoked-await-raw`, two plumbing proofs). It is not cheap: a fact would have to be inserted under the
  quantifier in the statement, and named by the `intros` inside each induction case of the proof,
  not by the first `intro`. That is a second code path in `insert-before-inv` and `with-own` for
  two proofs of about 15 lines.
- *`i10-current`'s wrappers through the first-position parameter* (§5q). `i10-current` is `i10-current-exempt [] []`: two
  parameters, and the mechanism instantiates one (`child-term`), so the tree needs a small
  extension first. The 49 wrapper theorems (`<x>-g10-r`) would then go; no source names them
  (they are reached through `i10-current`'s lemma map only), so that is safe, but it is a tree change,
  a rewrite of `inv.i10`'s last part and a gate of its own. Left as the next small PR.
- *`inv.marks-step`'s renaming of 17 `progress.l5` proofs* (§5x).
- *`current-members`'s own proofs as `:over` rows* (§5x): for the naming pass.

**What the plan got wrong.** Nothing in this PR; the deletion was mechanical once no caller was
left.

### Gate (last PR)

- **Statements** (name-independent fingerprints, against §5x): all 18,415 identical; none changed,
  none missing, none new. `inv-step`, `reach-inv`, `inv-empty`, `sys-reach-inv`,
  `l5-safety-total`, `step-chain`, `mv-refinement` unchanged.
- **Load**, one JVM at a time, against §5x's measure (which ran on a loaded host): `pres.tree`
  16.3 → 10.5 s, `inv.i1-runs` 10.3 → 7.5 s, `inv.idle` 8.0 → 8.2 s; untouched 473 → 334 s, whole
  model 508 → 360 s. Against §5w's measure, the last on a comparable host: 335 → 360 s.
- **Suite**: `clojure -M:test`, 310 tests, 208,521 assertions, 0 failures, 0 errors (oracle samples
  1–62). 84 assertions fewer than §5x: the per-part checks "no overrides, no patches" are replaced
  by one test that the copier's functions and the two maps do not exist.

## 6. Key pieces to read: the whole proof in 14 stops, in reading order (current names)

1. `inv`, `inv-step`, `WorldReach`, `reach-inv` (`top.clj`): the headline and its four-line induction.
2. `World` (`state.clj:137`), `Item` (`step.clj:206`): the state (15 fields: 11 row tables, `pins`,
   `pending-act`, `released`, `next-id`) and the 49 items.
3. `world-step`, `raw`, `then-cancel-losers`, `then-rule-r` (`engine.clj:3439-3447`), `transition` (`engine.clj:3325`), `rule-r`
   and `rule-r-round` (`rule.clj:1347-1354`): what a step is.
4. `well-formed`, `well-formed-parts`, `well-formed-intro` (`edits.clj:680`, `1214`): the base every part sits on.
5. `step-well-formed` (`engine.clj:3787`) → `well-formed-transition` (`3449`) → `well-formed-cancel-run-local` (`rule.clj:675`) →
   `well-formed-run-upd`: the base proof from the item to one primitive.
6. `filter-safe-of-refs` (`inv/copier.clj:3004`), `step-rule-r-safe` (`inv/base.clj:2133`): P3, Rule R's
   filter is safe; the shared premise of every part.
7. `chain-start`, `step-chain-start` (`inv/base.clj:2112-2146`): how parts are assembled with their companions.
8. `step-i10-task` (`inv/i10_task.clj`): one part's step theorem: refusal, then raw, then Rule R, with the
   companion `acts-parked`.
9. `i10-task-rest`/`i10-task-keys-ok`, `i10-task-view`, `i10-task-rest-frame` (`inv/copier.clj:77`, `1097`): a part, its view and its frame.
10. `i10-task-exempt`, `i10-task-exempt-kill`, `i10-task-task-done-x` (`inv/copier.clj`), `i10-task-cancel-run-local-hand` (`inv/i10_task.clj`): a
    violation deferred within a step: its break and its repair.
11. `mk-bundle`, `prim-form`, `copy-subst`, `lcopy!` (`inv/copier.clj:188-293`): how a part reuses the
    base proof today. This is the piece the generic tree replaces.
12. `i8-closed-close-local`, `i8-closed-cascade`, `i8-closed-cascade-done` (`inv/i8.clj:891`, ~1280-1305), `cascade-done-acts-parked`
    (`inv/acts.clj:1354`): an exemption as ghost state in a loop, emptied by P4.
13. `step-chain`, `l5-safety-total` (`inv/members/step.clj:916`, `927`): the end of the chain and what it
    buys (L5's safety half). Read the `inv.members.bundle` docstring for `current-members`, the most complex part.
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
  count of `(override! ` gives 337; E1 counted the forms it could attribute to a named bundle). The most overridden: `well-formed-dispatch-raw` 11,
  `well-formed-spawn-rows` 10, `well-formed-cancel-run-local`/`well-formed-take-park`/`well-formed-start-raw` 8. Primitive cells
  (`prim!` after `doseq` expansion): 1,357, of which 969 are `nil` and 388 are proofs; 39 distinct
  primitives.
- **E3, reads and writes.** For each bundle, the World fields its rest predicate reads (keywords and
  table accessors, followed through the `a/defn`s it calls); for each primitive, the fields its edit
  writes (setters and table edits, followed the same way). Cells: 875 disjoint and a frame, 46 disjoint
  but given a proof (the edge edits `mark-edge`, `unmark-edge`, `remove-edge` are defined by `match`,
  which `rfl` does not reduce: frames in substance), 42 overlapping but a frame (a column-level key is
  kept), and 316 overlapping with a proof.
- **E4, E5, transitions touching a part.** The 56 item-level transitions (`t*-inv`) and the tables or
  columns each one writes, against each part's reads. Large parts are touched by 39–52 of 56; `i1-scopes` and
  `comp-exists` by 17.
- **E6, E8, overrides by added premises.** An override's statement compared with the source lemma's:
  176 add a premise, 153 do not (2 unclassified). Combined with whether the override calls another
  override of the same bundle, this gives the plumbing versus content estimate of section 2.5.
- **E7, the overrides of `i8-closed`, `marks-waiting`, `i10-task`, `i9-res`, `comp-facts` and `i7-idle`**, with their added premises, read by
  hand (the grouping of `i8-closed`'s 51 in section 2.5).
- **E10, call sites.** 154 primitive call sites in 103 composites; 58 distinct (update primitive, row
  function) pairs.

## The naming pass

One pass renamed the hand-written definitions and theorems and, through the lines that build
names, the generated ones. It changed no statement: every constant has the same name-independent
fingerprint before and after (`dev/naming/fingerprint.clj`, `compare.clj`).

- The map is data: `dev/naming/rules.edn` (the decisions) and `dev/naming/generator-edits.edn`
  (the lines that build names from strings). `bb dev/naming/renames.clj` computes
  `notes/renames.edn` from them and a load of the model, checks it (no two names merge, every new
  name is free, prefix nesting) and, with `--apply`, writes the substitution. `dev/naming/NOTES.md`
  says how to rerun it.
- One copy rule. Every base lemma is `well-formed-<x>`; a part's lemma is that name with the
  part's name in place of `well-formed` (`pres.part/copy-name`). A bundle's prefix is its
  predicate's name. The private copiers of `inv.rank-step` and `progress.casc` follow the same
  rule with `i12-ranks` and `cascade-bound`.
- The substitution is by whole symbol and reads scope: a hypothesis or binder that has the
  short name a part used to have, and an Item constructor in a pattern that shares its name with a
  definition, are left alone
  (`dev/naming/scope.clj`).
- step.clj's `dispatch` and its transitions stayed in the naming pass (`step_test` and `rule_test`
  drove the compiled function; its T1, T8 and T15 were `<name>-basic`). They are deleted since:
  the two tests drive engine.clj's `transition`, and the 27 constants are the `:deleted` list of
  `notes/renames.edn`.
- Not renamed: internal helper families whose names are abbreviations of a proof step (`hk-`,
  `fm-`, `qk-`, `wdom-`, `oc-`, `z59-`, `sl-`, `s9-`). They keep their suffix words and take only
  the part's name where it was a prefix.
