# Replacing the lemma copier with a generic preservation theorem: prototype and path

Status 2026-11-18: a scoped prototype (`generic-preservation-proto.clj` next to this note, not loaded by the
model) and the plan below. The copier stays in place; nothing in the model depends on this note.

## What the copier does today

A bundle is `B w = well-formed w && B-rest w`. Its step theorem is obtained by re-elaborating the whole
`well-formed` proof tree of `step-well-formed` (the lemmas of `edits`, `step`, `rule`, `engine` that mention
`well-formed`) once per bundle, with `well-formed` replaced by `B` and every callee renamed to its copy
(`spindel.v2.inv.copier`: `mk-bundle`, `prim!`, `lcopy!`, `override!`, `patch!`; `inv.acts` and
`progress.casc` have two older copies of the same machinery).

| | count in `formal/src` |
|---|---|
| bundles (`mk-bundle`) | 51 |
| `prim!` (a primitive edit's rest-part lemma) | 410 |
| `lcopy!` (copy the closure of a root) | 209 |
| `override!` (a hand proof replaces the copy of one lemma) | 337 |
| `patch!` (a source proof is rewritten before the copy) | 94 |
| theorems in the env after loading the model | 16,119, of which roughly 10,000 are bundle copies |

Sound (every copy is kernel-checked) but it multiplies elaboration: the same proof tree is elaborated about
50 times, which is an estimated half or more of the model's 8-minute load (below). Eleven bundles use no
override or patch; the bundles of the main chain use up to 51 overrides each (`i8-closed` 51, `marks-waiting` 45, `i7-idle` 29,
`comp-facts` 23, `i5-dep-final` 21; counted as `override!` forms in the source).

## The generic alternative

Prove the tree once over an abstract rest part:

```
structure GPrim (Q : World -> Bool) where            -- one field per primitive obligation
  o-scope-upd : forall w x f (hf : ...), well-formed w = true -> Q w = true -> Q (scope-upd w x f) = true
  ...
gq Q P w := well-formed w && Q w                      -- P : GPrim Q
gq-<lemma> : forall Q (P : GPrim Q) ..., gq Q P w = true -> gq Q P w' = true      -- once, for every lemma
```

A bundle then supplies one value `pB : GPrim B-rest` built from its primitive lemmas, and every lemma of
the tree for `B` is `gq-<lemma> B-rest pB`: an application, checked by unfolding `gq` and `B` (no
re-elaboration).

## Prototype (i10-task, the I10 task-part bundle)

`generic-preservation-proto.clj`, run in a REPL after `(require 'spindel.v2.inv.copier)`:

1. gl's part of the tree: 156 composite lemmas in the closure of `step-well-formed` (gl's 9 overrides and 32
   primitives as stop points). 112 of them have no lemma in their closure that i10-task patches.
2. Of those, the prototype takes the roots whose primitives have a bundle-independent shape (no
   `run-upd` / `task-upd`, see obstacle 1): 19 primitives, which become the 19 fields of `GPrim`.
3. The existing copier, given the bundle `gq` with parameters `[Q, P : GPrim Q]` and each primitive's
   rest part `(GPrim.o-<prim> P ... R)`, produced **47 generic lemmas** (27 maximal roots, among them
   `well-formed-t3-create-top`, `well-formed-t8-observe-basic`, `well-formed-t8-unobserve`, `well-formed-t20-pin`, `well-formed-t20-unpin`, `well-formed-t22-host-unawait`,
   `well-formed-t-open-scope`, `well-formed-t-drain`, `well-formed-t-own`, `well-formed-t-owned-done`, `well-formed-cancel-res`,
   `well-formed-invalidate-dependents`, `well-formed-retire-after`, `well-formed-demote-epoch`, `well-formed-await-wire`).
4. `pgl : GPrim i10-task-rest` from gl's primitive lemmas (19 fields; a structure of proofs is in `Type`, so it
   is an `a/defn`).
5. Each of gl's own copies of those lemmas, restated with its exact statement, is proved by
   `(exact (gq-<lemma> i10-task-rest pgl ...))`: 46 of 46 (the 47th, `well-formed-t8-observe-basic`, has no i10-task copy because
   i10-task never needed it).

Timings (one JVM, after `inv.copier` is loaded; the standalone run of the script, with an earlier REPL run in
parentheses):

| | seconds |
|---|---|
| per-bundle copy of these 47 lemmas (a concrete bundle `gt` with a trivial rest part) | 1.05 (1.42) |
| the generic copy of the same 47 lemmas (`gq2`), once | 0.96 (1.67) |
| instantiation for i10-task (`pgl`) | 0.07 (0.16) |
| restating and checking gl's lemmas from the generic ones (optional) | 0.11 (0.27) |

So for this slice a bundle costs well under 0.1-0.2 s instead of 1-1.4 s, after a one-time copy of about the
same cost as one bundle's. At 20-30 ms per copied lemma (this slice; larger lemmas cost more) and roughly
10,000 copies, the copies are an estimated 200-300 s of the 470-500 s it takes to load the model; the
generic form would elaborate the tree once plus one instance per bundle.

## Obstacles found

1. **Primitive side conditions are bundle-specific.** gl's `run-upd`/`task-upd` primitives need the row
   function to keep gl's keys (`extra-args` inserts `(fn [r] (Eq.refl (run-key r)))` at each call site, true
   by definition for the concrete function there). i9-res has no general `resource-upd` primitive at all: it
   patches each call site with a lemma for that row function (`i9-res-res-upd-q` with `res-cancel-row`,
   `res-set-phase rp-fired`). Instantiating the prototype's `GPrim` for i9-res fails exactly at that field.
   So the fields must be **per call site** (a primitive applied to the concrete row function used there),
   not per primitive. That is mechanical: the copier already knows every call site.
2. **Patches thread companion facts.** 94 patches rewrite a source proof so that a lemma deep in the
   tree gets a fact about the input world (`acts-parked`, `comp-facts`, `i7-idle`, ...). Generically: `GPrim Q C` with fields
   `C w -> well-formed w -> Q w -> Q (edit w)`, and `C` carried through the intermediate worlds (C is itself
   a bundle, so its own instance gives that).
3. **Overrides are not compositional.** The 337 overrides prove a transition through an intermediate
   world where the invariant is broken (exemption lists such as gl's `i10-task-exempt`, h3's member exemptions).
   They become **composite-level fields**: the generic tree takes `T12-pres Q`, `cancel-run-local-pres Q`,
   ... as hypotheses at the points some bundle overrides, and a bundle that does not override supplies the
   default, proved once generically from `GPrim` (`default-t12 : GPrim Q -> T12-pres Q`).
4. **Introduction lemmas are not preservation lemmas.** `well-formed-intro` (build `well-formed` from its parts)
   and the lemmas proved through it (`well-formed-set-released`, `well-formed-set-pending-act`, `well-formed-run-ins-fresh`, ...)
   fail to copy generically; they must be fields too (i10-task treats them as primitives already).

## Path

1. Make the copier emit the obligation structure: fields per call-site primitive instance (1) and per
   introduction lemma (4), for the part of the tree no bundle patches or overrides; convert the eleven
   bundles without overrides or patches first and measure. Estimate: a week.
2. Override points as composite fields with generic defaults (3); convert the chain bundles one by one,
   their overrides becoming field proofs unchanged. Estimate: one to two weeks.
3. Companion context for patches (2). Estimate: one to two weeks.

Each step keeps every statement (the prototype's restatement check, applied to all copies, is the
regression test), and bundles not yet converted keep using the copier. Lines change little (primitive
and override proofs stay, as field proofs); load time and the shape of the proof change a lot: the step's
proof tree exists once, an invariant is data (one instance), and a new primitive edit is a new field that
every instance must supply, instead of a copier run per bundle.

A cheaper alternative with a different payoff is to have the copier write its generated theorems to
files that are checked in (reviewable, greppable, no load-time generation), at the cost of a larger tree.
