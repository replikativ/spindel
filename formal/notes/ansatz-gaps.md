# Ansatz gaps

## reach: `induction` drops the IH of a reflexive (Pi-typed) recursive field

Ansatz 0.2.604. The recursor is right (`GapW.rec` has the minor premise
`∀ x h, (ih_h : ∀ y, motive (succ y) (h y)) → motive x (mk x h)`), but the `induction`
tactic only treats a field as recursive when its type *is* the inductive
(`tactic/basic.clj` `is-recursive`, around line 1375). For `h : ∀ y, W (f y)` it creates no
`ih_h`, and the branch it builds does not match the recursor's minor premise. Extraction then
fails with a kernel type mismatch:

```clojure
(a/inductive GapW [] :in Prop :indices [x Nat]
  (mk [x Nat] [h (forall [y :- Nat] (GapW (Nat.succ y)))] :where [x]))
(a/theorem gap-w-ind [x :- Nat] (=> (GapW x) (= x x)) (intro h) (induction h) (rfl))
;; goal after induction has only `h`, no ih_h; the proof then fails:
;; "Type mismatch in application of GapW.rec ... domType ... (forall ih_h ...)"
```

Lean: `induction h` gives `ih_h : ∀ (y : Nat), motive (y+1) (h y)` (reflexive fields get a
Pi-typed IH, `Lean.Meta.Tactic.Induction` built from the recursor's minor premise).
Workaround used in `spindel.v2.reach`: `derive-run-complete` applies `Derive.rec` directly with
an explicit motive, and its minor premise is a separate lemma (`derive-run-complete-step`).

## reach: `subst h` with `h : a = b` (both fvars) eliminates `a`; Lean eliminates `b`

```clojure
(a/theorem subst-dir [v :- Nat, x :- Nat, h :- (= v x)] (= v x) (subst h) (exact (Eq.refl v)))
;; ansatz: after subst only `x` is left, so "Unknown constant: v"
```

Lean `Lean.Meta.subst` (Subst.lean, `substEq`) tries the RHS first (`symm := true`): when `b`
is an fvar it replaces `b` with `a`, so `v` survives and `exact rfl`/`Eq.refl v` works.
Proofs that name the surviving variable after `subst` diverge from Lean. Workaround used: `rw [h]`.

## reach: `simp at h1 h2` fails when simplifying `h1` closes the goal

```clojure
(a/theorem gap-simp-at2 [b :- Bool, c :- Bool]
  (=> (= false true) (= c true) (= b true)) (intro h1 h2) (simp at h1 h2))
;; ansatz: "simp at: no hypothesis named h2"
```

Lean: `simp at h1 h2` closes the goal as soon as one location becomes `False` (simpGoal returns
`none`), with no error. Workaround used: one `simp ... at` per case.

## reach: dotted `a/structure` names break codegen of functions that build them

```clojure
(a/structure Gap.Pair [] (a Nat) (b Bool))
(a/defn gap-mk [n :- Nat] Gap.Pair (Gap.Pair.mk n true))
;; Syntax error compiling ... ClassNotFoundException: ->Gap.Pair
```

The kernel side is fine, but the emitted Clojure calls the record constructor `->Gap.Pair`, and
Clojure reads a dotted symbol as a class name. Lean allows namespaced structure names. Relatedly,
a dotted `a/defn` name (`Reach.mem`) is interned as a var that Clojure callers cannot reference
unqualified, because `(Reach.mem …)` also resolves as a class. Workaround used: undotted names
(`ReachResult`, `reach-mem`, `reach-closure`).

## reach (not a gap): the nested `Or` form of `Derive` is rejected, as in Lean

`hd : ∀ y, List.Mem y (deps x) → Or (leaf y = true) (Derive … y)` gives "invalid nested inductive
datatype 'Or', nested inductive datatype parameters cannot contain local variables". Lean 4.33's
kernel rejects the same declaration with the same message (checked with `lean_run_code`).
`spindel.v2.reach` uses the equivalent `∀ y, List.Mem y (deps x) → leaf y = false → Derive … y`,
which is equivalent because `leaf` is Bool.

## reach (tier, not a bug): the bundled Init tier lacks most `List.Mem` lemmas

`(a/load-init!)` (6325 declarations) has `List.not_mem_nil` and `List.mem_cons` but not
`List.mem_append`, `List.mem_cons_self`, `List.mem_of_elem_eq_true`/`elem_eq_true_of_mem`,
`List.mem_filter`, or `List.all_eq_true`. `List.mem_cons` (stated over `∈`) also does not fire
under `simp` on a raw `List.Mem x (h :: t)`. `spindel.v2.reach` works in Bool (`reach-mem` with
`reach-mem-iff`, `-cons`, `-app`) and bridges to `List.Mem` only at the `Reach` constructors.

## state: a structure projection passed as a function value breaks codegen

Ansatz 0.2.604. Elaboration and kernel check succeed, but the compiled Clojure refers to the
projection by its kernel name, which Clojure reads as a class name:

```clojure
(a/structure GapRow [] (id Nat) (v Nat))
(a/defn gap-ids [xs :- (List GapRow)] (List Nat) (List.map GapRow.id xs))
;; Syntax error (ClassNotFoundException) compiling ... GapRow.id
(a/defn gap-ids2 [xs :- (List GapRow)] (List Nat) (List.map (fn [r :- GapRow] (:id r)) xs))
;; works: (gap-ids2 [(->GapRow 3 4)]) => (3)
```

Lean: a projection `GapRow.id` is an ordinary function constant; `List.map GapRow.id xs`
compiles (the compiler eta-expands / uses the projection's compiled definition). Workaround
used in `spindel.v2.state`: every table gets a named key function `<p>-id` (`(a/defn edge-id
[r :- EdgeRow] Nat (:id r))`) and the generic table operations take that.

## state: `simp only [name]` silently ignores an unknown lemma name; `Bool.not_eq_true'` missing

```clojure
(a/theorem gap-unknown-simp [b :- Bool, h :- (= b false)] (= (Bool.not b) true)
  (simp only [no-such-lemma-xyz h]))
;; ansatz: PROVED (the unknown name is dropped without a message)
```

Lean: `simp only [no_such_lemma_xyz, h]` is an error (`unknown identifier`). This hid a real
problem: `Bool.not_eq_true'` (Init/SimpLemmas.lean:394, `((!b) = true) = (b = false)`) is not in
the bundled Init env (`(a/load-init!)`, 6325 declarations: lookup returns nil), so `simp only
[... Bool.not_eq_true'] at h` just made no progress there. Workaround used: a local lemma
`bnot-true : (!b) = true -> b = false` (by `cases b`).

## step (not a gap): `simp only [h] at hb` leaves `hb : true = false` open, as in Lean

```clojure
(a/theorem gap-simp-only-ctor-eq [b :- Bool, h :- (= b true)] (=> (= b false) (= 1 2))
  (intro hb) (simp only [h] at hb))
;; ansatz: Proof incomplete, hb : true = false
```

Lean 4.33 (checked with `lean_run_code`) reports the same unsolved goal: `simp only` with only
`[h]` does not close a `true = false` hypothesis. Use `simp [...] at hb` (full simp set) to close
such branches; spindel.v2.step does this in every refusal lemma.

Related pitfall (project, not ansatz): all namespaces share ONE kernel env, so two namespaces
must not declare the same constant name (Lean would reject it too). `spindel.v2.retain` defines
`tbl-keep`; the filter edit appended to edits.clj is therefore named `tbl-filter`.

## retain: compiled structural recursion on a Nat fuel evaluates the recursive call eagerly

Ansatz 0.2.604. A function that matches on a Nat argument and calls itself in the `succ`
branch compiles to `Nat.recCompiled zero succ-fn fuel`; the minor premise receives the
recursive value (the IH) as an argument and the runtime computes it eagerly, although the
body never uses it (it calls `self` directly). Every level re-runs the whole recursion below
it, so the cost grows like (fuel choose pops):

```clojure
(a/defn gap-countdown [fuel :- Nat, n :- Nat] Nat
  (match fuel [zero n] [(succ k) (if (Nat.beq n 0) 0 (gap-countdown k (- n 1)))]))
;; (gap-countdown 30 6) 72 ms, (gap-countdown 30 10) 1.6 s, (gap-countdown 30 14) 9.5 s
```

`spindel.v2.reach/reach-run` has the same shape: `reach-run 40 succ [1]` on a 12-node chain
does not finish in 60 s, so the retention oracle could not run. Lean compiles structural
recursion to the self-call (the compiler uses the equation-compiled `_unsafe_rec` /
`implemented_by` body; `Nat.rec` itself is not even compilable, "code generator does not
support recursor"), so the cost is linear in the pops. List recursion is fine in ansatz (it
compiles to a self-call). Workaround used: `reach-closure-l` / `reach-run-l` in
`spindel.v2.reach`, the same worklist with one list cell per unit of fuel, plus
`reach-run-l-eq : reach-run-l fuel succ roots = reach-run (List.length fuel) succ roots`, so all
reach-run theorems transfer. `derive-run` / `derive-loop` have the same Nat-fuel shape.

## retain: a partially applied inductive family is rejected as a function argument

```clojure
(a/inductive GapR [roots (List Nat)] :in Prop :indices [x Nat]
  (mk [x Nat] [h (List.Mem Nat x roots)] :where [x]))
(a/theorem gap-use-pred [P :- (=> Nat Prop), x :- Nat, h :- (P x)] (P x) (exact h))
(a/theorem gap-partial-ind [roots :- (List Nat), x :- Nat, h :- (GapR roots x)] (GapR roots x)
  (exact (gap-use-pred (GapR roots) x h)))
;; ansatz: "Elaboration error: Type mismatch in application"
;; (exact (gap-use-pred (fn [a :- Nat] (GapR roots a)) x h)) works
```

Lean: `GapR roots : Nat → Prop` is an ordinary term and `gap_use_pred (GapR roots) x h`
elaborates. Workaround used in `spindel.v2.retain` (`live-filter-reach`): eta-expand to
`(fn [a :- Nat] (Reach (retain-succ w) (roots w) a))`.

## retain: `simp` turns `List.append` into `HAppend.hAppend` (not a bug, a recipe)

After unfolding a definition written with `(List.append Nat a b)`, `simp` states the goal with
`HAppend.hAppend` (as Lean's simp normal form `a ++ b`), so a Bool-membership lemma over
`List.append` no longer fires. Give simp both forms (`reach-mem-append` and
`reach-mem-app`), as `spindel.v2.reach` already provides.

## rule: `rw [h]` does not rewrite under a structure projection, and silently does nothing

Ansatz 0.2.604. `rw` does not find an instance of the LHS inside a projection (`:field x`
elaborates to an `Expr.proj`), and when it finds no instance it succeeds without changing the
goal instead of failing:

```clojure
(a/structure GapOut [] (wv Nat) (ok Bool))
(a/defn gap-f [n :- Nat] GapOut (GapOut.mk n true))
(a/theorem gap-rw-proj [n :- Nat, h :- (= (gap-f n) (GapOut.mk 0 false))] (= (:wv (gap-f n)) 0)
  (rw [h]))
;; ansatz: "Proof incomplete", goal still GapOut.0((gap-f n)) = 0
```

Lean 4.33 (checked with `lean_run_code`): `rw [h]` rewrites `(gapF n).wv` to
`{ wv := 0, ok := false }.wv` and closes the goal by `rfl`; `kabstract` visits the structure
argument of `Expr.proj`. With no occurrence Lean fails: "Tactic `rewrite` failed: Did not find
an occurrence of the pattern". In `spindel.v2.rule` this hid itself in `step-inv`
(`rw [(step-refuse w it ha)]` on `(:world (world-step w it))` made no change). Workaround:
`(have e := ...)` then `(simp only [e ...])`, or state the lemma about the projection
(`step-accepted` is stated as `(:world (world-step w it)) = ...` and `rw` with it works).

## sources: `simp only [f hf]` does not unfold a Nat-structural function at `n + 1`

```clojure
(a/theorem derive-loop-succ-nil [n :- Nat, ...]
  (=> (= (derive-fresh base deps leaf derived nodes) (List.nil Nat))
      (= (derive-loop (+ n 1) base deps leaf nodes derived) (DeriveResult.mk derived true)))
  (intro hf) (simp only [derive-loop hf]))   ; also (simp [derive-loop hf])
;; ansatz: Proof incomplete, the goal still has (derive-loop (n + 1) ...)
```

Lean 4.33: the equation lemmas of a structural definition on Nat are stated at `n + 1`
(`derive_loop.eq_2`), so `simp only [derive_loop, hf]` rewrites the goal. Workaround used in
`spindel.v2.reach` (`derive-loop-succ-nil/-cons`): state the lemma at `(Nat.succ n)` and rewrite
`List.length (u :: t)` to `Nat.succ (List.length t)` with a `have ... (rfl)`.

## sources: no `by` tactic block in term position

```clojure
(exact (tbl-all-mono A P Q (fn [x :- A, hx :- (= (P x) true)] (by (simp [hx]))) xs h))
;; ansatz: Elaboration error: Unknown constant: by
```

Lean: `fun x hx => by simp [hx]` elaborates. Workaround used in `spindel.v2.rank`: a named
auxiliary lemma (`pend-of-edge`) passed as the function.

## sources (ergonomics): `case` failures do not show the goal

`(case [nil] ...)` whose body leaves a goal fails with "case body did not close its goals" and
no goal display; the same proof with `case'` and plain tactics shows "Proof incomplete" with
the goal. Lean reports the unsolved goal in both forms. (Related to tracker #12.)

## oblig: `(fn [x :- T] (rfl))` as a term argument does not elaborate

Ansatz 0.2.604. `(rfl)` works as a term when its expected type is an equation (spindel.v2.rank
passes it as an argument), but not under a `fn` binder whose body type is `(= (:b (f g)) (:b g))`
with `f` a concrete row function (definitionally equal sides):

```clojure
(a/structure GapRk [] (a Nat) (b Nat))
(a/defn gap-rk-set [n :- Nat, g :- GapRk] GapRk (GapRk.mk n (:b g)))
(a/theorem gap-rk-use [f :- (=> GapRk GapRk), h :- (forall [g :- GapRk] (= (:b (f g)) (:b g)))] (= 1 1) (rfl))
(a/theorem gap-rk-1 [] (= 1 1) (exact (gap-rk-use (gap-rk-set 3) (fn [g :- GapRk] (rfl)))))
;; ansatz: "Elaboration error: Type mismatch in application"
(a/theorem gap-rk-2 [] (= 1 1) (exact (gap-rk-use (gap-rk-set 3) (fn [g :- GapRk] (Eq.refl (:b g))))))
;; proved
```

Lean: `gap_rk_use (gapRkSet 3) (fun g => rfl)` elaborates (`rfl` is checked against
`(gapRkSet 3 g).b = g.b` by `isDefEq`, which unfolds `gapRkSet`). Workaround used in
`spindel.v2.rank-step`: `(fn [c :- CompRow] (Eq.refl (:rank c)))`.

## oblig (recipe, with #12): a failed `require` keeps its declarations in the env

A namespace that fails half-way is removed by Clojure, but the kernel env keeps the
declarations checked before the failure, so a retry fails on the first one ("already declared").
`ansatz-env` is an atom of an immutable Env: snapshot `@a/ansatz-env` before each `require` and
`reset!` it before a retry (also drop the namespace from `*loaded-libs*`, and reload every
namespace loaded after the snapshot).

## p4: `simp at h` does not close a goal from `h : n < 0`

Ansatz 0.2.604:

```clojure
(a/theorem gap-p4-lt0 [n :- Nat, h :- (< n 0)] (= 1 2) (simp at h))
;; ansatz: "simp: simp at: made no progress"
```

Lean 4.33 (checked with `lean_run_code`): `example (n : Nat) (h : n < 0) : 1 = 2 := by simp at h`
succeeds: `Nat.not_lt_zero` is a simp lemma, `h` becomes `False` and the goal closes. The constant
`Nat.not_lt_zero` is in the bundled env, so the default simp set does not use it. Workaround used in
spindel.v2.casc (`casc-empties`, `norm-loop-ok`): `(simp only [List.length] at hp) (omega)`.

## p4 (recipe): name clashes across namespaces surface as "Type mismatch" in a REPL loader

A loader that skips already-declared constants (REPL iteration) silently reuses a same-named
constant of another namespace (`id-is` exists in spindel.v2.retain); the first use then fails with
"Elaboration error: Type mismatch in application". A clean load reports "already declared". Check
new names with `(.lookup env name)` before relying on a skip-loader.

## inv (pitfall, not a gap): nested `case'` with a constructor tag already used selects an outer goal

After `(cases h1 o1) (case' [some a]) (case' [none])`, a second `(cases h2 o2) (case' [some b])` inside the
`none` goal fails with "too many case variable names": the tag `some` resolves to the outer goal (already
named). Workaround used in spindel.v2.inv: the block form `(case [none] (cases h2 o2) (case [some b] ...))`,
or a helper lemma per level (`sl-drop-*-handle`). Lean 4 also resolves `case tag` to the first goal with that
tag, so this is a usage pattern, not a divergence.

## lit: `simp only [← h]` rewrites with `h` left-to-right

Ansatz 0.2.604:

```clojure
(a/theorem gap-simp-rev [P :- (=> Nat Bool), a :- Nat, b :- Nat, h :- (= a b), hp :- (= (P a) true)]
  (= (P b) true) (simp only [← h]) (exact hp))
;; ansatz: "Elaboration error: Type mismatch" (the goal is still P b = true)
(a/theorem gap-simp-rev-rw [P :- (=> Nat Bool), a :- Nat, b :- Nat, h :- (= a b), hp :- (= (P a) true)]
  (= (P b) true) (rw [← h]) (exact hp))
;; proved
```

Lean 4.33: `simp only [← h]` rewrites `b` to `a` (the reversed equation), the goal becomes `P a = true` and `exact hp`
closes it. In spindel.v2.lit (`find-witness`) `simp only [← hf]` with `hf : h = r0` rewrote `h` to `r0`, i.e. the
arrow was dropped. Workaround used: rewrite the hypothesis forward (`simp only [hf] at hp`) or `rw [← h]` on the goal.

## lit (pitfalls, not gaps)

- `cases hf (tbl-find ...)` replaces the term in the goal as well (Lean's `cases h : e`), so a conjunct of the goal that
  mentions the term no longer matches a hypothesis proved before the `cases`: prove such parts as `have`s first
  (`dep-cred-live`).
- `rw [h] at hl` with `h : (:id c) = x` may not rewrite a projection application; `Eq.trans (congrArg f h) hl` works.
- Name clashes again surfaced as "Type mismatch" with the skip-loader: `mem-has` (state.clj, activation members),
  `res-ok` (the RunResult tag code), `runs-nodup`, `resync-has` (rule/rank-step). Check new names against the
  pre-namespace env before relying on the loader (scratch `clashes`).
- Re-creating a namespace in the REPL (`remove-ns` + load) leaves test namespaces aliasing the old one ("Alias ...
  already exists"): `remove-ns` the test namespace too before reloading it.

## p3 (pitfalls, not filed as gaps)

- An explicit `_` for a World argument that later arguments' types (or the expected result type) determine only up to
  definitional unfolding is often not inferred: `(awo-rest-comps awc awr w _ (fn [a1 :- ...] (awake-upd ...)) (rfl) R)`
  and `(esb-scope-reparent _ _ s p1 h1)` fail with "Type mismatch in application"; the same term with the world
  written out (or the argument first bound by `have`) is accepted. Lean's app elaborator postpones such arguments
  until the expected type is unified; ansatz elaborates them in order. Not reduced to a minimal repro yet.
- `simp only [nat-fold]` (or any unfolding) closes a reflexive conjunct `x = x` to `True`, so a following `(rfl)` /
  `(exact (And.intro ... (rfl)))` meets `True`: build the `And` without simp (`exact` checks up to defeq).
- `rw [h] at z` where `z` mentions `(:id hd)` and `h` mentions `(edge-id hd)` silently does nothing (tracker #9's
  no-op; the terms are only definitionally equal): use `(Eq.trans (Eq.symm z) h)`.
- Bundle parameter names must not clash with the binder names of the copied source theorems (`rid` as a bundle
  parameter shadowed `inv-cancel-acts`'s `rid` and broke every copy that used it); use unusual names (`awc`, `awr`,
  `kc0`, `kd0`, `mkm`, `nax`).
- Name clashes across namespaces with the skip-loader: `has-false-all` (acts.clj), `of-at` (lit.clj). A clash check
  over the file's declared names against the pre-namespace env (scratch `clashes`) catches them.

## i10 (pitfalls and ergonomics)

- `rw [eb]` with `eb : complete-body W r res = Casc.mk W []` fails with "Type mismatch" when the goal mentions
  `(:world (complete-body ...))` and `(:rest (complete-body ...))` (tracker #9, rw under a projection; fixed upstream
  in #404, release pending); `simp only [eb]` works.
- No `sorry` tactic (Lean 4 has one), so a long proof cannot be checked piecewise; with #16 (a failing `case` block
  shows no goal) the workaround is to split a proof into lemmas. Tracker #21.
- Generic list lemmas over `A :- Type` instantiated at a structure type failed with "Type mismatch in application"
  twice; both times the cause was a name clash with an existing lemma (`gather-all`, `comps-nodup`) hidden by the
  skip-loader (p4/p3 pitfall). Run the clash check before trusting a skip-loaded file.
- (i11) A partially applied inductive family as a predicate argument (`(Reach succ roots)` for `Q :- (=> Nat Prop)`)
  is rejected again (tracker #8, fixed upstream in #400, release pending); eta-expanded `(fn [q :- Nat] (Reach ... q))`
  works.
## progress: no `sorry` tactic (ergonomics, with #16)

```clojure
(a/theorem gap-sorry [] (= 1 2) (sorry))
;; ansatz: "Unknown tactic: sorry"
```

Lean 4.33: `sorry` closes any goal with a warning ("declaration uses 'sorry'"), so a long proof can be checked up to a
point. Without it (and with `case` blocks hiding the remaining goal, #16) a failing step in a 120-line proof had to be
found by truncating the proof at line k and comparing the error ("Type mismatch" vs "did not close its goals"); the
scratch script cut the theorem and balanced the parentheses.

## progress (pitfalls, not gaps)

- A bundle copy reserves `<prefix><x>` for every copied `inv-<x>` lemma: a hand-written `mb-ack-raw` (a different statement)
  clashed with the copy of `inv-ack-raw`; the skip-loader skipped mine and the first use failed with "Type mismatch in
  application". Check new names against `(:copied B)` as well as other namespaces.
- `simp only [... h ...]` where `h` mentions `run-unwinding r` does not rewrite `run-unwinding (run-enter-row r)`; the goal
  stays open and the following `have` becomes part of the unfinished proof ("Unknown constant: so" later). State the fact on
  the edited row (`(have u2 (= (run-unwinding (run-enter-row r)) true)) (exact h)`, by defeq) and simp with that.

## l5 (pitfalls, not new gaps)

- Tracker #7 again, at runtime in the MODEL: `dirty-run` (spindel.v2.step) still uses the Nat-fuel `reach-run`, so a write
  in a world with a dozen dep edges takes minutes (a REPL hung on the 12-site settle scenario; the stack showed
  `reach.clj:60` recursing). The fix is released upstream as #403 (pending release); until then keep scenarios small or
  switch `dirty-run` to `reach-run-l`.
- Tracker #9 (rw under a projection) again: `rw [(settle-edge-eq ...)]` on `(:edges (settle-edge ...))` was a "Type
  mismatch"; `(have se := ...) (simp only [se])` works.
- After `(cases hm (:marked (f e)))` the goal mentions `true` where `(:marked (f e))` was, but a hypothesis simplified with
  `simp only [m] at hr` keeps its own shape; normalize both sides with the same simp set (`Bool.and_true`) before `exact`.
- The skip-loader leaves no Clojure var for an `a/defn` declared by an earlier failed `require` (the namespace was
  removed): tests calling it fail with "No such var". Reset the env to the pre-namespace snapshot and `require` afresh
  before running tests.

## z52 (ansatz 0.2.613 bump): `rw` leaves a beta-redex from an instantiated function argument (tracker #22)

```clojure
(a/defn gbq-all [p :- (=> Nat Bool), xs :- (List Nat)] Bool
  (match xs [nil true] [(cons h t) (Bool.and (p h) (gbq-all p t))]))
(a/defn gbq-g [n :- Nat] Nat n)
(a/theorem gbq-g-eq [n :- Nat] (= (gbq-g n) n) (rfl))
(a/theorem gbq-one [p :- (=> Nat Bool), n :- Nat]
  (= (gbq-all p (List.cons Nat n (List.nil Nat))) (Bool.and (p n) true)) (rfl))
(a/theorem gbq-beta2 [x :- Nat, h :- (= (gbq-all (fn [r :- Nat] (Nat.beq (gbq-g r) 0)) (List.cons Nat x (List.nil Nat))) true)]
  (= (Bool.and (Nat.beq x 0) true) true)
  (rw [gbq-one] at h) (rw [gbq-g-eq] at h) (exact h))
;; ansatz 0.2.613: "Did not find an occurrence of the pattern (gbq-g ?m)": after the first rw, h is
;; ((fun r => Nat.beq (gbq-g r) 0) x && true) = true, and gbq-g only occurs under the binder
```

Lean 4.33 (checked with `lean_run_code`): the same proof succeeds; `Lean.MVarId.rewrite` instantiates the motive with
`instantiateMVars`, which beta-reduces `?p n` once `?p := fun r => ..`, so h is `((gbqG x).beq 0 && true) = true`.
0.2.604's lenient `rw` hid this (four i10 proofs rewrote through such redexes). Workaround: `simp only [e]` (simp
beta-reduces), or `simp only [] at h` first.

## z52: `induction n` on Nat names the successor case `Nat.succ n` (Lean: `n + 1`) (with tracker #14)

The `succ` goal of `(induction fuel)` is stated at `Nat.succ n` (zero case `Nat.zero`), so lemmas stated at
`(+ n 1)` (the form gap #14 forces, e.g. `reach-closure-succ-cons`) do not match syntactically and `simp only` makes
no progress. Lean 4.33 (`@[induction_eliminator] Nat.rec` with `0` / `n + 1`, checked): `case succ ... ⊢ n + 1 + k = ..`.
Workaround in `reach-closure-more`: rewrite `(+ (Nat.succ n) k)` to `(+ (+ n k) 1)` by `omega`, restate the hypothesis
with `have` at `(+ n 1)` (defeq), then `show`.

## z52 (recipe): `case` blocks hide the goal; probe with `case'`

To see the goal inside a failing `(case [succ n ih] ...)` block (tracker #16), rewrite it as `(case' [succ n ih])`
followed by the tactics at top level and end the proof there: the error is then "Proof incomplete" with the goals.

## z52 (pitfalls, not gaps)

- An `_` world argument followed by a hypothesis argument about the world is solved from the FIRST argument that mentions it:
  `(g1-set-parent _ x p hs2 h1)` with `hs2 : scope-has w p` fixes `_ := w`, and `h1 : g1 (task-upd w ...)` then mismatches;
  pass the world explicitly (cf. the p3 pitfall on `_` world arguments).
- New names clashed again (`sd-fold`, `tsp-ok` existed elsewhere): check against the pre-namespace snapshot.
- `case` blocks nested three deep (`cases k2` on a 4-way `Or`) failed with "case body did not close its goals" while the same
  steps as `case'` + top level tactics proved (filter-lit-i1-scope): flatten with `case'`.

## z55 (pitfalls, no new gap filed)

- After `(cases hm (b))` a `(simp only [f hm])` that reduces one branch to `x = x` closes that goal (as Lean's simp does
  with `rfl`); a following `(rfl)` then runs on the NEXT goal and reports "rfl: sides are not definitionally equal".
  Drop the `(rfl)` (casc `ri-*`, lit `kw-*`). Same behaviour in Lean, not a gap.
- `simp only [(rkeys-upd x f hk)]` (a partially applied equation, the list argument still universally quantified) made
  no progress on `(KW.mk (rkeys (tbl-upd run-id x f rs)) ..)`, while `rw [(rkeys-upd x f hk rs)]` rewrote it (lit
  `kw-resume`). A minimal attempt (`simp only [(zg-eq 3)]` with the list still quantified, under a structure
  constructor) works, so the trigger is something else in that goal (a proof argument `hk` before the quantified list,
  or the implicit `RunRow` of `tbl-upd`); not filed, no tracker row until it reproduces.
- The REPL reload recipe used throughout: one env snapshot per namespace (`@a/ansatz-env` after each `require`), then
  `reset!` to the predecessor's snapshot + `remove-ns` + `require` (no skip-loader, so no name-clash masking).

## rest: `cases` accepts only a hypothesis name, not a term (tracker #24)

```clojure
(a/theorem gap-cases-term [p :- Prop, q :- Prop, r :- Prop] (=> (And p (Or q r)) (Or r q))
  (intro h) (cases (And.right h)) (case [inl a] (exact (Or.inr a))) (case [inr b] (exact (Or.inl b))))
;; ansatz 0.2.613: "Tactic error: cases: hypothesis not in context"
```

Lean 4.33 (checked with lean_run_code): `cases h.2 with | inl a => exact Or.inr a | inr b => exact Or.inl b` succeeds
(`cases` generalizes any term of an inductive type). Workaround: `(have hk := (And.right h)) (cases hk)`.

## rest (pitfalls and observations, no tracker row)

- Java heap exhaustion (-Xmx1g) while elaborating an induction over Rule R's loop whose goal mentioned
  `(rr-loop (cons x f) (rule-r-round w0))` and a `cases` on `(no-orphans (rule-r-round w0))`: the proof never finished.
  Stating the lemma over the round's OUTPUT as a variable (`rr-no-orphans` over `w1`, i1o) and rewriting `rr-loop` by
  small equations (`rr-loop-t`/`rr-loop-f`) avoided it. Not reduced to a minimal repro (suspect: whnf of the `if` in
  `rr-loop` unfolding `rule-r-round` symbolically).
- Copier (model tooling, not ansatz): a bundle whose `:extra-args` names a lemma that the source passes as a VALUE
  (`(nat-fold-inv mark-edge mark-edge-inv-sample ...)`) throws "used as a value"; i1r's GR0 reuses GRX lemmas at `[]`
  through extra-args and generates wrappers for the value-used ones (`gr0-wrap-form`).
- `(fn [c :- CompRow] (rfl))` as an argument failed again (tracker #17); `(Eq.refl (comp-id c))` works.
- `(all_goals ...)` inside a `have` proof reaches the outer goals as well (a `cases` there then fails with "Unknown
  constant"); use `case` blocks.
- `_` world arguments again had to be written out (`gr0-comp-del-free`, `grk-mk`); new names clashed with existing
  lemmas of the same statement (`scan-mem`, `all-true-of`, `any-upd-mono`, `runs-*-edge`, `runs-demote-epoch`: reused)
  or a different one (`listed-arm`, `has-false-ne`, `nz-mem`: renamed with suffix 5).

## z57 (pitfalls; one more instance of tracker #22, no new tracker row)

- Tracker #22 again, with a lemma whose function argument is given explicitly as a lambda: after
  `(have e := (fold8-field (List TaskRow) (fn [q :- World] (:tasks q)) scope-del ...))`, `rw [e]` looks for
  `((fun q => q.tasks) (nat-fold scope-del w sub))` and finds no occurrence of `(:tasks (nat-fold ...))`. Lean's
  `inferType` of the application instantiates the binder with `instantiateBetaRevRange`, so the statement is
  `(nat-fold ..).tasks = w.tasks` and the rewrite succeeds. Workaround: a lemma stated on the projection
  (`tasks-sdel-fold`).
- An `_` predicate argument solved by unification can come back eta-expanded: `(tbl-all-mono X8K _ _ (x8-mono _ _ hs) _ h)`
  had type `tbl-all (fun x => x8 sks2 x) xs = true`, and a later `simp only [.. a2 ..]` did not rewrite the goal's
  `tbl-all (x8 sks2) xs` (the "case body did not close its goals" / unknown-constant symptom of an unfinished `have`).
  Lean's simp matches up to eta (discrimination trees eta-reduce), so this is likely another gap; not reduced to a minimal
  repro. Workaround: wrapper lemmas that state the predicate explicitly (`x8-all-mono`, `r8-esc-all`).
- `(cases (And.right hx))` again (tracker #24): `(have hz := (And.right hx)) (cases hz)`.
- Not gaps (same in Lean): `rw` closes a goal by `rfl`, so a following `simp` errs with "No goals"; `simp only [..] at h`
  leaves `h : false = true` open (close with `(cases h)`); `have e := (lemma _ x y)` whose `_` occurs only under a
  projection of the result cannot be synthesized (pass the fuel explicitly: `(fin-fuel X)`).
- Name clashes again with the skip-free loader: `sok` (progress' slice-ok), `rkeys-keep`, `runs-iec` (identical
  statements: reused). New key structures prefixed `T8K`/`S8K`/`X8K`.
- Model tooling: a bundle patch that rewrites a call to a lemma with the bundle parameter must name the parameter in
  the replacement (`(g8-run-upd x8s w x f hid run-wake-rkey h)`), since `copy-subst` only inserts parameters for heads
  it renames; `override!` dependency lists must name every lemma the override's proof uses that the closure would not
  otherwise reach (`inv-add-run-scope` for `g8-start-raw`).

## z59 (pitfalls, no new gap)

- `Bool.not_eq_true'` is still missing from the bundled Init (tracker #10); case on the Bool instead (`z59-cut-p1`).
- Not gaps (same in Lean): `rfl` does not close `(!(b && false)) = true` for an opaque `b` (`&&` matches on its first
  argument): `simp only [.. Bool.and_false Bool.not_false]`; `Nat.blt_eq` is an equation of Props, so `Nat.blt_eq.mpr`
  does not exist (use `simp only [Nat.blt_eq]`).
- Model tooling (not ansatz): `clj-nrepl-eval` calls that outlive the shell's 180 s foreground limit sometimes never
  reach the REPL (the JVM idle, the client waiting); run long work as a REPL `future` that writes a log and a done
  marker (`bg!`), and poll the log.

## l5b (pitfalls, no new gap filed)

- `_` world arguments had to be written out again (`gd-rest-same w _ ...` in the edge primitives, `gd-add-run-scope _`
  in `gd-spawn-rows`): "Type mismatch in application" until the world was explicit.
- A name clash hidden by the skip-loader: `kw` (lit's world key) vs the watch bundle's predicate; renamed `hkw`.
- `simp only [gdk Bool.and_eq_true]` evaluated the conjunct `Nat.blt 0 (n + 1 + 1)` to `True`, so a following
  `And.intro (And.left p) ..` mismatched; simp with the fact itself instead (`simp only [gdk (And.left p) Bool.true_and]`).
- Not in the bundled Init (not checked against Lean): `Nat.lt_of_blt_eq_true`, `Nat.ble_refl`, `Nat.beq_eq_true_of_eq`
  (local helpers `gd-lt-of`, `gd-ble-refl`, `simp only [Nat.beq_eq]`).
- Copier: an `override!` form is only checked inside `lcopy!`, and a hand-written theorem that uses a COPIED lemma
  (`gd-df` uses `gd-demand-reactive`) must follow an `lcopy!` of that lemma's closure in the file; a REPL session that
  ran `lcopy-try!` first hides this (fresh-load before committing).
- Recipe (with #16/#21): bisect a failing proof by evaluating its tactic prefixes as fresh theorems and reporting the
  first prefix whose error is not "Proof incomplete" (`bisect!`, scratch); nested `case` blocks count as one step, so
  flatten with `case'` first.

## hm (pitfalls; one observation without a minimal repro)

- A theorem that FAILED to elaborate under a name (here a copier attempt of `hmk-fire-wait-act`) made a later, correct proof
  under the SAME name fail with "Type mismatch in application", while the identical form under a fresh name proved
  (`hmk-fire-wait-act-x`). A trivial repro (fail then succeed under one name, `(exact (Nat.add_zero ..))`) does not
  reproduce, so the trigger is something the failed proof created (suspect: `cases` on an Option/`match` auxiliaries keyed by
  the theorem name). Not filed. Recipe: test overrides under fresh names (`ov-bisect!`, scratch), then reset the env to the
  pre-namespace snapshot and reload before trusting a failure list.
- The skip-loader (`ld!`, skips declared names) silently keeps a theorem's OLD statement when the statement is edited: a
  premise change of `hmk-remove-edge` surfaced only as "Type mismatch in application" at its users. Reset after any
  statement change.
- `Exists.intro w proof` failed with "Type mismatch in application" where the expected type is `(fun r => ..) w` (beta,
  tracker #22 family); restated with Bool `tbl-any` + `any-elim`/`any-elim-of` instead (`hk-cone-edge`).
- `simp only [List.append_nil]` does not rewrite `List.append Nat xs (List.nil Nat)` (simp states it with `++`, cf. the
  retain recipe): a local `hk-append-nil` by induction.
- `rw [k1]` with `k1 : (:kind e) = ek-wait` closed `Nat.beq ek-wait ek-dep = false` by rfl, so a following `(rfl)` failed
  ("rfl: sides are not definitionally equal" on the next goal); same in Lean, not a gap.
- After `(cases m)` on `List.Mem r (h :: t)` without `case` blocks, a later tactic referring to the variable `r` failed with
  "Unknown constant: r" (the head goal substitutes r := h; the goal order was not the expected one); `case [head]` /
  `case [tail m2]` blocks fixed it (`hk-tgt-mem`).

## i14: `exact (Exists.intro x proof)` does not take the implicit arguments from the expected type (tracker #25)

```clojure
(a/theorem ex-t1 [n :- Nat] (Exists (fn [m :- Nat] (= m n))) (exact (Exists.intro n (Eq.refl n))))
;; ansatz 0.2.613: "Elaboration error: Type mismatch"
(a/theorem ex-t2 [n :- Nat] (Exists (fn [m :- Nat] (= m n))) (apply (Exists.intro n)) (rfl))            ;; proved
(a/theorem ex-t3 [n :- Nat] (Exists (fn [m :- Nat] (= m n))) (exact (Exists.intro Nat (fn [m :- Nat] (= m n)) n (Eq.refl n))))  ;; proved
```

Lean 4.33 (checked with lean_run_code): `example (n : Nat) : ∃ m, m = n := by exact Exists.intro n (Eq.refl n)`
succeeds (α and p are implicit and unified with the goal). Workaround used in spindel.v2.i14 (`vsucc-mem`,
`idle-row-c`): `(apply (Exists.intro x))` then `(exact ..)`.

## i14 (pitfalls, no new tracker row)

- Bundle parameter names clashed again with source binder names (`xs` of `nat-fold-inv` against a bundle
  parameter `xs`: "Type mismatch in application" in the copy); the bundles use `zq9 zw9 zs9` / `zd9 zr9`.
- An extra-args hypothesis inserted BEFORE the inv-sample premise cannot be checked when the call site
  passes `_` for the world and the edge (`(inv-insert-edge-checked _ _ h)`: `(Eq.refl true)` is checked against
  `dnaq14 .. ?w ?e` before `h` fixes them); putting the extra hypothesis LAST (position after `h`) fixes it.
- `(cases hf (comp-find w p))` also rewrites `comp-find w p` in an `Exists` goal (Lean's `cases h : e`): the
  witness equation is then `(Eq.refl (Option.some T c))`, not `hf`.
- `rfl` did not close `dnaq14 xq cs (EdgeRow.mk 0 ek-wait ..) = true` after `simp only [await-edge hd]`, while
  `(simp [dnaq14 await-edge hd ek-wait ek-dep])` did; not reduced to a minimal repro.
- `rw [ly]` closed the goal by rfl and a following `(rfl)` failed on the next goal (as noted in z55/z57).
- Debug recipe (with #16/#21): flatten a failing `case` block along a path of tactic indices and print the
  goal of a prefix (`goal-at`, scratch boot.clj), or bisect inside it (`bisect-in!`).

## hm2 (pitfalls; one candidate gap to confirm against Lean)

- `simp only [..] at h` that turns `h` into `false = true` (e.g. `(simp only [gd-ncur gdkey o2 hc3 hal Bool.and_self
  Bool.not_true] at nq)`) leaves the goal open with `nq : false = true`; a following `(cases nq)` closes it. Lean 4.33.1's
  `simp only` runs the default simprocs (`reduceCtorEq`), which rewrite `false = true` to `False` and close the goal. Not
  filed yet (no minimal repro run against Lean in this branch); workaround `(cases h)` after the simp. Same for
  `(simp only [run-current-of hq] at rc)`.
- `Bool.and_eq_false_iff`, `Bool.not_eq_false'` are not in the bundled Init (tracker #10 family); case splits on the conjuncts
  instead, and `bnot-false` (edits) for `(!b) = false`.
- "Type mismatch in application" again where several `_` stand for worlds/lists that only unification of a lambda argument
  could determine (`(hmk-intro (List.append ..) _ (hmk-sample _ _ h1) ...)`, `(all-of-mem EdgeRow _ _ (fn ...))`, `hmk-dis`
  with a `fn` returning `Or.inr (Or.inr ..)`): spelling the worlds out, or `apply` + `intros` instead of a `fn` argument,
  fixed every instance (l5b pitfall).
- After `(cases hf (comp-find w x))`, hypotheses that mention `comp-find w x` (here inside an `Option.rec` from a `match`) are
  not rewritten (as in Lean: `cases h : e` generalizes the goal only); `(rw [hf] at hc2)` then `exact` with the reduced type.
- `rw [e]` with `e : (edge-id e2) = x` (from `Nat.eq_of_beq_eq_true` on a `hk-sq edge-id ..` conjunct) finds no `(:id e2)`:
  restate as `(have i2 (= (:id e2) x)) (exact ..)` first (projection vs. the named `edge-id` function, cf. gap #9).
- Recipe: a Python paren checker over the scratch file (top-level forms start at column 0) found every unbalanced `case`
  block before the reader did; ansatz/Clojure reader errors only name the form after which reading failed.

## hm3 (pitfalls, no new gap filed)

- "Type mismatch in application" again when a lemma with several universally quantified hypotheses got them as inline
  `fn` arguments (`h3r-comp-upd`); stating each as a `have` first and passing the names proved it (l5b/hm2 family).
- The skip-loader (forms whose names are declared are skipped) leaves no Clojure var for an `a/defn` of a removed
  namespace; the next `a/defn` whose body calls it fails to compile ("No such var"). Recipe: intern stub vars for the
  declared defns before loading later forms (REPL only), or rebuild the env.
- Rebuilding the env in the same JVM: `(reset! ansatz.core/ansatz-env nil)` then `(a/load-init!)` gives a fresh Init env
  (`load-init!` on an existing env with the same manifest keeps it), then `(require 'spindel.v2.hmk2 :reload-all)`
  (about 4 minutes) and a snapshot before the new namespace; this avoids giving up a JVM slot.
- `rw [e1 e2]` where `e2`'s left side is a projection of a structure built by a function (`(:of (rk3 r))`) failed after
  `e1` had exposed the reduced projection `(:of r)` ("Did not find an occurrence"); `(exact (Eq.trans e1 e2))` works.
- An `induction` after `intros` of hypotheses that mention the induction variable did generalize them in a minimal test;
  the failing `h3-cur-inc` was a simp-at-a-hypothesis issue, so no gap (checked before filing).

## hm4 (pitfalls, no new gap filed)

- `tbl-all-mono` with `_ _` for the predicates infers the target as an eta-expanded lambda (`(fun c => ar-c (f r) c)`), which a
  later `simp only [.. t ..]` cannot use as a rewrite of `(tbl-all (ar-c (f r)) cs)`: state the `have` with its type
  (`(have t (= (tbl-all (ar-c (f r)) cs) true)) (exact (tbl-all-mono ..))`).
- Inline `fn` arguments again gave "Type mismatch in application" (`h3-edge-upd-m` with a `fn` for the armed side condition,
  `h3-freeb-frame` with a `fn` for currency): a named `have` fixed both (hm3 family).
- `(simp only [rk3] at l)` fails with "no progress" when an earlier `simp at` already reduced the projections of `(rk3 r)`;
  `(try (simp only [rk3] at l))` keeps the proof robust.
- Debugging recipe: `ansatz.tactic.repl/goal-at` with the a/theorem's params, statement and a FLAT tactic list (no `case`
  blocks: after `(cases h e)` use `(rename_i x)` on the goal that introduced a variable) prints the goal state; the
  `case body did not close its goals` error itself names no goal.
- The env is append-only: a lemma whose statement changes must get a new name in the REPL (`ar-run-upd` -> `ar-run-upd-a`).

## hm5: `rw [f]` with a definition name fails (tracker #27); pitfalls

- Gap (tracker #27): `rw` with a definition name. Repro (Init only, ansatz 0.2.613):
  `(a/defn chk [b :- Bool, n :- Nat] Nat (if b (+ n 1) n))`, `(a/theorem rp2 [n :- Nat] (= (chk true n) (+ n 1)) (rw [chk]))`
  -> "rewrite: lemma is not (∀ …, _ = _ / _ ↔ _)". Lean 4 v4.33.1: `example : chk true n = n + 1 := by rw [chk]; simp`
  is accepted (`rw` unfolds by the equation lemma). Workaround: `simp only [f]`.
- Pitfall (no gap): `(rw [e]) (rfl)` failed with "sides are not definitionally equal" on `(= (rk3 r) (rk3 (run-arm z r)))`
  inside a long proof, while the minimal repro (`rk r = rk (arm z r)` by `rfl`) is accepted by ansatz as by Lean; the
  in-proof goal after `rw` was likely not the one expected. `(simp only [rk3 run-arm])` closes it.
- `simp only [h3-fa h3-fr]` does not unfold `h3-fr` when it occurs partially applied under `tbl-all` (the predicate
  argument); prove the pointwise equation (`(simp only [h3-fr]) (rw [e])` per row) and use `tbl-all-congr`.
- A `have` stated over `(:runs W)` where `W` is a projection-heavy composite: `simp only [h3-rest]` already reduces
  `(:acts (set-acts w ...))`, so a following `rw [e2]` on the projection fails; state the target equation explicitly
  (`e3 : tbl-all P (tbl-ins a as) = Bool.and (P a) (tbl-all P as)` by `rfl`) and `rw` with it.
- `tbl-all-upd` with `_` for P/Q and an inline-typed `hin` gave "Type mismatch in application" (higher-order
  unification); name the predicate with an `a/defn` (`h3-ridk`) and pass it explicitly (hm3/hm4 family).
- Passing a bundle lemma as a function argument needs its leading bundle parameter applied: `(h3-drop-act-nc xm)`.
- After `(cases hxx (reach-mem y xm))` the goal holds `false` in place of the term; in the `false` branch a fact about
  `reach-mem x xm` must be split (`cases`) rather than matched against the goal.
- Paren counts in hand-edited nested `case` blocks: an extra `)` silently ends the theorem early and the rest is read as
  junk forms, surfacing only as "case body did not close its goals". A flattening goal probe (`case` -> `case'`) misaligns
  goals; probe by stating the sub-step as its own lemma instead.
- REPL vs file: `lcopy-try!` in the REPL registers copies (`hm3-take-now`, `hm3-arm-raw`, ...) that a file load lacks;
  add the `lcopy!` calls to the file and check the namespace standalone (`clojure -M:test -n <ns>-test`).
