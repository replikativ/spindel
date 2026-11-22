# Naming pass: how to rerun it

Everything is driven by `rules.edn` (the names) and `generator-edits.edn` (lines that build names
from strings). To change a name, edit `rules.edn` and rerun from the commit before the
substitution.

All commands from `formal/`. JVM steps go through `~/Development/ansatz/.internal/scripts/jvm-slot.sh run --`.

1. On the tree BEFORE the substitution (the commit "names as reviewed …", or 53258048 plus the
   current `dev/naming`):

       clojure -Sdeps '{:aliases {:nm {:jvm-opts ["-Xmx1g" "-Xss16m"]}}}' -M:nm dev/naming/dump.clj dev/naming/out/model.edn
       clojure -Sdeps '{:aliases {:nm {:jvm-opts ["-Xmx1g" "-Xss16m"]}}}' -M:nm dev/naming/fingerprint.clj dev/naming/out/fp-old.edn

   Both load the whole model (about 10 to 12 minutes each). They do not depend on the rules, so they
   are needed once per base commit; `dev/naming/out/` is not tracked.

2. The map, its checks and the dry run (babashka, under two minutes):

       bb dev/naming/renames.clj            # writes notes/renames.edn and dev/naming/out/report.txt

   It must print `problems 0`.

3. The substitution (writes src/, test/, README.md, notes/):

       bb dev/naming/renames.clj --apply
       bb dev/naming/stale.clj              # no old name left

   To redo it, first `git checkout -- src test README.md notes` on the pre-substitution commit.
   Do not run `renames.clj` without `--apply` on a substituted tree: it reads the declarations
   from the sources.

4. The gate:

       clojure … dev/naming/fingerprint.clj dev/naming/out/fp-new.edn     # loads the renamed model
       bb dev/naming/compare.clj dev/naming/out/fp-old.edn dev/naming/out/fp-new.edn
       clojure -M:test

   `compare.clj` maps the old names through `notes/renames.edn` and expects the same constants
   with the same fingerprints. A load error names a constant the substitution did not reach: a
   name built from strings (add a generator edit) or a local read as a global (scope.clj).

After the pass (a deletion, a refactor, a later rename): dump the fingerprints before and after the
change and compare them constant by constant,

       bb dev/naming/delta.clj dev/naming/out/fp-before.edn dev/naming/out/fp-after.edn [MAP.edn]

It lists what was removed, added and changed and checks the headline theorems. `compare.clj` is for
the substitution itself (it maps the old names through `notes/renames.edn`).

Files: `dump.clj` (model to EDN), `renames.clj` (map, checks, dry run, `--apply`), `lex.clj`
(whole-symbol lexer), `scope.clj` (locals and constructors), `fingerprint.clj`, `compare.clj`,
`delta.clj`, `stale.clj`.

## State (2026-11-21)

Commits on `formal/naming`: rules and tooling, generator edits, the substitution, the exposition,
then one follow-up that (a) replaces old names written in the possessive in prose (`raw0's`), which
the lexer had skipped, and (b) fixes the two regexes over names in `test/spindel/v2/pres/tree_test.clj`
(generator edits). With the current `dev/naming`, `renames.clj --apply` on the pre-substitution tree
gives the substitution commit plus that follow-up in one step (checked: the only difference from the
branch head is the exposition commit). `bb dev/naming/stale.clj --fix` replaces whatever `stale.clj`
still lists.

Gate at the head: 22,033 constants before and after, fingerprints identical, 9,709 predicted
generated names present, 310 tests / 208,521 assertions, 0 failures. Nothing pushed.
