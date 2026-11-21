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

Files: `dump.clj` (model to EDN), `renames.clj` (map, checks, dry run, `--apply`), `lex.clj`
(whole-symbol lexer), `scope.clj` (locals and constructors), `fingerprint.clj`, `compare.clj`,
`stale.clj`.
