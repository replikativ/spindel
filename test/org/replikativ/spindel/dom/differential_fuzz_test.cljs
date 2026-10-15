(ns org.replikativ.spindel.dom.differential-fuzz-test
  "Differential DOM fuzzer on a REAL jsdom tree.

   The gap this closes. `consistency_test` compares VDOM, and the JVM render
   tests read `MockDischarge`'s op log — neither can say what is attached
   (see `jsdom_final_state_test`'s docstring for why the op log cannot). Here
   every check is on the DOM the real `DOMDischarge` built.

   One trial: a random program (`dom/differential_fuzz.cljc` — nested spins
   tracking signals at the top, keyed ifor-each, conditional subtrees and
   roots, awaits on deferreds) is mounted, then a random op sequence runs
   against its signals and deferreds: flips, inserts/deletes/moves/updates in
   keyed lists, deliveries in random order, `:tick` (one event-loop task of
   partial progress) and `:settle` (an observation point). At every
   observation point, once the engine is QUIESCENT:

     (a) DIFFERENTIAL — the incrementally updated mount equals a FRESH mount
         of the same state in a NEW execution context (canonical form:
         tags, sorted attributes, merged text). Checked whenever every
         deferred the program awaits has been delivered; before that a
         stale frame is retained by design.
     (b) KEY IDENTITY — an ifor-each item root (stamped `data-fk` = for-node
         id + key path) present at the previous point and now is the SAME DOM
         node, unless something in the step could legitimately have unmounted
         it: an ancestor `:if`'s signal flipped, or the item's key (or an
         enclosing item's key) was deleted.
     (c) INTEGRITY — no `::addr-collision` / `::commit-unbound-addr` was
         recorded, no render spin rejected, nothing logged at :error.
     (d) MOUNT REFS (R5) — every element carries a probe `:ref`. Each mount
         call finds its element `.isConnected` and is that element's first;
         every element in the container (incremental and fresh mount) has
         had one.

   Quiescence is coordination, not a delay: `settle!` yields one event-loop
   task at a time (the EventLoopExecutor's own unit of work) until the
   context reports `events-settled?` AND its state value is IDENTICAL across
   a full task — nothing ran. A context that never settles is reported as a
   failure (livelock), never waited out.

   Running it — the focused `:dom-fuzz` build compiles only these
   namespaces (plus the pinned regressions) and what they require:

     npx shadow-cljs compile dom-fuzz
     node target/dom-fuzz.js

   It also runs as part of the `:ci` / `:test` builds (`-test$`). A trial
   takes ~40-70 ms. Every stopped context of a trial stays reachable (open
   defect 4 in the regressions namespace), ~0.2 MB per trial: keep long
   runs to a few thousand trials per process and cap node's heap on shared
   machines (`node --max-old-space-size=2048 target/dom-fuzz.js`).

   Knobs (environment variables):

     SPINDEL_FUZZ_TRIALS   trials per run           (default 40)
     SPINDEL_FUZZ_SEED     test.check seed, or `random`
                           (default: fixed — see `default-seed`)
     SPINDEL_FUZZ_SIZE     max generator size       (default 30)
     SPINDEL_FUZZ_SHRINKS  max shrink evaluations   (default 400)
     SPINDEL_FUZZ_VERBOSE  1 = print seed + coverage counts
     SPINDEL_FUZZ_PROFILE  comma-separated generator changes (see
                           `fz/normalize`): `unkeyed` (item roots without
                           :key) and `siblings` (fragments beside sibling
                           nodes) go OUTSIDE the documented ifor-each
                           contract; `no-await` drops deferred awaits

   A failure report carries the seed, the shrunk program printed as the
   spindel code it stands for, the shrunk initial state and op sequence, and
   the minimal case as EDN — paste that EDN into
   `differential_fuzz_regressions_test.cljs` to pin it."
  (:require [cljs.test :refer-macros [deftest is async]]
            [clojure.string :as str]
            [org.replikativ.spindel.dom.differential-fuzz-harness :as h]
            [org.replikativ.spindel.engine.core :as ec]))

;; =============================================================================
;; Knobs
;; =============================================================================

(defn- env-int [k default]
  (let [v (some-> js/process .-env (aget k))]
    (if (seq v) (js/parseInt v 10) default)))

(def ^:private default-seed
  "Fixed by default, so the suite is reproducible: the generator reaches
   OPEN defects (differential_fuzz_regressions_test) at a low rate, and a
   time-based seed would make CI fail on them at random. Explore with
   SPINDEL_FUZZ_SEED=random and many trials."
  20261015)

(defn- knobs []
  {:trials (env-int "SPINDEL_FUZZ_TRIALS" 40)
   :seed (let [v (some-> js/process .-env (aget "SPINDEL_FUZZ_SEED"))]
           (cond (= v "random") (.now js/Date)
                 (seq v) (js/parseInt v 10)
                 :else default-seed))
   :max-size (env-int "SPINDEL_FUZZ_SIZE" 30)
   :max-shrinks (env-int "SPINDEL_FUZZ_SHRINKS" 400)
   :verbose? (= 1 (env-int "SPINDEL_FUZZ_VERBOSE" 0))
   :profile (let [v (some-> js/process .-env (aget "SPINDEL_FUZZ_PROFILE"))]
              (into #{} (map keyword) (when (seq v) (str/split v #","))))})

;; =============================================================================
;; The property
;; =============================================================================

(deftest incremental-dom-equals-fresh-mount
  (async done
         (let [k (knobs)
               saved-ctx ec/*execution-context*]
           (-> (h/quick-check-async k)
               (.then (fn [r]
                        (set! ec/*execution-context* saved-ctx)
                        (when (:verbose? k)
                          (println "differential fuzz:" (pr-str (select-keys r [:seed :trials]))
                                   (pr-str @h/coverage)))
                        (is (:pass? r) (if (:pass? r) "" (h/report r)))
                        (done))
                      (fn [e]
                        (set! ec/*execution-context* saved-ctx)
                        (is false (str "fuzz driver threw: " (.-message e) "\n" (.-stack e)))
                        (done)))))))
