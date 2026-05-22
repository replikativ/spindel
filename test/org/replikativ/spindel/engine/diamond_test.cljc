(ns org.replikativ.spindel.engine.diamond-test
  "Regression: a single-parent diamond must re-run each node exactly once
  per signal change.

  Diamond shape — signal `S`; spin `C` tracks `S`; spin `P` tracks `S`
  AND awaits `C`. So `P` depends on `S` by two paths: directly, and
  transitively through `C`.

  The bug: on an `S` change the `:signal-change` handler dispatched `P`
  twice — once from `direct-observers` (P directly tracks S) and once
  from `roots-to-execute` (C is awaited by P, so C escalates to its
  root, which is P). The two sets could overlap with no dedup, so `P`
  re-ran twice, and each P-run re-awaited a dirty `C`, so `C` re-ran
  twice too. Final values were always correct — the cost was a
  redundant re-run per change.

  The fix excludes escalation-root spins from `direct-observers`, so a
  spin that is both a direct observer and an escalation root is resumed
  once (via the escalation path — the same continuation either way)."
  (:require #?(:clj [clojure.test :refer [deftest is testing]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]))

#?(:clj
   (deftest single-parent-diamond-runs-each-node-once-per-change
     (testing "S → C (tracks S); P (tracks S, awaits C). Each signal change
              must re-run C and P exactly once — not twice via the
              direct-observer / escalation-root overlap."
       (let [ctx-root (ctx/create-execution-context)
             c-runs (atom 0)
             p-runs (atom 0)]
         (try
           (binding [ec/*execution-context* ctx-root]
             (let [s (sig/signal 1)
                   c (spin (let [{v :new} (track s)]
                             (swap! c-runs inc)
                             (* v 10)))
                   p (spin (let [{v :new} (track s)
                                 cv (await c)]
                             (swap! p-runs inc)
                             [v cv]))]
               (is (= [1 10] @p) "initial value")
               (simple/await-drain-complete! ctx-root :timeout-ms 3000)
               (is (= 1 @c-runs) "C runs once initially")
               (is (= 1 @p-runs) "P runs once initially")

               (reset! s 2)
               (simple/await-drain-complete! ctx-root :timeout-ms 3000)
               (is (= [2 20] @p) "value correct after first change")
               (is (= 2 @c-runs) "C re-runs exactly once per change (not twice)")
               (is (= 2 @p-runs) "P re-runs exactly once per change (not twice)")

               (reset! s 3)
               (simple/await-drain-complete! ctx-root :timeout-ms 3000)
               (is (= [3 30] @p) "value correct after second change")
               (is (= 3 @c-runs) "C: one re-run per change")
               (is (= 3 @p-runs) "P: one re-run per change")))
           (finally
             (ctx/close-context! ctx-root)))))))
