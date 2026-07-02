(ns org.replikativ.spindel.ygg-convergent-fork-portable-test
  "PORTABLE proof (JVM + cljs/node) that a DURABLE convergent-CRDT ygg-signal forks
   as a REAL yggdrasil BRANCH — the payoff of the Design-B `async+sync` lift of the
   spindel↔yggdrasil bridge.

   TWO deftests, two regimes:

   1. `convergent-branch-fork-portable` — the SYNC branch (`{:sync? true}`). In-memory
      konserve reads synchronously on cljs (a plain `Iter`, no async-seq), so the WHOLE
      flow runs the bridge's SYNC branch and exercises the CLJS-SPECIFIC new logic the
      JVM never runs: `fork-value` DEFERS on cljs (`#?(:cljs this)`) and `fork!`'s
      post-pass branches the convergent system. A raw `binding` is valid here because no
      op suspends.

   2. `convergent-branch-fork-async-through-spin` — the ASYNC continuation, driven THROUGH
      A SPIN so the ENGINE conveys `*execution-context*` across the suspending durable
      awaits. `fork!`/`merge-fork!` run `{:sync? false}` (a partial-cps CPS on cljs, and a
      FOREIGN konserve thread on the JVM — so the JVM exercises the real async path too,
      no browser needed). This SUPERSEDES the sync test's async gap: it proves the natural
      fork API (`@kref` inherits, `g/conj` writes, `merge-fork!` folds) works fully async.

      The load-bearing bridge fix (`org.replikativ.spindel.yggdrasil/convey-context`):
      spindel EXCLUDES `*execution-context*` from partial-cps binding capture (it is
      re-bound only by the engine on spin resume — see `engine/bindings.cljc`). So a raw
      `(async … (await (fork!)) … @kref …)` loses the context after the suspending await.
      `convey-context` wraps each durable bridge op's resolve/reject to re-bind the
      captured context, carrying it into the awaiting spin's continuation — so the
      natural reads/writes AFTER an `await` resolve against the right context."
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.test-async :refer [deftest-async]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
            #?(:clj  [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [yggdrasil.convergent.gset :as g])
  #?(:cljs (:require-macros [org.replikativ.spindel.test-async :refer [deftest-async]]
                            [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.test-helpers :refer [async with-ctx]])))

(deftest-async convergent-branch-fork-portable
  (testing "SYNC branch: a durable G-Set forks as a branch on BOTH platforms; @kref inherits, g/conj writes, merge folds"
    (let [ctx (sp/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [g1   (-> (g/gset "kb" {:store-config {:backend :memory :id (random-uuid)}} {:sync? true})
                       (g/conj :shared {:sync? true}))
              kref (ygg/register! g1)
              fh   (ygg/fork! {:sync? true})]
          ;; INSIDE the fork — @kref resolves against the fork's child context. On cljs,
          ;; fork-value DEFERRED (returned the parent value) and fork!'s post-pass branched
          ;; the convergent system; on the JVM fork-value branched it directly.
          (binding [ec/*execution-context* (:child-ctx fh)]
            (is (= #{:shared} (g/elements @kref {:sync? true}))
                "fork inherited the parent tip via branch! (natural @kref read)")
            (reset! (ygg/system-signal "kb") (g/conj @kref :fork-fact {:sync? true}))
            (is (= #{:shared :fork-fact} (g/elements @kref {:sync? true}))
                "natural conj write works on the fork branch"))
          ;; the parent is isolated during the fork
          (is (= #{:shared} (g/elements @kref {:sync? true}))
              "parent isolated during the fork")
          ;; fold the fork back
          (ygg/merge-fork! fh {:sync? true})
          (is (= #{:shared :fork-fact} (g/elements @kref {:sync? true}))
              "merge-fork! folds the fork's write into the parent (natural read)"))))))

(deftest convergent-branch-fork-async-through-spin
  ;; ASYNC continuation, driven THROUGH A SPIN. `fork!`/`merge-fork!` are `{:sync? false}`
  ;; — a real suspending durable op (foreign konserve thread on the JVM, a later microtask
  ;; on cljs). The engine conveys *execution-context* across the awaits via the bridge's
  ;; `convey-context`, so the NATURAL fork API works after each suspend.
  (async done
         (with-ctx [ctx]
           (let [g1   (-> (g/gset "kb" {:store-config {:backend :memory :id (random-uuid)}} {:sync? true})
                          (g/conj :shared {:sync? true}))
                 yref (ygg/register! g1)
                 flow (spin
                       (let [;; SUSPENDING durable branch-fork (async path)
                             fh        (await (ygg/fork! {:sync? false}))
                         ;; inside the fork: read inherited tip, write a fork-only fact.
                         ;; ctx conveyed by the bridge → binding the child ctx resolves @yref there.
                             in-fork   (binding [ec/*execution-context* (:child-ctx fh)]
                                         (let [inherited (g/elements @yref {:sync? true})]
                                           (reset! (ygg/system-signal "kb")
                                                   (g/conj @yref :fork-fact {:sync? true}))
                                           [inherited (g/elements @yref {:sync? true})]))
                         ;; back in the parent continuation (ctx conveyed by fork!): parent isolated
                             parent-iso (g/elements @yref {:sync? true})
                         ;; SUSPENDING durable merge (conflict pre-check runs — no :force)
                             _          (await (ygg/merge-fork! fh {:sync? false}))
                             merged     (g/elements @yref {:sync? true})]
                         {:inherited (first in-fork) :fork-after (second in-fork)
                          :parent-iso parent-iso :merged merged}))]
             (run-spin! flow
                        (fn [r]
                          (is (= #{:shared} (:inherited r))
                              "fork inherited the parent tip via branch! (async, @yref read after suspend)")
                          (is (= #{:shared :fork-fact} (:fork-after r))
                              "g/conj write visible in the fork branch (async)")
                          (is (= #{:shared} (:parent-iso r))
                              "parent isolated during the fork (async continuation on parent ctx)")
                          (is (= #{:shared :fork-fact} (:merged r))
                              "merge-fork! folds the fork write into the parent (async, after conflict pre-check)")
                          (done))
                        (fn [e]
                          (is false (str "async fork/merge spin rejected: " e))
                          (done)))))))
