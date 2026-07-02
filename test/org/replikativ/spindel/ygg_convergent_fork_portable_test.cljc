(ns org.replikativ.spindel.ygg-convergent-fork-portable-test
  "PORTABLE proof (JVM + cljs/node) that a DURABLE convergent-CRDT ygg-signal forks
   as a REAL yggdrasil BRANCH on cljs too — the payoff of the Design-B `async+sync`
   lift of the spindel↔yggdrasil bridge.

   WHY SYNC MODE ON CLJS (`{:sync? true}`): the bridge is now `async+sync`, so on cljs
   its ops CAN return a partial-cps continuation. But DRIVING that async path across an
   internal durable await needs `*execution-context*` bound through the resume — and
   spindel deliberately re-binds the context only via its ENGINE (spin resume),
   EXCLUDING it from raw partial-cps binding capture (see engine/bindings.cljc). A raw
   `binding`/`set!` does NOT survive a partial-cps await; a durable async drain
   (`g/elements`) even spawns spins that read the context mid-drain. So the async path
   with internal awaits is a spin/engine concern (a higher layer). Here we pin
   `{:sync? true}` — in-memory konserve reads synchronously on cljs (a plain `Iter`,
   no async-seq) — which runs the bridge's SYNC branch and, crucially, exercises the
   CLJS-SPECIFIC new logic that the JVM never runs: `fork-value` DEFERS on cljs
   (`#?(:cljs this)`) and `fork!`'s post-pass branches the convergent system. `binding`
   is valid here precisely because no op suspends. (The async CPS branch itself is
   compile-validated on cljs, and `ygg-bridge-portable-test` runs it at runtime for a
   no-internal-await system.)"
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [org.replikativ.spindel.test-async :refer [deftest-async]]
            [clojure.test :refer [is testing]]
            [yggdrasil.convergent.gset :as g])
  #?(:cljs (:require-macros [org.replikativ.spindel.test-async :refer [deftest-async]])))

(deftest-async convergent-branch-fork-portable
  (testing "a durable G-Set forks as a branch on BOTH platforms; @kref inherits, g/conj writes, merge folds"
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
