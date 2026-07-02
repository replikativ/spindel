(ns org.replikativ.spindel.ygg-convergent-fork-test
  "Branch-based convergent forks: a convergent CRDT ygg-signal forks as a REAL yggdrasil
   BRANCH (inherits the parent tip), so the NATURAL API works inside a fork — `@kref` reads
   the actual set, `swap! + g/conj` writes, `merge-fork!` folds back — with none of the
   `:following`-overlay footguns (empty-delta reads, Overlay write NPE, merge fn-seating).
   Overlays remain reachable via `:convergent-fork :overlay`.

   JVM-only for now: durable `branch!`/`checkout` are async on cljs and the engine's
   `fork-context` is synchronous, so durable branch-fork is JVM-first until the async
   fork-context lift lands (the in-mem ConflictFreeSystem forks sync on both platforms)."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [yggdrasil.convergent.gset :as g]
            [yggdrasil.convergent.overlay :as ovl]
            [yggdrasil.convergent.cdvcs :as cdvcs]))

(defn- mem-gset [id]
  (g/gset id {:store-config {:backend :memory :id (random-uuid)}} {:sync? true}))

(deftest convergent-branch-fork-roundtrip-natural-api
  (testing "a durable G-Set forks as a branch; @kref inherits, g/conj writes, merge folds"
    (let [ctx (sp/create-execution-context)]
      (sp/with-context ctx
        (let [kref (ygg/register! (-> (mem-gset "kb") (g/conj :shared)))
              fh   (ygg/fork!)]
          (ygg/with-fork fh
            (is (= #{:shared} (g/elements @kref))
                "fork inherits the parent tip via branch! (natural @kref read)")
            (swap! (ygg/system-signal "kb") (fn [s] (g/conj s :fork-fact)))
            (is (= #{:shared :fork-fact} (g/elements @kref))
                "natural swap!+g/conj write works on the fork branch"))
          (is (= #{:shared} (g/elements @kref)) "parent isolated during the fork")
          (ygg/merge-fork! fh)
          (is (= #{:shared :fork-fact} (g/elements @kref))
              "merge-fork! folds the fork's write into the parent (natural read)"))))))

(deftest convergent-fork-discard-drops-branch
  (testing "discard-fork! abandons the fork without touching the parent"
    (let [ctx (sp/create-execution-context)]
      (sp/with-context ctx
        (let [kref (ygg/register! (-> (mem-gset "kb") (g/conj :shared)))
              fh   (ygg/fork!)]
          (ygg/with-fork fh
            (swap! (ygg/system-signal "kb") (fn [s] (g/conj s :discarded))))
          (ygg/discard-fork! fh)
          (is (= #{:shared} (g/elements @kref)) "parent unchanged after discard"))))))

(deftest convergent-fork-overlay-opt-still-works
  (testing ":convergent-fork :overlay forces the live-:following overlay path; merge still folds"
    (let [ctx (sp/create-execution-context)]
      (sp/with-context ctx
        (let [kref (ygg/register! (-> (mem-gset "kb") (g/conj :shared)))
              fh   (ygg/fork! {:convergent-fork :overlay})]
          (ygg/with-fork fh
            (is (ovl/overlay? @(ygg/system-signal "kb"))
                "under :overlay the signal holds an Overlay, not a branched system")
            (ovl/overlay-swap! @(ygg/system-signal "kb") (fn [s] (g/conj s :ov-fact))))
          (ygg/merge-fork! fh)
          (is (= #{:shared :ov-fact} (g/elements @kref))
              "overlay merge folds into the parent (relies on merge-down! :sync? fix)"))))))

(deftest non-branchable-convergent-fork-fails-loud
  (testing "forking a cdvcs (convergent, :branchable false, no Overlayable) throws clearly, not NPE"
    (let [ctx (sp/create-execution-context)]
      (sp/with-context ctx
        (ygg/register! (cdvcs/cdvcs "cd" {:store-config {:backend :memory :id (random-uuid)}} {:sync? true}))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"neither :branchable"
                              (ygg/fork!)))))))
