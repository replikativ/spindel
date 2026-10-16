(ns org.replikativ.spindel.ygg-convergent-fork-test
  "Branch-based convergent forks: a convergent CRDT ygg-signal forks as a REAL yggdrasil
   BRANCH (inherits the parent tip), so the NATURAL API works inside a fork — `@kref` reads
   the actual set, `swap! + g/conj` writes, `merge-fork!` folds back — with none of the
   `:following`-overlay footguns (empty-delta reads, Overlay write NPE, merge fn-seating).
   Overlays remain reachable via `:convergent-fork :overlay`.

   JVM-flavoured suite (uses `with-fork` + `swap!`, both JVM-only): the bridge fork/merge
   fns are now `async+sync`, so durable branch-fork ALSO works on cljs (the engine's
   `fork-context` stays synchronous; the async lives in `fork!`'s awaited post-pass +
   the merge/discard loops). The cross-platform proof lives in
   `ygg-convergent-fork-portable-test` (a `.cljc` `deftest-async` exercising the real
   cljs async path); this JVM suite keeps the ergonomic sync surface."
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

(deftest a-fork-that-merged-a-nested-fork-merges-everything
  (testing "outer overlay fork, inner fork of it: inner merges into outer, outer into root, both land"
    (let [ctx (sp/create-execution-context)]
      (sp/with-context ctx
        (let [kref (ygg/register! (-> (mem-gset "kb") (g/conj :shared)))
              outer (ygg/fork! {:convergent-fork :overlay})]
          (ygg/with-fork outer
            (ovl/overlay-swap! @(ygg/system-signal "kb") (fn [s] (g/conj s :outer)))
            (let [inner (ygg/fork! {:convergent-fork :overlay})]
              (ygg/with-fork inner
                (ovl/overlay-swap! @(ygg/system-signal "kb") (fn [s] (g/conj s :inner))))
              (ygg/merge-fork! inner))
            (is (ovl/overlay? @(ygg/system-signal "kb"))
                "the outer fork still holds its overlay after absorbing the inner one")
            ;; a :following overlay's writable system holds the fork's own writes
            (is (= #{:outer :inner} (g/elements (ovl/overlay-system @(ygg/system-signal "kb"))))
                "the inner write joined the outer fork's own writes"))
          (is (= #{:shared} (g/elements @kref)) "the root is untouched until the outer merge")
          (ygg/merge-fork! outer)
          (is (= #{:shared :outer :inner} (g/elements @kref))
              "the outer merge lands its own write and the inner one"))))))

(deftest sibling-nested-forks-both-land
  (testing "two overlay forks of an overlay fork: merging both keeps both, and the outer merge lands all"
    (let [ctx (sp/create-execution-context)]
      (sp/with-context ctx
        (let [kref (ygg/register! (-> (mem-gset "kb") (g/conj :shared)))
              outer (ygg/fork! {:convergent-fork :overlay})]
          (ygg/with-fork outer
            (ovl/overlay-swap! @(ygg/system-signal "kb") (fn [s] (g/conj s :outer)))
            (let [a (ygg/fork! {:convergent-fork :overlay})
                  b (ygg/fork! {:convergent-fork :overlay})]
              (ygg/with-fork a (ovl/overlay-swap! @(ygg/system-signal "kb") (fn [s] (g/conj s :a))))
              (ygg/with-fork b (ovl/overlay-swap! @(ygg/system-signal "kb") (fn [s] (g/conj s :b))))
              (ygg/merge-fork! a)
              (ygg/merge-fork! b)))
          (ygg/merge-fork! outer)
          (is (= #{:shared :outer :a :b} (g/elements @kref))
              "the second sibling's merge did not drop the first's"))))))

(deftest a-branch-fork-of-an-overlay-fork-merges-everything
  (testing "outer overlay fork, inner default (branch) fork of it: both land"
    (let [ctx (sp/create-execution-context)]
      (sp/with-context ctx
        (let [kref (ygg/register! (-> (mem-gset "kb") (g/conj :shared)))
              outer (ygg/fork! {:convergent-fork :overlay})]
          (ygg/with-fork outer
            (ovl/overlay-swap! @(ygg/system-signal "kb") (fn [s] (g/conj s :outer)))
            (let [inner (ygg/fork!)]
              (ygg/with-fork inner
                (swap! (ygg/system-signal "kb") (fn [s] (g/conj s :inner))))
              (ygg/merge-fork! inner))
            (is (ovl/overlay? @(ygg/system-signal "kb")) "the outer fork keeps its overlay"))
          (ygg/merge-fork! outer)
          (is (= #{:shared :outer :inner} (g/elements @kref))))))))
