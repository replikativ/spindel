(ns org.replikativ.spindel.continuation-snapshot-test
  "Regression tests for the continuation snapshot of :spin-tracking and bindings.

  Covers the partial-resume-record-deps bug where a parent body that suspends
  on one await, then resumes from another await re-completion, lost the deps
  it had tracked in the pre-suspend slice. record-deps! at body completion
  saw only the post-resume tracking and tore down observer relations for
  the pre-suspend deps. The fix snapshots :spin-tracking [parent-id] into
  the cont-map at suspend and restores it before invoking resume-fn."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

(defn clean-context-fixture [f]
  (binding [ec/*execution-context* nil]
    (f)))

(use-fixtures :each clean-context-fixture)

;; =============================================================================
;; The bug: partial-resume tracks only post-resume deps
;; =============================================================================

(deftest partial-resume-preserves-pre-suspend-deps
  (testing "When a parent body resumes from a child re-completion, its
            recorded deps must include the children it awaited *before*
            the resume point, not only the ones it tracked after."
    (with-ctx [ctx]
      (let [counter-a (sig/signal 0)
            counter-b (sig/signal 0)
            ;; Two children, each with a track. The parent awaits them
            ;; sequentially. After the parent's body completes once, we
            ;; perturb counter-b — that re-runs child-b, which re-completes,
            ;; which resumes the parent's body from the *second* await.
            ;; The body runs forward from there (no new tracks/awaits in
            ;; the post-resume slice for this test). At body completion,
            ;; record-deps! must see {child-a, child-b}, not just {child-b}.
            child-a (spin
                      (let [{:keys [new]} (track counter-a)]
                        (str "a:" new)))
            child-b (spin
                      (let [{:keys [new]} (track counter-b)]
                        (str "b:" new)))
            parent (spin
                     (let [a (await child-a)
                           b (await child-b)]
                       [a b]))]
        ;; Run parent once.
        (is (= ["a:0" "b:0"] @parent))
        (await-drain ctx)

        ;; Inspect parent's deps after first run.
        (let [parent-id (org.replikativ.spindel.spin.core/spin-id parent)
              child-a-id (org.replikativ.spindel.spin.core/spin-id child-a)
              child-b-id (org.replikativ.spindel.spin.core/spin-id child-b)
              parent-node-1 (rtp/get-state ctx [:nodes parent-id])
              deps-1 (nodes/get-deps parent-node-1)]
          (is (contains? (:spins deps-1) child-a-id) "after first run: parent deps include child-a")
          (is (contains? (:spins deps-1) child-b-id) "after first run: parent deps include child-b")

          ;; Perturb counter-b: child-b re-runs from its track, re-completes.
          ;; The parent's body should resume from the second-await point,
          ;; reach the let body, return, complete.
          (reset! counter-b 1)
          (await-drain ctx)

          ;; Inspect parent's deps after partial-resume re-completion.
          (let [parent-node-2 (rtp/get-state ctx [:nodes parent-id])
                deps-2 (nodes/get-deps parent-node-2)]
            (is (contains? (:spins deps-2) child-a-id)
                "after partial-resume: child-a still in parent's deps (pre-suspend slice deps preserved)")
            (is (contains? (:spins deps-2) child-b-id)
                "after partial-resume: child-b still in parent's deps")

            ;; Cross-check observer side: child-a's :observers should still
            ;; contain parent-id (record-deps! didn't remove it).
            (let [child-a-node (rtp/get-state ctx [:nodes child-a-id])
                  child-a-observers (nodes/get-observers child-a-node)]
              (is (contains? child-a-observers parent-id)
                  "child-a's observer relation to parent is preserved through partial-resume"))))))))

(deftest partial-resume-from-track-preserves-pre-suspend-deps
  (testing "Same invariant for track-resume (signal change resumes the
            body forward; deps tracked before the track point must survive)."
    (with-ctx [ctx]
      (let [counter (sig/signal 0)
            child (spin "child-result")
            parent (spin
                     (let [a (await child)
                           {:keys [new]} (track counter)]
                       [a new]))]
        (is (= ["child-result" 0] @parent))
        (await-drain ctx)

        (let [parent-id (org.replikativ.spindel.spin.core/spin-id parent)
              child-id (org.replikativ.spindel.spin.core/spin-id child)]
          ;; Check first run.
          (is (contains? (:spins (nodes/get-deps (rtp/get-state ctx [:nodes parent-id])))
                         child-id)
              "after first run: parent depends on child")

          ;; Perturb counter: parent's track point re-fires.
          (reset! counter 1)
          (await-drain ctx)

          (is (contains? (:spins (nodes/get-deps (rtp/get-state ctx [:nodes parent-id])))
                         child-id)
              "after track-resume: child still in parent's deps (the await before the track survived)"))))))
