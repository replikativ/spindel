(ns org.replikativ.spindel.structural-id-test
  "Regression tests for structural addressing of (spin …).

  These tests pin down a property that a sidebar-duplication regression
  forced us to confront: when a parent spin re-runs (because an awaited
  child re-completed or a tracked signal flipped), every `(spin …)` form
  inside the parent body must mint the SAME id across re-runs.

  Under chain-head addressing this property holds only by accident — when
  the chain-head cursor lands on the same value at the same form. After a
  partial resume the cursor drifts and the same `(spin …)` form mints a
  fresh id, which manifests downstream as DOM elements with shifted
  structural addresses (the renderer can't dedupe across the parent's
  re-emissions).

  With `next-id` (structural addressing), the id is a pure function of
  (source-loc, parent-id, key) — so re-runs are deterministic regardless
  of evaluation order."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

(defn clean-context-fixture [f]
  (binding [ec/*execution-context* nil]
    (f)))

(use-fixtures :each clean-context-fixture)

;; =============================================================================
;; A pair of "component-like" factory functions.
;; =============================================================================

(defn make-child-a []
  (spin
   (let [{:keys [new]} (track (sig/signal 0))]
     [:a new])))

(defn make-child-b []
  (spin
   (let [{:keys [new]} (track (sig/signal 0))]
     [:b new])))

;; =============================================================================
;; Test 1: stable id across parent body re-runs
;; =============================================================================

#?(:clj
   (deftest spin-id-stable-across-parent-rerun
     (testing "When parent body re-runs because a tracked signal changes, the
            `(spin …)` macro inside a factory called from the parent must
            mint the SAME id on the re-run. Otherwise the renderer sees a
            fresh child spin in the parent's vnode tree and can't dedupe."
       (with-ctx [ctx]
         (let [tick (sig/signal 0)
               child-ids (atom [])
               parent (spin
                       (let [{:keys [new]} (track tick)
                             child (make-child-a)]
                         (swap! child-ids conj (spin-core/spin-id child))
                         new))]
           @parent
           (await-drain ctx)
           (reset! tick 1)
           (await-drain ctx)
           (reset! tick 2)
           (await-drain ctx)
           (let [ids @child-ids]
             (is (>= (count ids) 2)
                 "parent body ran at least twice")
             (is (apply = ids)
                 (str "child id must be stable across re-runs. got: " (vec ids)))))))))

;; =============================================================================
;; Test 2: two distinct call sites mint distinct ids
;; =============================================================================

#?(:clj
   (deftest distinct-call-sites-get-distinct-ids
     (testing "Two separate `(make-child-…)` call sites in the same parent body
            must mint DIFFERENT spin ids — otherwise they would collide and
            cache-share."
       (with-ctx [ctx]
         (let [a-id (atom nil)
               b-id (atom nil)
               parent (spin
                       (let [a (make-child-a)
                             b (make-child-b)]
                         (reset! a-id (spin-core/spin-id a))
                         (reset! b-id (spin-core/spin-id b))
                         [:done]))]
           @parent
           (await-drain ctx)
           (is (some? @a-id))
           (is (some? @b-id))
           (is (not= @a-id @b-id)
               "two distinct factory functions called from the same parent must produce distinct spin ids"))))))

;; =============================================================================
;; Test 3: same factory called twice from same parent without key — collision
;;          is the expected (and documented) failure mode for structural
;;          addressing. The fix is `with-key`; see the addressing namespace.
;; =============================================================================

;; (We intentionally do NOT assert this collision here — the structural
;;  addressing migration treats it as a known caller responsibility, and
;;  user-facing component factories should `with-key` when they appear in
;;  lists. The audit doc covers this.)

;; =============================================================================
;; Test 4: stable id across partial-resume from child re-completion
;; =============================================================================

#?(:clj
   (deftest spin-id-stable-across-await-resume
     (testing "When parent's body suspends on an await, then resumes after the
            child re-completes, any `(spin …)` form executed in the
            post-resume slice must mint the SAME id as the first run."
       (with-ctx [ctx]
         (let [tick (sig/signal 0)
            ;; A leaf child that we'll perturb to force parent re-runs.
               leaf (spin
                     (let [{:keys [new]} (track tick)]
                       [:leaf new]))
            ;; Capture the id of the spin minted AFTER the await.
               post-await-ids (atom [])
               parent (spin
                       (let [l (await leaf)
                           ;; A spin created in the post-resume slice.
                             after (make-child-a)]
                         (swap! post-await-ids conj (spin-core/spin-id after))
                         [l (spin-core/spin-id after)]))]
           @parent
           (await-drain ctx)
           (reset! tick 1)
           (await-drain ctx)
           (reset! tick 2)
           (await-drain ctx)
           (let [ids @post-await-ids]
             (is (>= (count ids) 2)
                 "parent body ran at least twice")
             (is (apply = ids)
                 (str "post-await spin id must be stable across re-runs. got: " (vec ids)))))))))
