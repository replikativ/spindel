(ns org.replikativ.spindel.dom.superseded-run-test
  "An ABANDONED body run must not move the DOM caches.

   A body slice can build its elements and then suspend on an `await`. When a
   newer signal value resumes the track continuation above it, `resume-body!`
   truncates and CANCELS that slice — its CPS chain never resolves, so its
   vnode never reaches the render effect. Before the staging fix, the slice's
   cache writes were already in ctx state: the committed run then reconciled
   against a baseline the DOM had never seen, produced no deltas, and the
   change was silently lost.

   Worse, it compounded: a lost `:add` left the slot cache claiming a child
   the DOM never gained, so the NEXT transition removed the wrong index — a
   live sibling.

   The fix: `build-element`/`ifor-each` STAGE their reconciliations
   (`[:dom/pending]`), and `cache/commit-pending!` promotes them only for
   addresses present in a vdom tree that actually reached the DOM
   (initial-mount!, update-render!'s two branches, discharge-all!)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.test-async :refer [await-drain]]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]))

(defn clean-context-fixture [f]
  (binding [ec/*execution-context* nil]
    (f)))

(use-fixtures :each clean-context-fixture)

;; =============================================================================
;; 1. The measured bug: a superseded suspended run loses attr AND child deltas
;; =============================================================================

(deftest superseded-suspended-run-still-updates-the-dom
  (testing "run builds, suspends, is superseded — the committed run must still
            carry the attribute update and the conditional child"
    (with-ctx [rt]
      (let [{:keys [discharge log]} (disch/make-mock-discharge)
            a (sig/signal 0)
            s (spin
               (let [{av :new} (track a)
                     cls (if (pos? av) "editor readonly" "editor")
                     v (el/div {:class cls}
                               (when (pos? av) (el/span "BANNER")))]
                 ;; Suspend AFTER building — the window in which a newer signal
                 ;; value supersedes this slice.
                 (await (comb/sleep 60))
                 v))]
        (render/render-spin! nil s discharge)
        @s
        (await-drain rt)
        (Thread/sleep 150)
        (reset! log [])
        ;; Two changes in quick succession: the first run is superseded while
        ;; suspended on the sleep. Both runs compute the SAME new state
        ;; (readonly + banner), so before the fix the committed run reconciled
        ;; against the abandoned run's cache writes and emitted nothing.
        (reset! a 1)
        (Thread/sleep 5)
        (reset! a 2)
        (Thread/sleep 400)
        (await-drain rt)
        (is (some #(and (= :set-attr (:op %)) (= :class (:attr %))
                        (= "editor readonly" (:value %)))
                  @log)
            "class update must reach the DOM")
        (is (some #(and (= :create-text (:op %)) (= "BANNER" (:text %))) @log)
            "conditional child must reach the DOM")))))

;; =============================================================================
;; 2. The compounding corruption: the caches must stay a model of the DOM
;; =============================================================================

(deftest slot-cache-stays-synced-with-the-dom-across-supersession
  (testing "after a superseded transition, the following transition operates on
            children the DOM actually holds — not on the cache's fiction"
    (with-ctx [rt]
      (let [{:keys [discharge log]} (disch/make-mock-discharge)
            a (sig/signal 0)
            s (spin
               (let [{av :new} (track a)
                     v (el/div {:class "root"}
                               (when (pos? av) (el/span {:class "banner"} "BANNER"))
                               (el/p {:class "stable"} "STABLE"))]
                 (await (comb/sleep 60))
                 v))]
        (render/render-spin! nil s discharge)
        @s
        (await-drain rt)
        (Thread/sleep 200)
        (reset! log [])
        ;; Supersede: two changes before the first run resolves.
        (reset! a 1)
        (Thread/sleep 5)
        (reset! a 2)
        (Thread/sleep 400)
        (await-drain rt)
        (let [flip-on-ops @log]
          ;; The banner must have actually been inserted. Before the fix it
          ;; never was — while the slot cache claimed it existed.
          (is (some #(and (= :create-text (:op %)) (= "BANNER" (:text %)))
                    flip-on-ops)
              "flip-on must insert the banner")
          (reset! log [])
          ;; A single clean change back. With the caches honest, this removes
          ;; exactly the banner. Before the fix the DOM had no banner, so the
          ;; removal at index 0 deleted the live STABLE <p> instead.
          (reset! a 0)
          (Thread/sleep 400)
          (await-drain rt)
          (let [removes (filter #(= :remove-child (:op %)) @log)]
            (is (= 1 (count removes))
                (str "flip-off removes exactly the banner, got " (vec removes)))))))))

;; =============================================================================
;; 3. The commit-protocol detector: no-change re-render emits ZERO ops
;; =============================================================================

(deftest no-change-rerender-emits-zero-ops
  (testing "a body re-run that produces identical output discharges nothing —
            the single most sensitive detector for a missed commit point: if a
            tree's caches were never promoted, the re-run reconciles against
            nil and re-emits the whole mount as :add deltas"
    (with-ctx [rt]
      (let [{:keys [discharge log]} (disch/make-mock-discharge)
            a (sig/signal 0)
            s (spin
               (let [{_ :new} (track a)]
                 ;; Output does not depend on the tracked value.
                 (el/div {:class "shell"}
                         (el/span {:class "static"} "Same")
                         (el/p "Every time"))))]
        (render/render-spin! nil s discharge)
        @s
        (await-drain rt)
        (reset! log [])
        (reset! a 1)
        (await-drain rt)
        (Thread/sleep 100)
        (await-drain rt)
        (is (empty? @log)
            (str "identical output must produce zero DOM ops, got " (vec @log)))))))
