(ns org.replikativ.spindel.dom.cross-spin-rerender-test
  "Regression test for cross-spin vnode reuse on parent re-emission.

  Pattern: a parent spin awaits a child spin (which returns a vnode
  tree), embeds the result in its own DOM. A separate signal change
  triggers the parent's body to re-emit. The expectation: the child's
  DOM stays at its original state (no duplication), since the child
  spin's body didn't re-run.

  The bug this guards against: the cached child vnode carries the
  :deltas computed by `build-element`'s initial reconciliation
  (`[:add header at 0, :add content at 1]`). Without dedup, each
  parent re-emission walks the cached vnode in `collect-nodes-with-deltas`
  and re-applies those :add deltas to the (existing) DOM element,
  duplicating children. The fix lives in `discharge-vnode!` /
  `mark-rendered!` / `create-render-effect` and uses an
  `*applied-vnodes*` set that persists across re-render cycles for
  one render-effect."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

(defn clean-context-fixture [f]
  (binding [ec/*execution-context* nil]
    (f)))

(use-fixtures :each clean-context-fixture)

;; =============================================================================
;; Three-level nesting:
;;   make-app-spin → render-app → {nav-spin (no track), cols-spin (tracks)}
;; =============================================================================

(defn make-nav-spin []
  ;; No track — must NOT re-run on tick change.
  (spin
   (el/aside {:class "nav-sidebar"}
             (el/div {:class "nav-header"} "Logo")
             (el/div {:class "nav-content"} "Content"))))

(defn make-cols-spin [tick]
  ;; Tracks tick — re-runs on every signal change.
  (spin
   (let [{:keys [new]} (track tick)]
     (el/div {:class "columns" :data-tick (str new)} (str "Tick: " new)))))

(defn make-render-app-spin [tick]
  (spin
   (let [nav-vnode  (await (make-nav-spin))
         cols-vnode (await (make-cols-spin tick))]
     (el/div {:class "app-shell"}
             nav-vnode
             cols-vnode))))

(defn make-app-spin* [tick]
  (spin
   (await (make-render-app-spin tick))))

(deftest test-cross-spin-vnode-stable-on-sibling-rerender
  (testing "When a sibling spin re-emits due to a signal change, an
            unrelated cached child spin's DOM does NOT duplicate.

            Pattern:
            make-app → render-app → {nav-spin (no track),
                                     cols-spin (tracks tick)}."
    (with-ctx [ctx]
      (let [tick (sig/signal 0)
            {:keys [discharge log]} (disch/make-mock-discharge)
            app-spin (make-app-spin* tick)]
        (render/render-spin! nil app-spin discharge)
        @app-spin
        (await-drain ctx)

        (let [initial-asides     (count (filter #(and (= :create-element (:op %))
                                                      (= :aside (:tag %)))
                                                @log))
              initial-nav-logos  (count (filter #(= "Logo" (:text %)) @log))]
          (is (= 1 initial-asides) "initial: 1 aside created")
          (is (= 1 initial-nav-logos) "initial: 1 'Logo' text created"))

        ;; Perturb tick three times. cols-spin re-runs each time; nav-spin
        ;; doesn't (no tracked signals). Parent body re-emits, embedding
        ;; the cached nav aside. Expectation: the aside's DOM stays as-is.
        (reset! tick 1)
        (await-drain ctx)
        (reset! tick 2)
        (await-drain ctx)
        (reset! tick 3)
        (await-drain ctx)

        (let [final-asides    (count (filter #(and (= :create-element (:op %))
                                                   (= :aside (:tag %)))
                                             @log))
              final-nav-logos (count (filter #(= "Logo" (:text %)) @log))]
          (is (= 1 final-asides)
              (str "after 3 sibling re-renders, expect still 1 aside, got "
                   final-asides))
          (is (= 1 final-nav-logos)
              (str "after 3 sibling re-renders, expect still 1 'Logo' text, got "
                   final-nav-logos)))))))
