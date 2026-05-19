(ns org.replikativ.spindel.dom.ifor-each-reactive-test
  "Regression test for ifor-each with *reactive* per-item spins.

  Pattern: `ifor-each` is given a render-fn that returns a spin which
  `track`s a signal — so each per-item spin re-completes whenever that
  signal changes. The expectation: a re-completion updates the item in
  place, it does NOT duplicate the item in the DOM.

  The bug this guards against lives in `for-each*`'s has-spins? path.
  That path returns `(spin (loop ... (await per-item-spin) ...))` and the
  loop closed over the `prev-by-key`/`prev-order` captured at `for-each*`
  call time. When a reactive per-item spin re-completes, the loop-spin's
  `(await …)` re-fires and rebuilds the fragment — but against that stale
  capture (empty on the first call), so `build-fragment-result` re-emits
  `:add` deltas for items that already exist. Propagated up as a
  `:fragment-update`, those `:add`s `insert-child!` duplicate DOM nodes.

  The fix: the loop-spin re-reads the keyed cache fresh right before
  `build-fragment-result`, so it diffs against the true previous order
  and emits `:update` deltas instead."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

(defn clean-context-fixture [f]
  (binding [ec/*execution-context* nil]
    (f)))

(use-fixtures :each clean-context-fixture)

(defn- net-children
  "Net child count of `parent-id` from a MockDischarge op log:
  append/insert add a child, remove drops one, replace is neutral."
  [log parent-id]
  (reduce (fn [n {:keys [op parent]}]
            (if (= parent parent-id)
              (case op
                (:append-child :insert-child) (inc n)
                :remove-child (dec n)
                n)
              n))
          0
          log))

(deftest test-ifor-each-reactive-per-item-spin-no-duplication
  (testing "A reactive per-item spin re-completing updates the item in
            place — it does not re-insert (duplicate) it.

            ifor-each render-fn returns a spin that tracks `tick`; each
            tick change re-completes every per-item spin, which re-fires
            the for-each* loop-spin's await and rebuilds the fragment."
    (with-ctx [ctx]
      (let [tick  (sig/signal 0)
            items [{:id "a"} {:id "b"} {:id "c"}]
            ;; render-fn returns a *reactive* spin (tracks `tick`)
            render-fn (fn [item]
                        (spin
                         (let [{:keys [new]} (track tick)]
                           (el/li {:key (:id item)}
                                  (str (:id item) "-" new)))))
            parent-spin (spin
                         (let [frag (await (foreach/for-each*
                                            {:file "test" :line 1 :column 1}
                                            :id render-fn items))]
                           (el/ul {:class "items"} frag)))
            {:keys [discharge log]} (disch/make-mock-discharge)]
        (render/render-spin! nil parent-spin discharge)
        @parent-spin
        (await-drain ctx)

        ;; Exactly one <ul> is ever created, and it has 3 <li> children.
        (let [ul-ids (->> @log
                          (filter #(and (= :create-element (:op %))
                                        (= :ul (:tag %))))
                          (mapv :id))]
          (is (= 1 (count ul-ids)) "exactly one <ul> element created")
          (is (= 3 (net-children @log (first ul-ids)))
              "initial mount: <ul> has 3 children")

          ;; Perturb the signal three times. Every per-item spin
          ;; re-completes each time, re-firing the for-each* loop-spin's
          ;; await and rebuilding the fragment.
          (reset! tick 1)
          (await-drain ctx)
          (reset! tick 2)
          (await-drain ctx)
          (reset! tick 3)
          (await-drain ctx)

          ;; With the stale-capture bug, each re-completion re-emitted
          ;; :add deltas → :fragment-update inserts → the <ul>'s child
          ;; count balloons. With the fix, the loop-spin re-reads the
          ;; cache fresh, sees the unchanged order, and emits :update
          ;; deltas → replace-child! (in place), so the count stays 3.
          (is (= 1 (->> @log
                        (filter #(and (= :create-element (:op %))
                                      (= :ul (:tag %))))
                        count))
              "still exactly one <ul> after 3 reactive re-completions")
          (is (= 3 (net-children @log (first ul-ids)))
              (str "after 3 reactive re-completions the <ul> must still "
                   "have 3 children — items update in place, not duplicate. "
                   "Got " (net-children @log (first ul-ids)))))))))
