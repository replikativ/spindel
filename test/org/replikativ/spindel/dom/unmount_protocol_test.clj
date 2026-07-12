(ns org.replikativ.spindel.dom.unmount-protocol-test
  "Unmount completeness: every address the render path writes must be reachable
  from the teardown walk, and every removal vocabulary must call refs with nil.

  Two defects these tests pin (both were live, both proven by probe):

  1. **ifor-each keyed-cache leak.** `flatten-slot` splices a `:keyed` slot's
     items into `:children` and drops the `KeyedFragment` itself, so the
     ifor-each CALL-SITE address — which holds `:by-key` (every rendered vnode,
     with its event-handler closures) and `:items-by-key` — appears on no vnode.
     The teardown walk could never reach it, so unmounting any subtree containing
     an `ifor-each` retained the whole rendered list for the lifetime of the
     context. In simmis (87 ifor-each sites) every closed chat room leaked its
     entire message list.

  2. **Root swap without teardown.** A spin whose root element changes re-mounts
     (formalism §3.9 R2). Without an explicit teardown the old tree's refs never
     received their `nil` call — foreign nodes (TipTap) never released — and its
     caches were never evicted.

  See docs/engine-formalism.md §3.9."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.foreach :refer [ifor-each]]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.test-async :refer [await-drain]]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]))

(defn- state-size [k] (count (ec/get-state [k])))

(deftest test-ifor-each-keyed-cache-is-evicted-on-unmount
  (testing "unmounting a subtree containing an ifor-each drops its keyed cache"
    (with-ctx [rt]
      (let [{:keys [discharge]} (disch/make-mock-discharge)
            show? (sig/signal true)
            items [{:id 1 :t "a"} {:id 2 :t "b"} {:id 3 :t "c"}]
            the-spin (spin (el/div {:class "shell"}
                                   (when @(track show?)
                                     (el/ul {:class "list"}
                                            (ifor-each :id items (fn [i] (el/li (:t i))))))))]
        (render/render-spin! nil the-spin discharge)
        @the-spin
        (is (pos? (state-size :dom/keyed-cache)) "mounted: keyed cache present")
        (let [mounted-slots (state-size :dom/cache)]
          (is (pos? mounted-slots))

          (reset! show? false)
          (await-drain rt)

          (is (zero? (state-size :dom/keyed-cache))
              "ifor-each keyed cache must be evicted — it holds every rendered vnode")
          (is (< (state-size :dom/cache) mounted-slots)
              "slot caches of the unmounted subtree must be evicted"))))))

(deftest test-ifor-each-cache-survives-when-subtree-stays-mounted
  (testing "the eviction cascade must not drop a LIVE ifor-each's cache"
    (with-ctx [rt]
      (let [{:keys [discharge]} (disch/make-mock-discharge)
            flag (sig/signal true)
            items [{:id 1 :t "a"} {:id 2 :t "b"}]
            the-spin (spin (el/div {:class "shell"}
                             ;; a sibling toggles; the list stays mounted
                                   (when @(track flag) (el/span "x"))
                                   (el/ul {:class "list"}
                                          (ifor-each :id items (fn [i] (el/li (:t i)))))))]
        (render/render-spin! nil the-spin discharge)
        @the-spin
        (reset! flag false)
        (await-drain rt)
        (is (pos? (state-size :dom/keyed-cache))
            "a still-mounted ifor-each must keep its keyed cache")))))

(deftest test-root-swap-calls-refs-on-unmount-and-evicts
  (testing "a changed root re-mounts with full teardown: refs nil-called, caches evicted"
    (with-ctx [rt]
      (let [{:keys [discharge]} (disch/make-mock-discharge)
            loading? (sig/signal true)
            unmounts (atom 0)
            mounts (atom 0)
            ;; :ref fires with the element on mount and nil on unmount — this is
            ;; what foreign nodes (TipTap) hang their teardown on.
            ref-fn (fn [el] (if el (swap! mounts inc) (swap! unmounts inc)))
            the-spin (spin (if @(track loading?)
                             (el/div {:class "loading" :ref ref-fn} (el/p "LOADING"))
                             (el/div {:class "loaded"} (el/p "CONTENT"))))]
        (render/render-spin! nil the-spin discharge)
        @the-spin
        (is (= 1 @mounts) "ref called with the element on initial mount")
        (is (= 0 @unmounts))
        (let [slots-before (state-size :dom/cache)]

          (reset! loading? false)
          (await-drain rt)

          (is (= 1 @unmounts)
              "root swap must call the old tree's refs with nil (foreign-node teardown)")
          (is (<= (state-size :dom/cache) slots-before)
              "old root's caches must not accumulate across the swap"))))))

(deftest test-root-swap-back-and-forth-is-bounded
  (testing "A->B->A re-claims addresses; caches stay bounded across N flips"
    (with-ctx [rt]
      (let [{:keys [discharge]} (disch/make-mock-discharge)
            loading? (sig/signal true)
            the-spin (spin (if @(track loading?)
                             (el/div {:class "loading"} (el/p "LOADING"))
                             (el/div {:class "loaded"} (el/p "CONTENT"))))]
        (render/render-spin! nil the-spin discharge)
        @the-spin
        (let [after-first (do (reset! loading? false) (await-drain rt)
                              (state-size :dom/cache))]
          (dotimes [_ 5]
            (reset! loading? true) (await-drain rt)
            (reset! loading? false) (await-drain rt))
          (is (<= (state-size :dom/cache) (* 2 after-first))
              "repeated root swaps must not grow the cache without bound"))))))
