(ns org.replikativ.spindel.v2.dom.revision-waiter-test
  "Revision waiters are acknowledgement code: each runs isolated, and none
   can skip a commit's finalization (sol's P4 review, finding 5). A waiter
   that asks for an unmount while the commit holds the mount and then
   throws still gets its unmount; a throwing waiter at teardown does not
   keep the others from their ::unmounted."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

(deftest a-waiter-that-requests-an-unmount-and-throws
  (fx/each-world
   (fn [env]
     (let [s (v2/signal 1)
           root (spin (el/div (str (iv/get-new (track s)))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (render/on-revision state 2 (fn [_]
                                     ((:unmount! ctl))
                                     (throw (ex-info "a throwing waiter" {}))))
       (fx/write! env s 2)
       (is (= :unmounted (render/phase state)) "the held unmount ran")
       (is (not (:busy @state)))
       (is (empty? (fx/leftovers env state)))
       (fx/violations)))))

(deftest a-throwing-waiter-at-teardown
  (fx/each-world
   (fn [env]
     (let [root (spin (el/div "x"))
           {:keys [state] :as ctl} (fx/render! env root)
           seen (atom [])]
       (render/on-revision state 10 (fn [x] (swap! seen conj [:first x]) (throw (ex-info "first" {}))))
       (render/on-revision state 10 (fn [x] (swap! seen conj [:second x])))
       (fx/unmount! env ctl)
       (is (= [[:first ::render/unmounted] [:second ::render/unmounted]] @seen))
       (is (empty? (fx/leftovers env state)))
       (fx/violations)))))

(deftest a-throwing-waiter-on-a-bump-does-not-starve-the-next
  (fx/each-world
   (fn [env]
     (let [s (v2/signal 1)
           root (spin (el/div (str (iv/get-new (track s)))))
           {:keys [state] :as ctl} (fx/render! env root)
           seen (atom [])]
       (render/on-revision state 2 (fn [_] (swap! seen conj :first) (throw (ex-info "first" {}))))
       (render/on-revision state 2 (fn [_] (swap! seen conj :second)))
       (fx/write! env s 2)
       (is (= [:first :second] @seen))
       (is (= :mounted (render/phase state)))
       (fx/unmount! env ctl)
       (fx/violations)))))
