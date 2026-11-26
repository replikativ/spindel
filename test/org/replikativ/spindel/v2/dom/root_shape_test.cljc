(ns org.replikativ.spindel.v2.dom.root-shape-test
  "The shapes a mount's root may take (sol's P4 review, finding 4). A root
   element is kept across commits only while its tag, address and key stay
   the same; otherwise the whole tree is replaced. A nil delivery keeps the
   last frame (no commit). A root without an address (a fragment) is
   replaced on every commit: there is no element to reconcile in place."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

(defn- dom [env] (mock/dom (:discharge (:mock env)) :container))

(deftest a-tag-change-at-the-root-replaces-it
  (fx/each-world
   (fn [env]
     (let [tag (v2/signal :div)
           log (atom [])
           root (spin (let [t (iv/get-new (track tag))]
                        (el/element t {:ref (fn [el] (swap! log conj [t (some? el)]))} "x")))
           {:keys [state] :as ctl} (fx/render! env root)
           addr (:addr (render/committed state))]
       (fx/write! env tag :span)
       (is (= addr (:addr (render/committed state))) "the same address")
       (is (= [[:span {} "x"]] (dom env)) "the DOM root is a span")
       (is (= [[:div true] [:div false] [:span true]] @log) "the div's ref is cleaned up, the span's set up")
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))

(deftest a-key-change-at-the-root-replaces-it
  (fx/each-world
   (fn [env]
     (let [k (v2/signal 1)
           log (atom [])
           root (spin (let [x (iv/get-new (track k))]
                        (el/div {:key x :ref (fn [el] (swap! log conj [x (some? el)]))} (str x))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (fx/write! env k 2)
       (is (= [[:div {} "2"]] (dom env)))
       (is (= [[1 true] [1 false] [2 true]] @log))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))

(deftest a-nil-delivery-keeps-the-last-frame
  (fx/each-world
   (fn [env]
     (let [show (v2/signal true)
           root (spin (when (iv/get-new (track show)) (el/div "x")))
           {:keys [state] :as ctl} (fx/render! env root)]
       (fx/write! env show false)
       (is (= [[:div {} "x"]] (dom env)) "the last frame stays")
       (is (= 1 (render/revision state)) "no commit")
       (is (= :mounted (render/phase state)))
       (fx/write! env show true)
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))

(deftest a-fragment-root-is-replaced-on-every-commit
  (fx/each-world
   (fn [env]
     (let [s (v2/signal 1)
           log (atom [])
           root (spin (let [x (iv/get-new (track s))]
                        (el/fragment (el/p {:ref (fn [el] (swap! log conj [x (some? el)]))} (str x))
                                     (el/i "y"))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (is (= [[:p {} "1"] [:i {} "y"]] (dom env)))
       (fx/write! env s 2)
       (is (= [[:p {} "2"] [:i {} "y"]] (dom env)) "the update reaches the DOM")
       (is (= [[1 true] [1 false] [2 true]] @log) "by replacing the tree")
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))
