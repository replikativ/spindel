(ns org.replikativ.spindel.v2.dom.foreign-test
  "Foreign nodes on engine v2 (phase-d addendum §3.8.2): `foreign-node`
   keeps its options and maps them onto the lifetime hook `:ref`, with
   `:on-unmount` as the returned cleanup. The container's attrs reconcile
   like any element's; its children belong to the library."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.dom.foreign :as foreign :refer [foreign-node]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]
            [org.replikativ.spindel.dom.discharge :as disch]))

(defn- library-child!
  "What a library does to its container: adds a child spindel does not own."
  [d el]
  (disch/append-child! d el (disch/create-text! d "library")))

(deftest a-foreign-node-mounts-once-and-unmounts-once
  (fx/each-world
   (fn [env]
     (let [d (:discharge (:mock env))
           log (atom [])
           cls (v2/signal "a")
           show (v2/signal true)
           root (spin (let [c (iv/get-new (track cls)) sh (iv/get-new (track show))]
                        (el/div (when sh
                                  (foreign-node {:tag :pre :class c
                                                 :on-mount (fn [el] (swap! log conj [:mount (mock/attached? d :container el)])
                                                             ;; the library owns the children
                                                             (library-child! d el))
                                                 :on-unmount (fn [x] (swap! log conj [:unmount x]))})))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (is (= [[:mount true]] @log) "on-mount sees the attached container")
       (is (= [[:div {} [:pre {:class "a"} "library"]]] (mock/dom d :container)))
       (fx/write! env cls "b")
       (is (= [[:mount true]] @log) "an attr change does not remount")
       (is (= [[:div {} [:pre {:class "b"} "library"]]] (mock/dom d :container))
           "the attrs reconcile; the library's children stay")
       (fx/write! env show false)
       (is (= [[:mount true] [:unmount nil]] @log) "on-unmount is the cleanup, called once with nil")
       (fx/unmount! env ctl)
       (is (= 2 (count @log)))
       (is (empty? (fx/leftovers env state)))))))

(deftest a-foreign-node-without-on-unmount
  (fx/each-world
   (fn [env]
     (let [log (atom [])
           root (spin (el/div (foreign-node {:on-mount (fn [el] (swap! log conj (some? el)))})))
           ctl (fx/render! env root)]
       (fx/unmount! env ctl)
       (is (= [true] @log) "the mount fn is not called again with nil")))))
