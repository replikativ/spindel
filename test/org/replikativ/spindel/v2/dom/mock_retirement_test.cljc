(ns org.replikativ.spindel.v2.dom.mock-retirement-test
  "The v2 mock models the live tree only (sol's P4 review, finding 7): a
   detached subtree's nodes, attrs, properties and child lists are retired,
   so a mock kept after unmount holds no handler. The operation log is the
   separate, intended history."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]
            #?(:clj [org.replikativ.spindel.v2.verify :as verify])))

(deftest a-removed-subtree-is-retired
  (fx/each-world
   (fn [env]
     (let [d (:discharge (:mock env))
           show (v2/signal true)
           root (spin (el/div (when (iv/get-new (track show))
                                (el/button {:on-click (fn [_] nil)} (el/b "a")))))
           {:keys [state] :as ctl} (fx/render! env root)
           before (mock/live-state d)]
       (fx/write! env show false)
       (let [after (mock/live-state d)]
         (is (< (:nodes after) (:nodes before)) "the button, its bold child and text are gone from the model")
         (is (zero? (:attrs after)) "no handler is held"))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))

(deftest unmount-leaves-no-live-model-and-keeps-the-log
  (fx/each-world
   (fn [env]
     (let [d (:discharge (:mock env))
           root (spin (el/div (el/button {:on-click (fn [_] nil)} "a")
                              (el/input {:value "x" :on-input (fn [_] nil)})))
           {:keys [state] :as ctl} (fx/render! env root)]
       (fx/unmount! env ctl)
       (is (= {:nodes 0 :attrs 0 :props 0 :kids 0 :parent 0} (mock/live-state d)))
       (is (seq @(:log (:mock env))) "the operation log is history, kept")
       (is (empty? (fx/leftovers env state)))))))

#?(:clj
   (deftest a-kept-control-object-holds-no-handler
     (fx/with-world
       {:verify? false}
       (fn [env]
         (let [handler (atom (fn [_] nil))
               weak (java.lang.ref.WeakReference. @handler)
               ctl (let [root (let [h @handler] (spin (el/div (el/button {:on-click h} "a"))))
                         c (fx/render! env root)]
                     (v2/release! root)
                     c)]
           (reset! handler nil)
           (fx/unmount! env ctl)
           (verify/gc-settle! (:w env))
           (fx/settle! env)
           (verify/gc-settle! (:w env))
           (let [gone? (nil? (.get weak))]
             (is gone? "the handler is collectable while the control object and its mock are kept"))
           (is (= :unmounted (render/phase (:state ctl)))))))))
