(ns org.replikativ.spindel.engine.await-running-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.spin.core :as sc]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-helpers :as th :refer [async with-ctx run-spin!]]))

(deftest await-joins-detached-mailbox-reader
  (async done
    (with-redefs [th/create-test-context
                  #(ctx/create-execution-context :executor (ex/synchronous-executor))]
      (with-ctx [world]
        (let [mailbox (sync/create-mailbox world)
              runs (atom 0)
              child (spin (swap! runs inc) (await mailbox))
              child-values (atom [])
              parent-values (atom [])
              parent (spin (await child))]
          (sync/spawn! child {:on-success #(swap! child-values conj %)})
          (run-spin! parent #(swap! parent-values conj %)
                     #(is false (str %)))
          (sync/post! mailbox :end)
          (is (= [:end] @parent-values))
          (is (= [:end] @child-values))
          (is (= 1 @runs) "await joins the existing run without restarting its input"))))
    (done)))

#?(:clj
   (deftest mailbox-completion-race-1000
     (let [outcomes
           (frequencies
            (for [_ (range 1000)]
              (let [world (ctx/create-execution-context)]
                (try
                  (binding [ec/*execution-context* world]
                    (let [mailbox (sync/create-mailbox world)
                          runs (atom 0)
                          child (spin (swap! runs inc) (await mailbox))
                          result (atom ::pending)]
                      (sync/spawn! child)
                      (sync/post! mailbox :end)
                      (sync/spawn! (spin (await child))
                                   {:on-success #(reset! result [:ok %])
                                    :on-error #(reset! result [:error %])})
                      (let [deadline (+ (System/nanoTime) 1000000000)]
                        (loop []
                          (when (and (not (simple/events-settled? world))
                                     (< (System/nanoTime) deadline))
                            (java.util.concurrent.locks.LockSupport/parkNanos 100000)
                            (recur))))
                      [@runs @result]))
                  (finally (ctx/close-context! world))))))]
       (is (= {[1 [:ok :end]] 1000} outcomes) (str outcomes)))))

(deftest completion-before-await-registration
  (async done
    (with-redefs [th/create-test-context
                  #(ctx/create-execution-context :executor (ex/synchronous-executor))]
      (with-ctx [world]
        (doseq [failure? [false true]]
          (let [mailbox (sync/create-mailbox world)
                runs (atom 0)
                child (spin (swap! runs inc)
                            (let [v (await mailbox)]
                              (if failure? (throw (ex-info "source failed" {})) v)))
                parent (spin (await child))
                values (atom [])
                errors (atom [])
                add! ec/continuation-add!
                forced? (atom false)]
            (sync/spawn! child {:on-error (fn [_])})
            (with-redefs [ec/continuation-add!
                          (fn [sid cont]
                            (when (and (= sid (sc/spin-id parent))
                                       (compare-and-set! forced? false true))
                              ;; Complete AND drain after await's first cache read,
                              ;; before its subscription becomes visible.
                              (sync/post! mailbox :end))
                            (add! sid cont))]
              (run-spin! parent #(swap! values conj %) #(swap! errors conj %)))
            (is @forced?)
            (if failure?
              (is (= ["source failed"] (mapv ex-message @errors)))
              (is (= [:end] @values)))
            (is (= 1 @runs) "completion in the registration window is read from cache")))))
    (done)))
