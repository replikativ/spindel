(ns org.replikativ.spindel.pubsub.mult-pump-wakeup-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [is.simm.partial-cps.sequence :as aseq]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.pubsub.mult :as mult]
            [org.replikativ.spindel.spin.core :as sc]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-helpers :as th :refer [async with-ctx run-spin!]]))

(defn- finite-mailbox [mailbox]
  (reify aseq/PAsyncSeq
    (anext [this]
      (fn [resolve reject]
        ((aseq/anext mailbox)
         (fn [[item _]] (resolve (when-not (= ::end item) [item this])))
         reject)))))

(deftest await-running-mult-pump
  (async done
    (with-redefs [th/create-test-context
                  #(ctx/create-execution-context :executor (ex/synchronous-executor))]
      (with-ctx [world]
        (let [mailbox (sync/create-mailbox world)
              m (mult/mult (finite-mailbox mailbox))
              results (atom [])
              observer (spin (await (mult/mult-pump m)))
              add! ec/continuation-add!
              forced? (atom false)]
          (mult/start! m)
          (with-redefs [ec/continuation-add!
                        (fn [sid cont]
                          (when (and (= sid (sc/spin-id observer))
                                     (compare-and-set! forced? false true))
                            (sync/post! mailbox ::end))
                          (add! sid cont))]
            (run-spin! observer #(swap! results conj %) #(is false (str %))))
          (is @forced?)
          (is (mult/mult-closed? m))
          (is (= 1 (count @results)) "completion before registration still wakes the awaiter"))))
    (done)))

#?(:clj
   (deftest mult-pump-completion-race-1000
     ;; Reporter's ordering: start, post the end marker, then spawn an awaiter.
     ;; Wait for queued work, not parked spins: a lost wakeup is the failure
     ;; being measured, and must not add a per-sample timeout to the test.
     (let [outcomes
           (frequencies
            (for [_ (range 1000)]
              (let [world (ctx/create-execution-context)]
                (try
                  (binding [ec/*execution-context* world]
                    (let [mailbox (sync/create-mailbox world)
                          m (mult/mult (finite-mailbox mailbox))
                          result (atom ::pending)]
                      (mult/start! m)
                      (sync/post! mailbox ::end)
                      (sync/spawn! (spin (await (mult/mult-pump m)))
                                   {:on-success #(reset! result [:ok %])
                                    :on-error #(reset! result [:error %])})
                      (let [deadline (+ (System/nanoTime) 1000000000)]
                        (loop []
                          (when (and (not (simple/events-settled? world))
                                     (< (System/nanoTime) deadline))
                            (java.util.concurrent.locks.LockSupport/parkNanos 100000)
                            (recur))))
                      [(mult/mult-closed? m) @result]))
                  (finally (ctx/close-context! world))))))]
       (is (= {[true [:ok nil]] 1000} outcomes) (str outcomes)))))
