(ns org.replikativ.spindel.spin.cancel-parking-race-test
  "Regression: `cancel-spin!` from another thread while the spin is about to
  park on an await.

  The await registers its continuation and then re-checks whether the spin
  was cancelled; `cancel-spin!` caches the cancellation and then rejects the
  parked continuations. One of the two must see the other. `cancel-spin!`
  used to read the parked continuations BEFORE caching the cancellation, so
  an await that parked in between was missed by both: the spin stayed parked,
  a later delivery was dropped as cancelled, and a deref never returned (a
  dvergr job cancelled while its work started settled neither way).

  The test makes the interleaving deterministic: the spin parks inside
  `cancel-spin!`, just before the cancellation is cached."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]))

(deftest a-spin-that-parks-while-it-is-cancelled-is-rejected
  (let [context (ctx/create-execution-context)]
    (try
      (binding [ec/*execution-context* context]
        (let [d (sync/create-deferred context)
              s (spin (await d))
              outcome (promise)
              abort spin-core/abort-spin-chain!]
          (with-redefs [spin-core/abort-spin-chain!
                        (fn [sid err]
                          ;; the spin runs to its await and parks, on this
                          ;; thread, between cancel-spin!'s start and its
                          ;; cache write
                          (s (fn [v] (deliver outcome [:resolved v]))
                             (fn [e] (deliver outcome [:rejected (:type (ex-data e))])))
                          (abort sid err))]
            (spin-core/cancel-spin! s))
          (is (= [:rejected spin-core/spin-cancelled] (deref outcome 5000 ::stranded))
              "the parked await is rejected with the cancellation")
          (is (empty? (ec/get-state [:await-conts (spin-core/spin-id s)]))
              "no continuation stays parked")))
      (finally
        (ctx/stop-context! context)))))
