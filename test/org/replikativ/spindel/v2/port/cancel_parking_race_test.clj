(ns org.replikativ.spindel.v2.port.cancel-parking-race-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.port.support2 :as h]
            [org.replikativ.spindel.v2.verify :as verify]))

(use-fixtures :each h/fixture)

(deftest a-spin-that-parks-while-it-is-cancelled-is-rejected
  ;; Race public admissions instead of redefining the old abort implementation.
  ;; A fresh asynchronous world lets task start, cancel and delivery compete.
  (dotimes [_ 50]
    (let [divergences (atom [])
          w (v2/world {:inline? false :verify? true :hook (verify/checking-hook divergences)})]
      (try
        (binding [v2/*world* w]
          (let [d (v2/deferred) entered (promise)
                t (task (deliver entered :starting) (await d))
                response (promise)]
            (v2/value-async t #(deliver response [%1 %2]))
            (is (= :starting (deref entered 2000 ::timeout)))
            @(future (v2/cancel-task! t))
            (let [[v err?] (deref response 2000 [::stranded false])]
              (is (true? err?)) (is (v2/cancelled? v)))
            (d :late)
            (is (v2/cancelled? (h/result t)))
            (is (empty? @divergences) (str "Rule R divergences: " @divergences))))
        (finally (v2/release-world! w))))))
