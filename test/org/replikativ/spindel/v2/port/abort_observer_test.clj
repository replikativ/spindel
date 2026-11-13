(ns org.replikativ.spindel.v2.port.abort-observer-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.port.support2 :as h]))

(use-fixtures :each h/fixture)

;; abort-invalidates-reactive-observer is dropped: it invokes the internal
;; abort-spin-chain! transition before completion publication, inspecting
;; dirty flags and completion subscriptions. v2 has no such public operation.
