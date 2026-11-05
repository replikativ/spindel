(ns org.replikativ.spindel.v2.port.retention-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.combinators :as comb :refer [parallel]]
            [org.replikativ.spindel.v2.port.support :refer
             [checking vworld with-world outcome check-result observed-value wait-until required-api]]))

(use-fixtures :each checking)

;; All old tests in this namespace inspect engine implementation details.
;; See .internal/port-report.md for the per-test disposition.
