(ns org.replikativ.spindel.v2.port.blocking-portable-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin await]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture outcome]]))

(use-fixtures :each checked-fixture)

(deftest blocking-resolves-with-the-value-of-f
  (is (= 42 (v2/value (spin (inc (await (comb/blocking (fn [] 41))))) 5000 ::timeout))))

(deftest blocking-rejects-with-the-throw-of-f
  (let [[tag e] (outcome (spin (await (comb/blocking (fn [] (throw (ex-info "boom" {:code 7})))))))]
    (is (= :err tag)) (is (= 7 (:code (ex-data e))))))
