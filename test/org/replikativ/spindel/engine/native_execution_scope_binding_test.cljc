(ns org.replikativ.spindel.engine.native-execution-scope-binding-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as signal]
            [org.replikativ.spindel.spin.cps :refer [spin]]))

(deftest public-spin-preserves-an-explicit-owner-across-reactive-resume
  (let [rt (context/create-execution-context {:engine :owned})
        scope (lifetime/open-scope! rt :explicit)
        bindings (atom []) values (atom []) errors (atom [])]
    (try
      (binding [ec/*execution-context* rt]
        (let [driver (signal/signal 0)
              task (spin
                    (lifetime/with-owner scope
                      (let [value (iv/get-new (track driver))]
                        (swap! bindings conj [value (identical? scope ec/*owner-scope*)])
                         ;; Fresh IDs distinguish retained ownership from a
                         ;; previous source allocation's cached owner.
                        (signal/register-signal! rt (signal/->SignalRef [:public-after value] value))
                        value)))]
          (task #(swap! values conj %) #(swap! errors conj %))
          (reset! driver 1)))
      (is (empty? @errors))
      (is (= [0 1] @values))
      (is (= [[0 true] [1 true]] @bindings))
      (let [after (owned/snapshot rt)]
        (is (= [:scope :id 0] (get-in after [:entities [:public-after 0] :owner])))
        (is (= [:scope :id 0] (get-in after [:entities [:public-after 1] :owner]))))
      (finally (context/release-context! rt)))))
