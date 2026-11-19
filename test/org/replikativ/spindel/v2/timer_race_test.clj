(ns org.replikativ.spindel.v2.timer-race-test
  "A timer whose callback has started is not cancelled: `unschedule!` answers
   false, so the engine never acknowledges a timer resource twice (once from
   its cancel, once from its fire)."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.host :as hs]))

(deftest unschedule-loses-to-a-running-callback
  (let [started (promise) release (promise) ran (atom 0)
        t (hs/schedule! 0 (fn [] (deliver started true) @release (swap! ran inc)))]
    (is (true? (deref started 2000 ::timeout)))
    (is (not (hs/unschedule! t)) "the callback is running: the timer fired")
    (deliver release true)
    (Thread/sleep 50)
    (is (= 1 @ran))))

(deftest unschedule-wins-before-the-callback
  (let [ran (atom 0)
        t (hs/schedule! 200 (fn [] (swap! ran inc)))]
    (is (true? (hs/unschedule! t)))
    (Thread/sleep 300)
    (is (zero? @ran) "cancelled: never runs")
    (is (not (hs/unschedule! t)) "a second unschedule does not claim it again")))

(deftest exactly-one-side-wins
  (testing "racing cancels against due timers: the callback runs iff unschedule! answered false"
    (dotimes [_ 2000]
      (let [ran (atom 0)
            t (hs/schedule! 0 (fn [] (swap! ran inc)))
            cancelled? (boolean (hs/unschedule! t))]
        (Thread/sleep 1)
        (loop [i 0] (when (and (not cancelled?) (zero? @ran) (< i 1000)) (Thread/sleep 1) (recur (inc i))))
        (is (= (if cancelled? 0 1) @ran))))))
