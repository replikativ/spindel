(ns org.replikativ.spindel.engine.interval-redelivery-test
  "A track site hands out a signal's deltas once per change.

  A root spin tracks `a` and then awaits a child that tracks `b`. When `a`
  changes, the root resumes at its `a` site. When later only `b` changes,
  the child's change escalates to the root, which re-runs from its earliest
  track continuation — the `a` site — though `a` did not change. That
  continuation must not hand out `a`'s previous deltas again: a consumer
  applying them (an ifor-each, a DOM list) would apply them twice."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.test-async :refer [await-drain]]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]))

(deftest a-resumed-track-site-does-not-hand-out-its-deltas-again
  (with-ctx [rt]
    (let [a (sig/signal [])
          b (sig/signal 0)
          seen (atom [])
          child (fn [] (spin (iv/get-new (track b))))
          root (spin (let [ia (track a)]
                       (swap! seen conj (:deltas ia))
                       (await (child))))]
      @root
      (swap! a conj :x)
      (await-drain rt)
      (testing "a's change is delivered with its deltas"
        (is (some? (last @seen))))
      (let [after-a (count @seen)]
        (swap! b inc)
        (await-drain rt)
        (testing "b's change re-runs the root (escalation), but a did not change"
          (is (< after-a (count @seen)) "the root re-ran")
          (is (nil? (last @seen))
              (str "a's deltas handed out again: " (pr-str (last @seen)))))))))
