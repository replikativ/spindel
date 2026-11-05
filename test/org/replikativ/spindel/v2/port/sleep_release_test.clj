(ns org.replikativ.spindel.v2.port.sleep-release-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.port.support2 :as h]))

(use-fixtures :each h/fixture)

;; Timer release is tested through lexical cleanup and absence of late work;
;; old delayed-entry and timer-handle map assertions are intentionally omitted.
(deftest a-timeout-whose-source-wins-releases-its-sleep
  (dotimes [_ 50]
    (is (= :done (h/result (comb/timeout (spin :done) 600000 :timed-out))))))

(deftest a-timeout-whose-sleep-wins-still-returns-the-fallback
  (is (= :timed-out (h/result (comb/timeout (v2/deferred) 20 :timed-out)))))

(deftest a-sleep-still-delivers-its-value
  (is (= :woke (h/result (comb/sleep 20 :woke)))))

(deftest cancelling-a-sleep-releases-its-entry-and-settles-its-awaiter
  (let [cleaned (promise)
        s (task (try (v2/sleep 600000) :never (finally (deliver cleaned :released))))
        watcher (task (try (await s) (catch Exception e (if (v2/cancelled? e) :cancelled :wrong-error))))]
    (v2/cancel-task! s)
    (is (= :cancelled (h/result watcher)))
    (is (= :released (deref cleaned 2000 ::timeout)))))

(deftest cancelling-an-inherited-sleep-in-a-fork-leaves-the-parent-running
  (let [s (task (v2/sleep 200) :woke)
        child (v2/fork! v2/*world*) cs (v2/in-world child s)]
    (v2/cancel-task! cs)
    (is (v2/cancelled? (h/result cs)))
    (is (= :woke (h/result s)))))

(deftest immediate-cancels-leave-nothing-behind
  (let [cleaned (atom 0)
        watchers (mapv (fn [_]
                         (let [s (task (try (v2/sleep 600000) :never (finally (swap! cleaned inc))))
                               w (task (try (await s) (catch Exception e (if (v2/cancelled? e) :cancelled :wrong-error))))]
                           (v2/cancel-task! s) w)) (range 200))]
    (is (every? #(= :cancelled (h/result %)) watchers))
    (is (= 200 @cleaned))))

(deftest the-losing-sleep-of-a-race-is-released
  (let [cleaned (promise) late (atom false)
        slow (spin (try (v2/sleep 600000) (reset! late true) :slow
                        (finally (deliver cleaned :released))))]
    (is (= :fast (h/result (comb/race (comb/sleep 20 :fast) slow))))
    (is (= :released (deref cleaned 2000 ::timeout)))
    (is (false? @late))))
