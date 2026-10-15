(ns org.replikativ.spindel.spin.sleep-release-test
  "A cancelled `sleep` releases its delayed entry and its timer.

  The losing arm of a `race` (and so of every `timeout` whose source wins)
  is a cancelled sleep. It used to keep its `[:engine/delayed-spins]` entry
  and its `[:engine/timer-handles]` handle until the full duration had
  elapsed, and with them the callback and everything it reaches. A dvergr
  experiment wraps each Run in a 10-minute `timeout`, so it held every Run
  of the last ten minutes, forked worlds included, until the heap ran out."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.impl.delayed :as delayed]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.combinators :as comb]))

(def ^:private long-ms 600000)

(defn- delayed-entries [c]
  (reduce + 0 (map count (vals (rtp/get-state c [:engine/delayed-spins])))))

(defn- timer-handles [c]
  (count (rtp/get-state c [:engine/timer-handles])))

(defn- settle
  "Wait (bounded) until `pred` holds: releases run on the drain."
  [pred]
  (loop [n 0]
    (cond (pred) true
          (> n 200) false
          :else (do (Thread/sleep 10) (recur (inc n))))))

(defmacro ^:private in-real-ctx [[c] & body]
  `(let [~c (sp/create-execution-context)]
     (try
       (delayed/set-time-mode! ~c :real)
       (binding [ec/*execution-context* ~c] ~@body)
       (finally (ctx/stop-context! ~c)))))

(deftest a-timeout-whose-source-wins-releases-its-sleep
  (in-real-ctx [c]
               (dotimes [_ 50]
                 (is (= :done @(comb/timeout (sp/spin :done) long-ms :timed-out))))
               (is (settle #(and (zero? (delayed-entries c)) (zero? (timer-handles c))))
                   (str "every losing sleep released its entry and timer; left: "
                        (delayed-entries c) " entries, " (timer-handles c) " timers"))
               (is (empty? (rtp/get-state c [:engine/delayed-spins]))
                   "no empty fire-time buckets are left behind")))

(deftest a-timeout-whose-sleep-wins-still-returns-the-fallback
  (in-real-ctx [c]
               (let [never (sp/deferred)]
                 (is (= :timed-out @(comb/timeout (sp/spin (sp/await never)) 50 :timed-out))))
               (is (settle #(zero? (timer-handles c))) "the fired sleep released its timer")))

(deftest a-sleep-still-delivers-its-value
  (in-real-ctx [c]
               (is (= :woke @(comb/sleep 30 :woke)))
               (is (settle #(and (zero? (delayed-entries c)) (zero? (timer-handles c)))))))

(deftest cancelling-a-sleep-releases-its-entry-and-settles-its-awaiter
  (in-real-ctx [c]
               (let [s (comb/sleep long-ms :never)
                     watcher (sp/spin (try (sp/await s) (catch Exception _ :cancelled)))
                     result (future @watcher)]
                 (is (settle #(= 1 (delayed-entries c))) "the sleep is scheduled")
                 (spin-core/cancel-spin! s)
                 (is (= :cancelled (deref result 5000 :still-waiting))
                     "the awaiter of a cancelled sleep finishes with the cancellation")
                 (is (settle #(and (zero? (delayed-entries c)) (zero? (timer-handles c))))
                     "the cancelled sleep released its entry and timer"))))

(deftest cancelling-an-inherited-sleep-in-a-fork-leaves-the-parent-running
  (in-real-ctx [c]
               (let [s (comb/sleep 200 :woke)
                     result (future @s)]
                 (is (settle #(= 1 (delayed-entries c))) "the parent's sleep is scheduled")
                 (let [f (ctx/fork-context c)]
                   (try
                     (binding [ec/*execution-context* f] (spin-core/cancel-spin! s))
                     (finally (ctx/stop-context! f))))
                 (is (= :woke (deref result 5000 :stranded))
                     "the parent's sleep still wakes after a fork cancelled its copy"))))

(deftest immediate-cancels-leave-nothing-behind
  (in-real-ctx [c]
               (let [watchers (doall
                               (for [_ (range 200)]
                                 (let [s (comb/sleep long-ms :never)
                                       w (sp/spin (try (sp/await s) (catch Exception _ :cancelled)))
                                       r (future @w)]
                                   (spin-core/cancel-spin! s)
                                   r)))]
                 (is (every? #(= :cancelled (deref % 5000 :still-waiting)) watchers)
                     "every awaiter of an immediately cancelled sleep finishes")
                 (is (settle #(and (zero? (delayed-entries c)) (zero? (timer-handles c))))
                     (str "no entry or timer is left; left: " (delayed-entries c) " entries, "
                          (timer-handles c) " timers")))))

(deftest the-losing-sleep-of-a-race-is-released
  (in-real-ctx [c]
               (is (= :fast @(comb/race (comb/sleep 20 :fast) (comb/sleep long-ms :slow))))
               (is (settle #(and (zero? (delayed-entries c)) (zero? (timer-handles c))))
                   "the slow sleep, cancelled by the race, released its entry")))
