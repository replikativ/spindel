(ns org.replikativ.spindel.v2.dom.fallback-test
  "Pending and fallback with `await-any` and a timer (phase-d plan P5; React
   comparison gap 4, §2.6). A deferred region shows its fallback when the
   timer wins and keeps the old content while it waits otherwise: a dirty
   root keeps its last result until it settles (spec §4.5 rule 5), and the
   loser child keeps its edge, so its settling reruns the region.

   The timer is a computation, and a computation that settled is final:
   adopted by a later run with the same captures, it is settled at once
   and does not arm again. So the timer must capture what starts a new
   wait (here the query); a timer with constant captures wins every later
   wait at once."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track await await-any]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

(def ^:private delay-ms 150)

(defn- dom [env] (mock/dom (:discharge (:mock env)) :container))

(defn- texts
  "The texts the region committed, in order, read from the operation log."
  [env]
  (into [] (comp (filter #(#{:create-text :set-text} (:op %))) (map #(or (:text %) (:content %))))
        @(:log (:mock env))))

(defn- wait-until
  "Pumps `env` until `(pred)` holds; false after the fixture's deadline."
  [env pred]
  (let [deadline (+ (System/currentTimeMillis) fx/wait-ms)]
    (loop []
      (fx/settle! env)
      (cond (pred) true
            (> (System/currentTimeMillis) deadline) false
            :else (do (Thread/sleep 2) (recur))))))

(defn- pump-for
  "Pumps `env` for `ms` milliseconds."
  [env ms]
  (let [end (+ (System/currentTimeMillis) ms)]
    (while (< (System/currentTimeMillis) end)
      (fx/settle! env)
      (Thread/sleep 2))))

(defn- region
  "The content fetched for the query, or \"loading\" once `delay-ms` pass
   before it arrives. `fetches`: query -> deferred. `timer` makes the timer
   computation for a query."
  [query fetches timer]
  (spin (let [q (iv/get-new (track query))
              child (spin (str "content " q (await (get fetches q))))
              v (await-any [child (timer q)])]
          (el/div {:class "region"} (if (string? v) v "loading")))))

(defn- per-query-timer
  "A timer that captures the query: a new query is a new wait."
  [q]
  (spin (v2/sleep delay-ms) [::pending q]))

(defn- shared-timer
  "A timer with constant captures: adopted and final after its first run."
  [_q]
  (comb/sleep delay-ms ::pending))

(defn- region-text [env] (get-in (dom env) [0 2]))

(deftest a-region-shows-its-fallback-late-and-keeps-old-content
  (fx/each-world
   (fn [env]
     (let [fetches (into {} (map (fn [q] [q (v2/deferred)])) [1 2 3])
           query (v2/signal 1)
           {:keys [state] :as ctl} (fx/render! env (region query fetches per-query-timer))]
       (testing "first load: nothing, then the fallback after the delay, then the content"
         (let [t0 (System/currentTimeMillis)]
           (is (= 0 (render/revision state)) "the region waits: nothing to commit")
           (is (wait-until env #(= "loading" (region-text env))))
           (is (>= (- (System/currentTimeMillis) t0) delay-ms) "not before the delay")
           (v2/deliver! (fetches 1) "!")
           (is (wait-until env #(= "content 1!" (region-text env))))))
       (testing "a fast fetch: the old content stays until the new one, no fallback"
         (let [n (count (texts env))]
           (fx/write! env query 2)
           (pump-for env (quot delay-ms 3))
           (is (= "content 1!" (region-text env)) "the old content while the new fetch is pending")
           (v2/deliver! (fetches 2) "!")
           (is (wait-until env #(= "content 2!" (region-text env))))
           (pump-for env (* 2 delay-ms))
           (is (= "content 2!" (region-text env)) "the timer firing later changes nothing")
           (is (not-any? #{"loading"} (drop n (texts env))) "the fallback was never committed")))
       (testing "a slow fetch: the old content until the delay, then the fallback, then the content"
         (fx/write! env query 3)
         (pump-for env (quot delay-ms 3))
         (is (= "content 2!" (region-text env)))
         (is (wait-until env #(= "loading" (region-text env))))
         (v2/deliver! (fetches 3) "!")
         (is (wait-until env #(= "content 3!" (region-text env)))))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))

(deftest a-timer-with-constant-captures-does-not-arm-again
  (fx/each-world
   (fn [env]
     (let [fetches (into {} (map (fn [q] [q (v2/deferred)])) [1 2])
           query (v2/signal 1)
           {:keys [state] :as ctl} (fx/render! env (region query fetches shared-timer))]
       (is (wait-until env #(= "loading" (region-text env))))
       (v2/deliver! (fetches 1) "!")
       (is (wait-until env #(= "content 1!" (region-text env))))
       (fx/write! env query 2)
       (is (= "loading" (region-text env))
           "the adopted timer is settled: the fallback wins at once, the old content is not kept")
       (v2/deliver! (fetches 2) "!")
       (is (wait-until env #(= "content 2!" (region-text env))))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))
