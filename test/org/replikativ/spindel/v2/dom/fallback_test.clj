(ns org.replikativ.spindel.v2.dom.fallback-test
  "Pending and fallback with `await-any` and a timer (phase-d plan P5; React
   comparison gap 4, §2.6). A deferred region shows its fallback when the
   timer wins and keeps the old content while it waits otherwise: a dirty
   root keeps its last result until it settles (spec §4.5 rule 5), and the
   loser child keeps its edge, so its settling reruns the region.

   The timer is a computation. A later run whose timer has the same
   captures adopts it with its cached settled result, so it wins at once
   and arms no new timer; changed captures rerun it and arm a new one. So
   the timer must capture what starts a new wait: here the query. If a
   fresh wait can start without the query value changing (the same query
   fetched again), the timer needs a request generation among its captures.

   The ordering cases run the engine's real `sleep` on a manual host clock
   the test advances (`hs/schedule!` redefined), so no assertion depends on
   wall-clock scheduling. One integration case uses the real timer and
   asserts only what holds however the process is scheduled."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track await await-any]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

(def ^:private delay-ms 150)

;; ---------------------------------------------------------------------------
;; A manual host clock

(defrecord ^:private ManualTimer [due f claimed])

(defn- manual-clock
  "A clock at 0 with no timers: {:now atom :timers atom}."
  []
  {:now (atom 0) :timers (atom [])})

(defn- with-clock
  "Calls `(f)` with the host timers on `clock`: a timer fires only when
   `advance!` moves the clock past its deadline. As the host's, a timer is
   claimed once, by its firing or by `unschedule!`."
  [clock f]
  (let [orig-unschedule hs/unschedule!
        orig-timer? hs/timer?]
    (with-redefs [hs/schedule! (fn [ms g]
                                 (let [t (->ManualTimer (+ @(:now clock) (long ms)) g (atom false))]
                                   (swap! (:timers clock) conj t)
                                   t))
                  hs/unschedule! (fn [t]
                                   (if (instance? ManualTimer t)
                                     (compare-and-set! (:claimed t) false true)
                                     (orig-unschedule t)))
                  hs/timer? (fn [t] (or (instance? ManualTimer t) (orig-timer? t)))]
      (f))))

(defn- advance!
  "Moves `clock` by `ms`, fires the timers now due in deadline order, and
   settles `env`."
  [env clock ms]
  (let [now (swap! (:now clock) + ms)
        [old _] (swap-vals! (:timers clock) (fn [ts] (filterv #(> (:due %) now) ts)))]
    (doseq [t (sort-by :due (filter #(<= (:due %) now) old))]
      (when (compare-and-set! (:claimed t) false true) ((:f t))))
    (fx/settle! env)))

;; ---------------------------------------------------------------------------
;; The region

(defn- dom [env] (mock/dom (:discharge (:mock env)) :container))

(defn- texts
  "The texts the region committed, in order, read from the operation log."
  [env]
  (into [] (comp (filter #(#{:create-text :set-text} (:op %))) (map :text))
        @(:log (:mock env))))

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
  "A timer with constant captures: adopted with its cached settled result
   after its first run."
  [_q]
  (comb/sleep delay-ms ::pending))

(defn- region-text [env] (get-in (dom env) [0 2]))

(defn- fetches-for [qs] (into {} (map (fn [q] [q (v2/deferred)])) qs))

;; ---------------------------------------------------------------------------
;; Ordering, on the manual clock

(deftest a-region-shows-its-fallback-late-and-keeps-old-content
  (fx/each-world
   (fn [env]
     (let [clock (manual-clock)]
       (with-clock
         clock
         (fn []
           (let [fetches (fetches-for [1 2 3])
                 query (v2/signal 1)
                 {:keys [state] :as ctl} (fx/render! env (region query fetches per-query-timer))]
             (testing "first load: nothing, then the fallback at the delay, then the content"
               (is (= 0 (render/revision state)) "the region waits: nothing to commit")
               (advance! env clock (dec delay-ms))
               (is (= 0 (render/revision state)) "not before the delay")
               (advance! env clock 1)
               (is (= "loading" (region-text env)) "the fallback at the delay")
               (v2/deliver! (fetches 1) "!")
               (fx/settle! env)
               (is (= "content 1!" (region-text env))))
             (testing "a fast fetch: the old content stays until the new one, no fallback"
               (let [n (count (texts env))]
                 (fx/write! env query 2)
                 (advance! env clock (dec delay-ms))
                 (is (= "content 1!" (region-text env)) "the old content while the new fetch is pending")
                 (v2/deliver! (fetches 2) "!")
                 (fx/settle! env)
                 (is (= "content 2!" (region-text env)))
                 (advance! env clock (* 2 delay-ms))
                 (is (= "content 2!" (region-text env)) "the timer firing later changes nothing")
                 (is (not-any? #{"loading"} (drop n (texts env))) "the fallback was never committed")))
             (testing "a slow fetch: the old content until the delay, then the fallback, then the content"
               (fx/write! env query 3)
               (advance! env clock (dec delay-ms))
               (is (= "content 2!" (region-text env)))
               (advance! env clock 1)
               (is (= "loading" (region-text env)))
               (v2/deliver! (fetches 3) "!")
               (fx/settle! env)
               (is (= "content 3!" (region-text env))))
             (fx/unmount! env ctl)
             (is (empty? (fx/leftovers env state))))))))))

(deftest a-timer-with-unchanged-captures-wins-every-later-wait
  (fx/each-world
   (fn [env]
     (let [clock (manual-clock)]
       (with-clock
         clock
         (fn []
           (let [fetches (fetches-for [1 2])
                 query (v2/signal 1)
                 {:keys [state] :as ctl} (fx/render! env (region query fetches shared-timer))]
             (advance! env clock delay-ms)
             (is (= "loading" (region-text env)))
             (v2/deliver! (fetches 1) "!")
             (fx/settle! env)
             (is (= "content 1!" (region-text env)))
             (fx/write! env query 2)
             (is (= "loading" (region-text env))
                 "adopted with its cached settled result: the fallback wins at once, the old content is not kept")
             (is (empty? @(:timers clock)) "and no new timer is armed")
             (v2/deliver! (fetches 2) "!")
             (fx/settle! env)
             (is (= "content 2!" (region-text env)))
             (fx/unmount! env ctl)
             (is (empty? (fx/leftovers env state))))))))))

;; ---------------------------------------------------------------------------
;; Integration, on the real timer: only scheduling-independent assertions

(defn- wait-until
  "Pumps `env` until `(pred)` holds; false after the fixture's deadline."
  [env pred]
  (let [deadline (+ (System/currentTimeMillis) fx/wait-ms)]
    (loop []
      (fx/settle! env)
      (cond (pred) true
            (> (System/currentTimeMillis) deadline) false
            :else (do (Thread/sleep 2) (recur))))))

(deftest the-real-timer-shows-the-fallback-no-earlier-than-the-delay
  (fx/each-world
   (fn [env]
     (let [fetches (fetches-for [1])
           query (v2/signal 1)
           t0 (System/nanoTime)                ; before the render arms the timer
           {:keys [state] :as ctl} (fx/render! env (region query fetches per-query-timer))]
       (is (wait-until env #(= "loading" (region-text env))))
       (is (>= (quot (- (System/nanoTime) t0) 1000000) delay-ms) "no earlier than the delay")
       (v2/deliver! (fetches 1) "!")
       (is (wait-until env #(= "content 1!" (region-text env))))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))
