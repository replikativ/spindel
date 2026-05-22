(ns org.replikativ.spindel.engine.track-continuation-test
  "Regression tests guarding the invariant that track continuations are
  bounded by the number of (track ...) call sites executed in the spin's
  body, not by the number of external signal changes.

  These tests guard against an accidental re-introduction of unbounded
  continuation accumulation under repeated signal updates."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.effects.track :refer [track]]))

(defn- cont-count [spin-id]
  ;; Continuations are split into :track-subscriptions (comonadic) and
  ;; :await-conts (monadic) — count both for a spin's total.
  (+ (count (ec/get-state [:track-subscriptions spin-id]))
     (count (ec/get-state [:await-conts spin-id]))))

(deftest single-track-stays-bounded-under-many-signal-changes
  (testing "A spin with one track call site retains exactly one continuation
            after thousands of signal changes."
    (let [ctx-root (ctx/create-execution-context)
          ;; Hold the spin object so the JVM Cleaner doesn't reap it mid-test
          hold (atom nil)]
      (try
        (binding [ec/*execution-context* ctx-root]
          (let [s   (sig/signal 0)
                obs (spin (let [{:keys [new]} (track s)] (* 2 new)))
                _   (reset! hold obs)
                tid (spin-core/spin-id obs)]
            @obs
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)
            (is (= 1 (cont-count tid)) "one continuation after initial run")
            (dotimes [_ 1000]
              (swap! s inc)
              (simple/await-drain-complete! ctx-root :timeout-ms 2000))
            (is (= 1 (cont-count tid))
                "one continuation after 1000 signal changes")
            (is (some? @hold))))
        (finally
          (ctx/stop-context! ctx-root))))))

(deftest track-in-loop-bounded-by-call-site-count-not-changes
  (testing "A spin that calls track inside a loop accumulates one
            continuation per loop-iteration × track-site, but does NOT
            grow with the number of subsequent signal changes."
    (let [ctx-root (ctx/create-execution-context)
          hold (atom nil)]
      (try
        (binding [ec/*execution-context* ctx-root]
          (let [s1  (sig/signal 0)
                s2  (sig/signal 0)
                obs (spin
                     (loop [n 5 acc 0]
                       (if (zero? n)
                         acc
                         (let [{a :new} (track s1)
                               {b :new} (track s2)]
                           (recur (dec n) (+ acc a b))))))
                _   (reset! hold obs)
                tid (spin-core/spin-id obs)]
            @obs
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)
            ;; 5 loop iterations × 2 tracks per iter = 10 call sites executed.
            (is (= 10 (cont-count tid))
                "10 continuations after one execution (5 iters × 2 tracks)")
            (dotimes [_ 100]
              (swap! s1 inc)
              (simple/await-drain-complete! ctx-root :timeout-ms 2000))
            (is (= 10 (cont-count tid))
                "still 10 continuations after 100 s1 changes")
            (dotimes [_ 100]
              (swap! s2 inc)
              (simple/await-drain-complete! ctx-root :timeout-ms 2000))
            (is (= 10 (cont-count tid))
                "still 10 continuations after 100 s2 changes")
            (is (some? @hold))))
        (finally
          (ctx/stop-context! ctx-root))))))
