(ns org.replikativ.spindel.engine.signal-stress-test
  "Stress tests pinning the engine invariant: every `(swap! signal …)`
  followed by `(await-drain ctx)` advances every dependent spin body
  exactly once.

  Pre-fix history: the JVM Cleaner-based GC cleanup fired on a
  reactive spin whose `Spin` Java object had become unreachable
  (e.g. the user's `let` binding went out of scope after last use),
  even though the spin still had a live `(track …)` continuation
  in `:track-subscriptions`. `full-cleanup-spin!` wiped the cont and the
  signal's observer registration; subsequent signal-changes found
  no observer and silently no-op'd. The render-count test in
  `dom/render_test.cljc` saw this as flake: 3 of 5 swap!s sometimes
  failed to re-render.

  Fix: `try-gc-cleanup-spin!` now also checks for live signal
  continuations. If any exist, the spin is marked `:orphaned?` but
  its state is preserved so reactive updates keep flowing.

  These tests are JVM-only because `await-drain` on CLJS cannot
  synchronously observe setTimeout-driven workers complete."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]
            #?(:clj [org.replikativ.spindel.test-async :refer [await-drain]])
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.test-helpers :refer [with-ctx]])))

#?(:clj
   (deftest stress-many-updates-no-explicit-hold
     (testing "1000 swap!s on one signal observed by one spin must produce
               1001 body re-runs even when the user does NOT explicitly hold
               the spin reference. The Cleaner thread may decide the Spin
               Java object is unreachable mid-loop; the engine must keep its
               continuations alive."
       (with-ctx [rt]
         (let [signal-ref (sig/signal 0)
               run-count (atom 0)
               body-spin (spin
                          (track signal-ref)
                          (swap! run-count inc)
                          nil)
               n 1000]
           (body-spin identity identity)
           (await-drain rt)
           (is (= 1 @run-count))
           (dotimes [_ n]
             (swap! signal-ref inc)
             (await-drain rt))
           (is (= (inc n) @run-count)
               (str "Expected " (inc n) " runs, got " @run-count
                    ". Dropped " (- (inc n) @run-count) ".")))))))

#?(:clj
   (deftest stress-multiple-signals-one-body
     (testing "300 swap!s alternating across 3 signals tracked by one body
               must produce 301 body re-runs."
       (with-ctx [rt]
         (let [s1 (sig/signal 0)
               s2 (sig/signal 0)
               s3 (sig/signal 0)
               run-count (atom 0)
               body-spin (spin
                          (track s1) (track s2) (track s3)
                          (swap! run-count inc)
                          nil)
               n 300]
           (body-spin identity identity)
           (await-drain rt)
           (dotimes [i n]
             (case (mod i 3)
               0 (swap! s1 inc)
               1 (swap! s2 inc)
               2 (swap! s3 inc))
             (await-drain rt))
           (is (= (inc n) @run-count)
               (str "Expected " (inc n) " runs, got " @run-count
                    ". Dropped " (- (inc n) @run-count) ".")))))))
