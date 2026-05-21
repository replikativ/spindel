(ns org.replikativ.spindel.stale-lexical-scope-test
  "REGRESSION SPEC for the stale-lexical-scope engine bug.

   A `(spin …)` form captures lexical values from its enclosing scope.
   When the enclosing scope re-runs, the form is re-evaluated → a fresh
   closure with fresh captures, but the SAME deterministic id. The engine
   keeps the old node's cached result; whether the stale cache is served
   or the fresh closure runs depends on WHICH re-execution path fired.

   `invalidate-created-spins!` papers over this on the track-resume and
   direct-invoke paths. These tests probe the same closure-capture gap
   across different re-execution forms — notably the await-cascade resume
   path, where `invalidate-created-spins!` is not reached.

   Tests that fail here are the target of the engine redesign. They are
   tagged ^:stale-scope-spec so the default suite can exclude them until
   the redesign lands."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-async :refer [await-drain]]
            [org.replikativ.spindel.test-helpers :as th]))

;; =============================================================================
;; Form 1 — baseline: nested spin over a track-derived local, parent re-runs
;; via track-resume. This is the form `invalidate-created-spins!` covers
;; (same as nested-spin-invalidation-test). Expected: PASS.
;; =============================================================================

(deftest ^:stale-scope-spec form-1-track-resume-baseline
  (testing "nested spin over track-derived local; parent re-runs via track-resume"
    (th/with-ctx [ctx]
      (let [s (sig/signal 2)
            outer (spin
                   (let [{m :new} (track s)]
                     (let [inner (spin (* 10 m))]
                       (await inner))))]
        (is (= 20 @outer) "first run: 10 * 2")
        (reset! s 3)
        (await-drain ctx)
        (is (= 30 @outer) "after s change — inner must see m=3")))))

;; =============================================================================
;; Form 2 — nested spin captures an AWAIT-derived local; the parent re-runs
;; because an awaited reactive child re-completes (await-cascade resume).
;; This path does not go through `invalidate-created-spins!`.
;; =============================================================================

(deftest ^:stale-scope-spec form-2-await-cascade-nested
  (testing "nested spin over await-result; parent re-runs via await-cascade"
    (th/with-ctx [ctx]
      (let [s (sig/signal 2)
            data (spin (let [{v :new} (track s)] v))
            parent (spin
                    (let [r (await data)]
                      (let [inner (spin (* 10 r))]
                        (await inner))))]
        (is (= 20 @parent) "first run: 10 * 2")
        (reset! s 3)
        (await-drain ctx)
        (is (= 30 @parent) "after s change — inner must see r=3")))))

;; =============================================================================
;; Form 3 — two nesting levels under an await-cascade resume.
;; =============================================================================

(deftest ^:stale-scope-spec form-3-await-cascade-deep
  (testing "two nesting levels under an await-cascade resume"
    (th/with-ctx [ctx]
      (let [s (sig/signal 2)
            data (spin (let [{v :new} (track s)] v))
            parent (spin
                    (let [r (await data)]
                      (let [mid (spin
                                 (let [inner (spin (* 10 r))]
                                   (await inner)))]
                        (await mid))))]
        (is (= 20 @parent) "first run: 10 * 2")
        (reset! s 3)
        (await-drain ctx)
        (is (= 30 @parent) "after s change — deep inner must see r=3")))))

;; =============================================================================
;; Form 4 — two sibling nested spins each capturing the same track-derived
;; local; track-resume. Probes whether sibling created-spins are all updated.
;; =============================================================================

(deftest ^:stale-scope-spec form-4-sibling-spins-track
  (testing "two sibling nested spins capture an outer local; track-resume"
    (th/with-ctx [ctx]
      (let [s (sig/signal 2)
            parent (spin
                    (let [{m :new} (track s)
                          a (spin (* 10 m))
                          b (spin (* 100 m))]
                      [(await a) (await b)]))]
        (is (= [20 200] @parent) "first run")
        (reset! s 3)
        (await-drain ctx)
        (is (= [30 300] @parent) "after s change — both siblings must see m=3")))))

;; =============================================================================
;; Form 5 — inner spin tracks its OWN signal AND captures an outer local.
;; After the outer re-runs (re-creating inner with a fresh capture), the
;; inner's own signal fires: does the inner's own re-run see the fresh
;; outer capture, or a stale one?
;; =============================================================================

(deftest ^:stale-scope-spec form-5-reactive-inner-captures-outer
  (testing "inner spin tracks its own signal AND captures an outer local"
    (th/with-ctx [ctx]
      (let [s (sig/signal 10)
            t (sig/signal 1)
            outer (spin
                   (let [{v :new} (track s)]
                     (let [inner (spin (let [{w :new} (track t)] (+ v w)))]
                       (await inner))))]
        (is (= 11 @outer) "first run: 10 + 1")
        (reset! s 20)
        (await-drain ctx)
        (is (= 21 @outer) "after s change: 20 + 1")
        (reset! t 5)
        (await-drain ctx)
        (is (= 25 @outer)
            "after t change — inner re-runs on its own signal; must use v=20")))))

;; =============================================================================
;; Form 6 — under await-cascade, prove the stale nested spin's BODY never
;; re-runs (not merely that the value is wrong) via an execution counter.
;; =============================================================================

(deftest ^:stale-scope-spec form-6-await-cascade-body-not-rerun
  (testing "under await-cascade, the stale nested spin's body must re-run"
    (th/with-ctx [ctx]
      (let [s (sig/signal 2)
            runs (atom 0)
            data (spin (let [{v :new} (track s)] v))
            parent (spin
                    (let [r (await data)]
                      (let [inner (spin (swap! runs inc) (* 10 r))]
                        (await inner))))]
        @parent
        (is (= 1 @runs) "inner ran once")
        (reset! s 3)
        (await-drain ctx)
        @parent
        (is (= 2 @runs) "inner must re-run with fresh r")))))

;; =============================================================================
;; Form 7 — nested spin under await-cascade that ALSO tracks its own signal.
;; Its own reactivity must not mask a stale await-derived capture.
;; =============================================================================

(deftest ^:stale-scope-spec form-7-await-cascade-reactive-inner
  (testing "nested reactive spin under await-cascade captures await-result"
    (th/with-ctx [ctx]
      (let [s (sig/signal 2)
            t (sig/signal 1)
            data (spin (let [{v :new} (track s)] v))
            parent (spin
                    (let [r (await data)]
                      (let [inner (spin (let [{w :new} (track t)]
                                          (+ (* 10 r) w)))]
                        (await inner))))]
        (is (= 21 @parent) "first run: 10*2 + 1")
        (reset! s 3)
        (await-drain ctx)
        (is (= 31 @parent) "after s change: 10*3 + 1 — inner must see r=3")))))

;; =============================================================================
;; Form 8 — sibling nested spins under an await-cascade resume.
;; =============================================================================

(deftest ^:stale-scope-spec form-8-await-cascade-siblings
  (testing "sibling nested spins under await-cascade"
    (th/with-ctx [ctx]
      (let [s (sig/signal 2)
            data (spin (let [{v :new} (track s)] v))
            parent (spin
                    (let [r (await data)
                          a (spin (* 10 r))
                          b (spin (* 100 r))]
                      [(await a) (await b)]))]
        (is (= [20 200] @parent) "first run")
        (reset! s 3)
        (await-drain ctx)
        (is (= [30 300] @parent) "after change — both siblings must see r=3")))))
