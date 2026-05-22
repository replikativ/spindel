(ns org.replikativ.spindel.stale-lexical-scope-test
  "REGRESSION SPEC for the stale-lexical-scope engine bug.

   A `(spin …)` form captures lexical values from its enclosing scope.
   When the enclosing scope re-runs, the form is re-evaluated → a fresh
   closure with fresh captures, but the SAME deterministic id. The bug:
   the engine kept the old node `:clean` and served the stale cached
   result instead of running the fresh closure — most visibly on the
   await-cascade resume path, which `invalidate-created-spins!` never
   covered.

   The fix (engine.free-vars + register-spin!): the `spin` macro records
   the body's captured free variables; on re-registration the engine
   `identical?`-compares them and re-runs only when the captured
   environment actually changed.

   Runs on both CLJ and CLJS — the engine is shared `.cljc`, and
   `free-variables` has a per-platform analyzer path (tools.analyzer.jvm
   / cljs.analyzer), so the CLJS run exercises the CLJS analyzer path.

   A spin invoked via `run-spin!` is a reactive subscription: its
   callback fires on *every* completion. Each test therefore drives one
   `run-spin!` and matches on a completion counter — completion 1 is the
   first run, completion 2 is the re-run after the signal mutation."
  (:refer-clojure :exclude [await])
  (:require #?(:clj  [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

(defn- check-rerun
  "Drive one `run-spin!` on the reactive `spin`. Completion 1 → assert
   `expected-1`, apply `mutate!` (which triggers a re-completion);
   completion 2 → assert `expected-2`, finish via `done`."
  [done spin expected-1 mutate! expected-2]
  (let [stage (atom 0)
        fail  (fn [e] (is false (str "unexpected spin error: " e)) (done))]
    (run-spin! spin
               (fn [r]
                 (case (swap! stage inc)
                   1 (do (is (= expected-1 r) "first run") (mutate!))
                   2 (do (is (= expected-2 r) "after change") (done))
                   nil))
               fail)))

;; =============================================================================
;; Form 1 — baseline: nested spin over a track-derived local, parent re-runs
;; via track-resume.
;; =============================================================================

(deftest ^:stale-scope-spec form-1-track-resume-baseline
  (async done
         (with-ctx [_ctx]
           (let [s (sig/signal 2)
                 outer (spin
                        (let [{m :new} (track s)]
                          (let [inner (spin (* 10 m))]
                            (await inner))))]
             (check-rerun done outer 20 #(reset! s 3) 30)))))

;; =============================================================================
;; Form 2 — nested spin captures an AWAIT-derived local; the parent re-runs
;; because an awaited reactive child re-completes (await-cascade resume).
;; =============================================================================

(deftest ^:stale-scope-spec form-2-await-cascade-nested
  (async done
         (with-ctx [_ctx]
           (let [s (sig/signal 2)
                 data (spin (let [{v :new} (track s)] v))
                 parent (spin
                         (let [r (await data)]
                           (let [inner (spin (* 10 r))]
                             (await inner))))]
             (check-rerun done parent 20 #(reset! s 3) 30)))))

;; =============================================================================
;; Form 3 — two nesting levels under an await-cascade resume.
;; =============================================================================

(deftest ^:stale-scope-spec form-3-await-cascade-deep
  (async done
         (with-ctx [_ctx]
           (let [s (sig/signal 2)
                 data (spin (let [{v :new} (track s)] v))
                 parent (spin
                         (let [r (await data)]
                           (let [mid (spin
                                      (let [inner (spin (* 10 r))]
                                        (await inner)))]
                             (await mid))))]
             (check-rerun done parent 20 #(reset! s 3) 30)))))

;; =============================================================================
;; Form 4 — two sibling nested spins each capturing the same track-derived
;; local; track-resume.
;; =============================================================================

(deftest ^:stale-scope-spec form-4-sibling-spins-track
  (async done
         (with-ctx [_ctx]
           (let [s (sig/signal 2)
                 parent (spin
                         (let [{m :new} (track s)
                               a (spin (* 10 m))
                               b (spin (* 100 m))]
                           [(await a) (await b)]))]
             (check-rerun done parent [20 200] #(reset! s 3) [30 300])))))

;; =============================================================================
;; Form 5 — inner spin tracks its OWN signal AND captures an outer local.
;; After the outer re-runs (re-creating inner with a fresh capture), the
;; inner's own signal fires: it must use the fresh outer capture.
;; =============================================================================

(deftest ^:stale-scope-spec form-5-reactive-inner-captures-outer
  (async done
         (with-ctx [_ctx]
           (let [s (sig/signal 10)
                 t (sig/signal 1)
                 outer (spin
                        (let [{v :new} (track s)]
                          (let [inner (spin (let [{w :new} (track t)] (+ v w)))]
                            (await inner))))
                 stage (atom 0)
                 fail (fn [e] (is false (str "unexpected spin error: " e)) (done))]
             (run-spin! outer
                        (fn [r]
                          (case (swap! stage inc)
                            1 (do (is (= 11 r) "first run: 10 + 1") (reset! s 20))
                            2 (do (is (= 21 r) "after s change: 20 + 1") (reset! t 5))
                            3 (do (is (= 25 r)
                                      "after t change — inner re-runs on its own signal; must use v=20")
                                  (done))
                            nil))
                        fail)))))

;; =============================================================================
;; Form 6 — under await-cascade, prove the stale nested spin's BODY re-runs
;; (not merely that the value is wrong) via an execution counter.
;; =============================================================================

(deftest ^:stale-scope-spec form-6-await-cascade-body-not-rerun
  (async done
         (with-ctx [_ctx]
           (let [s (sig/signal 2)
                 runs (atom 0)
                 data (spin (let [{v :new} (track s)] v))
                 parent (spin
                         (let [r (await data)]
                           (let [inner (spin (swap! runs inc) (* 10 r))]
                             (await inner))))
                 stage (atom 0)
                 fail (fn [e] (is false (str "unexpected spin error: " e)) (done))]
             (run-spin! parent
                        (fn [_]
                          (case (swap! stage inc)
                            1 (do (is (= 1 @runs) "inner ran once") (reset! s 3))
                            2 (do (is (= 2 @runs) "inner must re-run with fresh r") (done))
                            nil))
                        fail)))))

;; =============================================================================
;; Form 7 — nested spin under await-cascade that ALSO tracks its own signal.
;; =============================================================================

(deftest ^:stale-scope-spec form-7-await-cascade-reactive-inner
  (async done
         (with-ctx [_ctx]
           (let [s (sig/signal 2)
                 t (sig/signal 1)
                 data (spin (let [{v :new} (track s)] v))
                 parent (spin
                         (let [r (await data)]
                           (let [inner (spin (let [{w :new} (track t)]
                                               (+ (* 10 r) w)))]
                             (await inner))))]
             (check-rerun done parent 21 #(reset! s 3) 31)))))

;; =============================================================================
;; Form 8 — sibling nested spins under an await-cascade resume.
;; =============================================================================

(deftest ^:stale-scope-spec form-8-await-cascade-siblings
  (async done
         (with-ctx [_ctx]
           (let [s (sig/signal 2)
                 data (spin (let [{v :new} (track s)] v))
                 parent (spin
                         (let [r (await data)
                               a (spin (* 10 r))
                               b (spin (* 100 r))]
                           [(await a) (await b)]))]
             (check-rerun done parent [20 200] #(reset! s 3) [30 300])))))
