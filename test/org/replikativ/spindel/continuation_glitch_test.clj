(ns org.replikativ.spindel.continuation-glitch-test
  "Test that topological sorting prevents glitches in continuation resumption.
   Ported from laufzeit, adapted for spindel's execution-context API."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-async :refer [await-drain]]
            [org.replikativ.spindel.test-helpers :as th]))

;; =============================================================================
;; Glitch Prevention Tests
;;
;; These tests verify that spindel's topological ordering ensures consistent
;; updates. A "glitch" occurs when a downstream spin sees inconsistent values
;; from its dependencies (e.g., seeing one dependency updated but not another).
;; =============================================================================

(deftest test-diamond-problem-no-glitch
  (testing "Diamond problem: spins resume in topological order, no glitches"
    (th/with-ctx [ctx]
      (let [;; Root signal
            a (sig/signal 1)

            ;; Two spins that depend on 'a'
            b (spin
               (let [{:keys [new]} (track a)]
                 (* new 2)))  ; b = a * 2

            c (spin
               (let [{:keys [new]} (track a)]
                 (+ new 10)))  ; c = a + 10

            ;; Spin that depends on both b and c
            d (spin
               (let [bv (await b)
                     cv (await c)]
                 (+ bv cv)))]  ; d = b + c

        ;; Initial execution
        (is (= 2 @b) "b should be 1*2 = 2")
        (is (= 11 @c) "c should be 1+10 = 11")
        (is (= 13 @d) "d should be 2+11 = 13")

        ;; Change the root signal
        (swap! a (constantly 5))
        (await-drain ctx)

        ;; After continuation resumption in topological order:
        ;; 1. Spin b resumes: b = 5*2 = 10
        ;; 2. Spin c resumes: c = 5+10 = 15
        ;; 3. Spin d resumes: d = 10+15 = 25

        (is (= 10 @b) "After signal change: b should be 5*2 = 10")
        (is (= 15 @c) "After signal change: c should be 5+10 = 15")
        (is (= 25 @d) "After signal change: d should be 10+15 = 25 (no glitch!)")))))

(deftest test-multiple-signal-changes-no-glitch
  (testing "Multiple signal changes maintain consistency"
    (th/with-ctx [ctx]
      (let [x (sig/signal 1)
            y (sig/signal 2)

            ;; a depends on x
            a (spin
               (let [{:keys [new]} (track x)]
                 (* new 3)))

            ;; b depends on y
            b (spin
               (let [{:keys [new]} (track y)]
                 (+ new 5)))

            ;; c depends on both a and b
            c (spin
               (+ (await a) (await b)))]

        (is (= 3 @a))   ; 1*3 = 3
        (is (= 7 @b))   ; 2+5 = 7
        (is (= 10 @c))  ; 3+7 = 10

        ;; Change x
        (swap! x (constantly 4))
        (await-drain ctx)
        (is (= 12 @a))  ; 4*3 = 12
        (is (= 7 @b))   ; unchanged
        (is (= 19 @c))  ; 12+7 = 19 (no glitch!)

        ;; Change y
        (swap! y (constantly 10))
        (await-drain ctx)
        (is (= 12 @a))  ; unchanged
        (is (= 15 @b))  ; 10+5 = 15
        (is (= 27 @c))  ; 12+15 = 27 (no glitch!)
        ))))

(deftest test-deep-dependency-chain
  (testing "Deep dependency chains maintain topological order"
    (th/with-ctx [ctx]
      (let [s (sig/signal 1)

            ;; Chain: s -> a -> b -> c -> d
            a (spin
               (let [{:keys [new]} (track s)]
                 (inc new)))

            b (spin
               (inc (await a)))

            c (spin
               (inc (await b)))

            d (spin
               (inc (await c)))]

        (is (= 2 @a))  ; s+1 = 2
        (is (= 3 @b))  ; a+1 = 3
        (is (= 4 @c))  ; b+1 = 4
        (is (= 5 @d))  ; c+1 = 5

        ;; Change root signal
        (swap! s (constantly 10))
        (await-drain ctx)

        ;; Should propagate in order: s -> a -> b -> c -> d
        (is (= 11 @a))  ; 10+1 = 11
        (is (= 12 @b))  ; 11+1 = 12
        (is (= 13 @c))  ; 12+1 = 13
        (is (= 14 @d))  ; 13+1 = 14 (no intermediate values seen!)
        ))))

;; =============================================================================
;; Additional Glitch Tests for spindel
;; =============================================================================

(deftest test-wide-fan-out-no-glitch
  (testing "Wide fan-out from single signal maintains consistency"
    (th/with-ctx [ctx]
      (let [;; Single source signal
            source (sig/signal 10)

            ;; Many spins depending on the same signal
            t1 (spin (let [{:keys [new]} (track source)] (* new 1)))
            t2 (spin (let [{:keys [new]} (track source)] (* new 2)))
            t3 (spin (let [{:keys [new]} (track source)] (* new 3)))
            t4 (spin (let [{:keys [new]} (track source)] (* new 4)))

            ;; Aggregator that combines all
            agg (spin
                 (+ (await t1) (await t2) (await t3) (await t4)))]

        ;; Initial: 10*1 + 10*2 + 10*3 + 10*4 = 10 + 20 + 30 + 40 = 100
        (is (= 10 @t1))
        (is (= 20 @t2))
        (is (= 30 @t3))
        (is (= 40 @t4))
        (is (= 100 @agg))

        ;; Update source
        (swap! source (constantly 5))
        (await-drain ctx)

        ;; All should update consistently: 5*1 + 5*2 + 5*3 + 5*4 = 5 + 10 + 15 + 20 = 50
        (is (= 5 @t1))
        (is (= 10 @t2))
        (is (= 15 @t3))
        (is (= 20 @t4))
        (is (= 50 @agg) "Aggregator should see consistent updates (no glitch!")))))

(deftest test-mixed-dependencies-no-glitch
  (testing "Mixed signal and spin dependencies maintain consistency"
    (th/with-ctx [ctx]
      (let [;; Two independent signals
            s1 (sig/signal 2)
            s2 (sig/signal 3)

            ;; Spin depending on s1
            t1 (spin
                (let [{:keys [new]} (track s1)]
                  (* new new)))  ; s1^2

            ;; Spin depending on s2
            t2 (spin
                (let [{:keys [new]} (track s2)]
                  (* new new)))  ; s2^2

            ;; Spin depending on both t1, t2, AND s1 directly
            combined (spin
                      (let [{:keys [new]} (track s1)  ; Direct signal dependency
                            v1 (await t1)              ; Spin dependency
                            v2 (await t2)]             ; Spin dependency
                        (+ new v1 v2)))]  ; s1 + s1^2 + s2^2

        ;; Initial: 2 + 2^2 + 3^2 = 2 + 4 + 9 = 15
        (is (= 4 @t1))
        (is (= 9 @t2))
        (is (= 15 @combined))

        ;; Update s1 only
        (swap! s1 (constantly 5))
        (await-drain ctx)

        ;; Now: 5 + 5^2 + 3^2 = 5 + 25 + 9 = 39
        (is (= 25 @t1))
        (is (= 9 @t2))  ; unchanged
        (is (= 39 @combined) "combined should see consistent s1 and t1 values (no glitch!)")))))

;; =============================================================================
;; Dynamic Dependency Rediscovery — the "Pentagram of Death"
;;
;; Credit: Kenny Tilton (Cells), who named this failure mode and built the
;; original `df-interference` test for it.
;;
;; The topological sort is computed from the dependency graph that exists
;; BEFORE re-execution. But a conditional branch inside a spin body can
;; establish a brand-new dependency edge only AFTER the spin re-runs — an
;; edge the old topo sort never saw and could not have ordered. A scheduler
;; that trusted the topo sort alone would let a spin read a stale cache
;; through that new edge.
;;
;; Spindel is immune because `await` is a demand-driven pull: awaiting a
;; dirty / not-yet-processed child re-executes that child rather than
;; returning its cache (see effects/await.cljc `await-spin`, the
;; `allow-fast-path?` gate). The dependency chain is therefore walked in
;; the true data-flow order of the CURRENT computation, not a precomputed
;; one. These tests pin that behavior so a future scheduler change cannot
;; silently reintroduce the glitch.
;; =============================================================================

(deftest test-pentagram-dynamic-dependency-no-glitch
  (testing "Conditionally-discovered dependency: no stale read through a new edge"
    (th/with-ctx [ctx]
      ;; Kenny Tilton's example:
      ;;   X = 0
      ;;   A = X + B
      ;;   B = if X == 42 then K else 0
      ;;   K = X
      ;;
      ;; At X=0, B takes the `else` branch and NEVER awaits K, so the edge
      ;; B->K does not exist. At X->42, B re-runs, takes the `then` branch,
      ;; and NEWLY awaits K. The topo sort built from the X=0 graph cannot
      ;; know "K before B". If B read K's stale cache (0), A would be 42.
      (let [x (sig/signal 0)
            k (spin (:new (track x)))
            b (spin (if (= 42 (:new (track x)))
                      (await k)
                      0))
            a (spin (+ (:new (track x)) (await b)))]

        ;; X = 0: else branch taken, no B->K edge exists yet
        (is (= 0 @k))
        (is (= 0 @b))
        (is (= 0 @a))

        ;; X -> 42: B re-runs and discovers its dependency on K
        (swap! x (constantly 42))
        (await-drain ctx)

        (is (= 42 @k) "K = X = 42")
        (is (= 42 @b) "B took the then-branch and awaited fresh K")
        (is (= 84 @a) "A = X + B = 42 + 42; would be 42 if B read stale K")))))

(deftest test-newly-discovered-dependency-chain-no-glitch
  (testing "A multi-hop sub-path discovered entirely during re-execution"
    (th/with-ctx [ctx]
      ;;   X = 0
      ;;   O = X            (tracks X)
      ;;   K = 10 * O       (awaits O; does NOT track X)
      ;;   B = if X == 42 then K else 0
      ;;   A = X + B
      ;;
      ;; At X=0, neither K nor O is on B's path, and K is not an observer
      ;; of X at all. At X->42 the whole B->K->O sub-path is discovered
      ;; while B re-executes — each hop resolved by a recursive await-pull.
      (let [x (sig/signal 0)
            o (spin (:new (track x)))
            k (spin (* 10 (await o)))
            b (spin (if (= 42 (:new (track x)))
                      (await k)
                      0))
            a (spin (+ (:new (track x)) (await b)))]

        (is (= 0 @a) "X=0: B short-circuits, K and O never enter the graph")

        (swap! x (constantly 42))
        (await-drain ctx)

        (is (= 42 @o) "O = X = 42")
        (is (= 420 @k) "K = 10 * O")
        (is (= 420 @b) "B awaited the newly-discovered K")
        (is (= 462 @a) "A = X + B = 42 + 420; full B->K->O chain rediscovered")))))

(deftest test-dynamic-dependency-add-and-prune
  (testing "The conditional B->K edge is added and pruned cleanly across toggles"
    (th/with-ctx [ctx]
      ;; Same graph as the Pentagram test, toggled repeatedly. Verifies the
      ;; B->K edge is established when X=42 and pruned when X leaves 42 —
      ;; no stale dependency accumulates, no stale value leaks through.
      (let [x (sig/signal 0)
            k (spin (:new (track x)))
            b (spin (if (= 42 (:new (track x)))
                      (await k)
                      0))
            a (spin (+ (:new (track x)) (await b)))]

        (is (= 0 @a))

        (doseq [[v expected] [[42 84] [0 0] [42 84] [7 7] [42 84] [0 0]]]
          (swap! x (constantly v))
          (await-drain ctx)
          (is (= expected @a)
              (str "X=" v " => A should be " expected
                   " (B->K edge " (if (= v 42) "active" "pruned") ")")))))))
