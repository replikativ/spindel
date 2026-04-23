(ns org.replikativ.spindel.track-await-bug-test
  "Regression tests for a track + await continuation-chain bug (now fixed).

  Previously, a parent spin with this shape:
    1. first await → child spin that calls track
    2. second await → child spin that does not call track
  would fail on the second await with 'Invalid arity: 3'.

  Root cause: track-signal did not accept/handle the reject parameter,
  corrupting the continuation chain when the second await resumed.

  These tests guard against regression of that bug."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
            #?(:clj [org.replikativ.spindel.test-async :refer [await-drain]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; Test Spins
;; =============================================================================

(defn spin-with-track
  "Spin that uses track effect (subscribes to signal)."
  [signal]
  (spin
    (let [sig-iv (track signal)]
      ;; Return a simple value
      "spin-with-track-result")))

(defn spin-without-track
  "Spin without any track effect."
  []
  (spin
    "spin-without-track-result"))

;; =============================================================================
;; CLJ Tests
;; =============================================================================

#?(:clj
   (deftest track-await-two-simple-spins-works-clj
     (testing "Two simple spins (no track) should work"
       (with-ctx [ctx]
         (let [simple-parent (spin
                               (let [a (await (spin-without-track))
                                     b (await (spin-without-track))]
                                 [a b]))]
           (is (= ["spin-without-track-result" "spin-without-track-result"]
                  @simple-parent)
               "Two simple awaits should work"))))))

#?(:clj
   (deftest track-await-track-then-simple-fails-clj
     (testing "BUG: track spin + simple spin causes arity error"
       (with-ctx [ctx]
         (let [counter (sig/signal 0)
               ;; This pattern FAILS with "Invalid arity: 3"
               failing-parent (spin
                                (let [a (await (spin-with-track counter))  ; Has track
                                      b (await (spin-without-track))]      ; No track
                                  [a b]))]
           ;; This should work but currently fails
           (is (= ["spin-with-track-result" "spin-without-track-result"]
                  @failing-parent)
               "Track + simple await should work"))))))

#?(:clj
   (deftest track-await-simple-then-track-works-clj
     (testing "Simple spin + track spin should work (opposite order)"
       (with-ctx [ctx]
         (let [counter (sig/signal 0)
               ;; This pattern WORKS (track is second)
               working-parent (spin
                                (let [a (await (spin-without-track))      ; No track
                                      b (await (spin-with-track counter))] ; Has track
                                  [a b]))]
           (is (= ["spin-without-track-result" "spin-with-track-result"]
                  @working-parent)
               "Simple + track await should work"))))))

#?(:clj
   (deftest track-await-track-then-track-works-clj
     (testing "Track spin + track spin should work"
       (with-ctx [ctx]
         (let [counter1 (sig/signal 0)
               counter2 (sig/signal 0)
               ;; This pattern WORKS (both have track)
               working-parent (spin
                                (let [a (await (spin-with-track counter1)) ; Has track
                                      b (await (spin-with-track counter2))] ; Has track
                                  [a b]))]
           (is (= ["spin-with-track-result" "spin-with-track-result"]
                  @working-parent)
               "Track + track await should work"))))))

;; =============================================================================
;; CLJS Tests
;; =============================================================================

#?(:cljs
   (deftest track-await-two-simple-spins-works-cljs
     (testing "Two simple spins (no track) should work"
       (async done
         (with-ctx [ctx]
           (let [simple-parent (spin
                                 (let [a (await (spin-without-track))
                                       b (await (spin-without-track))]
                                   [a b]))]
             (run-spin! simple-parent
                        (fn [result]
                          (is (= ["spin-without-track-result" "spin-without-track-result"]
                                 result)
                              "Two simple awaits should work")
                          (done))
                        (fn [error]
                          (is false (str "Should not error: " error))
                          (done)))))))))

#?(:cljs
   (deftest track-await-track-then-simple-fails-cljs
     (testing "BUG: track spin + simple spin causes arity error"
       (async done
         (with-ctx [ctx]
           (let [counter (sig/signal 0)
                 ;; This pattern FAILS with "Invalid arity: 3"
                 failing-parent (spin
                                  (let [a (await (spin-with-track counter))  ; Has track
                                        b (await (spin-without-track))]      ; No track
                                    [a b]))]
             (run-spin! failing-parent
                        (fn [result]
                          (is (= ["spin-with-track-result" "spin-without-track-result"]
                                 result)
                              "Track + simple await should work")
                          (done))
                        (fn [error]
                          ;; Currently this test will hit the error callback
                          ;; with "Invalid arity: 3"
                          (is false (str "Should not error but got: " error))
                          (done)))))))))

#?(:cljs
   (deftest track-await-simple-then-track-works-cljs
     (testing "Simple spin + track spin should work (opposite order)"
       (async done
         (with-ctx [ctx]
           (let [counter (sig/signal 0)
                 ;; This pattern WORKS (track is second)
                 working-parent (spin
                                  (let [a (await (spin-without-track))      ; No track
                                        b (await (spin-with-track counter))] ; Has track
                                    [a b]))]
             (run-spin! working-parent
                        (fn [result]
                          (is (= ["spin-without-track-result" "spin-with-track-result"]
                                 result)
                              "Simple + track await should work")
                          (done))
                        (fn [error]
                          (is false (str "Should not error: " error))
                          (done)))))))))

#?(:cljs
   (deftest track-await-track-then-track-works-cljs
     (testing "Track spin + track spin should work"
       (async done
         (with-ctx [ctx]
           (let [counter1 (sig/signal 0)
                 counter2 (sig/signal 0)
                 ;; This pattern WORKS (both have track)
                 working-parent (spin
                                  (let [a (await (spin-with-track counter1)) ; Has track
                                        b (await (spin-with-track counter2))] ; Has track
                                    [a b]))]
             (run-spin! working-parent
                        (fn [result]
                          (is (= ["spin-with-track-result" "spin-with-track-result"]
                                 result)
                              "Track + track await should work")
                          (done))
                        (fn [error]
                          (is false (str "Should not error: " error))
                          (done)))))))))
