(ns org.replikativ.spindel.spin.race-test
  "Tests for race combinator with deferreds"
  (:refer-clojure :exclude [await])
  #?(:clj
     (:require [clojure.test :refer [deftest is testing use-fixtures]]
               [org.replikativ.spindel.runtime.core :as rtc]
               [org.replikativ.spindel.runtime.context :as ctx]
               [org.replikativ.spindel.runtime.scheduler :as sched]
               [org.replikativ.spindel.spin.sync :as sync]
               [org.replikativ.spindel.spin.combinators :refer [race]]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.effects.await :refer [await]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]]
               [org.replikativ.spindel.runtime.core :as rtc]
               [org.replikativ.spindel.runtime.context :as ctx]
               [org.replikativ.spindel.spin.sync :as sync]
               [org.replikativ.spindel.spin.combinators :refer [race]]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.effects.await :refer [await]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; CLJ-only fixture
#?(:clj
   (use-fixtures :each
     (fn [f]
       (let [execution-ctx (ctx/create-execution-context {:executor (sched/thread-pool-executor 4)})]
         (binding [rtc/*execution-context* execution-ctx]
           (f))))))

;; =============================================================================
;; Cross-platform basic race tests (async pattern)
;; =============================================================================

(deftest test-race-two-immediate-spins
  (testing "Race between two immediate spins - returns one of them"
    (async done
      (with-ctx [_ctx]
        (let [t1 (spin :first)
              t2 (spin :second)
              race-spin (race t1 t2)]
          (run-spin! race-spin
                     (fn [result]
                       (is (#{:first :second} result) "Result should be one of the spin values")
                       (done))
                     (fn [err]
                       (is false (str "Race failed: " err))
                       (done))))))))

(deftest test-race-three-immediate-spins
  (testing "Race between three immediate spins - returns one of them"
    (async done
      (with-ctx [_ctx]
        (let [t1 (spin :a)
              t2 (spin :b)
              t3 (spin :c)
              race-spin (race t1 t2 t3)]
          (run-spin! race-spin
                     (fn [result]
                       (is (#{:a :b :c} result) "Result should be one of the spin values")
                       (done))
                     (fn [err]
                       (is false (str "Race failed: " err))
                       (done))))))))

(deftest test-race-deferred-immediate
  (testing "Race between deferred and immediate - immediate wins"
    (async done
      (with-ctx [_ctx]
        (let [d (sync/deferred)
              immediate (spin :immediate)
              race-spin (race d immediate)]
          (run-spin! race-spin
                     (fn [result]
                       (is (= :immediate result) "Immediate spin should win race")
                       (done))
                     (fn [err]
                       (is false (str "Race failed: " err))
                       (done))))))))

(deftest test-await-race-in-spin
  (testing "Await race inside a spin"
    (async done
      (with-ctx [_ctx]
        (let [outer-spin (spin
                           (let [t1 (spin 10)
                                 t2 (spin 20)
                                 winner (await (race t1 t2))]
                             (* winner 2)))]
          (run-spin! outer-spin
                     (fn [result]
                       ;; Race can return either 10 or 20, so result is 20 or 40
                       (is (#{20 40} result) "Should await race result and double it")
                       (done))
                     (fn [err]
                       (is false (str "Spin failed: " err))
                       (done))))))))

(deftest test-race-result-can-be-processed
  (testing "Race result can be pattern matched"
    (async done
      (with-ctx [_ctx]
        (let [t1 (spin [:type-a :value-a])
              t2 (spin [:type-b :value-b])
              race-spin (race t1 t2)]
          (run-spin! race-spin
                     (fn [result]
                       (is (vector? result) "Result should be vector")
                       ;; Race can return either spin's result
                       (is (#{:type-a :type-b} (first result)) "Can distinguish by type tag")
                       (is (#{:value-a :value-b} (second result)) "Can extract value")
                       (done))
                     (fn [err]
                       (is false (str "Race failed: " err))
                       (done))))))))

;; =============================================================================
;; CLJ-only tests: require blocking deref, Thread/sleep, thread-pool-executor
;; =============================================================================

#?(:clj
   (deftest test-race-two-deferreds-first-wins
     (testing "Race between two deferreds - first to complete wins"
       (let [d1 (sync/deferred)
             d2 (sync/deferred)
             race-spin (race d1 d2)]

         ;; Deliver to d1 first
         (d1 :first-wins)

         ;; Race should complete with first value
         (is (= :first-wins @race-spin) "First deferred should win")

         ;; Delivering to d2 now should have no effect on race result
         (d2 :second)))))

#?(:clj
   (deftest test-race-two-deferreds-second-wins
     (testing "Race between two deferreds - second delivered wins if first"
       (let [d1 (sync/deferred)
             d2 (sync/deferred)
             race-spin (race d1 d2)]

         ;; Deliver to d2 first
         (d2 :second-wins)

         ;; Race should complete with second value
         (is (= :second-wins @race-spin) "Second deferred should win")))))

#?(:clj
   (deftest test-race-with-never-completing-deferred
     (testing "Race with one deferred that never completes"
       (let [never-d (sync/deferred)  ; Never delivered to
             winner-d (sync/deferred)
             race-spin (race never-d winner-d)]

         ;; Deliver only to winner
         (winner-d :winner)

         ;; Should complete despite never-d never completing
         (is (= :winner @race-spin) "Should complete with winning deferred")))))

#?(:clj
   (deftest test-race-yield-vs-termination
     (testing "Race between yield deferred and termination deferred - yield wins"
       (let [yield-d (sync/deferred)
             term-d (sync/deferred)
             race-spin (race yield-d term-d)]

         ;; Deliver yield marker
         (yield-d [:yield {:value 42}])

         ;; Race should complete with yield
         (is (= [:yield {:value 42}] @race-spin) "Yield deferred should win")))))

#?(:clj
   (deftest test-race-termination-wins
     (testing "Race between yield deferred and termination deferred - termination wins"
       (let [yield-d (sync/deferred)
             term-d (sync/deferred)
             race-spin (race yield-d term-d)]

         ;; Deliver termination
         (term-d [:ok nil])

         ;; Race should complete with termination
         (is (= [:ok nil] @race-spin) "Termination deferred should win")))))

#?(:clj
   (deftest test-race-can-distinguish-results
     (testing "Race result can be pattern matched to determine which won"
       (let [d1 (sync/deferred)
             d2 (sync/deferred)
             race-spin (race d1 d2)]

         ;; Deliver to d1 with distinct marker
         (d1 [:type-a :value-a])

         (let [result @race-spin]
           (is (vector? result) "Result should be vector")
           (is (= :type-a (first result)) "Can distinguish by type tag")
           (is (= :value-a (second result)) "Can extract value"))))))
