(ns org.replikativ.spindel.v2.port.race-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.port.support2 :as h]))

(use-fixtures :each h/fixture)

(deftest test-race-two-immediate-spins
  (is (#{:first :second} (h/result (comb/race (spin :first) (spin :second))))))

(deftest test-race-three-immediate-spins
  (is (#{:a :b :c} (h/result (comb/race (spin :a) (spin :b) (spin :c))))))

(deftest test-race-deferred-immediate
  (is (= :immediate (h/result (comb/race (v2/deferred) (spin :immediate))))))

(deftest test-await-race-in-spin
  (is (#{20 40} (h/result (spin (* 2 (await (comb/race (spin 10) (spin 20)))))))))

(deftest test-race-result-can-be-processed
  (let [r (h/result (comb/race (spin [:type-a :value-a]) (spin [:type-b :value-b])))]
    (is (vector? r)) (is (#{:type-a :type-b} (first r))) (is (#{:value-a :value-b} (second r)))))

(deftest test-race-two-deferreds-first-wins
  (let [a (v2/deferred) b (v2/deferred) r (comb/race a b)]
    (a :first-wins) (is (= :first-wins (h/result r))) (b :second)
    (is (= :first-wins (h/result r)))))

(deftest test-race-two-deferreds-second-wins
  (let [a (v2/deferred) b (v2/deferred) r (comb/race a b)]
    (b :second-wins) (is (= :second-wins (h/result r)))))

(deftest test-race-with-never-completing-deferred
  (let [a (v2/deferred) b (v2/deferred) r (comb/race a b)]
    (b :winner) (is (= :winner (h/result r)))))

(deftest test-race-yield-vs-termination
  (let [a (v2/deferred) b (v2/deferred) r (comb/race a b)]
    (a [:yield {:value 42}]) (is (= [:yield {:value 42}] (h/result r)))))

(deftest test-race-termination-wins
  (let [a (v2/deferred) b (v2/deferred) r (comb/race a b)]
    (b [:ok nil]) (is (= [:ok nil] (h/result r)))))

(deftest test-race-can-distinguish-results
  (let [a (v2/deferred) b (v2/deferred) r (comb/race a b)]
    (a [:type-a :value-a])
    (let [v (h/result r)]
      (is (vector? v)) (is (= :type-a (first v))) (is (= :value-a (second v))))))

(deftest ready-ties-use-input-order-including-errors
  (let [a (v2/deferred) b (v2/deferred)
        bad (task (throw (ex-info "first error" {:first true})))]
    (a :a) (b :b)
    (is (= :a (h/result (comb/race a b))))
    (is (= :b (h/result (comb/race b a))))
    (is (= :a (h/result (comb/race a bad))))
    (let [[status error] (h/outcome (comb/race bad a))]
      (is (= :err status))
      (is (= {:first true} (ex-data error))))))

(deftest first-error-wins-and-remains-the-result
  (let [trigger (v2/deferred) later (v2/deferred)
        bad (task (await trigger) (throw (ex-info "failed first" {:first true})))
        r (comb/race bad later)]
    (trigger :fail)
    (later :too-late)
    (dotimes [_ 2]
      (let [[status error] (h/outcome r)]
        (is (= :err status))
        (is (= {:first true} (ex-data error)))))))

(deftest race-does-not-cancel-a-shared-task
  (let [winner (v2/deferred) finish (v2/deferred)
        shared (task (await finish))
        observer (task (await shared))
        r (comb/race winner shared)]
    (winner :winner)
    (is (= :winner (h/result r)))
    (finish :shared-result)
    (is (= :shared-result (h/result shared)))
    (is (= :shared-result (h/result observer)))))

(deftest cancelling-a-race-does-not-cancel-shared-input-tasks
  (let [finish (v2/deferred) shared (task (await finish))
        r (comb/race (v2/deferred) shared)]
    (v2/cancel-task! r)
    (let [[status error] (h/outcome r)]
      (is (= :err status))
      (is (v2/cancelled? error)))
    (finish :still-running)
    (is (= :still-running (h/result shared)))))

(deftest race-withdraws-computation-demand-after-resolution
  (let [s (v2/signal 1) runs (atom 0)
        winner (spin (swap! runs inc) (:new (track s)))
        r (comb/race winner (v2/deferred))]
    (is (= 1 (h/result r)))
    (is (= 1 @runs))
    (reset! s 2)
    (is (= 1 @runs) "the completed race retains no demand on its winner")
    (is (= 1 (h/result r)))))

(deftest a-losing-computation-retains-demand-from-another-observer
  (let [finish (v2/deferred) winner (v2/deferred)
        shared (spin (await finish))
        seen (atom []) stop (v2/observe! shared #(swap! seen conj [%1 %2]))]
    (try
      (let [r (comb/race winner shared)]
        (winner :winner)
        (is (= :winner (h/result r)))
        (finish :shared-result)
        (is (= :shared-result (h/result shared)))
        (is (= [[:shared-result false]] @seen)))
      (finally (stop)))))

(deftest owned-task-children-cancel-on-their-owners-completion
  (let [finish (v2/deferred) winner (v2/deferred) child (atom nil)
        owner (task (let [loser (task (await finish))]
                      (reset! child loser)
                      (await (comb/race winner loser))))]
    (winner :winner)
    (is (= :winner (h/result owner)))
    (let [[status error] (h/outcome @child)]
      (is (= :err status))
      (is (v2/cancelled? error)))))

(deftest timeout-is-one-shot-and-preserves-shared-tasks
  (let [s (v2/signal :initial)
        c (spin (:new (track s)))
        keep-c (v2/observe! c (fn [_ _]))]
    (try
      (let [t (comb/timeout c 1000 :fallback)]
        (is (= :initial (h/result t)))
        (reset! s :changed)
        (is (= :changed (h/result c)))
        (is (= :initial (h/result t))))
      (finally (keep-c))))
  (let [finish (v2/deferred) shared (task (await finish))
        t (comb/timeout shared 1 :fallback)]
    (is (= :fallback (h/result t)))
    (finish :finished)
    (is (= :finished (h/result shared)))
    (is (= :fallback (h/result t)))))

(deftest timeout-releases-its-timer-and-wait-edges-when-input-wins
  (let [w v2/*world*
        census (fn []
                 (v2/call-in! w
                              #(frequencies (map (fn [r] (aget ^objects r rw/TYPE))
                                                 (vals (aget ^objects w rw/W-REG))))))
        finish (v2/deferred)
        t (comb/timeout finish 60000 :fallback)]
    (is (= 1 (get (census) rw/T-RES 0)) "the timeout timer is armed")
    (finish :in-time)
    (is (= :in-time (h/result t)))
    (is (= 0 (get (census) rw/T-RES 0)))
    (is (= 0 (get (census) rw/T-EDGE 0)))
    (is (= 0 (get (census) rw/T-RUN 0)))))
