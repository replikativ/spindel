(ns org.replikativ.spindel.v2.port.cancel-arbitration-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.combinators :as comb :refer [parallel]]
            [org.replikativ.spindel.v2.port.support :refer
             [checking vworld with-world outcome check-result observed-value wait-until required-api]]))

(use-fixtures :each checking)

;; Cancellation targets tasks in v2. A task awaiting a computation owns the
;; operation; cancelling it withdraws that computation's demand.
(defn- record! [h calls]
  (v2/value-async h
                  (fn [v err?]
                    (swap! calls conj (if err? [:rejected (v2/cancelled? v)] [:resolved v])))))

(deftest a-child-completing-inline-after-its-parent-was-cancelled-does-not-resume-it-again
  (with-world [w]
    (let [start (v2/deferred)
          parent-ref (atom nil)
          finals (atom 0)
          calls (atom [])
          child (spin (v2/cancel-task! (swap! parent-ref identity)) :v)
          parent (task (await start)
                       (try (await child) (finally (swap! finals inc))))]
      (reset! parent-ref parent)
      (record! parent calls)
      (v2/deliver! start :go)
      (is (= [[:rejected true]] @calls))
      (is (= 1 @finals))
      (v2/cancel-task! parent)
      (is (= [[:rejected true]] @calls)))))

(deftest a-cancelled-parent-that-already-moved-past-a-child-await-is-rejected-once
  (with-world [w]
    (let [d (v2/deferred) child (spin :a)
          finals (atom 0) calls (atom [])
          parent (task (try (await child) (await d)
                            (finally (swap! finals inc))))]
      (record! parent calls)
      (is (= [] @calls))
      (v2/cancel-task! parent)
      (is (= [[:rejected true]] @calls))
      (is (= 1 @finals))
      (v2/deliver! d :late)
      (is (= [[:rejected true]] @calls))
      (is (= 1 @finals)))))

(deftest cancelling-a-completed-parent-does-not-re-run-its-reject-path
  (with-world [w]
    (let [child (spin :a) finals (atom 0) calls (atom [])
          parent (task (try (await child) (finally (swap! finals inc))))]
      (record! parent calls)
      (is (= [[:resolved :a]] @calls))
      (v2/cancel-task! parent)
      (is (= [[:resolved :a]] @calls))
      (is (= 1 @finals)))))

(deftest cancelling-an-in-flight-race-rejects-it
  (with-world [w]
    (let [d1 (v2/deferred) d2 (v2/deferred)
          finals (atom []) calls (atom [])
          a (spin (try (await d1) (finally (swap! finals conj :a))))
          b (spin (try (await d2) (finally (swap! finals conj :b))))
          r (comb/race a b)
          owner (task (await r))]
      (record! owner calls)
      (is (= [] @calls))
      (v2/cancel-task! owner)
      (is (= [[:rejected true]] @calls))
      (is (= {:a 1 :b 1} (frequencies @finals)))
      (v2/cancel-task! owner)
      (is (= [[:rejected true]] @calls)))))

(deftest a-late-delivery-does-not-settle-a-cancelled-race
  (with-world [w]
    (let [d1 (v2/deferred) d2 (v2/deferred)
          finals (atom 0) calls (atom [])
          a (spin (try (await d1) (finally (swap! finals inc))))
          b (spin (try (await d2) (finally (swap! finals inc))))
          r (comb/race a b)
          owner (task (await r))]
      (record! owner calls)
      (v2/cancel-task! owner)
      (v2/deliver! d1 :late)
      (v2/deliver! d2 :also-late)
      (is (= [[:rejected true]] @calls))
      (is (= 2 @finals)))))

(deftest a-race-settles-once-when-cancelled-while-its-winner-completes
  (with-world [w]
    (let [start (v2/deferred) d (v2/deferred)
          owner-ref (atom nil) calls (atom [])
          a (spin (v2/cancel-task! (swap! owner-ref identity)) :a)
          b (spin (await d))
          r (comb/race a b)
          owner (task (await start) (await r))]
      (reset! owner-ref owner)
      (record! owner calls)
      (v2/deliver! start :go)
      (is (= [[:rejected true]] @calls))
      (v2/deliver! d :late)
      (is (= [[:rejected true]] @calls)))))
