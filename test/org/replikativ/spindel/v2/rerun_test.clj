(ns org.replikativ.spindel.v2.rerun-test
  "§4.1: rerun! writes a computation's rerun source; its next run starts
   from the body."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin await track]]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture]]))

(use-fixtures :each checked-fixture)

(deftest an-observed-computation-runs-again-and-its-creditors-see-the-new-result
  (let [ext (atom 1) runs (atom 0)
        c (spin (swap! runs inc) @ext)
        d (spin (* 10 (await c)))
        seen (atom [])
        stop (v2/observe! d (fn [v _] (swap! seen conj v)))]
    (try
      (is (= [10] @seen))
      (reset! ext 2)
      (v2/rerun! c)
      (is (= 2 @runs))
      (is (= [10 20] @seen))
      (finally (stop)))))

(deftest an-unchanged-result-does-not-re-run-creditors
  (let [runs (atom 0) druns (atom 0)
        c (spin (swap! runs inc) :same)
        d (spin (swap! druns inc) (await c))
        stop (v2/observe! d (fn [_ _]))]
    (try
      (v2/rerun! c)
      (is (= 2 @runs))
      (is (= 1 @druns) "the creditor's dep edge was only marked; c's value is unchanged")
      (finally (stop)))))

(deftest a-rerun-restarts-from-the-body-even-with-dependencies
  (let [s (v2/signal 1) before (atom 0)
        c (spin (swap! before inc) (* 2 (:new (track s))))
        stop (v2/observe! c (fn [_ _]))]
    (try
      (swap! s inc)
      (is (= 1 @before) "a signal change re-enters at the track site")
      (v2/rerun! c)
      (is (= 2 @before) "rerun! starts from the body")
      (is (= 4 @c))
      (finally (stop)))))

(deftest an-idle-computation-recomputes-when-next-demanded
  (let [ext (atom :a) runs (atom 0)
        c (spin (swap! runs inc) @ext)]
    (is (= :a @c))
    (reset! ext :b)
    (is (= :a @c) "nothing tells c that ext changed")
    (v2/rerun! c)
    (is (= 1 @runs) "an idle computation does not run on rerun!")
    (is (= :b @c))
    (is (= 2 @runs))))

(deftest rerun-is-for-computations
  (is (thrown? Exception (v2/rerun! (v2/signal 0)))))
