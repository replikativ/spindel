(ns org.replikativ.spindel.v2.ingress-test
  "Host ingress (H1-H4): concurrent host threads, bounded turns, handoff."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await take!]]
            [org.replikativ.spindel.incremental.interval :as iv]))

(deftest concurrent-writers-converge
  (let [w (v2/world)]
    (binding [v2/*world* w]
      (let [xs (vec (repeatedly 4 #(v2/signal 0)))
            total (spin (loop [i 0 acc 0]
                          (if (< i 4) (recur (inc i) (+ acc (iv/get-new (track (nth xs i))))) acc)))
            last-seen (atom nil)
            _ (v2/observe! total (fn [v _] (reset! last-seen v)))
            threads (mapv (fn [i] (Thread. #(dotimes [n 2000] (v2/write! (nth xs i) (inc n)))))
                          (range 4))]
        (run! #(.start ^Thread %) threads)
        (run! #(.join ^Thread %) threads)
        (is (= 8000 (v2/value total 5000 ::timeout)))
        (Thread/sleep 50)
        (is (= 8000 @last-seen) "the observer saw the final state")))))

(deftest small-budget-hands-off
  (let [w (v2/world {:budget 2})]
    (binding [v2/*world* w]
      (let [x (v2/signal 0)
            chain (reduce (fn [prev _] (spin (inc (await prev)))) (spin (iv/get-new (track x))) (range 30))
            seen (promise)
            _ (v2/observe! chain (fn [v _] (when (= v 31) (deliver seen v))))]
        (v2/write! x 1)
        (is (= 31 (deref seen 5000 ::timeout)) "the drainer finishes what the inline turn left")))))

(deftest not-inline-world
  (let [w (v2/world {:inline? false})]
    (binding [v2/*world* w]
      (let [mb (v2/mailbox)
            t (task (+ (take! mb) (take! mb)))]
        (v2/post! mb 1)
        (v2/post! mb 2)
        (is (= 3 (v2/value t 5000 ::timeout)))))))

(deftest cross-thread-delivery
  (let [w (v2/world)]
    (binding [v2/*world* w]
      (let [d (v2/deferred)
            t (task (* 2 (await d)))]
        (future (Thread/sleep 20) (v2/deliver! d 21))
        (is (= 42 (v2/value t 5000 ::timeout)))))))
