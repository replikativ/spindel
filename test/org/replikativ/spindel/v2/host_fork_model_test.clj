(ns org.replikativ.spindel.v2.host-fork-model-test
  "Bounded operational bridge model, not the external engine proof."
  (:require [clojure.test :refer [deftest is]]))

(defn- successors [s]
  (keep identity
        [(when (= :new (:phase s))
           (assoc s :phase (if (:valid? s) :queued :refused)))
         (when (= :queued (:phase s)) (assoc s :phase :claimed :gate? true))
         (when (and (= :node (:platform s)) (= :queued (:phase s)))
           (assoc s :phase :canceled :closure? false))
         (when (and (not (:gate? s)) (not (:closed? s))) (assoc s :closed? true))
         (when (= :claimed (:phase s))
           (if (or (:closed? s) (:unborn? s))
             (assoc s :phase :refused :closure? false)
             (assoc s :phase :committed :allocated 1 :owned? true :outbox :pending :closure? false)))
         (when (and (:gate? s) (#{:committed :refused} (:phase s))) (assoc s :gate? false))
         (when (and (= :committed (:phase s)) (not (:returned? s))) (assoc s :returned? true))
         (when (and (= :committed (:phase s)) (not (:callback-threw? s))) (assoc s :callback-threw? true))
         (when (and (= :pending (:outbox s)) (not (:gate? s))) (assoc s :outbox :dispatched))]))

(defn- reachable [initial]
  (loop [seen #{initial} todo [initial]]
    (if-let [s (peek todo)]
      (let [fresh (remove seen (successors s))]
        (recur (into seen fresh) (into (pop todo) fresh))) seen)))

(deftest canceled-or-refused-host-control-cannot-later-allocate
  (doseq [platform [:jvm :node] valid? [false true] unborn? [false true]]
    (let [states (reachable {:platform platform :valid? valid? :unborn? unborn?
                             :phase :new :gate? false :closed? false :closure? true
                             :allocated 0 :owned? false :returned? false
                             :callback-threw? false :outbox :none})]
      (doseq [s states]
        (is (<= (:allocated s) 1))
        (when (#{:canceled :refused} (:phase s)) (is (zero? (:allocated s))))
        (when (pos? (:allocated s)) (is (:owned? s)) (is (:valid? s)) (is (not (:unborn? s))))
        (when (:returned? s) (is (= :committed (:phase s))) (is (:owned? s)))
        (when (= :dispatched (:outbox s)) (is (not (:gate? s))))
        (doseq [next (successors s)]
          (when (#{:canceled :refused} (:phase s)) (is (= (:allocated s) (:allocated next)))))
      (doseq [s states :when (empty? (successors s))]
        (is (#{:canceled :refused :committed} (:phase s)))
        (when (= :committed (:phase s))
          (is (:returned? s)) (is (= :dispatched (:outbox s)))
          (is (:callback-threw? s) "callback failure cannot suppress the accepted outbox"))))))
