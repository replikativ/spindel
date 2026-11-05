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
          (when (#{:canceled :refused} (:phase s)) (is (= (:allocated s) (:allocated next))))))
      (doseq [s states :when (empty? (successors s))]
        (is (#{:canceled :refused :committed} (:phase s)))
        (when (= :committed (:phase s))
          (is (:returned? s)) (is (= :dispatched (:outbox s)))
          (is (:callback-threw? s) "callback failure cannot suppress the accepted outbox"))))))

(defn- transport-successors [s]
  (let [js-turn-can-finish? (or (= :jvm (:platform s))
                                (not= :claimed (:entry s)) (not= :absent (:outcome s)))]
    (keep identity
          [(when (and (= :pending (:entry s))
                      (or (= :jvm (:platform s)) (= :running (:transport s))))
             (assoc s :entry :claimed :closure? false))
           (when (and (= :claimed (:entry s)) (= :absent (:outcome s)))
             (assoc s :outcome (if (:fail? s) :own-error :nil-value)
                    :mutations (if (:fail? s) 0 1)))
           (when (and (= :running (:transport s)) js-turn-can-finish?)
             (assoc s :transport :returned))
           (when (and (= :running (:transport s)) js-turn-can-finish?)
             (assoc s :transport :turn-error))
           (when (and (= :pending (:entry s))
                      (or (= :turn-error (:transport s))
                          (and (= :node (:platform s)) (= :returned (:transport s)))))
             (assoc s :entry :canceled :closure? false))
           (when (and (= :canceled (:entry s)) (nil? (:delivered s)))
             (assoc s :delivered (if (= :turn-error (:transport s)) :turn-error :unsupported)))
           (when (and (not= :absent (:outcome s)) (= :turn-error (:transport s)) (zero? (:reports s)))
             (assoc s :reports 1))
           (when (and (not= :absent (:outcome s)) (nil? (:delivered s))
                      (not= :running (:transport s))
                      (or (= :returned (:transport s)) (= 1 (:reports s))))
             (assoc s :delivered (:outcome s)))])))

(deftest synchronous-control-transport-claim-cancel-and-outcome-priority
  (doseq [platform [:jvm :node] fail? [false true]]
    (let [initial {:platform platform :fail? fail? :entry :pending :closure? true
                   :outcome :absent :transport :running :delivered nil :reports 0 :mutations 0}
          states (loop [seen #{initial} todo [initial]]
                   (if-let [s (peek todo)]
                     (let [fresh (remove seen (transport-successors s))]
                       (recur (into seen fresh) (into (pop todo) fresh))) seen))]
      (doseq [s states]
        (is (<= (:reports s) 1))
        (when (= :canceled (:entry s))
          (is (not (:closure? s))) (is (zero? (:mutations s))) (is (= :absent (:outcome s))))
        (when (#{:own-error :nil-value} (:delivered s))
          (is (= (:outcome s) (:delivered s)))
          (is (= :claimed (:entry s)))
          (when (= :turn-error (:transport s)) (is (= 1 (:reports s)))))
        (when (#{:turn-error :unsupported} (:delivered s))
          (is (= :canceled (:entry s))) (is (zero? (:reports s))))
        (doseq [next (transport-successors s)]
          (when (= :canceled (:entry s)) (is (= :canceled (:entry next))))
          (when (:delivered s) (is (= (:delivered s) (:delivered next)))))
        (when (empty? (transport-successors s))
          (is (some? (:delivered s))))))))
