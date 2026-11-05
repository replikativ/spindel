(ns org.replikativ.spindel.v2.world-custody-model-test
  "Bounded protocol exploration, supplementary to actual gated runtime races.
   This is neither the external Z67 model nor an unbounded progress proof."
  (:require [clojure.test :refer [deftest is]]))

(defn- reachable [initial successors]
  (loop [seen #{initial} todo [initial]]
    (if-let [s (peek todo)]
      (let [fresh (remove seen (successors s))]
        (recur (into seen fresh) (into (pop todo) fresh))) seen)))

(defn- publication-successors [s]
  (for [[id {:keys [parent child phase]}] (:producers s)
        :let [next
              (case phase
                :prepared (assoc-in s [:producers id :phase] :checked)
                :checked (if (and (< parent child) (nil? (get-in s [:custody child])))
                           (-> s (assoc-in [:custody child] id)
                               (assoc-in [:producers id :phase] :claimed))
                           (assoc-in s [:producers id :phase] :rejected))
                ;; Bookkeeping is a separate parent-gate step after the
                ;; immutable child-local winner, not an atomic :publish.
                :claimed (-> s (assoc-in [:producers id :phase] :booked)
                             (update :reservations disj id) (update :debts conj id))
                nil)]
        :when next] next))

(deftest creation-ordered-custody-conserves-independent-parent-reservations
  (let [initial {:custody {} :reservations #{:a :b :up :down} :debts #{}
                 :producers {:a {:parent 0 :child 2 :phase :prepared}
                             :b {:parent 1 :child 2 :phase :prepared}
                             :up {:parent 0 :child 1 :phase :prepared}
                             :down {:parent 1 :child 0 :phase :prepared}}}
        states (reachable initial publication-successors)]
    (is (> (count states) 100))
    (doseq [s states]
      (doseq [[id {:keys [parent child phase]}] (:producers s)]
        (is (= (contains? (:reservations s) id) (not= phase :booked)))
        (is (= (contains? (:debts s) id) (= phase :booked)))
        (when (#{:claimed :booked} phase)
          (is (= id (get-in s [:custody child])))
          (is (< parent child)))
        (when (= phase :rejected)
          (is (contains? (:reservations s) id))
          (is (not (contains? (:debts s) id)))))
      (doseq [next (publication-successors s)]
        (doseq [[child owner] (:custody s)] (is (= owner (get-in next [:custody child]))))))
    (doseq [s states :when (empty? (publication-successors s))]
      (is (= :rejected (get-in s [:producers :down :phase])))
      (is (= #{:booked :rejected} (set (map #(get-in s [:producers % :phase]) [:a :b]))))
      ;; A rejected producer needs real reconciliation; fair engine work alone
      ;; cannot certify that an arbitrary acquired native output was disposed.
      (is (seq (:reservations s))))))

(defn- holder-successors [s]
  (keep identity
        [(when-not (:claimed? s) (assoc s :claimed? true :strong? false))
         (when (= :ready (:handoff s)) (assoc s :handoff :promoted :strong? true))
         (when (= :promoted (:handoff s))
           (cond-> (assoc s :handoff :done) (:claimed? s) (assoc :strong? false)))]))

(deftest holder-promotion-is-cleared-after-in-flight-handoff-finishes
  (let [states (reachable {:claimed? false :strong? false :handoff :ready} holder-successors)]
    (is (some #(and (:claimed? %) (:strong? %) (= :promoted (:handoff %))) states)
        "promotion may transiently follow the parent's clear")
    (doseq [s states :when (and (:claimed? s) (= :done (:handoff s)))]
      (is (false? (:strong? s))))
    (doseq [s states :when (empty? (holder-successors s))]
      (is (:claimed? s)) (is (= :done (:handoff s))) (is (false? (:strong? s))))))
