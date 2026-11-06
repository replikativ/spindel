(ns org.replikativ.spindel.v2.host-delivery-model-test
  "Finite ownership exploration, supplementary to controlled runtime regressions."
  (:require [clojure.test :refer [deftest is]]))

(defn- reachable [step initial]
  (loop [seen #{initial} todo [initial]]
    (if-let [s (peek todo)]
      (let [fresh (remove seen (step s))]
        (recur (into seen fresh) (into (pop todo) fresh))) seen)))

(defn- bridge-step [s]
  (keep identity
        [(when (= :pending (:entry s)) (assoc s :entry :deferred))
         (when (#{:pending :deferred} (:entry s))
           (assoc s :entry :claimed :closure? false))
         (when (#{:pending :deferred} (:entry s))
           (assoc s :entry :rejected :closure? false :after-gate? true))
         (when (and (= :claimed (:entry s)) (nil? (:outcome s)))
           (assoc s :outcome (if (:own-error? s) :own-error :nil-value) :runs 1))
         (when (:after-gate? s)
           (assoc s :after-gate? false :outcome :released))
         (when (= :running (:turn s)) (assoc s :turn :returned))
         (when (= :running (:turn s)) (assoc s :turn :failed))
         (when (and (= :waiting (:wait s)) (not (:interrupted? s)))
           (if (#{:pending :deferred} (:entry s))
             (assoc s :entry :canceled :closure? false :wait :delivered :delivered :interrupt)
             (assoc s :interrupted? true)))
         (when (and (#{:pending :deferred} (:entry s)) (= :failed (:turn s)))
           (assoc s :entry :canceled :closure? false :wait :delivered :delivered :transport-error))
         (when (and (:outcome s) (= :failed (:turn s)) (zero? (:reports s)))
           (assoc s :reports 1))
         (when (and (= :waiting (:wait s)) (:outcome s) (not= :running (:turn s))
                    (or (= :returned (:turn s)) (= 1 (:reports s))))
           (assoc s :wait :delivered :delivered (:outcome s) :restored? (:interrupted? s)))]))

(deftest ordinary-action-rejection-and-cancellation-retain-one-owner
  (doseq [own-error? [false true]]
    (let [states (reachable bridge-step {:entry :pending :closure? true :after-gate? false
                                         :outcome nil :runs 0 :turn :running :wait :waiting
                                         :interrupted? false :restored? false :delivered nil
                                         :reports 0 :own-error? own-error?})]
      (doseq [s states]
        (is (<= (:runs s) 1)) (is (<= (:reports s) 1))
        (when (= :canceled (:entry s))
          (is (not (:closure? s))) (is (nil? (:outcome s))) (is (zero? (:runs s))))
        (when (= :rejected (:entry s))
          (is (zero? (:runs s))) (is (not (:closure? s))))
        (when (#{:nil-value :own-error :released} (:delivered s))
          (is (= (:outcome s) (:delivered s)))
          (is (= (:interrupted? s) (:restored? s)))
          (when (= :failed (:turn s)) (is (= 1 (:reports s)))))
        (doseq [next (bridge-step s)]
          (when (#{:claimed :rejected :canceled} (:entry s))
            (is (= (:entry s) (:entry next))))
          (when (:delivered s) (is (= (:delivered s) (:delivered next)))))
        (when (empty? (bridge-step s)) (is (some? (:delivered s))))))))

(defn- callback-step [s]
  (keep identity
        [(when (and (:gate? s) (seq (:batch s)) (not (:failed? s)))
           (let [head (first (:batch s)) tail (vec (rest (:batch s)))
                 next (-> s (update :seen conj head) (assoc :batch tail))]
             (if (and (= head (:fail-at s)) (not (:thrown? s)))
               (-> next (assoc :queue (into tail [:new]) :batch [] :failed? true :thrown? true))
               next)))
         (when (and (:gate? s) (empty? (:batch s)))
           (assoc s :gate? false :context? false :handoff? true))
         (when (:handoff? s)
           (assoc s :handoff? false :failed? false :scheduled? (boolean (seq (:queue s)))))
         (when (and (:scheduled? s) (not (:gate? s)))
           (assoc s :scheduled? false :gate? true :context? true :batch (:queue s) :queue []))]))

(deftest throwing-callback-is-consumed-suffix-remains-fifo-and-handoff-is-unlocked
  (doseq [fail-at [:a :b :c]]
    (let [states (reachable callback-step {:queue [:a :b :c] :batch [] :seen [] :fail-at fail-at
                                           :gate? false :context? false :failed? false
                                           :thrown? false :handoff? false :scheduled? true})]
      (doseq [s states]
        (is (= (count (:seen s)) (count (distinct (:seen s)))))
        (is (= (:seen s) (subvec [:a :b :c :new] 0 (count (:seen s)))))
        (when (:handoff? s) (is (not (:gate? s))) (is (not (:context? s))))
        (when (empty? (callback-step s))
          (is (= [:a :b :c :new] (:seen s)))
          (is (:thrown? s)))))))
