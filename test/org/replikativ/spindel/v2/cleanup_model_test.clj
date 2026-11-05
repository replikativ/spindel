(ns org.replikativ.spindel.v2.cleanup-model-test
  "Finite contract exploration; not the external formal model or CPS proof.
   Two waits in an inner finalizer, one outer finalizer, and one resource ack."
  (:require [clojure.test :refer [deftest is]]))

(defn- initial []
  {:phase :body :remaining 2 :regions [:outer :inner] :active nil :wait nil
   :canceled? false :result nil :resource? true :sequence 0 :exits []})

(defn- step [s event]
  (case event
    :return (when (= :body (:phase s)) (assoc s :phase :cleanup :active :inner))
    :cancel (when (and (not (:canceled? s)) (not= :done (:phase s)))
              (cond-> (assoc s :canceled? true :result :cancelled)
                (= :body (:phase s)) (assoc :phase :cleanup :active :inner)))
    :wait (when (and (= :cleanup (:phase s)) (pos? (:remaining s)))
            (-> s (assoc :phase :waiting
                         :wait {:registered? false :outcome nil :controller :local})
                (update :sequence inc)))
    :registered (when (and (:wait s) (not (get-in s [:wait :registered?])))
                  (assoc-in s [:wait :registered?] true))
    :complete (when (and (:wait s) (nil? (get-in s [:wait :outcome])))
                (assoc-in s [:wait :outcome] :ok))
    :resume (when (and (get-in s [:wait :registered?]) (get-in s [:wait :outcome]))
              (-> s (assoc :phase :cleanup :wait nil) (update :remaining dec)))
    :inner-exit (when (and (= :cleanup (:phase s)) (zero? (:remaining s)))
                  (-> s (assoc :phase :outer :active :outer :regions [:outer])
                      (update :exits conj :inner)))
    :outer-exit (when (= :outer (:phase s))
                  (-> s (assoc :phase :done :active nil :regions []
                               :result (if (:canceled? s) :cancelled :ok))
                      (update :exits conj :outer)))
    :ack (when (:resource? s) (assoc s :resource? false))))

(def ^:private events [:return :cancel :wait :registered :complete :resume :inner-exit :outer-exit :ack])

(defn- successors [s] (set (keep #(step s %) events)))

(defn- reachable []
  (loop [seen #{(initial)} todo [(initial)]]
    (if-let [s (peek todo)]
      (let [fresh (remove seen (successors s))]
        (recur (into seen fresh) (into (pop todo) fresh)))
      seen)))

(defn- retirable? [s]
  (and (= :done (:phase s)) (empty? (:regions s)) (nil? (:active s))
       (nil? (:wait s)) (not (:resource? s))))

(defn- inherited [s]
  (when (:wait s)
    (assoc s :wait {:registered? true :outcome :forked :controller nil})))

(deftest bounded-interleavings-conserve-cleanup-obligations
  (let [states (reachable)]
    (is (> (count states) 50))
    (doseq [s states]
      (is (<= (count (:regions s)) 2))
      (is (= (count (:exits s)) (count (distinct (:exits s)))))
      (when (:wait s)
        (is (= :inner (:active s)))
        (is (not (retirable? s)))
        (when-let [canceled (step s :cancel)]
          (is (= (:wait s) (:wait canceled))))
        (let [child (inherited s) grandchild (inherited child)]
          (is (= :forked (get-in child [:wait :outcome])))
          (is (nil? (get-in child [:wait :controller])))
          (is (= (:wait child) (:wait grandchild)))
          (is (= :local (get-in s [:wait :controller])))))
      (when (:canceled? s) (is (= :cancelled (:result s))))
      (when (empty? (successors s))
        (is (retirable? s))
        (is (= [:inner :outer] (:exits s)))))))
