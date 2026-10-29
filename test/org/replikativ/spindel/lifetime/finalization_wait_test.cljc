(ns org.replikativ.spindel.lifetime.finalization-wait-test
  (:refer-clojure :exclude [deliver])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.cps-cleanup-test :as c]))

(def w c/w)
(def r c/r)
(def n c/n)
(def cell c/cell)
(def wait-action {:t :finalization-wait :w w :th :worker})
(defn deliver [s sequence value]
  (c/checked s {:t :cleanup-deliver :n n :sequence sequence :value value}))
(defn resume-live [s th]
  (c/checked s {:t :finalization-resume :w w :n n :th th}))
(defn waiting [] (c/checked (c/entered) wait-action))

(deftest live-finalization-can-resume-inline-and-wait-again
  (let [s (waiting) ready (deliver s 1 :first)
        resumed (resume-live ready :worker)]
    (is (= :cps-finalization (get-in s [:env :native n :kind])))
    (is (= :running (:status (m/run resumed w r))))
    (is (nil? (get-in resumed [:env :native n])))
    (is (nil? (get-in resumed [:env :threads :worker :cleanup-ticket])))
    ;; A live finalizer has ordinary admission after consuming its wait.
    (let [written (c/checked resumed {:t :signal-write :th :worker :e :cell :value :live})
          next (c/checked written wait-action)]
      (is (= 2 (get-in next [:env :native n :sequence])))
      (is (= next (m/step next {:t :cleanup-deliver :n n :sequence 1 :value :stale})))
      (let [resumed (resume-live (deliver next 2 :second) :worker)
            done (-> resumed (c/checked {:t :t07 :w w :r r :value :done})
                     (c/checked {:t :t38 :th :worker}))]
        (is (m/join-ready? done w r))
        (is (= :done (:result (m/ent done w :spin))))))))

(deftest live-callback-before-return-cannot-dispatch-another-frame
  (let [ready (deliver (waiting) 1 :ready)]
    (c/refused ready {:t :finalization-resume :w w :n n :th :foreign} ::cleanup/slice-busy)
    (let [returned (c/checked ready {:t :t38 :th :worker})
          resumed (resume-live returned :foreign)]
      (is (= r (get-in resumed [:env :threads :foreign :run])))
      (is (nil? (get-in resumed [:env :native n])))
      (is (= 1 (:finalization-sequence (m/run resumed w r)))))))

(deftest cancellation-preserves-the-existing-pending-finalizer
  (let [before (waiting)
        cancelled (c/checked before {:t :t11 :w w :r r})
        again (c/checked cancelled {:t :t11 :w w :r r})]
    (is (= (select-keys (get-in before [:env :native n]) [:owner :phase :sequence :delivery])
           (select-keys (get-in cancelled [:env :native n]) [:owner :phase :sequence :delivery])))
    (is (= (get-in cancelled [:env :native n]) (get-in again [:env :native n])))
    (is (= #{cell} (get-in cancelled [:env :native n :cells])))
    (c/refused cancelled {:t :cleanup-adopt :n n :th :worker} ::cleanup/not-ready)
    (let [ready (-> cancelled (c/checked {:t :t38 :th :worker}) (deliver 1 false))
          claimed (c/checked ready {:t :cleanup-claim :n n :th :foreign})]
      (is (= false (get-in claimed [:env :native n :delivery])))
      (is (false? (m/join-ready? claimed w r)))
      (is (m/join-ready? (c/finish claimed :foreign) w r)))))

(deftest callback-before-cancellation-is-preserved-for-in-place-cleanup
  (let [ready (deliver (waiting) 1 nil)
        cancelled (c/checked ready {:t :t11 :w w :r r})
        claimed (c/checked cancelled {:t :cleanup-adopt :n n :th :worker})]
    (is (contains? (get-in claimed [:env :native n]) :delivery))
    (is (nil? (get-in claimed [:env :native n :delivery])))
    (is (= 1 (get-in claimed [:env :native n :sequence])))
    (is (m/join-ready? (c/finish claimed :worker) w r))))

(deftest consumed-live-callback-cannot-wake-a-new-retirement-wait
  (let [resumed (resume-live (deliver (waiting) 1 :live) :worker)
        cancelled (c/checked resumed {:t :t11 :w w :r r})
        parked (-> cancelled (c/checked {:t :cleanup-adopt :n n :th :worker})
                   (c/checked {:t :cleanup-park :th :worker}))]
    (is (= 2 (get-in parked [:env :native n :sequence])))
    (is (= parked (m/step parked {:t :cleanup-deliver :n n :sequence 1 :value :duplicate-live})))
    (let [s (-> parked (c/checked {:t :t38 :th :worker})
                (deliver 2 :cleanup) (c/checked {:t :cleanup-claim :n n :th :foreign}))]
      (is (= :cleanup (get-in s [:env :native n :delivery])))
      (is (m/join-ready? (c/finish s :foreign) w r)))))

(deftest stale-finalizer-cannot-regain-current-generation-admission
  (let [stale (-> (waiting) (deliver 1 :ready)
                  (c/checked {:t :t09 :w w :e :spin :cause :track :order 1}))]
    (c/refused stale {:t :finalization-resume :w w :n n :th :worker} ::cleanup/not-current-slice)
    (let [retired (c/checked stale {:t :t10 :w w :r r})
          claimed (c/checked retired {:t :cleanup-adopt :n n :th :worker})]
      (is (= [:spin 2] (:owner (m/ent claimed w :cell))))
      (is (empty? (get-in claimed [:env :native n :cells])))
      (is (= :ready (get-in claimed [:env :native n :delivery])))
      (is (m/join-ready? (c/finish claimed :worker) w r)))))

(deftest released-world-keeps-the-same-finalizer-wait
  (let [released (c/checked (waiting) {:t :t34 :w w})
        s (-> released (c/checked {:t :t38 :th :worker}) (deliver 1 :late)
              (c/checked {:t :cleanup-claim :n n :th :foreign}))]
    (is (= :released (get-in s [:worlds w :status])))
    (is (= :original (get-in s [:env :cleanup-cells cell :result])))
    (is (m/join-ready? (c/finish s :foreign) w w))))

(deftest generic-environment-actions-cannot-consume-live-finalization
  (let [s (waiting)]
    (c/refused s {:t :native-progress :n n :state :joined} ::m/protected-cleanup)
    (c/refused s {:t :cleanup-adopt :n n :th :worker} ::cleanup/not-ready)
    (let [returned (c/checked s {:t :t38 :th :worker})]
      (c/refused returned {:t :thread-entry :th :foreign
                           :thread {:world w :run r :executing? true}} ::m/protected-cleanup))))

(deftest independent-oracle-detects-forgotten-and-restarted-waits
  (let [before (c/entered) after (c/checked before wait-action)
        forgotten (-> after (update-in [:env :native] dissoc n)
                      (update-in [:worlds w :runs r] dissoc :finalization-sequence))]
    (is (empty? (cleanup/errors forgotten)))
    (is (some #(= :TL21 (:id %))
              (inv/edge-check {:before before :action wait-action :after forgotten})))
    (let [action {:t :t11 :w w :r r}
          cancelled (c/checked after action)
          restarted (update-in cancelled [:env :native n] assoc :phase :ready :sequence 0)]
      (is (empty? (cleanup/errors restarted)))
      (is (some #(= :TL21 (:id %))
                (inv/edge-check {:before after :action action :after restarted}))))))

(deftest live-resume-needs-the-selected-world
  (let [ready (-> (waiting) (deliver 1 :ready) (c/checked {:t :t38 :th :worker}))]
    (c/refused ready {:t :finalization-resume :w [:w :wrong] :n n :th :foreign} ::cleanup/wrong-world)
    (is (= r (get-in (resume-live ready :foreign) [:env :threads :foreign :run])))))

(deftest independent-resume-oracle-checks-generation-and-physical-admission
  (let [ready (deliver (waiting) 1 :ready)
        stale (c/checked ready {:t :t09 :w w :e :spin :cause :track :order 1})
        occupied (-> ready (c/checked {:t :t04 :w w :e :other :mode :callback})
                     (c/checked {:t :slice-enter :w w :r [:other 1] :th :foreign}))]
    (doseq [[before th] [[stale :worker] [ready :foreign] [occupied :foreign]]]
      (let [action {:t :finalization-resume :w w :n n :th th}
            frame (get-in before [:env :threads th])
            corrupt (-> before (update-in [:env :native] dissoc n)
                        (assoc-in [:worlds w :runs r :status] :running)
                        (assoc-in [:env :threads th]
                                  (merge frame {:world w :scope r :run r :obligation-world w :executing? true})))]
        (is (empty? (cleanup/errors corrupt)))
        (is (some #(= :TL21 (:id %))
                  (inv/edge-check {:before before :action action :after corrupt})))))))

(defn finalization-alphabet [s]
  (concat
   (filter (fn [a]
             (case (:t a)
               :finalization-wait (< (:finalization-sequence (m/run s w r) 0) 2)
               :cleanup-park (< (get-in s [:env :native n :sequence] 0) 2)
               true)) (cleanup/enabled s))
   (for [[th frame] (get-in s [:env :threads]) :when (:run frame)] {:t :t38 :th th})
   (for [sequence [0 1 2]] {:t :cleanup-deliver :n n :sequence sequence :value :arrival})
   (when (= r (m/current s w :spin)) [{:t :t09 :w w :e :spin :cause :track :order 1}])
   [{:t :t07 :w w :r r :value :done}
    {:t :t07 :w w :r [:spin 2] :value :successor}
    {:t :t10 :w w :r r} {:t :t11 :w w :r r} {:t :t34 :w w}]))

(deftest bounded-live-finalization-and-retirement-interleavings
  (let [initial (c/entered)
        report
        (loop [pending [initial] cursor 0 seen #{(dissoc initial :events)} edges 0 covered #{}]
          (cond
            (= cursor (count pending)) {:states (count seen) :edges edges :covered covered :exhausted? true}
            (> (count seen) 5000) {:states (count seen) :exhausted? false}
            :else
            (let [before (nth pending cursor)
                  results (mapv (fn [action]
                                  (let [{after :state :keys [refusal observation]} (m/attempt before action)
                                        errors (concat (inv/check after)
                                                       (inv/edge-check {:before before :action action :after after
                                                                        :refusal refusal :observation observation}))]
                                    {:state after :key (dissoc after :events) :errors (vec errors)
                                     :action action :refusal refusal})) (finalization-alphabet before))]
              (if-let [bad (first (filter #(seq (:errors %)) results))]
                {:failure bad :states (count seen)}
                (let [fresh (vals (into {} (for [result results :when (not (seen (:key result)))]
                                             [(:key result) result])))]
                  (recur (into pending (map :state fresh)) (inc cursor)
                         (into seen (map :key fresh)) (+ edges (count results))
                         (into covered (for [result results :when (not (:refusal result))]
                                         (get-in result [:action :t])))))))))]
    (is (:exhausted? report) (pr-str report))
    (is (nil? (:failure report)) (pr-str report))
    (doseq [t [:finalization-wait :finalization-resume :cleanup-park :cleanup-deliver :cleanup-adopt :t10 :t34]]
      (is (contains? (:covered report) t)))))

(deftest inline-live-resume-uses-the-existing-frame-world
  (let [ready (deliver (waiting) 1 :ready)
        resumed (c/checked ready {:t :finalization-resume :w [:w :wrong] :n n :th :worker})]
    (is (= w (get-in resumed [:env :threads :worker :world])))
    (is (= :running (:status (m/run resumed w r))))))
