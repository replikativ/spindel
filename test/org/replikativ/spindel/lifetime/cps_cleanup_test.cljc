(ns org.replikativ.spindel.lifetime.cps-cleanup-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]
            [org.replikativ.spindel.lifetime.invariants :as inv]))

(def w [:w 0])
(def r [:spin 1])
(def n (cleanup/ticket w r))
(def cell [w r :cell])

(defn checked [s action]
  (let [{after :state :keys [refusal observation]} (m/attempt s action)]
    (is (nil? refusal) (pr-str [action refusal]))
    (is (empty? (inv/check after)) (pr-str (inv/check after)))
    (is (empty? (inv/edge-check {:before s :action action :after after
                                 :refusal refusal :observation observation})))
    after))

(defn refused [s action error]
  (let [result (m/attempt s action)]
    (is (= error (get-in result [:refusal :error])) (pr-str result))
    (is (= s (:state result)))))

(defn entered []
  (reduce checked (m/init-state {:slices? true :cps-exit? true})
          [{:t :t04 :w w :e :spin :mode :callback}
           {:t :slice-enter :w w :r r :th :worker}
           {:t :t02 :w w :scope r :e :cell :kind :atom :value :original}]))

(defn cancelled []
  (reduce checked (entered) [{:t :t11 :w w :r r} {:t :t38 :th :worker}]))

(defn finish [s th]
  (-> s (checked {:t :cleanup-return :th th}) (checked {:t :t38 :th th})))

(deftest cancellation-reserves-exit-before-the-active-slice-returns
  (let [s (checked (entered) {:t :t11 :w w :r r})]
    (is (= :unwinding (:status (m/run s w r))))
    (is (= :ready (get-in s [:env :native n :phase])))
    (is (false? (m/join-ready? s w r)))
    (refused s {:t :cleanup-claim :n n :th :foreign} ::cleanup/slice-busy)
    (let [s (-> s (checked {:t :t38 :th :worker})
                (checked {:t :cleanup-claim :n n :th :foreign}))]
      (is (false? (m/join-ready? s w r)))
      (is (= :original (get-in s [:env :cleanup-cells cell :result])))
      (refused s {:t :signal-write :th :foreign :e :cell :value :illegal} ::m/cleanup-only)
      (refused s {:t :t04 :th :foreign :e :new-work} ::m/cancelled)
      (refused s {:t :cleanup-cell :th :foreign :cell [w r :missing] :value 1}
               ::cleanup/missing-cleanup-cell)
      (let [s (checked s {:t :cleanup-cell :th :foreign :cell cell :value :cleaned})
            returning (checked s {:t :cleanup-return :th :foreign})
            done (checked returning {:t :t38 :th :foreign})]
        (is (= :cleaned (get-in returning [:env :cleanup-cells cell :result])))
        (is (false? (m/join-ready? returning w r)))
        (is (m/join-ready? done w r))
        (is (empty? (get-in done [:env :cleanup-cells])))
        (is (nil? (get-in done [:env :native n])))
        (is (nil? (m/run done w r)))))))

(deftest asynchronous-cleanup-delivery-is-one-shot-and-waits-for-physical-handoff
  (let [s (-> (cancelled) (checked {:t :cleanup-claim :n n :th :worker})
              (checked {:t :cleanup-park :th :worker}))
        sequence (get-in s [:env :native n :sequence])
        callback {:t :cleanup-deliver :n n :sequence sequence :value :arrived}
        ready (checked s callback)]
    (is (= :ready (get-in ready [:env :native n :phase])))
    (is (= (dissoc ready :events) (dissoc (checked ready callback) :events)))
    (refused ready {:t :cleanup-claim :n n :th :foreign} ::cleanup/slice-busy)
    (refused ready {:t :native-progress :n n :state :joined} ::m/protected-cleanup)
    (let [s (-> ready (checked {:t :t38 :th :worker})
                (checked {:t :t11 :w w :r r})
                (checked {:t :cleanup-claim :n n :th :foreign})
                (checked {:t :cleanup-park :th :foreign})
                (checked {:t :t38 :th :foreign}))
          old (checked s callback)]
      (is (= :waiting (get-in old [:env :native n :phase])))
      (is (= (dissoc s :events) (dissoc old :events)))
      (let [s (-> old (checked (assoc callback :sequence (inc sequence)))
                  (checked {:t :cleanup-claim :n n :th :worker})
                  (finish :worker))]
        (is (m/join-ready? s w w))
        (is (= (dissoc s :events) (dissoc (checked s callback) :events)))))))

(deftest never-started-and-completed-bodies-create-no-cleanup-work
  (doseq [complete? [false true]]
    (let [s (if complete? (-> (entered) (checked {:t :t07 :w w :r r :value :done})
                              (checked {:t :t38 :th :worker}))
                (checked (m/init-state {:slices? true :cps-exit? true})
                         {:t :t04 :w w :e :spin :mode :callback}))
          s (checked s {:t :t34 :w w})]
      (is (not-any? cleanup/protected? (vals (get-in s [:env :native]))))
      (is (empty? (get-in s [:env :cleanup-cells])))
      (is (m/join-ready? s w w)))))

(deftest released-world-keeps-private-cleanup-state-until-physical-exit
  (let [s (-> (entered)
              (checked {:t :t02 :w w :e :root-cell :kind :atom :value :root})
              (checked {:t :t34 :w w})
              (checked {:t :t38 :th :worker}))
        s (checked s {:t :cleanup-claim :n n :th :worker})]
    (is (= #{:id :lineage :status} (set (keys (m/wr s w)))))
    (is (contains? (get-in s [:env :native n :cells]) [w [:root w] :root-cell]))
    (let [s (-> s (checked {:t :cleanup-cell :th :worker :cell cell :value :after-release})
                (checked {:t :cleanup-park :th :worker})
                (checked {:t :t38 :th :worker})
                (checked {:t :cleanup-deliver :n n :sequence 1 :value :done})
                (checked {:t :cleanup-claim :n n :th :foreign})
                (finish :foreign))]
      (is (m/join-ready? s w w))
      (is (empty? (get-in s [:env :cleanup-cells]))))))

(deftest overlapping-parent-and-child-retirement-share-cells-in-either-order
  (doseq [child-first? [false true]]
    (let [child [:child 1] child-n (cleanup/ticket w child) child-cell [w child :child-cell]
          s (-> (entered)
                (checked {:t :t04 :w w :e :child :scope r :mode :callback})
                (checked {:t :slice-enter :w w :r child :th :child-worker})
                (checked {:t :t02 :w w :scope child :e :child-cell :kind :atom :value :child})
                (checked {:t :t38 :th :worker})
                (checked {:t :t38 :th :child-worker}))
          s (if child-first? (checked s {:t :t11 :w w :r child}) s)
          s (checked s {:t :t11 :w w :r r})]
      (doseq [key [cell child-cell]]
        (is (= #{n child-n} (get-in s [:env :cleanup-cells key :holders])))
        (is (every? #(contains? (get-in s [:env :native % :cells]) key) [n child-n])))
      (let [s (-> s (checked {:t :cleanup-claim :n child-n :th :worker})
                  (checked {:t :cleanup-cell :th :worker :cell cell :value :from-child})
                  (finish :worker)
                  (checked {:t :cleanup-claim :n n :th :worker}))]
        (is (= :from-child (get-in s [:env :cleanup-cells cell :result])))
        (is (= :child (get-in s [:env :cleanup-cells child-cell :result])))
        (is (empty? (get-in (finish s :worker) [:env :cleanup-cells])))))))

(deftest static-conservation-rejects-orphans-and-missing-physical-claims
  (let [s (cancelled)]
    (is (some #(= :L27 (:id %)) (inv/check (update-in s [:env :native n] dissoc :cells))))
    (is (some #(= :L27 (:id %)) (inv/check (assoc-in s [:env :native n :phase] :claimed))))
    (is (not-any? #(= :native-progress (:t %))
                  (filter #(= n (:n %)) (m/raw-enabled s))))
    (is (some #(= :cleanup-claim (:t %)) (m/raw-enabled s)))))

(deftest generic-entry-cannot-create-a-cleanup-frame
  (let [s (-> (cancelled) (checked {:t :cleanup-claim :n n :th :worker})
              (checked {:t :cleanup-return :th :worker}))]
    (refused s {:t :thread-entry :th :foreign
                :thread {:world w :run r :cleanup-ticket n}}
             ::m/protected-cleanup)
    (is (false? (m/join-ready? s w w)))
    (is (m/join-ready? (checked s {:t :t38 :th :worker}) w w))))

(deftest adopted-state-does-not-belong-to-the-retiring-generation
  (let [successor [:spin 2]
        s (-> (entered)
              (checked {:t :t09 :w w :e :spin :cause :track :order 1})
              (checked {:t :t10 :w w :r r})
              (checked {:t :t38 :th :worker})
              (checked {:t :cleanup-claim :n n :th :worker}))]
    (is (= successor (:owner (m/ent s w :cell))))
    (is (empty? (get-in s [:env :native n :cells])))
    (refused s {:t :cleanup-cell :th :worker :cell cell :value :stale-write}
             ::cleanup/missing-cleanup-cell)
    (is (= :original (:result (m/ent (finish s :worker) w :cell))))))

(deftest independent-retention-oracle-rejects-a-consistently-forgotten-cell
  (let [before (entered) action {:t :t11 :w w :r r}
        correct (m/step before action)
        corrupt (-> correct (update-in [:env :cleanup-cells] dissoc cell)
                    (update-in [:env :native n :cells] disj cell))]
    ;; Both ends were erased, so a local holder-count check sees nothing wrong.
    ;; The edge oracle reconstructs the required cell from pre-retirement ownership.
    (is (empty? (inv/check corrupt)))
    (is (some #(= :TL21 (:id %))
              (inv/edge-check {:before before :action action :after corrupt})))
    (let [s (-> correct (checked {:t :t38 :th :worker})
                (checked {:t :cleanup-claim :n n :th :worker})
                (checked {:t :cleanup-return :th :worker}))
          corrupt (-> s (update-in [:env :native] dissoc n)
                      (update-in [:env :cleanup-cells] dissoc cell))]
      (is (seq (inv/cleanup-edge-errors
                {:before s :action {:t :native-progress :n n :state :joined} :after corrupt}))))))

(deftest original-retired-slice-has-no-ordinary-source-authority
  (let [before (checked (entered) {:t :t02 :w w :e :root-cell :kind :atom :value :root})
        s (checked before {:t :t11 :w w :r r})]
    (refused s {:t :signal-write :th :worker :e :root-cell :value :illegal} ::m/cleanup-only)
    (is (= :root (:result (m/ent s w :root-cell))))))

(deftest indirect-world-cancellation-also-requires-retirement-evidence
  (let [before (entered) action {:t :t15 :w w} correct (checked before action)
        corrupt (-> correct (update-in [:env :native] dissoc n)
                    (assoc-in [:env :cleanup-cells] {}))]
    (is (empty? (inv/check corrupt)))
    (is (some #(= :TL21 (:id %))
              (inv/edge-check {:before before :action action :after corrupt})))))

(defn handoff-alphabet [s]
  (concat
   (filter #(or (not= :cleanup-park (:t %))
                (< (get-in s [:env :native n :sequence] 0) 2)) (cleanup/enabled s))
   (for [[th row] (get-in s [:env :threads]) :when (:run row)] {:t :t38 :th th})
   (for [sequence [0 1 2]] {:t :cleanup-deliver :n n :sequence sequence :value :arrival})
   [{:t :t11 :w w :r r} {:t :t34 :w w}
    {:t :native-progress :n n :state :joined}]))

(deftest bounded-cleanup-handoff-exploration
  (let [initial (checked (entered) {:t :t11 :w w :r r})
        result
        (loop [pending [initial] cursor 0 seen #{(dissoc initial :events)} edges 0 covered #{}]
          (cond
            (= cursor (count pending)) {:states (count seen) :edges edges :covered covered :exhausted? true}
            (> (count seen) 3000) {:states (count seen) :exhausted? false}
            :else
            (let [s (nth pending cursor)
                  results (mapv (fn [action]
                                  (let [{after :state :keys [refusal observation]} (m/attempt s action)
                                        bad (concat (inv/check after)
                                                    (inv/edge-check {:before s :action action :after after
                                                                     :refusal refusal :observation observation}))]
                                    {:state after :key (dissoc after :events) :bad (vec bad)
                                     :action action :refusal refusal})) (handoff-alphabet s))]
              (if-let [bad (first (filter #(seq (:bad %)) results))]
                {:failure bad :states (count seen)}
                (let [fresh (vals (into {} (for [result results :when (not (seen (:key result)))]
                                             [(:key result) result])))]
                  (recur (into pending (map :state fresh)) (inc cursor)
                         (into seen (map :key fresh)) (+ edges (count results))
                         (into covered (for [result results :when (not (:refusal result))]
                                         (get-in result [:action :t])))))))))]
    (is (:exhausted? result) (pr-str result))
    (is (> (:states result 0) 100) (pr-str result))
    (is (every? (:covered result #{})
                [:cleanup-claim :cleanup-park :cleanup-deliver :cleanup-return :t38 :t34])
        (pr-str result))))

(deftest running-cancellation-adopts-the-existing-physical-frame
  (let [before (checked (entered) {:t :t11 :w w :r r})
        wrong (assoc-in before [:env :threads :foreign]
                        {:world w :run [:other 1] :scope [:other 1] :executing? true})]
    (refused before {:t :cleanup-adopt :n n :th :foreign} ::cleanup/wrong-slice)
    (refused wrong {:t :cleanup-adopt :n n :th :foreign} ::cleanup/wrong-slice)
    (is (some #{{:t :cleanup-adopt :n n :th :worker}} (cleanup/enabled before)))
    (let [claimed (checked before {:t :cleanup-adopt :n n :th :worker})]
      (is (= (set (keys (get-in before [:env :threads])))
             (set (keys (get-in claimed [:env :threads])))))
      (is (= r (get-in claimed [:env :threads :worker :run])))
      (is (= :claimed (get-in claimed [:env :native n :phase])))
      (is (false? (m/join-ready? claimed w r)))
      (refused claimed {:t :cleanup-adopt :n n :th :worker} ::cleanup/not-ready)
      (refused claimed {:t :cleanup-claim :n n :th :foreign} ::cleanup/not-ready)
      (let [written (checked claimed {:t :cleanup-cell :th :worker :cell cell :value :in-place})
            returning (checked written {:t :cleanup-return :th :worker})
            done (checked returning {:t :t38 :th :worker})]
        (is (= :in-place (get-in returning [:env :cleanup-cells cell :result])))
        (is (false? (m/join-ready? returning w r)))
        (is (m/join-ready? done w r))
        (is (empty? (get-in done [:env :cleanup-cells])))))))

(deftest adopted-frame-parks-without-concurrent-resumption
  (let [s (-> (entered) (checked {:t :t11 :w w :r r})
              (checked {:t :cleanup-adopt :n n :th :worker})
              (checked {:t :cleanup-park :th :worker})
              (checked {:t :cleanup-deliver :n n :sequence 1 :value :ready}))]
    ;; Callback-before-return cannot re-adopt the suspending frame or dispatch
    ;; another one. Its existing callback sequence must survive the handoff.
    (refused s {:t :cleanup-adopt :n n :th :worker} ::cleanup/wrong-slice)
    (refused s {:t :cleanup-claim :n n :th :foreign} ::cleanup/slice-busy)
    (let [s (-> s (checked {:t :t38 :th :worker})
                (checked {:t :cleanup-claim :n n :th :foreign}))]
      (is (= 1 (get-in s [:env :native n :sequence])))
      (is (= :ready (get-in s [:env :native n :delivery])))
      (is (m/join-ready? (finish s :foreign) w r)))))

(deftest adoption-edge-oracle-rejects-an-equivalent-replacement-frame
  (let [before (checked (entered) {:t :t11 :w w :r r})
        action {:t :cleanup-adopt :n n :th :worker}
        after (checked before action)
        worker (get-in after [:env :threads :worker])
        foreign (get-in after [:env :threads :foreign])
        moved (-> after (assoc-in [:env :threads :foreign] worker)
                  (update-in [:env :threads] #(if foreign (assoc % :worker foreign) (dissoc % :worker))))]
    ;; Local conservation sees one correct owner and one claimed frame; the
    ;; pre/post oracle must also preserve the physical thread's identity.
    (is (empty? (cleanup/errors moved)))
    (doseq [corrupt [moved (assoc-in after [:env :native n :sequence] 9)]]
      (is (some #(= :TL21 (:id %))
                (inv/edge-check {:before before :action action :after corrupt}))))))

(deftest generic-thread-entry-cannot-forge-a-frame-to-adopt
  (let [ready (cancelled)]
    (refused ready {:t :thread-entry :th :foreign
                    :thread {:world w :run r :scope r :executing? true :retired? true}}
             ::m/protected-cleanup)))

(deftest released-world-can-adopt-its-surviving-physical-frame
  (let [released (checked (entered) {:t :t34 :w w})
        claimed (checked released {:t :cleanup-adopt :n n :th :worker})]
    (is (= :released (get-in claimed [:worlds w :status])))
    (is (false? (m/join-ready? claimed w w)))
    (let [done (finish claimed :worker)]
      (is (m/join-ready? done w w))
      (is (empty? (get-in done [:env :cleanup-cells]))))))

(deftest queued-adoption-still-checks-the-original-physical-frame
  (let [adopt {:t :cleanup-adopt :n n :th :worker}
        before (-> (checked (entered) {:t :t11 :w w :r r})
                   (assoc-in [:worlds w :queue] [{:action adopt}]))
        action {:t :queued :w w}
        after (checked before action)
        corrupt (-> after
                    (assoc-in [:env :threads :foreign] (get-in after [:env :threads :worker]))
                    (update-in [:env :threads] dissoc :worker))]
    (is (empty? (cleanup/errors corrupt)))
    (is (some #(= :TL21 (:id %))
              (inv/edge-check {:before before :action action :after corrupt})))))
