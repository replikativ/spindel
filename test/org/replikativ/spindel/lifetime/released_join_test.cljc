(ns org.replikativ.spindel.lifetime.released-join-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]))

(def w [:w 0])
(def run [:spin 1])
(def scope :resource)
(def native [:cancel [:o 1]])

(defn checked [state action]
  (let [{after :state :keys [refusal observation]} (m/attempt state action)
        edge {:before state :action action :after after :refusal refusal :observation observation}]
    (is (empty? (inv/check after)))
    (is (empty? (inv/edge-check edge)))
    (when (not= :join (:t action)) (is (nil? refusal) (pr-str action)))
    after))

(defn released-state [thread? native?]
  (reduce checked (m/init-state {:slices? true})
          (concat [{:t :t12 :w w :scope scope :parent [:root w]}
                   {:t :t04 :w w :e :spin :scope scope :mode :callback}]
                  (when thread? [{:t :slice-enter :w w :r run :th :worker}])
                  (when native? [{:t :t05 :w w :r run :kind :external :debtor [:host :native]}])
                  [{:t :t34 :w w}])))

(deftest selected-idle-threads-do-not-block-joining-a-released-world
  (let [state (checked (m/init-state) {:t :t34 :w w})]
    (is (= {:complete? true :busy []} (:observation (m/attempt state {:t :join :w w :x w :timeout? true}))))
    (checked state {:t :join :w w :x w :timeout? true})))

(deftest released-run-scope-and-world-joins-wait-for-every-physical-participant
  (doseq [[thread? native?] [[true false] [false true] [true true]]]
    (let [state (released-state thread? native?)]
      (is (= #{:id :lineage :status} (set (keys (m/wr state w)))))
      (doseq [x [run scope [:root w] w]]
        (let [action {:t :join :w w :x x :timeout? true} result (m/attempt state action)]
          (is (= ::m/join-timeout (get-in result [:refusal :error])))
          (is (= #{run} (set (get-in result [:refusal :busy]))))
          (checked state action)))
      (let [exited (if thread? (checked state {:t :t38 :th :worker}) state)]
        (is (= (not native?) (m/join-ready? exited w w)))
        (when thread? (is (nil? (get-in exited [:env :threads :worker :anchor]))))
        (let [joined (if native? (checked exited {:t :native-progress :n native :state :joined}) exited)]
          (when native? (is (nil? (get-in joined [:env :native native :anchor]))))
          (doseq [x [run scope [:root w] w]]
            (is (= {:complete? true :busy []} (:observation (m/attempt joined {:t :join :w w :x x :timeout? true}))))
            (checked joined {:t :join :w w :x x :timeout? true})))))))

(deftest released-join-targets-remain-in-the-physical-search-alphabet
  (let [state (released-state true true)
        targets (set (for [a (m/raw-enabled state) :when (= :join (:t a))] (:x a)))]
    (is (every? targets [run scope [:root w] w]))))

(deftest release-oracle-rejects-lost-scope-evidence
  (doseq [native? [false true]]
    (let [before (reduce checked (m/init-state)
                         (concat [{:t :t12 :w w :scope scope :parent [:root w]}
                                  {:t :t04 :w w :e :spin :scope scope :mode :callback}]
                                 (if native? [{:t :t05 :w w :r run :kind :external :debtor [:host :native]}]
                                     [{:t :slice-enter :w w :r run :th :worker}])))
          action {:t :t34 :w w} correct (m/step before action)
          path (if native? [:env :native native :anchor] [:env :threads :worker :anchor])
          corrupt (update-in correct path #(vec (remove #{scope} %)))]
      ;; World and run are still present in the anchor. Only the independent
      ;; release-edge oracle can notice that a closed scope was omitted.
      (is (empty? (inv/check corrupt)))
      (is (some #(= :TL19 (:id %)) (inv/edge-check {:before before :action action :after corrupt})))
      (is (empty? (inv/edge-check {:before before :action action :after correct}))))))
