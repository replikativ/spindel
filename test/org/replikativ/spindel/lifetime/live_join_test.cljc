(ns org.replikativ.spindel.lifetime.live-join-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]))

(def w [:w 0])
(def r [:spin 1])
(def successor [:spin 2])
(def scope [:scope :id 0])
(def native [:cancel [:o 1]])

(defn checked [s action]
  (let [{after :state :keys [refusal observation]} (m/attempt s action)]
    (is (nil? refusal) (pr-str [action refusal]))
    (is (empty? (inv/check after)))
    (is (empty? (inv/edge-check {:before s :action action :after after
                                 :refusal refusal :observation observation})))
    after))

(defn fixture [status thread? native?]
  (reduce checked (m/init-state {:slices? true})
          (concat [{:t :t12 :w w :scope scope :parent [:root w]}
                   {:t :t04 :w w :e :spin :scope scope :mode :callback}]
                  (when thread? [{:t :slice-enter :w w :r r :th :worker}])
                  (when native? [{:t :t05 :w w :r r :kind :external :debtor [:host :native]}])
                  (when (and native? (= :completed status)) [{:t :t06 :w w :o [:o 1]}])
                  [(case status
                     :completed {:t :t07 :w w :r r :value :answer}
                     :stale {:t :t09 :w w :e :spin})])))

(defn join [s x]
  (let [action {:t :join :w w :x x}
        result (m/attempt s action)]
    (is (empty? (inv/edge-check {:before s :action action :after (:state result)
                                 :refusal (:refusal result) :observation (:observation result)})))
    (:observation result)))

(deftest live-joins-count-completed-and-stale-physical-participants
  (doseq [status [:completed :stale]
          [thread? native?] [[true false] [false true] [true true]]]
    (let [s (fixture status thread? native?)]
      (is (= status (:status (m/run s w r))))
      (is (= {:complete? false :busy [r]} (join s r)))
      (let [action {:t :join :w w :x r :timeout? true}
            result (m/attempt s action)]
        (is (= ::m/join-timeout (get-in result [:refusal :error])))
        (is (= [r] (get-in result [:refusal :busy])))
        (is (= s (:state result)))
        (is (empty? (inv/edge-check {:before s :action action :after (:state result)
                                     :refusal (:refusal result)}))))
      (doseq [x [scope [:root w] w]]
        (let [result (join s x)]
          (is (false? (:complete? result)))
          (is (contains? (set (:busy result)) r)))))))

(deftest live-joins-wait-for-each-exit-in-either-order
  (doseq [status [:completed :stale]
          [thread? native?] [[true false] [false true] [true true]]
          reverse? [false true]]
    (let [s (fixture status thread? native?)
          exits (cond-> [] thread? (conj {:t :t38 :th :worker})
                        native? (conj {:t :native-progress :n native :state :joined}))
          exits (if reverse? (reverse exits) exits)
          states (reductions checked s exits) done (last states)]
      (doseq [state (butlast states)]
        (is (false? (:complete? (join state r)))))
      (is (= {:complete? true :busy []} (join done r)))
      ;; A successor is a separate generation. It still blocks the owning
      ;; scope/world, but cannot keep the old generation's physical join open.
      (let [done (if (= :stale status) (checked done {:t :t11 :w w :r successor}) done)]
        (doseq [x [scope [:root w] w]]
          (is (= {:complete? true :busy []} (join done x))))))))

(deftest nonphysical-completed-or-stale-storage-does-not-block-a-run-join
  (doseq [status [:completed :stale]]
    (let [s (fixture status false false)]
      (is (= status (:status (m/run s w r))))
      (is (= {:complete? true :busy []} (join s r))))))

(deftest independent-join-oracle-rejects-logical-only-readiness
  (doseq [status [:completed :stale] native? [false true]]
    (let [s (fixture status (not native?) native?)
          edge {:before s :action {:t :join :w w :x r} :after s
                :observation {:complete? true :busy []}}]
      (is (empty? (inv/check s)))
      (is (some #(= :TL19 (:id %)) (inv/edge-check edge))))))

(deftest physical-participation-in-another-world-does-not-block-the-local-run
  (let [v [:w 1]
        s (reduce checked (m/init-state {:slices? true})
                  [{:t :t19 :w w :v v :k [:cap 0] :scope [:root w] :systems #{:memory}}
                   {:t :t04 :w v :e :spin :mode :callback}
                   {:t :slice-enter :w v :r r :th :foreign-worker}
                   {:t :t05 :w v :r r :kind :external :debtor [:host :native]}
                   {:t :t04 :w w :e :spin :mode :callback}
                   {:t :t07 :w w :r r :value :answer}])]
    (is (= :completed (:status (m/run s w r))))
    (is (= :parked (:status (m/run s v r))))
    (is (= {:complete? true :busy []} (join s r)))
    (is (= {:complete? false :busy [r]}
           (:observation (m/attempt s {:t :join :w v :x r}))))))

(deftest settlement-preparation-waits-for-the-reactive-completion-tail
  (let [v [:w 1] cap [:cap 0] op :tail-settlement
        fixture (reduce checked (m/init-state {:slices? true :cps-exit? false})
                        [{:t :t19 :w w :v v :k cap :scope [:root w] :systems #{}}
                         {:t :t02 :w v :e :driver :value 0}
                         {:t :t04 :w v :e :spin :mode :callback}
                         {:t :slice-enter :w v :r r :th :worker}
                         {:t :t05 :w v :r r :kind :track :debtor [:entity v :driver] :order 0}
                         {:t :t07 :w v :r r :value 0}])
        seal {:t :t26 :caller (m/execution-holder w [:root w]) :k cap :op op :kind :merge}
        prepare {:t :t27 :k cap :op op :steps [] :bases {} :payload :tail}
        sealed (checked fixture seal)
        refused (m/attempt sealed prepare)]
    (is (= :completed (:status (m/run fixture v r))))
    (is (m/reactive? fixture v r))
    (is (m/quiescent? fixture v))
    (is (empty? (get-in fixture [:env :native])))
    (is (false? (m/joined? fixture v)))
    ;; T26 is a logical seal. T27 is the physical preparation fence.
    (is (= :sealed (:disposition (m/cap sealed cap))))
    (is (= ::m/not-joined (get-in refused [:refusal :error])))
    (is (= sealed (:state refused)))
    (is (nil? (m/record sealed op)))
    (let [forged (assoc-in sealed (conj (m/cap-path sealed cap) :disposition) :settling)]
      ;; A buggy transition helper cannot certify its own invariant.
      (with-redefs [m/joined? (fn [_ _] true) m/quiescent? (fn [_ _] true)]
        (is (some #(= [:worker] (:threads %)) (inv/l16 forged)))))
    (let [returned (checked sealed {:t :t38 :th :worker})
          prepared (checked returned prepare)]
      (is (= v (get-in returned [:env :threads :worker :world])))
      (is (nil? (get-in returned [:env :threads :worker :run])))
      (is (m/joined? returned v))
      (is (= :settling (:disposition (m/cap prepared cap))))
      (is (= :tail (:payload-hash (m/record prepared op)))))))
