(ns org.replikativ.spindel.lifetime.lockstep-smoke-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.walk :as walk]
            [org.replikativ.spindel.atom :as runtime-atom]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.lifetime.lockstep :as lockstep]
            [org.replikativ.spindel.lifetime.model :as model]))

(def w [:w 0])
(def e [:spin 0])

(deftest lockstep-smoke
  (is (= :passed (:status (lockstep/replay [{:t :t04 :e e}]))))
  (is (= :passed (:status (lockstep/replay [{:t :t01 :w w :e e}
                                            {:t :t04 :w w :e e :mode :callback}]))))
  (is (= :passed (:status (lockstep/replay [{:t :t02 :w w :e [:signal 0] :value 1}
                                            {:t :signal-write :w w :e [:signal 0] :value 2}]))))
  (is (= :skipped (:status (lockstep/replay [{:t :t13 :w w :scope [:scope 0]}])))))

(deftest oracle-detects-corruption
  (with-redefs [lockstep/project (fn [& _] {:entities {e {:kind :spin :completed? true :result :wrong}}})]
    (is (= :discrepancy (:status (lockstep/replay [{:t :t04 :w w :e e}]))))))

(deftest scripted-effects
  (doseq [name [:track :await :nested :collections :following]]
    (let [result (lockstep/replay (lockstep/scripted-corpus name))]
      (is (= :passed (:status result)) (pr-str result)))))

(deftest enabling-an-unprojected-component-fails-closed
  (with-redefs [lockstep/components (assoc-in lockstep/components [:owners :enabled?] true)]
    (is (= :discrepancy (:status (lockstep/replay [{:t :t04 :w w :e e}]))))))

(deftest unsupported-middle-is-not-deleted
  (let [result (lockstep/replay [{:t :t04 :w w :e e}
                                 {:t :t13 :w w :scope [:scope 0]}
                                 {:t :t07 :w w :r [e 1]}])]
    (is (= :skipped (:status result)))
    (is (= 1 (:checked result)))
    (is (= :B4 (get-in result [:reason :step])))))

(deftest model-and-runtime-visible-views
  (let [v [:w 1] source [:signal 0]
        state (reduce model/step (model/init-state)
                      [{:t :t02 :w w :e source :value 1}
                       {:t :t19 :w w :v v :k [:cap 0] :scope [:root w]}])
        view {:entities {source {:kind :signal :completed? false :result 1}}
              :lineage :absent :obligations :absent}
        projected {:worlds {w view v view}}]
    (is (= (lockstep/comparable state) (lockstep/comparable projected)))
    (is (empty? (lockstep/projection-invariants projected)))
    (is (= :L12 (:id (first (lockstep/projection-invariants
                             (assoc-in projected [:worlds w :entities source :result] (fn []))))))))
  (is (every? #(contains? lockstep/action-support %) (keys model/transitions))))

(deftest symbolic-script-addresses-survive-fork-order
  (let [v [:w 1]
        trace [{:t :t19 :w w :v v :k [:cap 0] :scope [:root w]}
               {:t :t04 :w v :e [:spin 0]}
               {:t :t04 :w w :e [:spin 2]}]
        result (lockstep/replay trace)]
    (is (= :passed (:status result)) (pr-str result))))

(deftest lexical-row-survives-host-handle-registration
  (let [trace [{:t :t04 :w w :e e}
               {:t :t01 :w w :r [e 1] :e [:spin 1] :tok [:tok 0]}
               {:t :t01 :w w :e [:spin 1] :tok [:tok 1]}]
        result (lockstep/replay trace)]
    (is (= :passed (:status result)) (pr-str result))))

(deftest cancellation-event-provenance
  (let [before (model/step (model/init-state) {:t :t04 :w w :e e})
        after (model/step before {:t :t11 :w w :r [e 1]})]
    (is (= [{:w w :e e :value ::model/cancelled}]
           (lockstep/model-deliveries before after)))))

(deftest minimization-preserves-the-refusal-type
  (is (not= (lockstep/discrepancy-key {:differences [{:kind :refusal :expected :unknown-handle :actual nil}]})
            (lockstep/discrepancy-key {:differences [{:kind :refusal :expected :token-spin-mismatch :actual nil}]}))))

(deftest following-cold-row-after-host-registration
  (let [v [:w 1] parent [:spin 2] child [:spin 3]
        trace [{:t :t19 :w w :v v :k [:cap 0] :scope [:root w]}
               {:t :t04 :w v :e parent}
               {:t :t04 :w w :e parent}
               {:t :t01 :w w :r [parent 1] :e child :tok [:tok 0]}
               {:t :t01 :w w :e child :tok [:tok 1]}]
        result (lockstep/replay trace)]
    (is (= :passed (:status result)) (pr-str result))))

(deftest every-enabled-component-fails-closed
  (doseq [component (keys lockstep/components)
          actions [[] [{:t :t04 :w w :e e}]]]
    (let [original lockstep/project]
      (with-redefs [lockstep/components (assoc-in lockstep/components [component :enabled?] true)
                    lockstep/project (fn [& args] (assoc (apply original args) component :absent))]
        (is (= :discrepancy (:status (lockstep/replay actions))) (str component " " actions))))))

(deftest literal-payload-mutations
  (doseq [tag [:w :scope :o :tok :op :cap :cut]
          payload [[tag 0] {:nested [[tag 0] #{[tag 0]}]}]
          kind [:signal :spin]]
    (let [original lockstep/project
          entity [kind 0]
          actions (if (= :signal kind)
                    [{:t :t02 :w w :e entity :value payload}]
                    [{:t :t01 :w w :e entity :tok [:tok 0]}
                     {:t :t04 :w w :e entity :tok [:tok 0]}
                     {:t :t07 :w w :r [entity 1] :value payload}])]
      (with-redefs [lockstep/project
                    (fn [& args]
                      (let [p (apply original args)]
                        (if (= payload (get-in p [:entities entity :result]))
                          (assoc-in p [:entities entity :result]
                                    (walk/postwalk #(if (= [tag 0] %) [tag 999] %) payload)) p)))]
        (let [result (lockstep/replay actions)]
          (is (some #(= :state (:kind %)) (:differences result)) (pr-str [kind payload result])))))))

(deftest unexpected-entities-are-visible
  (let [original lockstep/project]
    (doseq [kind [:atom :timer :waiter :fork :cache-row :surprise]]
      (with-redefs [lockstep/project
                    (fn [& args] (assoc-in (apply original args) [:entities [kind 99]]
                                           {:kind kind :result :wrong}))]
        (is (= :discrepancy (:status (lockstep/replay [{:t :t04 :w w :e e}]))))))))

(deftest synchronous-completion-boundary
  (doseq [name [:completion :errors]]
    (let [result (lockstep/replay (lockstep/scripted-corpus name))]
      (is (= :passed (:status result)) (pr-str result)))))

(deftest minimization-keeps-invariant-relation
  (let [result {:status :discrepancy :trace [:first :second] :differences []
                :invariants [{:id :L4 :evidence [{:index :creations :missing e}]}]}]
    (with-redefs [lockstep/replay (fn [_] {:status :discrepancy :differences []
                                           :invariants [{:id :L12 :evidence [{:non-data-state true}]}]})]
      (is (= (:trace result) (:minimal-trace (lockstep/minimize-discrepancy result)))))))

(deftest implemented-component-mutations
  (let [original lockstep/project]
    (doseq [kind (get-in lockstep/components [:entities :kinds]) mutation [:missing :wrong-value]]
      (let [entity [kind 0]
            actions (if (= kind :signal) [{:t :t02 :w w :e entity :value 1}]
                        [{:t :t04 :w w :e entity}])]
        (with-redefs [lockstep/project
                      (fn [& args] (let [p (apply original args)]
                                     (if (= mutation :missing) (update p :entities dissoc entity)
                                         (assoc-in p [:entities entity :result] :wrong))))]
          (is (= :discrepancy (:status (lockstep/replay actions)))))))))

(deftest acceptance-requires-complete-coverage
  (let [required {:witnesses #{"required"} :transitions #{:t07 :t08} :components #{:entities}
                  :profiles #{:one-spin}}
        result (lockstep/replay (lockstep/scripted-corpus :completion))
        report {:component-availability {:entities true} :coverage (lockstep/coverage) :witnesses {"required" result}
                :profiles {:one-spin [result]} :profile-limits {:one-spin {:status :exhausted}}
                :model-normative {"normative" [{:id :L16}]}}]
    (is (= :passed (:status (lockstep/acceptance report required))))
    (doseq [status [:skipped :discrepancy :truncated]]
      (is (= :failed (:status (lockstep/acceptance (assoc-in report [:witnesses "required" :status] status) required)))))
    (is (= :failed (:status (lockstep/acceptance (assoc-in report [:profile-limits :one-spin :status] :state-limit) required)))))
  (is (= :failed (:status (lockstep/acceptance {} {:witnesses #{} :transitions #{} :components #{:waiters} :profiles #{}})))))

(deftest completion-constituents-and-hooks
  (let [result (lockstep/replay (lockstep/scripted-corpus :completion))]
    (is (= [:t07 :t08] (mapv (comp :t :action) (get-in result [:boundaries 2 :constituents]))))
    (is (every? #(contains? % :model-invariants) (get-in result [:boundaries 2 :constituents]))))
  (let [actions (conj (lockstep/scripted-corpus :completion)
                      {:t :t11 :w w :r [e 1]}
                      {:t :t08 :w w :e e :value 42})
        result (lockstep/replay actions)]
    (is (= :needs-microstep-hook (get-in result [:reason :reason])))))

(deftest invariant-coverage-follows-descriptors
  (let [descriptors (into {} (for [[c d] lockstep/components]
                               [c (assoc d :enabled? (contains? #{:waiters :obligations} c))]))]
    (with-redefs [lockstep/components descriptors]
      (is (= [{:id :L24 :scope :full :required #{:waiters :obligations}}]
             (vec (lockstep/invariant-coverage))))
      (is (= :L24 (:id (first (lockstep/projection-invariants
                               {:env {:waiters {:token {:registered? true :armed? false}}}}))))))))

(deftest invariant-signatures-distinguish-index-relations
  (is (not= (lockstep/discrepancy-key {:invariants [{:id :L4 :evidence [{:index :creations :missing e}]}]})
            (lockstep/discrepancy-key {:invariants [{:id :L4 :evidence [{:index :spawned :missing e}]}]}))))

(deftest alpha-renaming-shares-component-identities
  (let [descriptor {:enabled? true :model-view identity :projected-view identity
                    :compare = :available? (constantly true)}]
    (with-redefs [lockstep/components {:a (assoc descriptor :model-view :a :projected-view :a)
                                       :b (assoc descriptor :model-view :b :projected-view :b)}]
      (is (not= (lockstep/comparable {:a {:owner [:scope 0]} :b {:scope [:scope 0]}})
                (lockstep/comparable {:a {:owner [:scope 0]} :b {:scope [:scope 999]}} false))))))

(deftest explicitly-declared-host-templates-follow-visibility
  (let [actions [{:t :t01 :w w :e e :tok [:tok 0]}
                 {:t :t19 :w w :v [:w 1] :k [:cap 0] :scope [:root w]}]
        result (lockstep/replay actions)]
    (is (= :passed (:status result)) (pr-str result))))

(deftest local-completion-resumes-an-awaiting-script
  (let [child [:spin 1]
        actions [{:t :t01 :w w :e e :tok [:tok 0]}
                 {:t :t01 :w w :e child :tok [:tok 1]}
                 {:t :t04 :w w :e e :tok [:tok 0]}
                 {:t :t04 :w w :e child :tok [:tok 1]}
                 {:t :t05 :w w :r [e 1] :kind :await-once :debtor [:entity w child]}
                 {:t :t07 :w w :r [child 1] :value :child-result}]
        result (lockstep/replay actions)]
    (is (= :passed (:status result)) (pr-str result))
    (is (= :resume (get-in result [:boundaries 5 :constituents 1 :induced 0 :event])))))

(deftest unexpected-runtime-atoms-are-visible
  (let [original lockstep/new-driver]
    (with-redefs [lockstep/new-driver
                  (fn [] (let [driver (original)]
                           (binding [ec/*execution-context* (get-in @driver [:contexts w])]
                             (swap! driver assoc :unmapped-handle (runtime-atom/atom :unexpected)))
                           driver))]
      (let [result (lockstep/replay [])]
        (is (= :discrepancy (:status result)))
        (is (= :state (get-in result [:differences 0 :kind])))))))

(deftest completion-cannot-hide-an-implicit-interleaving
  (doseq [prefix [(lockstep/scripted-corpus :completion)
                  (conj (lockstep/scripted-corpus :track) {:t :t07 :w w :r [e 1] :value 42})]]
    (let [actions (conj prefix {:t :t11 :w w :r [e 1]})
          result (lockstep/replay actions)]
      (is (= :skipped (:status result)))
      (is (= :needs-microstep-hook (get-in result [:reason :reason]))))))
