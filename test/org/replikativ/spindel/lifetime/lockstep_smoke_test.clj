(ns org.replikativ.spindel.lifetime.lockstep-smoke-test
  (:require [clojure.test :refer [deftest is]]
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
