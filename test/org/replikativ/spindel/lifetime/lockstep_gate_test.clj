(ns org.replikativ.spindel.lifetime.lockstep-gate-test
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.lifetime.lockstep :as l]
            [org.replikativ.spindel.lifetime.model :as m]))

(def w [:w 0])
(def e [:spin 0])
(def child [:spin 1])
(def r [e 1])

(def ownership-trace
  [{:t :t12 :w w :scope [:scope 0] :parent [:root w]}
   {:t :t04 :w w :e e :mode :callback}
   {:t :t01 :w w :r r :e child :order 3}
   {:t :t04 :w w :scope [:scope 0] :e child :mode :callback}])

(deftest b1-compares-each-ownership-field
  (let [state (reduce m/step (m/init-state) ownership-trace)
        descriptors (update-vals l/components
                                 #(assoc % :enabled? (= :B1 (:step %))))]
    (is (= r (get-in state [:worlds w :entities child :owner])))
    (is (= [:scope 0] (get-in state [:worlds w :runs [child 1] :owner])))
    (with-redefs [l/components descriptors]
      (doseq [path [[:entities child :owner] [:entities child :creator]
                    [:entities child :order] [:runs [child 1] :owner]
                    [:scopes [:scope 0] :parent] [:scopes [:scope 0] :kind]
                    [:scopes [:scope 0] :status]]]
        (is (not= (l/comparable state)
                  (l/comparable (assoc-in state (into [:worlds w] path) :corrupt) false))
            (pr-str path))))))

(deftest b1-run-view-does-not-enable-b3-lifecycle
  (let [state (reduce m/step (m/init-state) ownership-trace)]
    (with-redefs [l/components (update-vals l/components #(assoc % :enabled? (= :B1 (:step %))))]
      (is (= (l/comparable state)
             (l/comparable (assoc-in state [:worlds w :runs [child 1] :status] :different) false)))
      (is (not= (l/comparable state)
                (l/comparable (assoc-in state [:worlds w :root] [:scope 999]) false))))))
