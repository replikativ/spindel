(ns org.replikativ.spindel.lifetime.first-delivery-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.lifetime.model :as model]
            [org.replikativ.spindel.lifetime.invariants :as inv]))

(deftest standing-await-first-value-resumes-its-original-run
  (let [w [:w 0] p [:spin 0] c [:spin 1] s [:signal 0]
        before (reduce model/step (model/init-state)
                       [{:t :t02 :w w :e s :value 1}
                        {:t :t04 :w w :e p :mode :callback}
                        {:t :t04 :w w :e c :mode :callback}
                        {:t :t05 :w w :r [c 1] :kind :track :debtor [:entity w s]}
                        {:t :t05 :w w :r [p 1] :kind :await-reactive :debtor [:entity w c]}
                        {:t :t07 :w w :r [c 1] :value 42}])
        first-value (model/step before {:t :t08 :w w :e c :value 42})
        later-value (model/step first-value {:t :t08 :w w :e c :value 43})]
    (is (= :running (get-in first-value [:worlds w :runs [p 1] :status])))
    (is (nil? (get-in first-value [:worlds w :runs [p 2]])))
    (is (= :consumed (get-in first-value [:worlds w :obligations [:o 3] :slot])))
    (is (some #(and (= :resume (:event %)) (= [:o 3] (:o %))) (:events first-value)))
    (is (= :running (get-in later-value [:worlds w :runs [p 2] :status])))))

(defn cold-child-handoff-actions []
  (let [w [:w 0] p [:spin 0] c [:spin 1] s [:signal 0]]
    [{:t :t02 :w w :e s :value 1}
     {:t :t04 :w w :e p :mode :callback}
     {:t :t05 :w w :r [p 1] :kind :await-reactive :debtor [:entity w c]}
     {:t :t05 :w w :r [c 1] :kind :track :debtor [:entity w s]}
     {:t :t07 :w w :r [c 1] :value 10}
     {:t :t08 :w w :e c :value 10}
     {:t :t07 :w w :r [p 1] :value 10}
     {:t :t08 :w w :e p :value 10}
     {:t :t09 :w w :e c :cause :rerun! :order 0}
     {:t :t05 :w w :r [c 2] :kind :track :debtor [:entity w s]}
     {:t :t07 :w w :r [c 2] :value 20}
     {:t :t08 :w w :e c :value 20}
     {:t :t05 :w w :r [p 2] :kind :await-reactive :debtor [:entity w c]}
     {:t :t06 :w w :o [:o 4] :value 20}
     {:t :t07 :w w :r [p 2] :value 20}
     {:t :t08 :w w :e p :value 20}]))

(deftest reused-cold-child-survives-predecessor-retirement
  (let [s (reduce model/step (model/init-state) (cold-child-handoff-actions))
        w [:w 0] p [:spin 0] c [:spin 1]]
    (is (= [p 2] (get-in s [:worlds w :entities c :owner])))
    (is (= [p 2] (get-in s [:worlds w :runs [c 2] :owner])))
    (is (model/reactive? s w [c 2]))
    (is (empty? (inv/check s)))))

(deftest prefix-source-survives-predecessor-retirement
  (let [w [:w 0] p [:spin 0] e [:signal 0]
        s (reduce model/step (model/init-state)
                  [{:t :t04 :w w :e p :mode :callback}
                   {:t :t02 :w w :e e :r [p 1] :order 0 :value 1}
                   {:t :t05 :w w :r [p 1] :kind :track :debtor [:entity w e] :order 1}
                   {:t :t07 :w w :r [p 1] :value 1}
                   {:t :t08 :w w :e p :value 1}
                   {:t :signal-write :w w :e e :value 2}
                   {:t :t08 :w w :e e :value 2}
                   {:t :t05 :w w :r [p 2] :kind :track :debtor [:entity w e] :order 1}
                   {:t :t07 :w w :r [p 2] :value 2}])]
    (is (= [p 2] (get-in s [:worlds w :entities e :owner])))
    (is (nil? (get-in s [:worlds w :entities e :creator])))
    (is (contains? (get-in s [:worlds w :runs [p 2] :creations]) e))
    (is (empty? (inv/check s)))))

(defn prefix-scope-actions []
  (let [w [:w 0] p [:spin 0] e [:signal 0] scope [:scope 0]]
    [{:t :t04 :w w :e p :mode :callback}
     {:t :t12 :w w :scope scope :parent [p 1] :order 0}
     {:t :t02 :w w :scope scope :e e :value 1}
     {:t :t05 :w w :r [p 1] :kind :track :debtor [:entity w e] :order 1}
     {:t :t07 :w w :r [p 1] :value 1}
     {:t :t08 :w w :e p :value 1}
     {:t :signal-write :w w :e e :value 2}
     {:t :t08 :w w :e e :value 2}
     {:t :t05 :w w :r [p 2] :kind :track :debtor [:entity w e] :order 1}
     {:t :t07 :w w :r [p 2] :value 2}]))

(deftest prefix-scope-survives-predecessor-retirement
  (let [w [:w 0] p [:spin 0] e [:signal 0] scope [:scope 0]
        s (reduce model/step (model/init-state) (prefix-scope-actions))]
    (is (= [p 2] (get-in s [:worlds w :scopes scope :parent])))
    (is (= :open (get-in s [:worlds w :scopes scope :status])))
    (is (= scope (get-in s [:worlds w :entities e :owner])))
    (is (empty? (inv/check s)))))

(defn prefix-cache-actions []
  (let [w [:w 0] p [:spin 0] e [:signal 0]]
    [{:t :t02 :w w :e e :value 1}
     {:t :t04 :w w :e p :mode :callback}
     {:t :t03 :w w :r [p 1] :key :cached :order 0}
     {:t :t05 :w w :r [p 1] :kind :track :debtor [:entity w e] :order 1}
     {:t :t07 :w w :r [p 1] :value 1}
     {:t :t08 :w w :e p :value 1}
     {:t :signal-write :w w :e e :value 2}
     {:t :t08 :w w :e e :value 2}
     {:t :t05 :w w :r [p 2] :kind :track :debtor [:entity w e] :order 1}
     {:t :t07 :w w :r [p 2] :value 2}]))

(deftest prefix-cache-survives-predecessor-retirement
  (let [w [:w 0] p [:spin 0]
        s (reduce model/step (model/init-state) (prefix-cache-actions))]
    (is (= [p 2] (get-in s [:worlds w :entities [p :cached] :owner])))
    (is (empty? (inv/check s)))))

(deftest following-bundle-includes-descendant-scopes
  (let [w [:w 0] v [:w 1] p [:spin 0] e [:signal 0]
        scope [:scope 0] nested [:scope 1]
        before (reduce model/step (model/init-state)
                       [{:t :t04 :w w :e p :mode :callback}
                        {:t :t12 :w w :scope scope :parent [p 1]}
                        {:t :t12 :w w :scope nested :parent scope}
                        {:t :t02 :w w :scope nested :e e :value 1}
                        {:t :t05 :w w :r [p 1] :kind :await-once :debtor [:host :outside]}])
        after (model/step before {:t :t19 :w w :v v :k [:cap 0] :scope [:root w]})]
    (is (= [p 1] (get-in after [:worlds v :scopes scope :parent])))
    (is (= scope (get-in after [:worlds v :scopes nested :parent])))
    (is (= nested (get-in after [:worlds v :entities e :owner])))
    (is (= :inherited (get-in after [:worlds v :entities e :origin])))
    (is (empty? (inv/check after)))))

(defn burst-child-handoff-actions []
  (let [w [:w 0] p [:spin 0] c [:spin 1] s [:signal 0]]
    (into (vec (take 8 (cold-child-handoff-actions)))
          [{:t :t09 :w w :e p :order 0}
           {:t :t09 :w w :e p :order 0}
           {:t :t09 :w w :e p :order 0}
           {:t :t05 :w w :r [p 4] :kind :await-reactive :debtor [:entity w c]}
           {:t :t06 :w w :o [:o 3] :value 10}
           {:t :t07 :w w :r [p 4] :value 10}])))

(deftest retired-intermediate-does-not-break-predecessor-adoption
  (let [s (reduce model/step (model/init-state) (burst-child-handoff-actions))
        w [:w 0] p [:spin 0] c [:spin 1]]
    (is (= [p 4] (get-in s [:worlds w :entities c :owner])))
    (is (= [p 4] (get-in s [:worlds w :runs [c 1] :owner])))
    (is (model/reactive? s w [c 1]))
    (is (empty? (inv/check s)))))

(defn retired-creator-adoption-actions []
  (let [w [:w 0] p [:spin 0] c [:spin 1]]
    [{:t :t04 :w w :e p :mode :callback}
     {:t :t01 :w w :e c :r [p 1] :tok [:h 0]}
     {:t :t05 :w w :r [p 1] :kind :await-reactive :debtor [:entity w c]}
     {:t :t07 :w w :r [c 1] :value 10}
     {:t :t08 :w w :e c :value 10}
     {:t :t07 :w w :r [p 1] :value 10}
     {:t :t09 :w w :e p :order 0}
     {:t :t07 :w w :r [p 2] :value :skip}
     {:t :t09 :w w :e p :order 0}
     {:t :t01 :w w :e c :r [p 3] :tok [:h 1]}]))

(deftest retired-creator-remains-an-adoption-anchor
  (let [s (reduce model/step (model/init-state) (retired-creator-adoption-actions))
        w [:w 0] p [:spin 0] c [:spin 1]]
    (is (= [p 3] (get-in s [:worlds w :entities c :creator])))
    (is (nil? (get-in s [:worlds w :entities c :owner])))
    (is (not (contains? (get-in s [:worlds w :runs [p 3] :ancestors]) [p 1])))
    (is (empty? (inv/check s)))))
