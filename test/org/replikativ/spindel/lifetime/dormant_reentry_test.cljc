(ns org.replikativ.spindel.lifetime.dormant-reentry-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.cps-cleanup-test :as c]))

(def w c/w)
(def v [:w 1])
(def r c/r)

(defn forked []
  (reduce c/checked (c/entered)
          [{:t :t05 :w w :r r :kind :timer :debtor [:host :executor]}
           {:t :t38 :th :worker}
           {:t :t19 :w w :v v :k [:cap 0] :scope [:root w]}]))

(deftest dormant-reentry-cannot-donate-already-retired-prefix-resources
  (doseq [order [-1 0 1 2] cause [:dirty :rerun! :track]]
    (let [before (forked) parent (m/wr before w)
          action {:t :t09 :w v :e :spin :cause cause :order order}
          after (c/checked before action)
          successor (m/current after v :spin)]
      (is (= :inherited (:status (m/run before v r))))
      (is (= [:spin 2] successor))
      (is (nil? (m/run after v r)))
      (is (nil? (m/ent after v :cell)))
      (is (empty? (:creations (m/run after v successor))))
      (is (= parent (m/wr after w)))
      (is (not-any? #(= [v r] (:owner %)) (vals (get-in after [:env :native])))))))
