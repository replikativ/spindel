(ns org.replikativ.spindel.lifetime.logical-following-model-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.kernel :as kernel]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.composed-release-test :refer [normalize]]))

(def w [:w 0])
(def v [:w 1])
(def r [:worker 1])
(def request {:t :release-request :w w :release [:world-release w] :reason :done})
(def fork {:t :t19 :w w :v v :k :child :scope [:root w] :systems #{}})

(defn- checked [before action]
  (let [{after :state :keys [refusal observation]} (m/attempt before action)]
    (is (nil? refusal) (pr-str [action refusal]))
    (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
    (is (empty? (inv/edge-check {:before before :action action :after after
                                :refusal refusal :observation observation})) (pr-str action))
    after))

(defn- followed []
  (reduce checked (m/init-state {:slices? true})
          [{:t :t02 :w w :scope [:root w] :e :a :kind :signal :value 1}
           {:t :t02 :w w :scope [:root w] :e :b :kind :atom :value 2}
           {:t :t04 :w w :e :worker :mode :callback}
           {:t :t05 :w w :r r :kind :track :debtor [:entity w :a] :order 0}
           {:t :t05 :w w :r r :kind :track :debtor [:entity w :b] :order 1}
           {:t :t05 :w w :r r :kind :await-once :debtor [:host :gate] :order 2}
           fork]))

(defn- parity [before action expected]
  (doseq [cells? [false true]]
    (let [implementation (kernel/restore before {:cells? cells?})
          failure (try (kernel/step! implementation action) nil
                       (catch #?(:clj Exception :cljs :default) error (ex-data error)))]
      (is (nil? failure) (pr-str [cells? action failure]))
      (is (= (normalize expected) (normalize (kernel/snapshot implementation)))
          (pr-str [cells? action])))))

(defn- refused-unchanged [before]
  (let [{:keys [state refusal]} (m/attempt before request)]
    (is (= ::m/unsupported-world-release (:error refusal)) (pr-str refusal))
    (is (= before state))
    (doseq [cells? [false true]]
      (let [implementation (kernel/restore before {:cells? cells?})
            original (kernel/snapshot implementation)
            failure (try (kernel/step! implementation request) nil
                         (catch #?(:clj Exception :cljs :default) error (ex-data error)))]
        (is (= "unsupported-world-release" (some-> failure :error name)) (pr-str failure))
        (is (= original (kernel/snapshot implementation)))))))

(deftest release-admits-logical-bundles-individual-edges-and-releasing-extents
  (let [bundle (followed)
        activated (checked bundle {:t :t06 :w v :o [:o 3] :value :ready})
        ended (checked activated {:t :t11 :w v :r r})]
    (is (= #{[:bundle v #{:a :b}]} (:fdeps (m/wr bundle w))))
    (is (= #{[:a v [:o 1]] [:b v [:o 2]]} (:fdeps (m/wr activated w))))
    (is (seq (:releasing (m/wr ended w))))
    (doseq [before [bundle activated ended]]
      (let [after (checked before request)]
        (is (= :released (:status (m/wr after w))))
        (parity before request after)))))

(deftest release-admits-pending-same-family-join
  (let [bundle (followed)
        pending (-> bundle
                    (assoc-in [:worlds w :fdeps] #{})
                    (m/enqueue w {:join-bundle v :debtors #{:a :b}
                                  :members {[:o 1] {:debtor :a :source-world w :source-o [:o 1]}
                                            [:o 2] {:debtor :b :source-world w :source-o [:o 2]}}}))
        after (checked pending request)]
    (is (empty? (inv/check pending)))
    (is (= :released (:status (m/wr after w))))
    (parity pending request after)))

(deftest release-logical-extension-keeps-refusals-atomic
  (let [base (followed)]
    (doseq [kind [:deferred :mailbox]]
      (testing (str "foreign resource entity " kind)
        (refused-unchanged (assoc-in base [:worlds w :entities :a :kind] kind))))
    (doseq [kind [:timer :external :operation]]
      (testing (str "foreign unsupported obligation " kind)
        (refused-unchanged (assoc-in base [:worlds v :obligations [:o 1] :kind] kind))))
    (testing "independent family"
      (refused-unchanged (-> base (assoc-in [:lineages v :root] v)
                            (assoc-in [:worlds v :lineage :root] v))))
    (testing "active cut"
      (refused-unchanged (assoc-in base [:cuts :cut]
                                  {:phase :fenced :participants {:worlds #{w} :systems #{} :components #{}}})))
    (doseq [control [{:start-for :a :creditor-world v :o [:o 1]}
                     {:register-host [:o 1]}]]
      (refused-unchanged (m/enqueue base w control)))))

(defn- old-per-ob-conversion [before order]
  ;; Old T06 ordering after consuming the host slot and activating the Run.
  (let [started (-> before (m/end-obligation v [:o 3] :delivered)
                    (assoc-in [:worlds v :runs r :status] :running))]
    (reduce (fn [state o] (-> state (m/add-fdep v o) (m/sync-bundle w v))) started order)))

(deftest activation-converts-all-members-before-reconciling-the-bundle
  (let [before (followed)
        old-ab (old-per-ob-conversion before [[:o 1] [:o 2]])
        old-ba (old-per-ob-conversion before [[:o 2] [:o 1]])
        action {:t :t06 :w v :o [:o 3] :value :ready}
        after (checked before action)]
    ;; First old sync removed both inherited members before the second edge
    ;; existed, publishing a redundant ended subset dependent on map order.
    (is (= #{[:bundle v #{:b}]} (:releasing (m/wr old-ab w))))
    (is (= #{[:bundle v #{:a}]} (:releasing (m/wr old-ba w))))
    (is (= [:bundle v #{:b}] (:fdep-ended (first (:queue (m/wr old-ab w))))))
    (is (= [:bundle v #{:a}] (:fdep-ended (first (:queue (m/wr old-ba w))))))
    (is (empty? (:releasing (m/wr after w))))
    (is (empty? (:queue (m/wr after w))))
    (is (= #{[:a v [:o 1]] [:b v [:o 2]]} (:fdeps (m/wr after w))))
    (parity before action after)))

(deftest release-admits-ordinary-foreign-spin-run-creditor
  (let [before (reduce checked (followed)
                       [{:t :t04 :w w :e :spinner :mode :callback}
                        {:t :t05 :w w :r [:spinner 1] :kind :await-once :debtor [:host :spin-gate]}
                        {:t :t04 :w v :e :reader :mode :callback}
                        {:t :t05 :w v :r [:reader 1] :kind :await-reactive :debtor [:entity w :spinner]}])
        after (checked before request)]
    (is (some #(= :spinner (first %)) (:fdeps (m/wr before w))))
    (parity before request after)))
