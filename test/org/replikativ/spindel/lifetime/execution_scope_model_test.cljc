(ns org.replikativ.spindel.lifetime.execution-scope-model-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]))

(def w [:w 0])
(def v [:w 1])
(def root [:root w])
(def s0 [:scope :id 0])
(def s1 [:scope :id 1])
(def s2 [:scope :id 2])
(def r [:spin 1])

(defn checked [s action]
  (let [{after :state :keys [refusal observation]} (m/attempt s action)]
    (is (nil? refusal) (pr-str [action refusal]))
    (is (empty? (inv/check after)) (pr-str (inv/check after)))
    (is (empty? (inv/edge-check {:before s :action action :after after
                                 :refusal refusal :observation observation})))
    after))

(defn opened []
  (checked (m/init-state) {:t :t12 :w w :scope s0 :parent root}))

(defn refuses [s action error]
  (let [result (m/attempt s action)]
    (is (= error (get-in result [:refusal :error])) (pr-str result))
    (is (= s (:state result)))))

(deftest scope-allocation-is-fresh-and-disjoint-from-run-ids
  (let [initial (m/init-state)
        open (opened)
        closed (checked open {:t :t13 :w w :scope s0})]
    (doseq [id [root [:spin 1] [:scope 1] :scope nil [:scope :id -1] [:scope :id 0.5]]]
      (refuses initial {:t :t12 :w w :scope id :parent root} ::m/invalid-scope-id))
    (doseq [state [open closed]
            parent [root s0]]
      (refuses state {:t :t12 :w w :scope s0 :parent parent} ::m/scope-id-reused))
    (refuses initial {:t :t12 :w w :scope s0 :parent s0} ::m/scope-id-reused)
    (refuses open {:t :t12 :w w :scope s1 :parent [:scope :id 99]} ::m/closed-scope)
    (refuses open {:t :t12 :w w :scope s1 :parent [:root v]} ::m/closed-scope)
    (is (= closed (m/step closed {:t :t13 :w w :scope s0})))
    (is (= closed (m/step closed {:t :t13 :w w :scope [:scope :id 900]})))
    ;; :scope is also a legal spin ID: its Run [:scope 1] is never a Scope ID.
    (let [running (checked initial {:t :t04 :w w :e :scope :mode :callback})]
      (doseq [state [initial running]]
        (refuses state {:t :t13 :w w :scope [:scope 1]} ::m/invalid-scope-id))
      (is (m/run running w [:scope 1])))))

(deftest closed-scopes-drop-without-history-or-escaped-capability-retention
  (let [initial (m/init-state)
        final (reduce (fn [state n]
                        (let [id [:scope :id n]
                              next (-> state
                                       (checked {:t :t12 :w w :scope id :parent root})
                                       (checked {:t :t13 :w w :scope id}))]
                          (is (= 1 (count (:scopes (m/wr next w)))))
                          (is (zero? (:scope-balance (m/wr next w))))
                          next)) initial (range 128))]
    (is (= 128 (:next-scope (m/wr final w))))
    (is (= (keys (m/wr initial w)) (keys (m/wr final w)))))
  (testing "many intentionally open empty scopes are legitimate liveness"
    (let [state (reduce (fn [s n]
                          (checked s {:t :t12 :w w :scope [:scope :id n] :parent root}))
                        (m/init-state) (range 32))]
      (is (= 32 (:scope-balance (m/wr state w))))
      (is (= 33 (:scopes (inv/census (m/wr state w)))))
      (is (= 32 (:scope-parents (inv/census (m/wr state w)))))
      (is (empty? (inv/l13 state))))))

(deftest scope-forest-and-storage-oracles-detect-corruption-independently
  (let [state (-> (opened)
                  (checked {:t :t12 :w w :scope s1 :parent s0}))]
    (doseq [bad [(assoc-in state [:worlds w :scopes s0 :parent] s1)
                 (assoc-in state [:worlds w :scopes s0 :parent] [:scope :id 99])
                 (assoc-in state [:worlds w :scopes s0 :parent] [:root v])
                 (assoc-in state [:worlds w :scopes s0 :status] :closed)
                 (assoc-in state [:worlds w :scope-balance] 1)
                 (assoc-in state [:worlds w :next-scope] 1)]]
      (is (seq (inv/scope-errors bad))))
    (let [bad (reduce (fn [s n]
                        (assoc-in s [:worlds w :scopes [:scope :id n]]
                                  {:kind :explicit :parent root :status :closed}))
                      (m/init-state) (range 100))]
      (is (seq (inv/scope-errors bad)))
      (is (some #(= :scopes (:index %)) (inv/l13 bad)))))
  (let [state (-> (m/init-state)
                  (checked {:t :t04 :w w :e :spin :mode :callback})
                  (checked {:t :t12 :w w :scope s0 :parent r}))
        bad (assoc-in state [:worlds w :runs r :owner] s0)]
    (is (seq (inv/scope-errors bad)))))

(deftest nested-close-preserves-physical-join-anchors
  (let [state (reduce checked (m/init-state)
                      [{:t :t12 :w w :scope s0 :parent root}
                       {:t :t12 :w w :scope s1 :parent s0}
                       {:t :t04 :w w :scope s1 :e :spin :mode :callback}
                       {:t :slice-enter :w w :r r :th :worker}
                       {:t :t13 :w w :scope s0}])]
    (is (= #{root} (set (keys (:scopes (m/wr state w))))))
    (is (= [r s1 s0 root w] (:anchor (m/run state w r))))
    (doseq [target [s0 s1 r root w]]
      (is (false? (m/join-ready? state w target))))
    (let [after (checked state {:t :t38 :th :worker})]
      (doseq [target [s0 s1 r root w]]
        (is (m/join-ready? after w target))))))

(deftest forked-scope-allocation-is-local-and-monotone
  (let [state (reduce checked (m/init-state)
                      [{:t :t04 :w w :e :spin :mode :callback}
                       {:t :t12 :w w :scope s0 :parent r}
                       {:t :t12 :w w :scope s1 :parent s0}
                       {:t :t05 :w w :r r :kind :external :debtor [:host :external]}
                       {:t :t19 :w w :v v :k [:cap 0] :scope root :systems #{}}])]
    (is (= 2 (:next-scope (m/wr state v))))
    (is (= 2 (:scope-balance (m/wr state v))))
    (let [after (-> state
                    (checked {:t :t12 :w v :scope s2 :parent [:root v]})
                    (checked {:t :t13 :w w :scope s0}))]
      (is (= #{[:root v] s0 s1 s2} (set (keys (:scopes (m/wr after v))))))
      (is (= #{root} (set (keys (:scopes (m/wr after w)))))))))

(def scoped-fork-close
  [{:t :t12 :w w :scope s0 :parent root}
   {:t :t19 :w w :v v :k [:cap 0] :scope s0 :systems #{}}
   {:t :t13 :w w :scope s0}])

(defn independent-world-state []
  (let [other [:w 9] world (m/world-row other nil :root other)]
    (-> (m/init-state)
        (assoc-in [:worlds other] world)
        (update :registry conj other)
        (update :known-worlds conj other)
        (assoc-in [:lineages other] (:lineage world)))))

(deftest scoped-fork-discard-survives-owner-row-reclamation
  (let [state (reduce checked (m/init-state) scoped-fork-close)]
    (is (nil? (get-in state [:worlds w :scopes s0])))
    (is (= [{:custody-dispatch [:custody-claim 0] :cap [:cap 0] :op [:custody-op [:custody-claim 0]] :seq 1}] (:queue (m/wr state v))))
    (let [released (checked state {:t :release-request :w w :reason :done :release [:world-release w]})
          op [:custody-op [:custody-claim 0]]
          done (reduce checked released [{:t :queued :w v}
                                         {:t :t27 :k [:cap 0] :op op :payload :empty :bases {} :steps []}
                                         {:t :t29 :op op}])]
      (is (= :released (:status (m/wr released w))))
      (is (= :releasing (get-in released [:env :releases w :phase])))
      (is (= (get-in state [:env :cleanup-targets]) (get-in released [:env :cleanup-targets])))
      (is (= :joined (get-in done [:env :releases w :phase])))))
  (testing "an unrelated independent family's outstanding capability is not this root's authority"
    (let [other [:w 9]
          state (checked (independent-world-state)
                         {:t :t19 :w other :v [:w 10] :k [:cap 0]
                          :scope [:root other] :systems #{}})
          after (checked state {:t :release-request :w w :reason :done :release [:world-release w]})]
      (is (= :released (:status (m/wr after w))))
      (is (= :live (:status (m/wr after other))))
      (is (= :open (:disposition (m/cap after [:cap 0])))))))

(defn related-tombstone-state []
  (let [lineage {:parent w :root w :mode :following :cut nil :basis nil}]
    (-> (m/init-state)
        (assoc-in [:worlds v] {:id v :lineage lineage :status :released})
        (update :known-worlds conj v)
        (assoc-in [:lineages v] lineage))))

(deftest explicit-release-profile-remembers-family-provenance-without-owner-history
  (let [state (related-tombstone-state)]
    (is (empty? (inv/check state)))
    (let [released (checked state {:t :release-request :w w :reason :done :release [:world-release w]})]
      (is (= :joined (get-in released [:env :releases w :phase])))
      (is (= (:known-worlds state) (:known-worlds released)))
      (is (= (:lineages state) (:lineages released))))))

(defn scope-adoption-actions [cause order]
  (let [parent [:spin 0] run [parent 1] source [:signal 0]
        prefix [:scope :id 0] nested [:scope :id 1]
        equal [:scope :id 2] suffix [:scope :id 3]]
    [{:t :t02 :w w :e source :value 0}
     {:t :t04 :w w :e parent :mode :callback}
     {:t :t12 :w w :scope prefix :parent run :order 0}
     {:t :t12 :w w :scope nested :parent prefix}
     {:t :t12 :w w :scope equal :parent run :order 1}
     {:t :t12 :w w :scope suffix :parent run :order 2}
     {:t :t02 :w w :scope nested :e :prefix-source :value :prefix}
     {:t :t02 :w w :scope equal :e :equal-source :value :equal}
     {:t :t02 :w w :scope suffix :e :suffix-source :value :suffix}
     {:t :t05 :w w :r run :kind :track :debtor [:entity w source] :order 1}
     {:t :t07 :w w :r run :value 0}
     {:t :t09 :w w :e parent :cause cause :order order}
     {:t :t07 :w w :r [parent 2] :value 1}]))

(deftest reactive-prefix-scope-adoption-is-strict-and-nested
  (let [actions (scope-adoption-actions :track 1)
        before (reduce checked (m/init-state) (subvec actions 0 11))
        reentered (checked before (nth actions 11))
        final (checked reentered (nth actions 12))
        prefix [:scope :id 0] nested [:scope :id 1]]
    (is (= 4 (:scope-balance (m/wr before w))))
    (is (= 4 (:scope-balance (m/wr reentered w))))
    (doseq [state [before reentered final]]
      (is (= 4 (:next-scope (m/wr state w)))))
    (is (= [[:spin 0] 2] (get-in reentered [:worlds w :scopes prefix :parent])))
    (is (= prefix (get-in reentered [:worlds w :scopes nested :parent])))
    ;; Boundary and later scopes stay with the old Run until it retires.
    (doseq [scope [[:scope :id 2] [:scope :id 3]]]
      (is (= [[:spin 0] 1] (get-in reentered [:worlds w :scopes scope :parent])))
      (is (nil? (get-in final [:worlds w :scopes scope]))))
    (is (= #{root prefix nested} (set (keys (:scopes (m/wr final w))))))
    (is (= 2 (:scope-balance (m/wr final w))))
    (is (= nested (get-in final [:worlds w :entities :prefix-source :owner])))
    (is (nil? (m/ent final w :equal-source)))
    (is (nil? (m/ent final w :suffix-source)))
    (is (nil? (m/run final w [[:spin 0] 1])))))

(deftest dirty-restart-adopts-no-scope-prefix
  (let [final (reduce checked (m/init-state) (scope-adoption-actions :dirty -1))]
    (is (= #{root} (set (keys (:scopes (m/wr final w))))))
    (is (zero? (:scope-balance (m/wr final w))))
    (is (= 4 (:next-scope (m/wr final w))))
    (doseq [source [:prefix-source :equal-source :suffix-source]]
      (is (nil? (m/ent final w source))))))
