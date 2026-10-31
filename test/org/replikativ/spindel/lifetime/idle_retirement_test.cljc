(ns org.replikativ.spindel.lifetime.idle-retirement-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.custody-model-test :as custody]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]))

(def w [:w 0])
(def root [:root w])
(def scope [:scope :id 0])

(defn checked [before action]
  (let [after (m/step before action)]
    (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
    (is (empty? (inv/edge-check {:before before :action action :after after}))
        (pr-str [action (inv/edge-check {:before before :action action :after after})]))
    after))
(defn walk [state actions] (reduce checked state actions))

(defn pair-actions [parent child ownership signal?]
  (let [p [parent 1] c [child 1]]
    (vec (concat
          [{:t :t01 :w w :e parent :tok :hp}
           {:t :t01 :w w :e child :tok :hc}
           {:t :t04 :w w :e parent :tok :hp :mode :callback}
           {:t :t01 :w w :e child :r p :order 0 :tok :hc}]
          (when (= ownership :scope) [{:t :t12 :w w :scope scope :parent p :order 0}])
          [{:t :t04 :w w :e child :tok :hc :mode :deref
            :scope (case ownership :scope scope :independent root p)}
           {:t :t05 :w w :r p :kind :await-reactive :debtor [:entity w child] :tok :hc}
           ;; The parent now observes the child; withdraw its redundant direct
           ;; host observer so this fixture isolates retirement ordering.
           {:t :withdraw-deref :w w :o [:o 1]}]
          (when signal?
            [{:t :t02 :w w :e :source :value 1}
             {:t :t05 :w w :r c :kind :track :debtor [:entity w :source] :order 1}
             {:t :t06 :w w :o [:o 3] :value 1}])
          [{:t :t07 :w w :r c :value 42}
           {:t :t08 :w w :e child :value 42}
           {:t :t07 :w w :r p :value 42}
           {:t :t08 :w w :e parent :value 42}
           {:t :t14 :w w :e parent :pin? true}
           {:t :unsubscribe :w w :o [:o 0]}]))))

(defn reorder-rows [state reverse?]
  (reduce (fn [state table]
            (update-in state [:worlds w table]
                       #(into (array-map) ((if reverse? reverse identity) (seq %)))))
          state [:entities :runs]))

(deftest idle-batch-preserves-owned-cache-invalidation
  (doseq [[parent child] [[:z-parent :a-child] [:a-parent :z-child]]
          ownership [:direct :scope :independent]
          signal? [false true]
          reverse? [false true]]
    (testing (pr-str [parent child ownership signal? reverse?])
      (let [before (reorder-rows (walk (m/init-state) (pair-actions parent child ownership signal?)) reverse?)
            _ (is (= 2 (count (:runs (m/wr before w)))))
            after (checked before {:t :t14 :w w :e parent :pin? false})]
        (is (empty? (:runs (m/wr after w))))
        (is (true? (:dirty? (m/ent after w child))))
        ;; Closing a child Scope precedes parent end-run-links. Its cancellation
        ;; invalidates the still-consumed standing parent await; direct Run
        ;; cancellation occurs after parent end-run-links instead.
        (is (= (or signal? (= ownership :scope))
               (boolean (:dirty? (m/ent after w parent)))))
        (is (= [42 42] (mapv #(:result (m/ent after w %)) [parent child])))
        (is (every? nil? (map #(:owner (m/ent after w %)) [parent child])))
        (is (= 2 (count (filter #(= :run-exit (:event %)) (:events after)))))
        (when (= ownership :scope) (is (nil? (get-in after [:worlds w :scopes scope]))))))))

(defn union-cycle-actions [parent child]
  (let [p1 [parent 1] p2 [parent 2] c1 [child 1]]
    [{:t :t04 :w w :e parent :mode :deref}
     {:t :t01 :w w :e child :r p1 :order 0}
     {:t :t04 :w w :e child :scope root :mode :deref}
     {:t :t07 :w w :r p1 :value :p-one}
     {:t :t08 :w w :e parent :debtor-world w :value :p-one}
     {:t :invalidate-computation :w w :e parent}
     {:t :t04 :w w :e parent :scope c1 :mode :deref}
     {:t :t01 :w w :e child :r p2 :order 0}
     {:t :t07 :w w :r p2 :value :p-two}
     {:t :t08 :w w :e parent :debtor-world w :value :p-two}
     {:t :withdraw-deref :w w :o [:o 1]}]))

(deftest entity-and-execution-forests-may-have-a-valid-union-cycle
  (doseq [[parent child] [[:z-parent :a-child] [:a-parent :z-child]]]
    (let [before (walk (m/init-state) (union-cycle-actions parent child))
          p2 [parent 2] c1 [child 1]
          action {:t :t07 :w w :r c1 :value :child}
          after (checked before action)
          exits (filter #(= :run-exit (:event %)) (:events after))]
      (is (= root (:owner (m/run before w c1))))
      (is (= c1 (:owner (m/run before w p2))))
      (is (= p2 (:owner (m/ent before w child))))
      (is (= {[w c1] 1 [w p2] 1}
             (frequencies (map #(vector (:world %) (:r %)) exits))))
      (is (= {c1 :superseded p2 :cancelled} (into {} (map (juxt :r :cause) exits))))
      (is (empty? (:runs (m/wr after w))))
      (let [corrupt (update after :events conj (first exits))]
        (is (some #(= :RunExitOnce (:id %))
                  (inv/edge-check {:before before :action action :after corrupt})))))))

(deftest generation-ordering-uses-run-identities
  (let [p :p c :c p1 [p 1] p2 [p 2] p3 [p 3] c1 [c 1]
        before (walk (m/init-state)
                     [{:t :t04 :w w :e p :mode :deref}
                      {:t :t01 :w w :e c :r p1 :order 0}
                      {:t :t04 :w w :e c :scope p1 :mode :deref}
                      {:t :t07 :w w :r p1 :value 1}
                      {:t :invalidate-computation :w w :e p}
                      {:t :t04 :w w :e p :scope c1 :mode :deref}
                      {:t :t09 :w w :e p :cause :track :order 0}
                      {:t :t07 :w w :r c1 :value 2}])]
    ;; This is a reachable live graph, not an assertion that all rows are idle.
    ;; P1 -> C1 -> P2 is acyclic even though collapsed Spin IDs give P <-> C.
    (is (= p1 (:owner (m/run before w c1))))
    (is (= c1 (:owner (m/run before w p2))))
    (is (= :running (:status (m/run before w p3))))
    (is (= [p1 c1 p2] (m/idle-retirement-order before w #{p c})))
    (is (= (:runs (m/wr before w)) (:runs (m/wr (m/rule-l before w) w))))))

(deftest union-cycle-claims-and-physical-anchors-use-real-run-owners
  (let [parent :z-parent child :a-child c1 [child 1] p2 [parent 2]
        initial (assoc-in (custody/scope-fixture) [:model :cps-exit?] false)
        before (walk initial (union-cycle-actions parent child))
        entered (checked before {:t :slice-enter :w w :r c1 :th :actor})
        accepted (checked entered
                          (assoc (custody/transfer (custody/holder w custody/s0)
                                                   (custody/holder w c1)
                                                   custody/k0 custody/k1 :cycle-move)
                                 :acceptance {:th :actor :order 1}))
        after (checked accepted {:t :t07 :w w :r c1 :value :done})
        claims (vals (get-in after [:custody :claims]))
        exits (filter #(= :run-exit (:event %)) (:events after))]
    (is (= 1 (count claims)))
    (is (= custody/k1 (:cap (first claims))))
    (is (= (custody/holder w c1) (:origin (first claims))))
    (is (= [(custody/holder w c1) (custody/holder w root)] (:anchor (first claims))))
    ;; Entity A was allocated under P2, but the physical Run always belonged
    ;; to Root. Neither retirement scheduling nor entity release can reparent it.
    (is (= :unwinding (:status (m/run after w c1))))
    (is (= [c1 root w] (:anchor (m/run after w c1))))
    (is (nil? (m/run after w p2)))
    (is (= {c1 :superseded p2 :cancelled} (into {} (map (juxt :r :cause) exits))))
    (is (= 2 (count exits)))
    (is (false? (:complete? (m/join-observation after {:w w :x root}))))
    (let [returned (checked after {:t :t38 :th :actor})]
      (is (nil? (m/run returned w c1)))
      (is (= claims (vals (get-in returned [:custody :claims])))))))

(defn scope-cycle-actions [parent child scope physical?]
  (let [p1 [parent 1] p2 [parent 2] c1 [child 1]]
    (vec (concat
          [{:t :t04 :w w :e parent :mode :deref}
           {:t :t01 :w w :e child :r p1 :order 0}
           {:t :t04 :w w :e child :scope root :mode :deref}]
          (when physical?
            [{:t :slice-enter :w w :r c1 :th :active-child}
             {:t :t02 :w w :scope c1 :e :cell :kind :atom :value :payload}])
          [{:t :t12 :w w :scope scope :parent c1 :kind :explicit}
           {:t :t07 :w w :r p1 :value :p-one}
           {:t :t08 :w w :e parent :debtor-world w :value :p-one}
           {:t :invalidate-computation :w w :e parent}
           {:t :t04 :w w :e parent :scope scope :mode :deref}
           {:t :t01 :w w :e child :r p2 :order 0}
           {:t :t07 :w w :r p2 :value :p-two}
           {:t :t08 :w w :e parent :debtor-world w :value :p-two}]))))

(defn scope-cycle-custody-before []
  (let [scope [:scope :id 1]
        actions (scope-cycle-actions :z-parent :a-child scope false)]
    (reduce m/step (custody/scope-fixture)
            (mapcat (fn [action]
                      (cond-> [action]
                        (= :t12 (:t action))
                        (conj (custody/transfer (custody/holder w custody/s0)
                                                (custody/holder w scope)
                                                custody/k0 custody/k1 :scope-cycle-move)))) actions))))

(deftest scope-cycle-preserves-the-independent-roots-physical-cell-cleanup
  (let [w [:w 0] root [:root w] parent :z-parent child :a-child
        p1 [parent 1] p2 [parent 2] c1 [child 1] scope [:scope :id 0]
        cell [w c1 :cell] ticket (cleanup/ticket w c1)
        before (reduce checked (m/init-state {:slices? true :cps-exit? true})
                       [{:t :t04 :w w :e parent :mode :deref}
                        {:t :t01 :w w :e child :r p1 :order 0}
                        {:t :t04 :w w :e child :scope root :mode :deref}
                        {:t :slice-enter :w w :r c1 :th :active-child}
                        {:t :t02 :w w :scope c1 :e :cell :kind :atom :value :payload}
                        {:t :t12 :w w :scope scope :parent c1 :kind :explicit}
                        {:t :t07 :w w :r p1 :value :p-one}
                        {:t :t08 :w w :e parent :debtor-world w :value :p-one}
                        {:t :invalidate-computation :w w :e parent}
                        {:t :t04 :w w :e parent :scope scope :mode :deref}
                        {:t :t01 :w w :e child :r p2 :order 0}
                        {:t :t07 :w w :r p2 :value :p-two}
                        {:t :t08 :w w :e parent :debtor-world w :value :p-two}])
        _ (is (= root (:owner (m/run before w c1))))
        _ (is (= c1 (get-in before [:worlds w :scopes scope :parent])))
        _ (is (= scope (:owner (m/run before w p2))))
        _ (is (= p2 (:owner (m/ent before w child))))
        action {:t :t13 :w w :scope scope}
        after (checked before action)
        errors (inv/check after)]
    (is (= 0 (:scope-balance (m/wr after w))))
    (is (= #{root} (set (keys (:scopes (m/wr after w))))))
    (is (= {[w c1] 1 [w p2] 1}
           (frequencies (for [event (:events after) :when (= :run-exit (:event event))]
                          [(:world event) (:r event)]))))
    (is (= :unwinding (:status (m/run after w c1))))
    (is (= [c1 root w] (:anchor (m/run after w c1))))
    (is (= [c1 root w] (get-in after [:env :native ticket :anchor])))
    (is (= #{ticket} (get-in after [:env :cleanup-cells cell :holders])))
    (is (= :payload (get-in after [:env :cleanup-cells cell :result])))
    ;; The collateral Root-owned child is outside the closed Scope's physical
    ;; domain: Scope join is ready, but Root/child join must still wait.
    (is (true? (m/join-ready? after w scope)))
    (is (false? (m/join-ready? after w root)))
    (when (empty? errors)
      (let [returned (checked after {:t :t38 :th :active-child})
            claimed (checked returned {:t :cleanup-claim :n ticket :th :cleaner})
            duplicate (m/attempt claimed {:t :cleanup-claim :n ticket :th :duplicate-cleaner})
            cleaned (checked claimed {:t :cleanup-cell :th :cleaner :cell cell :value :cleaned})
            returning (checked cleaned {:t :cleanup-return :th :cleaner})
            done (checked returning {:t :t38 :th :cleaner})]
        (is (some? (:refusal duplicate)))
        (is (= claimed (:state duplicate)))
        (is (= :cleaned (get-in returning [:env :cleanup-cells cell :result])))
        (is (false? (m/join-ready? returning w root)))
        (is (true? (m/join-ready? done w root)))
        (is (nil? (m/run done w c1)))
        (is (nil? (get-in done [:env :native ticket])))
        (is (empty? (get-in done [:env :cleanup-cells])))
        (is (= 0 (:scope-balance (m/wr done w))))))))

(deftest model-scope-cycle-claims-custody-before-its-parent-disappears
  (let [w custody/a root [:root w] parent :z-parent child :a-child
        p1 [parent 1] p2 [parent 2] c1 [child 1] scope [:scope :id 1]
        initial (custody/scope-fixture)
        before (reduce checked initial
                       [{:t :t04 :w w :e parent :mode :deref}
                        {:t :t01 :w w :e child :r p1 :order 0}
                        {:t :t04 :w w :e child :scope root :mode :deref}
                        {:t :t12 :w w :scope scope :parent c1 :kind :explicit}
                        (custody/transfer (custody/holder w custody/s0)
                                          (custody/holder w scope)
                                          custody/k0 custody/k1 :scope-cycle-move)
                        {:t :t07 :w w :r p1 :value :p-one}
                        {:t :t08 :w w :e parent :debtor-world w :value :p-one}
                        {:t :invalidate-computation :w w :e parent}
                        {:t :t04 :w w :e parent :scope scope :mode :deref}
                        {:t :t01 :w w :e child :r p2 :order 0}
                        {:t :t07 :w w :r p2 :value :p-two}
                        {:t :t08 :w w :e parent :debtor-world w :value :p-two}])
        expected-anchor [(custody/holder w scope) (custody/holder w c1) (custody/holder w root)]
        after (checked before {:t :t13 :w w :scope scope})
        claims (get-in after [:custody :claims])
        [id claim] (first claims)]
    (is (= scope (:owner (m/run before w p2))))
    (is (= root (:owner (m/run before w c1))))
    (is (= p2 (:owner (m/ent before w child))))
    ;; No physical Run row survives to recover A1's ancestry afterward.
    (is (empty? (:runs (m/wr after w))))
    (is (= 1 (:scope-balance (m/wr after w))))
    (is (= #{root custody/s0} (set (keys (:scopes (m/wr after w))))))
    (is (= 1 (count claims)))
    (is (= custody/k1 (:cap claim)))
    (is (= (custody/holder w scope) (:origin claim)))
    (is (= expected-anchor (:anchor claim)))
    (is (= [:cleanup id] (:holder (m/cap after custody/k1))))
    (is (= #{custody/k1} (get-in after [:custody :by-holder [:cleanup id]])))
    (is (= 1 (count (:queue (m/wr after custody/child)))))))

(defn sibling-actions [nested?]
  (let [w [:w 0] root [:root w] p :z-parent a :a-child x :zz-sibling
        p1 [p 1] p2 [p 2] a1 [a 1] x1 [x 1]
        s [:scope :id 0] t [:scope :id 1] u [:scope :id 2]]
    (vec (concat
          [{:t :t04 :w w :e p :mode :deref}
           {:t :t01 :w w :e a :r p1 :order 0}
           {:t :t04 :w w :e a :scope root :mode :deref}
           {:t :t12 :w w :scope s :parent a1 :kind :explicit}]
          (when nested? [{:t :t12 :w w :scope t :parent s :kind :explicit}
                         {:t :t12 :w w :scope u :parent s :kind :explicit}])
          [{:t :t07 :w w :r p1 :value :p-one}
           {:t :t08 :w w :e p :debtor-world w :value :p-one}
           {:t :invalidate-computation :w w :e p}
           {:t :t04 :w w :e p :scope (if nested? t s) :mode :deref}
           {:t :t01 :w w :e a :r p2 :order 0}
           {:t :t07 :w w :r p2 :value :p-two}
           {:t :t08 :w w :e p :debtor-world w :value :p-two}
           {:t :t04 :w w :e x :scope (if nested? u s) :mode :deref}
           {:t :slice-enter :w w :r x1 :th :physical-sibling}
           {:t :t02 :w w :scope x1 :e :sibling-cell :kind :atom :value :payload}]))))

(defn sibling-prefix [nested? cps?]
  (walk (m/init-state {:slices? true :cps-exit? cps?}) (sibling-actions nested?)))

(deftest later-sibling-keeps-the-original-parent-chain
  (doseq [nested? [false true] cps? [false true]]
    (let [w [:w 0] root [:root w] a1 [:a-child 1] p2 [:z-parent 2] x1 [:zz-sibling 1]
          s [:scope :id 0] u [:scope :id 2]
          before (sibling-prefix nested? cps?)
          expected (vec (concat [x1] (when nested? [u]) [s a1 root w]))
          after (checked before {:t :t13 :w w :scope s})
          ticket (cleanup/ticket w x1) cell [w x1 :sibling-cell]]
      (is (= root (:owner (m/run before w a1))))
      (is (= (if nested? [:scope :id 1] s) (:owner (m/run before w p2))))
      (is (nil? (m/run after w a1)))
      (is (nil? (m/run after w p2)))
      (is (= :unwinding (:status (m/run after w x1))))
      (is (= expected (:anchor (m/run after w x1))))
      (is (= 0 (:scope-balance (m/wr after w))))
      (is (= #{root} (set (keys (:scopes (m/wr after w))))))
      (is (false? (m/join-ready? after w root)))
      (is (false? (m/join-ready? after w s)))
      (is (= {[w a1] 1 [w p2] 1 [w x1] 1}
             (frequencies (for [ev (:events after) :when (= :run-exit (:event ev))]
                            [(:world ev) (:r ev)]))))
      (when cps?
        (is (= expected (get-in after [:env :native ticket :anchor])))
        (is (= #{ticket} (get-in after [:env :cleanup-cells cell :holders])))
        (is (= :payload (get-in after [:env :cleanup-cells cell :result]))))
      ;; A coherently shortened Run/ticket anchor used to evade all static
      ;; checks. The edge proof must recover the actual full BEFORE forest.
      (let [wrong (vec (remove #{root} expected))
            corrupt (cond-> (assoc-in after [:worlds w :runs x1 :anchor] wrong)
                      cps? (assoc-in [:env :native ticket :anchor] wrong))
            errors (inv/retirement-anchor-errors {:before before :action {:t :t13 :w w :scope s}
                                                  :after corrupt})]
        (is (some #(= :ordinary-retirement-anchor (:kind %)) errors))
        (when cps? (is (some #(= :cleanup-retirement-anchor (:kind %)) errors)))
        (is (some #(= :RetirementAnchor (:id %))
                  (inv/edge-check {:before before :action {:t :t13 :w w :scope s} :after corrupt}))))
      (when (empty? (inv/check after))
        (let [returned (checked after {:t :t38 :th :physical-sibling})
              done (if cps?
                     (reduce checked returned [{:t :cleanup-claim :n ticket :th :cleaner}
                                               {:t :cleanup-cell :th :cleaner :cell cell :value :cleaned}
                                               {:t :cleanup-return :th :cleaner}
                                               {:t :t38 :th :cleaner}]) returned)]
          (is (m/join-ready? done w root))
          (is (nil? (m/run done w x1)))
          (is (empty? (get-in done [:env :cleanup-cells]))))))))

