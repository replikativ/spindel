(ns org.replikativ.spindel.lifetime.rooted-liveness-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]))

(def w [:w 0])
(def v [:w 1])

(defn check-walk! [actions]
  (reduce (fn [before action]
            (let [after (m/step before action)]
              (is (empty? (inv/check after)) (pr-str action))
              (is (empty? (inv/edge-check {:before before :action action :after after})) (pr-str action))
              after))
          (m/init-state) actions))

(defn completed-pair-actions []
  [{:t :t01 :w w :e :child :tok :hc}
   {:t :t01 :w w :e :parent :tok :hp}
   {:t :t04 :w w :e :parent :tok :hp :mode :callback}
   {:t :t05 :w w :r [:parent 1] :kind :await-reactive :debtor [:entity w :child] :tok :hc}
   {:t :t07 :w w :r [:child 1] :value 42}
   {:t :t08 :w w :e :child :value 42}
   {:t :t07 :w w :r [:parent 1] :value 42}
   {:t :t08 :w w :e :parent :value 42}])

(deftest completed-island-normalizes-before-host-collection
  (let [actions (conj (completed-pair-actions) {:t :unsubscribe :w w :o [:o 0]})
        state (check-walk! actions)]
    (is (empty? (get-in state [:worlds w :runs])))
    (is (empty? (get-in state [:worlds w :obligations])))
    (is (= {:parent 42 :child 42} (update-vals (get-in state [:worlds w :entities]) :result)))
    (is (every? nil? (map :owner (vals (get-in state [:worlds w :entities])))))
    (let [final (check-walk! (into actions [{:t :t16 :tok :hp}
                                            {:t :t17 :w w :e :parent :tok :hp}
                                            {:t :t16 :tok :hc}
                                            {:t :t17 :w w :e :child :tok :hc}]))]
      (is (empty? (get-in final [:worlds w :entities]))))))

(deftest normalization-oracle-rejects-an-omitted-local-cleanup
  (let [before (reduce m/step (m/init-state) (completed-pair-actions))
        action {:t :unsubscribe :w w :o [:o 0]}
        ;; Simulate an implementation that commits the host unsubscribe but
        ;; omits Rule L. Static storage invariants deliberately allow extent.
        corrupt (m/end-obligation (assoc before :events []) w [:o 0] :creditor-cancelled)
        correct (m/step before action)]
    (is (empty? (inv/check corrupt)))
    (is (= #{:extent} (m/reasons corrupt w :parent)))
    (is (some #(= :TL20 (:id %))
              (inv/edge-check {:before before :action action :after corrupt})))
    (is (empty? (inv/edge-check {:before before :action action :after correct})))
    ;; A GC notification is not an ordinary cleanup publication. The
    ;; independent oracle must preserve that distinction too.
    (let [unreachable (m/step corrupt {:t :t16 :tok :hp})
          gc-action {:t :t17 :w w :e :parent :tok :hp}
          notified (m/step unreachable gc-action)]
      (is (empty? (inv/edge-check {:before unreachable :action gc-action :after notified}))))))

(deftest another-observer-keeps-the-ownership-closure
  (let [state (check-walk! (into (completed-pair-actions)
                                 [{:t :t04 :w w :e :child :tok :hc :mode :callback}
                                  {:t :unsubscribe :w w :o [:o 0]}]))]
    ;; A final child delivers its own callback once, so use a pin as the
    ;; independent anchor while the original parent observer disappears.
    (is (empty? (get-in state [:worlds w :runs]))))
  (let [state (check-walk! (into (completed-pair-actions)
                                 [{:t :t14 :w w :e :child :pin? true}
                                  {:t :unsubscribe :w w :o [:o 0]}]))]
    (is (= 2 (count (get-in state [:worlds w :runs]))))
    (is (m/execution-live? state w :parent))
    (is (m/execution-live? state w :child))))

(deftest unfinished-work-survives-without-handles-or-observers
  (let [prefix [{:t :t01 :w w :e :parent :tok :hp}
                {:t :t04 :w w :e :parent :tok :hp :mode :callback}
                {:t :t05 :w w :r [:parent 1] :kind :timer :debtor [:host :executor]}
                {:t :unsubscribe :w w :o [:o 0]}
                {:t :t16 :tok :hp}
                {:t :t17 :w w :e :parent :tok :hp}]
        state (check-walk! prefix)]
    (is (= :parked (get-in state [:worlds w :runs [:parent 1] :status])))
    (is (m/execution-live? state w :parent))
    (let [final (check-walk! (into prefix [{:t :t06 :w w :o [:o 1] :value nil}
                                           {:t :t07 :w w :r [:parent 1] :value 42}]))]
      (is (empty? (get-in final [:worlds w :entities])))
      (is (empty? (get-in final [:worlds w :runs]))))))

(deftest explicit-resource-scope-is-an-independent-anchor
  (let [prefix [{:t :t12 :w w :scope :resource-scope :parent [:root w]}
                {:t :t02 :w w :e :source :scope :resource-scope :value 1}]
        state (check-walk! prefix)]
    (is (m/execution-live? state w :source))
    (is (= :resource-scope (get-in state [:worlds w :entities :source :owner])))
    (let [final (check-walk! (conj prefix {:t :t13 :w w :scope :resource-scope}))]
      (is (empty? (get-in final [:worlds w :entities]))))))

(deftest a-completed-run-does-not-anchor-its-own-source
  (let [state (check-walk! [{:t :t01 :w w :e :parent :tok :hp}
                            {:t :t04 :w w :e :parent :tok :hp :mode :callback}
                            {:t :t02 :w w :e :source :r [:parent 1] :value 1}
                            {:t :t07 :w w :r [:parent 1] :value 42}
                            {:t :t08 :w w :e :parent :value 42}])]
    (is (nil? (get-in state [:worlds w :entities :source])))
    (is (empty? (get-in state [:worlds w :runs])))
    (is (= 42 (get-in state [:worlds w :entities :parent :result])))))

(deftest following-read-through-does-not-pin-a-completed-owner
  (let [prefix [{:t :t04 :w w :e :parent :mode :callback}
                {:t :t02 :w w :e :source :r [:parent 1] :value 1}
                {:t :t19 :w w :v v :k [:cap 1] :scope [:root w] :systems #{}}]
        state (check-walk! prefix)]
    (is (= w (m/read-source state v :source)))
    (is (nil? (get-in state [:worlds v :entities :source])))
    (let [final (check-walk! (into prefix [{:t :t07 :w w :r [:parent 1] :value 42}
                                           {:t :t08 :w w :e :parent :value 42}]))]
      (is (nil? (m/read-source final v :source)))
      (is (nil? (get-in final [:worlds w :entities :source]))))))

(deftest frozen-value-basis-survives-live-world-reclamation
  (let [prefix [{:t :t12 :w w :scope :resource-scope :parent [:root w]}
                {:t :t02 :w w :e :source :scope :resource-scope :value 1}
                {:t :t20 :c :cut :scope [:root w] :mode :frozen
                 :participants {:worlds #{w} :components #{} :systems #{}}}
                {:t :t21 :c :cut} {:t :t22 :c :cut}
                {:t :t23 :c :cut :v v :k [:cap 1] :mode :frozen}
                {:t :t24 :c :cut :e :fork-result}
                {:t :t07 :w v :r [:fork-result 1] :value :ready}
                {:t :t13 :w w :scope :resource-scope}]
        state (check-walk! prefix)]
    (is (nil? (get-in state [:worlds w :entities :source])))
    (is (= 1 (get-in state [:worlds v :entities :source :result])))
    (is (= 1 (get-in state [:worlds v :lineage :basis w :entities :source :result])))
    (is (every? empty? (map :runs (vals (:worlds state)))))
    (is (every? empty? (map :obligations (vals (:worlds state)))))
    (let [final (check-walk! (conj prefix {:t :t13 :w v :scope :resource-scope}))]
      (is (nil? (get-in final [:worlds v :entities :source])))
      (is (= 1 (get-in final [:worlds v :lineage :basis w :entities :source :result]))))))

(defn queued-host-actions []
  [{:t :t01 :w w :e :target :tok :h}
   {:t :t04 :w w :e :target :tok :h :mode :callback}
   {:t :t07 :w w :r [:target 1] :value 42}
   {:t :t08 :w w :e :target :value 42}
   {:t :t19 :w w :v v :k [:cap 1] :scope [:root w] :systems #{}}
   {:t :t04 :w v :e :target :mode :callback}
   {:t :t16 :tok :h}
   {:t :t17 :w w :e :target :tok :h}])

(deftest queued-host-admission-retains-the-promised-value
  (let [state (check-walk! (queued-host-actions))]
    (is (= #{:obl} (m/reasons state w :target)))
    (is (= 42 (get-in state [:worlds w :entities :target :result])))
    (let [final (check-walk! (conj (queued-host-actions) {:t :queued :w w}))]
      (is (nil? (get-in final [:worlds w :entities :target])))
      (is (some #(= :host-delivery (:event %)) (:events final))))))

(defn held-host-actions []
  (let [actions (queued-host-actions)]
    (into (conj (subvec actions 0 5)
                {:t :t20 :c :held-cut :scope [:root w] :mode :frozen
                 :participants {:worlds #{w} :components #{} :systems #{}}})
          (subvec actions 5))))

(deftest a-held-host-registration-is-still-an-observation
  (let [actions (held-host-actions) state (check-walk! actions)]
    (is (= #{:obl} (m/reasons state w :target)))
    (is (= 42 (get-in state [:worlds w :entities :target :result])))
    (is (= 1 (count (get-in state [:env :outside]))))
    (let [final (check-walk! (into actions [{:t :t25 :c :held-cut} {:t :queued :w w}]))]
      (is (nil? (get-in final [:worlds w :entities :target])))
      (is (some #(= :host-delivery (:event %)) (:events final))))))

(defn foreign-completed-cycle-actions []
  [{:t :t19 :w w :v v :k [:cap 1] :scope [:root w] :systems #{}}
   {:t :t02 :w w :e :source :value 1}
   {:t :t04 :w w :e :a :mode :callback}
   {:t :t05 :w w :r [:a 1] :kind :track :debtor [:entity w :source]}
   {:t :t07 :w w :r [:a 1] :value 1}
   {:t :t08 :w w :e :a :value 1}
   {:t :t04 :w v :e :b :mode :callback}
   {:t :t05 :w v :r [:b 1] :kind :await-reactive :debtor [:entity w :a]}
   {:t :t06 :w v :o [:o 3] :value 1}
   {:t :t07 :w v :r [:b 1] :value 1}
   {:t :t08 :w v :e :b :value 1}
   {:t :t09 :w w :e :a :cause :rerun! :order -1}
   {:t :t05 :w w :r [:a 2] :kind :await-reactive :debtor [:entity v :b]}
   {:t :t06 :w w :o [:o 4] :value 1}
   {:t :t07 :w w :r [:a 2] :value 1}
   {:t :t08 :w w :e :a :value 1}
   {:t :t08 :w v :e :a :debtor-world w :value 1}
   {:t :t05 :w v :r [:b 2] :kind :await-reactive :debtor [:entity w :a]}
   {:t :t06 :w v :o [:o 5] :value 1}
   {:t :t07 :w v :r [:b 2] :value 1}
   {:t :unsubscribe :w w :o [:o 0]}
   {:t :unsubscribe :w v :o [:o 2]}])

(deftest foreign-index-mirrors-do-not-anchor-a-completed-cycle
  (let [actions (foreign-completed-cycle-actions)
        state (check-walk! actions)]
    (is (empty? (get-in state [:worlds v :runs])))
    ;; The other world still owns its release protocol. Its value remains
    ;; readable while it has not acknowledged the foreign edge removals.
    (is (= 1 (get-in state [:worlds w :entities :a :result])))
    (is (seq (get-in state [:worlds w :releasing])))
    (let [final (check-walk! (into actions [{:t :queued :w w}
                                            {:t :queued :w w}
                                            {:t :queued :w w}
                                            {:t :queued :w v}
                                            {:t :queued :w v}]))]
      (is (nil? (get-in final [:worlds w :entities :a])))
      (is (nil? (get-in final [:worlds v :entities :b])))
      (is (every? empty? (map :runs (vals (:worlds final)))))
      (is (every? empty? (map :obligations (vals (:worlds final)))))
      (is (every? empty? (map :releasing (vals (:worlds final)))))
      (is (not-any? #(= :body-entry (:event %)) (:events final))))))

(defn foreign-owned-source-actions []
  (let [actions (foreign-completed-cycle-actions)]
    (into (conj (subvec actions 0 12)
                {:t :t02 :w w :e :owned-source :r [:a 2] :value 1})
          (subvec actions 12))))

(deftest normalization-oracle-requires-the-owning-worlds-next-publication
  (let [before (reduce m/step (m/init-state) (foreign-owned-source-actions))
        action {:t :t02 :w w :e :unrelated :value 7}
        mutant (with-redefs [m/rule-l (fn [s _] s)] (m/step before action))
        correct (m/step before action)
        foreign-action (assoc action :w v)
        foreign-publication (m/step before foreign-action)]
    (is (empty? (inv/check mutant)))
    (is (some? (m/ent mutant w :owned-source)))
    (is (some #(= :TL20 (:id %))
              (inv/edge-check {:before before :action action :after mutant})))
    (is (nil? (m/ent correct w :owned-source)))
    (is (empty? (inv/edge-check {:before before :action action :after correct})))
    (is (some? (m/ent foreign-publication w :owned-source)))
    (is (empty? (inv/edge-check {:before before :action foreign-action :after foreign-publication})))))

(deftest foreign-root-loss-preserves-only-the-pending-local-cleanup-extent
  (let [actions (foreign-owned-source-actions)
        state (check-walk! actions)]
    (is (= #{:extent} (m/reasons state w :owned-source)))
    (is (not (m/execution-live? state w :owned-source)))
    (let [final (check-walk! (into actions
                                   [{:t :queued :w w} {:t :queued :w w} {:t :queued :w w}
                                    {:t :queued :w v} {:t :queued :w v}]))]
      (is (nil? (get-in final [:worlds w :entities :owned-source]))))
    ;; GC has no authority to publish execution or foreign protocol changes.
    (let [prefix (into [{:t :t01 :w w :e :a :tok :ha}] actions)
          before (check-walk! (conj prefix {:t :t16 :tok :ha}))
          after (m/step before {:t :t17 :w w :e :a :tok :ha})]
      (is (= (m/non-idle-projection before) (m/non-idle-projection after)))
      (is (= #{:extent} (m/reasons after w :owned-source)))
      (is (empty? (inv/check after))))))

(deftest explicit-cache-release-first-publishes-pending-local-cleanup
  (let [actions (into [{:t :t01 :w w :e :a :tok :ha}] (foreign-owned-source-actions))
        final (check-walk! (conj actions {:t :t18 :w w}))]
    (is (nil? (get-in final [:worlds w :entities :owned-source])))
    (is (empty? (get-in final [:worlds w :runs])))
    (is (empty? (get-in final [:worlds w :entities :a :tokens])))))

(defn foreign-owned-ancestor-actions []
  [{:t :t01 :w w :e :p :tok :hp}
   {:t :t04 :w w :e :p :tok :hp :mode :callback}
   {:t :t01 :w w :e :a :r [:p 1] :tok :ha}
   {:t :t05 :w w :r [:p 1] :kind :await-reactive :debtor [:entity w :a] :tok :ha}
   {:t :t07 :w w :r [:a 1] :value 1}
   {:t :t08 :w w :e :a :value 1}
   {:t :t07 :w w :r [:p 1] :value 1}
   {:t :t08 :w w :e :p :value 1}
   {:t :t19 :w w :v v :k :k :scope [:root w] :systems #{}}
   {:t :t04 :w v :e :b :mode :callback}
   {:t :t05 :w v :r [:b 1] :kind :await-reactive :debtor [:entity w :a]}
   {:t :t06 :w v :o [:o 3] :value 1}
   {:t :t07 :w v :r [:b 1] :value 1}
   {:t :t08 :w v :e :b :value 1}
   {:t :unsubscribe :w w :o [:o 0]}
   {:t :unsubscribe :w v :o [:o 2]}])

(deftest pending-storage-extent-also-protects-completed-ancestors
  (let [actions (foreign-owned-ancestor-actions)
        pending (check-walk! actions)
        final (check-walk! (into actions [{:t :t16 :tok :hp}
                                          {:t :t17 :w w :e :p :tok :hp}]))]
    (is (= #{:extent} (m/reasons pending w :p)))
    (is (not (m/execution-live? pending w :p)))
    (is (= (m/non-idle-projection pending) (m/non-idle-projection final)))
    (is (= #{:extent} (m/reasons final w :p)))
    (let [released (m/step final {:t :t18 :w w})]
      (is (empty? (get-in released [:worlds w :runs])))
      (is (empty? (inv/check released))))))
