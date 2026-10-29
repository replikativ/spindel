(ns org.replikativ.spindel.engine.kernel-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.kernel :as kernel]
            [org.replikativ.spindel.lifetime.model :as model]
            [org.replikativ.spindel.lifetime.first-delivery-test :as handoff]
            [org.replikativ.spindel.lifetime.rooted-liveness-test :as rooted]
            [clojure.walk :as walk]))

(def w [:w 0])
(def parent [:spin 0])
(def child [:spin 1])
(def signal [:signal 0])

(defn- fixture []
  (reduce model/step (model/init-state)
          [{:t :t04 :w w :e parent :mode :callback}
           {:t :t04 :w w :e child :mode :callback}
           {:t :t02 :w w :e signal :value 1}]))

(defn- view [state]
  (walk/postwalk
   (fn [x]
     (if (and (keyword? x) (#{"cancelled" "released"} (name x))
              (#{"org.replikativ.spindel.engine.kernel"
                 "org.replikativ.spindel.lifetime.model"} (namespace x)))
       (keyword "error" (name x)) x))
   (select-keys state [:worlds :env :serial :events :generation-clock :clocks :host-delivered
                       :registry :caps :durable :known-worlds :lineages :cuts :records])))

(defn- compare-walk! [initial actions]
  (doseq [[cells? seal?] [[false true] [true true] [true false]]]
    (let [actual (kernel/restore initial {:cells? cells?})]
      (loop [expected initial remaining actions]
        (if-let [action (first remaining)]
          (let [{after :state refusal :refusal} (model/attempt expected action)
                actual-error (try (kernel/step! actual action) nil
                                  (catch #?(:clj Exception :cljs :default) e
                                    (merge {:error ::unexpected-exception :message (ex-message e)} (ex-data e))))]
            (is (= (some-> refusal :error name) (some-> actual-error :error name)) (str action))
            (when seal?
              (is (= (view after) (view (kernel/snapshot actual))) (str action)))
            (recur after (next remaining)))
          (when-not seal?
            (is (= (view expected) (view (kernel/snapshot actual))) (str actions))))))))

(deftest completed-island-refines-rooted-normalization
  (compare-walk! (model/init-state)
                 (into (rooted/completed-pair-actions)
                       [{:t :unsubscribe :w w :o [:o 0]}
                        {:t :t16 :tok :hp} {:t :t17 :w w :e :parent :tok :hp}
                        {:t :t16 :tok :hc} {:t :t17 :w w :e :child :tok :hc}])))

(deftest queued-host-admission-refines-retention
  (compare-walk! (model/init-state) (conj (rooted/queued-host-actions) {:t :queued :w w})))

(deftest foreign-completed-cycle-refines-local-release-acknowledgements
  (compare-walk! (model/init-state)
                 (into (rooted/foreign-completed-cycle-actions)
                       [{:t :queued :w w} {:t :queued :w w} {:t :queued :w w}
                        {:t :queued :w [:w 1]} {:t :queued :w [:w 1]}])))

(deftest source-bursts-refine-latest-notification-storage
  (compare-walk! (model/init-state)
                 (into [{:t :t02 :w w :e signal :value 0}]
                       (map #(hash-map :t :signal-write :w w :e signal :value %) (range 1 33)))))

(deftest idle-reactive-caches-refine-validation-loss
  (doseq [source-kind [:signal :atom] transitive? [false true] cancel-child? [false true]]
    (compare-walk! (model/init-state) (handoff/idle-reactive-cache-actions transitive? cancel-child? source-kind))))

(deftest parked-creditor-refines-validation-loss-through-completion
  (compare-walk! (model/init-state) (handoff/parked-creditor-validation-actions)))

(deftest inherited-creditor-refines-validation-loss-before-activation
  (compare-walk! (model/init-state) (handoff/inherited-creditor-validation-actions)))

(deftest dirty-await-refines-fresh-owned-run
  (doseq [kind [:await-once :await-reactive]]
    (compare-walk! (model/init-state) (handoff/dirty-await-actions kind))))

(deftest await-refines-joining-active-refresh
  (doseq [kind [:await-once :await-reactive]]
    (compare-walk! (model/init-state) (handoff/refreshing-await-actions kind))))

(deftest obligation-kind-walks
  (doseq [[kind debtor] [[:track [:entity w signal]]
                         [:await-once [:entity w child]]
                         [:await-reactive [:entity w child]]
                         [:external [:host :external]]
                         [:timer [:host :executor]]]]
    (testing (name kind)
      (compare-walk!
       (fixture)
       (cond-> [{:t :t05 :w w :r [parent 1] :kind kind :debtor debtor}]
         (= kind :track) (conj {:t :unsubscribe :w w :o [:o 2]})
         (not= kind :track) (conj {:t :t06 :w w :o [:o 2] :value 42}
                                ;; Duplicates cannot resume a consumed slot.
                                  {:t :t06 :w w :o [:o 2] :value 43})
         (= kind :await-reactive) (conj {:t :unsubscribe :w w :o [:o 2]}))))))

(deftest create-invoke-and-cold-await
  (compare-walk!
   (model/init-state)
   [{:t :t12 :w w :scope [:scope 0] :parent [:root w]}
    {:t :t02 :w w :scope [:scope 0] :e signal :value 1}
    {:t :t04 :w w :e parent :mode :callback}
    {:t :t04 :w w :e parent :mode :callback}
    {:t :t05 :w w :r [parent 1] :kind :await-once :debtor [:entity w child]}
    {:t :t06 :w w :o [:o 2] :value 42}]))

(deftest completion-and-idle-reclamation
  (compare-walk!
   (model/init-state)
   [{:t :t04 :w w :e parent :mode :callback}
    {:t :t07 :w w :r [parent 1] :value 42}
    {:t :t08 :w w :e parent :value 42}
    {:t :t07 :w w :r [parent 1] :value :late}
    {:t :t11 :w w :r [parent 1]}]))

(deftest cancellation-releases-owned-child
  (compare-walk!
   (model/init-state)
   [{:t :t04 :w w :e parent :mode :callback}
    {:t :t05 :w w :r [parent 1] :kind :await-once :debtor [:entity w child]}
    {:t :t11 :w w :r [parent 1]}
    {:t :t07 :w w :r [child 1] :value :late}]))

(deftest close-scope-cascades-before-return
  (compare-walk!
   (model/init-state)
   [{:t :t12 :w w :scope [:scope 0] :parent [:root w]}
    {:t :t02 :w w :e signal :scope [:scope 0] :value 1}
    {:t :t04 :w w :e parent :scope [:scope 0] :mode :callback}
    {:t :t13 :w w :scope [:scope 0]}
    {:t :t13 :w w :scope [:scope 0]}]))

(deftest reactive-successor-fences-old-completion
  (compare-walk!
   (model/init-state)
   [{:t :t02 :w w :e signal :value 1}
    {:t :t04 :w w :e parent :mode :callback}
    {:t :t05 :w w :r [parent 1] :kind :track :debtor [:entity w signal]}
    {:t :t07 :w w :r [parent 1] :value 10}
    {:t :t08 :w w :e parent :value 10}
    {:t :signal-write :w w :e signal :value 2}
    {:t :t08 :w w :e signal :value 2}
    {:t :t05 :w w :r [parent 2] :kind :track :debtor [:entity w signal]}
    {:t :t07 :w w :r [parent 1] :value :late}
    {:t :t07 :w w :r [parent 2] :value 20}
    {:t :t08 :w w :e parent :value 20}]))

(deftest successor-adopts-child-and-owned-source
  (compare-walk!
   (model/init-state)
   [{:t :t04 :w w :e parent :mode :callback}
    {:t :t02 :w w :e signal :r [parent 1] :value 1}
    {:t :t05 :w w :r [parent 1] :kind :track :debtor [:entity w signal]}
    {:t :t01 :w w :r [parent 1] :e child :order 1}
    {:t :t04 :w w :r [parent 1] :e child :mode :callback}
    {:t :t09 :w w :e parent :cause :track :order 0}
    {:t :t01 :w w :r [parent 2] :e child :order 1}
    {:t :t07 :w w :r [parent 2] :value 2}
    {:t :t11 :w w :r [parent 2]}]))

(deftest cancellation-keeps-only-physical-evidence
  (compare-walk!
   (model/init-state)
   [{:t :t04 :w w :e parent :mode :callback}
    {:t :slice-enter :w w :r [parent 1] :th :host}
    {:t :t12 :w w :scope [:scope 0] :parent [parent 1]}
    {:t :t02 :w w :e signal :scope [:scope 0] :value 1}
    {:t :t11 :w w :r [parent 1]}
    {:t :t01 :th :host :e child}
    {:t :signal-write :th :host :e signal :value :late}
    {:t :t07 :th :host :r [parent 1] :value :late}
    {:t :t38 :th :host}]))

(deftest native-cancellation-waits-for-physical-exit
  (compare-walk!
   (model/init-state)
   [{:t :t04 :w w :e parent :mode :callback}
    {:t :t05 :w w :r [parent 1] :kind :external :debtor [:host :native]}
    {:t :t11 :w w :r [parent 1]}
    {:t :native-progress :n [:cancel [:o 1]] :state :joined}
    {:t :waiter-unregister :token [:cancel [:o 1]]}]))

(deftest reused-await-target-is-adopted
  (compare-walk! (model/init-state) (handoff/cold-child-handoff-actions)))

(deftest prefix-source-survives-successor-completion
  (compare-walk!
   (model/init-state)
   [{:t :t04 :w w :e parent :mode :callback}
    {:t :t02 :w w :e signal :r [parent 1] :order 0 :value 1}
    {:t :t05 :w w :r [parent 1] :kind :track :debtor [:entity w signal] :order 1}
    {:t :t07 :w w :r [parent 1] :value 1}
    {:t :t08 :w w :e parent :value 1}
    {:t :signal-write :w w :e signal :value 2}
    {:t :t08 :w w :e signal :value 2}
    {:t :t05 :w w :r [parent 2] :kind :track :debtor [:entity w signal] :order 1}
    {:t :t07 :w w :r [parent 2] :value 2}
    {:t :signal-write :w w :e signal :value 3}]))

(deftest reentry-removes-the-predecessors-timer-in-the-same-transition
  (compare-walk!
   (model/init-state)
   [{:t :t04 :w w :e parent :mode :callback}
    {:t :t05 :w w :r [parent 1] :kind :timer :debtor [:host :executor]}
    {:t :t09 :w w :e parent :cause :rerun!}
    {:t :t07 :w w :r [parent 2] :value 1}
    {:t :t08 :w w :e parent :value 1}]))

(deftest ready-await-refines-registration-and-claim
  (let [initial (model/step (fixture) {:t :t07 :w w :r [child 1] :value 42})
        action {:t :t05 :w w :r [parent 1] :kind :await-reactive :debtor [:entity w child]}
        expected (-> initial (model/step action)
                     (model/step {:t :t06 :w w :o [:o 2] :value 42}))]
    (doseq [options [{} {:cells? true}]]
      (let [actual (kernel/restore initial options)
            result (kernel/step! actual (assoc action :t :await))]
        (is (= (view expected) (view (kernel/snapshot actual))))
        (is (= {:o [:o 2] :value 42 :inline? true} (:result result)))
        (is (empty? (:commands result)))))))

(deftest foreign-obligation-admission-and-release
  (let [v [:w 1]
        initial (reduce model/step (fixture)
                        [{:t :t19 :w w :v v :k [:k 0]
                          :scope [:root w] :systems #{}}
                         {:t :t04 :w v :e [:spin 2] :mode :callback}])]
    (compare-walk!
     initial
     [{:t :t05 :w v :r [[:spin 2] 1] :kind :track :debtor [:entity w signal]}
      {:t :unsubscribe :w v :o [:o 3]}])))

(deftest refused-registration-restores-store
  (let [initial (fixture)
        actual (kernel/restore initial)
        before (kernel/snapshot actual)]
    (is (thrown? #?(:clj Exception :cljs js/Error)
                 (kernel/step! actual {:t :t05 :w w :r [parent 1] :kind :track
                                       :debtor [:entity w :absent]})))
    (is (= before (kernel/snapshot actual)))))

(defn- bounded-walks! [initial alphabet depth]
  (letfn [(walk [state trace depth]
            (if (zero? depth)
              (compare-walk! initial trace)
              (doseq [action (filter #(alphabet (:t %)) (model/enabled state))]
                (walk (:state (model/attempt state action)) (conj trace action) (dec depth)))))]
    (walk initial [] depth)))

(deftest bounded-obligation-walks
  (let [initial (model/init-state {:worlds 1 :world-ids 1 :spins 1 :signals 1 :atoms 1
                                   :scopes 0 :handles 0 :cuts 0 :generations 1
                                   :invocations 1 :host-registrations 1
                                   :filters [:local] :invoke-modes [:callback]})
        alphabet #{:t02 :t04 :t05 :t06 :unsubscribe}]
    (bounded-walks! initial alphabet 4)))

(deftest bounded-lifecycle-walks
  (let [initial (model/init-state {:worlds 1 :world-ids 1 :spins 1 :signals 0 :atoms 0
                                   :scopes 0 :handles 0 :cuts 0 :generations 2
                                   :invocations 2 :host-registrations 2
                                   :filters [:local] :invoke-modes [:callback]})]
    (bounded-walks! initial #{:t04 :t07 :t09 :t10 :t11 :t15} 5)))

(deftest handle-collection-and-idle-release
  (let [tok [:tok 0]
        fresh [:tok 1]
        setup [{:t :t01 :w w :e parent :tok tok}
               {:t :t04 :w w :e parent :tok tok :mode :callback}
               {:t :t07 :w w :r [parent 1] :value 42}
               {:t :t08 :w w :e parent :value 42}]]
    (testing "delayed and duplicate collection notifications"
      (compare-walk! (model/init-state)
                     (into setup [{:t :t16 :tok tok}
                                  {:t :t17 :w w :e parent :tok tok}
                                  {:t :t17 :w w :e parent :tok tok}
                                  {:t :t01 :w w :e parent :tok fresh}
                                  {:t :t04 :w w :e parent :tok fresh :mode :callback}
                                  {:t :t17 :w w :e parent :tok tok}])))
    (testing "explicit release poisons held tokens without resetting generations"
      (compare-walk! (model/init-state)
                     (into setup [{:t :t18 :w w}
                                  {:t :t04 :w w :e parent :tok tok :mode :callback}
                                  {:t :t01 :w w :e parent :tok fresh}
                                  {:t :t04 :w w :e parent :tok fresh :mode :callback}
                                  {:t :t07 :w w :r [parent 1] :value :late}
                                  {:t :t07 :w w :r [parent 2] :value 43}
                                  {:t :t08 :w w :e parent :value 43}])))))

(deftest collection-does-not-cancel-wanted-work
  (compare-walk!
   (model/init-state)
   [{:t :t01 :w w :e parent :tok [:tok 0]}
    {:t :t04 :w w :e parent :tok [:tok 0] :mode :callback}
    {:t :t18 :w w}
    {:t :t16 :tok [:tok 0]}
    {:t :t17 :w w :e parent :tok [:tok 0]}
    {:t :t07 :w w :r [parent 1] :value 42}
    {:t :t08 :w w :e parent :value 42}]))

(deftest prefix-scope-survives-successor-completion
  (compare-walk! (model/init-state) (handoff/prefix-scope-actions)))

(deftest prefix-cache-survives-successor-completion
  (compare-walk! (model/init-state) (handoff/prefix-cache-actions)))

(deftest following-fork-and-inherited-activation
  (let [v [:w 1]]
    (compare-walk!
     (model/init-state)
     [{:t :t02 :w w :e signal :value 1}
      {:t :t01 :w w :e parent :tok [:tok 0]}
      {:t :t04 :w w :e parent :tok [:tok 0] :mode :callback}
      {:t :t05 :w w :r [parent 1] :kind :track :debtor [:entity w signal]}
      {:t :t05 :w w :r [parent 1] :kind :await-once :debtor [:host :outside]}
      {:t :t19 :w w :v v :k [:k 0] :scope [:root w] :systems #{}}
      {:t :t06 :w v :o [:o 2] :value 42}
      {:t :t07 :w v :r [parent 1] :value 42}
      {:t :t08 :w v :e parent :value 42}
      {:t :unsubscribe :w v :o [:o 1]}
      {:t :t36 :w w}])))

(deftest following-fork-preserves-owned-scopes
  (let [v [:w 1] scope [:scope 0]]
    (compare-walk!
     (model/init-state)
     [{:t :t04 :w w :e parent :mode :callback}
      {:t :t12 :w w :scope scope :parent [parent 1]}
      {:t :t02 :w w :scope scope :e signal :value 1}
      {:t :t05 :w w :r [parent 1] :kind :external :debtor [:host :outside]}
      {:t :t19 :w w :v v :k [:k 0] :scope [:root w] :systems #{:a}}
      {:t :t06 :w v :o [:o 1] :value 42}
      {:t :t13 :w v :scope scope}
      {:t :t07 :w v :r [parent 1] :value 42}
      {:t :t08 :w v :e parent :value 42}])))

(deftest foreign-cold-request-and-delayed-cleanup
  (let [v [:w 1]]
    (compare-walk!
     (model/init-state)
     [{:t :t19 :w w :v v :k [:k 0] :scope [:root w] :systems #{}}
      {:t :t04 :w v :e parent :mode :callback}
      {:t :t05 :w v :r [parent 1] :kind :await-once :debtor [:entity w child]}
      {:t :t37 :w w}
      {:t :t07 :w w :r [child 1] :value 42}
      {:t :t08 :w v :e child :debtor-world w :value 42}
      {:t :t36 :w w}
      {:t :t06 :w v :o [:o 1] :value :duplicate}])))

(deftest inherited-run-is-retired-before-a-local-invocation
  (let [v [:w 1]]
    (compare-walk!
     (model/init-state)
     [{:t :t04 :w w :e parent :mode :callback}
      {:t :t05 :w w :r [parent 1] :kind :await-once :debtor [:host :outside]}
      {:t :t19 :w w :v v :k [:k 0] :scope [:root w] :systems #{}}
      {:t :t04 :w v :e parent :mode :callback}
      {:t :t06 :w v :o [:o 1] :value :late}
      {:t :t07 :w v :r [parent 2] :value 42}
      {:t :queued :w v}])))

(deftest foreign-callback-registers-in-the-debtor-world
  (let [v [:w 1]]
    (compare-walk!
     (model/init-state)
     [{:t :t04 :w w :e child :mode :callback}
      {:t :t19 :w w :v v :k [:k 0] :scope [:root w] :systems #{}}
      {:t :t04 :w v :e child :mode :callback}
      {:t :queued :w w}
      {:t :t07 :w w :r [child 1] :value 42}
      {:t :queued :w w}
      {:t :t04 :w v :e child :mode :callback}
      {:t :queued :w w}])))

(deftest debtor-cancellation-retires-inherited-bundle-members
  (let [v [:w 1]]
    (compare-walk!
     (model/init-state)
     [{:t :t04 :w w :e parent :mode :callback}
      {:t :t05 :w w :r [parent 1] :kind :await-reactive :debtor [:entity w child]}
      {:t :t19 :w w :v v :k [:k 0] :scope [:root w] :systems #{}}
      {:t :t11 :w w :r [child 1]}
      {:t :queued :w v}
      {:t :t07 :w v :r [parent 1] :value 42}
      {:t :queued :w v}])))

(deftest predecessor-adoption-survives-retired-intermediates
  (compare-walk! (model/init-state) (handoff/burst-child-handoff-actions))
  (compare-walk! (model/init-state) (handoff/retired-creator-adoption-actions)))

(deftest fresh-run-allocation-evidence-refines-the-model
  (compare-walk! (model/init-state) (handoff/fresh-run-allocation-actions))
  (doseq [evidence [[] nil [42] [[w parent 0]] [[w parent 1.5]] [[w :wrong 10]]
                    [[[:w 1] parent 10]] [[w parent 10] [w parent 11]]]]
    (compare-walk! (model/init-state)
                   [{:t :t04 :w w :e parent :mode :callback :fresh-runs evidence}]))
  (compare-walk! (model/init-state)
                 [{:t :t04 :w w :e parent :mode :callback :fresh-runs [[w parent 10]]}
                  {:t :t09 :w w :e parent :fresh-runs [[w parent 10]]}]))

(deftest foreign-owned-cleanup-extent-refines-world-local-publication
  (doseq [tail [[{:t :queued :w w} {:t :queued :w w} {:t :queued :w w}
                 {:t :queued :w [:w 1]} {:t :queued :w [:w 1]}]
                [{:t :t16 :tok :ha} {:t :t17 :w w :e :a :tok :ha}]
                [{:t :t18 :w w}]]]
    (compare-walk! (model/init-state)
                   (into (into [{:t :t01 :w w :e :a :tok :ha}]
                               (rooted/foreign-owned-source-actions)) tail))))

(deftest foreign-owned-ancestor-refines-gc-only-storage-retention
  (compare-walk! (model/init-state)
                 (into (rooted/foreign-owned-ancestor-actions)
                       [{:t :t16 :tok :hp} {:t :t17 :w w :e :p :tok :hp}
                        {:t :t18 :w w}])))
