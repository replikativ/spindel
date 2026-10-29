(ns org.replikativ.spindel.engine.kernel-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.kernel :as kernel]
            [org.replikativ.spindel.lifetime.model :as model]
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
   (select-keys state [:worlds :env :serial :events :generation-clock :clocks :host-delivered])))

(defn- compare-walk! [initial actions]
  (let [actual (kernel/restore initial)]
    (loop [expected initial remaining actions]
      (when-let [action (first remaining)]
        (let [{after :state refusal :refusal} (model/attempt expected action)
              actual-error (try (kernel/step! actual action) nil
                                (catch #?(:clj Exception :cljs :default) e (ex-data e)))]
          (is (= (some-> refusal :error name) (some-> actual-error :error name)) (str action))
          (is (= (view after) (view (kernel/snapshot actual))) (str action))
          (recur after (next remaining)))))))

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
