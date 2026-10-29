(ns org.replikativ.spindel.engine.kernel-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.kernel :as kernel]
            [org.replikativ.spindel.lifetime.model :as model]))

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
  (select-keys state [:worlds :env :serial :events]))

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

(deftest bounded-obligation-walks
  (let [initial (model/init-state {:worlds 1 :world-ids 1 :spins 1 :signals 1 :atoms 1
                                   :scopes 0 :handles 0 :cuts 0 :generations 1
                                   :invocations 1 :host-registrations 1
                                   :filters [:local] :invoke-modes [:callback]})
        alphabet #{:t02 :t04 :t05 :t06 :unsubscribe}]
    (letfn [(walk [state trace depth]
              (if (zero? depth)
                (compare-walk! initial trace)
                (doseq [action (filter #(alphabet (:t %)) (model/enabled state))]
                  (walk (:state (model/attempt state action)) (conj trace action) (dec depth)))))]
      (walk initial [] 4))))
