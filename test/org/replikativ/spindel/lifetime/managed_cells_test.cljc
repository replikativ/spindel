(ns org.replikativ.spindel.lifetime.managed-cells-test
  (:require [clojure.walk :as walk]
            #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.engine.kernel :as kernel]))

(def w [:w 0])
(def v [:w 1])
(def r [:owner 1])
(def receipt [w :cell :allocation-1])
(def notify {:t :source-unreachable :w w :e :cell :allocation :allocation-1})
(def reap (assoc notify :t :reap-source))

(defn fixture []
  (reduce m/step (m/init-state)
          [{:t :t04 :w w :e :owner :mode :callback}
           {:t :t02 :w w :scope r :e :cell :kind :atom :allocation :allocation-1 :value 42}]))

(defn- semantic-view [state]
  ;; Search-use counters are model instrumentation, not kernel state. Kernel
  ;; cancellation values use the implementation namespace, as in kernel-test.
  (walk/postwalk
   (fn [x]
     (if (and (keyword? x) (#{"cancelled" "released"} (name x))
              (#{"org.replikativ.spindel.engine.kernel"
                 "org.replikativ.spindel.lifetime.model"} (namespace x)))
       (keyword "error" (name x)) x))
   (dissoc state :uses)))

(defn pair-step [state action]
  (let [expected (m/attempt state action)]
    (doseq [cells? [false true]]
      (let [k (kernel/restore state {:cells? cells?})
            refusal (try (kernel/step! k action) nil
                         (catch #?(:clj Exception :cljs :default) ex (ex-data ex)))
            actual (kernel/snapshot k)]
        (is (= (some-> expected :refusal :error name) (some-> refusal :error name)) (pr-str action))
        (is (= (semantic-view (:state expected)) (semantic-view actual)) (pr-str action))))
    (:state expected)))

(deftest allocation-fencing-and-owner-survival
  (let [initial (fixture)
        pending (pair-step initial notify)
        gone (pair-step pending reap)]
    (is (= pending (pair-step pending notify)))
    (is (get-in pending [:env :source-gc receipt]))
    (is (nil? (m/ent gone w :cell)))
    (is (= :running (:status (m/run gone w r))))
    (is (not (contains? (:creations (m/run gone w r)) :cell)))
    (is (= gone (pair-step gone reap)))
    (let [replacement (pair-step gone {:t :t02 :w w :scope r :e :cell :kind :atom
                                       :allocation :allocation-2 :value 99})
          stale (assoc-in replacement [:env :source-gc receipt] true)
          reaped (pair-step stale reap)]
      (is (= replacement reaped))
      (is (= replacement (pair-step replacement notify)))
      (is (= 99 (:result (m/ent reaped w :cell)))))))

(deftest unannotated-cohorts-and-released-world-notifications-are-inert
  (doseq [state [(update-in (fixture) [:worlds w :entities :cell] dissoc :allocation)
                 (assoc-in (fixture) [:worlds w :entities :cell :kind] :signal)
                 (assoc-in (m/init-state) [:worlds w] {:id w :status :released})]]
    (is (= (dissoc state :events)
           (dissoc (pair-step state notify) :events)))))

(deftest ordinary-blockers-refuse-with-the-receipt-pending
  (doseq [block [(fn [s] (update-in s [:worlds w :pins] conj :cell))
                 (fn [s] (assoc-in s [:env :cell-claims receipt] #{:native-borrow}))
                 (fn [s] (assoc-in s [:worlds w :obligations :o]
                                   {:kind :track :debtor [:entity w :cell] :creditor [:host :subscriber]}))
                 (fn [s] (update-in s [:worlds w :queue] conj {:completion :cell :debtor-world w}))
                 (fn [s] (update-in s [:env :outside] conj {:w w :event {:completion :cell :debtor-world w}}))
                 (fn [s] (update-in s [:worlds w :fdeps] conj [:cell v :o]))
                 (fn [s] (update-in s [:worlds w :fdeps] conj [:bundle v #{:cell}]))]]
    (let [state (block (pair-step (fixture) notify))
          result (m/attempt state reap)]
      (is (= ::m/source-in-use (get-in result [:refusal :error])))
      (is (= state (pair-step state reap)))
      (is (get-in state [:env :source-gc receipt])))))

(defn add-child [s mode local?]
  (let [child (cond-> (m/world-row v w mode w)
                local? (assoc-in [:entities :cell]
                                 (assoc (m/ent s w :cell) :owner [:root v])))]
    (-> s (assoc-in [:worlds v] child)
        (update :known-worlds conj v) (update :registry conj v)
        (assoc-in [:lineages v] (:lineage child)))))

(deftest followers-need-backing-but-frozen-and-local-copies-are-independent
  (let [pending (pair-step (fixture) notify)
        follower (add-child pending :following false)]
    (is (= follower (pair-step follower reap)))
    (doseq [[mode local?] [[:following true] [:frozen true] [:frozen false]]]
      (let [state (add-child pending mode local?)
            child (get-in state [:worlds v])
            gone (pair-step state reap)]
        (is (nil? (m/ent gone w :cell)))
        (is (= child (get-in gone [:worlds v])))))))

(deftest foreign-obligations-block-even-with-independent-child-storage
  (let [state (-> (pair-step (fixture) notify)
                  (add-child :following true)
                  (assoc-in [:worlds v :obligations :foreign]
                            {:kind :track :debtor [:entity w :cell]
                             :creditor [:host :subscriber]}))]
    (is (= ::m/source-in-use (get-in (m/attempt state reap) [:refusal :error])))
    (is (= state (pair-step state reap)))))

(deftest cleanup-payload-survives-collection-until-physical-return
  (let [entered (reduce m/step (m/init-state {:slices? true :cps-exit? true})
                        [{:t :t04 :w w :e :owner :mode :callback}
                         {:t :slice-enter :w w :r r :th :worker}
                         {:t :t02 :w w :scope r :e :cell :kind :atom
                          :allocation :allocation-1 :value :original}])
        pending (pair-step entered notify)
        cancelled (pair-step pending {:t :t11 :w w :r r})
        n (cleanup/ticket w r)
        key [w r :cell]
        cells (get-in cancelled [:env :cleanup-cells])
        stale (pair-step cancelled reap)]
    (is (= :original (get-in cells [key :result])))
    (is (= cells (get-in stale [:env :cleanup-cells])))
    (is (= (get-in cancelled [:env :native n]) (get-in stale [:env :native n])))
    (let [exited (pair-step stale {:t :t38 :th :worker})
          claimed (pair-step exited {:t :cleanup-claim :n n :th :cleaner})
          returning (pair-step claimed {:t :cleanup-return :th :cleaner})
          done (pair-step returning {:t :t38 :th :cleaner})]
      (is (= cells (get-in returning [:env :cleanup-cells])))
      (is (empty? (get-in done [:env :cleanup-cells]))))))

(defn- checked-pair-step [before action]
  (let [{after :state :keys [refusal observation]} (m/attempt before action)
        state-errors (inv/check after)
        edge-errors (inv/edge-check {:before before :action action :after after
                                     :refusal refusal :observation observation})]
    (is (empty? state-errors) (pr-str [action state-errors]))
    (is (empty? edge-errors) (pr-str [action edge-errors]))
    (pair-step before action)))

(deftest valid-managed-collection-trace-satisfies-independent-invariants
  (let [gone (reduce checked-pair-step (m/init-state)
                     [{:t :t04 :w w :e :owner :mode :callback}
                      {:t :t02 :w w :scope r :e :cell :kind :atom
                       :allocation :allocation-1 :value 42}
                      {:t :t14 :w w :e :cell :pin? true}
                      notify notify
                      ;; This blocker is established by a real transition.
                      reap
                      {:t :t14 :w w :e :cell :pin? false}
                      reap reap
                      {:t :t02 :w w :scope r :e :cell :kind :atom
                       :allocation :allocation-2 :value 99}
                      notify reap
                      (assoc notify :allocation :allocation-2)
                      (assoc reap :allocation :allocation-2)])]
    (is (nil? (m/ent gone w :cell)))
    (is (= :running (:status (m/run gone w r))))))

(deftest valid-cleanup-and-stale-collection-trace-satisfies-independent-invariants
  (let [n (cleanup/ticket w r)
        done (reduce checked-pair-step (m/init-state {:slices? true :cps-exit? true})
                     [{:t :t04 :w w :e :owner :mode :callback}
                      {:t :slice-enter :w w :r r :th :worker}
                      {:t :t02 :w w :scope r :e :cell :kind :atom
                       :allocation :allocation-1 :value :original}
                      notify
                      {:t :t11 :w w :r r}
                      ;; Cancellation removed ordinary storage, but retained
                      ;; cleanup payloads still belong to the physical exit.
                      notify reap
                      {:t :t38 :th :worker}
                      {:t :cleanup-claim :n n :th :cleaner}
                      {:t :cleanup-return :th :cleaner}
                      {:t :t38 :th :cleaner}])]
    (is (empty? (get-in done [:env :cleanup-cells])))
    (is (nil? (get-in done [:env :native n])))))
