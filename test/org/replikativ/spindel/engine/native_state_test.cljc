(ns org.replikativ.spindel.engine.native-state-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.impl.owned :as owned #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]))

(deftest application-state-uses-the-public-state-protocol
  (let [rt (owned/runtime)]
    (binding [ec/*execution-context* rt]
      (is (= 2 (ec/swap-state-args! [:app :counter] (fnil + 0) 2)))
      (is (= 7 (rtp/swap-state-args! rt [:app :counter] + [2 3])))
      (is (= 7 (ec/get-state [:app :counter])))
      (is (rtp/cas-state! rt [:app :counter] 7 8))
      (is (not (rtp/cas-state! rt [:app :counter] 7 9)))
      (is (= 8 (ec/get-state [:app :counter])))
      (rtp/swap-state! rt [:app :vector] (constantly [0 1 2]))
      (is (rtp/cas-state! rt [:app :vector] (vec (range 3)) :done)))))

(deftest application-functions-run-outside-the-gate-and-retry
  (let [rt (owned/runtime) calls (atom 0)]
    (rtp/swap-state! rt [:app :counter] (constantly 0))
    (is (= 1 (rtp/swap-state! rt [:app :counter]
                              (fn [value]
                                (is #?(:clj (not (Thread/holdsLock (:gate rt))) :cljs true))
                                (when (= 1 (swap! calls inc))
                                  (rtp/swap-state! rt [:app :other] (constantly true)))
                                (inc value)))))
    (is (= 2 @calls))
    (is (true? (rtp/get-state rt [:app :other])))))

(deftest engine-state-is-read-only-through-generic-state-paths
  (let [rt (owned/runtime) before (owned/snapshot rt)]
    (doseq [path (concat [[] [:nodes :illegal] [:entities :illegal] [:runs :illegal]
                          [:obligations :illegal] [:engine/pending] [:lifetime/run]]
                         (map vector (keys before)))]
      (is (= :engine-state-read-only
             (try (rtp/swap-state! rt path (constantly :illegal)) nil
                  (catch #?(:clj Exception :cljs :default) error (:error (ex-data error))))))
      (is (= :engine-state-read-only
             (try (rtp/cas-state! rt path nil :illegal) nil
                  (catch #?(:clj Exception :cljs :default) error (:error (ex-data error)))))))
    (is (= before (owned/snapshot rt)))
    (is (= before (select-keys (rtp/get-state rt []) (keys before))))
    (is (= (:entities before) (rtp/get-state rt [:entities])))
    (is (nil? (rtp/get-state rt [:app])))))

(deftest application-failure-publishes-no-cell-change
  (let [rt (owned/runtime) failure (ex-info "application update failed" {})]
    (rtp/swap-state! rt [:app] (constantly {:counter 1}))
    (is (identical? failure (try (rtp/swap-state! rt [:app :counter] (fn [_] (throw failure))) nil
                                 (catch #?(:clj Exception :cljs :default) error error))))
    (is (= {:counter 1} (rtp/get-state rt [:app])))))

(deftest following-application-cells-shadow-locally-without-pinning-parent-history
  (let [rt (owned/runtime) ticket (owned/ticket :parked)
        spin (owned/cspin rt :spin (owned/park ticket))]
    (rtp/swap-state! rt [:app] (constantly {:counter 1 :values [1 2 3]}))
    (owned/observe! rt spin (fn [_]) #(throw %))
    (let [before (rtp/get-state rt []) child (owned/fork-parked! rt [:w 1])]
      (is (not (ec/same-world? rt child)))
      (is (identical? (rtp/get-state rt [:app]) (rtp/get-state child [:app])))
      (rtp/swap-state! child [:app :counter] inc)
      (rtp/swap-state-args! rt [:app :values] conj [4])
      (is (= {:counter 2 :values [1 2 3 4]} (rtp/get-state child [:app])))
      (is (= {:counter 1 :values [1 2 3 4]} (rtp/get-state rt [:app])))
      (is (= {:counter 1 :values [1 2 3]} (:app before))))))

(deftest a-nested-cell-write-copies-the-cell-and-keeps-its-siblings
  (let [parent (owned/runtime)]
    (rtp/swap-state! parent [:app :config] (constantly {:a 1 :b 2}))
    (let [child (owned/fork-parked! parent [:w 1])]
      (rtp/swap-state! child [:app :config :a] inc)
      (rtp/swap-state! parent [:app :config :b] inc)
      (is (= {:a 2 :b 2} (rtp/get-state child [:app :config])))
      (is (= {:a 1 :b 3} (rtp/get-state parent [:app :config]))))))

(deftest following-cell-update-retries-if-the-parent-changes-before-commit
  (let [parent (owned/runtime) calls (atom 0)]
    (rtp/swap-state! parent [:app :config] (constantly {:a 1 :b 2}))
    (let [child (owned/fork-parked! parent [:w 1])]
      (is (= 2 (rtp/swap-state! child [:app :config :a]
                                (fn [value]
                                  (when (= 1 (swap! calls inc))
                                    (rtp/swap-state! parent [:app :config :b] inc))
                                  (inc value)))))
      (is (= 2 @calls))
      (is (= {:a 2 :b 3} (rtp/get-state child [:app :config]))))))

(deftest local-map-cells-remain-consistent-if-the-parent-group-changes-shape
  (let [parent (owned/runtime)]
    (rtp/swap-state! parent [:app] (constantly {:counter 1 :sibling 3}))
    (let [child (owned/fork-parked! parent [:w 1])]
      (rtp/swap-state! child [:app :counter] inc)
      (doseq [replacement [:replaced [9 8 7] nil]]
        (rtp/swap-state! parent [:app] (constantly replacement))
        (is (= 2 (rtp/get-state child [:app :counter])))
        (is (nil? (rtp/get-state child [:app :sibling])))
        (is (nil? (rtp/get-state child [:app 1])))
        (is (= {:counter 2} (rtp/get-state child [:app])))
        (is (= {:counter 2} (:app (rtp/get-state child []))))))))

(deftest vector-groups-are-copied-whole-before-nested-edits
  (let [parent (owned/runtime)]
    (rtp/swap-state! parent [:app] (constantly [0 1 2]))
    (let [child (owned/fork-parked! parent [:w 1])]
      (is (= 2 (rtp/swap-state! child [:app 1] inc)))
      (rtp/swap-state! parent [:app 0] inc)
      (is (= [0 2 2] (rtp/get-state child [:app])))
      (is (= 2 (rtp/get-state child [:app 1])))
      (is (= [1 1 2] (rtp/get-state parent [:app]))))))

(deftest explicit-application-contexts-override-the-active-native-slice
  (let [parent (owned/runtime) child (owned/fork-parked! parent [:w 1]) values (atom nil)]
    (rtp/swap-state! parent [:app :name] (constantly :parent))
    (rtp/swap-state! child [:app :name] (constantly :child))
    (owned/observe!
     parent (owned/cspin parent :probe
                         [(rtp/get-state child [:app :name])
                          (binding [ec/*execution-context* child] (ec/get-state [:app :name]))
                          (rtp/swap-state! child [:app :name] (constantly :changed))])
     #(reset! values %) #(throw %))
    (is (= [:child :child :changed] @values))
    (is (= :parent (rtp/get-state parent [:app :name])))
    (is (= :changed (rtp/get-state child [:app :name])))))

(deftype ReentrantEqual [f]
  #?@(:clj [Object (equals [_ _] (f) true) (hashCode [_] 0)]
      :cljs [IEquiv (-equiv [_ _] (f) true) IHash (-hash [_] 0)]))

(deftest application-cas-preserves-writes-performed-by-user-equality
  (let [rt (owned/runtime) held? (atom nil) wrote? (atom false)]
    (rtp/swap-state! rt [:app :target] (constantly :old))
    (is (rtp/cas-state!
         rt [:app :target]
         (ReentrantEqual. (fn []
                            (reset! held? #?(:clj (Thread/holdsLock (:gate rt)) :cljs false))
                            (when (compare-and-set! wrote? false true)
                              (rtp/swap-state! rt [:app :other] (constantly :retained)))))
         :new))
    (is (false? @held?))
    (is (= :retained (rtp/get-state rt [:app :other])))
    (is (= :new (rtp/get-state rt [:app :target])))))

(deftype ObservedKey [observe]
  #?@(:clj [Object (hashCode [_] (observe) 7) (equals [this other] (identical? this other))]
      :cljs [IHash (-hash [_] (observe) 7) IEquiv (-equiv [this other] (identical? this other))]))

(deftest application-key-hashing-never-runs-under-the-engine-gate
  (let [rt (owned/runtime) held? (atom false)
        key (ObservedKey. (fn [] #?(:clj (when (Thread/holdsLock (:gate rt)) (reset! held? true)) :cljs nil)))]
    (rtp/swap-state! rt [:app key] (constantly 1))
    (is (= 1 (rtp/get-state rt [:app key])))
    (is (rtp/cas-state! rt [:app key] 1 2))
    (is (= 2 (get-in (rtp/get-state rt []) [:app key])))
    (is (false? @held?))))

#?(:clj
   (deftest concurrent-application-updates-do-not-lose-writes
     (let [rt (owned/runtime) start (promise)]
       (rtp/swap-state! rt [:app :counter] (constantly 0))
       (let [workers (doall (repeatedly 4 #(future @start
                                                   (dotimes [_ 100]
                                                     (rtp/swap-state! rt [:app :counter] inc)))))]
         (deliver start true)
         (doseq [worker workers] @worker))
       (is (= 400 (rtp/get-state rt [:app :counter]))))))
