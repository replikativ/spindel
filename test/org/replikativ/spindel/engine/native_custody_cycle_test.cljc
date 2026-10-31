(ns org.replikativ.spindel.engine.native-custody-cycle-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.lifecycle :as lifecycle]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]))

(defn- ignore-result [_])
(defn- world-id [rt] (let [state (c/snapshot rt)] (or (:id state) (second (:root state)))))
(defn- publish [rt owner id]
  (rtp/fork-owned-world! rt {:world-id id :owner owner :systems #{} :mode :following}))
(defn- live-cap-id [rt child]
  (first (for [[id row] (get-in (c/snapshot rt) [:global :caps])
               :when (and (= (world-id child) (:world row)) (= :open (:disposition row)))] id)))

(defn- cycle-with-finalizer [try-self-wait?]
  (let [rt (c/runtime {:audit? true :cps-exit? true}) root (lifetime/root-scope rt)
        {b :context b-cap :capability} (publish rt root [:w 1])
        b-scope (lifetime/open-scope! b :holds-c)
        {target-c :context} (publish b b-scope [:w 2])
        c-scope (lifetime/open-scope! target-c :holds-b)
        moved (rtp/transfer-owned-world! rt b-cap root target-c c-scope {:operation-id :cycle-move})
        b-id (live-cap-id rt b) c-id (live-cap-id rt target-c)
        b-world (world-id b) c-world (world-id target-c)
        callback (atom nil) c-completion (atom nil)
        delivered (atom []) late-delivered (atom []) errors (atom []) task-errors (atom [])
        trace (atom []) refused (atom nil) unchanged? (atom nil) self-notifications (atom [])
        task (c/cspin b :busy-b
                      (let [cell (c/signal b :cleanup-cell 41)]
                        (try
                          (c/park (c/ticket :body))
                          (finally
                            (swap! trace conj :finally-entered)
                            (c/await-finalization (fn [resolve _] (reset! callback resolve)))
                            ;; Resume on B's real cleanup frame. C already owes
                            ;; B, so observing C here would wait on this frame.
                            (when try-self-wait?
                              (let [before (c/snapshot-family rt)
                                    error (try
                                            (lifecycle/observe! @c-completion
                                                                #(swap! self-notifications conj [:ok %])
                                                                #(swap! self-notifications conj [:error %]))
                                            nil
                                            (catch #?(:clj Exception :cljs :default) error error))]
                                (reset! refused error)
                                (reset! unchanged? (= before (c/snapshot-family rt)))))
                            (c/set-signal! b cell 42)
                            (swap! trace conj [:finally-returning (c/read-signal b cell) (empty? @delivered)])))))]
    (is (some? moved))
    (is (= [:execution-owner c-world :scope
            (first (remove #{[:root c-world]} (keys (:scopes (c/snapshot target-c)))))]
           (get-in (c/snapshot rt) [:global :caps b-id :holder])))
    (binding [ec/*execution-context* b]
      (c/observe! b task ignore-result #(swap! task-errors conj %)))
    ;; B's Scope claims C; terminal C then closes its Scope and claims B.
    ;; C has no public receipt yet. B cannot finish while its finally is parked.
    (lifetime/close-scope! b b-scope)
    (is (= [:finally-entered] @trace))
    (is (ifn? @callback))
    (is (= :sealed (:status (c/snapshot b))))
    (is (= :released (:status (c/snapshot target-c))))
    (is (= :sealed (get-in (c/snapshot rt) [:global :caps b-id :disposition])))
    (is (= :discarded (get-in (c/snapshot rt) [:global :caps c-id :disposition])))
    (is (false? (c/join-ready? b [:root b-world])))
    (is (true? (rtp/execution-owner-joined? b b-scope)))
    (let [debts (:cleanup-targets (c/snapshot rt))]
      (is (= #{b-world c-world} (set (keys debts))))
      (is (= #{c-world} (set (map :target-world (vals (get debts b-world))))))
      (is (= #{b-world} (set (map :target-world (vals (get debts c-world)))))))
    (reset! c-completion (rtp/request-world-release! target-c :observe-cycle))
    (is (satisfies? rtp/PWorldRelease @c-completion))
    (lifecycle/observe! @c-completion #(swap! delivered conj %) #(swap! errors conj %))
    (is (empty? @delivered))
    (is (= :releasing (get-in (c/snapshot target-c) [:release :phase])))
    (@callback :finish-b)
    (is (= [:finally-entered [:finally-returning 42 true]] @trace))
    (when try-self-wait?
      (is (= :self-release-join (:error (ex-data @refused))))
      (is (true? @unchanged?) "Self-wait refuses before observer issuance or adoption")
      (is (empty? @self-notifications)))
    (is (= [nil] @delivered))
    (is (empty? @errors))
    (is (= 1 (count @task-errors)))
    (is (= :released (:status (c/snapshot b))))
    (is (= :released (:status (c/snapshot target-c))))
    (is (= :joined (get-in (c/snapshot target-c) [:release :phase])))
    (is (empty? (:cleanup-targets (c/snapshot rt))))
    (is (empty? (get-in (c/snapshot rt) [:global :custody :claims])))
    (is (empty? (get-in (c/snapshot rt) [:global :custody :by-holder])))
    (doseq [field [:custody-live-leaves :custody-holder-buckets :custody-claims :custody-pending]]
      (is (zero? (get (c/storage-stats rt) field)) (str field)))
    ;; The completed receipt remains usable without recreating either world.
    (let [detach (lifecycle/observe! @c-completion #(swap! late-delivered conj %) #(swap! errors conj %))]
      (is (ifn? detach))
      (detach) (detach))
    (is (= [nil] @late-delivered))
    (is (empty? @errors))
    (@callback :stale)
    (is (= [nil] @delivered))
    (is (= [nil] @late-delivered))
    (verify-boundaries! rt)))

(deftest cyclic-custody-completes-after-real-asynchronous-finally-return
  (cycle-with-finalizer false))

(deftest transitive-release-self-wait-refuses-before-cleanup-observer-adoption
  (cycle-with-finalizer true))
