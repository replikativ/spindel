(ns org.replikativ.spindel.engine.native-custody-profile-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]))

(defn- ignore-result [_])
(defn- world-id [rt] (let [state (c/snapshot rt)] (or (:id state) (second (:root state)))))
(defn- publish [rt owner id]
  (rtp/fork-owned-world! rt {:world-id id :owner owner :systems #{} :mode :following}))
(defn- live-cap [rt child]
  (first (for [[id row] (get-in (c/snapshot rt) [:global :caps])
               :when (and (= (world-id child) (:world row)) (= :open (:disposition row)))] [id row])))
(defn- refuses-unchanged! [rt f operation]
  (let [before (c/snapshot-family rt)
        error (try (f) nil (catch #?(:clj Exception :cljs :default) error error))]
    (is (= :unsupported-operation (:error (ex-data error))))
    (when operation (is (= operation (:operation (ex-data error)))))
    (is (= before (c/snapshot-family rt)))
    error))

(deftest automatic-run-retirement-fences-the-entire-prospective-custody-closure
  (doseq [ownership [:parked-run :reactive-run :scope-under-run]]
    (testing (str ownership)
      (let [rt (c/runtime {:audit? true :cps-exit? true}) root (lifetime/root-scope rt)
            driver (c/signal rt :driver 0)
            {b :context b-cap :capability} (publish rt root [:w 1])
            b-scope (lifetime/open-scope! b :holds-c)
            {target-c :context} (publish b b-scope [:w 2])
            c-scope (lifetime/open-scope! target-c :destination)
            {d :context d-cap :capability} (publish rt root [:w 3])
            acquired (atom nil) actor-errors (atom [])
            actor (c/cspin rt :actor
                           (let [owner (if (= ownership :scope-under-run)
                                         (lifetime/open-scope! rt :automatic (lifetime/current-scope rt))
                                         (lifetime/current-scope rt))]
                             (reset! acquired
                                     (rtp/transfer-owned-world! rt b-cap root rt owner
                                                                {:operation-id :acquire-b})))
                           (if (= ownership :reactive-run)
                             (do (c/track driver) :ready)
                             (c/park (c/ticket :actor))))]
        (binding [ec/*execution-context* rt]
          (c/observe! rt actor ignore-result #(swap! actor-errors conj %)))
        (is (some? @acquired))
        (is (empty? @actor-errors))
        (let [[_ row] (live-cap rt b)]
          (is (= (if (= ownership :scope-under-run) :scope :run) (nth (:holder row) 2)))
          (is (= (world-id rt) (second (:holder row)))))
        (is (= (if (= ownership :reactive-run) :completed :parked)
               (get-in (c/snapshot rt) [:runs [:actor 1] :status])))
        (is (empty? (:cleanup-targets (c/snapshot rt)))
            "The invariant applies before any cleanup claim is committed")
        (verify-boundaries! rt)
        ;; C is two custody edges away from the automatic owner. Neither
        ;; resource creation may be cleaned up later to hide partial admission.
        (refuses-unchanged! rt #(c/create-public-deferred! target-c nil) :custody-resource-ingress)
        (refuses-unchanged! rt #(c/create-public-mailbox! target-c nil) :custody-resource-ingress)
        ;; D is Root-held and outside that closure: allocation is permitted,
        ;; but linking its unsupported target into protected C must be atomic.
        (is (some? (c/create-public-deferred! d nil)))
        (let [[d-id _] (live-cap rt d)]
          (refuses-unchanged! rt
                              #(rtp/transfer-owned-world! rt d-cap root target-c c-scope
                                                          {:operation-id :unsupported-link}) nil)
          (is (= :open (get-in (c/snapshot rt) [:global :caps d-id :disposition]))))
        ;; Timer ingress requires an actual ordinary C activation. Check the
        ;; exact snapshot inside its body, before body completion or Rule L.
        (let [attempts (atom []) results (atom []) timer-errors (atom [])
              timer-task (c/cspin target-c :timer-probe
                                  (let [before (c/snapshot-family rt)
                                        error (try
                                                (rtp/await-public-timer! target-c 1000 nil ignore-result ignore-result)
                                                nil
                                                (catch #?(:clj Exception :cljs :default) error error))]
                                    (swap! attempts conj [(select-keys (ex-data error) [:error :operation])
                                                          (= before (c/snapshot-family rt))]))
                                  :timer-refused)]
          (binding [ec/*execution-context* target-c]
            (c/observe! target-c timer-task #(swap! results conj %) #(swap! timer-errors conj %)))
          (is (= [[{:error :unsupported-operation :operation :custody-resource-ingress} true]] @attempts))
          (is (= [:timer-refused] @results))
          (is (empty? @timer-errors))
          (is (empty? (:native (c/snapshot target-c)))))
        (verify-boundaries! rt)
        ;; Automatic retirement is executable because every attempted mutation
        ;; refused before changing the bounded target profile.
        (c/cancel-spin! rt actor)
        (is (= :released (:status (c/snapshot b))))
        (is (= :released (:status (c/snapshot target-c))))
        (is (= :live (:status (c/snapshot d))))
        (is (= 1 (count @actor-errors)))
        (is (empty? (:cleanup-targets (c/snapshot rt))))
        (is (zero? (:custody-claims (c/storage-stats rt))))
        (is (zero? (:custody-pending (c/storage-stats rt))))
        (is (= 1 (:custody-live-leaves (c/storage-stats rt)))
            "Unrelated Root-held D remains live, without implicit disposal")
        (verify-boundaries! rt)))))

(deftest uncommitted-manual-custody-permits-resources-but-refuses-unsupported-disposal
  (doseq [holder-kind [:root :independent-scope]]
    (let [rt (c/runtime {:audit? true :cps-exit? true}) root (lifetime/root-scope rt)
          holder (if (= holder-kind :root) root (lifetime/open-scope! rt :manual))
          {b :context bearer :capability} (publish rt holder [:w 1])
          inner (lifetime/open-scope! b :holds-c)
          {target-c :context} (publish b inner [:w 2])]
      (is (some? (c/create-public-deferred! target-c nil)))
      (is (= :live (:status (c/snapshot target-c))))
      (is (empty? (get-in (c/snapshot rt) [:global :custody :claims])))
      (refuses-unchanged! rt
                          #(if (= holder-kind :root)
                             (rtp/discard-owned-world! rt bearer holder {:operation-id :unsupported-manual})
                             (lifetime/close-scope! rt holder)) nil)
      (is (= :live (:status (c/snapshot b))))
      (is (= :live (:status (c/snapshot target-c))))
      (is (empty? (:cleanup-targets (c/snapshot rt))))
      (verify-boundaries! rt))))
