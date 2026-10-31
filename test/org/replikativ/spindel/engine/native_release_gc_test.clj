(ns org.replikativ.spindel.engine.native-release-gc-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.atom :as ratom]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.lifecycle :as lifecycle]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync])
  (:import [java.lang.ref Reference WeakReference]))

(defn- collect! [^WeakReference weak]
  (loop [remaining 100]
    (System/gc)
    (Thread/sleep 10)
    (cond (nil? (.get weak)) true
          (= 1 remaining) false
          :else (recur (dec remaining)))))

(defn- joined-fixture []
  (let [rt (context/create-execution-context {:engine :owned})
        payload (Object.)]
    (binding [ec/*execution-context* rt]
      (let [cell (ratom/atom payload)
            completion (context/release-context! rt)]
        {:context rt :cell cell :completion completion :weak-payload (WeakReference. payload)}))))

(deftest completed-release-and-old-context-aliases-do-not-retain-application-state
  (let [fixture (joined-fixture)]
    (try
      (is (collect! (:weak-payload fixture)))
      (is (thrown? Exception (binding [ec/*execution-context* (:context fixture)] @(:cell fixture))))
      (let [joined (atom [])]
        ((:completion fixture) #(swap! joined conj %) #(throw %))
        (is (= [nil] @joined)))
      (finally (Reference/reachabilityFence fixture)))))

(defn- unreachable-sibling-fixture []
  (let [source (owned/runtime {:cps-exit? true})
        source-root (rtp/root-execution-owner source)
        {sibling :context bearer :capability}
        (rtp/fork-owned-world! source {:world-id [:w 1] :owner source-root})
        sibling-root (rtp/root-execution-owner sibling)
        moved (rtp/transfer-owned-world! source bearer source-root sibling sibling-root
                                         {:operation-id :move-sibling})
        payload (Object.)]
    (owned/signal sibling :payload payload)
    (let [completion (rtp/request-world-release! source :old-world)]
      {:completion completion :bearer moved :owner sibling-root
       :was-live? (= :live (:status (owned/snapshot sibling)))
       :source-joined? (= :joined (get-in (owned/snapshot source) [:release :phase]))
       :weak-payload (WeakReference. payload) :weak-world (WeakReference. sibling)})))

(deftest completed-receipt-and-data-capabilities-do-not-pin-a-live-sibling-arena
  (let [before (owned/pending-release-count)
        fixture (unreachable-sibling-fixture)]
    (try
      (is (:was-live? fixture))
      (is (:source-joined? fixture))
      (is (= before (owned/pending-release-count)))
      (is (collect! (:weak-payload fixture)))
      (is (collect! (:weak-world fixture)))
      (let [values (atom [])]
        (lifecycle/observe! (:completion fixture) #(swap! values conj %) #(throw %))
        (is (= [nil] @values)))
      (finally (Reference/reachabilityFence fixture)))))

(defn- unfinished-fixture []
  (let [rt (context/create-execution-context {:engine :owned})
        payload (Object.) trace (atom [])]
    (binding [ec/*execution-context* rt]
      (let [pending (sync/deferred) ack (sync/deferred)
            target (spin
                    (let [cell (ratom/atom payload)]
                      (try (await pending)
                           (finally
                             (await-finalization ack)
                             (swap! trace conj (identical? payload @cell))))))]
        (target (fn [_]) (fn [_]))
        (let [completion (context/release-context! rt)]
          ;; Neither the caller's context nor the completion is returned strongly.
          {:ack ack :trace trace :weak-payload (WeakReference. payload)
           :weak-world (WeakReference. (rtp/release-runtime completion))
           :weak-completion (WeakReference. completion)})))))

(defn- acknowledge! [fixture]
  ;; Deferred delivery selects an explicit context. Keep its temporary strong
  ;; reference inside this helper, which returns before the collection checks.
  (when-let [rt (.get ^WeakReference (:weak-world fixture))]
    (binding [ec/*execution-context* rt] ((:ack fixture) nil))))

(deftest explicit-release-owns-unfinished-cleanup-after-the-caller-drops-its-handles
  (let [before (owned/pending-release-count)
        fixture (unfinished-fixture)]
    (try
      (is (= (inc before) (owned/pending-release-count)))
      (System/gc)
      (is (some? (.get ^WeakReference (:weak-payload fixture))))
      (is (empty? @(:trace fixture)))
      (is (true? (acknowledge! fixture)))
      (is (= [true] @(:trace fixture)))
      (is (= before (owned/pending-release-count)))
      (is (collect! (:weak-payload fixture)))
      (is (collect! (:weak-world fixture)))
      (is (collect! (:weak-completion fixture)))
      (finally (Reference/reachabilityFence fixture)))))

(defn- queue-raw-payload! [mailbox]
  ;; Return before the raw callback's physical return publishes joining.
  (let [payload (Object.)]
    (sync/post! mailbox payload)
    (WeakReference. payload)))

(defn- blocked-observer-fixture []
  (let [rt (context/create-execution-context {:engine :owned})
        entered (promise) leave (promise) raw-entered (promise) raw-leave (promise)
        weak (atom nil)]
    (binding [ec/*execution-context* rt]
      (let [mailbox (sync/mailbox)]
        (mailbox
         (fn [_]
           (deliver raw-entered true)
           (when-not (= true (deref raw-leave 5000 ::timeout))
             (throw (ex-info "Raw callback latch timed out" {})))
           (reset! weak (queue-raw-payload! mailbox)))
         #(throw %))
        {:runtime rt :mailbox mailbox :entered entered :leave leave
         :raw-entered raw-entered :raw-leave raw-leave :weak-payload weak
         :worker (future (binding [ec/*execution-context* rt] (sync/post! mailbox :start)))}))))

(deftest stale-accepted-payloads-collect-while-an-external-join-observer-is-still-running
  (let [fixture (blocked-observer-fixture)]
    (try
      (is (= true (deref (:raw-entered fixture) 5000 ::timeout)))
      (let [completion (context/release-context! (:runtime fixture))]
        (lifecycle/observe!
         completion
         (fn [_]
           (deliver (:entered fixture) true)
           (when-not (= true (deref (:leave fixture) 5000 ::timeout))
             (throw (ex-info "Joined observer latch timed out" {}))))
         #(throw %))
        (deliver (:raw-leave fixture) true)
        (is (= true (deref (:entered fixture) 5000 ::timeout)))
        (is (= :joined (get-in (owned/snapshot (:runtime fixture)) [:release :phase])))
        (is (instance? WeakReference @(:weak-payload fixture)))
        (when-let [weak @(:weak-payload fixture)]
          (is (collect! weak) "The raw post must not retain its payload behind the joined observer"))
        (Reference/reachabilityFence completion))
      (finally
        (deliver (:raw-leave fixture) true)
        (deliver (:leave fixture) true)))
    (is (not= ::timeout (deref (:worker fixture) 5000 ::timeout)))
    (Reference/reachabilityFence fixture)))
