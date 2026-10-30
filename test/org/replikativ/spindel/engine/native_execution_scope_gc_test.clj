(ns org.replikativ.spindel.engine.native-execution-scope-gc-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.signal :as signal]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync])
  (:import [java.lang.ref Reference WeakReference]))

(defn- collected? [^WeakReference weak]
  (loop [remaining 100]
    (System/gc)
    (Thread/sleep 10)
    (cond
      (nil? (.get weak)) true
      (= 1 remaining) false
      :else (recur (dec remaining)))))

(defn- scoped-source [park?]
  (let [rt (context/create-execution-context {:engine :owned})
        scope (lifetime/open-scope! rt :explicit)
        payload (Object.)]
    (binding [ec/*execution-context* rt]
      (lifetime/with-owner scope
        (signal/signal payload)
        (when park?
          (let [pending (sync/deferred)
                target (spin (lifetime/with-owner scope (await pending) payload))]
            (target (fn [_]) (fn [_]))
            (when-not (some #(and (= :parked (:status %)) (= :scope (first (:owner %))))
                            (vals (:runs (owned/snapshot rt))))
              (throw (ex-info "GC fixture did not park a scope-owned Run" {})))))))
    {:context rt :scope scope :weak-payload (WeakReference. payload)}))

(deftest closed-scope-releases-payload-while-world-and-capability-remain-live
  (let [{:keys [context scope weak-payload] :as fixture} (scoped-source false)]
    (try
      (System/gc)
      (is (some? (.get ^WeakReference weak-payload)) "An open root-owned scope retains its source")
      (is (nil? (lifetime/close-scope! context scope)))
      (is (true? (rtp/execution-owner-joined? context scope)))
      (is (thrown? Exception (lifetime/bindable-scope context scope)))
      (is (collected? weak-payload))
      (is (= :live (:status (owned/snapshot context))) "Collection must not require releasing the world")
      (finally
        (context/release-context! context)
        (Reference/reachabilityFence fixture)))))

(defn- escaped-capability [release? park?]
  (let [{:keys [context scope weak-payload]} (scoped-source park?)]
    (when release? (context/release-context! context))
    {:scope scope :weak-world (WeakReference. context) :weak-payload weak-payload}))

(deftest saved-open-scope-capability-does-not-root-an-unobserved-world
  (let [fixture (escaped-capability false false)]
    (try
      (is (collected? (:weak-world fixture)))
      (is (collected? (:weak-payload fixture)))
      (finally (Reference/reachabilityFence fixture)))))

(deftest saved-scope-does-not-pin-an-unobserved-parked-run
  (let [fixture (escaped-capability false true)]
    (try
      (is (collected? (:weak-world fixture)))
      (is (collected? (:weak-payload fixture)))
      (finally (Reference/reachabilityFence fixture)))))

(deftest saved-scope-capability-does-not-retain-a-released-world
  (let [fixture (escaped-capability true false)]
    (try
      (is (collected? (:weak-world fixture)))
      (is (collected? (:weak-payload fixture)))
      (finally (Reference/reachabilityFence fixture)))))
