(ns org.replikativ.spindel.engine.native-timer-gc-test
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.combinators :as combinators]
            [org.replikativ.spindel.spin.core :as spin-core])
  (:import [java.lang.ref Reference WeakReference]))

(defn- ignore-result [_] nil)
(defn- no-sweep [] nil)

(defn- controlled-transport []
  (let [scheduled (atom []) workers (atom []) cancelled (atom [])]
    {:scheduled scheduled :workers workers :cancelled cancelled
     :transport {:schedule (fn [_ dispatch]
                             (let [handle [:timer-handle (count @scheduled)]]
                               (swap! scheduled conj dispatch)
                               handle))
                 :submit (fn [worker] (swap! workers conj worker))
                 :cancel (fn [handle] (swap! cancelled conj handle))}}))

(defn- collected? [^WeakReference weak sweep]
  (loop [remaining 100]
    (sweep)
    (System/gc)
    (Thread/sleep 10)
    (cond
      (nil? (.get weak)) true
      (= 1 remaining) false
      :else (recur (dec remaining)))))

(defn- sleep-aliases-without-world []
  ;; The allocating frame must return before collecting the runtime. The kept
  ;; Sleep bodies may retain their values, but neither may retain this world.
  (let [driver (controlled-transport)
        rt (owned/runtime {:cps-exit? true :timer-transport (:transport driver)})]
    (binding [ec/*execution-context* rt]
      (let [cold (combinators/sleep 100000 :cold)
            pending (combinators/sleep 100000 :pending)]
        (pending ignore-result ignore-result)
        ((first @(:scheduled driver)))
        {:weak-world (WeakReference. rt) :cold cold :pending pending :driver driver}))))

(deftest kept-sleep-aliases-and-platform-wrappers-do-not-retain-the-world
  (let [fixture (sleep-aliases-without-world)
        driver (:driver fixture)]
    (try
      (is (= 1 (count @(:scheduled driver))))
      (is (= 1 (count @(:workers driver))))
      (is (collected? (:weak-world fixture) no-sweep)
          "cold/pending Sleep aliases and retained platform wrappers contain no strong runtime reference")
      ;; Both transport stages remain callable after the world disappears.
      ((first @(:workers driver)))
      ((first @(:scheduled driver)))
      (is (nil? (.get ^WeakReference (:weak-world fixture))))
      (finally (Reference/reachabilityFence fixture)))))

(defn- cancelled-payload-without-sleep [rt driver]
  ;; Return no Sleep, body template, observation callback, or successful value.
  ;; Holding any user Sleep body here would legitimately retain its payload.
  (binding [ec/*execution-context* rt]
    (let [payload (Object.)
          weak (WeakReference. payload)
          sleep (combinators/sleep 100000 payload)]
      (sleep ignore-result ignore-result)
      ((first @(:scheduled driver)))
      (rtp/cancel-computation! rt sleep (spin-core/spin-id sleep)
                               (spin-core/spin-body sleep) (ex-info "cancel heap probe" {}))
      weak)))

(deftest cancelled-timer-releases-payload-after-all-sleep-aliases-are-dropped
  (let [driver (controlled-transport)
        rt (owned/runtime {:cps-exit? true :timer-transport (:transport driver)})
        weak (cancelled-payload-without-sleep rt driver)]
    (try
      (is (= 1 (count @(:scheduled driver))))
      (is (= 1 (count @(:workers driver))))
      (is (= [[:timer-handle 0]] @(:cancelled driver)))
      (is (collected? weak #(owned/snapshot rt))
          "the live world releases the cancelled value while stale transport wrappers remain retained")
      ((first @(:workers driver)))
      ((first @(:scheduled driver)))
      (is (nil? (.get ^WeakReference weak)))
      (is (zero? (:timer-resources (owned/storage-stats rt))))
      (finally
        (Reference/reachabilityFence rt)
        (Reference/reachabilityFence driver)))))
