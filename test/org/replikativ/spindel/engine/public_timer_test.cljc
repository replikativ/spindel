(ns org.replikativ.spindel.engine.public-timer-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.engine.fault :as fault]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.combinators :as c]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.signal :as signal]
            [org.replikativ.spindel.test-helpers :refer [async]]
            [org.replikativ.spindel.incremental.interval :as iv]))

(bindings/register-spin-scope-key! :timer-test/scope)

(defn- controlled []
  (let [scheduled (atom []) workers (atom []) cancelled (atom [])]
    {:scheduled scheduled :workers workers :cancelled cancelled
     :transport {:schedule (fn [delay dispatch]
                             (let [handle [:handle (count @scheduled)]]
                               (swap! scheduled conj {:delay delay :dispatch dispatch :handle handle})
                               handle))
                 :submit (fn [worker] (swap! workers conj worker))
                 :cancel (fn [handle] (swap! cancelled conj handle))}}))

(defn- runtime [driver]
  (owned/runtime {:audit? true :cps-exit? true :timer-transport (:transport driver)}))
(defn- observe! [s values errors]
  (s #(swap! values conj %) #(swap! errors conj %)))
(defn- cancel! [rt s reason]
  (rtp/cancel-computation! rt s (spin-core/spin-id s) (spin-core/spin-body s) reason))
(defn- dispatch! [driver i] ((:dispatch (nth @(:scheduled driver) i))))
(defn- worker! [driver i] ((nth @(:workers driver) i)))
(defn- timer-rows [rt]
  (filter #(= :timer-resource (:kind %)) (vals (:native (owned/snapshot rt)))))

(deftest sleep-is-lazy-and-its-callback-resumes-the-real-continuation
  (let [driver (controlled) rt (runtime driver) values (atom []) errors (atom [])]
    (binding [ec/*execution-context* rt]
      (let [s (c/sleep 100 41) parent (spin (inc (await s)))]
        (is (empty? @(:scheduled driver)))
        (observe! parent values errors)
        (is (= [100] (mapv :delay @(:scheduled driver))))
        (is (empty? @values))
        (dispatch! driver 0)
        (is (empty? @values))
        (worker! driver 0)
        (is (= [42] @values))
        (is (empty? @errors))
        (is (empty? (timer-rows rt)))))
    (verify-boundaries! rt)))

(deftest timer-values-have-no-error-disposition
  (doseq [value [nil false (ex-info "successful timer data" {})
                 {:variant :error :type spin-core/spin-cancelled}]]
    (let [driver (controlled) rt (runtime driver) values (atom []) errors (atom [])]
      (binding [ec/*execution-context* rt]
        (observe! (c/sleep 1 value) values errors)
        (dispatch! driver 0) (worker! driver 0)
        (is (= [value] @values))
        (is (empty? @errors))
        (is (empty? (timer-rows rt))))
      (verify-boundaries! rt))))

(deftest cancelling-a-dispatched-timer-revokes-queued-worker-entry
  (let [driver (controlled) rt (runtime driver) values (atom []) errors (atom [])
        reason (ex-info "cancel timer" {})]
    (binding [ec/*execution-context* rt]
      (let [s (c/sleep 100000 :late)]
        (observe! s values errors)
        (dispatch! driver 0)
        (cancel! rt s reason)
        (is (= [reason] @errors))
        (is (empty? @values))
        (worker! driver 0)
        (worker! driver 0)
        (cancel! rt s reason)
        (is (= [reason] @errors))
        (is (empty? @values))
        (is (= [[:handle 0]] @(:cancelled driver)))
        (is (empty? (timer-rows rt)))))
    (verify-boundaries! rt)))

(deftest cancellation-before-dispatch-does-not-revive-the-registration
  (let [driver (controlled) rt (runtime driver) values (atom []) errors (atom [])]
    (binding [ec/*execution-context* rt]
      (let [s (c/sleep 100000 41) reason (ex-info "cancel before dispatch" {})]
        (observe! s values errors)
        (cancel! rt s reason)
        (dispatch! driver 0) (worker! driver 0)
        (is (empty? @values))
        (is (= [reason] @errors))
        (is (empty? (timer-rows rt)))))
    (verify-boundaries! rt)))

(deftest synchronous-readiness-waits-for-the-installer-to-return
  (let [order (atom []) cancelled (atom [])
        driver {:transport {:schedule (fn [_ dispatch]
                                        (swap! order conj :install)
                                        (dispatch)
                                        (swap! order conj :after-callback)
                                        :inline-handle)
                            :submit (fn [worker] (worker))
                            :cancel #(swap! cancelled conj %)}}
        rt (runtime driver) errors (atom [])]
    (binding [ec/*execution-context* rt]
      (let [parent (spin (inc (await (c/sleep 0 41))))]
        (parent #(swap! order conj [:result %]) #(swap! errors conj %))
        (is (= [:install :after-callback [:result 42]] @order))
        (is (empty? @errors))
        (is (= [:inline-handle] @cancelled))
        (is (empty? (timer-rows rt)))))
    (verify-boundaries! rt)))

(deftest installation-failure-is-an-explicit-error
  (let [error (ex-info "schedule rejected" {})
        driver {:transport {:schedule (fn [_ _] (throw error))
                            :submit (fn [worker] (worker)) :cancel (fn [_])}}
        rt (runtime driver) values (atom []) errors (atom [])]
    (binding [ec/*execution-context* rt]
      (observe! (c/sleep 1 41) values errors)
      (is (empty? @values))
      (is (= [error] @errors))
      (is (empty? (timer-rows rt))))
    (verify-boundaries! rt)))

(deftest asynchronous-worker-rejection-does-not-strand-a-wait
  (let [error (ex-info "worker rejected" {}) scheduled (atom nil) cancelled (atom [])
        driver {:transport {:schedule (fn [_ dispatch] (reset! scheduled dispatch) :handle)
                            :submit (fn [_] (throw error))
                            :cancel #(swap! cancelled conj %)}}
        rt (runtime driver) values (atom []) errors (atom []) faults (atom [])
        previous (fault/current-fault-reporter)]
    (try
      (fault/set-fault-reporter! #(swap! faults conj [%1 %2]))
      (binding [ec/*execution-context* rt]
        (observe! (c/sleep 1 41) values errors)
        (@scheduled)
        (is (empty? @values))
        (is (= [error] @errors))
        (is (= 1 (count @faults)))
        (is (= [:handle] @cancelled))
        (is (empty? (timer-rows rt))))
      (verify-boundaries! rt)
      (finally (fault/set-fault-reporter! previous)))))

(deftest old-timer-callbacks-cannot-wake-a-reactive-successor
  (let [driver (controlled) rt (runtime driver) values (atom []) errors (atom [])]
    (binding [ec/*execution-context* rt]
      (let [trigger (signal/signal 0)
            parent (spin (let [n (iv/get-new (track trigger))]
                           (+ n (await (c/sleep 100 40)))))]
        (observe! parent values errors)
        (reset! trigger 1)
        (is (= 2 (count @(:scheduled driver))))
        (dispatch! driver 0) (worker! driver 0)
        (is (empty? @values))
        (dispatch! driver 1) (worker! driver 1)
        (is (= [41] @values))
        (is (empty? @errors))
        (is (empty? (timer-rows rt)))))
    (verify-boundaries! rt)))

(deftest synchronous-timer-loops-remain-stack-safe-and-release-resource-receipts
  (let [driver {:transport {:schedule (fn [_ dispatch] (dispatch) nil)
                            :submit (fn [worker] (worker)) :cancel (fn [_])}}
        rt (owned/runtime {:cps-exit? true :audit? false :timer-transport (:transport driver)})
        values (atom []) errors (atom [])]
    (binding [ec/*execution-context* rt]
      (observe! (spin (loop [i 0 sum 0]
                        (if (= i 1000) sum
                            (recur (inc i) (+ sum (await (c/sleep 0 i))))))) values errors)
      (is (= [499500] @values))
      (is (empty? @errors))
      (is (empty? (timer-rows rt))))))

(deftest timer-resumption-restores-scope-on-its-selected-world
  (let [driver (controlled) rt (runtime driver) foreign (owned/runtime {:cps-exit? true :audit? true})
        values (atom []) errors (atom [])
        task (binding [ec/*execution-context* (assoc rt :bindings {:timer-test/scope :construction})]
               (spin [(await (c/sleep 1 41))
                      (get-in (ec/current-execution-context) [:bindings :timer-test/scope])
                      (ec/same-world? rt (ec/current-execution-context))]))]
    (binding [ec/*execution-context* (assoc rt :bindings {:timer-test/scope :caller})]
      (observe! task values errors))
    (binding [ec/*execution-context* (assoc foreign :bindings {:timer-test/scope :foreign})]
      (dispatch! driver 0) (worker! driver 0)
      (is (= :foreign (get-in (ec/current-execution-context) [:bindings :timer-test/scope])))
      (is (ec/same-world? foreign (ec/current-execution-context))))
    (is (= [[41 :construction true]] @values))
    (is (empty? @errors))
    (verify-boundaries! rt)
    (verify-boundaries! foreign)))

(deftest real-platform-timer-resumes-a-public-spin
  (async done
         (let [rt (context/create-execution-context {:engine :owned :audit? true})]
           (binding [ec/*execution-context* rt]
             (let [task (spin (inc (await (c/sleep 1 41))))]
               (task (fn [value]
                       (try
                         (is (= 42 value))
                         (verify-boundaries! rt)
                         (finally (done))))
                     (fn [error]
                       (is false (str "Real timer failed: " error))
                       (done))))))))

(deftest raw-mailbox-callback-cannot-register-a-root-timer
  (let [driver (controlled) rt (runtime driver) refused (atom [])]
    (binding [ec/*execution-context* rt]
      (let [mb (sync/mailbox)]
        (mb (fn [_]
              (try (rtp/await-public-timer! rt 0 41 (fn [_]) (fn [_]))
                   (catch #?(:clj Throwable :cljs :default) error
                     (swap! refused conj (:error (ex-data error))))))
            #(throw %))
        (mb :message)
        (is (= [:cleanup-only] @refused))
        (is (empty? @(:scheduled driver)))
        (is (empty? (timer-rows rt)))))
    (verify-boundaries! rt)))

#?(:clj
   (deftest cancellation-does-not-join-an-installer-still-on-stack
     (let [entered (promise) leave (promise) cancelled (atom [])
           driver {:transport {:schedule (fn [_ _]
                                           (deliver entered true)
                                           @leave
                                           :late-handle)
                               :submit (fn [worker] (worker))
                               :cancel #(swap! cancelled conj %)}}
           rt (runtime driver) values (atom []) errors (atom [])
           s (binding [ec/*execution-context* rt] (c/sleep 100000 41))
           reason (ex-info "cancel while installing" {})
           installer (future
                       (binding [ec/*execution-context* rt]
                         (observe! s values errors)))]
       (try
         (is (= true (deref entered 10000 ::timeout)))
         (binding [ec/*execution-context* rt]
           (cancel! rt s reason)
           (is (= :error (:variant (rtp/computation-result rt s (spin-core/spin-id s))))))
         (is (not (owned/join-ready? rt owned/w)))
         (is (some #(= :pending (:install %)) (timer-rows rt)))
         (finally (deliver leave true)))
       (is (not= ::timeout (deref installer 10000 ::timeout)))
       (is (empty? @values))
       (is (= [reason] @errors))
       (is (= [:late-handle] @cancelled))
       (is (empty? (timer-rows rt)))
       (is (owned/join-ready? rt owned/w))
       (verify-boundaries! rt))))

#?(:clj
   (deftest pending-sleep-follows-prefix-adoption-and-keeps-the-successor-join-anchor
     (let [driver (controlled) rt (runtime driver) entered (promise) leave (promise)
           values (atom []) errors (atom []) reason (ex-info "retire adopted timer ancestry" {})
           trigger (binding [ec/*execution-context* rt] (signal/signal 0))
           parent (binding [ec/*execution-context* rt]
                    (spin (let [child (c/sleep 100 40)
                                n (iv/get-new (track trigger))]
                            (+ n (await child)))))]
       (binding [ec/*execution-context* rt]
         (parent (fn [value] (swap! values conj value) (deliver entered true) @leave)
                 #(swap! errors conj %))
         (let [before (:anchor (first (timer-rows rt)))]
           (reset! trigger 1)
           (is (= 1 (count @(:scheduled driver))) "The prefix sleep was adopted")
           (is (not= before (:anchor (first (timer-rows rt)))))))
       (dispatch! driver 0)
       (let [worker (future (worker! driver 0))]
         (try
           (is (= true (deref entered 10000 ::timeout)))
           (is (= [41] @values))
           (binding [ec/*execution-context* rt]
             (cancel! rt parent reason))
           (is (some #(and (:retired? %) (seq (:frames %))) (timer-rows rt)))
           (is (not (owned/join-ready? rt owned/w)))
           (finally (deliver leave true)))
         (is (not= ::timeout (deref worker 10000 ::timeout))))
       (is (= [reason] @errors) "The standing reactive observer receives cancellation once")
       (is (empty? (timer-rows rt)))
       (is (owned/join-ready? rt owned/w))
       (verify-boundaries! rt))))

#?(:clj
   (deftest a-completed-body-does-not-erase-the-timer-callback-frame
     (let [driver (controlled) rt (runtime driver)
           entered (promise) leave (promise) values (atom []) errors (atom [])
           s (binding [ec/*execution-context* rt] (c/sleep 1 41))]
       (binding [ec/*execution-context* rt]
         (s (fn [value]
              (swap! values conj value)
              (deliver entered true)
              @leave)
            #(swap! errors conj %)))
       (dispatch! driver 0)
       (let [worker (future (worker! driver 0))]
         (try
           (is (= true (deref entered 10000 ::timeout)))
           (is (= [41] @values))
           (is (some #(seq (:frames %)) (timer-rows rt)))
           (is (not (owned/join-ready? rt owned/w)))
           (binding [ec/*execution-context* rt]
             (cancel! rt s (ex-info "retire completed timer owner" {})))
           (is (not (owned/join-ready? rt owned/w)))
           (is (some #(and (:retired? %) (seq (:frames %))) (timer-rows rt)))
           (finally (deliver leave true)))
         (is (not= ::timeout (deref worker 10000 ::timeout))))
       (is (empty? @errors) "Already committed success is not withdrawn")
       (is (empty? (timer-rows rt)))
       (is (owned/join-ready? rt owned/w))
       (verify-boundaries! rt))))

(deftest protected-operation-cannot-create-a-timer-through-a-root-fallback
  (let [driver (controlled) rt (runtime driver) values (atom []) errors (atom [])]
    (binding [ec/*execution-context* rt]
      (observe! (spin (await-finalization
                       (fn [succeed fail]
                         (rtp/await-public-timer! rt 0 41 succeed fail)))) values errors)
      (is (empty? @values))
      (is (= 1 (count @errors)))
      (is (= :cleanup-only (:error (ex-data (first @errors)))))
      (is (empty? @(:scheduled driver)))
      (is (empty? (timer-rows rt))))
    (verify-boundaries! rt)))
