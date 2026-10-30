(ns org.replikativ.spindel.engine.timer-transport-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.fault :as fault]
            [org.replikativ.spindel.test-helpers :refer [async]]
            [org.replikativ.spindel.engine.timer-transport :as transport]))

(def ^:dynamic *transport-probe* :neutral)
#?(:cljs (bindings/register-var! #'*transport-probe*))

(defn- controlled []
  (let [dispatch (atom nil) worker (atom nil) cancelled (atom [])
        handle #?(:clj (Object.) :cljs (js-obj))]
    {:dispatch dispatch :worker worker :cancelled cancelled :handle handle
     :driver {:schedule (fn [_ task] (reset! dispatch task) handle)
              :submit (fn [task] (reset! worker task))
              :cancel (fn [value] (swap! cancelled conj value))}}))

(defn- with-faults [f]
  (let [previous (fault/current-fault-reporter) faults (atom [])]
    (fault/set-fault-reporter! (fn [event data] (swap! faults conj [event data])))
    (try (f faults) (finally (fault/set-fault-reporter! previous)))))

(deftest neutral-dispatch-does-not-capture-registered-bindings
  (let [{:keys [driver dispatch worker handle]} (controlled) values (atom [])]
    (is (identical? handle
                    (binding [*transport-probe* :application-payload]
                      (transport/schedule-native-timer!
                       driver 100 #(swap! values conj *transport-probe*) #(throw %)))))
    (@dispatch)
    (is (empty? @values))
    (@worker)
    (is (= [:neutral] @values))))

(deftest cancellation-is-a-platform-request-not-a-worker-return
  (let [{:keys [driver dispatch worker handle cancelled]} (controlled)
        admitted? (atom true) entries (atom [])]
    (transport/schedule-native-timer! driver 10
                                      #(when @admitted? (swap! entries conj :ready)) #(throw %))
    (@dispatch)
    (reset! admitted? false)
    (is (nil? (transport/cancel-native-timer! driver handle)))
    (is (= [handle] @cancelled))
    ;; The platform may still invoke an already queued weak-ID wrapper. Only
    ;; engine admission, represented here by admitted?, revokes application work.
    (@worker)
    (is (empty? @entries))))

(deftest inline-readiness-can-precede-handle-return
  (let [events (atom []) handle #?(:clj (Object.) :cljs (js-obj))
        driver {:schedule (fn [_ task] (task) (swap! events conj :schedule-return) handle)
                :submit (fn [task] (task)) :cancel (fn [_])}]
    (is (identical? handle (transport/schedule-native-timer!
                            driver 0 #(swap! events conj :ready) #(throw %))))
    (is (= [:ready :schedule-return] @events))))

(deftest submission-rejection-has-an-explicit-failure-callback
  (with-faults
    (fn [faults]
      (let [{:keys [driver dispatch worker]} (controlled)
            error (ex-info "worker rejected" {}) ready (atom 0) failed (atom [])
            ;; Even a driver which queues and then throws cannot admit ready
            ;; after the explicit failure has already won the transport seam.
            driver (assoc driver :submit (fn [task] (reset! worker task) (throw error)))]
        (transport/schedule-native-timer! driver 0 #(swap! ready inc) #(swap! failed conj %))
        (@dispatch)
        (@worker)
        (is (zero? @ready))
        (is (= [error] @failed))
        (is (= 1 (count @faults)))
        (@dispatch)
        (@worker)
        (is (= [error] @failed))))))

(deftest post-entry-throws-report-without-selecting-a-failure
  (with-faults
    (fn [faults]
      (let [{:keys [driver dispatch]} (controlled)
            ready (atom 0) failed (atom [])
            driver (assoc driver :submit (fn [task] (task) (throw (ex-info "late submit throw" {}))))]
        (transport/schedule-native-timer!
         driver 0 #(do (swap! ready inc) (throw (ex-info "ready throw" {}))) #(swap! failed conj %))
        (@dispatch)
        (is (= 1 @ready))
        (is (empty? @failed))
        (is (= 2 (count @faults)))))))

(deftest schedule-failure-is-owned-by-the-installer
  (let [error (ex-info "schedule rejected" {}) failed (atom [])
        driver {:schedule (fn [_ _] (throw error)) :submit (fn [task] (task)) :cancel (fn [_])}]
    (is (identical? error
                    (try (transport/schedule-native-timer! driver 0 (fn []) #(swap! failed conj %))
                         nil (catch #?(:clj Throwable :cljs :default) actual actual))))
    (is (empty? @failed))))

#?(:clj
   (deftest shared-default-transport-is-neutral-and-leaves-delay-thread
     (let [result (promise)]
       (binding [*transport-probe* :application-payload]
         (transport/schedule-native-timer!
          transport/default-transport 0
          #(deliver result [*transport-probe* (.getName (Thread/currentThread))])
          #(deliver result %)))
       (let [value (deref result 5000 ::timeout)]
         (is (vector? value))
         (when (vector? value)
           (is (= :neutral (first value)))
           (is (not= "laufzeit-delay" (second value)))))))
   :cljs
   (deftest shared-default-transport-is-neutral
     (async done
            (binding [*transport-probe* :application-payload]
              (transport/schedule-native-timer!
               transport/default-transport 0
               #(do (is (= :neutral *transport-probe*)) (done))
               #(do (is false (str %)) (done)))))))

#?(:clj
   (defn- pending-timer-without-payload-reference []
     (let [payload (Object.)]
       (binding [*transport-probe* payload]
         {:payload (java.lang.ref.WeakReference. payload)
          :handle (transport/schedule-native-timer!
                   transport/default-transport 60000 (fn []) (fn [_]))}))))

#?(:clj
   (deftest pending-default-timer-does-not-retain-ambient-payload
     (let [{:keys [payload handle]} (pending-timer-without-payload-reference)]
       (try
         (loop [remaining 100]
           (System/gc)
           (when (and (pos? remaining) (.get ^java.lang.ref.WeakReference payload))
             (Thread/sleep 10)
             (recur (dec remaining))))
         (is (nil? (.get ^java.lang.ref.WeakReference payload)))
         (finally (transport/cancel-native-timer! transport/default-transport handle))))))
