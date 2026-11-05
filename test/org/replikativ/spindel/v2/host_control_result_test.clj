(ns org.replikativ.spindel.v2.host-control-result-test
  (:require [clojure.test :refer [deftest is]]
            [taoensso.trove :as trove]
            [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.lifetime :as lt]))

(defn- env []
  (let [jobs (atom []) executor (reify java.util.concurrent.Executor (execute [_ f] (swap! jobs conj f)))]
    {:p (v2/world {:verify? true :budget 1 :executor executor}) :jobs jobs}))
(defn- pump-one! [{:keys [jobs]}]
  (when-let [f (first @jobs)] (swap! jobs subvec 1) (.run ^Runnable f) true))
(defn- pump! [e] (loop [n 1000] (when (pump-one! e) (assert (pos? n)) (recur (dec n)))))
(defn- close! [e] (v2/release-world! (:p e)) (pump! e))
(defn- outcome [f] (try [:value (f)] (catch Throwable error [:error error])))
(defn- recorder [events]
  (fn [_ns _coords level id lazy-data]
    (when (= id :engine/host-control-turn-failed)
      (swap! events conj {:level level :id id :data (:data (force lazy-data))}))))
(defn- pending-throwing-result! [{:keys [p] :as e} error]
  (binding [v2/*world* p]
    (let [gate (v2/deferred) t (task (v2/await gate))]
      (v2/value-async t (fn [_ _] (throw error)))
      ;; A real delivery gets its own budget unit. Stop before the later
      ;; callback unit, without manufacturing queues or lifecycle flags.
      (v2/send-world! p #(v2/deliver! gate :ready))
      (loop [n 100]
        (when-not (and (hs/mpsc-empty? (aget ^objects p rw/W-INGRESS))
                       (pos? (count (aget ^objects p rw/W-CALLBACKS))))
          (assert (pos? n)) (assert (pump-one! e)) (recur (dec n))))
      t)))
(defn- snapshot [p]
  [@(deref #'v2/world-order) (#'v2/peek-id p) (aget ^objects p rw/W-EPOCH)
   (:next-child (aget ^objects p rw/W-CLOSE))
   (:worlds (lt/census (aget ^objects p rw/W-FAMILY) (aget ^objects p rw/W-WATCHES) nil))])

(deftest committed-fork-result-survives-a-later-throwing-parent-result-callback
  (let [{:keys [p] :as e} (env) error (ex-info "later parent callback" {})
        t (pending-throwing-result! e error) events (atom [])]
    (binding [trove/*log-fn* (recorder events)]
      (let [[kind value] (outcome #(v2/fork! p))]
        (is (= :value kind))
        (when (= :value kind)
          (is (= rw/T-WORLD (aget ^objects value rw/TYPE)))
          (is (some? (aget ^objects value rw/W-HOLDER))))
        (is (= 1 (count (filter #(= :fork-host (first (:item %))) (aget ^objects p rw/W-LOG)))))
        (is (= [{:level :error :id :engine/host-control-turn-failed :data {:error error}}] @events))))
    (close! e) (hs/fence! t)))

(deftest a-returned-settlement-capability-is-not-lost-to-later-callback-failure
  (let [{:keys [p] :as e} (env) error (ex-info "later callback after native registration" {})
        t (pending-throwing-result! e error) events (atom [])]
    (binding [trove/*log-fn* (recorder events)]
      (let [[kind value] (outcome #(v2/register-world-settlement! (v2/world-host-owner p) p []))]
        (is (= :value kind))
        (is (= 1 (count (:settlements (aget ^objects p rw/W-CLOSE)))))
        (is (= [error] (mapv #(get-in % [:data :error]) @events)))
        (close! e)
        (is (not (:terminal? (aget ^objects p rw/W-CLOSE))))
        ;; Teardown the real accepted debt even in the red lost-result case;
        ;; the public caller itself never received this private fallback.
        (let [cap (if (= :value kind) value (:capability (first (vals (:settlements (aget ^objects p rw/W-CLOSE))))))]
          (v2/acknowledge-world-settlement! cap {:settled? true :value :physically-closed})
          (pump! e)
          (is (:terminal? (aget ^objects p rw/W-CLOSE))))))
    (hs/fence! t)))

(deftest nil-value-and-own-error-have-priority-over-distinct-later-turn-error
  (doseq [failed? [false true]]
    (let [{:keys [p] :as e} (env) turn-error (ex-info "later turn" {}) own-error (ex-info "own control refusal" {})
          t (pending-throwing-result! e turn-error) events (atom [])]
      (binding [trove/*log-fn* (recorder events)]
        (is (= (if failed? [:error own-error] [:value nil])
               (outcome #(#'v2/internal-call! p (fn [] (when failed? (throw own-error)) nil)))))
        (is (= [turn-error] (mapv #(get-in % [:data :error]) @events))))
      (close! e) (hs/fence! t))))

(deftest earlier-queued-turn-error-cancels-control-before-later-pump
  (let [{:keys [p] :as e} (env) error (ex-info "earlier queued body" {}) before (snapshot p)]
    (v2/send-world! p #(throw error))
    (is (= [:error error] (outcome #(v2/fork! p))))
    (is (= before (snapshot p)))
    (pump! e)
    (is (= before (snapshot p)))
    (is (nil? (aget ^objects p rw/W-OWNED)))
    (close! e)))

(deftest jvm-claim-wins-cancellation-race-and-delivers-its-owned-outcome
  (doseq [failed? [false true]]
    (let [{:keys [p] :as e} (env) original-internal @#'v2/internal!
          claimed (java.util.concurrent.CountDownLatch. 1) proceed (java.util.concurrent.CountDownLatch. 1)
          transport-threw (java.util.concurrent.CountDownLatch. 1)
          own-error (ex-info "claimed control failure" {}) turn-error (ex-info "submission error after remote claim" {})
          unique (Object.) events (atom []) worker (atom nil) caller (atom nil) initiator (atom nil)]
      (try
        (with-redefs-fn
          {#'v2/internal! (fn [w action]
                            (if (and (identical? p w) (identical? @initiator (Thread/currentThread)))
                              (do (reset! worker (future (original-internal w action)))
                                  (assert (.await claimed 5 java.util.concurrent.TimeUnit/SECONDS))
                                  (.countDown transport-threw)
                                  (throw turn-error))
                              (original-internal w action)))}
          (fn []
            (reset! caller
                    (future
                      (reset! initiator (Thread/currentThread))
                      (binding [trove/*log-fn* (recorder events)]
                        (outcome #(#'v2/internal-call! p
                                                       (fn []
                                                         (.countDown claimed) (.await proceed)
                                                         (if failed? (throw own-error) unique)))))))
            (is (.await transport-threw 5 java.util.concurrent.TimeUnit/SECONDS))
            (is (not (realized? @caller)))
            (.countDown proceed)
            (is (= (if failed? [:error own-error] [:value unique]) (deref @caller 5000 ::timeout)))
            (is (= [turn-error] (mapv #(get-in % [:data :error]) @events)))
            (is (not= ::timeout (deref @worker 5000 ::timeout)))))
        (close! e)
        (finally (.countDown proceed) (when @caller (future-cancel @caller)) (when @worker (future-cancel @worker)))))))
