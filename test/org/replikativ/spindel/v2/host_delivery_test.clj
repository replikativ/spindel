(ns org.replikativ.spindel.v2.host-delivery-test
  (:require [clojure.test :refer [deftest is]]
            [taoensso.trove :as trove]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.rows :as rw]))

(defn- env [options]
  (let [jobs (atom []) submitted (java.util.concurrent.CountDownLatch. 1)
        executor (reify java.util.concurrent.Executor
                   (execute [_ f] (swap! jobs conj f) (.countDown submitted)))]
    {:p (v2/world (merge {:verify? true :executor executor} options))
     :jobs jobs :submitted submitted}))
(defn- outcome [f] (try [:value (f)] (catch Throwable e [:error e])))
(defn- pump-one! [{:keys [jobs]}]
  (when-let [f (first @jobs)] (swap! jobs subvec 1) (.run ^Runnable f) true))
(defn- pump! [e] (loop [n 1000] (when (pump-one! e) (assert (pos? n)) (recur (dec n)))))
(defn- close! [{:keys [p] :as e}]
  ;; Teardown only, after assertions; never wait on a manually stopped executor.
  (aset ^objects p rw/W-INLINE true) (v2/release-world! p) (pump! e))
(defn- recorder [events]
  (fn [_ _ level id lazy-data]
    (when (#{:engine/host-call-turn-failed :engine/host-handoff-failed} id)
      (swap! events conj [level id (:error (:data (force lazy-data)))]))))
(defn- caller [f]
  (let [answer (atom nil) done (java.util.concurrent.CountDownLatch. 1)
        thread (Thread. (fn [] (let [value (outcome f)]
                                (reset! answer [value (.isInterrupted (Thread/currentThread))])
                                (.countDown done))))]
    (.start thread) {:thread thread :answer answer :done done}))
(defn- result! [{:keys [^Thread thread answer ^java.util.concurrent.CountDownLatch done]}]
  (is (.await done 5 java.util.concurrent.TimeUnit/SECONDS))
  (.join thread 5000) (is (not (.isAlive thread))) @answer)
(defn- reblocked? [^Thread thread]
  (let [end (+ (System/nanoTime) 5000000000)]
    (loop [] (cond (= java.lang.Thread$State/TERMINATED (.getState thread)) false
                  (and (= java.lang.Thread$State/WAITING (.getState thread)) (not (.isInterrupted thread))) true
                  (< (System/nanoTime) end) (do (Thread/yield) (recur)) :else false))))

(deftest committed-ordinary-outcome-wins-over-a-later-real-observer-error
  (doseq [value [nil false :unique] own-error? [false true]]
    (let [{:keys [p] :as e} (env {}) x (v2/signal p 0) callbacks (atom 0) events (atom [])
          late (ex-info "observer failure" {}) own (ex-info "action failure" {})
          withdraw (v2/observe! x (fn [v failed?] (when (and (= 1 v) (not failed?))
                                                  (swap! callbacks inc) (throw late))))]
      (binding [trove/*log-fn* (recorder events)]
        (is (= (if own-error? [:error own] [:value value])
               (outcome #(v2/call-in! p (fn [] (v2/reset-world! p {:committed true})
                                         (v2/write! x 1) (if own-error? (throw own) value))))))
        (is (= [[:error :engine/host-call-turn-failed late]] @events)))
      (is (= {:committed true} (v2/world-state p)))
      (is (= 1 @callbacks)) (withdraw) (close! e))))

(deftest callback-suffix-is-owned-before-new-callbacks-with-no-rescue-ingress
  (doseq [queued? [false true] fail-at [0 1 2]]
    (let [{:keys [p jobs] :as e} (env {}) x (v2/signal p 0) y (v2/signal p :new)
          seen (atom []) error (ex-info "batch callback failure" {})
          extra (atom nil)
          withdraws (mapv (fn [i] (v2/observe! x (fn [v failed?]
                                                  (when (and (= 1 v) (not failed?))
                                                    (swap! seen conj i)
                                                    (when (= i fail-at)
                                                      (reset! extra (v2/observe! y (fn [v _] (swap! seen conj v))))
                                                      (v2/send-world! p #(v2/reset-world! p {:queued true}))
                                                      (throw error)))))) (range 3))]
      (is (empty? @jobs))
      (let [actual (if queued?
                     (do (v2/send-world! p #(v2/write! x 1)) (outcome #(pump-one! e)))
                     (outcome #(v2/write! x 1)))]
        (is (= [:error error] actual))
        (is (= (vec (range (inc fail-at))) @seen))
        (is (seq @jobs) "failed turn must hand off without new API ingress")
        (pump! e)
        (is (= [0 1 2 :new] @seen))
        ;; Read only after existing jobs; this cannot rescue missing handoff.
        (is (= {:queued true} (aget ^objects p rw/W-STATE))))
      (doseq [f withdraws] (f)) (when-let [f @extra] (f)) (close! e))))

(deftest pending-ordinary-wait-interruption-cancels-before-later-pump
  (let [{:keys [p submitted] :as e} (env {:inline? false}) runs (atom 0)
        c (caller #(v2/call-in! p (fn [] (swap! runs inc) (v2/reset-world! p {:late true}))))]
    (is (.await ^java.util.concurrent.CountDownLatch submitted 5 java.util.concurrent.TimeUnit/SECONDS))
    (.interrupt ^Thread (:thread c))
    (let [[[kind error] _] (result! c)] (is (= :error kind)) (is (instance? InterruptedException error)))
    (pump! e) (is (zero? @runs)) (is (= {} (aget ^objects p rw/W-STATE))) (close! e)))

(deftest claimed-ordinary-outcome-survives-repeated-interruption
  (doseq [own-error? [false true]]
    (let [{:keys [p submitted] :as e} (env {:inline? false})
          claimed (java.util.concurrent.CountDownLatch. 1) proceed (java.util.concurrent.CountDownLatch. 1)
          value (Object.) own (InterruptedException. "own action interrupt") runs (atom 0)
          c (caller #(v2/call-in! p (fn [] (swap! runs inc) (.countDown claimed) (.await proceed)
                                    (if own-error? (throw own) value))))
          worker (Thread. ^Runnable #(pump! e))]
      (try
        (is (.await ^java.util.concurrent.CountDownLatch submitted 5 java.util.concurrent.TimeUnit/SECONDS))
        (.start worker) (is (.await claimed 5 java.util.concurrent.TimeUnit/SECONDS))
        (dotimes [_ 2] (.interrupt ^Thread (:thread c)) (is (reblocked? (:thread c))))
        (.countDown proceed)
        (is (= [(if own-error? [:error own] [:value value]) true] (result! c)))
        (.join worker 5000) (is (not (.isAlive worker))) (is (= 1 @runs))
        (finally (.countDown proceed) (.join worker 5000) (.join ^Thread (:thread c) 5000) (close! e))))))

(deftest rejected-ordinary-entry-owns-its-after-gate-completion
  (let [{:keys [p submitted] :as e} (env {:inline? false})
        entry (atom nil) initiator (atom nil) pump-thread (atom nil)
        original-prepare @#'v2/prepare-host-entry! original-after @#'v2/after-gate-action!
        rejected (java.util.concurrent.CountDownLatch. 1) proceed (java.util.concurrent.CountDownLatch. 1)
        runs (atom 0) c (atom nil) worker (atom nil)]
    (try
      (with-redefs-fn
        {#'v2/prepare-host-entry! (fn [control f reject intent]
                                  (let [answer (original-prepare control f reject intent)]
                                    (when (identical? @initiator (Thread/currentThread)) (reset! entry control)) answer))
         #'v2/after-gate-action! (fn [f]
                                  (when (and (identical? @pump-thread (Thread/currentThread))
                                             (identical? p (#'v2/cw)) @entry
                                             (= :rejected (:phase @(.-state ^org.replikativ.spindel.v2.core.HostIngress @entry))))
                                    (.countDown rejected) (.await proceed))
                                  (original-after f))}
        (fn []
          (v2/release-world! p)
          (reset! c (caller #(do (reset! initiator (Thread/currentThread))
                                (v2/call-in! p (fn [] (swap! runs inc))))))
          ;; Witness the actual ordinary entry, not the prior release job.
          (let [end (+ (System/nanoTime) 5000000000)]
            (while (and (nil? @entry) (< (System/nanoTime) end)) (Thread/yield)))
          (is (some? @entry))
          (reset! worker (Thread. ^Runnable #(do (reset! pump-thread (Thread/currentThread)) (pump! e))))
          (.start ^Thread @worker)
          (is (.await rejected 5 java.util.concurrent.TimeUnit/SECONDS))
          (.interrupt ^Thread (:thread @c)) (is (reblocked? (:thread @c)))
          (.countDown proceed)
          (let [[[kind error] interrupted?] (result! @c)]
            (is (= :error kind)) (is (:spindel/released (ex-data error))) (is interrupted?))
          (.join ^Thread @worker 5000) (is (zero? @runs))))
      (finally (.countDown proceed) (when @worker (.join ^Thread @worker 5000))
               (when @c (.join ^Thread (:thread @c) 5000)) (close! e)))))
