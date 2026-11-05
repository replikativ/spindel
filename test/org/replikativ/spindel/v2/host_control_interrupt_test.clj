(ns org.replikativ.spindel.v2.host-control-interrupt-test
  (:require [clojure.test :refer [deftest is]]
            [taoensso.trove :as trove]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.lifetime :as lt]))

(defn- env [inline?]
  (let [jobs (atom []) submitted (java.util.concurrent.CountDownLatch. 1)
        executor (reify java.util.concurrent.Executor
                   (execute [_ f] (swap! jobs conj f) (.countDown submitted)))]
    {:p (v2/world {:inline? inline? :verify? true :executor executor}) :jobs jobs :submitted submitted}))
(defn- pump! [{:keys [jobs]}]
  (loop [fuel 1000]
    (when-let [f (first @jobs)] (assert (pos? fuel)) (swap! jobs subvec 1) (.run ^Runnable f) (recur (dec fuel)))))
(defn- close! [e]
  ;; Teardown only: every behavior assertion precedes this call. Restore inline
  ;; dispatch BEFORE any synchronous acknowledgement/status control can wait.
  (aset ^objects (:p e) rw/W-INLINE true)
  (v2/release-world! (:p e))
  (pump! e))
(defn- snapshot [p]
  [@(deref #'v2/world-order) (#'v2/peek-id p) (aget ^objects p rw/W-EPOCH)
   (:next-child (aget ^objects p rw/W-CLOSE))
   (count (:settlements (aget ^objects p rw/W-CLOSE)))
   (:worlds (lt/census (aget ^objects p rw/W-FAMILY) (aget ^objects p rw/W-WATCHES) nil))])
(defn- caller [f preinterrupt?]
  (let [answer (atom nil) done (java.util.concurrent.CountDownLatch. 1)
        thread (Thread.
                (fn []
                  (when preinterrupt? (.interrupt (Thread/currentThread)))
                  (let [outcome (try [:value (f)] (catch Throwable error [:error error]))]
                    (reset! answer {:outcome outcome :interrupted? (.isInterrupted (Thread/currentThread))})
                    (.countDown done))))]
    (.start thread)
    {:thread thread :answer answer :done done}))
(defn- result! [{:keys [^Thread thread answer ^java.util.concurrent.CountDownLatch done]}]
  (is (.await done 5 java.util.concurrent.TimeUnit/SECONDS))
  (.join thread 5000)
  (is (not (.isAlive thread)))
  @answer)
(defn- reblocked? [^Thread thread]
  (let [deadline (+ (System/nanoTime) 5000000000)]
    (loop []
      (let [state (.getState thread)]
        (cond
          (= java.lang.Thread$State/TERMINATED state) false
          (and (= java.lang.Thread$State/WAITING state) (not (.isInterrupted thread))) true
          (< (System/nanoTime) deadline) (do (Thread/yield) (recur))
          :else false)))))

(deftest pending-interrupt-revokes-only-the-unclaimed-fork-or-capability
  (doseq [operation [:fork :settlement] preinterrupt? [false true]]
    (let [{:keys [p submitted] :as e} (env false) before (snapshot p)
          held-entry (atom nil) allocation (atom nil) original-prepare @#'v2/prepare-host-entry!
          c (caller #(with-redefs-fn
                       {#'v2/prepare-host-entry!
                        (fn [entry f reject intent]
                          (reset! held-entry entry)
                          (reset! allocation (java.lang.ref.WeakReference. f))
                          (original-prepare entry f reject intent))}
                       (fn [] (if (= operation :fork) (v2/fork! p)
                                  (v2/register-world-settlement! (v2/world-host-owner p) p [])))) preinterrupt?)]
      (is (.await ^java.util.concurrent.CountDownLatch submitted 5 java.util.concurrent.TimeUnit/SECONDS))
      (when-not preinterrupt? (.interrupt ^Thread (:thread c)))
      (let [{[kind error] :outcome} (result! c)]
        (is (= :error kind)) (is (instance? InterruptedException error)))
      (is (= before (snapshot p)))
      (is (= :canceled (:phase @(.-state ^org.replikativ.spindel.v2.core.HostIngress @held-entry))))
      (is (loop [n 100]
            (System/gc)
            (if (nil? (.get ^java.lang.ref.WeakReference @allocation)) true
                (if (zero? n) false (do (Thread/sleep 10) (recur (dec n)))))))
      (pump! e)
      (is (= before (snapshot p)))
      (is (nil? (aget ^objects p rw/W-OWNED)))
      ;; Red-case private teardown of an otherwise inaccessible cap. close!
      ;; restores inline before synchronous ack; the original caller has none.
      (close! e)
      (doseq [debt (vals (:settlements (aget ^objects p rw/W-CLOSE)))]
        (v2/acknowledge-world-settlement! (:capability debt) {:settled? true :value :closed}))
      (pump! e))))

(deftest claimed-control-survives-repeated-caller-interrupts
  (doseq [failed? [false true]]
    (let [{:keys [p submitted] :as e} (env false)
          claimed (java.util.concurrent.CountDownLatch. 1) proceed (java.util.concurrent.CountDownLatch. 1)
          own-error (ex-info "own claimed refusal" {}) original-fork @#'v2/fork-world*
          worker (atom nil) c (atom nil)]
      (try
        (with-redefs-fn
          {#'v2/fork-world* (fn
                              ([w] (let [child (original-fork w)]
                                     (.countDown claimed) (.await proceed) child))
                              ;; The original one-arity implementation delegates
                              ;; through this Var to its mutating arity.
                              ([w creation] (original-fork w creation)))}
          (fn []
            (reset! c (caller #(if failed?
                                 (#'v2/internal-call! p (fn [] (.countDown claimed) (.await proceed) (throw own-error)))
                                 (v2/fork! p)) false))
            (is (.await ^java.util.concurrent.CountDownLatch submitted 5 java.util.concurrent.TimeUnit/SECONDS))
            (reset! worker (Thread. ^Runnable #(pump! e)))
            (.start ^Thread @worker)
            (is (.await claimed 5 java.util.concurrent.TimeUnit/SECONDS))
            (.interrupt ^Thread (:thread @c))
            (is (reblocked? (:thread @c)))
            (.interrupt ^Thread (:thread @c))
            (is (reblocked? (:thread @c)))
            (.countDown proceed)
            (let [{[kind value] :outcome interrupted? :interrupted?} (result! @c)]
              (if failed? (is (= [:error own-error] [kind value]))
                  (do (is (= :value kind))
                      (when (= :value kind) (is (= rw/T-WORLD (aget ^objects value rw/TYPE))))))
              (is (true? interrupted?)))
            (.join ^Thread @worker 5000)
            (is (not (.isAlive ^Thread @worker)))))
        (close! e)
        (finally (.countDown proceed)
                 (when @worker (.join ^Thread @worker 5000))
                 (when @c (.join ^Thread (:thread @c) 5000)))))))

(deftest already-published-outcome-wins-over-interrupt-before-promise-await
  (doseq [operation [:fork :own-error :own-interrupt]]
    (let [{:keys [p] :as e} (env true) original-internal @#'v2/internal!
          own-error (if (= operation :own-interrupt) (InterruptedException. "own f exception") (ex-info "own error" {}))]
      (with-redefs-fn
        {#'v2/internal! (fn [w action]
                          (let [value (original-internal w action)]
                            (.interrupt (Thread/currentThread)) value))}
        (fn []
          (let [c (caller #(if (= operation :fork) (v2/fork! p)
                               (#'v2/internal-call! p (fn [] (throw own-error)))) false)
                {[kind value] :outcome interrupted? :interrupted?} (result! c)]
            (if (= operation :fork)
              (do (is (= :value kind)) (when (= :value kind) (is (= rw/T-WORLD (aget ^objects value rw/TYPE)))))
              (is (= [:error own-error] [kind value])))
            (is (true? interrupted?)))))
      (close! e)))
  (let [{:keys [p] :as e} (env true) own (InterruptedException. "f's own stored failure")
        {[kind value] :outcome interrupted? :interrupted?}
        (result! (caller #(#'v2/internal-call! p (fn [] (throw own))) false))]
    (is (= [:error own] [kind value]))
    (is (false? interrupted?))
    (close! e)))

(deftest submission-interrupt-after-claim-restores-status-after-diagnostic-delivery
  (doseq [failed? [false true]]
    (let [{:keys [p] :as e} (env true) original-internal @#'v2/internal!
          claimed (java.util.concurrent.CountDownLatch. 1) proceed (java.util.concurrent.CountDownLatch. 1)
          transport (InterruptedException. "submission interrupted after remote claim")
          own (ex-info "own refused control" {}) unique (Object.) events (atom []) worker (atom nil) c (atom nil)]
      (try
        (with-redefs-fn
          {#'v2/internal! (fn [w action]
                            (reset! worker (Thread. ^Runnable #(original-internal w action)))
                            (.start ^Thread @worker)
                            (assert (.await claimed 5 java.util.concurrent.TimeUnit/SECONDS))
                            (throw transport))}
          (fn []
            (reset! c (caller
                       #(binding [trove/*log-fn*
                                  (fn [_ _ _ id lazy-data]
                                    (when (= id :engine/host-control-turn-failed)
                                      (swap! events conj [(:error (:data (force lazy-data)))
                                                          (.isInterrupted (Thread/currentThread))])))]
                          (#'v2/internal-call! p (fn [] (.countDown claimed) (.await proceed)
                                                   (if failed? (throw own) unique)))) false))
            (is (.await claimed 5 java.util.concurrent.TimeUnit/SECONDS))
            (is (reblocked? (:thread @c)))
            (.countDown proceed)
            (let [{:keys [outcome interrupted?]} (result! @c)]
              (is (= (if failed? [:error own] [:value unique]) outcome))
              (is (true? interrupted?)))
            (is (= [[transport false]] @events))
            (.join ^Thread @worker 5000)))
        (close! e)
        (finally (.countDown proceed)
                 (when @worker (.join ^Thread @worker 5000))
                 (when @c (.join ^Thread (:thread @c) 5000)))))))
