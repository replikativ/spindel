(ns org.replikativ.spindel.v2.cleanup-test
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.ioc :as ioc]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await await-finalization]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.verify :as verify]))

(def ^:dynamic *checked-worlds* nil)

(use-fixtures :each
  (fn [f]
    (binding [*checked-worlds* (atom [])]
      (f)
      (doseq [env @*checked-worlds*]
        (is (empty? @(:divergences env))
            (str "cleanup invariant/reachability violations: " @(:divergences env)))))))

(defn- manual-world
  ([] (manual-world true))
  ([verify?]
   (let [jobs (atom []) divergences (atom [])
         env {:world (v2/world {:verify? verify?
                                :hook (when verify? (verify/checking-hook divergences))
                                :executor (reify java.util.concurrent.Executor
                                            (execute [_ f] (swap! jobs conj f)))})
              :jobs jobs :divergences divergences}]
     (when *checked-worlds* (swap! *checked-worlds* conj env))
     env)))

(defn- pump! [{:keys [jobs]}]
  (loop [fuel 1000]
    (when-let [job (first @jobs)]
      (assert (pos? fuel) "cleanup did not reach a boundary")
      (swap! jobs subvec 1)
      (.run ^Runnable job)
      (recur (dec fuel)))))

(defn- outcome [t]
  (let [out (atom [])]
    (v2/value-async t #(swap! out conj [%1 %2]))
    out))

(defn- runs [w]
  (filter #(= rw/T-RUN (aget ^objects % rw/TYPE)) (hs/mvals (aget ^objects w rw/W-REG))))

(def ^:dynamic *cleanup-binding* :outer)

(defn restore-cleanup-binding [captured _runner] captured)

;; partial-cps carries explicit lexical scope adapters across suspension;
;; arbitrary dynamic Vars are not promised generic snapshot semantics.
(ioc/register-binding-scope! 'org.replikativ.spindel.v2.cleanup-test/*cleanup-binding*
                             'clojure.core/identity
                             'org.replikativ.spindel.v2.cleanup-test/restore-cleanup-binding)

(deftest success-error-and-cancellation-share-cleanup-domain
  (doseq [mode [:success :error :cancel]]
    (testing (str mode)
      (let [{w :world :as env} (manual-world)
            complete (atom nil) events (atom []) error (ex-info "body" {:body true})]
        (binding [v2/*world* w]
          (let [gate (v2/deferred)
                t (task
                   (let [resource (v2/cleanup-resource (fn [cb]
                                                         (is (not (hs/held? (aget ^objects w rw/W-LOCK))))
                                                         (swap! events conj :register)
                                                         (reset! complete cb) nil))]
                     (try
                       (case mode :success :value :error (throw error) :cancel (await gate))
                       (finally (swap! events conj :enter)
                                (await-finalization (v2/cleanup-operation resource))
                                (swap! events conj :exit)))))
                out (outcome t)]
            (when (= mode :cancel) (v2/cancel-task! t))
            (is (= [:enter :register] @events))
            (is (= 1 (count (runs w))))
            (if (= mode :cancel)
              (is (v2/cancelled? (ffirst @out)))
              (is (empty? @out)))
            (@complete :released)
            (@complete :duplicate)
            (pump! env)
            (is (= [:enter :register :exit] @events))
            (case mode
              :success (is (= [[:value false]] @out))
              :error (is (= [[error true]] @out))
              :cancel (is (v2/cancelled? (ffirst @out))))
            (is (empty? (runs w)))
            (is (empty? (aget ^objects w rw/W-CLEANUP-WAITS)))
            (is (empty? @(:divergences env)))))))))

(deftest cancellation-during-normal-cleanup-bypasses-outer-catch-and-suffix
  (let [{w :world :as env} (manual-world) complete (atom nil) events (atom [])]
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource (fn [cb] (reset! complete cb) nil))]
                 (try
                   (try
                     (try :body
                          (finally
                            (swap! events conj :inner-enter)
                            (await-finalization (v2/cleanup-operation resource))
                            (swap! events conj :inner-exit)))
                     (catch Throwable _ (swap! events conj :resurrected)))
                   (swap! events conj :suffix)
                   (finally (swap! events conj :outer)))))
            out (outcome t)]
        (v2/cancel-task! t)
        (is (v2/cancelled? (ffirst @out)))
        (@complete :closed)
        (pump! env)
        (is (= [:inner-enter :inner-exit :outer] @events))
        (is (= 1 (count @out)))
        (is (empty? (runs w)))))))

(deftest two-waits-pure-helper-finally-and-binding
  (let [{w :world :as env} (manual-world) complete (atom nil) events (atom []) calls (atom 0)]
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource (fn [cb] (swap! calls inc) (reset! complete cb) nil))]
                 (try :body
                      (finally
                        (binding [*cleanup-binding* :inner]
                          (try
                            (await-finalization (v2/cleanup-operation resource))
                            (swap! events conj *cleanup-binding*)
                            (await-finalization (v2/cleanup-operation resource))
                            (finally (swap! events conj :helper))))))))
            out (outcome t)]
        (let [callback-thread (Thread. #(do (@complete :closed) (pump! env)))]
          (.start callback-thread)
          (.join callback-thread))
        (is (= [[:body false]] @out))
        (is (= [:inner :helper] @events))
        (is (= :outer *cleanup-binding*))
        (is (= 1 @calls))
        (is (empty? (runs w)))))))

(deftest body-cause-and-cleanup-errors-are-preserved
  (let [{w :world} (manual-world)
        body (ex-info "body" {}) inner (ex-info "inner" {}) outer (ex-info "outer" {})]
    (binding [v2/*world* w]
      (let [t (task (try (try (throw body) (finally (throw inner))) (finally (throw outer))))
            out (outcome t)
            error (ffirst @out)]
        (is (= body (ex-cause error)))
        (is (= [inner outer] (:spindel/cleanup-failures (ex-data error))))
        (is (empty? (aget ^objects w rw/W-CLEANUP-FAILURES)))
        (is (empty? (runs w)))))))

(defn- forbidden-source [] (v2/signal :forbidden))

(deftest hidden-ordinary-creation-and-offload-are-forbidden-on-normal-entry
  (doseq [mode [:source :offload]]
    (let [{w :world} (manual-world)]
      (binding [v2/*world* w]
        (let [t (task (try :ok (finally (case mode :source (forbidden-source)
                                              :offload (v2/offload (fn [] :forbidden))))))
              error (ffirst @(outcome t))]
          (is (= :finalizer-effect
                 (:spindel/invalid (ex-data (first (:spindel/cleanup-failures (ex-data error)))))))
          (is (empty? (runs w))))))))

(deftest cancellation-conserves-unpublished-inner-cleanup-failure
  (doseq [recovered? [false true]]
    (let [{w :world :as env} (manual-world)
          complete (atom nil) body (ex-info "body" {}) inner (ex-info "inner" {})]
      (binding [v2/*world* w]
        (let [t (task
                 (let [resource (v2/cleanup-resource (fn [cb] (reset! complete cb) nil))]
                   (try
                     (try
                       (try (throw body) (finally (throw inner)))
                       (catch Throwable e (if recovered? :recovered (throw e))))
                     (finally (await-finalization (v2/cleanup-operation resource))))))
              out (outcome t)]
          (v2/cancel-task! t)
          (@complete :closed)
          (pump! env)
          (is (v2/cancelled? (ffirst @out)))
          (let [report (vals (aget ^objects w rw/W-CLEANUP-FAILURES))]
            (if recovered?
              (is (empty? report))
              (do (is (= [inner] (mapv :error report)))
                  (is (= [body] (mapv :body-error report))))))
          (is (empty? (runs w))))))))

(defn- consume-report! [{w :world :as env}]
  (let [report (atom nil)]
    ;; Internal egress remains admitted after ordinary host admissions close.
    (#'v2/internal! w #(reset! report (#'v2/take-cleanup-report! w)))
    (pump! env)
    @report))

(deftest report-consumption-during-outer-wait-does-not-republish-inner-failure
  (doseq [outer-fails? [false true] released? [false true]]
    (let [{w :world :as env} (manual-world)
          complete (atom nil) body (ex-info "body" {})
          inner (ex-info "inner" {}) outer (ex-info "outer" {})]
      (binding [v2/*world* w]
        (let [t (task
                 (let [resource (v2/cleanup-resource (fn [cb] (reset! complete cb) nil))]
                   (try (try (throw body) (finally (throw inner)))
                        (finally (await-finalization (v2/cleanup-operation resource))))))
              out (outcome t)]
          (v2/cancel-task! t)
          (when released? (v2/release-world! w))
          (is (= [inner] (mapv :error (consume-report! env))))
          (is (empty? (consume-report! env)))
          (is (= 1 (count (runs w))) "the outer finalizer is still pending")
          (if outer-fails? (@complete outer true) (@complete :closed))
          (pump! env)
          (is (v2/cancelled? (ffirst @out)))
          ;; T32 claims remaining unreported errors under the target gate.
          ;; Before request the explicit egress still owns that same report.
          (let [report (if released?
                         (:spindel/cleanup-provenance
                          (ex-data (first (:outcome (v2/world-close-status w)))))
                         (consume-report! env))]
            (is (= (if outer-fails? [outer] []) (mapv :error report)))
            (is (= (if outer-fails? [body] []) (mapv :body-error report))))
          (is (empty? (consume-report! env)))
          (is (empty? (runs w))))))))

(deftest inherited-unwind-does-not-inherit-parent-report-transfer-authority
  (let [{w :world :as env} (manual-world)
        complete (atom nil) body (ex-info "body" {}) inner (ex-info "inner" {})]
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource (fn [cb] (reset! complete cb) nil))]
                 (try (try (throw body) (finally (throw inner)))
                      (finally (await-finalization (v2/cleanup-operation resource))))))]
        (v2/cancel-task! t)
        (is (= [inner] (mapv :error (consume-report! env))))
        (let [child (v2/fork! w)]
          (v2/host-call! child (fn [] nil))
          (pump! env)
          (let [report (consume-report! (assoc env :world child))]
            (is (= 2 (count report)))
            (is (= inner (:error (first report))))
            (is (:spindel/forked (ex-data (:error (second report)))))
            (is (= [body body] (mapv :body-error report))))
          (is (empty? (runs child)))
          (is (empty? (consume-report! (assoc env :world child)))))
        (is (empty? (consume-report! env)) "child conservation cannot change the parent report")
        (@complete :closed)
        (pump! env)
        (is (empty? (consume-report! env)) "parent outer exit cannot re-add its consumed inner error")
        (is (empty? (runs w)))))))

(def ^:dynamic *plain-binding* :outer)

(deftest unregistered-binding-matches-ordinary-partial-cps-contract
  (let [{w :world :as env} (manual-world) complete (atom nil) seen (atom [])]
    (binding [v2/*world* w]
      (let [t (task (binding [*plain-binding* :inner]
                      (swap! seen conj *plain-binding*)
                      (v2/external (fn [cb] (reset! complete cb) nil))
                      (swap! seen conj *plain-binding*)
                      :done))
            out (outcome t)
            callback-thread (Thread. #(do (@complete :value) (pump! env)))]
        (.start callback-thread)
        (.join callback-thread)
        (is (= [[:done false]] @out))
        (is (= [:inner :outer] @seen))
        (is (= :outer *plain-binding*))))))

(deftest pending-report-is-conserved-and-acknowledged-without-run-history
  (let [{w :world :as env} (manual-world) complete (atom nil) error (ex-info "cleanup" {})]
    (binding [v2/*world* w]
      (let [t (task (let [resource (v2/cleanup-resource (fn [cb] (reset! complete cb) nil))]
                      (try :body (finally (await-finalization (v2/cleanup-operation resource))))))]
        (v2/cancel-task! t)
        (@complete error true)
        (pump! env)
        (is (empty? (runs w)))
        (is (= 1 (:unreported-failures (v2/call-in! w #(#'v2/cleanup-diagnostics* w)))))
        (is (= [error] (mapv :error (v2/call-in! w #(#'v2/take-cleanup-report! w)))))
        (is (empty? (v2/call-in! w #(#'v2/take-cleanup-report! w))))))))

(deftest cleanup-capability-origin-is-not-a-family-local-numeric-world-id
  (let [{wa :world} (manual-world) {wb :world} (manual-world)
        resource (v2/cleanup-resource wa (fn [_] (is false "foreign registration")))]
    (is (= (aget ^objects wa rw/ID) (aget ^objects wb rw/ID)))
    (binding [v2/*world* wb]
      (is (:spindel/forked (ex-data (try (v2/cleanup-operation resource)
                                         (catch Throwable e e))))))))

(deftest physical-resource-acknowledgement-is-independent-of-cleanup-completion
  (let [{w :world :as env} (manual-world)
        ordinary (atom nil) release (atom nil) detached (atom 0)]
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource (fn [cb] (reset! release cb) #(swap! detached inc)))]
                 (try (v2/external (fn [cb] (reset! ordinary cb) (fn [] nil)))
                      (finally (await-finalization (v2/cleanup-operation resource))))))
            out (outcome t)]
        (v2/cancel-task! t)
        (is (v2/cancelled? (ffirst @out)))
        (@release :closed)
        (pump! env)
        (is (= 1 @detached))
        (is (= 1 (count (runs w))) "ordinary physical operation still owes acknowledgement")
        (is (empty? (aget ^objects w rw/W-CLEANUP-WAITS)))
        (@ordinary :late)
        (pump! env)
        (is (empty? (runs w)))))))

(deftest cancellation-before-and-during-registration-does-not-restart-finalizer
  (doseq [when-cancel [:before :during :queued]]
    (let [{w :world :as env} (manual-world) events (atom [])
          previous (aget ^objects w rw/W-HOOK)
          cancel-run (fn [] (v2/call-in! w #(when-let [r (first (runs w))]
                                              (#'v2/cancel! w r :org.replikativ.spindel.v2.core/cancelled))))]
      (when (= when-cancel :before)
        (aset ^objects w rw/W-HOOK
              (fn [world item]
                (when (= :cleanup-wait (first item)) (cancel-run))
                (previous world item))))
      (binding [v2/*world* w]
        (let [t (task
                 (let [resource (v2/cleanup-resource
                                 (fn [cb]
                                   (is (not (hs/held? (aget ^objects w rw/W-LOCK))))
                                   (swap! events conj :register)
                                   (when (= when-cancel :during) (cancel-run))
                                   (cb :closed)
                                   (when (= when-cancel :queued) (cancel-run))
                                   (fn [] (swap! events conj :detach))))]
                   (try :body (finally (swap! events conj :enter)
                                       (await-finalization (v2/cleanup-operation resource))
                                       (swap! events conj :exit)))))
              out (outcome t)]
          (pump! env)
          (is (v2/cancelled? (ffirst @out)))
          (is (= [:enter :register :detach :exit] @events))
          (is (empty? (runs w))))))))

(deftest local-catch-can-recover-cleanup-failure-but-not-cancellation
  (let [{w :world :as env} (manual-world) complete (atom nil) events (atom [])]
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource (fn [cb] (reset! complete cb) nil))]
                 (try
                   (try :body
                        (finally
                          (try (await-finalization (v2/cleanup-operation resource))
                               (catch Throwable _ (swap! events conj :recovered)))
                          (swap! events conj :inner-exit)))
                   (swap! events conj :suffix)
                   (finally (swap! events conj :outer)))))
            out (outcome t)]
        (v2/cancel-task! t)
        (@complete (ex-info "recoverable close" {}) true)
        (pump! env)
        (is (v2/cancelled? (ffirst @out)))
        (is (= [:recovered :inner-exit :outer] @events))
        (is (empty? (aget ^objects w rw/W-CLEANUP-FAILURES)))
        (is (empty? (runs w)))))))

(deftest pending-and-queued-forks-fail-locally-without-subscribing-to-parent
  (doseq [queued? [false true]]
    (let [{w :world :as env} (manual-world)
          complete (atom nil) calls (atom 0) detached (atom 0)
          child (atom nil) events (atom [])]
      (binding [v2/*world* w]
        (let [t (task
                 (let [resource (v2/cleanup-resource (fn [cb] (swap! calls inc) (reset! complete cb)
                                                       #(swap! detached inc)))]
                   (try :body
                        (finally
                          (try (await-finalization (v2/cleanup-operation resource))
                               (catch Throwable e
                                 (swap! events conj [(aget ^objects (v2/cw) rw/ID)
                                                     (:spindel/forked (ex-data e))])))))))
              parent-out (outcome t)]
          (if queued?
            (let [previous (aget ^objects w rw/W-HOOK)]
              (aset ^objects w rw/W-HOOK
                    (fn [world item]
                      (when (and (= :cleanup-ready (first item)) (nil? @child))
                        (reset! child (v2/fork! world)))
                      (previous world item)))
              (@complete :closed)
              (pump! env))
            (do (reset! child (v2/fork! w))
                (v2/call-in! @child (fn [] nil))
                (pump! env)))
          (is (= [[:body false]] @(outcome (v2/in-world @child t))))
          (is (empty? (runs @child)))
          (is (= [[(aget ^objects @child rw/ID) true]] @events))
          (is (= 1 @calls))
          (when-not queued?
            (is (empty? @parent-out))
            (is (= 0 @detached))
            (is (= 1 (count (runs w))))
            (@complete :closed)
            (pump! env))
          (is (= [[:body false]] @parent-out))
          (is (= 1 @detached))
          (is (empty? (runs w))))))))

(deftest fork-of-unactivated-fork-keeps-local-failure-rule
  (let [{w :world :as env} (manual-world) complete (atom nil) events (atom [])]
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource (fn [cb] (reset! complete cb) nil))]
                 (try :body
                      (finally (try (await-finalization (v2/cleanup-operation resource))
                                    (catch Throwable e
                                      (swap! events conj [(aget ^objects (v2/cw) rw/ID)
                                                          (:spindel/forked (ex-data e))])))))))
            child (v2/fork! w)
            grandchild (v2/fork! child)]
        (v2/call-in! grandchild (fn [] nil))
        (pump! env)
        (is (= [[:body false]] @(outcome (v2/in-world child t))))
        (is (= [[:body false]] @(outcome (v2/in-world grandchild t))))
        (is (= #{[(aget ^objects child rw/ID) true] [(aget ^objects grandchild rw/ID) true]}
               (set @events)))
        (is (= 1 (count (runs w))))
        (@complete :closed)
        (pump! env)
        (is (empty? (runs w)))))))

(deftest world-release-preserves-admitted-cleanup-and-later-cleanup-waits
  (let [{w :world :as env} (manual-world) complete (atom nil) events (atom []) calls (atom 0)]
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource (fn [cb] (swap! calls inc) (reset! complete cb) nil))]
                 (try :body
                      (finally
                        (await-finalization (v2/cleanup-operation resource))
                        (swap! events conj :first)
                        (await-finalization (v2/cleanup-operation resource))
                        (swap! events conj :second)))))
            out (outcome t)
            remaining (v2/release-world! w)]
        (is (:spindel/released (ex-data (ffirst @out))))
        (is (= 1 (count (runs w))))
        (@complete :closed)
        (pump! env)
        (is (= [:first :second] @events))
        (is (= 1 @calls))
        (is (empty? (runs w)))
        (is (zero? (remaining)))))))

(deftest stale-predecessor-only-resumes-its-own-cleanup
  (let [{w :world :as env} (manual-world) callbacks (atom {}) events (atom [])]
    (binding [v2/*world* w]
      (let [signal (v2/signal 1)
            c (v2/spin
               (let [n (org.replikativ.spindel.incremental.interval/get-new (v2/track signal))
                     resource (v2/cleanup-resource (fn [cb] (swap! callbacks assoc n cb) nil))]
                 (try n (finally
                          (await-finalization (v2/cleanup-operation resource))
                          (swap! events conj n)))))
            out (outcome c)]
        (v2/write! signal 2)
        (is (= #{1 2} (set (keys @callbacks))))
        ((get @callbacks 1) :closed)
        (pump! env)
        (is (empty? @out) "stale cleanup cannot publish the old result")
        ((get @callbacks 2) :closed)
        (pump! env)
        (is (= [[2 false]] @out))
        (is (= [1 2] @events))
        (is (empty? (runs w)))))))

(deftest unborn-discard-runs-no-inherited-cleanup-or-detach
  (let [{w :world :as env} (manual-world)
        complete (atom nil) detached (atom 0) events (atom []) publication (atom nil)]
    (v2/install-handlers! w {:freeze #(reset! publication %)})
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource (fn [cb] (reset! complete cb) #(swap! detached inc)))]
                 (try :body (finally (await-finalization (v2/cleanup-operation resource))
                                     (swap! events conj :finalized)))))
            publisher (task (v2/savepoint :freeze nil))
            instance (v2/instantiate @publication)]
        (v2/discard! instance)
        (pump! env)
        (is (empty? @events))
        (is (zero? @detached))
        (is (empty? (runs instance)))
        (is (nil? (aget ^objects instance rw/W-CLEANUP-DORMANT)))
        (is (= 1 (count (aget ^objects w rw/W-CLEANUP-WAITS))))
        (@complete :closed)
        (pump! env)
        (is (= [[:body false]] @(outcome t)))
        (is (= [:finalized] @events))
        (is (= 1 @detached))
        (v2/abandon! @publication)
        (is (v2/cancelled? (ffirst @(outcome publisher))))))))

(deftest with-open-registers-real-cleanup-once
  (doseq [cancel? [false true]]
    (let [{w :world} (manual-world) closes (atom 0)]
      (binding [v2/*world* w]
        (let [gate (v2/deferred)
              closeable (proxy [java.io.StringReader] [""] (close [] (swap! closes inc)))
              t (task (with-open [r closeable] (if cancel? (await gate) :body)))
              out (outcome t)]
          (when cancel? (v2/cancel-task! t))
          (is (= 1 @closes))
          (if cancel? (is (v2/cancelled? (ffirst @out))) (is (= [[:body false]] @out)))
          (is (empty? (runs w))))))))

(deftest resource-declaration-and-arbitrary-await-targets-are-rejected-in-finalizer
  (doseq [kind [:resource :arbitrary]]
    (let [{w :world} (manual-world) invoked (atom false)]
      (binding [v2/*world* w]
        (let [t (task (try :body (finally
                                   (case kind
                                     :resource (v2/cleanup-resource (fn [_] (reset! invoked true)))
                                     :arbitrary (await-finalization {:looks :like-an-operation})))))
              error (first (:spindel/cleanup-failures (ex-data (ffirst @(outcome t)))))]
          (is (contains? #{:finalizer-effect :cleanup-operation} (:spindel/invalid (ex-data error))))
          (is (false? @invoked))
          (is (empty? (runs w))))))))

(defn- retained-result-fixture [mode]
  (let [jobs (atom [])
        w (v2/world {:executor (reify java.util.concurrent.Executor
                                 (execute [_ f] (swap! jobs conj f)))})
        env {:world w :jobs jobs}
        payload (byte-array (* 1024 1024))
        weak (java.lang.ref.WeakReference. payload)
        complete (atom nil) operation (atom nil)]
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource
                               (fn [cb] (assert (= (* 1024 1024) (alength payload)))
                                 (reset! complete cb) nil))
                     op (v2/cleanup-operation resource)]
                 (reset! operation op)
                 (try (if (= mode :error) (throw (ex-info "body" {})) :body)
                      (finally (await-finalization op)))))
            out (outcome t)]
        (when (= mode :cancel) (v2/cancel-task! t))
        (@complete :closed)
        (pump! env)
        {:weak weak :task t :callback @complete :operation @operation :world w :out out}))))

(defn- collected? [^java.lang.ref.WeakReference weak]
  (loop [n 0]
    (System/gc)
    (if (nil? (.get weak)) true
        (if (= n 50) false (do (Thread/sleep 10) (recur (inc n)))))))

(deftest held-result-terminal-operation-and-callback-release-close-payload
  (doseq [mode [:success :error :cancel]]
    (let [{:keys [weak task callback operation world out]} (retained-result-fixture mode)]
      (is (collected? weak) (str "held terminal artifacts retain close payload: " mode))
      (is (some? callback))
      (is (= :settled (:phase (v2/cleanup-operation-status operation))))
      (is (some? world))
      (is (= 1 (count @out)))
      (is (nil? (aget ^objects (v2/row-of task) rw/K-BODY)))
      (is (nil? (aget ^objects (v2/row-of task) rw/K-INPUTS)))
      (let [child (v2/fork! world)]
        (is (= @out @(outcome (v2/in-world child task))))
        (v2/discard! child)))))

(deftest adapter-registration-cannot-admit-ordinary-engine-work
  (let [{w :world :as env} (manual-world)]
    (binding [v2/*world* w]
      (let [t (task (let [resource (v2/cleanup-resource (fn [_] (v2/signal w :forbidden)))]
                      (try :body (finally (await-finalization (v2/cleanup-operation resource))))))
            out (outcome t)]
        (pump! env)
        (let [error (first (:spindel/cleanup-failures (ex-data (ffirst @out))))]
          (is (= :finalizer-effect (:spindel/invalid (ex-data error)))))
        (is (empty? (runs w)))))))

(deftest synchronous-completion-then-throw-cannot-resume-before-registration-returns
  (let [{w :world :as env} (manual-world) events (atom [])]
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource
                               (fn [cb]
                                 (swap! events conj :register-enter)
                                 (cb :closed)
                                 (is (= [:register-enter] @events))
                                 (swap! events conj :register-exit)
                                 (throw (ex-info "after completion" {}))))]
                 (try :body (finally (await-finalization (v2/cleanup-operation resource))
                                     (swap! events conj :cleanup-exit)))))
            out (outcome t)]
        (pump! env)
        (is (= [[:body false]] @out))
        (is (= [:register-enter :register-exit :cleanup-exit] @events))
        (is (empty? (runs w)))))))

(deftest cancellation-while-outer-finalizer-is-parked-preserves-both-exits
  (let [{w :world :as env} (manual-world) callbacks (atom {}) events (atom [])]
    (binding [v2/*world* w]
      (let [t (task
               (let [inner (v2/cleanup-resource (fn [cb] (swap! callbacks assoc :inner cb) nil))
                     outer (v2/cleanup-resource (fn [cb] (swap! callbacks assoc :outer cb) nil))]
                 (try
                   (try :body (finally (await-finalization (v2/cleanup-operation inner))
                                       (swap! events conj :inner)))
                   (finally (await-finalization (v2/cleanup-operation outer))
                            (swap! events conj :outer)))))
            out (outcome t)]
        ((get @callbacks :inner) :closed)
        (pump! env)
        (is (= [:inner] @events))
        (v2/cancel-task! t)
        ((get @callbacks :outer) :closed)
        (pump! env)
        (is (v2/cancelled? (ffirst @out)))
        (is (= [:inner :outer] @events))
        (is (empty? (runs w)))))))

(def cleanup-handler-calls (atom 0))

(v2/defeffect forbidden-cleanup-effect [_args _ctx]
  (swap! cleanup-handler-calls inc)
  [:value :forbidden])

(defn- hidden-custom-effect []
  (v2/custom-effect! 'org.replikativ.spindel.v2.cleanup-test/forbidden-cleanup-effect
                     [] :hidden identity identity))

(deftest ordinary-await-and-custom-effects-are-rejected-during-cancellation
  (doseq [kind [:await :track :external :sleep :spawn :spin :fork :savepoint :scope :custom :custom-helper]]
    (let [{w :world :as env} (manual-world)]
      (binding [v2/*world* w]
        (let [gate (v2/deferred) signal (v2/signal :value)
              t (task (try (await gate)
                           (finally
                             (cond
                               (= kind :await) (await gate)
                               (= kind :track) (v2/track signal)
                               (= kind :external) (v2/external (fn [_] (is false "unadmitted external")))
                               (= kind :sleep) (v2/sleep 1)
                               (= kind :spawn) (task :bad)
                               (= kind :spin) (v2/spin :bad)
                               (= kind :fork) (v2/fork)
                               (= kind :savepoint) (v2/savepoint :bad nil)
                               (= kind :scope) (v2/with-scope :bad)
                               (= kind :custom) (forbidden-cleanup-effect)
                               (= kind :custom-helper) (hidden-custom-effect)))))
              out (outcome t)]
          (v2/cancel-task! t)
          (pump! env)
          (is (v2/cancelled? (ffirst @out)))
          (is (zero? @cleanup-handler-calls))
          (is (= [:finalizer-effect]
                 (mapv (comp :spindel/invalid ex-data :error)
                       (vals (aget ^objects w rw/W-CLEANUP-FAILURES)))))
          (is (empty? (runs w))))))))

(def ^:dynamic *cleanup-context* {:lexical :ambient :world nil})

(defn capture-cleanup-context [value] (:lexical value))
(defn restore-cleanup-context [captured _runner]
  {:lexical captured :world (v2/cw)})

(ioc/register-binding-scope! 'org.replikativ.spindel.v2.cleanup-test/*cleanup-context*
                             'org.replikativ.spindel.v2.cleanup-test/capture-cleanup-context
                             'org.replikativ.spindel.v2.cleanup-test/restore-cleanup-context)

(defn- cleanup-scope-read [position]
  [position *cleanup-binding* (:lexical *cleanup-context*)
   (identical? (:world *cleanup-context*) (v2/cw)) (aget ^objects (v2/cw) rw/ID)])

(defn- complete-on-foreign-runner! [env complete]
  (let [foreign (v2/world) error (atom nil) after (atom nil)
        thread (Thread.
                (fn []
                  (binding [v2/*world* foreign *cleanup-binding* :runner
                            *cleanup-context* {:lexical :runner :world foreign}]
                    (try
                      (complete :closed)
                      (pump! env)
                      (reset! after [*cleanup-binding* (:lexical *cleanup-context*)
                                     (identical? foreign (:world *cleanup-context*)) (v2/cw)])
                      (catch Throwable e (reset! error e))))))]
    (.start thread)
    (.join thread)
    (is (nil? @error) (str "foreign runner failed: " @error))
    (is (= [:runner :runner true nil] @after) "cleanup scope must exit back to runner bindings")
    (v2/release-world! foreign)))

(deftest bindings-surrounding-try-enter-nested-finalizers-on-selected-runner
  (doseq [cancel? [false true]]
    (let [{w :world :as env} (manual-world) callbacks (atom {}) events (atom [])]
      (binding [v2/*world* w]
        (let [gate (v2/deferred)
              t (task
                 (let [inner (v2/cleanup-resource (fn [cb] (swap! callbacks assoc :inner cb) nil))
                       outer (v2/cleanup-resource (fn [cb] (swap! callbacks assoc :outer cb) nil))]
                   (binding [*cleanup-binding* :outer-scope
                             *cleanup-context* {:lexical :outer-scope :world (v2/cw)}]
                     (try
                       (binding [*cleanup-binding* :inner-scope
                                 *cleanup-context* {:lexical :inner-scope :world (v2/cw)}]
                         (try (await gate)
                              (finally
                                (swap! events conj (cleanup-scope-read :inner-before))
                                (await-finalization (v2/cleanup-operation inner))
                                (swap! events conj (cleanup-scope-read :inner-after)))))
                       (finally
                         (swap! events conj (cleanup-scope-read :outer-before))
                         (await-finalization (v2/cleanup-operation outer))
                         (swap! events conj (cleanup-scope-read :outer-after)))))))
              out (outcome t)
              wid (aget ^objects w rw/ID)]
          (if cancel? (v2/cancel-task! t) (v2/deliver! gate :body))
          (is (= [[:inner-before :inner-scope :inner-scope true wid]] @events))
          (complete-on-foreign-runner! env (get @callbacks :inner))
          (complete-on-foreign-runner! env (get @callbacks :outer))
          (is (= [[:inner-before :inner-scope :inner-scope true wid]
                  [:inner-after :inner-scope :inner-scope true wid]
                  [:outer-before :outer-scope :outer-scope true wid]
                  [:outer-after :outer-scope :outer-scope true wid]] @events))
          (if cancel? (is (v2/cancelled? (ffirst @out))) (is (= [[:body false]] @out)))
          (is (= :outer *cleanup-binding*))
          (is (empty? (runs w))))))))

(deftest copied-cleanup-entry-restores-lexical-data-with-child-origin
  (let [{w :world :as env} (manual-world) complete (atom nil) calls (atom 0)
        events (atom []) copied-errors (atom [])]
    (binding [v2/*world* w]
      (let [gate (v2/deferred)
            t (task
               (let [resource (v2/cleanup-resource (fn [cb] (swap! calls inc) (reset! complete cb) nil))]
                 (binding [*cleanup-binding* :fork-scope
                           *cleanup-context* {:lexical :fork-scope :world (v2/cw)}]
                   (try (await gate)
                        (finally
                          (swap! events conj (cleanup-scope-read :before))
                          (try (await-finalization (v2/cleanup-operation resource))
                               (catch Throwable e
                                 (swap! copied-errors conj [(aget ^objects (v2/cw) rw/ID)
                                                            (:spindel/forked (ex-data e))])))
                          (swap! events conj (cleanup-scope-read :after)))))))
            child (v2/fork! w)
            child-task (v2/in-world child t)
            child-out (outcome child-task)
            child-id (aget ^objects child rw/ID)
            parent-out (outcome t)]
        (v2/cancel-task! child-task)
        (pump! env)
        (is (v2/cancelled? (ffirst @child-out)))
        (is (= [[:before :fork-scope :fork-scope true child-id]
                [:after :fork-scope :fork-scope true child-id]] @events))
        (is (= [[child-id true]] @copied-errors))
        (is (zero? @calls) "a copied target cannot register its parent's close")
        (is (empty? (runs child)))
        (v2/cancel-task! t)
        (complete-on-foreign-runner! env @complete)
        (is (= 1 @calls))
        (is (v2/cancelled? (ffirst @parent-out)))
        (is (= [[:before :fork-scope :fork-scope true (aget ^objects w rw/ID)]
                [:after :fork-scope :fork-scope true (aget ^objects w rw/ID)]]
               (subvec @events 2)))
        (is (empty? (runs w)))))))

(defn- creation-snapshot [w publication instance]
  {:next (.get ^java.util.concurrent.atomic.AtomicLong (aget ^objects w rw/W-NEXT))
   :worlds (hs/msize (:worlds (aget ^objects w rw/W-FAMILY)))
   :basis-epoch (aget ^objects (:basis publication) rw/W-EPOCH)
   :publication @(:state publication)
   :unborn (aget ^objects instance rw/W-UNBORN)
   :activation (aget ^objects instance rw/W-PENDING-ACT)
   :activation-owner (aget ^objects instance rw/W-PUB-WORLD)
   :owned (when-let [owned (aget ^objects w rw/W-OWNED)]
            (mapv (fn [[id entry]]
                    [id (mapv (fn [holder]
                                [(some-> (aget ^objects holder 0) (aget rw/ID))
                                 (hs/flag? (aget ^objects holder 2))])
                              (aget ^objects entry 0))])
                  (hs/mentries owned)))})

(deftest callable-fork-and-savepoint-boundaries-refuse-before-mutation
  (doseq [cancel? [false true] kind [:instantiate :activate :resume :fork]]
    (let [{w :world :as env} (manual-world) publication (atom nil)
          snapshots (atom nil) refusal (atom nil)]
      (v2/install-handlers! w {:seed #(reset! publication %)})
      (binding [v2/*world* w]
        (let [publisher (task (v2/savepoint :seed :pending))
              instance (v2/instantiate @publication)
              gate (v2/deferred)
              t (task
                 (try (if cancel? (await gate) :body)
                      (finally
                        (let [before (creation-snapshot w @publication instance)]
                          (try
                            (case kind
                              :instantiate (v2/instantiate @publication)
                              :activate (v2/activate! instance :forbidden)
                              :resume (v2/resume! @publication :forbidden)
                              :fork (v2/fork! w))
                            (catch Throwable e (reset! refusal e)))
                          (reset! snapshots [before (creation-snapshot w @publication instance)])))))
              out (outcome t)]
          (when cancel? (v2/cancel-task! t))
          (pump! env)
          (is (= :finalizer-effect (:spindel/invalid (ex-data @refusal))))
          (is (= (first @snapshots) (second @snapshots)) (str "creation/activation changed state: " kind))
          (is (= :pending @(:state @publication)))
          (is (true? (aget ^objects instance rw/W-UNBORN)))
          (if cancel? (is (v2/cancelled? (ffirst @out))) (is (= [[:body false]] @out)))
          (v2/discard! instance)
          (v2/abandon! @publication)
          (is (v2/cancelled? (ffirst @(outcome publisher)))))))))

(deftest adapter-registration-cannot-create-or-activate-worlds
  (doseq [cancel? [false true] kind [:fork :instantiate :activate :resume]]
    (let [{w :world :as env} (manual-world) publication (atom nil)
          snapshots (atom nil) refusal (atom nil)]
      (v2/install-handlers! w {:seed #(reset! publication %)})
      (binding [v2/*world* w]
        (let [publisher (task (v2/savepoint :seed :pending))
              instance (v2/instantiate @publication)
              gate (v2/deferred)
              t (task
                 (let [resource
                       (v2/cleanup-resource
                        (fn [_]
                          (is (nil? (v2/active-run)))
                          (is (not (hs/held? (aget ^objects w rw/W-LOCK))))
                          (let [before (creation-snapshot w @publication instance)]
                            (try
                              (case kind
                                :fork (v2/fork! w)
                                :instantiate (v2/instantiate @publication)
                                :activate (v2/activate! instance :forbidden)
                                :resume (v2/resume! @publication :forbidden))
                              (catch Throwable e (reset! refusal e) (throw e))
                              (finally (reset! snapshots [before (creation-snapshot w @publication instance)]))))))]
                   (try (if cancel? (await gate) :body)
                        (finally (await-finalization (v2/cleanup-operation resource))))))
              out (outcome t)]
          (when cancel? (v2/cancel-task! t))
          (pump! env)
          (is (= :finalizer-effect (:spindel/invalid (ex-data @refusal))))
          (is (= (first @snapshots) (second @snapshots)) (str "registration admitted ordinary work: " kind))
          (if cancel?
            (do (is (v2/cancelled? (ffirst @out)))
                (is (= [@refusal] (mapv :error (v2/call-in! w #(#'v2/take-cleanup-report! w))))))
            (is (= [@refusal] (:spindel/cleanup-failures (ex-data (ffirst @out))))))
          (v2/discard! instance)
          (v2/abandon! @publication)
          (is (v2/cancelled? (ffirst @(outcome publisher)))))))))

(defn- cleanup-failure-payload-fixture [env mode]
  (let [w (:world env) public (byte-array 65536) private (byte-array 65536)
        public-weak (java.lang.ref.WeakReference. public)
        private-weak (java.lang.ref.WeakReference. private)
        error (ex-info "physical close failed" {:payload public})
        complete (atom nil) operation (atom nil) detached (atom 0)]
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource
                               (fn [cb]
                                 (reset! complete cb)
                                 (fn [] (swap! detached + (alength private)))))
                     op (v2/cleanup-operation resource)]
                 (reset! operation op)
                 (try :body (finally (await-finalization op)))))
            out (outcome t)]
        (when (= mode :cancel) (v2/cancel-task! t))
        (@complete error true)
        (pump! env)
        (is (= 65536 @detached))
        {:public public-weak :private private-weak
         :holder (atom {:task t :result @out :operation @operation :callback @complete})}))))

(defn- report-count [w]
  (v2/call-in! w #(:unreported-failures (#'v2/cleanup-diagnostics* w))))

(defn- all-live? [weaks]
  (every? (fn [^java.lang.ref.WeakReference r] (some? (.get r))) weaks))

(defn- collected-many? [weaks]
  (loop [n 0]
    (System/gc)
    (if (every? (fn [^java.lang.ref.WeakReference r] (nil? (.get r))) weaks)
      true
      (if (= n 50) false (do (Thread/sleep 10) (recur (inc n)))))))

(deftest canceled-cleanup-errors-retain-only-current-unconsumed-report-payloads
  (let [{w :world :as env} (manual-world false)]
    (dotimes [_round 3]
      (let [fixtures (mapv (fn [_] (cleanup-failure-payload-fixture env :cancel)) (range 12))
            public (mapv :public fixtures) private (mapv :private fixtures)]
        ;; Keep canceled results, but drop the optional terminal error observers.
        (doseq [f fixtures] (swap! (:holder f) select-keys [:task :result]))
        (is (= 12 (report-count w)))
        (is (= 12 (report-count w)) "diagnostic reads cannot consume failures")
        (is (all-live? public) "unreported close failures remain actual retention obligations")
        (is (collected-many? private) "reports must not retain registration/detach payloads")
        (let [reports (atom (v2/call-in! w #(#'v2/take-cleanup-report! w)))]
          (is (= 12 (count @reports)))
          (is (zero? (report-count w)))
          (is (all-live? public) "a held returned report owns its public error payloads")
          (reset! reports nil)
          (is (collected-many? public) "acknowledged reports collect with world and canceled results held"))
        (doseq [f fixtures]
          (is (v2/cancelled? (ffirst (:result @(:holder f)))))
          (is (nil? (aget ^objects (v2/row-of (:task @(:holder f))) rw/K-RUN)))))
      (is (zero? (report-count w))))))

(deftest normal-cleanup-failure-does-not-create-a-global-error-history
  (let [{w :world :as env} (manual-world false)]
    (dotimes [_round 3]
      (let [fixtures (mapv (fn [_] (cleanup-failure-payload-fixture env :normal)) (range 12))]
        (is (zero? (report-count w)))
        (doseq [f fixtures]
          (swap! (:holder f) select-keys [:task :result])
          (is (seq (:spindel/cleanup-failures (ex-data (ffirst (:result @(:holder f))))))))
        (is (all-live? (mapv :public fixtures)) "held failed results intentionally retain their public error")
        (is (collected-many? (mapv :private fixtures)))
        (doseq [f fixtures] (reset! (:holder f) nil))
        (is (collected-many? (mapv :public fixtures)) "world does not keep delivered errors after results drop")
        (is (zero? (report-count w)))))))

(deftest failure-terminal-operation-and-callback-release-private-registration-captures
  (let [{w :world :as env} (manual-world false)
        {:keys [public private holder]} (cleanup-failure-payload-fixture env :normal)]
    (swap! holder select-keys [:operation :callback])
    (is (zero? (report-count w)))
    (is (= :settled (:phase (v2/cleanup-operation-status (:operation @holder)))))
    (is (collected? private))
    (is (all-live? [public]) "the public terminal error is still observed by the held operation/callback")
    (reset! holder nil)
    (is (collected? public) "dropping public terminal observers permits collection without dropping world")))
