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

(defn- manual-world []
  (let [jobs (atom []) divergences (atom [])]
    (let [env {:world (v2/world {:verify? true :hook (verify/checking-hook divergences)
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
                             (case kind
                               :await (await gate)
                               :track (v2/track signal)
                               :external (v2/external (fn [_] (is false "unadmitted external")))
                               :sleep (v2/sleep 1)
                               :spawn (task :bad)
                               :spin (v2/spin :bad)
                               :fork (v2/fork)
                               :savepoint (v2/savepoint :bad nil)
                               :scope (v2/with-scope :bad)
                               :custom (forbidden-cleanup-effect)
                               :custom-helper (hidden-custom-effect)))))
              out (outcome t)]
          (v2/cancel-task! t)
          (pump! env)
          (is (v2/cancelled? (ffirst @out)))
          (is (zero? @cleanup-handler-calls))
          (is (= [:finalizer-effect]
                 (mapv (comp :spindel/invalid ex-data :error)
                       (vals (aget ^objects w rw/W-CLEANUP-FAILURES)))))
          (is (empty? (runs w))))))))
