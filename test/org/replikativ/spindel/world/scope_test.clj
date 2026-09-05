(ns org.replikativ.spindel.world.scope-test
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.world.scope :as scope]
            [org.replikativ.spindel.yggdrasil :as ygg]))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %])
               #(deliver result [:error %]))
    (let [[status value :as outcome] (deref result 5000 ::timeout)]
      (when (= ::timeout outcome)
        (throw (ex-info "CPS operation timed out" {})))
      (if (= :ok status) value (throw value)))))

(defn- fork! [world-scope source]
  (let [result (promise)]
    (scope/fork! world-scope source
                 #(deliver result [:ok %])
                 #(deliver result [:error %]))
    (let [[status value :as outcome] (deref result 5000 ::timeout)]
      (when (= ::timeout outcome)
        (throw (ex-info "World fork timed out" {})))
      (if (= :ok status) value (throw value)))))

(deftest generic-scope-owns-quiescence-and-affine-discard
  (let [root (context/create-execution-context)
        world-scope (scope/create {:purpose :search
                                   :fork-opts {:systems :none}})
        generation (scope/begin-activity! world-scope :generation)
        world (binding [ec/*execution-context* root]
                (fork! world-scope root))
        handle (first (:handles @world-scope))
        child (:child-ctx world)
        quiescent (promise)]
    (try
      (is (:admitted?
           (scope/exchange-activity!
            world-scope generation
            [{:id (:fork-id child) :kind :context :value child}])))
      ((scope/await-quiescence world-scope)
       #(deliver quiescent %)
       #(deliver quiescent %))
      (is (= ::pending (deref quiescent 20 ::pending)))
      (is (= :search (:fork/purpose (:descriptor world))))

      (testing "cancellation is only a request until the client proves quiescence"
        (scope/request-cancel! world-scope)
        (is (ygg/open-fork? handle))
        (scope/end-activity! world-scope (:fork-id child))
        (is (nil? (deref quiescent 5000 ::timeout)))
        (await-cps (scope/discard-when-quiescent! world-scope)))

      (is (= :discarded (:status @world-scope)))
      (is (empty? (:handles @world-scope)))
      (is (= 1 (count (scope/descriptors world-scope))))
      (is (= :search (:fork/purpose (first (scope/descriptors world-scope)))))
      (is (not (ygg/open-fork? handle)))

      (testing "a consumed scope cannot leak a later fork"
        (let [outcome (try
                        (binding [ec/*execution-context* root]
                          (fork! world-scope root))
                        :unexpected-success
                        (catch Throwable error error))]
          (is (= ::scope/scope-consumed (:type (ex-data outcome))))
          (is (empty? (:handles @world-scope)))))
      (finally
        (when (ygg/open-fork? handle)
          (binding [ec/*execution-context* root]
            (ygg/discard-fork! handle)))
        (context/stop-context! child)
        (context/stop-context! root)))))

(deftest quiescence-closes-admission-atomically
  (let [world-scope (scope/create {:purpose :search})]
    (is (nil? (await-cps (scope/await-quiescence world-scope))))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"closed world scope"
         (scope/begin-activity! world-scope :late-work)))))

(deftest discard-rejects-live-activity-without-consuming-the-scope
  (let [world-scope (scope/create {:purpose :search})
        activity (scope/begin-activity! world-scope :evaluation)
        outcome (try
                  (await-cps (scope/discard! world-scope))
                  :unexpected-success
                  (catch Throwable error error))]
    (is (= ::scope/scope-busy (:type (ex-data outcome))))
    (is (= :open (:status @world-scope)))
    (scope/end-activity! world-scope activity)
    (is (nil? (await-cps (scope/discard! world-scope))))
    (is (= :discarded (:status @world-scope)))))

(deftest successful-callback-exceptions-are-not-reinterpreted-as-rejections
  (let [root (context/create-execution-context)
        child (context/create-execution-context)
        world-scope (scope/create {:purpose :search})
        activity (scope/begin-activity! world-scope :construction)
        callback-error (ex-info "callback failed" {:stage :continuation})]
    (try
      (with-redefs [ygg/fork! (fn [_opts]
                                (fn [resolve _reject]
                                  (resolve {:child-ctx child})))
                    ygg/fork-descriptor (constantly {:fork/id :synthetic})]
        (is (thrown-with-msg?
             clojure.lang.ExceptionInfo
             #"callback failed"
             (binding [ec/*execution-context* root]
               (scope/fork! world-scope root
                            (fn [_] (throw callback-error))
                            (fn [error] (throw error)))))))
      (finally
        ;; The synthetic handle carries no settlement authority.
        (swap! world-scope assoc :handles [])
        (scope/end-activity! world-scope activity)
        (context/stop-context! child)
        (context/stop-context! root)))))

(deftest activity-exchange-cannot-overwrite-another-lease
  (let [world-scope (scope/create {:purpose :search})
        source (scope/begin-activity! world-scope :source)
        existing (scope/begin-activity! world-scope :existing)
        outcome (try
                  (scope/exchange-activity!
                   world-scope source
                   [{:id existing :kind :replacement}])
                  :unexpected-success
                  (catch Throwable error error))]
    (is (= ::scope/activity-id-collision (:type (ex-data outcome))))
    (is (= 2 (count (:activities @world-scope))))
    (scope/end-activity! world-scope source)
    (scope/end-activity! world-scope existing)
    (is (nil? (await-cps (scope/discard! world-scope))))))

(deftest discard-callback-exceptions-do-not-corrupt-settlement
  (let [world-scope (scope/create {:purpose :search})
        activity (scope/begin-activity! world-scope :work)
        callback-error (ex-info "discard callback failed" {})]
    (scope/end-activity! world-scope activity)
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"discard callback failed"
         ((scope/discard! world-scope)
          (fn [_] (throw callback-error))
          (fn [error] (throw error)))))
    (is (= :discarded (:status @world-scope)))
    (is (nil? (await-cps (scope/discard! world-scope))))))

(deftest quiescence-readers-are-released-only-by-a-committed-transition
  (let [world-scope (scope/create {:purpose :search})
        old-activity (scope/begin-activity! world-scope :old)
        quiescent (promise)
        transition-entered (promise)
        release-transition (promise)
        armed? (atom false)]
    ((scope/await-quiescence world-scope)
     #(deliver quiescent [:ok %])
     #(deliver quiescent [:error %]))
    ;; Atom validators run after swap!'s function has selected a candidate but
    ;; before compare-and-set. Hold the empty/quiescent candidate while another
    ;; activity wins the CAS, forcing the completion function to retry.
    (set-validator!
     world-scope
     (fn [state]
       (when (and @armed? (:quiescent? state))
         (deliver transition-entered true)
         @release-transition)
       true))
    (reset! armed? true)
    (let [ending (future (scope/end-activity! world-scope old-activity))]
      (is (= true (deref transition-entered 5000 ::timeout)))
      (let [new-activity (scope/begin-activity! world-scope :new)]
        (deliver release-transition true)
        (is (nil? (deref ending 5000 ::timeout)))
        (is (= ::pending (deref quiescent 50 ::pending))
            "a failed quiescence CAS must not release captured readers")
        (scope/end-activity! world-scope new-activity)
        (is (= [:ok nil] (deref quiescent 5000 ::timeout)))))))

(deftest quiescence-reader-failure-does-not-orphan-other-readers
  (let [world-scope (scope/create {:purpose :search})
        activity (scope/begin-activity! world-scope :work)
        callback-error (ex-info "quiescence callback failed" {})
        second-reader (promise)]
    ((scope/await-quiescence world-scope)
     (fn [_] (throw callback-error))
     (fn [error] (throw error)))
    ((scope/await-quiescence world-scope)
     #(deliver second-reader [:ok %])
     #(deliver second-reader [:error %]))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo
         #"quiescence callback failed"
         (scope/end-activity! world-scope activity)))
    (is (= [:ok nil] (deref second-reader 5000 ::timeout))
        "one continuation exception must not strand later subscribers")
    (is (nil? (await-cps (scope/discard! world-scope))))))

(deftest concurrent-discard-completes-each-subscriber-once
  (let [world-scope (scope/create {:purpose :search})
        token (random-uuid)
        handle (ygg/->ForkHandle nil nil (random-uuid) {:fork/id :test}
                                 (atom {:status :open :token token}) token)
        physical-callbacks (promise)
        callback-counts (atom [0 0])
        invoke (fn [idx]
                 ((scope/discard! world-scope)
                  (fn [_] (swap! callback-counts update idx inc))
                  (fn [_] (swap! callback-counts update idx inc))))]
    (swap! world-scope assoc :handles [handle])
    (with-redefs [ygg/discard-fork!
                  (fn [_handle _opts]
                    (fn [resolve reject]
                      (deliver physical-callbacks [resolve reject])))]
      (invoke 0)
      (is (= :discarding (:status @world-scope)))
      (invoke 1)
      (let [[resolve _reject] (deref physical-callbacks 5000 ::timeout)]
        (is (fn? resolve))
        (resolve nil))
      (is (= [1 1] @callback-counts)
          "one physical cleanup completes every subscriber exactly once")
      (is (= :discarded (:status @world-scope)))
      (is (nil? (await-cps (scope/discard! world-scope)))))))

(deftest activity-results-agree-with-the-committed-scope-state-after-retry
  (testing "begin neither loses a committed lease ID nor reports a phantom lease"
    (let [world-scope (scope/create {:purpose :search})
          entered (promise)
          release-transition (promise)
          armed? (atom false)]
      (swap! world-scope assoc :status :discarding)
      (set-validator!
       world-scope
       (fn [state]
         (when (and @armed? (= :discarding (:status state)))
           (deliver entered true)
           @release-transition)
         true))
      (reset! armed? true)
      (let [outcome (future
                      (try
                        [:ok (scope/begin-activity! world-scope :work)]
                        (catch Throwable error [:error error])))]
        ;; A pure CAS implementation may reject without proposing the unchanged
        ;; state. The old retry-side-effect implementation enters the validator;
        ;; reopen it to make that stale error observable after its successful retry.
        (when (= true (deref entered 200 ::not-entered))
          (swap! world-scope assoc :status :open)
          (deliver release-transition true))
        (when-not (realized? release-transition)
          (swap! world-scope assoc :status :open)
          (deliver release-transition true))
        (let [completed (deref outcome 5000 ::timeout)
              _ (is (not= ::timeout completed))
              [status value] (when (vector? completed) completed)
              work-ids (->> (:activities @world-scope)
                            (keep (fn [[id activity]]
                                    (when (= :work (:kind activity)) id)))
                            set)]
          (if (= :ok status)
            (is (contains? work-ids value))
            (is (empty? work-ids)
                "a rejected begin must not have committed an unreachable lease"))
          (doseq [id work-ids] (scope/end-activity! world-scope id))
          (is (nil? (await-cps (scope/discard! world-scope))))))))

  (testing "exchange cannot commit replacements and then throw a stale collision"
    (let [world-scope (scope/create {:purpose :search})
          source (scope/begin-activity! world-scope :source)
          collision (scope/begin-activity! world-scope :collision)
          entered (promise)
          release-transition (promise)
          armed? (atom false)]
      (set-validator!
       world-scope
       (fn [state]
         (when (and @armed?
                    (contains? (:activities state) source)
                    (contains? (:activities state) collision))
           (deliver entered true)
           @release-transition)
         true))
      (reset! armed? true)
      (let [outcome (future
                      (try
                        [:ok (scope/exchange-activity!
                              world-scope source
                              [{:id collision :kind :replacement}])]
                        (catch Throwable error [:error error])))]
        (when (= true (deref entered 200 ::not-entered))
          (scope/end-activity! world-scope collision)
          (deliver release-transition true))
        (when-not (realized? release-transition)
          (deliver release-transition true))
        (let [completed (deref outcome 5000 ::timeout)
              _ (is (not= ::timeout completed))
              [status value] (when (vector? completed) completed)
              replacement? (= :replacement
                              (get-in @world-scope
                                      [:activities collision :kind]))]
          (if (= :ok status)
            (do
              (is (:admitted? value))
              (is replacement?))
            (is (not replacement?)
                "a rejected exchange must not commit replacement leases"))
          (doseq [id (keys (:activities @world-scope))]
            (scope/end-activity! world-scope id))
          (is (nil? (await-cps (scope/discard! world-scope)))))))))
