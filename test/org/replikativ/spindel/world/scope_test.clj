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
