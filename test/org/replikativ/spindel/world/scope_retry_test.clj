(ns org.replikativ.spindel.world.scope-retry-test
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.world.scope :as scope]
            [org.replikativ.spindel.yggdrasil :as ygg]))

(defn- start-discard [world-scope]
  (let [result (promise)
        worker (future
                 ((scope/discard! world-scope)
                  #(deliver result [:ok %])
                  #(deliver result [:error %])))]
    {:result result :worker worker}))

(defn- await-result [{:keys [result worker]}]
  (let [outcome (deref result 5000 ::timeout)]
    (is (not= ::timeout outcome))
    (is (not= ::timeout (deref worker 5000 ::timeout)))
    outcome))

(defn- wait-until [pred timeout-ms]
  (let [deadline (+ (System/currentTimeMillis) timeout-ms)]
    (loop []
      (cond
        (pred) true
        (< (System/currentTimeMillis) deadline)
        (do (Thread/sleep 5) (recur))
        :else false))))

(deftest failed-discard-closes-its-cleanup-generation-before-retry
  (let [world-scope (scope/create {:purpose :retry-test})
        token (random-uuid)
        handle (ygg/->ForkHandle nil nil (random-uuid) {:fork/id :test}
                                 (atom {:status :open :token token}) token)
        failure (ex-info "first discard failed" {})
        transition-entered (promise)
        release-transition (promise)
        block-first-failure? (atom true)
        discard-calls (atom 0)
        second-discard-invoked (promise)]
    (swap! world-scope assoc :handles [handle])
    (set-validator!
     world-scope
     (fn [state]
       (when (and (= :open (:status state))
                  (identical? failure (:error state))
                  (compare-and-set! block-first-failure? true false))
         (deliver transition-entered true)
         @release-transition)
       true))
    (try
      (with-redefs [ygg/discard-fork!
                    (fn [_handle _opts]
                      (let [call (swap! discard-calls inc)]
                        (fn [resolve reject]
                          (if (= 1 call)
                            (reject failure)
                            (do
                              (deliver second-discard-invoked true)
                              (resolve nil))))))]
        (let [first-attempt (start-discard world-scope)]
          (is (= true (deref transition-entered 5000 ::timeout)))
          (let [joined-attempt (start-discard world-scope)]
            (is (= ::pending
                   (deref second-discard-invoked 100 ::pending))
                "a retry cannot start while the failed generation is unpublished")
            (deliver release-transition true)
            (is (= [:error failure] (await-result first-attempt)))
            (is (= [:error failure] (await-result joined-attempt)))
            (is (= 1 @discard-calls))
            (is (= :open (:status @world-scope)))
            (is (= [:ok nil]
                   (await-result (start-discard world-scope))))
            (is (= true
                   (deref second-discard-invoked 5000 ::timeout)))
            (is (= 2 @discard-calls))
            (is (= :discarded (:status @world-scope))))))
      (finally
        (deliver release-transition true)
        (set-validator! world-scope nil)))))

(deftest busy-discard-does-not-create-a-shared-cleanup-generation
  (let [world-scope (scope/create {:purpose :busy-retry-test})
        activity (scope/begin-activity! world-scope :work)
        [status error] (await-result (start-discard world-scope))]
    (is (= :error status))
    (is (= ::scope/scope-busy (:type (ex-data error))))
    (is (= :open (:status @world-scope)))
    (is (not (contains? @world-scope :discard-readers)))
    (scope/end-activity! world-scope activity)
    (is (= [:ok nil] (await-result (start-discard world-scope))))
    (is (= :discarded (:status @world-scope)))))

(deftest cancellation-after-a-busy-attempt-remains-live
  (let [world-scope (scope/create {:purpose :cancel-retry-test})
        activity (scope/begin-activity! world-scope :work)
        [status error] (await-result (start-discard world-scope))]
    (is (= :error status))
    (is (= ::scope/scope-busy (:type (ex-data error))))
    (scope/end-activity! world-scope activity)
    (scope/request-cancel! world-scope)
    (is (wait-until #(= :discarded (:status @world-scope)) 5000))
    (is (true? (:cancel-requested? @world-scope)))
    (is (empty? (:handles @world-scope)))))
