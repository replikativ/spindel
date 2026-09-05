(ns org.replikativ.spindel.search.mcts-test
  (:require [clojure.test :refer [deftest is]]
            #?(:clj [clojure.edn :as edn]
               :cljs [cljs.reader :as edn])
            [org.replikativ.spindel.atom :as ratom]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.search.mcts :as mcts]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.test-helpers :refer [async run-spin! with-ctx]]
            [org.replikativ.spindel.world.scope :as world-scope]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [yggdrasil.protocols :as yp])
  #?(:cljs (:require-macros [org.replikativ.spindel.test-helpers
                             :refer [async with-ctx]])))

(defrecord SharedSystem [id]
  yp/SystemIdentity
  (system-id [_] id)
  (system-type [_] :shared-test)
  (capabilities [_] nil))

(deftest uct-prefers-unvisited-and-then-value
  (is (= ##Inf (mcts/uct-score 10 {:visits 0 :value-total 0.0} 1.0)))
  (is (> (mcts/uct-score 10 {:visits 2 :value-total 2.0} 1.0)
         (mcts/uct-score 10 {:visits 2 :value-total 0.0} 1.0))))

(deftest owned-context-evaluation-completes
  (async done
         (with-ctx [runtime]
           (let [scope (world-scope/create {:purpose :test})
                 search-activity (world-scope/begin-activity! scope :test/search)
                 finish! (fn []
                           (world-scope/end-activity! scope search-activity)
                           (done))]
             (run-spin!
              (spin
               (await (#'mcts/context-call scope runtime :test/value
                                           (constantly 42))))
              (fn [result]
                (is (= 42 result))
                (finish!))
              (fn [error]
                (is false (str "owned context evaluation failed: " error))
                (finish!)))))))

(deftest search-is-deterministic-bounded-and-does-not-apply-the-winner
  (async done
         (with-ctx [_runtime]
           (let [ambient (ratom/atom [])
                 environment
                 {:actions (fn [state] (if (:terminal? state) [] [:bad :good]))
                  :transition (fn [_state action]
                                (swap! ambient conj action)
                                {:terminal? true :action action})
                  :terminal? (fn [state] (:terminal? state))
                  :reward (fn [state] (if (= :good (:action state)) 1.0 0.0))}
                 options {:max-simulations 24
                          :max-depth 3
                          :max-nodes 3
                          :seed :repeatable}]
             (run-spin!
              (spin
               [(await (mcts/search environment {:terminal? false} options))
                (await (mcts/search environment {:terminal? false} options))])
              (fn [[first-result second-result]]
                (is (= :good (:search/selected-action first-result)))
                (is (= (dissoc first-result :world/descriptors :search/nodes)
                       (dissoc second-result :world/descriptors :search/nodes)))
                (is (= first-result (edn/read-string (pr-str first-result)))
                    "the complete result round-trips as cross-runtime data")
                (is (= 24 (:search/simulations first-result)))
                (is (<= (:search/node-count first-result) 3))
                (is (empty? @ambient)
                    "all transition mutations remained in discarded worlds")
                (is (seq (:world/descriptors first-result)))
                (is (every? #(= :discarded (:fork/status %))
                            (:world/descriptors first-result)))
                (is (every? #(not= :open
                                   (get-in % [:world/descriptor :fork/status]))
                            (:search/nodes first-result)))
                (done))
              (fn [error]
                (is false (str "deterministic search failed: " error))
                (done)))))))

(deftest external-resource-predicate-can-stop-before-count-limit
  (async done
         (with-ctx [_runtime]
           (run-spin!
            (mcts/search
             {:actions (constantly [:only])
              :transition (fn [state _] (inc state))
              :terminal? (constantly false)
              :reward double}
             0
             {:max-simulations 100
              :max-depth 2
              :max-nodes 4
              :continue? #(< (:simulations %) 7)})
            (fn [result]
              (is (= 7 (:search/simulations result)))
              (is (= :completed (:search/status result)))
              (done))
            (fn [error]
              (is false (str "resource-bounded search failed: " error))
              (done))))))

(deftest node-cap-search-continues-through-retained-children
  (async done
         (with-ctx [_runtime]
           (run-spin!
            (mcts/search
             {:actions (fn [state] (if (:terminal? state) [] [:first :second]))
              :transition (fn [_ action] {:terminal? true :action action})
              :terminal? (fn [state] (:terminal? state))
              :reward (constantly 1.0)}
             {:terminal? false}
             {:max-simulations 20 :max-depth 2 :max-nodes 2 :seed :node-cap})
            (fn [result]
              (let [child (first (remove #(nil? (:node/action %))
                                         (:search/nodes result)))]
                (is (= 20 (:search/simulations result)))
                (is (= 2 (:search/node-count result)))
                (is (> (:node/visits child) 1)
                    "simulations descend through the retained child after saturation"))
              (done))
            (fn [error]
              (is false (str "node-cap search failed: " error))
              (done))))))

(deftest shared-systems-are-rejected-before-speculative-callbacks
  (async done
         (with-ctx [_runtime]
           (ygg/register! (->SharedSystem :ambient-only))
           (let [transitions (atom 0)]
             (run-spin!
              (mcts/search
               {:actions (constantly [:attempt])
                :transition (fn [state _] (swap! transitions inc) state)
                :terminal? (constantly false)
                :reward (constantly 0.0)}
               :root
               {:max-simulations 1 :max-depth 2 :max-nodes 2})
              (fn [result]
                (is false (str "shared expansion unexpectedly succeeded: " result))
                (done))
              (fn [error]
                (is (= ::mcts/shared-world-systems (:type (ex-data error))))
                (is (= :expansion (:phase (ex-data error))))
                (is (zero? @transitions))
                (done)))))))

(deftest shared-systems-are-rejected-before-rollout-callbacks
  (async done
         (with-ctx [_runtime]
           (ygg/register! (->SharedSystem :ambient-only))
           (let [terminal-checks (atom 0)]
             (run-spin!
              (mcts/search
               {:actions (constantly [:attempt])
                :transition (fn [state _] state)
                :terminal? (fn [_] (swap! terminal-checks inc) false)
                :reward (constantly 0.0)}
               :root
               {:max-simulations 1 :max-depth 2 :max-nodes 1})
              (fn [result]
                (is false (str "shared rollout unexpectedly succeeded: " result))
                (done))
              (fn [error]
                (is (= ::mcts/shared-world-systems (:type (ex-data error))))
                (is (= :rollout (:phase (ex-data error))))
                (is (= 1 @terminal-checks)
                    "only the observational root check ran before rejection")
                (done)))))))

(deftest synchronous-spawn-rejection-releases-evaluation-lease
  (async done
         (with-ctx [runtime]
           (let [scope (world-scope/create {:purpose :test})
                 search-activity (world-scope/begin-activity! scope :test/search)]
             (with-redefs [org.replikativ.spindel.spin.sync/spawn!
                           (fn
                             ([_]
                              (throw (ex-info "spawn rejected" {})))
                             ([_ _]
                              (throw (ex-info "spawn rejected" {}))))]
               (run-spin!
                (spin
                 (await (#'mcts/context-call scope runtime :test/rejection
                                             (constantly 42))))
                (fn [result]
                  (is false (str "spawn unexpectedly succeeded: " result))
                  (world-scope/end-activity! scope search-activity)
                  #?(:clj (done) :cljs (js/setTimeout done 0)))
                (fn [error]
                  (is (re-find #"spawn rejected" (str error)))
                  (is (empty? (world-scope/activity-values
                               scope :mcts/evaluation)))
                  (world-scope/end-activity! scope search-activity)
                  ;; A synchronous rejection reaches this callback before
                  ;; `with-redefs` restores the CLJS Var. Defer completion so
                  ;; cljs.test cannot start the next test against the stub.
                  #?(:clj (done) :cljs (js/setTimeout done 0)))))))))

(deftest terminal-root-produces-no-selected-action
  (async done
         (with-ctx [_runtime]
           (run-spin!
            (mcts/search
             {:actions (fn [_]
                         (throw (ex-info "terminal actions evaluated" {})))
              :transition (fn [state _] state)
              :terminal? (constantly true)
              :reward (constantly 0.75)}
             :done
             {:max-simulations 2 :seed :terminal})
            (fn [result]
              (is (nil? (:search/selected-action result)))
              (is (= 2 (:search/simulations result)))
              (is (= 1 (:search/node-count result)))
              (is (= 0.75 (get-in result [:search/root :mean-value])))
              (is (empty? (:world/descriptors result)))
              (done))
            (fn [error]
              (is false (str "terminal-root search failed: " error))
              (done))))))

(deftest invalid-environment-is-rejected-before-world-work
  (is (thrown-with-msg?
       #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
       #":continue\? must be a function"
       (mcts/search {:actions (constantly [])
                     :transition (fn [state _] state)
                     :terminal? (constantly true)
                     :reward (constantly 0.0)}
                    :root
                    {:continue? :not-a-function})))
  (is (thrown-with-msg?
       #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
       #":rollout-action must be a function"
       (mcts/search {:actions (constantly [])
                     :transition (fn [state _] state)
                     :terminal? (constantly true)
                     :reward (constantly 0.0)
                     :rollout-action :not-a-function}
                    :root))))

#?(:clj
   (deftest mutable-search-keys-are-rejected-before-world-work
     (is (thrown-with-msg?
          clojure.lang.ExceptionInfo
          #"seed must be immutable cross-runtime data"
          (mcts/search {:actions (constantly [])
                        :transition (fn [state _] state)
                        :terminal? (constantly true)
                        :reward (constantly 0.0)}
                       :root
                       {:seed (byte-array [1 2 3])})))))

(deftest initialization-failure-still-settles-the-scope
  (async done
         (with-ctx [_runtime]
           (let [scope* (atom nil)
                 create world-scope/create]
             (with-redefs [world-scope/create
                           (fn [opts]
                             (let [scope (create opts)]
                               (reset! scope* scope)
                               scope))]
               (run-spin!
                (mcts/search
                 {:actions (fn [_]
                             (throw (ex-info "initialization failed" {})))
                  :transition (fn [state _] state)
                  :terminal? (constantly false)
                  :reward (constantly 0.0)}
                 :root
                 {:max-simulations 1})
                (fn [result]
                  (is false (str "initialization unexpectedly succeeded: " result))
                  (done))
                (fn [error]
                  (is (re-find #"initialization failed" (str error)))
                  (is (= :discarded (:status @@scope*)))
                  (is (empty? (:handles @@scope*)))
                  (done))))))))

#?(:clj
   (deftest cancellation-unwinds-evaluation-before-world-settlement
     (let [runtime (context/create-execution-context)
           scope* (atom nil)
           entered (promise)
           create world-scope/create]
       (try
         (binding [ec/*execution-context* runtime]
           (with-redefs [world-scope/create
                         (fn [opts]
                           (let [scope (create opts)]
                             (reset! scope* scope)
                             scope))]
             (let [task (mcts/search
                         {:actions (constantly [:wait])
                          :transition (fn [state _]
                                        (spin
                                         (deliver entered true)
                                         (await (fn [_resolve _reject] nil))
                                         state))
                          :terminal? (constantly false)
                          :reward (constantly 0.0)}
                         :root
                         {:max-simulations 2 :max-depth 2 :max-nodes 2})
                   outcome (future
                             (try @task (catch Throwable error error)))]
               (is (= true (deref entered 5000 ::timed-out)))
               (binding [ec/*execution-context* runtime]
                 (spin-core/cancel-spin! task))
               (let [result (deref outcome 5000 ::timed-out)]
                 (is (instance? Throwable result))
                 (is (= spin-core/spin-cancelled (:type (ex-data result))))
                 (is (= :discarded (:status @@scope*)))
                 (is (empty? (:handles @@scope*)))))))
         (finally
           (context/stop-context! runtime))))))
