(ns org.replikativ.spindel.engine.component-test
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.component :as component]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.state-backend :as backend]))

(defrecord ForkableBox [value]
  component/PWorldComponent
  (realization [this] this)

  rtp/PForkable
  (fork-value [_ fork-id directive]
    (->ForkableBox [value fork-id directive])))

(deftest component-ref-selects-the-current-world
  (let [parent (context/create-execution-context)]
    (try
      (let [ref (binding [ec/*execution-context* parent]
                  (component/register! :box (->ForkableBox :parent)))
            child (context/fork-context parent :mode :frozen)]
        (try
          (is (= :parent (:value (component/resolve-in parent ref))))
          (let [[value fork-id directive]
                (:value (component/resolve-in child ref))]
            (is (= :parent value))
            (is (= (:fork-id child) fork-id))
            (is (= {:fork :component :mode :frozen} directive)))
          (binding [ec/*execution-context* child]
            (is (= (:fork-id child)
                   (second (:value (component/resolve ref))))))
          (finally
            (context/close-context! child))))
      (finally
        (context/close-context! parent)))))

(deftest explicit-component-selection-attenuates-the-child
  (let [parent (context/create-execution-context)]
    (try
      (let [kept (binding [ec/*execution-context* parent]
                   (component/register! :kept (->ForkableBox 1)))
            removed (binding [ec/*execution-context* parent]
                      (component/register! :removed (->ForkableBox 2)))
            child (context/fork-context parent :forkable-components #{:kept})]
        (try
          (is (some? (component/resolve-in child kept)))
          (is (thrown-with-msg? clojure.lang.ExceptionInfo
                                #"not available"
                                (component/resolve-in child removed)))
          (finally
            (context/close-context! child))))
      (finally
        (context/close-context! parent)))))

(deftest component-selection-cannot-be-overridden-through-state-updates
  (let [parent (context/create-execution-context)]
    (try
      (binding [ec/*execution-context* parent]
        (component/register! :kept (->ForkableBox 1)))
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo
           #"owned by fork-context"
           (context/fork-context
            parent
            :forkable-components #{}
            :state-updates {:world/components {:kept (->ForkableBox :alias)}})))
      (finally
        (context/close-context! parent)))))

(deftest explicit-component-selection-is-normalized
  (let [parent (context/create-execution-context)
        fork-count (atom 0)]
    (try
      (binding [ec/*execution-context* parent]
        (component/register!
         :counted
         (component/forkable
          :parent
          (fn [_ _ _]
            (swap! fork-count inc)
            :child))))
      (let [child (context/fork-context
                   parent :forkable-components [:counted :counted])]
        (try
          (is (= 1 @fork-count))
          (finally
            (context/close-context! child))))
      (finally
        (context/close-context! parent)))))

(deftest registration-and-selection-fail-closed
  (let [parent (context/create-execution-context)]
    (try
      (is (thrown-with-msg? clojure.lang.ExceptionInfo
                            #"explicit fork or sharing policy"
                            (binding [ec/*execution-context* parent]
                              (component/register! :unsafe (atom {})))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo
                            #"unknown world components"
                            (context/fork-context
                             parent :forkable-components #{:missing})))
      (finally
        (context/close-context! parent)))))

(deftest sharing-a-component-is-an-explicit-declaration
  (let [parent (context/create-execution-context)
        mutable-value (atom [])]
    (try
      (let [ref (binding [ec/*execution-context* parent]
                  (component/register! :shared
                                       (component/shared mutable-value)))
            child (context/fork-context parent)]
        (try
          (is (identical? mutable-value (component/resolve-in parent ref)))
          (is (identical? mutable-value (component/resolve-in child ref)))
          (binding [ec/*execution-context* parent]
            (is (= {:shared mutable-value} (component/registered))))
          (finally
            (context/close-context! child))))
      (finally
        (context/close-context! parent)))))

(deftest unregister-is-idempotent-and-world-local
  (let [parent (context/create-execution-context)]
    (try
      (let [ref (binding [ec/*execution-context* parent]
                  (component/register! :temporary (->ForkableBox :parent)))
            child (context/fork-context parent :mode :frozen)]
        (try
          (binding [ec/*execution-context* child]
            (component/unregister! ref)
            (component/unregister! ref))
          (is (thrown-with-msg? clojure.lang.ExceptionInfo
                                #"not available"
                                (component/resolve-in child ref)))
          (is (= :parent (:value (component/resolve-in parent ref)))
              "removing the child realization cannot mutate its parent")
          (binding [ec/*execution-context* parent]
            (component/unregister! ref))
          (is (thrown-with-msg? clojure.lang.ExceptionInfo
                                #"not available"
                                (component/resolve-in parent ref)))
          (finally
            (context/close-context! child))))
      (finally
        (context/close-context! parent)))))

(deftest materialized-forks-use-canonical-fork-invariants
  (let [parent (context/create-execution-context)]
    (try
      (let [ref (binding [ec/*execution-context* parent]
                  (component/register! :heap (->ForkableBox :parent)))]
        (binding [ec/*execution-context* parent]
          (ec/swap-state! [:listeners] (constantly {:host identity}))
          (ec/swap-state! [:pending-callbacks]
                          (constantly {:spin [{:resolve identity}]})))
        (let [child (context/materialized-fork-context
                     parent :clean-in-flight? false)]
          (try
            (is (identical? parent (:parent-ctx child)))
            (is (identical? (:running parent) (:running child)))
            (is (identical? (:drain-active parent) (:drain-active child)))
            (is (= :atom (backend/backend-type (:backend child))))
            (is (empty? (ec/get-state-in child [:listeners])))
            (is (empty? (ec/get-state-in child [:pending-callbacks])))
            (is (= :parent
                   (first (:value (component/resolve-in child ref)))))
            (finally
              (context/close-context! child)))))
      (binding [ec/*execution-context* parent]
        (ec/swap-state! [:forkable-signals] (constantly #{:external})))
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo
           #"cannot own external forkable signals"
           (context/materialized-fork-context parent)))
      (finally
        (context/close-context! parent)))))

(deftest portable-snapshots-drop-process-local-components
  (let [parent (context/create-execution-context)]
    (try
      (let [ref (binding [ec/*execution-context* parent]
                  (component/register! :ephemeral (->ForkableBox :live)))
            snapshot (context/snapshot-context parent)]
        (is (= :live (:value (component/resolve-in parent ref))))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo
                              #"not available"
                              (component/resolve-in snapshot ref))))
      (finally
        (context/close-context! parent)))))
