(ns org.replikativ.spindel.ygg-checkpoint-portable-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [org.replikativ.spindel.yggdrasil.construction-test :as fixtures]
            [yggdrasil.protocols :as p]))

(defrecord ValidationSystem [id validations allocations reply live cleanup]
  p/SystemIdentity
  (system-id [_] id)
  (system-type [_] :checkpoint-preflight-probe)
  (capabilities [_] {:overlayable true :snapshotable true :checkpoint-overlay true
                     :checkpoint-overlay-modes #{:sync :async}})
  p/Snapshotable
  (snapshot-id [_] "basis")
  (parent-ids [_] #{})
  (as-of [_ _] nil)
  (as-of [_ _ _] nil)
  (snapshot-meta [_ _] nil)
  (snapshot-meta [_ _ _] nil)
  p/CheckpointOriginValidator
  (-validate-checkpoint-origin [_ origin _]
    (swap! validations conj id)
    (if (= :same reply) origin reply))
  p/Overlayable
  (overlay [this _]
    (swap! allocations inc)
    (swap! live conj id)
    (fixtures/->NativeOverlay this (atom this) :frozen id live cleanup (atom false))))

(defn- origin []
  {:version 1 :kind :datahike :commit (random-uuid)
   :source {:store (random-uuid) :repository (random-uuid)}})

(deftest physical-checkpoint-preflight-never-stores-an-async-constructor-as-a-value
  (let [ctx (sp/create-execution-context) validations (atom []) allocations (atom 0)
        live (atom #{}) cleanup (atom []) selected (origin)]
    (try
      (binding [org.replikativ.spindel.engine.core/*execution-context* ctx]
        (ygg/register! (->ValidationSystem "a" validations allocations :same live cleanup))
        (ygg/register! (->ValidationSystem "b" validations allocations nil live cleanup))
        (let [policy (array-map "a" selected "b" selected)
              error (try (ygg/fork! {:sync? true :checkpoints policy}) nil
                         (catch #?(:clj Throwable :cljs :default) error error))]
          (is (= #?(:clj ::ygg/invalid-checkpoint-validation :cljs ::ygg/async-checkpoint-fork)
                 (:type (ex-data error))))
          (is (= #?(:clj ["a" "b"] :cljs []) @validations))
          (is (zero? @allocations))
          (is (empty? @live))
          (is (empty? @cleanup))
          (is (nil? (:construction/owner (ex-data error))))))
      (finally (context/stop-context! ctx)))))
