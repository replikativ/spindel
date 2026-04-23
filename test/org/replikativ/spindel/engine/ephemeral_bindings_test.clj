(ns org.replikativ.spindel.engine.ephemeral-bindings-test
  "Tests for ephemeral binding keys.

  Keys registered via engine.bindings/register-ephemeral-binding-key! are
  cleared when a track continuation resumes (= new render pass) but preserved
  across an await continuation resume (= mid-body, same render pass).
  Unregistered keys behave persistently in all cases."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]))

;; Register a test-only key so this test doesn't depend on DOM registration.
(bindings/register-ephemeral-binding-key! ::ephemeral)

(defn- observe-bindings
  "Read the current context's :bindings for both ephemeral and persistent keys."
  []
  (let [b (:bindings ec/*execution-context*)]
    {:ephemeral  (get b ::ephemeral)
     :persistent (get b ::persistent)}))

(deftest ephemeral-key-cleared-on-track-resume
  (testing "Ephemeral key is cleared on track resume; persistent key survives"
    (let [ctx-root (ctx/create-execution-context
                    :bindings {::ephemeral  :set
                               ::persistent :set})]
      (try
        (binding [ec/*execution-context* ctx-root]
          (let [counter  (sig/signal 0)
                observed (atom [])
                s (spin
                    (let [{:keys [new]} (track counter)]
                      (swap! observed conj (assoc (observe-bindings) :count new))
                      new))]
            ;; First pass — both bindings visible at initial execution.
            (is (= 0 @s))
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)

            ;; Second pass — signal change forces track resume.
            (swap! counter inc)
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)

            (is (= 2 (count @observed)) "spin body should execute twice")
            (let [[p1 p2] @observed]
              (is (= :set (:ephemeral p1))  "pass 1: ephemeral visible")
              (is (= :set (:persistent p1)) "pass 1: persistent visible")
              (is (nil? (:ephemeral p2))    "pass 2 (track resume): ephemeral cleared")
              (is (= :set (:persistent p2)) "pass 2 (track resume): persistent preserved"))))
        (finally
          (ctx/stop-context! ctx-root))))))

(deftest ephemeral-key-preserved-across-await-resume
  (testing "Ephemeral key survives an await resume (same render pass)"
    (let [ctx-root (ctx/create-execution-context
                    :bindings {::ephemeral  :set
                               ::persistent :set})]
      (try
        (binding [ec/*execution-context* ctx-root]
          (let [observed (atom nil)
                child  (spin 42)
                parent (spin
                         (let [_ (await child)]
                           (reset! observed (observe-bindings))))]
            @parent
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)
            (is (= {:ephemeral :set :persistent :set} @observed)
                "both bindings visible after await resume")))
        (finally
          (ctx/stop-context! ctx-root))))))

(deftest ephemeral-registry-is-global
  (testing "Ephemeral keys registered earlier are returned by the accessor"
    (is (contains? (bindings/ephemeral-binding-keys) ::ephemeral)))
  (testing "DOM keys are pre-registered by dom.addressing"
    (require 'org.replikativ.spindel.dom.addressing)
    (is (contains? (bindings/ephemeral-binding-keys) :dom/parent-addr))
    (is (contains? (bindings/ephemeral-binding-keys) :dom/current-slot))))
