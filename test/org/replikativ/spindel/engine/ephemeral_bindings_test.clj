(ns org.replikativ.spindel.engine.ephemeral-bindings-test
  "Tests for the historical ephemeral binding keys mechanism.

  This mechanism is being phased out: continuations now snapshot full
  :bindings at suspend time and restore them at resume time, so the
  per-key ephemerality category is no longer needed. Keys registered via
  register-ephemeral-binding-key! are now preserved across both track and
  await resumes — the suspend-time scope is what the body sees on resume,
  the same way lexical bindings flow into a continuation's closure.

  These tests document the post-snapshot behavior."
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

(deftest ephemeral-key-preserved-on-track-resume
  (testing "Ephemeral key is preserved on track resume (new snapshot model)"
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

            ;; Second pass — signal change forces track resume. Body resumes
            ;; with the bindings that were active at the track suspend point.
            (swap! counter inc)
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)

            (is (= 2 (count @observed)) "spin body should execute twice")
            (let [[p1 p2] @observed]
              (is (= :set (:ephemeral p1))  "pass 1: ephemeral visible")
              (is (= :set (:persistent p1)) "pass 1: persistent visible")
              (is (= :set (:ephemeral p2))  "pass 2 (track resume): ephemeral preserved via snapshot")
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
