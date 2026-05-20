(ns org.replikativ.spindel.engine.spin-scope-keys-test
  "Tests for the spin-scope-key mechanism.

  A spin-scope key is a :bindings entry that represents a spin's lexical
  construction scope. `make-spin` snapshots the registered scope keys onto
  the spin's node and the engine re-establishes them on every body-entry
  path — initial run, track resume, and await resume — so the body always
  runs under the scope it was constructed in, the same way lexical bindings
  flow into a continuation's closure.

  The registry (engine.bindings) is the engine's only knowledge of these
  keys: the engine never names a :dom/* (or any domain) key itself."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]))

;; Register a test-only scope key so this test doesn't depend on DOM registration.
(bindings/register-spin-scope-key! ::scoped)

(defn- observe-bindings
  "Read the current context's :bindings for both a scope key and a
  persistent (unregistered) key."
  []
  (let [b (:bindings ec/*execution-context*)]
    {:scoped     (get b ::scoped)
     :persistent (get b ::persistent)}))

(deftest scope-key-preserved-on-track-resume
  (testing "Scope key is preserved when a spin resumes from a track continuation"
    (let [ctx-root (ctx/create-execution-context
                    :bindings {::scoped     :set
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

            ;; Second pass — signal change forces a track resume.
            (swap! counter inc)
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)

            (is (= 2 (count @observed)) "spin body should execute twice")
            (let [[p1 p2] @observed]
              (is (= :set (:scoped p1))     "pass 1: scope key visible")
              (is (= :set (:persistent p1)) "pass 1: persistent visible")
              (is (= :set (:scoped p2))     "pass 2 (track resume): scope key preserved")
              (is (= :set (:persistent p2)) "pass 2 (track resume): persistent preserved"))))
        (finally
          (ctx/stop-context! ctx-root))))))

(deftest scope-key-preserved-across-await-resume
  (testing "Scope key survives an await resume (re-applied from the spin's snapshot)"
    (let [ctx-root (ctx/create-execution-context
                    :bindings {::scoped     :set
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
            (is (= {:scoped :set :persistent :set} @observed)
                "both bindings visible after await resume")))
        (finally
          (ctx/stop-context! ctx-root))))))

(deftest scope-key-registry-is-global
  (testing "Scope keys registered earlier are returned by the accessor"
    (is (contains? (bindings/spin-scope-keys) ::scoped)))
  (testing "DOM keys are pre-registered by dom.addressing"
    (require 'org.replikativ.spindel.dom.addressing)
    (is (contains? (bindings/spin-scope-keys) :dom/parent-addr))
    (is (contains? (bindings/spin-scope-keys) :dom/current-slot))))
