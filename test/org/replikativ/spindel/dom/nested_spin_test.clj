(ns org.replikativ.spindel.dom.nested-spin-test
  "Tests for nested spin support in DOM elements.

  These tests verify that:
  1. await works inside element children
  2. Component functions that return spins can be awaited
  3. Local state (signal/track) works in component spins

  Implementation notes:
  Element macros now use let-bindings with CPS-aware context macros (with-slot,
  with-parent-addr) instead of thunks, enabling await to work correctly in
  element children. The partial-cps transformer handles binding forms specially,
  capturing/restoring bindings across await points."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.dom.core :as dom]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.state.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

;; Fixture to ensure clean execution context between tests
(defn clean-context-fixture [f]
  (println "FIXTURE: Starting test, testing-vars=" (mapv str clojure.test/*testing-vars*))
  (binding [rtc/*execution-context* nil]
    (f))
  (println "FIXTURE: Finished test, testing-vars=" (mapv str clojure.test/*testing-vars*)))

(use-fixtures :each clean-context-fixture)

;; =============================================================================
;; Helper Components (these return spins)
;; =============================================================================

(defn simple-greeting
  "A simple component that returns a spin.
  No async - just wraps rendering in a spin for local scope."
  [name]
  (spin
    (el/span {:class "greeting"} (str "Hello, " name "!"))))

(defn counter-component
  "A component with local state using signal/track."
  [initial-value]
  (spin
    (let [counter (sig/signal initial-value)
          iv (track counter)
          current @iv]
      (el/div {:class "counter"}
        (el/span (str "Count: " current))))))

(defn nested-component
  "A component that renders a child component."
  [child-name]
  (spin
    (el/div {:class "wrapper"}
      (el/h1 "Parent")
      (await (simple-greeting child-name)))))

;; =============================================================================
;; Tests
;; =============================================================================

(deftest test-await-in-element-children
  (testing "await works directly inside element children"
    (let [rt (ctx/create-execution-context)]
      (binding [rtc/*execution-context* rt]
        (let [{:keys [discharge log]} (disch/make-mock-discharge)
              d (sync/deferred)
              render-spin (spin
                            (el/div {:class "test"}
                              (el/span "Static text")
                              (el/span (await d))))
              container nil]
          ;; Start render
          (render/render-spin! container render-spin discharge)

          ;; Resolve deferred - call d with value
          (d "Async content")
          (await-drain rt)

          ;; Verify spin completed and rendered
          (is (some #(and (= :create-text (:op %))
                          (= "Async content" (:text %))) @log)
              "Should render async content"))))))

(deftest test-component-spin-awaited
  (testing "Component that returns spin can be awaited in element child"
    (let [rt (ctx/create-execution-context)]
      (binding [rtc/*execution-context* rt]
        (let [{:keys [discharge log]} (disch/make-mock-discharge)
              render-spin (spin
                            (el/div {:class "app"}
                              (await (simple-greeting "World"))))
              container nil]
          (render/render-spin! container render-spin discharge)
          @render-spin
          (await-drain rt)

          ;; Verify greeting was rendered
          (is (some #(and (= :create-text (:op %))
                          (= "Hello, World!" (:text %))) @log)
              "Should render greeting from async component"))))))

(deftest test-nested-component-spins
  (testing "Nested component spins work correctly"
    (let [rt (ctx/create-execution-context)]
      (binding [rtc/*execution-context* rt]
        (let [{:keys [discharge log]} (disch/make-mock-discharge)
              render-spin (spin
                            (el/div {:class "root"}
                              (await (nested-component "Nested"))))
              container nil]
          (render/render-spin! container render-spin discharge)
          @render-spin
          (await-drain rt)

          ;; Verify nested content was rendered
          (is (some #(and (= :create-text (:op %))
                          (= "Hello, Nested!" (:text %))) @log)
              "Should render deeply nested async content"))))))

(deftest test-component-with-local-state
  (testing "Component with local signal/track works"
    (let [rt (ctx/create-execution-context)]
      (binding [rtc/*execution-context* rt]
        (let [{:keys [discharge log]} (disch/make-mock-discharge)
              render-spin (spin
                            (el/div {:class "app"}
                              (await (counter-component 42))))
              container nil]
          (render/render-spin! container render-spin discharge)
          @render-spin
          (await-drain rt)

          ;; Verify counter was rendered with initial value
          (is (some #(and (= :create-text (:op %))
                          (= "Count: 42" (:text %))) @log)
              "Should render counter with local state"))))))

(deftest test-multiple-async-children
  (testing "Multiple async children are evaluated in order"
    (let [rt (ctx/create-execution-context)]
      (binding [rtc/*execution-context* rt]
        (let [{:keys [discharge log]} (disch/make-mock-discharge)
              render-spin (spin
                            (el/ul {:class "list"}
                              (await (simple-greeting "First"))
                              (await (simple-greeting "Second"))
                              (await (simple-greeting "Third"))))
              container nil]
          (render/render-spin! container render-spin discharge)
          @render-spin
          (await-drain rt)

          ;; Verify all greetings were rendered
          (let [texts (filter #(= :create-text (:op %)) @log)
                text-values (map :text texts)]
            (is (some #(= "Hello, First!" %) text-values))
            (is (some #(= "Hello, Second!" %) text-values))
            (is (some #(= "Hello, Third!" %) text-values))))))))
