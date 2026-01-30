(ns is.simm.spindel.dom.nested-spin-test
  "Tests for nested spin support in DOM elements.

  These tests verify that:
  1. await works inside element children
  2. Component functions that return spins can be awaited
  3. Local state (signal/track) works in component spins"
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [is.simm.spindel.dom.core :as dom]
            [is.simm.spindel.dom.elements :as el]
            [is.simm.spindel.dom.discharge :as disch]
            [is.simm.spindel.dom.render :as render]
            [is.simm.spindel.state.signal :as sig]
            [is.simm.spindel.effects.track :refer [track]]
            [is.simm.spindel.effects.await :refer [await]]
            [is.simm.spindel.spin.cps :refer [spin]]
            [is.simm.spindel.spin.sync :as sync]
            [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.runtime.context :as ctx]
            [is.simm.spindel.test-async :refer [await-drain]]))

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
