(ns org.replikativ.spindel.distributed.macro-test
  "Tests for defn-spin-remote macro."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.distributed.macros :refer [defn-spin-remote spin-remote]]
            [org.replikativ.spindel.distributed.core :as dist]
            [is.simm.distributed-scope :as ds]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.executor :as scheduler]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [clojure.core.async :as a :refer [go <! >! chan close! put!]]))

;; =============================================================================
;; Test Fixtures
;; =============================================================================

(def ^:dynamic *test-runtime* nil)

(defn with-runtime [f]
  (let [executor (scheduler/default-executor)
        rt (ctx/create-execution-context :executor executor)]
    ;; Register context for remote spin lookup
    (dist/register-context! :default rt)
    (try
      (binding [*test-runtime* rt
                ec/*execution-context* rt]
        (f))
      (finally
        (dist/unregister-context! :default)
        (ctx/stop-context! rt)))))

(use-fixtures :each with-runtime)

;; =============================================================================
;; Macro Expansion Tests
;; =============================================================================

(deftest test-spin-remote-standalone-throws
  (testing "spin-remote throws when used outside defn-spin-remote"
    ;; Note: We can't directly test (spin-remote ...) because it would
    ;; fail at compile time if the macro is working. Instead, test the
    ;; standalone function which throws at runtime.
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"spin-remote must be used inside defn-spin-remote"
                          (org.replikativ.spindel.distributed.macros/spin-remote
                           :server-id [] :dummy-body)))))

;; Define a simple remote function for testing
;; This tests macro expansion without requiring actual peer connection
(defn-spin-remote simple-double [server-id x]
  (spin-remote server-id [x]
               (* x 2)))

;; Define the namespace name as a constant for symbol lookup
(def this-ns "org.replikativ.spindel.distributed.macro-test")

(deftest test-defn-spin-remote-expands-correctly
  (testing "defn-spin-remote creates function and registers remote"
    ;; The function should exist
    (is (fn? simple-double))

    ;; Remote function should be registered with distributed-scope
    (is (some? (get @ds/remote-fn-registry
                    (symbol this-ns "spin-remote-simple-double-0"))))))

(deftest test-remote-function-returns-channel
  (testing "registered remote function returns core.async channel"
    (let [remote-fn (get @ds/remote-fn-registry
                         (symbol this-ns "spin-remote-simple-double-0"))
          ch (remote-fn {:x 21})
          ;; Take result from channel via promise — deterministic, no Thread/sleep guess
          p (promise)]
      (a/take! ch (fn [v] (deliver p v)))
      (is (= 42 (deref p 1000 :timeout))))))

;; Test with multiple args
(defn-spin-remote add-numbers [server-id a b c]
  (spin-remote server-id [a b c]
               (+ a b c)))

(deftest test-multiple-args
  (testing "defn-spin-remote works with multiple args"
    (let [remote-fn (get @ds/remote-fn-registry
                         (symbol this-ns "spin-remote-add-numbers-0"))
          ch (remote-fn {:a 1 :b 2 :c 3})
          p (promise)]
      (a/take! ch (fn [v] (deliver p v)))
      (is (= 6 (deref p 1000 :timeout))))))

;; Test error handling in remote body
(defn-spin-remote error-thrower [server-id msg]
  (spin-remote server-id [msg]
               (throw (ex-info msg {:type :test-error}))))

(deftest test-error-in-remote-body
  (testing "errors in remote body are captured"
    (let [remote-fn (get @ds/remote-fn-registry
                         (symbol this-ns "spin-remote-error-thrower-0"))
          ch (remote-fn {:msg "boom"})
          p (promise)]
      (a/take! ch (fn [v] (deliver p v)))
      (let [v (deref p 1000 :timeout)]
        (is (instance? Throwable v))
        (is (= "boom" (ex-message v)))))))

;; =============================================================================
;; Free Variable Validation Tests
;; =============================================================================

;; Note: Free variable validation happens at compile time. Testing compile-time
;; errors is tricky because the code fails before the test can even run.
;; We verify the mechanism works by ensuring valid code compiles successfully.

(deftest test-free-variable-validation
  (testing "declared variables compile successfully"
    ;; This test passes because all free variables are declared
    (is (fn? simple-double))
    (is (fn? add-numbers))
    (is (fn? error-thrower))))  ; missing-var not declared

;; =============================================================================
;; Integration Test (Local Only - No Network)
;; =============================================================================

(deftest test-full-round-trip-local
  (testing "full spin -> channel -> spin round trip locally"
    ;; Manually invoke the registered remote function to simulate what
    ;; would happen over the network
    (let [remote-fn (get @ds/remote-fn-registry
                         (symbol this-ns "spin-remote-simple-double-0"))
          ;; Simulate remote execution
          ch (remote-fn {:x 100})
          ;; Convert back to spindel spin
          t (dist/chan->spin ch)
          ;; Await result
          result @(spin (await t))]
      (is (= 200 result)))))
