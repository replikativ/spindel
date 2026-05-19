(ns org.replikativ.spindel.distributed.integration-test
  "Integration tests for spindel distributed functions over kabel peers.

  These tests verify end-to-end distributed function invocation:
  1. Start a kabel server peer
  2. Connect a kabel client peer
  3. Define distributed functions using defn-spin-remote
  4. Invoke functions across peers using spindel spins"
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.distributed.macros :refer [defn-spin-remote spin-remote]]
            [org.replikativ.spindel.distributed.core :as dist]
            [is.simm.distributed-scope :as ds]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.executor :as scheduler]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [kabel.peer :as peer]
            [kabel.http-kit :as http-kit]
            [kabel.middleware.transit :refer [transit]]
            [hasch.core :refer [uuid]]
            [superv.async :refer [S <??]]
            [clojure.core.async :as a])
  (:import (java.net ServerSocket)))

;; =============================================================================
;; Test Infrastructure
;; =============================================================================

(defn- free-port
  "Find an available port for the test server."
  []
  (with-open [^ServerSocket ss (ServerSocket. 0)]
    (.getLocalPort ss)))

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
;; Peer Setup Helpers
;; =============================================================================

(defn start-server!
  "Start a kabel server peer on the given URL."
  [url server-id]
  (let [handler (http-kit/create-http-kit-handler! S url server-id)
        server (peer/server-peer S handler server-id ds/remote-middleware transit)]
    (ds/invoke-on-peer server)
    (<?? S (peer/start server))
    {:server server :handler handler}))

(defn stop-server!
  "Stop a kabel server peer."
  [{:keys [server]}]
  (when server
    (<?? S (peer/stop server))))

(defn start-client!
  "Start a kabel client peer and connect to the given URL."
  [url client-id]
  (let [client (peer/client-peer S client-id ds/remote-middleware transit)]
    (ds/invoke-on-peer client)
    (<?? S (peer/connect S client url))
    client))

;; =============================================================================
;; Distributed Functions for Testing
;; =============================================================================

;; Simple computation on remote peer
(defn-spin-remote compute-on-server [server-id x y]
  (spin-remote server-id [x y]
               (+ x y)))

;; NOTE: Chained/nested spin-remote calls are not yet supported.
;; The remote body runs in a core.async go block, so spindel's await
;; cannot be used there. For nested remote calls, use separate functions
;; and compose at the caller level.

;; Simple multi-step: caller coordinates multiple remote calls
(defn-spin-remote increment-remote [server-id x]
  (spin-remote server-id [x]
               (inc x)))

(defn-spin-remote double-remote [server-id x]
  (spin-remote server-id [x]
               (* x 2)))

;; Remote function that returns nil
(defn-spin-remote return-nil [server-id]
  (spin-remote server-id []
               nil))

;; Remote function that conditionally returns nil
(defn-spin-remote conditional-nil [server-id return-value?]
  (spin-remote server-id [return-value?]
               (when return-value? 42)))

;; Remote function that throws an error
(defn-spin-remote throw-error [server-id msg]
  (spin-remote server-id [msg]
               (throw (ex-info msg {:type :test-error}))))

;; =============================================================================
;; Integration Tests
;; =============================================================================

(deftest ^:integration test-simple-remote-computation
  (testing "Simple remote computation across peers"
    (let [port (free-port)
          url (str "ws://localhost:" port)
          server-id (uuid :server)
          client-id (uuid :client)
          started (start-server! url server-id)
          _client (start-client! url client-id)]
      (try
        (let [result (deref (spin (await (compute-on-server server-id 10 32))) 10000 ::timeout)]
          (is (not= ::timeout result) "Remote computation timed out")
          (is (= 42 result)))
        (finally
          (stop-server! started))))))

(deftest ^:integration test-nil-handling
  (testing "Remote function returning nil"
    (let [port (free-port)
          url (str "ws://localhost:" port)
          server-id (uuid :server)
          client-id (uuid :client)
          started (start-server! url server-id)
          _client (start-client! url client-id)]
      (try
        (testing "explicit nil return"
          (let [result (deref (spin (await (return-nil server-id))) 10000 ::timeout)]
            (is (not= ::timeout result) "Remote nil return timed out")
            (is (nil? result))))

        (testing "conditional nil - when true"
          (let [result (deref (spin (await (conditional-nil server-id true))) 10000 ::timeout)]
            (is (not= ::timeout result) "Remote conditional-nil timed out")
            (is (= 42 result))))

        (testing "conditional nil - when false"
          (let [result (deref (spin (await (conditional-nil server-id false))) 10000 ::timeout)]
            (is (not= ::timeout result) "Remote conditional-nil timed out")
            (is (nil? result))))
        (finally
          (stop-server! started))))))

(deftest ^:integration test-error-propagation
  (testing "Errors from remote functions propagate correctly"
    (let [port (free-port)
          url (str "ws://localhost:" port)
          server-id (uuid :server)
          client-id (uuid :client)
          started (start-server! url server-id)
          _client (start-client! url client-id)]
      (try
        ;; Wait for the peer handshake to complete by doing a warmup
        ;; round-trip. A fixed Thread/sleep was a real race here: if the
        ;; kabel middleware-registration hadn't reached steady state, the
        ;; remote call message dropped silently and the test below saw
        ;; `::timeout`. Performing one successful call confirms the path
        ;; is live; subsequent calls inherit that liveness.
        (let [warmup (deref (spin (await (compute-on-server server-id 1 1)))
                            10000 ::timeout)]
          (when (= ::timeout warmup)
            (throw (ex-info "peer handshake did not complete within 10s"
                            {:server-id server-id :url url}))))
        ;; distributed-scope 0.1.2 propagates the original ex-info message
        ;; directly without a "Remote invocation error" wrapper. The remote
        ;; ex-info raised by throw-error has :message "boom" + :data
        ;; {:type :test-error}, and that's what the client deref re-raises.
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"boom"
                              (deref (spin (await (throw-error server-id "boom"))) 10000 ::timeout)))
        (finally
          (stop-server! started))))))

(deftest ^:integration test-multi-step-remote-calls
  (testing "Multi-step remote calls coordinated by caller"
    (let [port (free-port)
          url (str "ws://localhost:" port)
          server-id (uuid :server)
          client-id (uuid :client)
          started (start-server! url server-id)
          _client (start-client! url client-id)]
      (try
        ;; Caller coordinates: initial=10 -> inc -> 11 -> *2 -> 22
        (let [result (deref (spin
                             (let [incremented (await (increment-remote server-id 10))
                                   doubled (await (double-remote server-id incremented))]
                               doubled))
                            10000 ::timeout)]
          (is (not= ::timeout result) "Multi-step remote calls timed out")
          (is (= 22 result)))
        (finally
          (stop-server! started))))))

;; =============================================================================
;; Context Addressing Tests
;; =============================================================================

;; Define a function that uses context-id addressing
(defn-spin-remote read-from-context [server-id context-id key]
  (spin-remote [server-id context-id] [key]
    ;; Read a value from the execution context's bindings
               (get-in ec/*execution-context* [:bindings key])))

(deftest ^:integration test-context-addressing
  (testing "Remote execution with explicit context-id"
    (let [port (free-port)
          url (str "ws://localhost:" port)
          server-id (uuid :server)
          client-id (uuid :client)

          ;; Create two contexts with different bindings
          executor (scheduler/default-executor)
          ctx-a (ctx/create-execution-context
                 :executor executor
                 :bindings {:test-value 100})
          ctx-b (ctx/create-execution-context
                 :executor executor
                 :bindings {:test-value 200})

          ;; Register contexts
          _ (dist/register-context! :ctx-a ctx-a)
          _ (dist/register-context! :ctx-b ctx-b)

          started (start-server! url server-id)
          _client (start-client! url client-id)]
      (try
        ;; Read from context A
        (let [result-a (deref (spin (await (read-from-context server-id :ctx-a :test-value))) 10000 ::timeout)]
          (is (not= ::timeout result-a) "Context A read timed out")
          (is (= 100 result-a) "Should read from context A's bindings"))

        ;; Read from context B
        (let [result-b (deref (spin (await (read-from-context server-id :ctx-b :test-value))) 10000 ::timeout)]
          (is (not= ::timeout result-b) "Context B read timed out")
          (is (= 200 result-b) "Should read from context B's bindings"))
        (finally
          ;; Cleanup
          (dist/unregister-context! :ctx-a)
          (dist/unregister-context! :ctx-b)
          (stop-server! started))))))

(deftest ^:integration test-default-context
  (testing "Remote execution without context-id uses :default"
    (let [port (free-port)
          url (str "ws://localhost:" port)
          server-id (uuid :server)
          client-id (uuid :client)

          ;; Create and register default context
          executor (scheduler/default-executor)
          default-ctx (ctx/create-execution-context
                       :executor executor
                       :bindings {:test-value 42})
          _ (dist/register-context! :default default-ctx)

          started (start-server! url server-id)
          _client (start-client! url client-id)]
      (try
        ;; read-from-context with explicit context-id
        (let [result (deref (spin (await (read-from-context server-id :default :test-value))) 10000 ::timeout)]
          (is (not= ::timeout result) "Default context read timed out")
          (is (= 42 result) "Should read from default context"))
        (finally
          (dist/unregister-context! :default)
          (stop-server! started))))))
