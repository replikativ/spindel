(ns org.replikativ.spindel.distributed.core
  "Bridge layer between spindel spins and core.async channels.

  This namespace provides interop functions for integrating spindel's
  reactive spin system with distributed-scope's core.async-based
  remote invocation mechanism.

  Key functions:
  - spin->chan: Convert spindel spin to core.async channel
  - chan->deferred: Convert core.async channel to spindel Deferred
  - invoke-remote-spin: Create a spin that executes on a remote peer

  Design:
  - Uses core.async channels at the network boundary (distributed-scope compatibility)
  - Uses spindel Deferred internally for suspension/resumption
  - Each execution context can be addressed by peer-id + fork-id"
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.runtime.core :as rtc]
            [is.simm.partial-cps.async :as pcps-async]
            #?(:clj [clojure.core.async :as a :refer [put! take! chan close!]]
               :cljs [cljs.core.async :as a :refer [chan close! put! take!]])))

;; =============================================================================
;; Sentinel value for nil (core.async doesn't allow nil on channels)
;; =============================================================================

(def ^:private nil-sentinel ::nil-value)

;; Also handle distributed-scope's nil-sentinel for interop
(def ^:private ds-nil-sentinel :is.simm.distributed-scope/nil-value)

(defn- wrap-nil
  "Wrap nil values with sentinel for core.async transport."
  [v]
  (if (nil? v) nil-sentinel v))

(defn- unwrap-nil
  "Unwrap sentinel back to nil.

  Handles both spindel and distributed-scope nil-sentinels for interop."
  [v]
  (if (or (= v nil-sentinel) (= v ds-nil-sentinel)) nil v))

;; =============================================================================
;; Spin -> Channel conversion
;; =============================================================================

(defn spin->chan
  "Convert a spindel Spin to a core.async channel.

  The returned channel will receive exactly one value:
  - The spin's result on success
  - A Throwable/Error on failure

  The channel closes after delivering the value.

  This is used when sending spin results over the network via
  distributed-scope's core.async-based messaging.

  Example:
    (let [t (spin (+ 1 2))
          ch (spin->chan t)]
      (go (println (<! ch))))  ; prints 3"
  [reactive-spin]
  (let [ch (chan 1)]
    ;; Execute spin with callbacks that deliver to channel
    (reactive-spin
      (fn [result]
        (put! ch (wrap-nil result))
        (close! ch))
      (fn [error]
        (put! ch error)
        (close! ch)))
    ch))

;; =============================================================================
;; Channel -> Deferred conversion
;; =============================================================================

(defn chan->spin
  "Convert a core.async channel to a spindel Spin.

  The Spin will complete when the channel delivers a value:
  - If the value is a Throwable/Error, the spin fails
  - Otherwise, the spin succeeds with the value

  This is used when receiving remote invocation results from
  distributed-scope's core.async-based messaging.

  Example:
    (spin
      (let [result (await (chan->spin ch))]
        (process result)))"
  [ch]
  ;; Capture current execution context at creation time
  ;; This is necessary because the take! callback runs on a different thread
  (let [captured-rt rtc/*execution-context*]
    ;; Return a Spin that waits for the channel
    (spin-core/make-spin
      (fn [resolve reject]
        ;; Take from channel asynchronously
        (take! ch
          (fn [result]
            (let [result (unwrap-nil result)]
              ;; CRITICAL: Rebind runtime context and *in-trampoline* when resuming
              (binding [pcps-async/*in-trampoline* false
                        rtc/*execution-context* captured-rt]
                (if (instance? #?(:clj Throwable :cljs js/Error) result)
                  (spin-core/resume reject result)
                  (spin-core/resume resolve result))))))
        ;; Return incomplete - will complete when channel delivers
        spin-core/incomplete))))

;; =============================================================================
;; Execution Context Registry
;; =============================================================================

(def execution-context-registry
  "Registry of execution contexts addressable for remote invocation.

  Maps context-id (keyword) → ExecutionContext.

  Each peer can have multiple execution contexts:
  - :default - The peer's main/default context
  - :fork-xxx - Forked contexts (for parallel exploration)
  - :session-xxx - Per-session contexts

  Remote invocations specify [peer-id context-id] to target a specific context.
  If context-id is nil or :default, uses the :default context."
  (atom {}))

(defn register-context!
  "Register an execution context for remote addressing.

  Args:
    context-id - Keyword identifier (e.g., :default, :my-fork)
    ctx - ExecutionContext instance

  Example:
    (register-context! :default (create-execution-context ...))
    (register-context! :particle-1 (fork-context parent-ctx ...))"
  [context-id ctx]
  (swap! execution-context-registry assoc context-id ctx))

(defn unregister-context!
  "Remove an execution context from the registry.

  Args:
    context-id - Keyword identifier to remove"
  [context-id]
  (swap! execution-context-registry dissoc context-id))

(defn get-context
  "Look up a registered execution context.

  Args:
    context-id - Keyword identifier (nil defaults to :default)

  Returns: ExecutionContext or nil if not found"
  [context-id]
  (get @execution-context-registry (or context-id :default)))

(defn list-contexts
  "List all registered context IDs.

  Returns: Sequence of context-id keywords"
  []
  (keys @execution-context-registry))

;; =============================================================================
;; Remote Spin Registry
;; =============================================================================

(def remote-spin-registry
  "Registry of spin factories that can be invoked remotely.

  Maps fully-qualified symbols to functions that:
  - Accept an arg-map
  - Return a core.async channel (for distributed-scope compatibility)

  Functions are registered at namespace load time via defn-spin-remote."
  (atom {}))

(defn register-remote-spin!
  "Register a spin factory for remote invocation.

  Args:
    fn-name - Fully-qualified symbol (e.g., 'my.ns/fetch-data)
    spin-factory-fn - Function that takes arg-map, returns core.async channel"
  [fn-name spin-factory-fn]
  (swap! remote-spin-registry assoc fn-name spin-factory-fn))

(defn get-remote-spin
  "Look up a registered remote spin factory.

  Returns nil if not found."
  [fn-name]
  (get @remote-spin-registry fn-name))

;; =============================================================================
;; Remote Invocation State
;; =============================================================================

(def system-peer
  "Atom holding the current kabel peer for remote communication.

  Set via (set-system-peer! peer) before invoking remote spins.
  Can be nil if only acting as a server (receiving invocations)."
  (atom nil))

(defn set-system-peer!
  "Set the kabel peer for remote invocation.

  Must be called before using invoke-remote-spin."
  [peer]
  (reset! system-peer peer))

(defn get-system-peer
  "Get the current kabel peer, throwing if not set."
  []
  (or @system-peer
      (throw (ex-info "System peer not set. Call set-system-peer! first."
                      {:hint "Use (set-system-peer! peer) after connecting"}))))

;; =============================================================================
;; Response Handler Registry
;; =============================================================================

(def ^:private response-handlers
  "Map of request-id -> callback function for pending remote invocations."
  (atom {}))

(defn register-response-handler!
  "Register a callback for a pending remote invocation.

  The callback receives the response map with :result or :error."
  [request-id callback]
  (swap! response-handlers assoc request-id callback))

(defn unregister-response-handler!
  "Remove a response handler after completion."
  [request-id]
  (swap! response-handlers dissoc request-id))

(defn get-response-handler
  "Get the response handler for a request-id."
  [request-id]
  (get @response-handlers request-id))

(defn handle-response!
  "Dispatch a response to its registered handler.

  Called by the middleware when receiving ::invoke-result messages."
  [{:keys [request-id] :as response}]
  (when-let [handler (get-response-handler request-id)]
    (unregister-response-handler! request-id)
    (handler response)))

;; =============================================================================
;; Utility: Throwable detection
;; =============================================================================

(defn throwable?
  "Check if a value is a Throwable (JVM) or Error (JS)."
  [x]
  (instance? #?(:clj Throwable :cljs js/Error) x))
