(ns org.replikativ.spindel.engine.effects
  "Effect system for extensible continuation handling.

  Effects are the extension mechanism for laufzeit's CPS transformation.
  Libraries can register effect handlers to support domain-specific operations
  (probabilistic programming, logic programming, backward execution, etc.).

  Core insight: Every effectful operation in a spin suspends execution and
  calls an effect handler. The handler determines how to resume (or transform)
  the continuation.

  ## Architecture

  - **PEffectHandler**: Protocol for implementing effect handlers
  - **Call-form symbols**: Effects are invoked by registering call-form symbols
    (e.g., org.replikativ.spindel.spin/await) with handlers and small arg adapters.
  - **Library effects**: sample (random variables), observe (conditioning), etc.

  ## Effect Handler Lifecycle

  1. **Registration**: Effect handlers registered against symbols at ns load
  2. **Invocation**: Spin macro intercepts calls to those symbols and dispatches
  3. **Runtime swapping**: Forked runtimes can replace handlers if desired
  4. **Continuation**: Handlers call resolve/reject to resume execution"
  (:require [org.replikativ.spindel.engine.core :as ec]
            [replikativ.logging :as log]))

;; =============================================================================
;; Effect Handler Protocol
;; =============================================================================

(defprotocol PEffectHandler
  "Protocol for effect handlers that extend the CPS transformation.

  Effect handlers are the extension mechanism for laufzeit. They receive:
  - runtime: The runtime context (access via ec/*execution-context* binding)
  - args: Arguments passed to the effect (e.g., signal-ref, spin-ref)
  - resolve: Continuation to call with success value
  - reject: Continuation to call with error

  Handlers are responsible for:
  1. Reading/modifying context state via PState protocol
  2. Setting up dependencies/observers
  3. Calling resolve(value) or reject(error) to resume execution

  Handlers can be synchronous (resolve immediately) or asynchronous (resolve later)."

  (handle-effect [this context args resolve reject]
    "Handle an effect invocation.

    Args:
    - context: Execution context instance (bound in ec/*execution-context*)
    - args: Map of effect-specific arguments
    - resolve: (fn [value] ...) - Resume with success
    - reject: (fn [error] ...) - Resume with error

    Returns: nil (side-effects only)"))

;; Note: Keyword-based global registries and perform-based invocation have been
;; removed in favor of explicit symbol-based registration and dispatch.

;; =============================================================================
;; Utility: Synchronous Effect Helper
;; =============================================================================

(defn sync-effect
  "Helper for creating synchronous effect handlers.

  Takes a function (fn [context args] value-or-error) and wraps it
  in PEffectHandler protocol, calling resolve/reject appropriately.

  Catches exceptions and passes them to reject.

  Example:
    (sync-effect
      (fn [context {:keys [signal-ref]}]
        (binding [ec/*execution-context* context]
          (sig/get-signal-value signal-ref))))"
  [effect-fn]
  (reify PEffectHandler
    (handle-effect [_ context args resolve reject]
      (try
        (let [result (effect-fn context args)]
          (resolve result))
        (catch #?(:clj Exception :cljs js/Error) e
          (reject e))))))

;; =============================================================================
;; Utility: Async Effect Helper
;; =============================================================================

(defn async-effect
  "Helper for creating asynchronous effect handlers.

  Takes a function (fn [context args resolve reject] ...) that is
  responsible for calling resolve or reject at some future point.

  The function should:
  1. Set up async operation (use ec/*execution-context* binding for state access)
  2. Register callbacks that will call resolve/reject
  3. Return nil

  Example:
    (async-effect
      (fn [context {:keys [spin-ref]} resolve reject]
        (binding [ec/*execution-context* context]
          (register-spin-observer! spin-ref
            (fn [value] (resolve value))
            (fn [error] (reject error))))))"
  [effect-fn]
  (reify PEffectHandler
    (handle-effect [_ context args resolve reject]
      (effect-fn context args resolve reject)
      nil)))

;; =============================================================================
;; Symbol-based syntax registry for direct CPS interception
;; =============================================================================

(def ^:private ^{:doc "Registry mapping syntax symbols to effect metadata.

  Map of symbol → {:effect keyword :adapter symbol}

  - :effect is the effect keyword used to look up the handler
  - :adapter is a fully-qualified var symbol naming a function
    (fn [args-vector] args-map) that will shape positional args
    into the map expected by the effect handler. This adapter runs
    at runtime in the generated code.

  Consumers (e.g., the spin macro) can read this registry to add
  dynamic breakpoints for function-call syntax like `(sample dist)`.
  Library authors then only need to register effects and their syntax,
  without touching the spin macro."
  } effect-syntax-registry (atom {}))

(defn get-effect-syntax
  "Return the current symbol→effect syntax registry map."
  []
  @effect-syntax-registry)

;; Common adapters for convenience
(defn one-arg->awaitable-map
  "Adapter: (effect x) → {:awaitable x}"
  [args]
  {:awaitable (first args)})

;; Public API: register an effect by its call-form symbol
(defn register-effect-by-symbol!
  "Register an effect handler for a call-form symbol.

  - sym: fully-qualified symbol used in code (e.g., 'org.replikativ.spindel.spin/await)
  - handler: PEffectHandler instance OR keyword marker for direct handlers
  - adapter-var-sym: fully-qualified var symbol naming an adapter
    (fn [args-vector] args-map)

  Keyword handlers are markers for direct handlers that bypass dispatch.
  The spin macro checks for keyword handlers and uses direct breakpoints.

  Stores the adapter function (on Clojure) to avoid context resolution issues."
  ([sym handler adapter-var-sym]
   (register-effect-by-symbol! sym handler adapter-var-sym nil))
  ([sym handler adapter-var-sym direct-handler-sym]
   {:pre [(symbol? sym)
          (or (satisfies? PEffectHandler handler) (keyword? handler))
          (symbol? adapter-var-sym)]}
   #?(:clj
      (let [v (requiring-resolve adapter-var-sym)
            f @v]
        (swap! effect-syntax-registry assoc sym {:handler handler
                                                 :adapter-fn f
                                                 :direct-handler-sym direct-handler-sym}))
      :cljs
      (swap! effect-syntax-registry assoc sym {:handler handler
                                               :adapter adapter-var-sym
                                               :direct-handler-sym direct-handler-sym}))
   nil))

;; Runtime dispatch for symbol-invoked effects
(defn dispatch-symbol-call
  "Dispatch a symbol-invoked effect from CPS code.

  - context: execution context instance
  - sym: the call-form symbol (e.g., 'org.replikativ.spindel.spin/await)
  - argsv: vector of evaluated positional args
  - spin-id, source-loc: augmented context
  - resolve, reject: continuations

  Looks up the handler and adapter from the symbol registry, shapes args,
  augments with spin context, and calls handle-effect."
  [context sym argsv spin-id source-loc resolve reject]
  (let [{:keys [handler adapter-fn adapter]} (get @effect-syntax-registry sym)]
    (when-not handler
      (throw (ex-info (str "No effect registered for symbol: " sym)
                      {:symbol sym :available (keys @effect-syntax-registry)})))
    (let [adapter-fn (or adapter-fn
                         #?(:clj (some-> adapter requiring-resolve deref)
                            :cljs nil)
                         (throw (ex-info (str "Adapter not resolvable: " adapter)
                                         {:symbol sym :adapter adapter})))
          base-args (adapter-fn argsv)
          args (assoc base-args :spin-id spin-id :source-loc source-loc)]
      ;; Debug instrumentation to trace effect dispatch context for awaits
      (when (= sym 'org.replikativ.spindel.effects.await/await)
        (log/trace :effects/dispatch-await {:spin-id spin-id
                            :source-loc source-loc
                            :args-count (count argsv)}))
      (handle-effect handler context args resolve reject))))

;; =============================================================================
;; Shared Helper Functions
;; =============================================================================

(defn check-cancellation!
  "Check if current spin is cancelled, throw if so.

  Called at entry point of all effect handlers to enforce cancellation."
  [spin-id]
  (when (and spin-id (ec/spin-is-cancelled?))
    (throw (ex-info "Spin cancelled" {:spin-id spin-id}))))

(defn type-error
  "Create standardized type error for wrong awaitable/trackable type.

  Usage:
    (type-error 'await 'Spin signal-ref)"
  [effect-name expected-type actual-value]
  (ex-info (str effect-name " requires " expected-type)
           {:effect effect-name
            :expected expected-type
            :actual-type (type actual-value)
            :actual-value actual-value}))
