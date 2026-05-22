(ns org.replikativ.spindel.spin.cps
  "CPS transformation machinery for spin macro"
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.engine.effects]
            [org.replikativ.spindel.effects.await]   ;; Load await effect handler
            [org.replikativ.spindel.effects.track]   ;; Load track effect handler
            [is.simm.partial-cps.async :as async]
            [is.simm.partial-cps.runtime]            ;; Loads Thunk into the runtime ns
            #?(:clj [is.simm.partial-cps.ioc :as ioc])
            #?(:clj [org.replikativ.spindel.engine.free-vars :as free-vars])
            [org.replikativ.spindel.spin.core :as spin-core])
  ;; Make the spin macro available to CLJS via require-macros
  ;; Note: effect is not included here because it's defined in #?(:clj ...) only and
  ;; causes self-referential load issues. Users can require effect separately if needed.
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; CPS Breakpoint Machinery
;; =============================================================================

;; Factory: create a direct breakpoint handler that bypasses symbol dispatch
(defn- make-direct-breakpoint ^:private [direct-fn-sym]
  (fn [{:keys [spin-id env]} r e]
    (let [current-ns (str *ns*)]
      (fn [args]
        `(let [;; Continuations that use invoke-continuation for proper trampolining
               resolve# (fn [value#]
                          (try
                            (async/invoke-continuation ~r value#)
                            (catch ~(if (:js-globals env) :default `Throwable) t#
                              (async/invoke-continuation ~e t#))))
               reject# (fn [error#]
                         (try
                           (async/invoke-continuation ~e error#)
                           (catch ~(if (:js-globals env) :default `Throwable) t#
                             (async/invoke-continuation ~e t#))))
               ;; Read spin-id from dynamic binding at runtime
               current-spin-id# ec/*spin-id*]
           ;; Direct call to handler, bypassing dispatch
           (~direct-fn-sym ~@args current-spin-id# ~current-ns resolve# reject#))))))

;; Factory: create a breakpoint handler that dispatches via symbol-call dispatch
(defn- make-symbol-call-breakpoint ^:private [sym]
  (fn [{:keys [spin-id env]} r e]
    (let [current-ns (str *ns*)]
      (fn [args]
        `(let [resolve# (fn [value#]
                          (try
                            (async/invoke-continuation ~r value#)
                            (catch ~(if (:js-globals env) :default `Throwable) t#
                              (async/invoke-continuation ~e t#))))
               reject# (fn [error#]
                         (try
                           (async/invoke-continuation ~e error#)
                           (catch ~(if (:js-globals env) :default `Throwable) t#
                             (async/invoke-continuation ~e t#))))
               current-spin-id# ec/*spin-id*]
           ;; Dispatch via symbol-call dispatch (adapter + handler from registry)
           (org.replikativ.spindel.engine.effects/dispatch-symbol-call
            ec/*execution-context*
            '~sym
            [~@args]
            current-spin-id#
            ~current-ns
            resolve#
            reject#))))))

#?(:clj
   (defn ^:no-doc build-breakpoints
     "Build breakpoints for spin macro - symbol call-forms, built from effects registry.

     Called at macro-expansion time to pick up all registered effects.

     Strategy:
     1. Check registry for each effect
     2. If :direct-handler-sym is present, use make-direct-breakpoint
     3. Otherwise, use make-symbol-call-breakpoint for standard dispatch
     4. This allows users to override await/track before spindel loads while
        keeping direct handler optimization for the default implementation"
     []
     (let [reg (org.replikativ.spindel.engine.effects/get-effect-syntax)

           entries (for [[sym {:keys [handler direct-handler-sym]}] reg]
                     (let [vname (symbol (str "bp__" (munge (str sym))))
                           breakpoint-fn (if direct-handler-sym
                                           (make-direct-breakpoint direct-handler-sym)
                                           (make-symbol-call-breakpoint sym))
                           _ (intern *ns* vname breakpoint-fn)
                           var-sym (symbol (str *ns*) (name vname))]
                       [sym var-sym]))]
       (merge async/breakpoints
              (into {} entries)))))

#?(:clj
   (defn ^:no-doc build-cps-fn
     "Build CPS function from body and breakpoints.

      Parameters:
      - body: Clojure forms to transform (as list)
      - breakpoints: Map of symbol → breakpoint handler
      - env: Macro expansion environment (&env)

      Returns: CPS function code with signature:
        (fn [resolve reject] ...) — execution-context & spin-id via dynamic binding (*execution-context*, *spin-id*)."
     [body breakpoints env]
     (let [r (gensym "resolve")
           e (gensym "reject")
           params {:r r :e e :env env :breakpoints breakpoints}
           ;; ioc/invert handles macro expansion internally via expand-macro
           ;; Don't use macroexpand-all as it introduces CLJ-specific code for CLJS targets
           expanded (cons 'do body)
           ;; Detect target platform at macroexpansion time. A reader
           ;; conditional in the syntax-quoted body wouldn't help: the
           ;; macro's source is read once (in CLJ), so #?(:clj … :cljs …)
           ;; resolves to the :clj branch even when expanding for CLJS.
           is-cljs?  (some? (:js-globals env))
           ;; Thunk class reference per platform:
           ;; - CLJ: Java FQCN (dots). No Var named Thunk exists.
           ;; - CLJS: namespaced symbol (slash). The dotted form would be
           ;;   parsed as nested property access on a symbol called `is`,
           ;;   which CLJS resolves as a local — and thus shadows when the
           ;;   user namespace :refers `cljs.test/is`, producing the bogus
           ;;   `cljs.test.is.simm.partial_cps.runtime.Thunk`.
           thunk-sym (if is-cljs?
                       'is.simm.partial-cps.runtime/Thunk
                       'is.simm.partial_cps.runtime.Thunk)]
       `(fn [~r ~e]
          (try
            ;; Execute CPS body with trampoline support
            ;; If already in trampoline, return result directly (may be Thunk)
            ;; Otherwise, establish trampoline to unwrap Thunks from loop/recur
            (if async/*in-trampoline*
              ~(ioc/invert params expanded)
              (binding [async/*in-trampoline* true]
                (loop [result# ~(ioc/invert params expanded)]
                  (if (instance? ~thunk-sym result#)
                    (recur ((.-f result#)))
                    result#))))
            (catch ~(if is-cljs? :default `Throwable) t# (~e t#)))))))

#?(:clj
   (defn- captured-locals-form
     "Build a `{'sym sym …}` form snapshotting the runtime values of the
      body's free variables. register-spin! `identical?`-compares this map
      across re-registrations to decide whether a spin's captured
      environment changed — and so whether the re-evaluated form must
      re-run rather than serve its cached result. Free vars are found by
      a proper analysis (engine.free-vars); on analyzer failure it falls
      back to all enclosing locals (a safe over-approximation)."
     [env body]
     (into {}
           (map (fn [s] [(list 'quote s) s]))
           (free-vars/free-variables-or-all env (cons 'do body)))))

#?(:clj
   (defmacro spin
     "Create a cached, reactive spin that automatically tracks dependencies and re-executes when dependencies change.

      TEMPLATE MODEL: Each invocation creates a NEW spin instance.
      Spins are like functions - use defonce for singleton semantics.

      The spin ID is generated DETERMINISTICALLY using hash-chain addressing:
      - Each spin ID depends on source location + all previous addresses
      - Sequential spins at same location get different IDs
      - Forked contexts replay with same ID sequence (deterministic)

      This enables fork/restore: re-execution of forked state finds the same spin IDs.

  The macro takes only body forms and resolves the execution-context at EVAL time
  via current-execution-context (use with-context to bind it):
  - (spin body ...)

  Note: If you want to be explicit about grouping multiple top-level
  forms, wrap them in (do ...).

      The spin macro:
      - Auto-generates a DETERMINISTIC ID via hash-chain addressing
      - Transforms body to CPS with execution-context threading
      - Wraps in Spin for automatic caching and reactivity
      - Tracks dependencies via await
      - Re-executes when dependencies change
      - Automatically cleaned up when GC'd
      "
     [& body]
     (let [execution-context-expr `(ec/current-execution-context)
           cps-fn (build-cps-fn body (build-breakpoints) &env)
           ;; Free variables the body captures, snapshotted as {'sym sym}
           ;; so register-spin! can identical?-detect a changed environment.
           captured (captured-locals-form &env body)
           ;; Capture source location at macro expansion time
           source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(let [ctx# ~execution-context-expr]
          (ec/with-context ctx#
            ;; Generate deterministic spin ID via hash-chain addressing
            (let [spin-id# (addressing/next-address! ctx# "spin" ~source-loc)]
              (spin-core/make-spin ~cps-fn spin-id# ~captured))))))

   #?(:clj
      (defmacro effect
        "Create an effect-only spin for reactive side effects without rendering.

      Automatically tracks dependencies and re-executes when they change,
      but returns nil instead of a vnode — use this when you need reactive
      behavior without contributing to the rendered output.

      Use `effect` when you need reactive behavior without rendering:
      - Focus management
      - Analytics/logging
      - External system synchronization
      - DOM imperative operations

      Example:
        ;; Focus management - no invisible div hack needed
        (effect
          (let [focus-id @(track focus-signal)]
            (when focus-id
              (when-let [el (.getElementById js/document focus-id)]
                (.focus el)))))

        ;; Logging changes
        (effect
          (let [value @(track my-signal)]
            (js/console.log \"Value changed:\" value)))

      The effect participates in the reactive graph just like a regular spin,
      tracking all signals accessed via `track` or `await`. When those signals
      change, the effect re-runs.

      Unlike `spin`, the return value of the body is discarded (nil is returned).
      This makes it clear that the effect is for side effects only."
        [& body]
        (let [execution-context-expr `(ec/current-execution-context)
           ;; Wrap body to return nil after executing
              body-with-nil (concat body [nil])
              cps-fn (build-cps-fn body-with-nil (build-breakpoints) &env)
           ;; Free variables the body captures (see `spin`).
              captured (captured-locals-form &env body)
           ;; Capture source location at macro expansion time
              source-loc {:file *file*
                          :line (:line (meta &form))
                          :column (:column (meta &form))}]
          `(let [ctx# ~execution-context-expr]
             (ec/with-context ctx#
            ;; Generate deterministic effect ID via hash-chain addressing
               (let [spin-id# (addressing/next-address! ctx# "effect" ~source-loc)]
                 (spin-core/make-spin ~cps-fn spin-id# ~captured))))))))
