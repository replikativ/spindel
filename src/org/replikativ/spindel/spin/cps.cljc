(ns org.replikativ.spindel.spin.cps
  "CPS transformation machinery for spin macro"
  (:require [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.addressing :as addressing]
            [org.replikativ.spindel.effects.core]
            [org.replikativ.spindel.effects.await]   ;; Load await effect handler
            [org.replikativ.spindel.effects.track]   ;; Load track effect handler
            [org.replikativ.spindel.spin.continuation :as cont]
            [is.simm.partial-cps.async :as async]
            #?(:clj [is.simm.partial-cps.ioc :as ioc])
            [is.simm.partial-cps.runtime]
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
               current-spin-id# rtc/*spin-id*]
           ;; Direct call to handler, bypassing dispatch
           (~direct-fn-sym ~@args current-spin-id# ~current-ns resolve# reject#))))))

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
     (let [reg (org.replikativ.spindel.effects.core/get-effect-syntax)

           entries (for [[sym {:keys [handler direct-handler-sym]}] reg]
                     (let [ vname (symbol (str "bp__" (name handler)))
                           breakpoint-fn (make-direct-breakpoint direct-handler-sym)
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
           expanded (cons 'do body)]
       `(fn [~r ~e]
          (try
            ;; Execute CPS body with trampoline support
            ;; If already in trampoline, return result directly (may be Thunk)
            ;; Otherwise, establish trampoline to unwrap Thunks from loop/recur
            (if async/*in-trampoline*
              ~(ioc/invert params expanded)
              (binding [async/*in-trampoline* true]
                (loop [result# ~(ioc/invert params expanded)]
                  (if (instance? is.simm.partial_cps.runtime.Thunk result#)
                    (recur ((.-f ^is.simm.partial_cps.runtime.Thunk result#)))
                    result#))))
            (catch ~(if (:js-globals env) :default `Throwable) t# (~e t#)))))))

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
  via current-execution-context-atom (use with-execution-context to bind it):
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
     (let [execution-context-expr `(rtc/current-execution-context)
           cps-fn (build-cps-fn body (build-breakpoints) &env)
           ;; Capture source location at macro expansion time
           source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(let [ctx# ~execution-context-expr]
          (rtc/with-execution-context ctx#
            ;; Generate deterministic spin ID via hash-chain addressing
            (let [spin-id# (addressing/next-address! ctx# "spin" ~source-loc)]
              (spin-core/make-spin ~cps-fn spin-id#))))))

#?(:clj
   (defmacro effect
     "Create an effect-only spin for reactive side effects without rendering.

      Similar to React's useEffect or SolidJS's createEffect. The effect
      automatically tracks dependencies and re-executes when they change,
      but returns nil instead of a vnode.

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
     (let [execution-context-expr `(rtc/current-execution-context)
           ;; Wrap body to return nil after executing
           body-with-nil (concat body [nil])
           cps-fn (build-cps-fn body-with-nil (build-breakpoints) &env)
           ;; Capture source location at macro expansion time
           source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(let [ctx# ~execution-context-expr]
          (rtc/with-execution-context ctx#
            ;; Generate deterministic effect ID via hash-chain addressing
            (let [spin-id# (addressing/next-address! ctx# "effect" ~source-loc)]
              (spin-core/make-spin ~cps-fn spin-id#))))))))
