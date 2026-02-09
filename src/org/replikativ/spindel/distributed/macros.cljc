(ns org.replikativ.spindel.distributed.macros
  "Macros for defining distributed functions using spindel spins.

  Provides defn-spin-remote and spin-remote macros that mirror
  distributed-scope's defn-sp-remote and sp-remote but use spindel's
  spin system instead of Missionary.

  Key features:
  - Explicit argument vectors for data flow auditing
  - Compile-time free variable validation
  - Pre-registration of remote functions
  - Seamless integration with spindel's await/track effects

  Usage:
    (defn-spin-remote my-distributed-fn [arg1]
      (spin-remote server-id [arg1]
        ;; This runs on server-id
        (let [result (await (database-query arg1))]
          (process result))))

    ;; In caller
    (spin
      (let [result (await (my-distributed-fn server-id))]
        (use result)))"
  (:refer-clojure :exclude [await])
  (:require [is.simm.distributed-scope :as ds]
            [org.replikativ.spindel.distributed.core :as dist]
            [org.replikativ.spindel.engine.core]
            [org.replikativ.spindel.spin.cps]
            [org.replikativ.spindel.effects.await]
            #?(:clj [clojure.tools.analyzer.jvm :as ana.jvm])
            #?(:clj [cljs.analyzer :as ana.js])
            [clojure.set :as set]
            [clojure.walk :as walk])
  #?(:cljs (:require-macros [org.replikativ.spindel.distributed.macros])))

;; =============================================================================
;; Free Variable Analysis (reused from distributed-scope)
;; =============================================================================

#?(:clj
   (defn free-variables
     "Analyze code to find unbound/free variables.
      Uses clojure.tools.analyzer.jvm for CLJ, cljs.analyzer for CLJS.

      Returns a set of symbols that are used but not defined in scope."
     [env body]
     (let [free-variables (atom #{})]
       (if (:js-globals env)
         ;; ClojureScript analysis
         (binding [ana.js/*cljs-warning-handlers*
                   [(fn [warning-type _env extra]
                      (when (= warning-type :undeclared-var)
                        (swap! free-variables conj (:suffix extra))))]]
           (ana.js/analyze env body))
         ;; Clojure JVM analysis
         (ana.jvm/analyze
           body
           (ana.jvm/empty-env)
           {:passes-opts
            {:validate/unresolvable-symbol-handler
             (fn [_a s _b]
               (swap! free-variables conj s)
               ;; Return valid AST node for nil to continue analysis
               {:op :const :env {} :type :nil :literal? true
                :val nil :form nil :top-level true :o-tag nil :tag nil})}}))
       (disj @free-variables 'clojure))))

;; =============================================================================
;; spin-remote placeholder (throws outside defn-spin-remote)
;; =============================================================================

(defn spin-remote
  "Execute body on remote peer using spindel spins.

  Must be used inside defn-spin-remote. Throws if used standalone.

  Usage:
    ;; Simple: peer-id only (uses :default context)
    (spin-remote server-id [arg1 arg2] ...body...)

    ;; With context-id: target specific execution context
    (spin-remote [server-id :my-fork] [arg1 arg2] ...body...)

  The scope can be:
  - peer-id (symbol/expression) - Uses :default context on that peer
  - [peer-id context-id] - Targets specific context on that peer

  The arg vector explicitly lists which variables from the current scope
  should be captured and sent to the remote peer."
  [_scope _explicit-args & _body]
  (throw (ex-info "spin-remote must be used inside defn-spin-remote"
                  {:hint "Wrap with (defn-spin-remote fn-name [args] ...)"})))

;; =============================================================================
;; defn-spin-remote Macro
;; =============================================================================

#?(:clj
   (defmacro defn-spin-remote
     "Define a distributed function using spindel spins.

      Like distributed-scope's defn-sp-remote, but uses spindel's spin
      system for local execution and returns Spin instead of
      Missionary spin.

      Remote bodies are registered with distributed-scope's registry and
      execute as go blocks for wire compatibility. The local function
      returns a spindel spin that awaits the remote result.

      Usage:
        ;; Simple: peer-id only (uses :default context)
        (defn-spin-remote fetch-page [server-id page-uuid]
          (spin-remote server-id [page-uuid]
            (let [db (db/get-db)]
              (crud/format-page-with-blocks db page-uuid))))

        ;; With context-id: target specific execution context
        (defn-spin-remote process-in-fork [server-id context-id data]
          (spin-remote [server-id context-id] [data]
            (heavy-computation data)))

      The scope can be:
      - peer-id (symbol/expression) - Uses :default context on that peer
      - [peer-id context-id] - Targets specific context on that peer

      The explicit arg vector declares which values cross the network boundary.
      Compile-time analysis validates that all free variables in the body are declared.

      Options (via metadata):
        ^:no-validate - Skip free variable validation"
     {:style/indent [1 :form [1]]
      :arglists '([fn-name [params*] & body])}
     [fn-name args & body]
     {:pre [(symbol? fn-name) (vector? args)]}

     (let [;; Track all remote forms found in body
           remote-forms (atom [])

           ;; Walk body to find and transform spin-remote invocations
           new-body
           (walk/postwalk
             (fn [form]
               (if (and (seq? form)
                        (= 'spin-remote (first form)))
                 (let [[_ scope-form explicit-args & remote-body] form
                       _ (when-not (vector? explicit-args)
                           (throw (ex-info "spin-remote requires explicit arg vector"
                                           {:form form
                                            :got explicit-args
                                            :hint "(spin-remote peer-id [arg1 arg2] body...) or (spin-remote [peer-id ctx-id] [args] body...)"})))

                       ;; Parse scope-form: either peer-id or [peer-id context-id]
                       [peer-id-expr context-id-expr]
                       (if (and (vector? scope-form) (= 2 (count scope-form)))
                         ;; [peer-id context-id] form
                         [(first scope-form) (second scope-form)]
                         ;; Simple peer-id form (context-id defaults to :default)
                         [scope-form nil])

                       ;; Analyze for free variables
                       combined-body `(do ~@remote-body)
                       free-vars (free-variables &env combined-body)
                       declared-args (set explicit-args)
                       missing (set/difference free-vars declared-args)
                       extra (set/difference declared-args free-vars)

                       ;; Validate all free vars are declared
                       _ (when (seq missing)
                           (throw (ex-info (str "spin-remote: variables used but not in arg list")
                                           {:missing missing
                                            :declared declared-args
                                            :used free-vars
                                            :form form})))

                       ;; Warn about unused declared args (debug level)
                       _ (when (seq extra)
                           (println "DEBUG: spin-remote: unused args" extra))

                       ;; Generate unique function name for this remote block
                       remote-idx (count @remote-forms)
                       ns-sym (symbol (str *ns*)
                                      (str "spin-remote-" (name fn-name) "-" remote-idx))

                       ;; Build arg-map for wire transport
                       ;; Include reserved :__context-id__ key for routing
                       user-args (into {} (map (fn [s] [(keyword (str s)) s]) explicit-args))
                       arg-map (if context-id-expr
                                 `(assoc ~user-args :__context-id__ ~context-id-expr)
                                 user-args)]

                   ;; Record this remote form for later registration
                   (swap! remote-forms conj
                          {:form form
                           :explicit-args explicit-args
                           :remote-body remote-body
                           :ns-sym ns-sym})

                   ;; Replace with call that invokes remote
                   ;; For top-level spin-remote (in defn body): wrap in await + chan->spin
                   ;; For nested spin-remote (in remote body): use core.async <! directly
                   ;; The outer spin wrapper will handle the CPS transformation
                   `(org.replikativ.spindel.effects.await/await
                      (dist/chan->spin
                        (ds/invoke-remote ~peer-id-expr '~ns-sym ~arg-map))))
                 form))
             `(do ~@body))

           ;; Generate remote function definitions
           ;; These use spindel spin->chan for proper CPS and effect support
           ;; The remote function extracts __context-id__ and binds the appropriate context
           remote-defs
           (mapv
             (fn [{:keys [explicit-args remote-body ns-sym]}]
               (let [local-sym (symbol (name ns-sym))]
                 {:def `(defn ~local-sym [arg-map#]
                          ;; Extract context-id and user args
                          (let [context-id# (:__context-id__ arg-map#)
                                user-args# (dissoc arg-map# :__context-id__)
                                ;; Destructure user args
                                {:keys ~(vec explicit-args)} user-args#
                                ;; Look up execution context
                                ctx# (dist/get-context context-id#)]
                            ;; CRITICAL: Bind execution context AROUND the spin creation
                            ;; The spin macro calls current-runtime at creation time for ID generation
                            ;; So the binding must be in effect before (spin ...) is evaluated
                            (if ctx#
                              (binding [org.replikativ.spindel.engine.core/*execution-context* ctx#]
                                (dist/spin->chan
                                  (org.replikativ.spindel.spin.cps/spin
                                    ~@remote-body)))
                              ;; No context registered - this will throw!
                              ;; All remote spins should have a context registered
                              (throw (ex-info "No execution context registered for remote spin"
                                              {:context-id context-id#
                                               :fn-name '~ns-sym
                                               :hint "Register context with (dist/register-context! :default ctx)"})))))
                  :registration `(ds/register-remote-fn! '~ns-sym ~local-sym)}))
             @remote-forms)]

       ;; Emit code that:
       ;; 1. Defines remote functions
       ;; 2. Registers them with distributed-scope
       ;; 3. Defines the main function (returns spindel spin)
       `(do
          ;; Define remote functions
          ~@(map :def remote-defs)

          ;; Register with distributed-scope
          ~@(map :registration remote-defs)

          ;; Define main distributed function
          ;; Returns a spindel spin that can be awaited
          (defn ~fn-name ~args
            (org.replikativ.spindel.spin.cps/spin
              ~new-body))))))
