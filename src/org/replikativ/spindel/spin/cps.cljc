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
  (fn [{:keys [spin-id env form]} r e]
    (let [;; Where this call is in the source. partial-cps hands the handler
          ;; the call form from 0.1.61 on; before that a site is known by its
          ;; namespace only, and sites of one effect in one spin can be told
          ;; apart only by the order in which they run.
          {:keys [line column]} (meta form)
          current-ns (if line
                       {:ns (str *ns*) :line line :column column}
                       (str *ns*))]
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
   (do
     (def ^:private hof-names
       #{"map" "mapv" "filter" "filterv" "remove" "keep" "reduce" "run!" "doseq" "for"})

     (defn- core-name
       "The clojure.core / cljs.core function name `sym` resolves to, or nil —
       also when a binding inside the spin body shadows it."
       [ctx sym]
       (when (and (symbol? sym) (not (contains? (:locals ctx) sym)))
         (let [v (ioc/var-name (:env ctx) sym)]
           (when (and v (#{"clojure.core" "cljs.core"} (namespace v)))
             (name v)))))

     (defn- form-name
       "The name of the special form or clojure.core / cljs.core macro or
       function `op` stands for, or nil."
       [ctx op]
       (if (and (symbol? op) (special-symbol? op)) (name op) (core-name ctx op)))

     (defn- bound-names
       "The local names a binding form (a symbol or destructuring pattern) binds."
       [binding]
       (set (take-nth 2 (destructure [binding nil]))))

     (defn- occurs? [sym body]
       (some #{sym} (tree-seq coll? seq body)))

     (defn- fn-literal
       "[params body] of a single-arity fn literal, else nil — also for a
       variadic one and for a named one that refers to itself."
       [form]
       (when (and (seq? form) (#{'fn 'fn*} (first form)))
         (let [[_ & more] form
               self (when (symbol? (first more)) (first more))
               more (if self (rest more) more)]
           (when (and (vector? (first more))
                      (not (some #{'&} (first more)))
                      (not (and self (occurs? self (rest more)))))
             [(first more) (rest more)]))))

     (defn- effectful? [ctx body]
       (ioc/has-breakpoints? (cons 'do body) ctx))

     (declare rewrite-hofs)

     (defn- inline-call
       "A fn literal's body applied in place, `bindings` [param arg …] binding
       its params: a loop when the body recurs, so the recur still targets it."
       [bindings body]
       (if (occurs? 'recur body)
         `(loop ~bindings ~@body)
         `(let ~bindings ~@body)))

     (defn- seq-loop
       "A loop over `coll` from `init`: `step` gets [element-sym out-sym] and
       returns the next out, evaluated before the walk advances. With
       `reduced?`, a reduced out ends the loop with its value."
       ([coll init step] (seq-loop coll init step false))
       ([coll init step reduced?]
        (let [s (gensym "s") out (gensym "out") x (gensym "x") v (gensym "v")]
          `(loop [~out ~init ~s (seq ~coll)]
             (if ~s
               (let [~x (first ~s)
                     ~v ~(step x out)]
                 ~(if reduced?
                    `(if (reduced? ~v) (deref ~v) (recur ~v (next ~s)))
                    `(recur ~v (next ~s))))
               ~out)))))

     (defn- with-locals [ctx bindings]
       (update ctx :locals (fnil into #{}) (mapcat bound-names bindings)))

     (defn- rewrite-hof
       "The loop for a higher-order call whose fn literal performs effects, or
       nil when the call is not one of those."
       [form ctx]
       (let [[op & args] form
             hof (core-name ctx op)]
         (when (hof-names hof)
           (case hof
             ("doseq" "for")
             (let [[bindings & body] args]
               (when (and (vector? bindings) (= 2 (count bindings)) (effectful? ctx body))
                 (let [[params coll] bindings
                       body (map #(rewrite-hofs % (with-locals ctx [params])) body)
                       coll (rewrite-hofs coll ctx)]
                   (if (= hof "for")
                     (seq-loop coll [] (fn [x out] `(conj ~out (let [~params ~x] ~@body))))
                     (seq-loop coll nil (fn [x _] `(let [~params ~x] ~@body nil)))))))

             "reduce"
             (let [[f init coll] args
                   [params body] (fn-literal f)]
               (when (and params (= 3 (count args)) (= 2 (count params)) (effectful? ctx body))
                 (let [[acc-p x-p] params
                       body (map #(rewrite-hofs % (with-locals ctx params)) body)]
                   (seq-loop (rewrite-hofs coll ctx) (rewrite-hofs init ctx)
                             (fn [x out] (inline-call [acc-p out x-p x] body))
                             true))))

             ;; map mapv filter filterv remove keep run!
             (let [[f coll & more] args
                   [params body] (fn-literal f)]
               (when (and params (empty? more) (= 1 (count params)) (effectful? ctx body))
                 (let [body (map #(rewrite-hofs % (with-locals ctx params)) body)
                       coll (rewrite-hofs coll ctx)
                       [p] params
                       call (fn [x] (inline-call [p x] body))]
                   (case hof
                     ("map" "mapv") (seq-loop coll [] (fn [x out] `(conj ~out ~(call x))))
                     ("filter" "filterv") (seq-loop coll [] (fn [x out] `(if ~(call x) (conj ~out ~x) ~out)))
                     "remove" (seq-loop coll [] (fn [x out] `(if ~(call x) ~out (conj ~out ~x))))
                     "keep" (seq-loop coll [] (fn [x out] `(let [v# ~(call x)] (if (nil? v#) ~out (conj ~out v#)))))
                     "run!" (seq-loop coll nil (fn [x _] `(do ~(call x) nil)))))))))))

     (defn- rewrite-bindings
       "A let-style binding vector with its inits rewritten in order, each in
       the scope of the names bound before it, and the scope after the last:
       [bindings ctx]. With `seq?`, a doseq / for binding vector."
       [bindings ctx seq?]
       (reduce (fn [[out ctx] [b init]]
                 (cond
                   (and seq? (= :let b)) (let [[bs ctx] (rewrite-bindings init ctx false)]
                                           [(conj out b bs) ctx])
                   (and seq? (keyword? b)) [(conj out b (rewrite-hofs init ctx)) ctx]
                   :else [(conj out b (rewrite-hofs init ctx)) (with-locals ctx [b])]))
               [[] ctx]
               (partition 2 bindings)))

     (def ^:private let-forms
       #{"let" "let*" "loop" "loop*" "when-let" "if-let" "when-some" "if-some"
         "when-first" "with-open" "dotimes"})

     (defn- rewrite-scoped
       "A binding form rewritten with its locals in scope, or nil when `form` is
       not one."
       [form ctx]
       (let [[op bindings & body] form
             op-name (form-name ctx op)
             scoped (fn [bindings ctx]
                      (apply list op bindings (map #(rewrite-hofs % ctx) body)))]
         (cond
           (= 'catch op)
           (let [[cls local & body] (rest form)]
             (apply list op cls local (map #(rewrite-hofs % (with-locals ctx [local])) body)))

           (not (vector? bindings)) nil

           (let-forms op-name) (apply scoped (rewrite-bindings bindings ctx false))
           (#{"doseq" "for"} op-name) (apply scoped (rewrite-bindings bindings ctx true))
           (= "letfn" op-name) (scoped bindings (with-locals ctx (map first bindings)))
           (= "letfn*" op-name) (scoped bindings (with-locals ctx (take-nth 2 bindings))))))

     (defn ^:no-doc rewrite-hofs
       "Rewrite, in a spin body, the higher-order calls (map, mapv, filter,
       filterv, remove, keep, reduce with an initial value, run!, and doseq
       and for over one binding) whose fn literal performs an effect (await,
       track, sample, …) into loops the CPS transformation sees through —
       eagerly, into vectors, in the order the call evaluates. A call whose
       function performs none keeps its laziness; a name bound inside the
       body is not taken for the core function it shadows; nested spins, fns
       and quoted forms are left alone."
       [form ctx]
       (cond
         (seq? form)
         (let [op (first form)]
           (cond
             (#{'quote 'fn 'fn*} op) form
             (= "spin" (some-> (ioc/var-name (:env ctx) op) name)) form
             :else (with-meta (or (rewrite-hof form ctx)
                                  (rewrite-scoped form ctx)
                                  (apply list (map #(rewrite-hofs % ctx) form)))
                     (meta form))))
         (vector? form) (with-meta (mapv #(rewrite-hofs % ctx) form) (meta form))
         (map? form) (with-meta (into {} (map (fn [[k v]] [(rewrite-hofs k ctx) (rewrite-hofs v ctx)])) form) (meta form))
         :else form))))

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
           ;; higher-order calls over effectful fn literals become loops
           expanded (rewrite-hofs (cons 'do body) {:breakpoints breakpoints :env env})
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
            (if (async/in-trampoline?)
              ~(ioc/invert params expanded)
              (async/with-trampoline ~(ioc/invert params expanded)))
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
