(ns org.replikativ.spindel.engine.free-vars
  "Free-variable analysis for spin bodies — compile-time only.

   `free-variables` returns the set of enclosing lexical locals a body
   actually references: the variables a spin's closure captures. The
   `spin` macro records this set so the engine can detect, on
   re-registration, whether a spin's captured environment changed.

   This is a real analysis, not the empty-env unresolvable-symbol hack
   (`distributed-scope`'s `free-variables`). That hack analyses with an
   *empty* environment and collects symbols the analyzer cannot resolve,
   which

     - silently MISSES a local whose name shadows a var — `name`,
       `count`, `type`, `val`, … resolve to clojure.core and are
       dropped; a spin capturing one would go stale, and
     - THROWS when a captured local is in function position — the
       unresolved symbol is replaced by `nil` and `(nil x)` fails the
       analyzer's validation pass.

   Here the enclosing locals (the keys of `&env`) are registered WITH
   the analyzer. tools.analyzer.jvm (CLJ) then resolves them as locals —
   shadowing a var correctly, never throwing in call position — and
   performs the macroexpansion and lexical scope resolution, so a
   body-internal binding form that shadows an enclosing local is handled.
   CLJ body-internal locals are uniquified by the analyzer, so
   intersecting the referenced `:local` names with the enclosing set is
   exact.

   Runs at macro-expansion time only. `cljs.analyzer` is required lazily
   (it is heavy and only needed when expanding for a CLJS target), the
   same pattern partial-cps's ioc.clj uses."
  (:require [clojure.set :as set]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.tools.analyzer.ast :as ana.ast]))

;; =============================================================================
;; CLJ — tools.analyzer.jvm
;; =============================================================================

(defn- clj-free-variables
  "Analyse `body` with `enclosing` locals registered as `:binding` nodes;
   return the subset of `enclosing` referenced as `:op :local` in the AST.
   Body-internal locals are uniquified by the analyzer and so fall
   outside `enclosing` — the intersection is exact."
  [enclosing body]
  (let [base   (ana.jvm/empty-env)
        locals (into {}
                     (map (fn [s]
                            [s {:op :binding :name s :form s
                                :local :let :env base :children []}]))
                     enclosing)
        ast    (ana.jvm/analyze body (assoc base :locals locals))]
    (into #{}
          (comp (filter #(= :local (:op %)))
                (map :name)
                (filter enclosing))
          (ana.ast/nodes ast))))

;; =============================================================================
;; CLJS — cljs.analyzer (lazily resolved)
;; =============================================================================

(defn- cljs-local-names
  "Names referenced by `:op :local` nodes anywhere in a cljs.analyzer AST."
  [node]
  (if-not (map? node)
    #{}
    (reduce (fn [acc k]
              (let [c (get node k)]
                (set/union acc
                           (if (sequential? c)
                             (reduce #(set/union %1 (cljs-local-names %2)) #{} c)
                             (cljs-local-names c)))))
            (if (= :local (:op node)) #{(:name node)} #{})
            (:children node))))

(defn- cljs-free-variables
  "The CLJS analyzer `&env` already carries `:locals` for the enclosing
   scope. Analyse `body` and return the subset of those locals referenced
   as `:op :local`. A body-internal local that shadows an enclosing name
   can over-include it — harmless (a needless equality check)."
  [env body]
  (let [analyze       (requiring-resolve 'cljs.analyzer/analyze)
        warn-handlers (requiring-resolve 'cljs.analyzer/*cljs-warning-handlers*)
        enclosing     (set (keys (:locals env)))
        ast           (with-bindings {warn-handlers []}
                        (analyze env body))]
    (set/intersection (cljs-local-names ast) enclosing)))

;; =============================================================================
;; Public API
;; =============================================================================

(defn enclosing-locals
  "The full set of enclosing lexical locals visible at the macro site."
  [env]
  (if (:js-globals env)
    (set (keys (:locals env)))
    (set (keys env))))

(defn free-variables
  "Set of enclosing lexical locals referenced by `body`.

   `env`  — the macro `&env` (CLJ: sym→LocalBinding; CLJS: analyzer env
            carrying `:locals`).
   `body` — body forms wrapped in one form, e.g. `(do …)`.

   Result ⊆ the enclosing locals. May throw if the analyzer cannot
   handle `body`; callers wanting resilience use `free-variables-or-all`."
  [env body]
  (if (:js-globals env)
    (cljs-free-variables env body)
    (clj-free-variables (set (keys env)) body)))

(defn free-variables-or-all
  "Like `free-variables` but never throws: on any analyzer failure, fall
   back to ALL enclosing locals — a correct, less-precise
   over-approximation (an unchanged spin may re-run, but it is never
   wrongly skipped)."
  [env body]
  (try
    (free-variables env body)
    (catch Throwable _ (enclosing-locals env))))
