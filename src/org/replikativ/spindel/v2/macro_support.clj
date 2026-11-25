(ns org.replikativ.spindel.v2.macro-support
  "Internal, macro time: the scope walk under `v2/effectful?` and the DOM
   element macros (phase-d design §2.5). Not a public API.

   A macro can declare how the walk treats its calls, in its var metadata
   under `::scope`:

   - `::transparent`: the walk does not expand the macro and walks its
     operands as expressions of the caller's scope;
   - `::opaque`: the walk does not enter the call at all.

   Both are trusted assertions, not checked: a `::transparent` macro's
   expansion must introduce no effect and must evaluate each operand in the
   caller's execution scope (not in a closure, a nested body or a later
   turn); an `::opaque` macro's operands must all be bodies of their own,
   with nothing evaluated in the caller. A macro that breaks its declaration
   misleads the walk: an effect it hides makes an effectful form look
   effect-free."
  (:require [is.simm.partial-cps.ioc :as ioc]))

(defn local?
  "Whether `sym` is a local in macro environment `env` (CLJ or CLJS)."
  [env sym]
  (if (:js-globals env) (contains? (:locals env) sym) (contains? env sym)))

(defn head-name
  "The qualified name `h` resolves to in `env`, or nil (locals, special
   forms, unresolvable symbols)."
  [env h]
  (when (and (symbol? h) (not (local? env h)))
    (try (ioc/var-name env h) (catch Exception _ nil))))

(defn macro-meta
  "The var metadata of the macro `h` names in `env`, or nil."
  [env h]
  (when (and (symbol? h) (not (local? env h)))
    (if (:js-globals env)
      (let [m (ioc/resolve-macro-var-cljs env h)] (when (:macro m) m))
      (let [v (try (resolve env h) (catch Exception _ nil))]
        (when (and (var? v) (:macro (meta v))) (meta v))))))

(defn special?
  "Whether `h` is a special form of the target platform."
  [env h]
  (or (special-symbol? h)
      (and (:js-globals env) (contains? @(requiring-resolve 'cljs.analyzer/specials) h))))

(def ^:private body-operands
  "The v2 body forms: each body is a scope of its own; these functions
   return the operands the caller evaluates."
  {'org.replikativ.spindel.v2.core/spin (constantly nil)
   'org.replikativ.spindel.v2.core/task (constantly nil)
   'org.replikativ.spindel.v2.core/body* (constantly nil)
   'org.replikativ.spindel.v2.core/task-with (fn [[_ opts]] [opts])           ; (task-with opts & body)
   'org.replikativ.spindel.v2.core/aseq (fn [[_ [_ init]]] [init])})       ; (aseq [s init] & body)

(def ^:private body-forms
  "The bodies of each v2 body form: what runs in its own scope, later."
  {'org.replikativ.spindel.v2.core/spin rest
   'org.replikativ.spindel.v2.core/task rest
   'org.replikativ.spindel.v2.core/body* rest
   'org.replikativ.spindel.v2.core/task-with nnext
   'org.replikativ.spindel.v2.core/aseq nnext})

(defn body-of
  "The body forms of `form` when it is a v2 body form (`spin`, `task`,
   `task-with`, `body*`, `aseq`) in `env`, else nil."
  [env form]
  (when (seq? form)
    (when-let [f (get body-forms (head-name env (first form)))]
      (or (f form) ()))))

(defn some-call
  "The first truthy `(f env call)` over the calls of `form` that execute in
   its own scope, `env` the macro environment there; `::skip` from `f`
   skips that call's subforms. The walk tracks `let`/`loop`/`letfn`/`catch`
   locals; it does not enter `quote`, `var`, `fn`/`fn*`, `reify`,
   `deftype`, the functions of a `letfn`, the bodies of the v2 body forms
   (it walks their caller-evaluated operands: `aseq`'s initial state,
   `task-with`'s options) nor a macro declared `::opaque`; it expands
   other macros with `env`, except one declared `::transparent`, whose
   operands it walks."
  [env form f]
  (letfn [(scan-all [env xs] (some #(scan env %) xs))
          (scan-bindings [env bvec body]
            (loop [env env ps (seq (partition 2 bvec))]
              (if-let [[[b init] & more] ps]
                (or (scan env init) (recur (ioc/bind-locals env (ioc/binding-symbols b)) more))
                (scan-all env body))))
          (scan-special [env [h & args]]
            (case h
              (quote var fn* reify* deftype* defrecord*) nil
              (let* loop*) (scan-bindings env (first args) (rest args))
              letfn* (scan-all (ioc/bind-locals env (take-nth 2 (first args))) (rest args))
              catch (let [[_ local & body] args] (scan-all (ioc/bind-locals env [local]) body))
              case* (if (:js-globals env)
                      (let [[t _ vs default] args] (or (scan env t) (scan-all env vs) (scan env default)))
                      (let [[t _ _ default table] args]
                        (or (scan env t) (scan env default) (scan-all env (map #(second (val %)) table)))))
              . (let [[target & members] args]
                  (or (scan env target)
                      (some #(cond (seq? %) (scan-all env (rest %)) (symbol? %) nil :else (scan env %)) members)))
              (scan-all env args)))
          (scan [env x]
            (cond
              (seq? x)
              (when (seq x)
                (let [h (first x)
                      r (f env x)]
                  (cond
                    (= ::skip r) nil
                    r r
                    (not (symbol? h)) (scan-all env x)
                    (local? env h) (scan-all env (rest x))
                    (special? env h) (scan-special env x)
                    :else
                    (if-let [operands (get body-operands (head-name env h))]
                      (scan-all env (operands x))
                      (case (::scope (macro-meta env h))
                        ::opaque nil
                        ::transparent (scan-all env (rest x))
                        (if-let [[expanded] (ioc/expand-macro x env)]
                          (scan env expanded)
                          (scan-all env (rest x))))))))
              (map? x) (some (fn [[k v]] (or (scan env k) (scan env v))) x)
              (coll? x) (scan-all env x)
              :else nil))]
    (scan env form)))
