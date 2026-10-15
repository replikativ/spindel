(ns org.replikativ.spindel.sci.core
  "Shared SCI infrastructure for spindel integration.

  Provides common code used by both boundary.clj and macro.clj:
  - load-partial-cps! - CPS runtime loader
  - COMMON_CLASSES - Class allowlist for SCI contexts

  This is the single source of truth for SCI context setup."
  (:require [sci.core :as sci]
            [sci.ctx-store :as ctx-store]
            [org.replikativ.spindel.engine.core :as ec]))

(defn ^:no-doc same-world-or-descendant?
  "True when `candidate` is the captured world or one of its COW descendants.

  Continuation slice restoration may construct another ExecutionContext record
  for the same branch, so stable fork identity—not object identity—is the base
  case."
  [candidate captured]
  (loop [ctx candidate]
    (cond
      (nil? ctx) false
      (= (:fork-id ctx) (:fork-id captured)) true
      :else (recur (:parent-ctx ctx)))))

(defn- world-bound-fn
  "partial-cps's `bound-fn` for SCI code: conveys the creator's bindings as
  `bound-fn*` does, but not its world over a fork's. Called in the captured
  world or a COW descendant, `f` runs in the calling world and interpreter (an
  interpreter forked after wrapping it acts in the fork, on the fork's vars);
  called elsewhere, in the captured ones — the continuation rule of
  `macro/invoke-sci-awaitable`."
  [f]
  (let [captured (when (ec/execution-context-bound?) (ec/current-execution-context))
        g (bound-fn* (fn [overrides args]
                       (with-bindings overrides (apply f args))))]
    (fn [& args]
      (let [ambient (when (ec/execution-context-bound?) (ec/current-execution-context))
            here? (and ambient (or (nil? captured)
                                   (same-world-or-descendant? ambient captured)))
            interpreter ctx-store/*ctx*]
        (g (cond-> {}
             here? (assoc #'ec/*execution-context* ambient)
             (and here? interpreter) (assoc #'ctx-store/*ctx* interpreter))
           args)))))

;; =============================================================================
;; CPS Runtime Loading
;; =============================================================================

(defn load-partial-cps!
  "Load partial-cps into a SCI context.

  Required for CPS transformation to work inside SCI: without this,
  await/track/sample/observe effects won't be recognized as breakpoints.

  `ioc.clj` and `async.cljc` ARE interpreted inside SCI — they carry the
  CPS-transform machinery (`invert`, the `async` macro) that must expand
  against SCI's symbol environment.

  `runtime.cljc` is NOT interpreted — it is injected as a NATIVE namespace
  using the compiled `Thunk`/`->thunk`/`bound-fn`. Interpreting it would
  run `(deftype Thunk [f])` inside SCI, producing a `sci.impl.deftype.SciType`
  rather than the compiled `is.simm.partial_cps.runtime.Thunk` class. The
  trampoline — both the SCI-expanded `spin` macro wrapper and the compiled
  `invoke-continuation` — checks `(instance? is.simm.partial_cps.runtime.Thunk x)`
  against the *compiled* class. A `SciType` is never an instance of it, so the
  trampoline silently never bounces and any `recur` after a breakpoint inside
  a loop/dotimes hangs forever. Keeping one canonical compiled `Thunk` class
  fixes that.

  See: SCI_INTEGRATION_FINDINGS.md"
  [sci-ctx]
  (require 'is.simm.partial-cps.runtime)
  ;; Native runtime namespace — one canonical compiled Thunk class.
  ;; Inject the WHOLE runtime ns (all publics, native) — the interpreted async/seq CPS
  ;; macros reference runtime/thunk?, runtime/force-thunk, … (added in partial-cps 0.1.57).
  ;; A hand-picked subset silently breaks whenever partial-cps adds a runtime helper the
  ;; macros emit (this bit the SCI spin/gen-aseq path via `runtime/thunk?`). All runtime
  ;; publics are plain native fns / the ONE compiled Thunk ctor, so this stays canonical.
  ;; Not `enter-trampoline!`/`leave-trampoline!`: code could leave an
  ;; activation unbalanced, read the token of the one running (the host's), or
  ;; set a stale one, so that another computation's continuation that carries
  ;; it returns its Thunk to no trampoline. The interpreted `with-trampoline`
  ;; only needs `call-in-trampoline`, which is balanced.
  (sci/add-namespace! sci-ctx 'is.simm.partial-cps.runtime
                      (-> (update-vals (ns-publics 'is.simm.partial-cps.runtime) deref)
                          (dissoc 'enter-trampoline! 'leave-trampoline!)
                          (assoc 'bound-fn world-bound-fn)))
  (let [ioc-src (slurp (clojure.java.io/resource "is/simm/partial_cps/ioc.clj"))
        async-src (slurp (clojure.java.io/resource "is/simm/partial_cps/async.cljc"))]
    (sci/eval-string* sci-ctx ioc-src)
    (sci/eval-string* sci-ctx async-src)
    sci-ctx))

;; =============================================================================
;; Common Classes
;; =============================================================================

(defn common-classes
  "Standard class allowlist for spindel SCI contexts.

  Returns a map of classes needed for:
  - Clojure runtime (Var, Namespace, IFn, etc.)
  - Spindel types (Spin, Thunk)
  - Exception handling (Throwable)
  - Dereferencing (IDeref)
  - Atoms (for state)

  Lazily resolved to avoid class loading issues at namespace load time.
  Uses Class/forName for deftype classes (Thunk, Spin) since they are
  Java classes, not Clojure vars.

  LOCKED BY DEFAULT — no `:allow :all`. On the JVM, `:allow :all` turns SCI's
  per-class interop gate OFF (ADR 0015), so a spindel-backed context with it set
  is a full JVM escape from otherwise-sandboxed code: from ANY object,
  `.getClass` → `.getClassLoader` → `.loadClass \"java.lang.Runtime\"` → reflect
  reaches a host shell. That is fine for a TRUSTED context (a developer's own
  frontend), but every UNTRUSTED consumer — an agent sandbox running code an
  outsider can influence — inherited it, silently escapable. So the default here
  is fail-safe: interop is gated to this allowlist, and a caller that genuinely
  needs wider host reach opts in EXPLICITLY with `(assoc (common-classes) :allow
  :all)` — a locally visible, auditable decision rather than a hidden default.

  The spindel engine itself needs none of that reach — its whole suite (916
  tests, incl. sci/lock_test) passes with interop locked to this map; the
  deref/atom/Spin/Thunk types above are all it touches. On CLJS `:allow :all` was already redundant, since
  `:unrestricted` bypasses the interop check upstream (ADR 0015), so removing it
  changes only JVM contexts. A JVM consumer whose spin code does interop on a
  class NOT listed here now gets a loud \"Method X on class Y not allowed!\" at
  the call site — register the class (or opt into `:allow :all` if trusted)
  rather than have the sandbox stay wide open by default."
  []
  ;; Ensure namespaces are loaded before referencing their deftypes
  (require 'is.simm.partial-cps.runtime)
  (require 'org.replikativ.spindel.spin.core)
  {;; Named (`instance?`), never called: their static members (`find`,
   ;; `intern`, `getThreadBindings`, …) hand code the HOST's vars, so its
   ;; functions run outside the sandbox, and its dynamic bindings, the live
   ;; execution context among them.
   'clojure.lang.Var {:class clojure.lang.Var :closed true}
   'clojure.lang.Namespace {:class clojure.lang.Namespace :closed true}
   'clojure.lang.IFn clojure.lang.IFn
   'clojure.lang.Atom clojure.lang.Atom
   'clojure.lang.IDeref clojure.lang.IDeref
   ;; Deftypes are Java classes - use Class/forName with munged names
   'is.simm.partial_cps.runtime.Thunk (Class/forName "is.simm.partial_cps.runtime.Thunk")
   'org.replikativ.spindel.spin.core.Spin (Class/forName "org.replikativ.spindel.spin.core.Spin")
   'java.lang.Throwable java.lang.Throwable
   'is.simm.partial-cps.ioc/Throwable java.lang.Throwable
   'is.simm.partial-cps.async/Throwable java.lang.Throwable})
