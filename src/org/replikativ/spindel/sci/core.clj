(ns org.replikativ.spindel.sci.core
  "Shared SCI infrastructure for spindel integration.

  Provides common code used by both boundary.clj and macro.clj:
  - load-partial-cps! - CPS runtime loader
  - COMMON_CLASSES - Class allowlist for SCI contexts

  This is the single source of truth for SCI context setup."
  (:require [sci.core :as sci]))

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
  (sci/add-namespace! sci-ctx 'is.simm.partial-cps.runtime
    {'bound-fn @(resolve 'is.simm.partial-cps.runtime/bound-fn)
     '->thunk  @(resolve 'is.simm.partial-cps.runtime/->thunk)
     '->Thunk  @(resolve 'is.simm.partial-cps.runtime/->Thunk)})
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
  Java classes, not Clojure vars."
  []
  ;; Ensure namespaces are loaded before referencing their deftypes
  (require 'is.simm.partial-cps.runtime)
  (require 'org.replikativ.spindel.spin.core)
  {'clojure.lang.Var clojure.lang.Var
   'clojure.lang.Namespace clojure.lang.Namespace
   'clojure.lang.IFn clojure.lang.IFn
   'clojure.lang.Atom clojure.lang.Atom
   'clojure.lang.IDeref clojure.lang.IDeref
   ;; Deftypes are Java classes - use Class/forName with munged names
   'is.simm.partial_cps.runtime.Thunk (Class/forName "is.simm.partial_cps.runtime.Thunk")
   'org.replikativ.spindel.spin.core.Spin (Class/forName "org.replikativ.spindel.spin.core.Spin")
   'java.lang.Throwable java.lang.Throwable
   'is.simm.partial-cps.async/Throwable java.lang.Throwable
   :allow :all})
