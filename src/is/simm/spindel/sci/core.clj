(ns is.simm.spindel.sci.core
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
  "Load partial-cps source files into SCI context.

  Required for CPS transformation to work inside SCI. Without this,
  await/track effects won't be recognized as breakpoints.

  The partial-cps runtime must run entirely inside SCI for symbol
  resolution to work correctly during macro expansion.

  See: SCI_INTEGRATION_FINDINGS.md"
  [sci-ctx]
  (let [partial-cps-root "../partial-cps/src/is/simm/partial_cps"
        runtime-src (slurp (str partial-cps-root "/runtime.cljc"))
        ioc-src (slurp (str partial-cps-root "/ioc.clj"))
        async-src (slurp (str partial-cps-root "/async.cljc"))]

    (sci/eval-string* sci-ctx runtime-src)
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
  (require 'is.simm.spindel.spin.core)
  {'clojure.lang.Var clojure.lang.Var
   'clojure.lang.Namespace clojure.lang.Namespace
   'clojure.lang.IFn clojure.lang.IFn
   'clojure.lang.Atom clojure.lang.Atom
   'clojure.lang.IDeref clojure.lang.IDeref
   ;; Deftypes are Java classes - use Class/forName with munged names
   'is.simm.partial_cps.runtime.Thunk (Class/forName "is.simm.partial_cps.runtime.Thunk")
   'is.simm.spindel.spin.core.Spin (Class/forName "is.simm.spindel.spin.core.Spin")
   'java.lang.Throwable java.lang.Throwable
   'is.simm.partial-cps.async/Throwable java.lang.Throwable
   :allow :all})
