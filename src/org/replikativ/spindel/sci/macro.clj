(ns org.replikativ.spindel.sci.macro
  "SCI integration for spindel - enables full spin/await/track syntax in SCI contexts.

  Architecture: CPS transformation runs INSIDE SCI for correct symbol resolution.
  Native spindel primitives (make-spin, next-address!, etc.) are injected from
  outside as functions, while the spin macro and await are defined as SCI source
  that delegates to partial-cps for CPS transformation.

  This gives agents vanilla spindel syntax:
    (spin (let [x (await other-spin)] (* x 2)))

  Without exposing spindel internals or requiring callback-style code.

  Example:
    (def sci-ctx (create-spin-macro-context {:runtime rt}))

    (binding [ec/*execution-context* rt]
      (sci/eval-string* sci-ctx
        \"(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                   '[org.replikativ.spindel.effects.await :refer [await]])
         (spin
           (let [x (await other-spin)]
             (* x 2)))\"))"
  (:require [sci.core :as sci]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.effects.track :as eff-track]
            [org.replikativ.spindel.sci.boundary :as boundary]
            [is.simm.partial-cps.async :as async]
            [org.replikativ.spindel.sci.core :as sci-core]))

(defn create-spin-macro-context
  "Create SCI context with full spin/await/track syntax support.

  Architecture:
  - Native spindel primitives (make-spin, next-address!, etc.) are injected
    from outside as functions in SCI's namespace map
  - partial-cps source is loaded INTO SCI so CPS transformation happens
    entirely inside SCI (correct symbol resolution)
  - The spin macro is defined inside SCI using partial-cps async for CPS
  - await is re-exported from partial-cps under spindel's namespace

  This gives agents vanilla spindel code without callbacks or internals.

  Options:
    :runtime - Execution context (required)
    :native-spins - Map of native spins to expose (will be wrapped via boundary)
    :expose-track? - Include track effect (default true)

  Example:
    (def rt (ctx/create-execution-context))

    (def sci-ctx
      (create-spin-macro-context
        {:runtime rt}))

    (binding [ec/*execution-context* rt]
      (sci/eval-string* sci-ctx
        \"(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                   '[org.replikativ.spindel.effects.await :refer [await]])
         @(spin
            (let [a (spin 10)
                  b (spin 20)
                  x (await a)
                  y (await b)]
              (+ x y)))\"))  ; => 30"
  [{:keys [runtime native-spins expose-track?]
    :or {native-spins {}
         expose-track? true}}]
  (let [;; Wrap all native spins for SCI (BoundaryTask pattern)
        wrapped-natives (into {}
                              (map (fn [[k v]]
                                     [k (boundary/wrap-spin-for-sci v runtime)])
                                   native-spins))

        ;; Build namespace map — inject native primitives SCI code needs
        namespaces (merge
                    {;; spin macro placeholder — will be redefined after load-partial-cps!
                     'org.replikativ.spindel.spin.cps {}

                      ;; await placeholder — will be redefined after load-partial-cps!
                     'org.replikativ.spindel.effects.await {}

                      ;; Native runtime functions the spin macro references
                     'org.replikativ.spindel.spin.core
                     {'make-spin spin-core/make-spin}

                     'org.replikativ.spindel.engine.core
                     {'*execution-context* (sci/new-dynamic-var '*execution-context* runtime)
                      '*spin-id* (sci/new-dynamic-var '*spin-id* nil)
                      'current-execution-context ec/current-execution-context
                      'with-context (var ec/with-context)
                      'spin-current-result ec/spin-current-result
                      'deps-track-spin! ec/deps-track-spin!}

                     'org.replikativ.spindel.engine.addressing
                     {'next-address! addressing/next-address!}

                     'is.simm.partial-cps.async
                     {'invoke-continuation async/invoke-continuation
                      '*in-trampoline* (sci/new-dynamic-var '*in-trampoline* false)}}

                     ;; Optionally include track effect
                    (when expose-track?
                      {'org.replikativ.spindel.effects.track
                       {'track (var eff-track/track)
                        'track-handler eff-track/track-handler}}))

        ;; Create SCI context
        sci-ctx (sci/init
                 {:classes (sci-core/common-classes)
                  :features #{:clj}
                  :bindings wrapped-natives
                  :namespaces namespaces})]

    ;; Load partial-cps for CPS transformation support (runs inside SCI)
    (sci-core/load-partial-cps! sci-ctx)

    ;; Extend partial-cps breakpoints to also recognize spindel's await namespace.
    ;; The async macro checks breakpoints at macro-expansion time, so updating the
    ;; var before defining spin ensures the CPS transformer recognizes await from
    ;; either namespace.
    (sci/eval-string* sci-ctx
                      "(in-ns 'is.simm.partial-cps.async)
       (def breakpoints (assoc breakpoints
                          'org.replikativ.spindel.effects.await/await
                          'is.simm.partial-cps.async/await-handler))")

    ;; Re-export await under spindel's namespace for agent ergonomics
    (sci/eval-string* sci-ctx
                      "(ns org.replikativ.spindel.effects.await
         (:require [is.simm.partial-cps.async :as pcps-async]))
       (def await pcps-async/await)")

    ;; Define spin macro inside SCI — uses partial-cps async for CPS transformation
    ;; and native make-spin/next-address! from injected namespaces
    (sci/eval-string* sci-ctx
                      "(ns org.replikativ.spindel.spin.cps
         (:require [is.simm.partial-cps.async :as pcps-async]
                   [org.replikativ.spindel.spin.core :as spin-core]
                   [org.replikativ.spindel.engine.core :as ec]
                   [org.replikativ.spindel.engine.addressing :as addressing]))

       (defmacro spin [& body]
         (let [cps-form `(pcps-async/async ~@body)]
           `(let [ctx# (ec/current-execution-context)]
              (ec/with-context ctx#
                (let [spin-id# (addressing/next-address!
                                 ctx# \"spin\"
                                 ~{:file (str *file*)
                                   :line (:line (meta &form))
                                   :column (:column (meta &form))})]
                  (spin-core/make-spin ~cps-form spin-id#))))))")

    sci-ctx))

;; =============================================================================
;; Convenience Helpers
;; =============================================================================

(defn eval-spin
  "Evaluate spin code in SCI context and return the Spin.

  Example:
    (def my-spin
      (eval-spin sci-ctx
        \"(require '[org.replikativ.spindel.spin.cps :refer [spin]])
         (spin (+ 1 2))\"))"
  [sci-ctx code-str]
  (sci/eval-string* sci-ctx code-str))

(defn eval-and-deref
  "Evaluate spin code and immediately deref (blocking).

  Convenience for testing. Requires *execution-context* to be bound.

  Example:
    (binding [ec/*execution-context* rt]
      (eval-and-deref sci-ctx
        \"(require '[org.replikativ.spindel.spin.cps :refer [spin]])
         (spin (* 7 6))\"))  ; => 42"
  [sci-ctx code-str]
  (let [spin (eval-spin sci-ctx code-str)]
    @spin))

;; =============================================================================
;; Usage Examples
;; =============================================================================

(comment
  (require '[org.replikativ.spindel.engine.context :as ctx]
           '[org.replikativ.spindel.spin.cps :refer [spin]])

  ;; Setup
  (def rt (ctx/create-execution-context))

  ;; Test 1: Simple spin in SCI
  (def sci-ctx (create-spin-macro-context {:runtime rt}))

  (binding [ec/*execution-context* rt]
    (eval-and-deref sci-ctx
                    "(require '[org.replikativ.spindel.spin.cps :refer [spin]])
       (spin (+ 100 200))"))  ; => 300

  ;; Test 2: Spin with await — CPS transformation happens inside SCI
  (binding [ec/*execution-context* rt]
    (eval-and-deref sci-ctx
                    "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                 '[org.replikativ.spindel.effects.await :refer [await]])
       (def a (spin 10))
       (def b (spin 20))
       @(spin (let [x (await a)
                    y (await b)]
                (+ x y)))"))  ; => 30

  ;; Test 3: Await native spins from outside SCI
  (binding [ec/*execution-context* rt]
    (def native-spin (spin (* 7 6))))  ; => 42

  (def sci-ctx-native
    (create-spin-macro-context
     {:runtime rt
      :native-spins {'other-spin native-spin}}))

  (binding [ec/*execution-context* rt]
    (eval-and-deref sci-ctx-native
                    "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                 '[org.replikativ.spindel.effects.await :refer [await]])
       (spin
         (let [x (await other-spin)]
           (* x 2)))"))  ; => 84
  )
