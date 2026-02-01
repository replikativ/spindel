(ns is.simm.spindel.sci.macro
  "Native macro pass-through for SCI - enables full spin syntax in SCI contexts.

  This approach exposes the native `spin` macro and all native functions it references
  to SCI's namespace map. When the macro expands, it produces code with qualified symbols
  that resolve to the exposed native functions.

  **Key advantage**: Don't need to load spindel source into SCI - just expose compiled functions!

  Example:
    (def sci-ctx (create-spin-macro-context {:runtime rt}))

    ;; In SCI - identical syntax to native!
    (sci/eval-string* sci-ctx
      \"(require '[is.simm.spindel.spin.cps :refer [spin]]
                 '[is.simm.spindel.effects.await :refer [await]])
       (spin
         (let [x (await other-spin)]
           (* x 2)))\")"
  (:require [sci.core :as sci]
            [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.runtime.addressing :as addressing]
            [is.simm.spindel.spin.core :as spin-core]
            [is.simm.spindel.spin.cps :refer [spin]]
            [is.simm.spindel.effects.await :as eff-await]
            [is.simm.spindel.effects.track :as eff-track]
            [is.simm.partial-cps.async :as async]
            [is.simm.spindel.sci.core :as sci-core]))

(defn create-spin-macro-context
  "Create SCI context with native spin macro support.

  Exposes:
  - spin macro (full CPS transformation)
  - await effect (suspend until completion)
  - track effect (reactive signal tracking)
  - All native runtime functions

  Options:
    :runtime - Execution context (required)
    :native-spins - Map of native spins to expose (will be wrapped via boundary)
    :expose-track? - Include track effect (default true)

  Example:
    (require '[is.simm.spindel.runtime.context :as ctx]
             '[is.simm.spindel.sci.boundary :as boundary])

    (def rt (ctx/create-execution-context))

    (binding [rtc/*execution-context* rt]
      (def native-spin (spin (+ 10 20))))  ; => 30

    (def sci-ctx
      (create-spin-macro-context
        {:runtime rt
         :native-spins {'my-native-spin native-spin}}))

    ;; SCI code with full spin syntax!
    (binding [rtc/*execution-context* rt]
      (def sci-spin
        (sci/eval-string* sci-ctx
          \"(require '[is.simm.spindel.spin.cps :refer [spin]]
                     '[is.simm.spindel.effects.await :refer [await]])
           (spin
             (let [x (await my-native-spin)]
               (* x 2)))\")))

    (binding [rtc/*execution-context* rt]
      @sci-spin)  ; => 60"
  [{:keys [runtime native-spins expose-track?]
    :or {native-spins {}
         expose-track? true}}]
  (let [;; Wrap all native spins for SCI (BoundaryTask pattern)
        wrapped-natives (into {}
                              (map (fn [[k v]]
                                     (require 'is.simm.spindel.sci.boundary)
                                     [k ((resolve 'is.simm.spindel.sci.boundary/wrap-spin-for-sci) v runtime)])
                                   native-spins))

        ;; Build namespace map
        namespaces (merge
                     {;; The spin macro
                      'is.simm.spindel.spin.cps
                      {'spin (var spin)}

                      ;; await effect
                      'is.simm.spindel.effects.await
                      {'await (var eff-await/await)
                       'await-handler eff-await/await-handler}

                      ;; Native runtime functions the macro references
                      'is.simm.spindel.spin.core
                      {'make-spin spin-core/make-spin}

                      'is.simm.spindel.runtime.core
                      {'*execution-context* (sci/new-dynamic-var '*execution-context* runtime)
                       '*spin-id* (sci/new-dynamic-var '*spin-id* nil)
                       'current-execution-context rtc/current-execution-context
                       'with-execution-context (var rtc/with-execution-context)
                       'spin-current-result rtc/spin-current-result
                       'deps-track-spin! rtc/deps-track-spin!}

                      'is.simm.spindel.runtime.addressing
                      {'next-address! addressing/next-address!}

                      'is.simm.partial-cps.async
                      {'invoke-continuation async/invoke-continuation
                       '*in-trampoline* (sci/new-dynamic-var '*in-trampoline* false)}}

                     ;; Optionally include track effect
                     (when expose-track?
                       {'is.simm.spindel.effects.track
                        {'track (var eff-track/track)
                         'track-handler eff-track/track-handler}}))

        ;; Create SCI context
        sci-ctx (sci/init
                  {:classes (sci-core/common-classes)
                   :features #{:clj}
                   :bindings wrapped-natives
                   :namespaces namespaces})]

    ;; Load partial-cps for runtime support
    (sci-core/load-partial-cps! sci-ctx)

    sci-ctx))

;; =============================================================================
;; Convenience Helpers
;; =============================================================================

(defn eval-spin
  "Evaluate spin code in SCI context and return the Spin.

  Example:
    (def my-spin
      (eval-spin sci-ctx
        \"(require '[is.simm.spindel.spin.cps :refer [spin]])
         (spin (+ 1 2))\"))"
  [sci-ctx code-str]
  (sci/eval-string* sci-ctx code-str))

(defn eval-and-deref
  "Evaluate spin code and immediately deref (blocking).

  Convenience for testing. Requires *execution-context* to be bound.

  Example:
    (binding [rtc/*execution-context* rt]
      (eval-and-deref sci-ctx
        \"(require '[is.simm.spindel.spin.cps :refer [spin]])
         (spin (* 7 6))\"))  ; => 42"
  [sci-ctx code-str]
  (let [spin (eval-spin sci-ctx code-str)]
    @spin))

;; =============================================================================
;; Usage Examples
;; =============================================================================

(comment
  (require '[is.simm.spindel.runtime.context :as ctx]
           '[is.simm.spindel.sci.boundary :as boundary])

  ;; Setup
  (def rt (ctx/create-execution-context))

  ;; Test 1: Simple spin
  (def sci-ctx (create-spin-macro-context {:runtime rt}))

  (binding [rtc/*execution-context* rt]
    (eval-and-deref sci-ctx
      "(require '[is.simm.spindel.spin.cps :refer [spin]])
       (spin (+ 100 200))"))  ; => 300

  ;; Test 2: Spin with await
  (binding [rtc/*execution-context* rt]
    (def native-spin (spin (* 7 6))))  ; => 42

  (def sci-ctx-await
    (create-spin-macro-context
      {:runtime rt
       :native-spins {'other-spin native-spin}}))

  (binding [rtc/*execution-context* rt]
    (eval-and-deref sci-ctx-await
      "(require '[is.simm.spindel.spin.cps :refer [spin]]
                 '[is.simm.spindel.effects.await :refer [await]])
       (spin
         (let [x (await other-spin)]
           (* x 2)))"))  ; => 84

  ;; Test 3: Chain multiple awaits
  (binding [rtc/*execution-context* rt]
    (def spin-a (spin (+ 10 5)))   ; => 15
    (def spin-b (spin (* 3 2))))   ; => 6

  (def sci-ctx-chain
    (create-spin-macro-context
      {:runtime rt
       :native-spins {'a spin-a
                      'b spin-b}}))

  (binding [rtc/*execution-context* rt]
    (eval-and-deref sci-ctx-chain
      "(require '[is.simm.spindel.spin.cps :refer [spin]]
                 '[is.simm.spindel.effects.await :refer [await]])
       (spin
         (let [x (await a)
               y (await b)]
           (+ x y)))"))  ; => 21
  )
