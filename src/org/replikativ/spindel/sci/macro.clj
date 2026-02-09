(ns org.replikativ.spindel.sci.macro
  "Native macro pass-through for SCI - enables full spin syntax in SCI contexts.

  This approach exposes the native `spin` macro and all native functions it references
  to SCI's namespace map. When the macro expands, it produces code with qualified symbols
  that resolve to the exposed native functions.

  **Key advantage**: Don't need to load spindel source into SCI - just expose compiled functions!

  Example:
    (def sci-ctx (create-spin-macro-context {:runtime rt}))

    ;; In SCI - identical syntax to native!
    (sci/eval-string* sci-ctx
      \"(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                 '[org.replikativ.spindel.effects.await :refer [await]])
       (spin
         (let [x (await other-spin)]
           (* x 2)))\")"
  (:require [sci.core :as sci]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :as eff-await]
            [org.replikativ.spindel.effects.track :as eff-track]
            [org.replikativ.spindel.sci.boundary :as boundary]
            [is.simm.partial-cps.async :as async]
            [org.replikativ.spindel.sci.core :as sci-core]))

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
    (require '[org.replikativ.spindel.engine.context :as ctx]
             '[org.replikativ.spindel.sci.boundary :as boundary])

    (def rt (ctx/create-execution-context))

    (binding [ec/*execution-context* rt]
      (def native-spin (spin (+ 10 20))))  ; => 30

    (def sci-ctx
      (create-spin-macro-context
        {:runtime rt
         :native-spins {'my-native-spin native-spin}}))

    ;; SCI code with full spin syntax!
    (binding [ec/*execution-context* rt]
      (def sci-spin
        (sci/eval-string* sci-ctx
          \"(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                     '[org.replikativ.spindel.effects.await :refer [await]])
           (spin
             (let [x (await my-native-spin)]
               (* x 2)))\")))

    (binding [ec/*execution-context* rt]
      @sci-spin)  ; => 60"
  [{:keys [runtime native-spins expose-track?]
    :or {native-spins {}
         expose-track? true}}]
  (let [;; Wrap all native spins for SCI (BoundaryTask pattern)
        wrapped-natives (into {}
                              (map (fn [[k v]]
                                     [k (boundary/wrap-spin-for-sci v runtime)])
                                   native-spins))

        ;; Build namespace map
        namespaces (merge
                     {;; The spin macro
                      'org.replikativ.spindel.spin.cps
                      {'spin (var spin)}

                      ;; await effect
                      'org.replikativ.spindel.effects.await
                      {'await (var eff-await/await)
                       'await-handler eff-await/await-handler}

                      ;; Native runtime functions the macro references
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
           '[org.replikativ.spindel.sci.boundary :as boundary])

  ;; Setup
  (def rt (ctx/create-execution-context))

  ;; Test 1: Simple spin
  (def sci-ctx (create-spin-macro-context {:runtime rt}))

  (binding [ec/*execution-context* rt]
    (eval-and-deref sci-ctx
      "(require '[org.replikativ.spindel.spin.cps :refer [spin]])
       (spin (+ 100 200))"))  ; => 300

  ;; Test 2: Spin with await
  (binding [ec/*execution-context* rt]
    (def native-spin (spin (* 7 6))))  ; => 42

  (def sci-ctx-await
    (create-spin-macro-context
      {:runtime rt
       :native-spins {'other-spin native-spin}}))

  (binding [ec/*execution-context* rt]
    (eval-and-deref sci-ctx-await
      "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                 '[org.replikativ.spindel.effects.await :refer [await]])
       (spin
         (let [x (await other-spin)]
           (* x 2)))"))  ; => 84

  ;; Test 3: Chain multiple awaits
  (binding [ec/*execution-context* rt]
    (def spin-a (spin (+ 10 5)))   ; => 15
    (def spin-b (spin (* 3 2))))   ; => 6

  (def sci-ctx-chain
    (create-spin-macro-context
      {:runtime rt
       :native-spins {'a spin-a
                      'b spin-b}}))

  (binding [ec/*execution-context* rt]
    (eval-and-deref sci-ctx-chain
      "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                 '[org.replikativ.spindel.effects.await :refer [await]])
       (spin
         (let [x (await a)
               y (await b)]
           (+ x y)))"))  ; => 21
  )
