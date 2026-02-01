(ns is.simm.spindel.sci.boundary
  "SCI/Native boundary for spindel integration.

  Enables transparent interop between native spindel spins and SCI-evaluated code:
  - BoundaryTask wrapper propagates *execution-context* bindings across boundary
  - make-spin-for-sci creates spins inside SCI contexts
  - Full bidirectional communication: Native ↔ SCI

  Based on zeitlauf SCI integration findings (see SCI_RUNTIME_BOUNDARY_DESIGN.md)."
  (:require [sci.core :as sci]
            [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.spin.core :as spin-core]
            [is.simm.spindel.sci.core :as sci-core]))

;; =============================================================================
;; BoundaryTask Wrapper
;; =============================================================================

;; Wrapper for native spins to be called from SCI.
;; Establishes proper runtime bindings when SCI code invokes native spins.
;; Without this wrapper, native spin code would not see *execution-context*.
(deftype BoundaryTask [task runtime task-spin-id]
  clojure.lang.IFn
  (invoke [this resolve reject]
    (binding [rtc/*execution-context* runtime
              rtc/*spin-id* task-spin-id]
      (task resolve reject)))

  clojure.lang.IDeref
  (deref [this]
    (binding [rtc/*execution-context* runtime]
      @task)))

(defn wrap-spin-for-sci
  "Wrap a native spin for use in SCI contexts.

  Returns a BoundaryTask that establishes proper bindings when called from SCI.

  Example:
    (def native-spin (spin (+ 1 2)))
    (def wrapped (wrap-spin-for-sci native-spin rt))

    ;; In SCI:
    (wrapped resolve reject)  ; Works! Bindings established automatically"
  [task runtime]
  (BoundaryTask. task runtime (.-spin_id task)))

;; =============================================================================
;; SCI Spin Creation
;; =============================================================================

(defn make-spin-for-sci
  "Create a spin from SCI context with proper bindings.

  Wraps spin-core/make-spin to establish native bindings during creation.

  Parameters:
    spin-fn - CPS function (fn [resolve reject] ...)
    spin-id - Keyword identifier for the spin
    runtime - Native execution context

  Example in SCI:
    (require '[spindel.spin :as spin])
    (spin/make-spin
      (fn [resolve reject]
        (resolve (+ 1 2)))
      :my-spin)"
  [spin-fn spin-id runtime]
  (binding [rtc/*execution-context* runtime
            rtc/*spin-id* spin-id]
    (spin-core/make-spin spin-fn spin-id)))

;; =============================================================================
;; SCI Context Creation
;; =============================================================================

(defn create-spindel-sci-context
  "Create SCI context with spindel support (functional API only).

  Provides:
  - make-spin for creating spins in SCI
  - Full partial-cps loaded for CPS transformation
  - Access to runtime state (optional)

  Options:
    :runtime - Execution context (required)
    :expose-runtime-state? - If true, expose get-state/swap-state! (default false)
    :native-spins - Map of native spins to expose (will be wrapped automatically)

  Example:
    (def rt (ctx/create-execution-context))
    (def sci-ctx
      (create-spindel-sci-context
        {:runtime rt
         :native-spins {'my-native-spin some-native-spin}}))

    ;; In SCI:
    (require '[spindel.spin :as spin])
    (def my-spin
      (spin/make-spin
        (fn [resolve reject]
          (my-native-spin
            (fn [v] (resolve (* v 2)))
            reject))
        :my-sci-spin))"
  [{:keys [runtime expose-runtime-state? native-spins]
    :or {expose-runtime-state? false
         native-spins {}}}]
  (let [;; Wrap all native spins for SCI
        wrapped-natives (into {} (map (fn [[k v]]
                                        [k (wrap-spin-for-sci v runtime)])
                                      native-spins))

        ;; Create base SCI context
        sci-ctx (sci/init
                  {:classes (sci-core/common-classes)
                   :features #{:clj}
                   :bindings wrapped-natives
                   :namespaces (merge
                                 {'spindel.spin
                                  {'make-spin (fn [spin-fn spin-id]
                                                (make-spin-for-sci spin-fn spin-id runtime))}}
                                 (when expose-runtime-state?
                                   {'spindel.runtime
                                    {'get-state (fn [path] (rtc/get-state path))
                                     'swap-state! (fn [path f & args] (apply rtc/swap-state! path f args))}}))})]

    ;; Load partial-cps for CPS transformation support
    (sci-core/load-partial-cps! sci-ctx)

    sci-ctx))

;; =============================================================================
;; Usage Examples
;; =============================================================================

(comment
  (require '[is.simm.spindel.runtime.context :as ctx]
           '[is.simm.spindel.spin.cps :refer [spin]])

  ;; Setup
  (def rt (ctx/create-execution-context))

  ;; Create native spin
  (binding [rtc/*execution-context* rt]
    (def native-spin (spin (+ 10 5))))  ; Returns 15

  ;; Create SCI context with native spin exposed
  (def sci-ctx
    (create-spindel-sci-context
      {:runtime rt
       :native-spins {'native-spin native-spin}}))

  ;; SCI code that uses native spin
  (def sci-code
    "(require '[spindel.spin :as spin])
     (spin/make-spin
       (fn [resolve reject]
         (native-spin
           (fn [value] (resolve (* value 2)))
           reject))
       :sci-spin)")

  (def sci-spin (sci/eval-string* sci-ctx sci-code))

  ;; Execute from native
  (binding [rtc/*execution-context* rt]
    @sci-spin)  ; => 30

  ;; Bidirectional chain: Native → SCI → Native
  (binding [rtc/*execution-context* rt]
    (def native-2 (spin (* 3 2))))  ; Returns 6

  (def sci-ctx-chain
    (create-spindel-sci-context
      {:runtime rt
       :native-spins {'n1 native-spin
                      'n2 native-2}}))

  (def chain-code
    "(require '[spindel.spin :as spin])
     (spin/make-spin
       (fn [resolve reject]
         (n1
           (fn [v1]
             (n2
               (fn [v2]
                 (resolve (+ v1 v2)))
               reject))
           reject))
       :chain-spin)")

  (def chained (sci/eval-string* sci-ctx-chain chain-code))

  (binding [rtc/*execution-context* rt]
    @chained)  ; => 21 (15 + 6)
  )
