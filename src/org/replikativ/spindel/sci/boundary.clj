(ns org.replikativ.spindel.sci.boundary
  "SCI/Native boundary for spindel integration.

  Enables transparent interop between native spindel spins and SCI-evaluated code:
  - BoundaryTask wrapper propagates *execution-context* bindings across boundary
  - make-spin-for-sci creates spins inside SCI contexts
  - Full bidirectional communication: Native ↔ SCI

  Based on zeitlauf SCI integration findings (see SCI_RUNTIME_BOUNDARY_DESIGN.md)."
  (:require [sci.core :as sci]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.sci.core :as sci-core]))

;; =============================================================================
;; BoundaryTask Wrapper
;; =============================================================================

;; Wrapper for native spins to be called from SCI.
;; Establishes proper runtime bindings when SCI code invokes native spins.
;; Without this wrapper, native spin code would not see *execution-context*.
(deftype BoundaryTask [task runtime task-spin-id]
  clojure.lang.IFn
  (invoke [this resolve reject]
    (let [caller-runtime (ec/current-execution-context)
          caller-spin-id ec/*spin-id*
          return-to-caller
          (fn [continuation]
            (fn [value]
              (binding [ec/*execution-context* caller-runtime
                        ec/*spin-id* caller-spin-id]
                (continuation value))))]
      ;; The task executes where it is hosted, but its result returns to the
      ;; caller's world. Without the wrapped callbacks, awaiting a task in a
      ;; nested child world migrates the caller's continuation into that child
      ;; and caches the caller's result on the wrong execution context.
      (binding [ec/*execution-context* runtime
                ec/*spin-id* task-spin-id]
        (task (return-to-caller resolve)
              (return-to-caller reject)))))

  clojure.lang.IDeref
  (deref [this]
    (binding [ec/*execution-context* runtime]
      @task)))

(defn wrap-spin-for-sci
  "Wrap a native spin for use in SCI contexts.

  Returns a BoundaryTask that executes in the task runtime and re-enters the
  caller runtime for resolve/reject.

  Example:
    (def native-spin (spin (+ 1 2)))
    (def wrapped (wrap-spin-for-sci native-spin rt))

    ;; In SCI:
    (wrapped resolve reject)  ; Works! Bindings established automatically"
  [task runtime]
  (BoundaryTask. task runtime (spin-core/spin-id task)))

(deftype AmbientBoundaryTask [task task-spin-id]
  clojure.lang.IFn
  (invoke [_ resolve reject]
    (let [caller-runtime (ec/current-execution-context)
          caller-spin-id ec/*spin-id*
          return-to-caller
          (fn [continuation]
            (fn [value]
              (binding [ec/*execution-context* caller-runtime
                        ec/*spin-id* caller-spin-id]
                (continuation value))))]
      ;; Capabilities inherited by a fork belong to the selected world. Unlike
      ;; an explicit cross-world task handle, they must not retain the runtime
      ;; in which the interpreter was originally constructed.
      (binding [ec/*execution-context* caller-runtime
                ec/*spin-id* task-spin-id]
        (task (return-to-caller resolve)
              (return-to-caller reject)))))

  clojure.lang.IDeref
  (deref [_]
    @task))

(defn wrap-capability-for-sci
  "Wrap an inherited native capability so it executes in the caller's world.

  Use this for `:native-spins` installed in a forkable interpreter. Use
  `wrap-spin-for-sci` instead for an explicit handle to a task hosted by a
  particular world."
  [task]
  (AmbientBoundaryTask. task (spin-core/spin-id task)))

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
  (binding [ec/*execution-context* runtime
            ec/*spin-id* spin-id]
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
                                        [k (wrap-capability-for-sci v)])
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
                                 {'spindel.engine
                                  {'get-state (fn [path] (ec/get-state path))
                                   'swap-state! (fn [path f & args] (apply ec/swap-state! path f args))}}))})]

    ;; Load partial-cps for CPS transformation support
    (sci-core/load-partial-cps! sci-ctx)

    sci-ctx))

;; =============================================================================
;; Usage Examples
;; =============================================================================

(comment
  (require '[org.replikativ.spindel.engine.context :as ctx]
           '[org.replikativ.spindel.spin.cps :refer [spin]])

  ;; Setup
  (def rt (ctx/create-execution-context))

  ;; Create native spin
  (binding [ec/*execution-context* rt]
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
  (binding [ec/*execution-context* rt]
    @sci-spin)  ; => 30

  ;; Bidirectional chain: Native → SCI → Native
  (binding [ec/*execution-context* rt]
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

  (binding [ec/*execution-context* rt]
    @chained)  ; => 21 (15 + 6)
  )
