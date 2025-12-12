(ns is.simm.spindel.spin.error
  "Error handling operators - attempt, absolve"
  (:require [is.simm.spindel.spin.core :as spin-core]
            [is.simm.spindel.spin.protocols :as tp]))

;; =============================================================================
;; Error Handling Combinators
;; =============================================================================

(defn attempt
  "Wrap spin result in a zero-argument function that returns result or throws error.

   Always succeeds - errors are captured as throwable functions.

   Example:
     (def risky (spin ctx (/ 1 0)))
     (def safe (attempt ctx risky))

     @safe  ; => #(throw ArithmeticException)
     (@safe)  ; => throws ArithmeticException

   Use cases:
   - Optional error handling
   - Composing error-prone operations
   - Error recovery strategies"
  ([spin]
   (spin-core/make-spin
    (fn [runtime-atom _ resolve _]
      ;; Always succeed with a thunk capturing either value or error
      (let [spin-id (tp/spin-id spin)
            on-ok (fn [v] (resolve (fn [] v)))
            on-err (fn [e] (resolve (fn [] (throw e))))]
        (spin runtime-atom spin-id on-ok on-err)
        spin-core/incomplete)))))

(defn absolve
  "Unwrap a spin returning a zero-argument function, calling it and returning result.

   Inverse of attempt - converts wrapped errors back to thrown errors.

   Example:
     (def wrapped (attempt ctx risky-spin))
     (def unwrapped (absolve ctx wrapped))

     @unwrapped  ; => throws if risky-spin threw

   Use cases:
   - Composing with attempt for error handling
   - Conditional error unwrapping"
  ([spin]
   (spin-core/make-spin
    (fn [runtime-atom _ resolve reject]
      (let [spin-id (tp/spin-id spin)
            on-ok (fn [thunk]
                    (try
                      (resolve (thunk))
                      (catch #?(:clj Throwable :cljs :default) e
                        (reject e))))
            on-err (fn [e] (reject e))]
        (spin runtime-atom spin-id on-ok on-err)
        spin-core/incomplete)))))
