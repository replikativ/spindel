(ns org.replikativ.spindel.spin.lifecycle
  "Spin lifecycle management - cancellation, cleanup, status checking"
  (:require [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.spin.protocols :as tp]
            [org.replikativ.spindel.spin.result :as result]
            [org.replikativ.spindel.spin.core :as spin-core]))

;; =============================================================================
;; Spin Status Checking
;; =============================================================================

(defn spin-cancelled?
  "Check if a spin has been cancelled by user.

   Uses PSpin protocol and PSpinLifecycle to check error state.
   Requires *execution-context* to be bound."
  [spin]
  (let [cached (rtc/spin-current-result (tp/spin-id spin))]
    (when (and cached (result/error? cached))
      (result/match cached
        (fn [_] false)
        (fn [e] (= "Spin cancelled by user" (.getMessage ^Throwable e)))))))

(defn spin-failed?
  "Check if a spin has failed (either due to error or cancellation).

   Uses PSpin protocol and PSpinLifecycle to check cached error.
   Requires *execution-context* to be bound.
   This includes both user-initiated cancellation and error propagation."
  [spin]
  (let [cached (rtc/spin-current-result (tp/spin-id spin))]
    (boolean (and cached (result/error? cached)))))

;; =============================================================================
;; Spin Lifecycle Operations
;; =============================================================================

(defn cancel-spin!
  "Cancel a spin and all its observers (cooperative cancellation).

   Spins will check cancellation at await points (cooperative, not preemptive).

   This is useful for:
   - User-initiated cancellation (e.g., cancelling expensive UI operations)
   - Abandoning a computation tree when it's no longer needed
   - Race semantics (first to complete wins, cancel others)

   Parameters:
     spin - The Spin to cancel (not spin-id!)

   Returns:
     nil

   Example:
     (def expensive (spin ctx (do-expensive-computation)))
     ;; User clicks cancel button:
     (cancel-spin! expensive)
     @expensive  ; => throws ex-info \"Spin cancelled\""
  [spin]
  (let [spin-id (tp/spin-id spin)
        error (ex-info "Spin cancelled by user"
                       {:type spin-core/spin-cancelled
                        :spin-id spin-id
                        :cancelled-at #?(:clj (java.util.Date.)
                                         :cljs (js/Date.))})]
    ;; Requires *execution-context* to be bound by caller
    (spin-core/abort-spin-chain! spin-id error)))

(defn cleanup-spin!
  "Manually clean up a spin, removing it from the runtime.

   This is useful when you want explicit cleanup without waiting for GC.
   The spin will be removed from:
   - All signal observer lists
   - All spin observer lists
   - The dependency graph

   After cleanup, the spin should not be dereferenced again.

   Parameters:
     spin - The Spin to clean up (not spin-id!)

   Returns:
     nil

   Example:
     (def temp-spin (spin ctx (await some-signal)))
     @temp-spin  ; => evaluates once
     (cleanup-spin! temp-spin)  ; explicit cleanup
     ;; temp-spin is now removed from runtime

   Note: Automatic cleanup via GC still works - this is for cases where
   you want deterministic cleanup timing."
  [spin]
  (let [spin-id (tp/spin-id spin)]
    ;; Cancel the spin first (stops any running computation)
    (cancel-spin! spin)
    ;; Clean up dependencies and remove from runtime
    (rtc/graph-clear-deps! spin-id)))
