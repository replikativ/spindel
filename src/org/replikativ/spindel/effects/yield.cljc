(ns org.replikativ.spindel.effects.yield
  "yield effect - suspend and emit value in async sequence.

  Only used within gen-aseq context. Not registered globally."
  (:require [org.replikativ.spindel.runtime.core :as rtc]))

;; =============================================================================
;; Public API Shim
;; =============================================================================

(defn yield
  "Suspend execution and emit a value in an async sequence.

  Must only be called inside gen-aseq; outside, this throws."
  [& _]
  (throw (ex-info "yield called outside of gen-aseq context (should be CPS-transformed)" {})))

;; =============================================================================
;; Direct Breakpoint Factory
;; =============================================================================

#?(:clj
   (defn make-yield-breakpoint
     "CPS breakpoint handler for yield.

     Creates a marker map with the yielded value and raw continuation,
     then calls the yield-handler to deliver it to the deferred."
     []
     (fn [_ctx r _e]
       (fn [args]
         ;; Call yield-handler to deliver marker
         `(let [yield-value# ~(first args)
                marker# {::yield-marker true
                         :value yield-value#
                         :continuation-r ~r}]
            (if-let [handler# rtc/*yield-handler*]
              (handler# marker# nil)
              (throw (ex-info "*yield-handler* not bound in yield context" {})))
            ;; Return incomplete - actual result delivered via handler
            org.replikativ.spindel.spin.core/incomplete)))))

;; NOTE: yield is NOT registered globally - sequence/core.cljc adds it manually
;; to the breakpoints map when building gen-aseq.
