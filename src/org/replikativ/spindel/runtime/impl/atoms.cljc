(ns org.replikativ.spindel.runtime.impl.atoms
  "Atoms-based runtime implementation (portable CLJ/CLJS).

  DEPRECATED: This namespace now just delegates to ExecutionContext.
  Use org.replikativ.spindel.runtime.context/create-execution-context directly.

  Kept for backwards compatibility with code using:
    (ctx/create-execution-context)"
  (:require [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.scheduler :as scheduler]))

;; Register with runtime creation multimethod
;; Now just delegates to ExecutionContext
(defmethod rtc/create-runtime :atoms [opts]
  (let [executor (or (:scheduler opts) (scheduler/default-executor))]
    (ctx/create-execution-context :executor executor)))
