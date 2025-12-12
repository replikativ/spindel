(ns is.simm.spindel.spin.continuation
  "Continuation invocation helpers for CPS-transformed code.

  Provides a unified way to call resolve/reject callbacks that properly
  handles Thunk returns from loop/recur and other CPS constructs."
  (:require [is.simm.partial-cps.async :as pcps-async]))

(defn resume
  "Resume a CPS continuation (resolve or reject callback) with a value.

  This is the universal wrapper for calling any continuation in the system.
  It ensures that if the continuation returns a Thunk (as happens in loop/recur),
  that Thunk is properly trampolined to prevent stack overflow.

  Usage:
    (resume resolve value)
    (resume reject error)

  ALWAYS use this function instead of calling continuations directly.
  Direct calls will fail in loop/recur contexts.

  Examples:
    ;; ✅ CORRECT
    (resume resolve 42)
    (resume reject (ex-info \"error\" {}))

    ;; ❌ WRONG - will hang in loop/recur
    (resolve 42)
    (reject error)"
  [cont-fn value]
  (pcps-async/invoke-continuation cont-fn value))
