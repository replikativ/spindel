(ns is.simm.spindel.spin.result
  "Result type for spin execution outcomes.

  A Result represents the outcome of a spin execution:
  - Success: {:variant :ok, :payload value}
  - Error: {:variant :error, :payload throwable}

  This provides a consistent representation across the codebase,
  replacing the previous mixed formats.")

(defprotocol PResult
  "Protocol for spin execution results."
  (ok? [this]
    "Returns true if this is a success result, false if error.")
  (error? [this]
    "Returns true if this is an error result, false if success.")
  (unwrap [this]
    "Returns the value if success, throws the error if failure.")
  (match [this ok-fn error-fn]
    "Pattern match on result without throwing.
    Calls ok-fn with value if success, error-fn with error if failure."))

(defrecord Result [variant payload]
  PResult
  (ok? [_]
    (= variant :ok))

  (error? [_]
    (= variant :error))

  (unwrap [_]
    (if (= variant :ok)
      payload
      (throw payload)))

  (match [_ ok-fn error-fn]
    (if (= variant :ok)
      (ok-fn payload)
      (error-fn payload))))

(defn ok
  "Create a success result with the given value.
  Value can be nil."
  [value]
  (->Result :ok value))

(defn error
  "Create an error result with the given throwable."
  [err]
  (->Result :error err))
