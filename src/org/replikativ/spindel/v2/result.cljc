(ns org.replikativ.spindel.v2.result
  "Results as values (the old spin.core Result API, engine-independent).")

(defprotocol PResult
  (ok? [this] "True for a success result.")
  (error? [this] "True for an error result.")
  (unwrap [this] "The value of a success; throws the error of a failure.")
  (match [this ok-fn error-fn] "Calls ok-fn with the value, or error-fn with the error."))

(defrecord Result [variant payload]
  PResult
  (ok? [_] (= variant :ok))
  (error? [_] (= variant :error))
  (unwrap [_] (if (= variant :ok) payload (throw payload)))
  (match [_ ok-fn error-fn] (if (= variant :ok) (ok-fn payload) (error-fn payload))))

(defn ok "A success result." [value] (->Result :ok value))
(defn error "An error result." [err] (->Result :error err))
