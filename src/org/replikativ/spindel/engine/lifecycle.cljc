(ns org.replikativ.spindel.engine.lifecycle
  "Asynchronous world lifecycle completions."
  (:require [org.replikativ.spindel.engine.protocols :as rtp]))

(defn observe!
  "Observe lifecycle completion. Return a function that detaches this observer
   without cancelling the operation's cleanup. Success receives nil."
  [completion resolve reject]
  (rtp/observe-completion! completion resolve reject))

(deftype ReleaseCompletion [runtime receipt]
  rtp/PWorldRelease
  (release-runtime [_] runtime)
  (release-receipt [_] receipt)
  rtp/PCompletion
  (observe-completion! [_ resolve reject]
    (rtp/observe-world-release! runtime receipt resolve reject))
  #?@(:clj [clojure.lang.IFn
            (invoke [this resolve reject] (observe! this resolve reject))]
      :cljs [IFn
             (-invoke [this resolve reject] (observe! this resolve reject))]))

(defn ^:no-doc completion
  "Construct a backend's stable completion using a minimal runtime view.
   The backend must authenticate receipt identity and revoke retained storage
   after physical joining. Do not pass a caller's decorated context here."
  [runtime receipt]
  (ReleaseCompletion. runtime receipt))

(deftype ^:no-doc DiscardCompletion [backend receipt]
  rtp/PCompletion
  (observe-completion! [_ resolve reject]
    (rtp/observe-owned-world-disposal! backend receipt resolve reject))
  #?@(:clj [clojure.lang.IFn
            (invoke [this resolve reject] (observe! this resolve reject))]
      :cljs [IFn
             (-invoke [this resolve reject] (observe! this resolve reject))]))

(defn ^:no-doc discard-completion
  "Construct a stable disposal observation using a minimal revocable backend.
   The backend authenticates the opaque receipt and drops live family/service
   references after terminal disposal and physical target release. Observation
   grants no holder authority; do not pass a decorated caller context here."
  [backend receipt]
  (DiscardCompletion. backend receipt))
