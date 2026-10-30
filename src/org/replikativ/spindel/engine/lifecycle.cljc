(ns org.replikativ.spindel.engine.lifecycle
  "Asynchronous world release completions."
  (:require [org.replikativ.spindel.engine.protocols :as rtp]))

(defn observe!
  "Observe physical release. Return a function that detaches this observer
   without cancelling the released world's cleanup. Success receives nil."
  [completion resolve reject]
  (rtp/observe-world-release! (rtp/release-runtime completion)
                              (rtp/release-receipt completion) resolve reject))

(deftype ReleaseCompletion [runtime receipt]
  rtp/PWorldRelease
  (release-runtime [_] runtime)
  (release-receipt [_] receipt)
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
