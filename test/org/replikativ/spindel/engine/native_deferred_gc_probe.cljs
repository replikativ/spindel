(ns org.replikativ.spindel.engine.native-deferred-gc-probe
  "Advanced-optimized Deferred anchor retention/release; never reads its anchor."
  (:require [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.sync :as sync]))

(defn -main []
  (when-not (fn? (.-gc js/globalThis))
    (throw (js/Error. "Run this probe with --expose-gc")))
  (let [rt (owned/runtime)
        holder (atom (sync/create-deferred rt))
        id (:id (rtp/deferred-payload @holder))]
    (letfn [(reap! [remaining]
              (js/setTimeout
               (fn []
                 (.gc js/globalThis)
                 (js/setTimeout
                  (fn []
                    (cond
                      (not (contains? (:entities (owned/snapshot rt)) id))
                      (do (println "advanced Deferred anchor retention and release: PASS") (js/process.exit 0))
                      (zero? remaining)
                      (do (println "advanced Deferred anchor release: FAIL") (js/process.exit 1))
                      :else (reap! (dec remaining)))) 10)) 0))
            (keep! [remaining]
              (js/setTimeout
               (fn []
                 (.gc js/globalThis)
                 (js/setTimeout
                  (fn []
                    (cond
                      (not= {:assigned? false :value nil} (rtp/read-public-deferred rt @holder))
                      (do (println "advanced live Deferred lost its allocation: FAIL") (js/process.exit 1))
                      (zero? remaining) (do (reset! holder nil) (reap! 100))
                      :else (keep! (dec remaining)))) 10)) 0))]
      (keep! 20))))
