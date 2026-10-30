(ns org.replikativ.spindel.engine.native-cell-gc-probe
  "Advanced-optimized heap probe. Deliberately never reads wrapper anchor fields."
  (:require [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.atom :as ratom]))

(defn- unread-alias [rt]
  (binding [ec/*execution-context* rt]
    (let [original (ratom/atom :alive)]
      (ratom/->RuntimeAtom (ratom/atom-id original)))))

(defn -main []
  (when-not (fn? (.-gc js/globalThis))
    (throw (js/Error. "Run this probe with --expose-gc")))
  (let [rt (owned/runtime)
        holder (atom (unread-alias rt))
        id (ratom/atom-id @holder)]
    (letfn [(reap! [remaining]
              (js/setTimeout
               (fn []
                 (.gc js/globalThis)
                 (js/setTimeout
                  (fn []
                    (cond
                      (not (rtp/runtime-cell-present? rt id))
                      (do (println "advanced anchor retention and release: PASS")
                          (js/process.exit 0))
                      (zero? remaining)
                      (do (println "advanced anchor release: FAIL")
                          (js/process.exit 1))
                      :else (reap! (dec remaining)))) 10)) 0))
            (keep! [remaining]
              (js/setTimeout
               (fn []
                 (.gc js/globalThis)
                 (js/setTimeout
                  (fn []
                    (let [actual (binding [ec/*execution-context* rt] @@holder)]
                      (cond
                        (not= :alive actual)
                        (do (println "advanced live wrapper lost its allocation:" actual)
                            (js/process.exit 1))
                        (zero? remaining)
                        (do (reset! holder nil) (reap! 100))
                        :else (keep! (dec remaining))))) 10)) 0))]
      (keep! 20))))
