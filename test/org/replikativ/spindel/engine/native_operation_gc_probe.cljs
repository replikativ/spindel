(ns org.replikativ.spindel.engine.native-operation-gc-probe
  "Advanced-build check that escaped terminal capabilities do not retain a world."
  (:require [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer-macros [spin]]
            [org.replikativ.spindel.effects.await :refer [await-finalization]]
            [org.replikativ.spindel.spin.sync :as sync]))

(defn completed-operation []
  (let [rt (context/create-execution-context {:engine :owned :audit? false})
        terminal (atom nil) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred)
            task (spin
                  (await-finalization
                   (fn [succeed fail]
                     (reset! terminal succeed)
                     (d (fn [v] (succeed (inc v))) fail))))]
        (task #(swap! values conj %) #(throw %))
        (d 41)
        (when-not (= [42] @values) (throw (js/Error. "Operation did not complete")))))
    {:world (js/WeakRef. rt) :terminal @terminal}))

(defn -main []
  (when-not (fn? (.-gc js/globalThis))
    (throw (js/Error. "Run this probe with --expose-gc")))
  (let [{:keys [world terminal]} (completed-operation)]
    (letfn [(check! [remaining]
              (js/setTimeout
               (fn []
                 (.gc js/globalThis)
                 (js/setTimeout
                  (fn []
                    (cond
                      (nil? (.deref world))
                      (do (terminal :obsolete)
                          (println "advanced escaped operation terminal releases world: PASS")
                          (js/process.exit 0))
                      (zero? remaining)
                      (do (println "advanced escaped operation terminal retained world: FAIL")
                          (js/process.exit 1))
                      :else (check! (dec remaining)))) 10)) 0))]
      (check! 100))))
