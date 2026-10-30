(ns org.replikativ.spindel.engine.native-timer-gc-probe
  "Advanced-build checks for timer transport, cold handles and revoked captures."
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.timer-transport :as transport]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.combinators :as c]))

(def ^:dynamic *ambient-payload* nil)
(bindings/register-var! #'*ambient-payload*)

(defn ambient-payload-with-pending-timer []
  (let [payload (js-obj)]
    (binding [*ambient-payload* payload]
      {:payload (js/WeakRef. payload)
       :handle (transport/schedule-native-timer! transport/default-transport 60000 (fn []) (fn [_]))})))

(defn controlled []
  (let [dispatch (atom nil) worker (atom nil)]
    {:dispatch dispatch :worker worker
     :transport {:schedule (fn [_ task] (reset! dispatch task) :handle)
                 :submit (fn [task] (reset! worker task)) :cancel (fn [_])}}))

(defn sleep-without-world [started?]
  (let [driver (controlled)
        rt (owned/runtime {:cps-exit? true :audit? false :timer-transport (:transport driver)})
        s (binding [ec/*execution-context* rt] (c/sleep 60000 :done))]
    (when started?
      (binding [ec/*execution-context* rt] (s (fn [_]) (fn [_]))))
    {:world (js/WeakRef. rt) :sleep s :driver driver}))

(defn cancelled-payload-with-stale-platform-wrapper []
  (let [driver (controlled)
        rt (owned/runtime {:cps-exit? true :audit? false :timer-transport (:transport driver)})
        payload (js-obj)]
    (binding [ec/*execution-context* rt]
      (let [s (c/sleep 60000 payload)]
        (s (fn [_]) (fn [_]))
        (rtp/cancel-computation! rt s (spin-core/spin-id s) (spin-core/spin-body s)
                                 (ex-info "cancelled GC fixture" {}))))
    {:runtime rt :driver driver :payload (js/WeakRef. payload)}))

(defn -main []
  (when-not (fn? (.-gc js/globalThis))
    (throw (js/Error. "Run this probe with --expose-gc")))
  (let [ambient (ambient-payload-with-pending-timer)
        cold (sleep-without-world false) pending (sleep-without-world true)
        cancelled (cancelled-payload-with-stale-platform-wrapper)]
    (letfn [(check! [remaining]
              (js/setTimeout
               (fn []
                 (.gc js/globalThis)
                 (js/setTimeout
                  (fn []
                    (owned/snapshot (:runtime cancelled))
                    (cond
                      (and (nil? (.deref (:payload ambient)))
                           (nil? (.deref (:world cold)))
                           (nil? (.deref (:world pending)))
                           (nil? (.deref (:payload cancelled))))
                      (do
                        (when-not (and (some? (:sleep cold)) (some? (:sleep pending)))
                          (throw (js/Error. "Timer handle fixtures were dropped")))
                        (doseq [fixture [pending cancelled]]
                          (when-let [dispatch @(:dispatch (:driver fixture))]
                            (dispatch)
                            (when-let [worker @(:worker (:driver fixture))] (worker))))
                        (transport/cancel-native-timer! transport/default-transport (:handle ambient))
                        (println "advanced timer bindings, world handles and revoked payload release: PASS")
                        (js/process.exit 0))
                      (zero? remaining)
                      (do (println "advanced timer retained ambient payload, world or revoked capture: FAIL")
                          (js/process.exit 1))
                      :else (check! (dec remaining)))) 10)) 0))]
      (check! 100))))
