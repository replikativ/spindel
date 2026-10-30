(ns org.replikativ.spindel.engine.native-execution-scope-gc-probe
  "Advanced-build checks that escaped execution owners carry identity only."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.signal :as signal]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]))

(defn scoped-source [park?]
  (let [rt (context/create-execution-context {:engine :owned})
        scope (lifetime/open-scope! rt :explicit)
        payload (js-obj)]
    (binding [ec/*execution-context* rt]
      (lifetime/with-owner scope
        (signal/signal payload)
        (when park?
          (let [pending (sync/deferred)
                target (spin (lifetime/with-owner scope (await pending) payload))]
            (target (fn [_]) (fn [_]))
            (when-not (some #(and (= :parked (:status %)) (= :scope (first (:owner %))))
                            (vals (:runs (owned/snapshot rt))))
              (throw (js/Error. "GC fixture did not park a scope-owned Run")))))))
    {:context rt :scope scope :payload (js/WeakRef. payload)}))

(defn escaped-capability [release? park?]
  (let [{:keys [context scope payload]} (scoped-source park?)]
    (when release? (context/release-context! context))
    {:scope scope :world (js/WeakRef. context) :payload payload}))

(defn -main []
  (when-not (fn? (.-gc js/globalThis))
    (throw (js/Error. "Run this probe with --expose-gc")))
  (let [kept (scoped-source false)
        open (escaped-capability false false)
        parked (escaped-capability false true)
        released (escaped-capability true false)
        caps [(:scope kept) (:scope open) (:scope parked) (:scope released)]]
    (letfn [(check! [remaining]
              (js/setTimeout
               (fn []
                 (.gc js/globalThis)
                 (js/setTimeout
                  (fn []
                    (cond
                      (and (nil? (.deref (:payload kept)))
                           (nil? (.deref (:payload open)))
                           (nil? (.deref (:world open)))
                           (nil? (.deref (:payload parked)))
                           (nil? (.deref (:world parked)))
                           (nil? (.deref (:payload released)))
                           (nil? (.deref (:world released))))
                      (do
                        (when-not (and (= 4 (count caps)) (every? some? caps)
                                       (= :live (:status (owned/snapshot (:context kept))))
                                       (rtp/execution-owner-joined? (:context kept) (:scope kept)))
                          (throw (js/Error. "Scope collection changed kept capability/world state")))
                        (context/release-context! (:context kept))
                        (println "advanced execution scope identity and payload collection: PASS")
                        (js/process.exit 0))
                      (zero? remaining)
                      (do
                        (println "advanced execution scope retained payload or world: FAIL")
                        (js/process.exit 1))
                      :else (check! (dec remaining)))) 10)) 0))]
      ;; WeakRef deref temporarily keeps its referent until this JS job ends.
      ;; Close here and perform every later GC/check in separate jobs.
      (js/setTimeout
       (fn []
         (.gc js/globalThis)
         (js/setTimeout
          (fn []
            (when-not (some? (.deref (:payload kept)))
              (throw (js/Error. "Open execution scope lost its owned source")))
            (lifetime/close-scope! (:context kept) (:scope kept))
            (check! 100)) 10)) 0))))
