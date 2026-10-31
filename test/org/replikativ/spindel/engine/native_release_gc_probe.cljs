(ns org.replikativ.spindel.engine.native-release-gc-probe
  "Advanced-build checks for explicit release ownership and joined arenas."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.atom :as ratom]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]))

(defn joined-fixture []
  (let [rt (context/create-execution-context {:engine :owned}) payload (js-obj)]
    (binding [ec/*execution-context* rt]
      {:context rt :cell (ratom/atom payload)
       :completion (context/release-context! rt) :payload (js/WeakRef. payload)})))

(defn unfinished-fixture []
  (let [rt (context/create-execution-context {:engine :owned}) payload (js-obj) trace (atom [])]
    (binding [ec/*execution-context* rt]
      (let [pending (sync/deferred) ack (sync/deferred)
            target (spin
                    (let [cell (ratom/atom payload)]
                      (try (await pending)
                           (finally
                             (await-finalization ack)
                             (swap! trace conj (identical? payload @cell))))))]
        (target (fn [_]) (fn [_]))
        (let [completion (context/release-context! rt)]
          {:ack ack :trace trace :payload (js/WeakRef. payload)
           :world (js/WeakRef. (rtp/release-runtime completion))
           :completion (js/WeakRef. completion)})))))

(defn acknowledge! [fixture]
  (when-let [rt (.deref (:world fixture))]
    (binding [ec/*execution-context* rt] ((:ack fixture) nil))))

(defn unreachable-sibling-fixture []
  (let [source (owned/runtime {:cps-exit? true})
        source-root (rtp/root-execution-owner source)
        {sibling :context bearer :capability}
        (rtp/fork-owned-world! source {:world-id [:w 1] :owner source-root})
        sibling-root (rtp/root-execution-owner sibling)
        moved (rtp/transfer-owned-world! source bearer source-root sibling sibling-root
                                         {:operation-id :move-sibling})
        payload (js-obj)]
    (owned/signal sibling :payload payload)
    (let [completion (rtp/request-world-release! source :old-world)]
      {:completion completion :bearer moved :owner sibling-root
       :was-live? (= :live (:status (owned/snapshot sibling)))
       :source-joined? (= :joined (get-in (owned/snapshot source) [:release :phase]))
       :payload (js/WeakRef. payload) :world (js/WeakRef. sibling)})))

(defn -main []
  (when-not (fn? (.-gc js/globalThis))
    (throw (js/Error. "Run this probe with --expose-gc")))
  (let [before (owned/pending-release-count)
        joined (joined-fixture) pending (unfinished-fixture)
        sibling (unreachable-sibling-fixture)]
    (letfn [(check! [remaining]
              (js/setTimeout
               (fn []
                 (.gc js/globalThis)
                 (js/setTimeout
                  (fn []
                    (cond
                      (and (nil? (.deref (:payload joined)))
                           (nil? (.deref (:payload pending)))
                           (nil? (.deref (:world pending)))
                           (nil? (.deref (:completion pending)))
                           (nil? (.deref (:payload sibling)))
                           (nil? (.deref (:world sibling))))
                      (let [values (atom []) sibling-values (atom [])]
                        ((:completion joined) #(swap! values conj %) #(throw %))
                        ((:completion sibling) #(swap! sibling-values conj %) #(throw %))
                        (when-not (and (= [nil] @values) (= [true] @(:trace pending))
                                       (= [nil] @sibling-values)
                                       (:was-live? sibling) (:source-joined? sibling)
                                       (some? (:owner sibling)) (some? (:bearer sibling))
                                       (= before (owned/pending-release-count))
                                       (some? (:context joined)) (some? (:cell joined)))
                          (throw (js/Error. "Release completion or kept-alias fixture changed")))
                        (println "advanced explicit release ownership and joined arena collection: PASS")
                        (js/process.exit 0))
                      (zero? remaining)
                      (do (println "advanced release retained application payload or unfinished coordinator: FAIL")
                          (js/process.exit 1))
                      :else (check! (dec remaining)))) 10)) 0))]
      (js/setTimeout
       (fn []
         (.gc js/globalThis)
         (js/setTimeout
          (fn []
            (when-not (and (= (inc before) (owned/pending-release-count))
                           (some? (.deref (:payload pending))) (empty? @(:trace pending)))
              (throw (js/Error. "Explicit release abandoned unfinished cleanup")))
            (when-not (true? (acknowledge! pending))
              (throw (js/Error. "Retained acknowledgement failed")))
            (check! 100)) 10)) 0))))
