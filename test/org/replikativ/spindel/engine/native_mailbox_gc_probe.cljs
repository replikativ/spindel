(ns org.replikativ.spindel.engine.native-mailbox-gc-probe
  "Advanced-build checks for Mailbox handles and consumed message retention."
  (:require [is.simm.partial-cps.sequence :as aseq]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.sync :as sync]))

(defn handles-without-a-world []
  (let [rt (context/create-execution-context {:engine :owned :audit? false})
        mb (sync/create-mailbox rt)]
    {:world (js/WeakRef. rt) :mailbox mb :next (aseq/anext mb)}))

(defn inbox-with-consumed-payload [rt]
  (binding [ec/*execution-context* rt]
    (let [mb (sync/mailbox) payload (js-obj)]
      (mb payload)
      (mb :tail)
      (when-not (identical? payload (sync/take-now! mb nil))
        (throw (js/Error. "Mailbox did not consume the first message")))
      {:holder (atom (aseq/anext mb)) :payload (js/WeakRef. payload)
       :id (:id (rtp/mailbox-payload mb))})))

(defn -main []
  (when-not (fn? (.-gc js/globalThis))
    (throw (js/Error. "Run this probe with --expose-gc")))
  (let [rt (context/create-execution-context {:engine :owned :audit? false})
        {:keys [holder payload id]} (inbox-with-consumed-payload rt)
        world-handles (handles-without-a-world)]
    (letfn [(fail! [message] (println message) (js/process.exit 1))
            (reap! [remaining]
              (js/setTimeout
               (fn []
                 (.gc js/globalThis)
                 (js/setTimeout
                  (fn []
                    (cond
                      (not (contains? (:entities (owned/snapshot rt)) id))
                      (do (println "advanced Mailbox consumed payload, world and allocation release: PASS")
                          (js/process.exit 0))
                      (zero? remaining) (fail! "advanced unreachable Mailbox retained its buffer: FAIL")
                      :else (reap! (dec remaining)))) 10)) 0))
            (check! [remaining]
              (js/setTimeout
               (fn []
                 (.gc js/globalThis)
                 (js/setTimeout
                  (fn []
                    (when-not (contains? (:entities (owned/snapshot rt)) id)
                      (fail! "advanced MailboxNext lost its allocation: FAIL"))
                    (cond
                      (and (nil? (.deref payload)) (nil? (.deref (:world world-handles))))
                      (do
                        (when-not (identical? (:mailbox world-handles)
                                              (rtp/mailbox-next-target (:next world-handles)))
                          (fail! "advanced next descriptor changed target: FAIL"))
                        (binding [ec/*execution-context* rt]
                          (let [mb (rtp/mailbox-next-target @holder)]
                            (when-not (= :tail (sync/take-now! mb nil))
                              (fail! "advanced Mailbox lost its unconsumed tail: FAIL"))
                            (mb :unreachable-buffer)))
                        (reset! holder nil)
                        (reap! 100))
                      (zero? remaining) (fail! "advanced Mailbox retained consumed payload or world: FAIL")
                      :else (check! (dec remaining)))) 10)) 0))]
      (check! 100))))
