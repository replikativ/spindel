(ns org.replikativ.spindel.v2.pubsub
  "Publish/subscribe over v2 streams (C0, core.async's structure over
   values). A position is already a tap: every reader holding one sees every
   element, and reading consumes nothing. `pub` routes a source into one
   stream per topic, so a subscriber wakes only for its topic; `sub` returns
   a position at that topic's tail. A subscription is that position plus the
   task walking it: cancelling the task unsubscribes."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [aseq await await-any task]])
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.core :refer [aseq task]])))

(defn- tagged [tag src]
  (aseq [p src]
    (when p
      (if-let [[v nx] (await p)] [[tag v] nx] [[tag ::end] nil]))))

(defn pub
  "A router over the source position `src`: it reads each element once,
   evaluates `(topic-fn v)` once and appends `v` to that topic's stream
   (with `{:multi true}`, `topic-fn` returns a collection of topics). Topic
   streams are created on the first `sub` and end when the source ends or
   the router's owner closes. Returns the pub."
  ([src topic-fn] (pub src topic-fn {}))
  ([src topic-fn {:keys [multi]}]
   (let [ctl (v2/stream)
         router (task
                 (loop [sp (tagged :src src) cp (tagged :ctl (v2/position ctl)) topics {}]
                   (if (and (nil? sp) (nil? cp))
                     nil
                     (let [[[tag x] nx] (await-any (filterv some? [sp cp]))]
                       (case tag
                         :ctl (if (= ::end x)
                                (recur sp nil topics)
                                (let [[topic reply] x
                                      s (or (get topics topic)
                                            (let [s (v2/stream)] (when (nil? sp) (v2/close! s)) s))]
                                  (v2/deliver! reply (v2/position s))
                                  (recur sp nx (assoc topics topic s))))
                         :src (if (= ::end x)
                                (do (doseq [s (vals topics)] (v2/close! s))
                                    (recur nil cp topics))
                                (do (doseq [t (if multi (topic-fn x) [(topic-fn x)])]
                                      (when-let [s (get topics t)] (v2/append! s x)))
                                    (recur nx cp topics))))))))]
     {:ctl ctl :router router})))

(defn sub
  "A deferred of a position at the tail of `topic`'s stream in pub `p`:
   the subscriber sees the elements routed after the router handled the
   subscription. In a body: `(await (sub p topic))`."
  [p topic]
  (let [d (v2/deferred)]
    (v2/append! (:ctl p) [topic d])
    d))
