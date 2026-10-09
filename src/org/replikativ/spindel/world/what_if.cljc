(ns org.replikativ.spindel.world.what-if
  "Live what-ifs: a world as it would be if some signals held other values,
  kept current as its parent moves.

  A what-if is the value (parent, overrides). Its VIEW is a frozen fork of the
  parent as it is now, with the overrides written into it, so what its spins
  see is always one moment of the parent under the overrides — never a mix of
  moments, which a following fork can show (see docs/forking.md). When a
  signal that a watched computation read changes in the parent, the view is
  stale: the next one is derived from the parent at that later moment and the
  watched computations run again in it. A signal the what-if overrides is not
  followed: its change in the parent does not reach the view.

    view(what-if, t) = view(parent, t) ⊕ overrides

  A what-if owns no history and is never settled. To keep one, `freeze` it: a
  frozen copy of the current view, a world like any other fork."
  (:require [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.spin.core :as spin-core]
            [is.simm.partial-cps.async :as pcps-async]
            [replikativ.logging :as log]))

(defrecord WhatIf [id parent overrides state])

(defn what-if
  "A live what-if of `parent` (an execution context) under `overrides`,
  {signal value}. Nothing runs until something is watched or viewed; `stop!`
  it when done."
  [parent overrides]
  (->WhatIf (gensym "what-if-") parent overrides
            (atom {:generation 0 :view nil :watches {} :listening #{}
                   :scheduled? false :stopped? false})))

(defn- override!
  "Write `value` into `signal` in the fresh `view` as if it had always held it:
  the node changes silently and whatever observes it is marked dirty, so it
  recomputes on its next read. No change event, so nothing that runs in the
  view later sees the override arrive."
  [view signal value]
  (let [id (:id signal)]
    (if-let [node (rtp/get-state view [:nodes id])]
      (do (rtp/swap-state! view [:nodes id]
                           (constantly (nodes/->signal-node (d/clear-deltas value)
                                                            (nodes/get-value node)
                                                            (d/get-deltas value)
                                                            (:deltaable? node)
                                                            (nodes/get-observers node)
                                                            (inc (or (:generation node) 0)))))
          (doseq [observer (nodes/get-observers node)]
            (simple/mark-dirty! view observer)))
      ;; never read in the parent: nothing observes it yet
      (binding [ec/*execution-context* view]
        (reset! signal value)))))

(defn- derive-view
  "A frozen fork of `parent` now, with `overrides` written into it."
  [parent overrides]
  (let [view (ctx/fork-context parent :mode :frozen)]
    (doseq [[signal value] overrides]
      (override! view signal value))
    view))

(defn view
  "The current view of `w`: the world its computations run in. Derived from
  the parent as it is now when there is none yet or it went stale."
  [w]
  (or (:view @(:state w))
      (let [v (derive-view (:parent w) (:overrides w))]
        (:view (swap! (:state w) #(if (:view %) % (assoc % :view v)))))))

(defn freeze
  "A frozen copy of the current view of `w`: the what-if at this moment, as a
  world of its own that does not follow the parent."
  [w]
  (ctx/fork-context (view w) :mode :frozen))

(defn- read-set
  "Ids of the signals the spin `spin-id` read in `world`, through the spins it
  awaited."
  [world spin-id]
  (loop [todo [spin-id] seen #{} signals #{}]
    (if-let [id (peek todo)]
      (if (contains? seen id)
        (recur (pop todo) seen signals)
        (let [{deps :deps} (rtp/get-state world [:nodes id])]
          (recur (into (pop todo) (:spins deps))
                 (conj seen id)
                 (into signals (:signals deps)))))
      signals)))

(declare stale!)

(defn- listen!
  "Follow in the parent exactly the signals the watches read, less the
  overridden ones."
  [w]
  (let [{:keys [parent overrides state id]} w
        overridden (into #{} (map :id) (keys overrides))
        wanted (fn [s]
                 (if (:stopped? s)
                   #{}
                   (apply disj (reduce into #{} (map :reads (vals (:watches s)))) overridden)))
        [before after] (swap-vals! state #(assoc % :listening (wanted %)))
        old (:listening before)
        new (:listening after)
        key [::what-if id]]
    (doseq [sid (remove new old)]
      (rtp/swap-state! parent [:listeners sid] #(dissoc % key)))
    (doseq [sid (remove old new)]
      (rtp/swap-state! parent [:listeners sid]
                       #(assoc % key (fn [_ _ old-value new-value]
                                       (when-not (identical? old-value new-value)
                                         (stale! w))))))))

(defn- run-watch!
  "Run the watch `watch-id` in the view of `generation`; report its value
  once, unless a newer view has been derived meanwhile, then follow what it
  read."
  [w watch-id generation world]
  (when-let [{:keys [make on-value on-error]} (get-in @(:state w) [:watches watch-id])]
    (let [reported? (atom false)
          current? #(and (= generation (:generation @(:state w)))
                         (not (:stopped? @(:state w))))
          finish (fn [s report value]
                   (when (and (current?) (compare-and-set! reported? false true))
                     (swap! (:state w) assoc-in [:watches watch-id :reads]
                            (read-set world (spin-core/spin-id s)))
                     (listen! w)
                     ;; a plain callback: its CPS code runs as a trampoline
                     ;; of its own
                     (binding [pcps-async/*in-trampoline* false]
                       (report value))))]
      ;; Nothing returns what the watched spin hands back: a trampoline of
      ;; its own, as for spawn!.
      (binding [ec/*execution-context* world
                pcps-async/*in-trampoline* false]
        (let [s (make)]
          (s (fn [value] (finish s on-value value))
             (fn [error] (finish s on-error error))))))))

(defn- rederive!
  "Derive a new view and run every watch in it."
  [w]
  (let [s (swap! (:state w) #(-> % (update :generation inc)
                                 (assoc :view nil :scheduled? false)))
        generation (:generation s)
        watches (keys (:watches s))]
    (when-not (:stopped? @(:state w))
      (let [world (view w)]
        (doseq [watch-id watches]
          (run-watch! w watch-id generation world))))))

(defn- stale!
  "The parent moved under a signal a watch read: derive a new view once the
  parent has settled — its drain has invalidated whatever the change reaches —
  so the view is one moment of it, not a signal ahead of what derives from it."
  [w]
  (let [[old _] (swap-vals! (:state w) #(if (or (:scheduled? %) (:stopped? %))
                                          %
                                          (assoc % :scheduled? true)))]
    (when-not (or (:scheduled? old) (:stopped? old))
      (let [parent (:parent w)
            exec (:executor parent)]
        (letfn [(attempt []
                  (try
                    (if (simple/events-settled? parent)
                      (rederive! w)
                      (executor/execute-after! exec 1 attempt))
                    (catch #?(:clj Throwable :cljs :default) e
                      (log/error :what-if/rederive-failed {:error e}))))]
          (executor/execute! exec attempt))))))

(defn watch!
  "Run `(make)` — a fn returning a spin — in the view of `w` and call
  `on-value` with its value, again whenever the parent changes a signal it
  read (and `on-error` with a failure). Returns a fn that stops this watch."
  ([w make on-value] (watch! w make on-value (fn [e] (log/error :what-if/watch-failed {:error e}))))
  ([w make on-value on-error]
   (let [watch-id (gensym "watch-")
         generation (:generation (swap! (:state w) assoc-in [:watches watch-id]
                                        {:make make :on-value on-value :on-error on-error :reads #{}}))]
     (run-watch! w watch-id generation (view w))
     (fn []
       (swap! (:state w) update :watches dissoc watch-id)
       (listen! w)))))

(defn stop!
  "Stop following the parent: no watch runs again."
  [w]
  (swap! (:state w) assoc :stopped? true :watches {})
  (listen! w)
  nil)
