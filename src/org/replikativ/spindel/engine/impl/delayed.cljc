(ns org.replikativ.spindel.engine.impl.delayed
  "Delayed spin scheduling and virtual time management.

  Provides time-based scheduling of spin execution, including:
  - Real time: schedules executor timers
  - Virtual time: advance-virtual-time! for deterministic testing

  All state is stored in the execution context at :engine/delayed-spins,
  :engine/virtual-time, :engine/time-mode, :engine/timer-handles."
  (:require [replikativ.logging :as log]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.executor :as executor]))

(declare process-delayed-spins!)

(defn current-time
  "Get current time (virtual or real) in milliseconds."
  [context]
  (let [time-mode (rtp/get-state context [:engine/time-mode])]
    (if (= time-mode :virtual)
      (rtp/get-state context [:engine/virtual-time])
      #?(:clj (System/currentTimeMillis)
         :cljs (.now js/Date)))))

(defn schedule-delayed-spin!
  "Schedule a spin to run after delay-ms. Returns spin-id for cancellation.

  Spin is stored in forkable event queue. In :real time mode, also schedules
  executor timer to trigger processing at the appropriate time."
  [context delay-ms spin-fn]
  (let [spin-id (keyword (gensym "delayed-spin-"))
        fire-time (+ (current-time context) delay-ms)
        spin-entry {:spin-fn spin-fn :id spin-id}]

    ;; Add to event queue (forkable state) - works for both atoms and STM
    (rtp/swap-state! context [:engine/delayed-spins]
                     (fn [queue]
                       (update queue fire-time (fnil conj []) spin-entry)))

    (log/trace :engine/schedule-delayed {:spin-id spin-id :delay-ms delay-ms :fire-time fire-time})

    spin-id))

(defn schedule-delayed!
  "Schedule a spin function to fire after delay-ms, integrating with both
  virtual-time and real-time modes.

  Two-level scheduling:
  1. Always queue the entry into [:engine/delayed-spins] (forkable state),
     so virtual-time advance can fire it deterministically and so it's
     visible to forks.
  2. In :real time mode, also schedule an executor timer that wakes the
     processor at the appropriate wall-clock time.

  This used to live on the dropped PScheduler protocol. It's a plain
  function now since the engine has only one implementation."
  [context delay-ms spin-fn]
  (let [spin-id (schedule-delayed-spin! context delay-ms spin-fn)
        time-mode (rtp/get-state context [:engine/time-mode])
        executor  (:executor context)]
    (when (and (= time-mode :real) executor)
      (executor/execute-after! executor delay-ms
                               (executor/alive-fn context
                                 #(process-delayed-spins! context executor))))
    spin-id))

(defn process-delayed-spins!
  "Process all delayed spins whose time has come. Returns number of spins executed.

  TRANSACTIONAL: Atomically extracts all ready spins from queue, then executes them
  outside the transaction to avoid holding the lock during execution."
  [context executor]
  (let [now (current-time context)
        ;; Atomically extract all ready spins and clean up queue + handles
        ready-spins (atom nil)
        _ (rtp/swap-state! context []
            (fn [state]
              (let [queue (get state :engine/delayed-spins (sorted-map))
                    ;; Find all entries with fire-time <= now
                    ready (take-while (fn [[fire-time _]] (<= fire-time now)) queue)
                    spins (vec (mapcat val ready))
                    ready-ids (set (map :id spins))
                    ;; Remove ready entries from queue
                    remaining (into (sorted-map)
                                    (drop (count ready) queue))
                    ;; Clean up timer handles for ready spins
                    new-handles (apply dissoc
                                       (get state :engine/timer-handles {})
                                       ready-ids)]
                ;; Store spins for execution outside swap
                (reset! ready-spins spins)
                ;; Return new state
                (-> state
                    (assoc :engine/delayed-spins remaining)
                    (assoc :engine/timer-handles new-handles)))))]

    ;; Execute spins outside the transaction
    (doseq [{:keys [spin-fn id fire-time]} @ready-spins]
      (log/trace :engine/execute-delayed {:spin-id id :fire-time fire-time :now now})
      (when executor
        (executor/execute! executor
          (executor/alive-fn context
            #(binding [ec/*execution-context* context]
               (spin-fn))))))

    (count @ready-spins)))

(defn cancel-delayed-spin!
  "Cancel a scheduled delayed spin by id. Returns true if cancelled, false if not found."
  [context spin-id]
  (let [cancelled? (atom false)]

    ;; Remove from event queue
    (rtp/swap-state! context [:engine/delayed-spins]
                     (fn [queue]
                       (into (sorted-map)
                             (for [[fire-time spins] queue
                                   :let [filtered (vec (remove #(= (:id %) spin-id) spins))]]
                               (do
                                 (when (not= (count filtered) (count spins))
                                   (reset! cancelled? true))
                                 [fire-time filtered])))))

    ;; Clean up timer handle
    (rtp/swap-state-args! context [:engine/timer-handles] dissoc [spin-id])

    (log/trace :engine/cancel-delayed {:spin-id spin-id :cancelled? @cancelled?})

    @cancelled?))

(defn advance-virtual-time!
  "Advance virtual time to target-time-ms, processing all spins along the way.
  Only works in :virtual time mode. Returns number of spins executed."
  [context target-time-ms]
  (let [time-mode (rtp/get-state context [:engine/time-mode])]
    (when (not= time-mode :virtual)
      (throw (ex-info "advance-virtual-time! only works in :virtual time mode"
                      {:current-mode time-mode})))

    (rtp/swap-state! context [:engine/virtual-time] (constantly target-time-ms))

    ;; Process all spins up to target time
    (process-delayed-spins! context nil)))

(defn set-time-mode!
  "Set time mode to :real or :virtual. Returns previous mode."
  [context mode]
  (when-not (#{:real :virtual} mode)
    (throw (ex-info "Time mode must be :real or :virtual" {:mode mode})))

  (let [prev-mode (rtp/get-state context [:engine/time-mode])]
    (rtp/swap-state! context [:engine/time-mode] (constantly mode))
    (log/trace :engine/set-time-mode {:prev-mode prev-mode :new-mode mode})
    prev-mode))
