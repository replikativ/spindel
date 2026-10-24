(ns org.replikativ.spindel.engine.quiescence
  "World quiescence: whether a world has nothing left to do on its own.

  A world's work runs in executor tasks — its drains, savepoint resumes and
  abandons, `parallel`/`race` children, fired timers, work jobs — and in the
  events those enqueue. Every site that schedules such a task for a world
  wraps it in `task`, which counts it in flight until it has run. A world is
  *quiescent* when no task of it is in flight, no event is queued and no
  drain holds it: every change made to it has reached everything it
  affects. A body suspended on something outside the world (a mailbox, a
  timer not yet fired, a deferred) is not in flight.

  The counter belongs to the world, not to its family: a fork has its own,
  so a busy sibling does not hold it up. A context without a tracker (an
  immutable snapshot being restored) counts nothing in flight.

  `on-quiescent` calls back once when the world is quiescent — the moment a
  caller that changed a world in one place can read every consequence (an
  incremental trace update, a test). O(1) per scheduled task."
  (:require [org.replikativ.spindel.engine.protocols :as rtp]))

(defn tracker
  "A fresh tracker, for a new world (`create-execution-context`,
  `fork-context`)."
  []
  {:in-flight (atom 0) :listeners (atom [])})

(defn- tracker-of [ctx] (:quiescence ctx))

(defn in-flight
  "How many tasks of `ctx` are scheduled or running."
  [ctx]
  (if-let [t (tracker-of ctx)] @(:in-flight t) 0))

(defn quiescent?
  "Whether `ctx` has no task in flight, no queued event and no drain."
  [ctx]
  (and (zero? (in-flight ctx))
       (not (rtp/get-state ctx [:engine/draining?]))
       (empty? (rtp/get-state ctx [:engine/pending]))))

(defn check!
  "Call `ctx`'s quiescence listeners if it is quiescent now. Each listener is
  called once. Cheap; called when a task ends and when a drain releases the
  world."
  [ctx]
  (when-let [t (tracker-of ctx)]
    (when (and (seq @(:listeners t)) (quiescent? ctx))
      (let [[listeners _] (swap-vals! (:listeners t) (constantly []))]
        (doseq [listener listeners] (listener)))))
  nil)

(defn begin!
  "Count one task of `ctx` in flight. Pair with `end!`; prefer `task`."
  [ctx]
  (when-let [t (tracker-of ctx)] (swap! (:in-flight t) inc))
  nil)

(defn end!
  "A task of `ctx` has run (or will not run)."
  [ctx]
  (when-let [t (tracker-of ctx)]
    (when (zero? (swap! (:in-flight t) dec))
      (check! ctx)))
  nil)

(defn task
  "`f` as a task of `ctx`: counted in flight from now until it has run. The
  count is released once, however often the returned fn is called."
  [ctx f]
  (if (tracker-of ctx)
    (let [done? (atom false)]
      (begin! ctx)
      (fn []
        (try (f)
             (finally
               (when (compare-and-set! done? false true)
                 (end! ctx))))))
    f))

(defn on-quiescent
  "Call `callback` (no arguments) once, when `ctx` is quiescent — now, if it
  already is. Called on the thread that ends the world's last task."
  [ctx callback]
  (if-let [t (tracker-of ctx)]
    (do (swap! (:listeners t) conj callback)
        (check! ctx))
    (callback))
  nil)
