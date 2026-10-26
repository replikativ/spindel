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
  {:state (atom {:in-flight 0 :listeners []})})

(defn- tracker-of [ctx] (:quiescence ctx))

(defn in-flight
  "How many tasks of `ctx` are scheduled or running."
  [ctx]
  (if-let [t (tracker-of ctx)] (:in-flight @(:state t)) 0))

(defn quiescent?
  "Whether `ctx` has no task in flight, no queued event and no drain."
  [ctx]
  (let [state (rtp/get-state ctx [])]
    (and (zero? (in-flight ctx))
         (not (:engine/draining? state))
         (empty? (:engine/pending state)))))

(defn check!
  "Call `ctx`'s quiescence listeners if it is quiescent now. Each listener is
  called once. Cheap; called when a task ends and when a drain releases the
  world."
  [ctx]
  (when-let [t (tracker-of ctx)]
    (let [state (:state t)]
      (loop []
        (let [{:keys [in-flight listeners] :as observed} @state]
          (when (and (zero? in-flight) (seq listeners) (quiescent? ctx))
            ;; Task admission and listener registration invalidate this exact
            ;; observation. An older idle check must never claim a newer batch.
            ;; CAS compares identity, so begin/end cannot create an ABA even
            ;; when their resulting counter values happen to equal observed.
            (if (compare-and-set! state observed (assoc observed :listeners []))
              (doseq [listener listeners] (listener))
              (recur)))))))
  nil)

(defn begin!
  "Count one task of `ctx` in flight. Pair with `end!`; prefer `task`."
  [ctx]
  (when-let [t (tracker-of ctx)] (swap! (:state t) update :in-flight inc))
  nil)

(defn end!
  "A task of `ctx` has run (or will not run)."
  [ctx]
  (when-let [t (tracker-of ctx)]
    (when (zero? (:in-flight (swap! (:state t) update :in-flight dec)))
      (check! ctx)))
  nil)

(defn task
  "`f` as a task of `ctx`: counted in flight from now until it has run. The
  count is released once, however often the returned fn is called, or by
  `release!` when the task will not run (its executor refused it)."
  [ctx f]
  (if (tracker-of ctx)
    (let [done? (atom false)
          release (fn [] (when (compare-and-set! done? false true) (end! ctx)))]
      (begin! ctx)
      (with-meta (fn [] (try (f) (finally (release))))
        {::release release}))
    f))

(defn release!
  "Release the count of `task` (from `task`) that will not run: the executor
  it was handed to refused it."
  [task]
  (when-let [release (::release (meta task))] (release))
  nil)

(defn submit!
  "Hand `task` (from `task`) to `submit` (fn [task]), releasing its count if
  that throws. Returns what `submit` returns."
  [submit task]
  (try (submit task)
       (catch #?(:clj Throwable :cljs :default) error
         (release! task)
         (throw error))))

(defn on-quiescent
  "Call `callback` (no arguments) once, when `ctx` is quiescent — now, if it
  already is. Called on the thread that ends the world's last task."
  [ctx callback]
  (if-let [t (tracker-of ctx)]
    (do (swap! (:state t) update :listeners conj callback)
        (check! ctx))
    (callback))
  nil)
