(ns org.replikativ.spindel.blocking
  "Blocking work as a Spin.

  The engine's threads must never block or be interrupted: persistent
  continuations and deferred deliveries resume inline on a context's drain,
  so blocking I/O in a Spin body (after an `await`) stalls every Spin of that
  context. Blocking work belongs on embedder threads that talk back to the
  engine only through enqueue-only APIs (`sync/deliver!`). `blocking` is that
  bridge, once, for every embedder:

    (spin
      (let [rows (await (blocking/blocking #(jdbc/query db sql)))]
        (render rows)))

  `f` runs on a worker thread of its own pool (virtual threads on JVM 21+),
  never on the engine's executor, and at most once per Spin: every execution
  of the Spin's body (a second parent awaiting it, a fork running it) waits
  for the same work, each in its own execution context. Its value resolves
  the Spin, its throw rejects it.

  Cancelling the Spin (`cancel-spin!`, losing a `race`, a `timeout`) releases
  the cancelled waiter; once no waiter is left the worker is interrupted (it
  is not an engine thread, so it may be), and work that has not started yet
  never starts.

  On the JVM `f` sees the dynamic bindings in effect where `blocking` is
  called, without the caller's `*spin-id*`. Every call of `blocking` is fresh
  work: the Spin is a resource (one-shot, gensym id), not a cached
  computation.

  ClojureScript has no threads to block: there `f` runs as a task on the
  event loop with the construction-time `*execution-context*` bound (other
  dynamic bindings are not conveyed), and a returned promise is awaited;
  cancellation cannot interrupt it."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            #?(:clj [org.replikativ.spindel.work :refer [task]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.work :refer [task]]))
  #?(:clj (:import [java.util.concurrent ExecutorService Executors Future ThreadFactory
                    ThreadPoolExecutor ThreadPoolExecutor$CallerRunsPolicy])))

#?(:clj
   (defn- new-pool ^ExecutorService []
     (try
       (let [m (.getMethod Executors "newVirtualThreadPerTaskExecutor" (into-array Class []))]
         (.invoke m nil (into-array Object [])))
       (catch NoSuchMethodException _
         (Executors/newCachedThreadPool
          (reify ThreadFactory
            (newThread [_ r]
              (doto (Thread. ^Runnable r "spindel-blocking")
                (.setDaemon true)))))))))

#?(:clj
   (defonce ^:private default-pool
     ;; Shared by every context: the workers carry no engine state.
     (delay (new-pool))))

#?(:clj
   (defn- check-pool! [pool]
     ;; Submission happens from a Spin body: a pool that runs a rejected task
     ;; on the submitting thread would run `f` on the drain.
     (when (and (instance? ThreadPoolExecutor pool)
                (instance? ThreadPoolExecutor$CallerRunsPolicy
                           (.getRejectedExecutionHandler ^ThreadPoolExecutor pool)))
       (throw (ex-info "blocking: a :pool with CallerRunsPolicy would run f on the engine's drain"
                       {:pool pool})))
     pool))

(defn- submit!
  "Run `thunk` on the worker pool; returns a handle `cancel!` takes."
  [pool thunk]
  #?(:clj (.submit ^ExecutorService (or pool @default-pool) ^Runnable thunk)
     :cljs (do (js/setTimeout thunk 0) nil)))

(defn- cancel! [handle]
  #?(:clj (when handle (.cancel ^Future handle true))
     :cljs nil))

(defn- settle!
  "Record `outcome` once and hand it to every waiter."
  [work outcome]
  (let [[old _] (swap-vals! work (fn [w] (if (:outcome w) w (assoc w :outcome outcome))))]
    (when-not (:outcome old)
      (doseq [{:keys [notify]} (vals (:waiters old))] (notify outcome)))))

(defn- join!
  "Register waiter `id` of context `fork-id` (`notify` takes the outcome) and
  start the work if no one has; an outcome already there is handed over at
  once."
  [work id fork-id notify start!]
  (let [[old new] (swap-vals! work (fn [w]
                                     (cond-> (assoc-in w [:waiters id] {:notify notify :fork-id fork-id})
                                       (not (:started? w)) (assoc :started? true))))]
    (cond
      (:outcome new) (notify (:outcome new))
      (not (:started? old)) (start!))))

(defn- leave!
  "Remove waiter `id`, or, when the Spin is cancelled in its context, every
  waiter of that context (an execution that a later one superseded never
  reaches its own `finally`); with none left and no outcome, stop the work."
  [work id fork-id cancelled?]
  (let [w (swap! work update :waiters
                 (fn [ws] (if cancelled?
                            (into {} (remove (fn [[_ v]] (= fork-id (:fork-id v)))) ws)
                            (dissoc ws id))))]
    (when (and (empty? (:waiters w)) (not (:outcome w)))
      (cancel! (:handle w)))))

(defn blocking
  "A Spin of `(f)` run on a worker thread: its value, or its throw.

  Options:
    :pool  a `java.util.concurrent.ExecutorService` to run on (JVM; default a
           shared virtual-thread-per-task pool). It must not be the engine's
           executor and must hand work to its own threads (a CallerRunsPolicy
           pool is refused).

  `f` runs at most once. Cancelling every waiter interrupts the worker (JVM)
  or keeps queued work from starting."
  ([f] (blocking f nil))
  ([f {:keys [pool]}]
   (let [ctx (ec/current-execution-context)
         pool #?(:clj (some-> pool check-pool!) :cljs nil)
         ;; the bindings of the call, not of wherever the body later runs
         conveyed #?(:clj (bound-fn* (fn [] (binding [ec/*spin-id* nil] (f))))
                     :cljs (fn [] (binding [ec/*execution-context* ctx
                                            ec/*spin-id* nil]
                                    (f))))
         work (atom {:waiters {}})
         sid (keyword (gensym "blocking-"))
         start! (fn []
                  (let [handle (submit! pool
                                        (fn []
                                          (try
                                            (let [v (conveyed)]
                                              #?(:clj (settle! work [:ok v])
                                                 :cljs (if (instance? js/Promise v)
                                                         (.then v
                                                                #(settle! work [:ok %])
                                                                #(settle! work [:error %]))
                                                         (settle! work [:ok v]))))
                                            (catch #?(:clj Throwable :cljs :default) t
                                              (settle! work [:error t])))))]
                    (swap! work assoc :handle handle)
                    ;; every waiter left before the handle was known
                    (when (and (empty? (:waiters @work)) (not (:outcome @work)))
                      (cancel! handle))))]
     (binding [ec/*execution-context* ctx]
       (spin-core/make-spin
        (task
         ;; this execution's own context: a fork running the Spin waits in
         ;; the fork, not where the Spin was built
         (let [here (ec/current-execution-context)
               done (sync/deferred)
               id (gensym "waiter-")]
           (join! work id (:fork-id here)
                  (fn [outcome]
                    (binding [ec/*execution-context* here
                              ec/*spin-id* nil]
                      (sync/deliver! done outcome)))
                  start!)
           (try
             (let [[kind v] (await done)]
               (if (= :ok kind) v (throw v)))
             (finally
               ;; completed: a no-op for the work; cancelled while parked on
               ;; `done`: `cancel-spin!` unwinds this await into its reject
               ;; path, and the last waiter to leave stops the worker
               (leave! work id (:fork-id here)
                       (binding [ec/*execution-context* here]
                         (boolean (ec/spin-is-cancelled? sid))))))))
        sid)))))
