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

  A blocking Spin is a call, not a shared future. When its body runs, `f`
  is submitted to a worker pool of its own (virtual threads on JVM 21+),
  never to the engine's executor; its value resolves the Spin, its throw (or
  a pool that refuses the work) rejects it. Cancelling the Spin
  (`cancel-spin!`, losing a `race`, a `timeout`) interrupts the worker, which
  is not an engine thread and so may be; work still queued never starts.

  Await it from one place. A second execution of the body while the first
  is unfinished (another parent awaiting the same unfinished Spin) is
  rejected instead of running `f` again: to share the result, await it once
  and share the value, or deliver it to a `sync/deferred`. Once the Spin is
  done, awaiting it again reads its cached result. The body runs in whatever
  execution context runs it (a fork included), and delivers there.

  On the JVM `f` sees the dynamic bindings in effect where `blocking` is
  called, without the caller's `*spin-id*`. Every call of `blocking` is fresh
  work: the Spin is a resource (one-shot, gensym id), not a cached
  computation.

  ClojureScript has no threads to block: there `f` runs as a task on the
  event loop with the construction-time `*execution-context*` bound (other
  dynamic bindings are not conveyed), and a returned promise is awaited.
  Cancelling before the task runs keeps it from running; a running `f`
  cannot be interrupted."
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
     :cljs (js/setTimeout thunk 0)))

(defn- cancel! [handle]
  #?(:clj (when handle (.cancel ^Future handle true))
     :cljs (when handle (js/clearTimeout handle))))

(defn blocking
  "A Spin of `(f)` run on a worker thread: its value, or its throw.

  Options:
    :pool  a `java.util.concurrent.ExecutorService` to run on (JVM; default a
           shared virtual-thread-per-task pool). It must not be the engine's
           executor, and `submit` must hand the work to its own threads
           without blocking (a CallerRunsPolicy pool is refused; a pool that
           rejects the work rejects the Spin).

  Cancelling the Spin interrupts the worker (JVM) or keeps queued work from
  starting. Await it from one place (see the namespace doc)."
  ([f] (blocking f nil))
  ([f {:keys [pool]}]
   (let [ctx (ec/current-execution-context)
         pool #?(:clj (some-> pool check-pool!) :cljs nil)
         ;; the bindings of the call, not of wherever the body later runs
         conveyed #?(:clj (bound-fn* (fn [] (binding [ec/*spin-id* nil] (f))))
                     :cljs (fn [] (binding [ec/*execution-context* ctx
                                            ec/*spin-id* nil]
                                    (f))))
         sid (keyword (gensym "blocking-"))
         running (atom false)]
     (binding [ec/*execution-context* ctx]
       (spin-core/make-spin
        (task
         (when-not (compare-and-set! running false true)
           (throw (ex-info "blocking: the Spin is already running; await it from one place and share its value"
                           {:type ::awaited-while-running :spin-id sid})))
         ;; this execution's own context: a fork running the Spin waits and
         ;; is delivered in the fork, not where the Spin was built
         (let [here (ec/current-execution-context)
               done (sync/deferred)
               deliver! (fn [outcome]
                          (binding [ec/*execution-context* here
                                    ec/*spin-id* nil]
                            (sync/deliver! done outcome)))
               settle-with (fn [thunk]
                             (try
                               (let [v (thunk)]
                                 #?(:clj (deliver! [:ok v])
                                    :cljs (if (instance? js/Promise v)
                                            (.then v
                                                   #(deliver! [:ok %])
                                                   #(deliver! [:error %]))
                                            (deliver! [:ok v]))))
                               (catch #?(:clj Throwable :cljs :default) t
                                 (deliver! [:error t]))))
               handle (try
                        (submit! pool #(settle-with conveyed))
                        (catch #?(:clj Throwable :cljs :default) t
                          ;; the pool refused the work (saturated, shut down)
                          (deliver! [:error t])
                          nil))]
           (try
             (let [[kind v] (await done)]
               (if (= :ok kind) v (throw v)))
             (finally
               ;; completed: a no-op; cancelled while parked on `done`:
               ;; `cancel-spin!` unwinds this await into its reject path and
               ;; the worker is interrupted (queued work never starts)
               (cancel! handle)
               (reset! running false)))))
        sid)))))
