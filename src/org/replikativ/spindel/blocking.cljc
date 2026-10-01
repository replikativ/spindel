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
  never on the engine's executor. Its value resolves the Spin, its throw
  rejects it. Cancelling the Spin (`cancel-spin!`, losing a `race`, a
  `timeout`) interrupts the worker: it is not an engine thread, so it may be.
  `f` sees the dynamic bindings in effect where `blocking` is called (not
  where the Spin's body later runs), without the caller's `*spin-id*`.

  Every call is fresh work: the Spin is a resource (one-shot, gensym id), not
  a cached computation, so two calls never share a result.

  ClojureScript has no threads to block: there `f` runs as a task on the
  event loop and the Spin resolves with its value (or its returned promise's
  value); cancellation cannot interrupt it."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            #?(:clj [org.replikativ.spindel.work :refer [task]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.work :refer [task]]))
  #?(:clj (:import [java.util.concurrent ExecutorService Executors Future ThreadFactory])))

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

(defn- submit!
  "Run `thunk` on the worker pool; returns a handle `cancel!` takes."
  [pool thunk]
  #?(:clj (.submit ^ExecutorService (or pool @default-pool) ^Runnable thunk)
     :cljs (do (js/setTimeout thunk 0) nil)))

(defn- cancel! [handle]
  #?(:clj (when handle (.cancel ^Future handle true))
     :cljs nil))

(defn blocking
  "A Spin of `(f)` run on a worker thread: its value, or its throw.

  Options:
    :pool  a `java.util.concurrent.ExecutorService` to run on (JVM; default a
           shared virtual-thread-per-task pool). It must not be the engine's
           executor.

  Cancelling the Spin interrupts the worker (JVM). `f` is called at most
  once, when the Spin starts."
  ([f] (blocking f nil))
  ([f {:keys [pool]}]
   (let [ctx (ec/current-execution-context)
         ;; the bindings of the call, not of wherever the body later runs
         conveyed #?(:clj (bound-fn* (fn [] (binding [ec/*spin-id* nil] (f))))
                     :cljs f)]
     (binding [ec/*execution-context* ctx]
       (spin-core/make-spin
        (task
         (let [done (sync/deferred)
               deliver! (fn [outcome]
                          (binding [ec/*execution-context* ctx
                                    ec/*spin-id* nil]
                            (sync/deliver! done outcome)))
               handle (submit! pool
                               (fn []
                                 (try
                                   (let [v (conveyed)]
                                     #?(:clj (deliver! [:ok v])
                                        :cljs (if (instance? js/Promise v)
                                                (.then v
                                                       #(deliver! [:ok %])
                                                       #(deliver! [:error %]))
                                                (deliver! [:ok v]))))
                                   (catch #?(:clj Throwable :cljs :default) t
                                     (deliver! [:error t])))))]
           (try
             (let [[kind v] (await done)]
               (if (= :ok kind) v (throw v)))
             (finally
               ;; Completed: a no-op. Cancelled while parked on `done`:
               ;; `cancel-spin!` unwinds this await into its reject path,
               ;; and the worker is interrupted.
               (cancel! handle)))))
        (keyword (gensym "blocking-")))))))
