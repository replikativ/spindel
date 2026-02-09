(ns org.replikativ.spindel.runtime.scheduler
  "Executors for running spin functions.

  Executors provide the execution context (thread pool, event loop, etc.) where
  spin functions run. The runtime uses executors to run spins, but maintains
  control over scheduling strategy (when/what to execute) via PScheduler protocol."
  (:require [org.replikativ.spindel.runtime.bindings :as bindings])
  #?(:clj (:import [java.util.concurrent Executors ExecutorService ThreadPoolExecutor
                                         ScheduledExecutorService ScheduledThreadPoolExecutor ThreadFactory
                                         TimeUnit LinkedBlockingQueue Callable ForkJoinPool])))

(defprotocol PExecutor
  "Protocol for executing spin functions in different contexts.

  This is the low-level execution abstraction - where code runs (thread pool,
  event loop, etc.). The runtime controls when/what to execute via PScheduler."

  (execute! [this spin-fn]
    "Execute a spin function asynchronously in this executor's context.

     Returns a Future (JVM) or Promise-like object (JS) that will contain the result.
     spin-fn is a zero-arg function to execute.

     For ThreadPoolExecutor: returns java.util.concurrent.Future.
     For EventLoopExecutor: returns a promise-like object.")

  (execute-after! [this delay-ms spin-fn]
    "Execute a spin function after delay-ms milliseconds.

     Each executor implements delayed execution in its own way:
     - ThreadPoolExecutor: uses ScheduledExecutorService
     - EventLoopExecutor: uses setTimeout

     Returns implementation-specific handle (or nil)."))

;; =============================================================================
;; Executor Implementations
;; =============================================================================

;; ImmediateExecutor removed - all execution now happens asynchronously via ThreadPoolExecutor
;; This ensures event processing never blocks the calling thread, preventing deadlocks

#?(:clj
   (do
     ;; Shared delayed executor for all ThreadPoolExecutor instances
     (defonce ^:private ^ScheduledExecutorService delay-executor
       (delay
         (let [^ThreadFactory tf (proxy [ThreadFactory] []
                                   (newThread [^Runnable r]
                                     (doto (Thread. r "laufzeit-delay")
                                       (.setDaemon true))))]
           ;; Single-threaded scheduled executor with daemon thread
           (ScheduledThreadPoolExecutor. 1 tf))))

     ;; Targeted binding capture: only the 4 bindings vars + *execution-context*
     ;; This replaces blanket get-thread-bindings (~30+ vars) with exactly
     ;; the 5 vars that matter. *execution-context* is resolved at runtime
     ;; to avoid circular dependency with runtime.core.
     (defn- capture-targeted-bindings
       "Capture only the dynamic vars that matter for worker threads.
       Returns a bindings map suitable for with-bindings."
       []
       (let [;; bindings/capture-bindings captures the 4 vars from bindings.cljc
             base (bindings/capture-bindings)
             ;; Also capture *execution-context* (resolved to avoid circular dep)
             exec-ctx-var (resolve 'org.replikativ.spindel.runtime.core/*execution-context*)]
         (if (and exec-ctx-var (.isBound ^clojure.lang.Var exec-ctx-var))
           (assoc base exec-ctx-var (.get ^clojure.lang.Var exec-ctx-var))
           base)))

     ;; ThreadPool Executor - executes on a thread pool (JVM only)
     ;; Kept for backward compatibility; prefer ForkJoinPoolExecutor for new code.
     (defrecord PoolExecutor [^ExecutorService executor]
       PExecutor
       (execute! [_ spin-fn]
         (let [bindings (capture-targeted-bindings)
               bound-spin-fn (fn []
                               (with-bindings bindings
                                 (spin-fn)))]
           (.submit executor ^Callable (reify Callable
                                         (call [_]
                                           (bound-spin-fn))))))

       (execute-after! [this delay-ms spin-fn]
         (.schedule ^ScheduledExecutorService @delay-executor
                    ^Runnable (fn [] (execute! this spin-fn))
                    (long delay-ms)
                    TimeUnit/MILLISECONDS))

       java.io.Closeable
       (close [_]
         (.shutdown executor)))

     ;; ForkJoinPool Executor - work-stealing pool with managed blocking (JVM only)
     ;; ForkJoinPool creates compensating threads when workers block (via managedBlock),
     ;; which prevents thread pool deadlock when drain threads wait on CountDownLatch.
     (defrecord ForkJoinPoolExecutor [^ForkJoinPool pool]
       PExecutor
       (execute! [_ spin-fn]
         (let [bindings (capture-targeted-bindings)
               bound-spin-fn (fn []
                               (with-bindings bindings
                                 (spin-fn)))]
           (.submit pool ^Callable (reify Callable
                                     (call [_]
                                       (bound-spin-fn))))))

       (execute-after! [this delay-ms spin-fn]
         (.schedule ^ScheduledExecutorService @delay-executor
                    ^Runnable (fn [] (execute! this spin-fn))
                    (long delay-ms)
                    TimeUnit/MILLISECONDS))

       java.io.Closeable
       (close [_]
         (.shutdown pool))))

   :cljs
   ;; EventLoop Executor - executes via setTimeout (JS only)
   (defrecord EventLoopExecutor []
     PExecutor
     (execute! [_ spin-fn]
       ;; Capture current dynamic bindings before scheduling
       (let [captured-bindings (bindings/capture-bindings)
             bound-spin-fn #(bindings/restore-bindings captured-bindings spin-fn)]
         ;; Schedule on next tick and return nil (TODO: return promise)
         (js/setTimeout bound-spin-fn 0)
         nil))

     (execute-after! [_ delay-ms spin-fn]
       ;; Capture current dynamic bindings before scheduling
       (let [captured-bindings (bindings/capture-bindings)
             bound-spin-fn #(bindings/restore-bindings captured-bindings spin-fn)]
         ;; Use setTimeout for delayed execution
         (js/setTimeout bound-spin-fn delay-ms)
         nil))))

#?(:clj
   (do
     (defn thread-pool-executor
       "Create an executor that runs spins on a fixed thread pool with unbounded queue.

        Kept for backward compatibility. Prefer fork-join-executor for new code.

        Options:
          :threads - Number of threads (default: available processors)

        Note: Must call .close to shutdown the thread pool when done."
       [& {:keys [threads]
           :or {threads (.availableProcessors (Runtime/getRuntime))}}]
       (let [thread-factory (reify java.util.concurrent.ThreadFactory
                              (newThread [_ runnable]
                                (doto (Thread. runnable)
                                  (.setDaemon true))))
             executor (java.util.concurrent.ThreadPoolExecutor.
                        threads
                        threads
                        60000
                        TimeUnit/MILLISECONDS
                        (LinkedBlockingQueue.)
                        thread-factory)]
         (.prestartAllCoreThreads executor)
         (->PoolExecutor executor)))

     (defn fork-join-executor
       "Create a ForkJoinPool-based executor with work stealing and managed blocking.

        ForkJoinPool creates compensating threads when workers block (via managedBlock),
        which prevents the thread pool deadlock that occurs with fixed ThreadPoolExecutor
        when drain threads block on CountDownLatch waiting for workers.

        Options:
          :parallelism - Number of worker threads (default: available processors)

        asyncMode=true configures FIFO scheduling (best for event-driven workloads).

        Note: Must call .close to shutdown the pool when done."
       [& {:keys [parallelism]
           :or {parallelism (.availableProcessors (Runtime/getRuntime))}}]
       (let [pool (ForkJoinPool.
                    (int parallelism)
                    ForkJoinPool/defaultForkJoinWorkerThreadFactory
                    nil    ; UncaughtExceptionHandler
                    true)] ; asyncMode = true (FIFO for event-driven workloads)
         (->ForkJoinPoolExecutor pool)))

     (defn virtual-threads-available?
       "Check if virtual threads are available (JVM 21+).
        Uses reflection to avoid compile-time dependency on Java 21+ APIs."
       []
       (try
         (.getMethod Executors "newVirtualThreadPerTaskExecutor" (into-array Class []))
         true
         (catch NoSuchMethodException _ false)))

     (defn virtual-thread-executor
       "Create an executor that runs each task on a new virtual thread (JVM 21+).

        Virtual threads eliminate pool exhaustion entirely: blocking yields the
        carrier thread, enabling unlimited concurrency without deadlock.

        ForkJoinPool.managedBlock calls from other parts of the runtime are harmless
        on virtual threads (they just block the virtual thread, which is free).

        Uses reflection for backward compatibility with JVM < 21.

        Note: Must call .close to shutdown the executor when done."
       []
       (let [method (.getMethod Executors "newVirtualThreadPerTaskExecutor" (into-array Class []))
             ^ExecutorService executor (.invoke method nil (into-array Object []))]
         (->PoolExecutor executor)))))

#?(:cljs
   (do
     (defn event-loop-executor
       "Create an executor that runs spins on the JavaScript event loop.

        Use for:
        - Production (ClojureScript)
        - Browser/Node.js environments
        - Non-blocking reactive updates"
       []
       (->EventLoopExecutor))))

(defn default-executor
  "Create the default executor for the current platform.

   JVM: Virtual threads (JVM 21+), falling back to ForkJoinPool
   JS:  EventLoopExecutor"
  []
  #?(:clj (if (virtual-threads-available?)
            (virtual-thread-executor)
            (fork-join-executor))
     :cljs (event-loop-executor)))

;; =============================================================================
;; Synchronous Executor (Deterministic Simulation)
;; =============================================================================

#?(:clj
   (defrecord SynchronousExecutor []
     PExecutor
     (execute! [_ spin-fn]
       ;; Execute immediately on calling thread for determinism
       ;; Returns a completed "future" for API compatibility
       (let [result (volatile! nil)
             exception (volatile! nil)]
         (try
           (vreset! result (spin-fn))
           (catch Throwable e
             (vreset! exception e)))
         ;; Return mock future for API compatibility
         (reify java.util.concurrent.Future
           (get [_]
             (if @exception
               (throw @exception)
               @result))
           (get [_ _timeout _unit]
             (if @exception
               (throw @exception)
               @result))
           (isDone [_] true)
           (isCancelled [_] false)
           (cancel [_ _] false))))

     (execute-after! [this delay-ms spin-fn]
       ;; For simulation: just execute immediately on calling thread
       ;; Time control happens via advance-time!, not actual delays
       ;; This ensures deterministic execution order
       (execute! this spin-fn)))

   :cljs
   (defrecord SynchronousExecutor []
     PExecutor
     (execute! [_ spin-fn]
       ;; Execute immediately for determinism
       (spin-fn)
       nil)

     (execute-after! [this delay-ms spin-fn]
       ;; Execute immediately - time is virtual
       (execute! this spin-fn))))

(defn synchronous-executor
  "Create synchronous executor for deterministic simulation testing.

  Use when:
  - You want execution order to be deterministic
  - You're testing concurrent behavior via forking (not threading)
  - You want each operation to complete before next starts

  Note: execute-after! executes immediately. Time control is via
  advance-time!, not actual delays.

  This is the recommended executor for simulation contexts:

  Example:
    (def ctx (create-simulation-context
               :executor (synchronous-executor)))

    ;; All spins execute synchronously on calling thread
    ;; Time is controlled explicitly via advance-time!"
  []
  (->SynchronousExecutor))
