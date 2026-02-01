(ns org.replikativ.spindel.runtime.scheduler
  "Executors for running spin functions.

  Executors provide the execution context (thread pool, event loop, etc.) where
  spin functions run. The runtime uses executors to run spins, but maintains
  control over scheduling strategy (when/what to execute) via PScheduler protocol."
  #?(:cljs (:require [org.replikativ.spindel.runtime.bindings :as bindings]))
  #?(:clj (:import [java.util.concurrent Executors ExecutorService ThreadPoolExecutor
                                         ScheduledExecutorService ScheduledThreadPoolExecutor ThreadFactory
                                         TimeUnit LinkedBlockingQueue Callable])))

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

     ;; Vars that should NOT be propagated to worker threads
     ;; These are test-framework vars that accumulate incorrectly across test runs
     ;; We use find-var to safely handle cases where clojure.test isn't loaded
     (defn- get-excluded-binding-vars
       "Returns set of vars that should be excluded from binding propagation.
       Uses find-var to safely handle cases where clojure.test isn't loaded."
       []
       (into #{}
         (keep identity
           [(find-var 'clojure.test/*testing-vars*)
            (find-var 'clojure.test/*testing-contexts*)
            (find-var 'clojure.test/*test-out*)])))

     (defn- filter-bindings
       "Remove excluded vars from bindings map."
       [bindings]
       (let [excluded (get-excluded-binding-vars)]
         (reduce dissoc bindings excluded)))

     ;; ThreadPool Executor - executes on a thread pool (JVM only)
     (defrecord PoolExecutor [^ExecutorService executor]
       PExecutor
       (execute! [_ spin-fn]
         ;; Capture thread bindings from current thread (includes *execution-context*, *spin-id*, etc.)
         ;; Filter out test-framework bindings that shouldn't be propagated
         (let [bindings (filter-bindings (get-thread-bindings))
               bound-spin-fn (fn []
                               (with-bindings bindings
                                 (spin-fn)))]
           ;; Submit bound-spin-fn and return Future for async result
           (.submit executor ^Callable (reify Callable
                                         (call [_]
                                           (bound-spin-fn))))))

       (execute-after! [this delay-ms spin-fn]
         ;; Use shared ScheduledExecutor to schedule submission to thread pool
         (.schedule ^ScheduledExecutorService @delay-executor
                    ^Runnable (fn [] (execute! this spin-fn))
                    (long delay-ms)
                    TimeUnit/MILLISECONDS))

       java.io.Closeable
       (close [_]
         (.shutdown executor))))

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
   (defn thread-pool-executor
     "Create an executor that runs spins on a fixed thread pool with unbounded queue.

      Use for:
      - Production (JVM)
      - Parallel spin execution
      - Non-blocking reactive updates

      Options:
        :threads - Number of threads (default: available processors)

      Uses an unbounded LinkedBlockingQueue - spins will queue indefinitely
      until executed. OOM is the natural boundary if spins queue faster than
      they can be processed.

      Note: Must call .close to shutdown the thread pool when done."
     [& {:keys [threads]
         :or {threads (.availableProcessors (Runtime/getRuntime))}}]
     (let [;; Create ThreadFactory that makes daemon threads (allows JVM to exit)
           thread-factory (reify java.util.concurrent.ThreadFactory
                            (newThread [_ runnable]
                              (doto (Thread. runnable)
                                (.setDaemon true))))
           executor (java.util.concurrent.ThreadPoolExecutor.
                      threads                          ; core pool size
                      threads                          ; max pool size
                      60000                           ; keep alive time (1 minute)
                      TimeUnit/MILLISECONDS           ; time unit
                      (LinkedBlockingQueue.)          ; work queue
                      thread-factory)]                ; daemon thread factory
       ;; CRITICAL: Prestart all core threads!
       ;; With unbounded queue, threads are NEVER created lazily
       ;; because queue never fills up. Must create them upfront.
       (.prestartAllCoreThreads executor)
       (->PoolExecutor executor))))

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

   JVM: ThreadPoolExecutor with available processor count
   JS:  EventLoopExecutor"
  []
  #?(:clj (thread-pool-executor)
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
