(ns org.replikativ.spindel.engine.executor
  "Executors for running spin functions.

  Execution mechanism — *where* code runs (thread pool, event loop, immediate).
  This layer is polymorphic because the platform demands it: JVM has multiple
  options (virtual threads, ForkJoinPool, custom thread pools), CLJS has the
  event loop, tests want a synchronous executor.

  Scheduling policy — *when* and *in what order* to run things (topological
  observer notification, batch coordination, drain ordering) — lives in the
  engine implementation (`engine.impl.simple`), not in this namespace."
  (:require [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.fault :as fault])
  #?(:clj (:import [java.util.concurrent Executors ExecutorService ThreadPoolExecutor
                    ScheduledExecutorService ScheduledThreadPoolExecutor ThreadFactory
                    TimeUnit LinkedBlockingQueue Callable ForkJoinPool])))

(defn alive-fn
  "Wrap `spin-fn` so it no-ops if `ctx` has been stopped (its :running
  atom is false) by the time the wrapped fn fires.

  Use at every async-schedule site that takes a context — the wrapper
  drops stale callbacks queued before stop-context! ran, which matters
  on JS where setTimeout callbacks can't be cancelled by reference and
  would otherwise restore stale dynamic bindings (especially *spin-id*)
  into the next reactive tick or the next test.

  Forks share the parent's :running atom, so stopping a root drops
  every fork's pending work for free. Contexts without a :running atom
  (e.g. an immutable snapshot mid-restore) are treated as alive.

  On the JVM this is a passthrough: PoolExecutor / ForkJoinPoolExecutor
  capture and restore the dynamic bindings explicitly via with-bindings,
  so stale callbacks cannot pollute *spin-id* in a fresh test. The leak
  is JS-specific (setTimeout callbacks resume against whatever the
  global binding box happens to hold at fire time)."
  [ctx spin-fn]
  #?(:clj spin-fn
     :cljs (let [running (:running ctx)]
             (if running
               (fn [] (when @running (spin-fn)))
               spin-fn))))

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
     - ThreadPoolExecutor / ForkJoinPoolExecutor: uses ScheduledExecutorService
     - EventLoopExecutor: uses setTimeout
     - SynchronousExecutor: runs immediately (virtual-time / simulation)

     Returns an implementation-specific TIMER HANDLE that
     `cancel-timer-handle!` can later cancel:
     - JVM pool executors: a `ScheduledFuture`
     - EventLoopExecutor: the `setTimeout` numeric id
     - SynchronousExecutor: nil — the work already ran, nothing to cancel.

     Callers that want disposal (`schedule-delayed!`) must retain this
     handle; a discarded handle leaks a pending timer."))

(defn cancel-timer-handle!
  "Cancel a timer handle returned by `execute-after!`, releasing the
  underlying executor resource so a completed / cancelled delayed spin
  does not leave a pending timer behind.

  Tolerates nil (SynchronousExecutor returns nil; an already-fired
  timer's handle is also harmless to cancel) and is idempotent.

  - JVM: `ScheduledFuture.cancel(false)` — does not interrupt a timer
    already running its task.
  - JS: `clearTimeout` on the numeric setTimeout id."
  [handle]
  (when handle
    #?(:clj  (when (instance? java.util.concurrent.Future handle)
               (.cancel ^java.util.concurrent.Future handle false))
       :cljs (js/clearTimeout handle)))
  nil)

(defn ^:no-doc guard-task
  "Wrap an executor task so an exception escaping it is REPORTED instead
  of vanishing. On the JVM, `execute!` returns a `.submit` Future that
  no caller derefs — an escaped throw is captured in the discarded
  Future and lost without a trace. On JS, a throw escaping a setTimeout
  callback surfaces as an uncaught error, but bypasses the engine's
  fault hook. Either way, the task seam is the last place the engine
  can observe the failure, so it is guarded here — this covers EVERY
  executor-run path (drain sessions, parallel observer dispatch,
  parallel/race children, delayed-spin resumes, semaphore wakes).

  InterruptedException additionally restores the thread's interrupt
  flag: the engine treats engine-owned threads as non-interruptible
  (see engine.md §Threading contract), so an interrupt that lands here
  is an embedder contract violation worth reporting — but the flag must
  survive for pool machinery that inspects it.

  The throw is NOT re-raised: there is no upstream observer to raise it
  to (that is the point), and re-raising on a pool thread would only
  feed the pool's uncaught-exception machinery inconsistently across
  executors."
  [task-fn]
  (fn []
    (try
      (task-fn)
      #?@(:clj [(catch InterruptedException ie
                  (.interrupt (Thread/currentThread))
                  (fault/report-fault! ::fault/executor-task-fault {:error ie :interrupted? true}))])
      (catch #?(:clj Throwable :cljs :default) e
        (fault/report-fault! ::fault/executor-task-fault {:error e})))))

;; =============================================================================
;; Executor Implementations
;; =============================================================================

;; An embedder thread never runs engine work: what it triggers goes to the
;; executor. Engine work triggered on a thread already running the executor's
;; work stays there (see Inline dispatch below).

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
     (def ^:private execution-context-var (volatile! nil))

     (defn- capture-targeted-bindings
       "Capture only the dynamic vars that matter for worker threads.
       Returns a bindings map suitable for with-bindings."
       []
       (let [;; bindings/capture-bindings captures the 4 vars from bindings.cljc
             base (bindings/capture-bindings)
             ;; Also capture *execution-context* (resolved to avoid circular dep)
             exec-ctx-var (or @execution-context-var
                              (vreset! execution-context-var
                                       (resolve 'org.replikativ.spindel.engine.core/*execution-context*)))]
         (if (and exec-ctx-var (.isBound ^clojure.lang.Var exec-ctx-var))
           (assoc base exec-ctx-var (.get ^clojure.lang.Var exec-ctx-var))
           base)))

     ;; ThreadPool Executor - executes on a thread pool (JVM only)
     ;; Kept for backward compatibility; prefer ForkJoinPoolExecutor for new code.
     (defrecord PoolExecutor [^ExecutorService executor]
       PExecutor
       (execute! [_ spin-fn]
         (let [bindings (capture-targeted-bindings)
               ;; guard-task: the returned Future is discarded by every
               ;; caller — without the guard an escaped throw vanishes.
               bound-spin-fn (guard-task
                              (fn []
                                (with-bindings bindings
                                  (spin-fn))))]
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
               ;; guard-task: same discarded-Future rationale as PoolExecutor.
               bound-spin-fn (guard-task
                              (fn []
                                (with-bindings bindings
                                  (spin-fn))))]
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
             ;; guard-task: route escaped throws through the engine fault
             ;; hook instead of the global uncaught-error handler.
             bound-spin-fn (guard-task
                            #(bindings/restore-bindings captured-bindings spin-fn))]
         ;; Schedule on next tick and return nil (TODO: return promise)
         (js/setTimeout bound-spin-fn 0)
         nil))

     (execute-after! [_ delay-ms spin-fn]
       ;; Capture current dynamic bindings before scheduling
       (let [captured-bindings (bindings/capture-bindings)
             bound-spin-fn (guard-task
                            #(bindings/restore-bindings captured-bindings spin-fn))]
         ;; Use setTimeout for delayed execution; return its id so the
         ;; caller can clearTimeout it (see cancel-timer-handle!) and not
         ;; leak a pending timer for a completed / cancelled delayed spin.
         (js/setTimeout bound-spin-fn delay-ms)))))

#?(:clj
   (do
     (defn ^:no-doc thread-pool-executor
       "Create an executor backed by a fixed-size ThreadPoolExecutor with an
        unbounded LinkedBlockingQueue.

        ⚠️ This pool can deadlock when spins block on awaits because, unlike
        ForkJoinPool, it does not create compensating threads via managedBlock.
        Prefer `fork-join-executor` (or `default-executor`, which picks
        virtual threads on JVM 21+, FJ otherwise) for production use.

        Kept for niche cases where the caller wants explicit thread-pool
        semantics. Marked ^:no-doc so it does not surface in user-facing
        docs.

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

(defprotocol PRunsInline
  "Optional executor capability: `execute!` runs the task on the calling
  thread before it returns (SynchronousExecutor, and wrappers of it)."
  (runs-inline? [this]))

(extend-protocol PRunsInline
  SynchronousExecutor
  (runs-inline? [_] true))

(defn- inline-executor? [executor]
  (and (satisfies? PRunsInline executor) (runs-inline? executor)))

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

;; =============================================================================
;; Inline dispatch
;; =============================================================================
;;
;; Engine work that becomes ready while a thread is already running work of
;; the same executor (a drain session, a savepoint continuation) does not need
;; another thread: it is queued on this thread and runs when the current task
;; returns. Handing it to the executor instead costs a thread hop per engine
;; step (on a loaded JVM ~100 µs on virtual threads), which is most of the
;; latency of a short computation.
;;
;; The queue is a trampoline, so inline work never nests on the stack. After
;; `frame-batch` tasks the rest is handed back to the executor, so one chain of
;; work does not keep a pool thread (or the JS event loop) to itself; a
;; synchronous executor has no other thread to hand to, so its frames keep
;; pumping instead. Each task's escaping error is reported on its own (as an
;; executor task's is) and does not stop the tasks queued behind it.
;;
;; Work that arrives on a thread not running this executor's work (an embedder
;; thread, a timer, an IO callback) still goes to the executor, so embedder
;; threads never run engine work (with a synchronous executor every thread
;; runs it). Parallelism is explicit: `parallel` / `race` children, parallel
;; observer dispatch and delayed spins use `execute!`; `spread!` fans out.
;;
;; A task running in a frame must not block on work queued in its frame, since
;; that work runs only after it returns: blocking waits run `call-unframed`,
;; which first hands the queued work to the executor.

(def ^:private frame
  "Per thread: nil, or {:executor e :queue (volatile! PersistentQueue)}."
  #?(:clj (ThreadLocal.) :cljs (volatile! nil)))

(defn- current-frame []
  #?(:clj (.get ^ThreadLocal frame) :cljs @frame))

(defn- install-frame! [value]
  #?(:clj (if (nil? value)
            (.remove ^ThreadLocal frame)
            (.set ^ThreadLocal frame value))
     :cljs (vreset! frame value)))

(def ^:private frame-batch
  "How many queued tasks one frame runs before handing the rest back to the
  executor."
  256)

(defn- bound-task
  "`task` under the dynamic bindings an executor task would capture now."
  [task]
  #?(:clj (let [b (capture-targeted-bindings)]
            (if (empty? b) task (fn [] (with-bindings b (task)))))
     :cljs (let [b (bindings/capture-bindings)]
             (fn [] (bindings/restore-bindings b task)))))

(declare run-framed!)

(defn- hand-over!
  "Submit `tasks` (a queue) to `executor` as one framed task, in order. Returns
  false when the executor refuses them."
  [executor tasks]
  (try
    (execute! executor (fn [] (run-framed!
                               executor
                               ;; re-queue, so each one runs on its own
                               (fn [] (vswap! (:queue (current-frame)) into tasks)))))
    true
    (catch #?(:clj Throwable :cljs :default) error
      (fault/report-fault! ::fault/executor-task-fault {:error error :handoff-rejected? true})
      false)))

(defn run-framed!
  "Run `task` as work of `executor` on this thread, then the tasks it (and
  they) dispatched. A task that throws is reported (`guard-task`) and does not
  take the queued ones with it. Returns nil."
  [executor task]
  (let [outer (current-frame)
        queue (volatile! #?(:clj clojure.lang.PersistentQueue/EMPTY
                            :cljs cljs.core/PersistentQueue.EMPTY))
        local? (inline-executor? executor)]
    (install-frame! {:executor executor :queue queue})
    (try
      ((guard-task task))
      (loop [ran 0]
        (when-let [next-task (peek @queue)]
          (if (or local? (< ran frame-batch))
            (do (vswap! queue pop)
                ((guard-task next-task))
                (recur (inc ran)))
            ;; hand the tail back, in order; keep it here if refused
            (let [tail @queue]
              (vreset! queue (empty tail))
              (when-not (hand-over! executor tail)
                (vreset! queue tail)
                (recur 0))))))
      (finally (install-frame! outer)))
    nil))

(defn dispatch!
  "Run `task` on `executor`: behind the current task when this thread is
  already running that executor's work, as a new executor task otherwise."
  [executor task]
  (let [f (current-frame)]
    (if (and f (identical? executor (:executor f)))
      (do (vswap! (:queue f) conj (bound-task task)) nil)
      (execute! executor (fn [] (run-framed! executor task))))))

(defn call-unframed
  "Call `f` with no frame on this thread, so the work it dispatches goes to
  the executor, after handing the work already queued in this thread's frame
  to the executor (or, if it refuses, running it here first). For code that
  blocks until engine work is done: that work may already be queued here.
  The handed-over work runs concurrently with the rest of the current task,
  as an executor task would. Call it around the wait itself, so a call that
  does not wait hands nothing over."
  [f]
  (let [outer (current-frame)]
    (if (nil? outer)
      (f)
      (let [queue (:queue outer)
            queued @queue]
        (when (seq queued)
          (vreset! queue (empty queued))
          (when-not (hand-over! (:executor outer) queued)
            ;; refused: run it here before waiting on it
            (run-framed! (:executor outer)
                         (fn [] (vswap! (:queue (current-frame)) into queued)))))
        (install-frame! nil)
        (try (f) (finally (install-frame! outer)))))))

(def ^:private default-parallelism
  #?(:clj (.availableProcessors (Runtime/getRuntime)) :cljs 1))

(defn spread!
  "Explicit parallel fan-out: run `(task i)` for every i < n, split into about
  `parallelism` executor tasks (default: the processor count) of contiguous
  shares. Each share runs on one thread together with the work it dispatches;
  the first share stays on this thread when it already runs the executor's
  work (`dispatch!`). A `(task i)` that throws is reported (`guard-task`); the
  other indices still run. Returns nil. Code that then blocks until the tasks
  are done waits `call-unframed`, since the first share may be queued here.

  Inline dispatch keeps a computation on its thread, so fan-out that should
  use several cores says so here, at the grain it chooses."
  ([executor n task] (spread! executor n task default-parallelism))
  ([executor n task parallelism]
   (let [shares (max 1 (min n parallelism))
         size (quot (+ n shares -1) shares)]
     (dotimes [c shares]
       (let [lo (* c size) hi (min n (+ lo size))]
         (when (< lo hi)
           ;; each index on its own: one that throws is reported and the
           ;; rest of its share still runs
           (let [run-share (fn [] (loop [i lo] (when (< i hi) ((guard-task #(task i))) (recur (inc i)))))]
             (if (zero? c)
               (dispatch! executor run-share)
               (execute! executor (fn [] (run-framed! executor run-share))))))))
     nil)))
