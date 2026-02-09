(ns org.replikativ.spindel.spin.combinators
  "Spin combinators - parallel, race, sleep, rate control, and accumulation"
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; Explicit Parallelism
;; =============================================================================

(defn parallel
  "Execute spins concurrently, return vector of results.

   Returns a Spin that completes when all children complete.
   If any child fails, all siblings are cancelled and error propagates (fail-fast).

   **Reactive behavior**: When child spins track signals and those signals change,
   the children re-run and parallel updates its result, notifying awaiters.

   Uses continuation-based execution - can be awaited in other spins without
   breaking the continuation chain.

   Example:
     (parallel spin-a spin-b spin-c)  ; => [result-a result-b result-c]

   Can be awaited in another spin:
     (spin
       (let [[a b c] (await (parallel spin-a spin-b spin-c))]
         (+ a b c)))

   Reactive example:
     (let [sig-a (signal 1)
           sig-b (signal 2)]
       (spin
         (let [[a b] (await (parallel
                              (spin (:new (track sig-a)))
                              (spin (:new (track sig-b)))))]
           (+ a b))))  ; Re-runs when sig-a or sig-b change

   With thread-pool-executor:
   - Each child spin runs on a separate thread pool worker
   - All spins execute concurrently (up to thread pool size)
   - Parent spin suspended until all complete

   With immediate-executor (testing):
   - Spins execute sequentially on calling thread
   - Deterministic execution order
   - No actual parallelism

   Thread-safety:
   - Atomic coordination via atoms
   - Each spin uses its own tracking slot
   - No race conditions in result collection

   Fork-safety:
   - Results stored in runtime state (not local atoms) for clean forking
   - Coordination atoms (completed, done?) are write-once, not forked"
  [& spins]
  (when (empty? spins)
    (throw (ex-info "parallel requires at least one spin" {})))
  (let [execution-context (ec/current-execution-context)
        ;; Generate ID upfront so we can reference it in continuations
        parallel-spin-id (keyword (gensym "parallel-"))
        n (count spins)
        ;; Coordination atoms are write-once during initial completion
        ;; These don't need to be in runtime state since they're only used once
        completed (atom 0)
        done? (atom false)
        spin-vec (vec spins)
        ;; Path in runtime state for this parallel's results
        results-path [:parallel/results parallel-spin-id]]
    (binding [ec/*execution-context* execution-context]
      ;; Initialize results vector in runtime state (fork-safe)
      (ec/swap-state! results-path (constantly (vec (repeat n nil))))

      (spin-core/make-spin
       (fn [resolve reject]
         ;; Start each child using CPS (no deref). The child will invoke our callbacks
         ;; when it completes; we coordinate final resolution here.
         (doseq [[i child-spin] (map-indexed vector spin-vec)]
           (let [on-ok (fn [v]
                         ;; Update result for this child in runtime state (fork-safe)
                         (ec/swap-state! results-path #(assoc % i v))
                         (when (= n (swap! completed inc))
                           ;; All children completed initially
                           (when (compare-and-set! done? false true)
                             ;; Capture initial values BEFORE registering continuations
                             ;; Used to distinguish initial completion events (already in queue)
                             ;; from re-completions (should trigger notifications)
                             (let [initial-results (vec (ec/get-state results-path))]
                               ;; Register continuations for reactive child re-completions
                               ;; This makes parallel reactive: when children re-run due to
                               ;; tracked signal changes, parallel will update and notify awaiters
                               ;; Only register for actual Spins (not deferreds which are one-shot)
                               (doseq [[j t] (map-indexed vector spin-vec)]
                                 (when (satisfies? spin-core/PSpin t)
                                   (let [t-id (spin-core/spin-id t)
                                         initial-val (get initial-results j)
                                         captured-bindings (bindings/capture-bindings)
                                         cont-map {:event-key [:spin/complete t-id]
                                                   :resolve-fn (fn [_]
                                                                 ;; Child completed, check if value changed from initial
                                                                 ;; This distinguishes initial completion events (still in queue)
                                                                 ;; from actual re-completions due to signal changes
                                                                 (let [child-result (ec/spin-current-result t-id)
                                                                       new-val (:payload child-result)]
                                                                   ;; Only notify if value differs from initial
                                                                   ;; Initial completion events have same value as initial-val
                                                                   ;; Re-completions have different value
                                                                   (when (not= new-val initial-val)
                                                                     ;; Update result in runtime state (fork-safe)
                                                                     (ec/swap-state! results-path #(assoc % j new-val))
                                                                     ;; Get current results and re-cache
                                                                     (let [current-results (ec/get-state results-path)]
                                                                       ;; Re-cache parallel's result to notify our awaiters
                                                                       (ec/spin-cache-result!
                                                                         parallel-spin-id
                                                                         (spin-core/ok current-results))
                                                                       ;; Fire completion event to resume awaiting spins
                                                                       (ec/enqueue-event!
                                                                         {:type :spin-completion :id parallel-spin-id})))))
                                                 :reject-fn (fn [e]
                                                              ;; Child failed on re-run
                                                              (ec/spin-cache-result!
                                                                parallel-spin-id
                                                                (spin-core/error e))
                                                              (ec/enqueue-event!
                                                                {:type :spin-completion :id parallel-spin-id}))
                                                 :bindings captured-bindings
                                                 :on-resume (fn [_] nil)}]
                                      (ec/continuation-add! parallel-spin-id cont-map))))
                               ;; Initial resolve with current results from runtime state
                               (spin-core/resume resolve (ec/get-state results-path))))))

                 on-err (fn [e]
                          ;; First error wins; cancel siblings and reject
                          (when (compare-and-set! done? false true)
                            (doseq [[j other] (map-indexed vector spin-vec)]
                              (when (not= i j)
                                (spin-core/cancel-spin! other)))
                            (spin-core/resume reject e)))]
             ;; Invoke child spin via execution-context scheduling to enable parallelism
             ;; Must explicitly bind *execution-context* because CLJS capture-bindings excludes it
             ;; to avoid circular references
             (ec/schedule-spin-execution! execution-context
                                           (fn []
                                             (binding [ec/*execution-context* execution-context]
                                               (child-spin on-ok on-err))))))

         ;; Async coordination; parent suspends
         spin-core/incomplete)
       parallel-spin-id))))

;; =============================================================================
;; Delay Primitive
;; =============================================================================

(defn sleep
  "Create a spin that completes with given value after specified duration (in milliseconds).

   Example:
     (def delayed (sleep 1000 :done))
     @delayed  ; => :done (after 1000ms)

   With immediate-executor (testing):
   - Executes immediately without delay (deterministic)

   With thread-pool-executor:
   - Sleeps the worker thread for the duration
   - Blocks one thread from pool while sleeping"
  ([duration]
   (sleep duration nil))
  ([duration value]
   (let [execution-context (ec/current-execution-context)]
    (binding [ec/*execution-context* execution-context]
       (spin-core/make-spin
        (fn [resolve _]
          ;; Non-blocking delay via execution-context scheduling
          ;; Event loop will establish binding when spin executes
          (ec/schedule-delayed-execution! execution-context duration
                                           #(spin-core/resume resolve value))
          spin-core/incomplete))))))

;; =============================================================================
;; Race Combinator
;; =============================================================================

(defn race
  "Execute spins concurrently, return result of first to complete.

   Returns a Spin that completes when first child completes.
   All losing spins are cancelled when winner is determined.

   Uses continuation-based execution - can be awaited in other spins without
   breaking the continuation chain.

   Example:
     (def fast (spin (do (Thread/sleep 10) :fast)))
     (def slow (spin (do (Thread/sleep 100) :slow)))

     @(race fast slow)  ; => :fast

   Can be awaited in another spin:
     (spin
       (let [result (await (race fast-spin slow-spin))]
         (process result)))

   Error handling:
   - If first spin to complete fails, race fails with that error
   - All losing spins are cancelled (cooperative - checked at await points)
   - Cancellation propagates through observer chains

   With immediate-executor (testing):
   - Returns result of first spin only
   - Deterministic behavior

   Use cases:
   - Timeouts with fallbacks
   - Multiple data sources (use fastest)
   - Redundant requests for reliability"
  [& spins]
  (when (empty? spins)
    (throw (ex-info "race requires at least one spin" {})))
  ;; Capture execution-context at creation time (like parallel does)
  ;; This ensures bindings are captured before any async scheduling
  (let [execution-context (ec/current-execution-context)]
    (binding [ec/*execution-context* execution-context]
      (spin-core/make-spin
       (fn [resolve reject]
         (let [done? (atom false)
               spin-vec (vec spins)]
           (doseq [[idx t] (map-indexed vector spin-vec)]
             (let [on-ok (fn [v]
                           (when (compare-and-set! done? false true)
                             ;; Cancel losing spins cooperatively
                             ;; Wrap in try-catch to handle any synchronous exceptions
                             ;; from the cancellation machinery
                             (doseq [[j other-t] (map-indexed vector spin-vec)]
                               (when (not= idx j)
                                 (try
                                   (spin-core/cancel-spin! other-t)
                                   (catch #?(:clj Throwable :cljs :default) _
                                     ;; Ignore cancellation errors - already handled
                                     ;; by the on-err callback's ex-data check
                                     nil))))
                             (spin-core/resume resolve v)))
                   on-err (fn [e]
                            ;; Ignore cancellation errors from losing spins
                            ;; (they're expected when a winner cancels them)
                            (when-not (= spin-core/spin-cancelled (:type (ex-data e)))
                              (when (compare-and-set! done? false true)
                                (spin-core/resume reject e))))]
               ;; Use captured execution-context, and bind it for the spin execution
               (ec/schedule-spin-execution! execution-context
                                             (fn []
                                               (binding [ec/*execution-context* execution-context]
                                                 (t on-ok on-err))))))
           spin-core/incomplete))))))

;; =============================================================================
;; Rate Control Combinators
;; =============================================================================

(defn debounce
  "Delay delivery by duration-ms before returning source value.

   For one-shot spins: Waits duration-ms, then returns the source value.

   For signal-based usage: When used with signals (via track), this provides
   debounce semantics where the value is only returned after the source
   goes quiet for duration-ms. The containing spin re-executes when the
   signal changes, which restarts the debounce timer.

   Useful for text input where you want to wait before processing.

   Example:
     ;; Only update preview after 300ms delay
     (spin
       (let [content (await (debounce (track content-sig) 300))]
         (render-preview content)))

   Args:
     source-spin: A spin or effect that produces values
     duration-ms: Time in milliseconds to wait before returning"
  [source-spin duration-ms]
  (spin
    (await (sleep duration-ms nil))  ; Wait for duration
    (await source-spin)))            ; Then return source value

(defn throttle
  "Wait for at least interval based on max-hz before returning source value.

   For one-shot spins: Waits for the interval duration, then returns the
   source value. The merge-fn is applied to nil and the source value.

   For signal-based usage: When used with signals (via track), this provides
   throttle semantics where updates are limited to max-hz frequency.
   The containing spin re-executes when the signal changes.

   merge-fn: (fn [accumulated-value new-value] -> merged-value)
     For 'keep latest' semantics, use: (fn [_ new] new)
     For 'collect all' semantics, use: (fn [acc new] (conj (or acc []) new))

   Example:
     ;; Limit window updates to 30fps, keeping only latest
     (spin
       (let [window (await (throttle (track window-signal) 30 (fn [_ new] new)))]
         (render-visible-items window)))

   Args:
     source-spin: A spin or effect that produces values
     max-hz: Maximum updates per second
     merge-fn: Function to merge accumulated values"
  [source-spin max-hz merge-fn]
  (let [interval-ms (/ 1000 max-hz)]
    (spin
      ;; Wait for interval, then return source value through merge-fn
      (await (sleep interval-ms nil))
      (merge-fn nil (await source-spin)))))

(defn sample
  "Sample the latest value at fixed intervals.

   Returns a Spin that waits for each interval, then gets and returns
   the current value from source-spin. Ignores all intermediate values.

   Example:
     ;; Sync state to server every 5 seconds
     (spin
       (let [state (await (sample (track app-state-signal) 5000))]
         (persist-to-server! state)))

   Args:
     source-spin: A spin or effect that produces values
     interval-ms: Sampling interval in milliseconds"
  [source-spin interval-ms]
  (spin
    (await (sleep interval-ms nil))  ; Wait for interval
    (await source-spin)))            ; Get and return current value

(defn relieve
  "Drop intermediate values when observer is slower than producer.

   Returns a Spin that always delivers the latest available value.
   If new values arrive while processing the previous one, intermediate
   values are dropped.

   Useful for real-time displays where freshness matters more than completeness.

   Example:
     ;; Only focus the final target after rapid navigation
     (spin
       (let [focus-id (await (relieve (track focus-signal)))]
         (when focus-id
           (focus-element! focus-id))))

   Args:
     source-spin: A spin or effect that produces values"
  [source-spin]
  (let [latest (atom nil)
        version (atom 0)]
    (spin
      (let [my-version (swap! version inc)]
        ;; Get value from source
        (let [v (await source-spin)]
          (reset! latest v)
          ;; Check if we're still current
          (if (= @version my-version)
            v  ; No newer value, deliver this one
            ;; Newer value arrived, return latest
            @latest))))))

(defn timeout
  "Race a spin against a timeout, returning fallback if timeout wins.

   Returns a Spin that races source-spin against a timeout. If source-spin
   completes first, returns its value. If timeout wins, returns fallback-value.

   This is a convenience wrapper around race + sleep for SLA-style guarantees.

   Example:
     ;; Process within 100ms or return cached data
     (spin
       (let [data (await (timeout (fetch-remote-data) 100 cached-data))]
         (render data)))

   Args:
     source-spin: The spin to race against timeout
     timeout-ms: Timeout duration in milliseconds
     fallback-value: Value to return if timeout wins"
  [source-spin timeout-ms fallback-value]
  (spin
    (let [result (await (race
                          source-spin
                          (sleep timeout-ms ::timeout)))]
      (if (= result ::timeout)
        fallback-value
        result))))

;; =============================================================================
;; Accumulator Combinator (CRDT-like Delta Merging)
;; =============================================================================

(defn accumulate
  "Accumulate intervals from a signal during rate-controlled observation.

   Creates a spin that tracks a signal and accumulates intervals between reads
   using an associative merge function. This preserves delta history when signals
   change faster than the observer can process.

   The merge-fn must be associative (like a CRDT or semigroup operation):
     merge(merge(a, b), c) = merge(a, merge(b, c))

   Use iv/merge-intervals for standard delta accumulation.

   How it works:
   1. The atom 'accumulated' persists across spin re-executions (closure capture)
   2. On each signal change, spin re-runs, merging new interval with accumulated
   3. Rate control combinators (throttle/debounce) delay delivery
   4. Final delivery contains all accumulated deltas

   Example:
     ;; Throttle at 10 Hz, preserving all deltas
     (spin
       (let [iv (await (throttle (accumulate todos iv/merge-intervals) 10 (fn [_ new] new)))]
         ;; iv contains ALL deltas since last delivery
         (process-incrementally iv)))

     ;; Debounce with delta preservation
     (spin
       (let [iv (await (debounce (accumulate input-signal iv/merge-intervals) 300))]
         (save-with-deltas iv)))

   Args:
     signal-ref: SignalRef to track
     merge-fn: (fn [accumulated-interval new-interval] -> merged-interval)
               Use iv/merge-intervals for delta accumulation

   Returns: Spin that delivers accumulated Interval on each run

   Note: Without accumulate, rate control may lose intermediate deltas.
   Use accumulate when you need complete delta history for incremental processing."
  [signal-ref merge-fn]
  ;; Atom persists across spin re-executions (captured in closure)
  (let [accumulated (atom nil)]
    (spin
      (let [current-interval (track signal-ref)
            merged (merge-fn @accumulated current-interval)]
        ;; Store for next run
        (reset! accumulated merged)
        ;; Return accumulated interval
        merged))))
