(ns org.replikativ.spindel.signal
  "Signal creation and manipulation"
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.nodes :as nodes]
            ;; The `signal` macro's EXPANSION emits `addressing/next-address!`,
            ;; so any ns expanding `(signal …)` needs addressing loaded. Alias it
            ;; (not a bare require) so that dependency is visible at the use site
            ;; and doesn't rely on the engine chain being transitively pre-loaded.
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.incremental.interval :as iv]
            #?(:clj  [is.simm.partial-cps.async :refer [async await]]
               :cljs [is.simm.partial-cps.async :refer [await]]))
  #?(:cljs (:require-macros [is.simm.partial-cps.async :refer [async]])))

;; =============================================================================
;; Batching Support
;; =============================================================================

(def ^:dynamic *batching?*
  "When true, signal changes are collected instead of triggering immediately."
  false)

(def ^:dynamic *batched-signal-ids*
  "Accumulator for signal IDs during batch. Vector for order preservation."
  nil)

#?(:clj
   (defmacro batch
     "Execute body with signal updates batched into a single reactive propagation.

     Multiple signal updates within the batch body are collected and trigger
     only one reactive pass after the batch completes, rather than triggering
     after each individual update.

     Usage:
       (batch
         (reset! focus-signal new-id)
         (swap! blocks-signal conj new-block))
       ;; Single reactive pass happens here

     Benefits:
     - Avoids intermediate renders during multi-signal updates
     - Ensures consistent state view within batch
     - Improves performance for coordinated updates

     Notes:
     - Batch is synchronous-only (no async operations inside)
     - Nested batches work correctly (inner batch just adds to outer)
     - Returns the value of the last expression in body"
     [& body]
     `(if *batching?*
        ;; Already batching - just execute body (inner batch contributes to outer)
        (do ~@body)
        ;; Start new batch
        (binding [*batching?* true
                  *batched-signal-ids* (atom [])]
          (let [result# (do ~@body)
                ids# @*batched-signal-ids*]
            ;; Enqueue one event per distinct signal (preserve order)
            (doseq [id# (distinct ids#)]
              (ec/enqueue-event! {:type :signal-change :id id#}))
            result#)))))

;; CLJS version - function since macros not available cross-platform
#?(:cljs
   (defn batch*
     "Execute thunk with signal updates batched. See batch macro for details."
     [thunk]
     (if *batching?*
       ;; Already batching - just execute thunk
       (thunk)
       ;; Start new batch
       (binding [*batching?* true
                 *batched-signal-ids* (atom [])]
         (let [result (thunk)
               ids @*batched-signal-ids*]
           ;; Enqueue one event per distinct signal (preserve order)
           (doseq [id (distinct ids)]
             (ec/enqueue-event! {:type :signal-change :id id}))
           result)))))

;; =============================================================================
;; SignalRef - Signal Reference Type
;; =============================================================================

;; Signal State Structure (stored in runtime atom at [:signals signal-id]):
;; {:snapshot current-value           ; Wrapped with wrap-deltaable if applicable
;;  :old-snapshot previous-value
;;  :deltas [{:op :conj :path [] :value ...}]
;;  :deltaable? boolean               ; Explicit flag: can this signal track deltas?
;;  :observers #{spin-ids}}

(declare swap-signal*-explicit get-signal-value compare-and-set-signal!)

(defrecord SignalRef [id initial-value]
  Object
  (toString [_]
    (str "#SignalRef{:id " id ", :initial-value " initial-value "}"))

  #?@(:clj
      [clojure.lang.IDeref
       (deref [this]
         ;; Deref returns current snapshot value (unwrapped)
         ;; Requires *execution-context* to be bound
              (d/unwrap-deltaable (get-signal-value this)))

       clojure.lang.IAtom
       ;; Enable standard clojure.core/swap! and reset! on SignalRef.
       ;; These delegate to swap-signal*-explicit which uses ec/*execution-context*.
       (swap [this f]
             (swap-signal*-explicit this f))
       (swap [this f a]
             (swap-signal*-explicit this f a))
       (swap [this f a b]
             (swap-signal*-explicit this f a b))
       (swap [this f a b xs]
             (apply swap-signal*-explicit this f a b xs))

       (reset [this newval]
              (swap-signal*-explicit this (constantly newval)))

       (compareAndSet [this oldv newv]
                      (compare-and-set-signal! this oldv newv))]

      :cljs
      [IDeref
       (-deref [this]
         ;; Deref returns current snapshot value (unwrapped)
         ;; Requires *execution-context* to be bound
               (d/unwrap-deltaable (get-signal-value this)))

       ISwap
       (-swap! [this f]
               (swap-signal*-explicit this f))
       (-swap! [this f a]
               (swap-signal*-explicit this f a))
       (-swap! [this f a b]
               (swap-signal*-explicit this f a b))
       (-swap! [this f a b xs]
               (apply swap-signal*-explicit this f a b xs))

       IReset
       (-reset! [this newval]
                (swap-signal*-explicit this (constantly newval)))]))

;; Resolve print-method dispatch ambiguity. SignalRef is a defrecord —
;; so it is BOTH clojure.lang.IRecord and clojure.lang.IPersistentMap —
;; and it also implements IDeref. print-method has a method for each of
;; those three interfaces, and they are mutually unordered, so dispatch
;; is ambiguous unless EVERY pair is pinned. clojure.core pins
;; IRecord > IPersistentMap; we pin the other two pairs here. Without
;; the IPersistentMap/IDeref pin, dispatch throws "Multiple methods
;; match ... and neither is preferred" non-deterministically — whether
;; it throws depends on the hash-iteration order of print-method's
;; method table, which varies per JVM run. With all three pairs pinned,
;; IRecord always wins and a SignalRef prints in its default record form.
#?(:clj (prefer-method print-method clojure.lang.IRecord clojure.lang.IDeref))
#?(:clj (prefer-method print-method clojure.lang.IPersistentMap clojure.lang.IDeref))

;; Ensure a signal has an initialized entry in the runtime state
(defn ensure-signal-initialized!
  [^SignalRef signal-ref]
  (let [id (:id signal-ref)]
    (when-not (ec/get-state [:nodes id])
      ;; Write to [:nodes id] using SignalNode (Phase 1B)
      (ec/swap-state! [:nodes id]
                      (fn [existing-node]
                        (or existing-node
                            (let [wrapped (d/wrap-deltaable (:initial-value signal-ref))]
                              (nodes/->signal-node wrapped nil nil (d/deltaable? wrapped) #{}))))))
    nil))

;; Simple value read helper (non-reactive)
(defn get-signal-value
  [^SignalRef signal-ref]
  (ensure-signal-initialized! signal-ref)
  ;; NEW: Read from :nodes using protocol (Phase 1B read migration)
  (let [id (:id signal-ref)
        node (ec/get-state [:nodes id])]
    (when node
      (nodes/get-value node))))

(defn get-signal-state
  "Get full signal state from runtime.

  Returns SignalNode record from :nodes structure."
  [signal-ref]
  (ensure-signal-initialized! signal-ref)
  ;; NEW: Read from :nodes (Phase 1B read migration)
  (ec/get-state [:nodes (:id signal-ref)]))

(defn clear-signal-deltas!
  "Clear deltas from signal node after they've been consumed.

  This prevents stale deltas from being re-processed on subsequent
  spin executions that are triggered by changes to other signals.

  IMPORTANT: We only clear deltas, not old-snapshot. The old-snapshot
  is needed for reactive change detection."
  [signal-ref]
  (let [id (:id signal-ref)]
    (ec/swap-state! [:nodes id]
                    (fn [node]
                      (when node
                        (nodes/->signal-node
                         (nodes/get-value node)
                         (:old-snapshot node)  ; preserve old-snapshot for change detection
                         nil                   ; clear deltas only
                         (:deltaable? node)
                         (nodes/get-observers node)))))))

;; =============================================================================
;; Signal Interval Helper (replaces SignalDeltaView)
;; =============================================================================

;; SignalDeltaView has been replaced by the unified Interval type.
;; See org.replikativ.spindel.incremental.interval for the implementation.
;;
;; The Interval type supports:
;; - @interval → current value (new)
;; - (:new interval), (:old interval), (:deltas interval) → map access
;; - (let [[new old deltas] interval] ...) → sequential destructuring
;; - (let [{:keys [new old deltas]} interval] ...) → map destructuring

(defn signal-interval
  "Create an Interval from signal values.

   This is the replacement for signal-delta-view.
   Typically called via get-signal-detailed or track effect."
  ([value]
   (iv/->Interval nil value nil))
  ([old-value value]
   (iv/->Interval old-value value nil))
  ([old-value value deltas]
   (iv/->Interval old-value value deltas)))

;; =============================================================================
;; Signal Creation and Manipulation
;; =============================================================================

#?(:clj
   (defmacro signal
     "Create a SignalRef with deterministic ID based on addressing chain.

     Two arities:
     - (signal initial-value) - uses *execution-context* from dynamic binding
     - (signal ctx initial-value) - uses explicit execution context

     The ID is generated via the addressing module's hash-chain, ensuring:
     - Determinism: Same execution path → same signal IDs
     - Fork-safe: Forked contexts continue with their own chain
     - Collision-free: Sequential signals at same location get different IDs

     Examples:
       ;; Top-level with explicit context:
       (defonce runtime (ctx/create-execution-context))
       (def todos (signal runtime (d/deltaable-vector [])))

       ;; Inside spin (context is bound):
       (spin
         (let [local-state (signal 0)]
           ...))
     "
     ([initial-value]
      (let [source-loc {:file *file*
                        :line (:line (meta &form))
                        :column (:column (meta &form))}]
        `(let [ctx# (ec/current-execution-context)
               id# (addressing/next-address! ctx# "signal" ~source-loc)]
           (->SignalRef id# (d/clear-deltas ~initial-value)))))
     ([ctx initial-value]
      (let [source-loc {:file *file*
                        :line (:line (meta &form))
                        :column (:column (meta &form))}]
        `(let [ctx# ~ctx
               id# (addressing/next-address! ctx# "signal" ~source-loc)]
           (->SignalRef id# (d/clear-deltas ~initial-value)))))))

(defn- swap-signal*-explicit
  "Internal worker for swap-signal! using PState protocol."
  [signal-ref f & args]
  (ensure-signal-initialized! signal-ref)
  (let [id (:id signal-ref)]

    ;; Update signal value in [:nodes id] using SignalNode (Phase 1B)
    (let [new-node (ec/swap-state! [:nodes id]
                                   (fn [old-node]
                                     (when old-node
                                       (let [old-value (nodes/get-value old-node)
                                             new-value (apply f old-value args)
                                             deltas (d/get-deltas new-value)
                                             clean-value (d/clear-deltas new-value)
                               ;; Increment generation for O(1) identity-based caching
                                             old-generation (or (:generation old-node) 0)]
                                         (nodes/->signal-node clean-value
                                                              old-value
                                                              deltas
                                                              (:deltaable? old-node)
                                                              (nodes/get-observers old-node)
                                                              (inc old-generation))))))]

      ;; Either collect for batch or enqueue immediately
      (if (and *batching?* *batched-signal-ids*)
        ;; Batching: collect signal ID for later
        (swap! *batched-signal-ids* conj id)
        ;; Normal: enqueue engine event for reactive propagation
        (ec/enqueue-event! {:type :signal-change :id id}))

      ;; Return new snapshot
      (nodes/get-value new-node))))

(defn- swap-signal-changed?-explicit
  "Like swap-signal*-explicit, but returns a boolean indicating if the value changed.

  Ensures change detection is computed atomically within the update."
  [signal-ref f & args]
  (ensure-signal-initialized! signal-ref)
  (let [id (:id signal-ref)
        changed? (volatile! false)]

    ;; Update signal value in [:nodes id] using SignalNode (Phase 1B)
    (ec/swap-state! [:nodes id]
                    (fn [old-node]
                      (when old-node
                        (let [old-value (nodes/get-value old-node)
                              new-value (apply f old-value args)
                              deltas (d/get-deltas new-value)
                              clean-value (d/clear-deltas new-value)
                ;; Increment generation for O(1) identity-based caching
                              old-generation (or (:generation old-node) 0)]
                          (vreset! changed? (not= old-value clean-value))
                          (nodes/->signal-node clean-value
                                               old-value
                                               deltas
                                               (:deltaable? old-node)
                                               (nodes/get-observers old-node)
                                               (inc old-generation))))))

    ;; Enqueue engine event
    (ec/enqueue-event! {:type :signal-change :id id})

    ;; Return changed flag
    @changed?))

(defn swap-signal-changed?
  "Like swap! but returns boolean indicating if the signal value changed.

  Usage: (swap-signal-changed? signal f & args)

  Returns true if the signal value changed, false otherwise.

  Note: Use standard swap!/reset! for normal updates. This function is only
  needed when you want to know if a swap actually changed the value."
  [signal-ref f & args]
  (apply swap-signal-changed?-explicit signal-ref f args))

(defn deref-signal
  "Dereference signal to get current value. Non-reactive.

  This is a simple read that does NOT track dependencies.
  Use await inside a spin for reactive reads.
  "
  [signal-ref]
  (get-signal-value signal-ref))

(defn compare-and-set-signal!
  "Atomically install `newval` iff the signal's current value is `identical?` to
   `oldval` — atom-CAS semantics, where `oldval` is the exact object the caller just
   read. Returns true on success, false if the value changed under it.

   The compare + install are ONE atomic step over the engine's `cas-state!` on the
   signal node (the same runtime CAS the engine exposes for 'advanced CAS patterns'),
   so a concurrent write can never be lost — no extra lock or coordination state, just
   the runtime's own atomicity. On success it bumps the generation and enqueues a
   reactive change like any `swap!`. This is the primitive a race-free
   read→await→commit uses (`swap-await!`): a false return means re-read and re-merge."
  [signal-ref oldval newval]
  (ensure-signal-initialized! signal-ref)
  (let [id (:id signal-ref)]
    (loop []
      (let [old-node (ec/get-state [:nodes id])]
        (cond
          (nil? old-node) false
          (not (identical? (nodes/get-value old-node) oldval)) false
          :else
          (let [deltas      (d/get-deltas newval)
                clean-value (d/clear-deltas newval)
                new-node    (nodes/->signal-node clean-value
                                                 (nodes/get-value old-node)
                                                 deltas
                                                 (:deltaable? old-node)
                                                 (nodes/get-observers old-node)
                                                 (inc (or (:generation old-node) 0)))]
            ;; cas-state! guards on node identity; a losing race (node replaced, even
            ;; with an =-value) re-checks the value identity above and retries — a
            ;; bounded sync loop (no await inside ⇒ no partial-cps loop/recur hazard).
            (if (ec/cas-state! [:nodes id] old-node new-node)
              (do (ec/enqueue-event! {:type :signal-change :id id}) true)
              (recur))))))))

(defn signal-ref?
  "True if `x` is a spindel SignalRef (runtime-backed signal) vs a plain atom."
  [x]
  (instance? SignalRef x))

(defn cas!
  "Compare-and-set across both signal kinds: install `newval` iff the current value is
   the just-read `oldval`; returns boolean. A spindel `SignalRef` goes through the
   runtime-atomic `compare-and-set-signal!`; a plain atom uses core `compare-and-set!`."
  [signal oldval newval]
  (if (signal-ref? signal)
    (compare-and-set-signal! signal oldval newval)
    (compare-and-set! signal oldval newval)))

(defn swap-await!
  "Async signal mutation for IO-backed / interval values (the bridge for a
   ygg-signal whose value is a yggdrasil system).

   Reads the current value, computes the new value OUTSIDE the engine swap —
   `(await (f current & args))`, so `f` may suspend on IO (e.g. a konserve-backed
   yggdrasil merge/commit on cljs) — then commits it and propagates reactively
   like any signal change. Returns a partial-cps `async`: `await` it from a spin
   (or run/deref it at the JVM REPL — it resolves synchronously when `f` is sync).

   CONTRACT: `f` MUST return an *awaitable* — a partial-cps CPS value (what a
   yggdrasil op returns in async mode). For a SYNCHRONOUS update just use `swap!`;
   the ygg-signal wrapper dispatches `swap!` vs `swap-await!` by the value's sync
   mode. We deliberately do NOT auto-detect: a partial-cps `async` IS a bare
   2-arg fn, indistinguishable from a function VALUE, so a `fn?` heuristic would
   silently mis-handle a signal whose value is a function — hence the explicit
   async contract.

   `f` carries the merge semantics (e.g. `#(p/merge! % branch)` / a CRDT `-join`);
   the signal core stays value-agnostic. RACE-FREE: the commit is a `compare-and-set-
   signal!` against the value read before the await, so a concurrent `swap!`/
   `swap-await!` landing during the IO is detected and `f` re-run against the fresh
   value (the CRDT merge is idempotent/commutative ⇒ the retry converges, nothing is
   lost). No lock or extra state — the signal's own atomic node-CAS is the only
   primitive. The commit rebinds the execution context captured at call time, since
   the post-IO resume may land off the engine thread."
  [signal-ref f & args]
  (let [ctx (ec/current-execution-context)]
    (letfn [(attempt []
              (async
               (let [cur (deref-signal signal-ref)
                     new (await (apply f cur args))]
                 (ec/with-context ctx
                   (if (compare-and-set-signal! signal-ref cur new)
                     new
                     ;; a write landed during the await — re-merge against the new
                     ;; current. Function recursion, NOT loop/recur: recur across an
                     ;; await can hang in partial-cps.
                     (await (attempt)))))))]
      (attempt))))

(defn get-signal-detailed
  "Get signal value wrapped in Interval for dual perspective access.

  Returns an Interval that can be destructured:
     (let [[new old deltas] (get-signal-detailed sig)] ...)
     (let [{:keys [new old deltas]} (get-signal-detailed sig)] ...)

  Deltas:
  - nil if the value is not deltaable
  - [] if the value is deltaable but no changes yet
  - [delta...] if there are deltas"
  [signal-ref]
  (ensure-signal-initialized! signal-ref)
  (let [signal-state (get-signal-state signal-ref)
        snapshot (:snapshot signal-state)]
    (signal-interval (:old-snapshot signal-state)
                     snapshot
                     (:deltas signal-state))))

