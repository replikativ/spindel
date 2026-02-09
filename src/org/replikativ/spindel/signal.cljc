(ns org.replikativ.spindel.signal
  "Signal creation and manipulation"
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.incremental.interval :as iv]))

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

(declare swap-signal*-explicit get-signal-value)

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

       (compareAndSet [_ _ _]
         ;; CAS not yet supported for signals
         (throw (UnsupportedOperationException.
                 "compareAndSet not yet supported on signals")))]

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
               id# (org.replikativ.spindel.engine.addressing/next-address! ctx# "signal" ~source-loc)]
           (->SignalRef id# (d/clear-deltas ~initial-value)))))
     ([ctx initial-value]
      (let [source-loc {:file *file*
                        :line (:line (meta &form))
                        :column (:column (meta &form))}]
        `(let [ctx# ~ctx
               id# (org.replikativ.spindel.engine.addressing/next-address! ctx# "signal" ~source-loc)]
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

