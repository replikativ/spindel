(ns org.replikativ.spindel.effects.track
  "track effect - read SignalRef with dual perspective.

  Returns an Interval with:
  - old: previous value (old-snapshot from SignalNode)
  - new: current value (snapshot from SignalNode)
  - deltas: incremental changes

  The Interval supports:
  - @interval → returns new value
  - (:new interval), (:old interval), (:deltas interval) → accessor keys
  - Destructuring: (let [{:keys [new old deltas]} interval] ...)

  This enables seamless integration with incremental combinators:
    (spin
      (let [todos-iv (track todos)]
        (->> todos-iv (ifilter :active) (imap :hours) (ireduce + 0))))"
  (:require [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.bindings :as bindings]
            [org.replikativ.spindel.state.signal :as sig]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.runtime.effects :as eff]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.log :as log])
  #?(:clj (:import [org.replikativ.spindel.state.signal SignalRef])))

(defn signal-ref?
  "Check if value is a SignalRef. Works across CLJ/CLJS."
  [x]
  (instance? #?(:clj SignalRef :cljs sig/SignalRef) x))

;; =============================================================================
;; Public API Shim
;; =============================================================================

(defn track
  "Place a breakpoint to track a SignalRef with dual perspective.

  Returns map with :snapshot, :old-snapshot, :deltas, :deltaable?.
  Must only be called inside a spin; outside, this throws."
  [& _]
  (throw (ex-info "track called outside of spin context (should be CPS-transformed)" {})))

;; =============================================================================
;; Direct Handler Implementation
;; =============================================================================

(defn- get-track-value
  "Get the value to return from track.

  Returns an Interval containing:
  - old: previous snapshot value
  - new: current snapshot value
  - deltas: structural changes from deltaable operations

  The Interval is compatible with:
  - @interval → current value
  - (:new interval), (:old interval), (:deltas interval)
  - Destructuring: {:keys [new old deltas]}
  - Incremental combinators: (ifilter pred interval)"
  [signal-ref]
  (let [node (sig/get-signal-state signal-ref)
        old-snapshot (:old-snapshot node)
        snapshot (:snapshot node)
        deltas (:deltas node)]
    ;; Return as Interval for unified incremental programming model
    (iv/->Interval old-snapshot snapshot deltas)))

(defn- get-track-value-if-newer
  "Get track value, but only include deltas if signal generation is newer.

  This prevents stale deltas from being re-processed when a spin re-executes
  without the signal actually changing. Each observer tracks its own
  'consumed generation' to ensure deltas are delivered exactly once per observer.

  Args:
    signal-ref - The SignalRef to read
    consumed-generation - The generation this observer last consumed

  Returns:
    Interval with deltas if generation > consumed-generation,
    Interval without deltas (nil) if generation <= consumed-generation (stale)"
  [signal-ref consumed-generation]
  (let [node (sig/get-signal-state signal-ref)
        current-generation (or (:generation node) 0)
        old-snapshot (:old-snapshot node)
        snapshot (:snapshot node)
        deltas (:deltas node)]
    (if (> current-generation consumed-generation)
      ;; Signal has new changes since we last consumed - return with deltas
      (do
        (log/trace! {:event :track/returning-fresh-deltas
                     :data {:current-gen current-generation
                            :consumed-gen consumed-generation
                            :delta-count (count deltas)}})
        (iv/->Interval old-snapshot snapshot deltas))
      ;; Stale - signal hasn't changed since our last consume
      ;; Return current value but WITHOUT deltas to prevent re-processing
      (do
        (log/trace! {:event :track/skipping-stale-deltas
                     :data {:current-gen current-generation
                            :consumed-gen consumed-generation}})
        (iv/->Interval snapshot snapshot nil)))))

(defn- track-signal
  "Direct track handler for SignalRef.

  Stores persistent continuation that can be resumed when signal changes.
  Returns an Interval containing old/new/deltas from the signal.

  The Interval enables seamless integration with incremental combinators
  for O(delta) reactive pipelines.

  Like laufzeit's consume: returns value immediately on first call,
  but stores continuation for resumption on signal changes.

  IMPORTANT: Per-observer generation tracking ensures deltas are delivered
  exactly once per observer. Each continuation captures the signal's current
  generation, and on resume only returns deltas if the generation advanced."
  [signal-ref spin-id source-loc resolve]
  ;; Ensure signal is initialized
  (sig/ensure-signal-initialized! signal-ref)

  (let [signal-id (.-id signal-ref)
        ;; Capture current generation for staleness detection on resume
        ;; This ensures each observer only sees deltas once, even if multiple
        ;; observers track the same signal or if a spin re-executes
        current-node (sig/get-signal-state signal-ref)
        current-generation (or (:generation current-node) 0)]

    ;; Store continuation for later resumption (like laufzeit's consume)
    ;; The :on-resume callback fetches fresh signal value when resuming
    ;; Continuations are never removed - fully reactive incremental graph
    ;; IMPORTANT: Capture bindings so they're restored when continuation resumes
    ;; This ensures dynamic vars like *yield-handler* are available after suspension
    ;; ALSO capture context bindings (DOM context like :dom/parent-addr, :dom/current-slot)
    ;; These are stored in ExecutionContext's :bindings field, not as dynamic vars
    (when spin-id
      (let [captured-bindings (bindings/capture-bindings)
            ;; Capture context bindings for DOM addressing
            captured-ctx-bindings (when-let [ctx (rtc/current-execution-context)]
                                    (:bindings ctx))
            cont {:event-key [:signal signal-id]
                  :resolve-fn resolve
                  :source-loc source-loc
                  :signal-id signal-id
                  :bindings captured-bindings
                  :ctx-bindings captured-ctx-bindings
                  ;; Capture generation at continuation creation time
                  ;; On resume, we only return deltas if signal generation > this value
                  :consumed-generation current-generation
                  ;; :on-resume fetches fresh signal value when resuming
                  ;; Uses captured generation to detect stale deltas
                  :on-resume (fn [_]
                               (get-track-value-if-newer signal-ref current-generation))}]
        (rtc/continuation-add! spin-id cont)
        (rtc/deps-track-signal! spin-id signal-id)
        (log/debug! {:event :track/registered
                     :data {:spin-id spin-id
                            :signal-id signal-id
                            :consumed-generation current-generation}})))

    ;; Return value via resolve continuation (synchronous on first call)
    ;; CRITICAL: Must call spin-core/resume like await does, not return value directly
    ;; Continuation is stored for later resumptions on signal changes
    ;; On first call, we return full deltas (initial render needs them)
    (spin-core/resume resolve (get-track-value signal-ref))))

(defn track-handler
  "Unified direct track handler - dispatches based on type.

  This is the entry point called from CPS-transformed code.
  Only handles SignalRef."
  [trackable spin-id source-loc resolve reject]
  (try
    ;; Check cancellation at track point
    (eff/check-cancellation! spin-id)

    ;; Type check
    (cond
      (signal-ref? trackable)
      (track-signal trackable spin-id source-loc resolve)

      :else
      (reject (eff/type-error 'track "SignalRef (not spins)" trackable)))

    (catch #?(:clj Throwable :cljs js/Error) t
      (reject t))))

;; =============================================================================
;; Registration
;; =============================================================================

(eff/register-effect-by-symbol!
  'org.replikativ.spindel.effects.track/track
  ::track-handler
  'org.replikativ.spindel.runtime.effects/one-arg->awaitable-map
  'org.replikativ.spindel.effects.track/track-handler)
