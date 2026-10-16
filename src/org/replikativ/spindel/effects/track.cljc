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
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.engine.effects :as eff]
            [org.replikativ.spindel.incremental.interval :as iv]
            [replikativ.logging :as log])
  #?(:clj (:import [org.replikativ.spindel.signal SignalRef])))

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

(defn- interval-since
  "[interval generation]: the signal's Interval as `get-track-value-if-newer`
  for `consumed-generation`: with the node's deltas if it changed since, without
  them otherwise, and the generation it was read at — one
  read of the node, so the generation recorded as handed out is the one whose
  deltas were."
  [signal-ref consumed-generation]
  (let [node (sig/get-signal-state signal-ref)
        generation (or (:generation node) 0)]
    [(if (> generation consumed-generation)
       (iv/->Interval (:old-snapshot node) (:snapshot node) (:deltas node))
       (iv/->Interval (:snapshot node) (:snapshot node) nil))
     generation]))

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
  [signal-ref spin-id source-loc resolve reject]
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
    ;; ALSO capture the per-slice :slice-state (see below)
    (when spin-id
      (let [captured-bindings (bindings/capture-bindings)
            ctx (ec/current-execution-context)
            ;; Capture context bindings for DOM addressing (DOM context like
            ;; :dom/parent-addr, :dom/current-slot). These are stored in
            ;; ExecutionContext's :bindings field, not as dynamic vars.
            captured-ctx-bindings (when ctx (:bindings ctx))
            ;; Capture transient deps tracking so resumed body slice continues
            ;; from the pre-suspend accumulator rather than empty (which would
            ;; cause record-deps! to wrongly remove the pre-suspend slice's deps).
            ;; IMPORTANT: Include THIS signal-id in the snap. The track effect
            ;; advances :spin-tracking by adding `signal-id` (via deps-track-signal!
            ;; below). On resume from this cont, the body slice continues from
            ;; AFTER the (track ...) call — so the body won't re-track this
            ;; signal during the slice. Without including it here, the restored
            ;; tracking would be missing this signal, and the eventual
            ;; record-deps! would commit a deps set that excludes it — leaving
            ;; the signal with no observer and no future resumes.
            base-snap (when ctx (rtp/get-state ctx [:spin-tracking spin-id]))
            tracking-snap (-> (or base-snap {})
                              (update :signals (fnil conj #{}) signal-id))
            ;; Capture this spin's per-spin addressing chain-head so any
            ;; `(spin …)` / `(effect …)` minted in the post-resume body slice
            ;; produce the same ids on every re-run. Under per-spin scoping
            ;; (see engine/addressing.cljc) the chain-head lives on this
            ;; spin's node in ctx state and is never modified by other
            ;; spins running during the suspend interval — so this snapshot
            ;; is safe to restore and cannot collide across distinct spins.
            chain-head-snap (addressing/get-chain-head ctx)
            ;; The children this run holds at the suspend point. A resume
            ;; from here does not re-evaluate their (spin …) forms, so they
            ;; stay held (`:kept-children`); a child created AFTER this
            ;; point that the resumed slice does not re-create is dropped —
            ;; reapable once orphaned (`superseded-child?`).
            live-children-snap (when ctx
                                 (simple/live-children
                                  (rtp/get-state ctx [:nodes spin-id])))
            ;; Named here so :on-resume can find this continuation in state
            cont-id (keyword (str "cont-" (random-uuid)))
            cont {:id cont-id
                  :event-key [:signal signal-id]
                  :kind :track
                  :resolve-fn resolve
                  :reject-fn reject
                  :source-loc source-loc
                  :signal-id signal-id
                  :bindings captured-bindings
                  ;; The per-slice snapshot the engine restores at resume:
                  ;; context bindings, addressing chain-head, deps tracking.
                  ;; restore-slice-state! in engine/impl/simple.cljc puts
                  ;; each piece back before the body slice resumes.
                  :slice-state {:bindings captured-ctx-bindings
                                :chain-head chain-head-snap
                                :tracking tracking-snap
                                :live-children live-children-snap}
                  ;; Capture generation at continuation creation time
                  ;; On resume, we only return deltas if signal generation > this value
                  :consumed-generation current-generation
                  ;; :on-resume fetches the signal's value when resuming, with
                  ;; deltas only if it changed since this site last handed
                  ;; them out. The continuation outlives its resumptions (an
                  ;; escalation can resume it again though its signal did not
                  ;; change), so the generation it handed out is recorded on
                  ;; the stored continuation, not kept in this closure.
                  :on-resume (fn [rctx]
                               (let [path [:track-subscriptions spin-id cont-id]
                                     consumed (or (:consumed-generation (rtp/get-state rctx path))
                                                  current-generation)
                                     [interval generation] (interval-since signal-ref consumed)]
                                 (when (> generation consumed)
                                   (rtp/swap-state! rctx [:track-subscriptions spin-id]
                                                    (fn [conts]
                                                      (if (contains? conts cont-id)
                                                        (assoc-in conts [cont-id :consumed-generation] generation)
                                                        conts))))
                                 interval))}]
        (ec/continuation-add! spin-id cont)
        (ec/deps-track-signal! spin-id signal-id)
        (log/debug :track/registered {:spin-id spin-id
                                      :signal-id signal-id
                                      :consumed-generation current-generation})))

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
      (track-signal trackable spin-id source-loc resolve reject)

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
 'org.replikativ.spindel.engine.effects/one-arg->awaitable-map
 'org.replikativ.spindel.effects.track/track-handler)
