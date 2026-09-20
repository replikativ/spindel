(ns org.replikativ.spindel.inference.effects
  "Probabilistic programming effects: unified choose primitive.

  This provides the fundamental primitive for compositional probabilistic programming:
  - choose: Unified effect for both sampling and observation

  The choose effect is algorithm-agnostic and works with any InferenceCoordinator
  implementation via protocol dispatch."
  (:require [org.replikativ.spindel.engine.core :as rtc]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.engine.effects :as eff]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.inference.address :as addr]
            [org.replikativ.spindel.inference.coordinator :as coord]
            [org.replikativ.spindel.effects.savepoint :as sp]
            [replikativ.logging :as log]
            [is.simm.partial-cps.async :as pcps-async]
            [anglican.runtime :as ar]))

;; =============================================================================
;; Public API Shims
;; =============================================================================

(defn choose
  "Unified primitive for probabilistic choice.

  Must only be called inside a spin; outside, this throws.

  Examples:
    ;; Sample from prior
    (choose (normal 0 1))

    ;; Observe value
    (choose (normal 0 1) :observe 1.5)

    ;; With explicit ID
    (choose (normal mu sigma) :id :my-param :observe observed)

    ;; With initial value
    (choose (normal 0 1) :init 0.5)

    ;; Counterfactual query
    (choose (normal 0 1) :where (> x 0))"
  [& _]
  (throw (ex-info "choose called outside of spin context (should be CPS-transformed)" {})))

(defn sample
  "Sample from a distribution (convenience wrapper around choose).

  Examples:
    (sample (normal 0 1))
    (sample (uniform 0 1) :id :my-param)"
  [dist & opts]
  (apply choose dist opts))

(defn observe
  "Condition on observed value (convenience wrapper around choose).

  Examples:
    (observe (normal mu sigma) observed-value)"
  [dist value & opts]
  (apply choose dist :observe value opts))

;; =============================================================================
;; Choose Effect Handler
;; =============================================================================

(defn- coordinator-choose-fn
  "Algorithm-agnostic handler for choose effect.

  This is the ONLY handler for probabilistic programming - no separate sample/observe.
  It notifies the coordinator and suspends, letting the coordinator decide values.

  Args:
    runtime: Runtime instance
    args: Map with :source, :options, :spin-id, :source-loc
    resolve: Continuation to resolve with value
    reject: Continuation to reject with error

  The coordinator receives checkpoint and decides:
  - Importance sampling: Sample or use observed value
  - SMC: Resample from prior or use observed value
  - MCMC: Use trace value or propose new value"
  [runtime args resolve reject]
  ;; Extract args from map (dispatch adds :spin-id and :source-loc)
  (let [{:keys [source options spin-id source-loc]} args
        {:keys [id observe init where tags]} options
        ctx rtc/*execution-context*
          ;; Use hash-chain addressing (unified with spin macro)
          ;; Each choose site advances the chain, ensuring deterministic addresses
        address (or id (addr/make-address ctx source-loc))
        coordinator (rtp/get-state ctx [:inference :inference-coordinator])
        particle-id (rtp/get-state ctx [:inference :particle-id])]

    (log/debug :choose/called {:address address
                               :has-observe? (some? observe)
                               :has-coordinator? (some? coordinator)})

    ;; Check for interventions (Pearl's do-operator)
    (when-let [intervention-value (get (or (rtp/get-state ctx [:inference :interventions]) {}) address)]
      (log/debug :choose/intervention {:address address :value intervention-value})
      ;; Intervention: return fixed value, don't update weight or trace
      ;; Hash-chain already advanced via make-address, no push needed
      (spin-core/resume resolve intervention-value)
      (throw (ex-info "Unreachable - spin-core/resume should not return" {})))

    ;; Detect duplicate addresses (MCMC invariant violation)
    (when-let [existing (get (or (rtp/get-state ctx [:inference :checkpoints]) {}) address)]
      (throw (ex-info "Duplicate address in choose site"
                      {:address address
                       :source-loc source-loc
                       :existing existing})))

    ;; Build the checkpoint. It is a continuation the coordinator will
    ;; resume later, possibly many times (MCMC replay), so like every
    ;; track/await continuation it carries the per-slice environment it
    ;; suspended in: bindings, addressing chain-head, dep tracking. The
    ;; chain-head is the part replay cannot do without — at this point the
    ;; cursor equals `address` itself, and reseeding it before a resume is
    ;; what makes every downstream site re-mint the SAME address it had, so
    ;; the trace stays the size of the model and a proposal lands on a live
    ;; site. `:seq` is the program-order position: checkpoints live in a
    ;; map, and map key order is not program order past eight entries.
    (let [seq-no (or (rtp/get-state ctx [:inference :checkpoint-seq]) 0)
          _ (rtp/swap-state! ctx [:inference :checkpoint-seq] (constantly (inc seq-no)))
          checkpoint {:resolve resolve
                      :reject reject
                      :address address
                      :spin-id spin-id
                      :seq seq-no
                      :slice-state (simple/capture-slice-state ctx spin-id)
                      :source source
                      :options {:observe observe
                                :init init
                                :where where
                                :tags tags}
                      :source-loc source-loc}]

      ;; DEBUG: Log checkpoint construction
      (log/debug :choose/checkpoint-created {:address address
                                             :source source
                                             :has-source? (some? source)
                                             :source-type (type source)})

      ;; Store checkpoint (PLURAL - for MCMC we keep all)
      (rtp/swap-state! ctx [:inference :checkpoints]
                       (fn [chkpts] (assoc (or chkpts {}) address checkpoint)))

      ;; Hash-chain already advanced via make-address, no push needed

      ;; If coordinator present, notify and suspend
      (if coordinator
        (do
          (log/debug :choose/notify-coordinator {:address address :particle-id particle-id})

          ;; Notify coordinator - it will call resume-particle!
          (coord/notify-checkpoint! coordinator particle-id ctx checkpoint)

          ;; Suspend execution
          spin-core/incomplete)

        ;; No coordinator: forward sampling mode
        ;; Check trace first for pre-populated values (used by PGAS scoring particles)
        (let [existing-trace (rtp/get-state ctx [:inference :trace])
              existing-entry (get existing-trace address)
              existing-value (when existing-entry
                               (if (map? existing-entry)
                                 (:value existing-entry)
                                 existing-entry))
              value (cond
                      ;; Observed value takes precedence
                      (some? observe) observe
                      ;; Use existing trace value if present
                      (some? existing-value) existing-value
                      ;; Otherwise sample fresh
                      :else (ar/sample* source))]
          (log/trace :choose/forward-sampling {:address address :value value :from-trace? (some? existing-value)})

          ;; Update trace (even if value came from trace, to ensure consistent format)
          (rtp/swap-state! ctx [:inference :trace]
                           (fn [trace] (assoc (or trace {}) address
                                              {:value value
                                               :distribution source
                                               :observed? (some? observe)})))

          ;; If observed, update weight
          ;; NOTE: Use (some? observe) not just observe, because observe can be boolean false!
          (when (some? observe)
            (let [log-prob (ar/observe* source observe)]
              (rtp/swap-state! ctx [:inference :log-weight]
                               (fn [w] (+ (or w 0.0) log-prob)))))

          ;; Continue with value
          (spin-core/resume resolve value))))))

(defn- choose-handler-fn
  "A choose site is a savepoint when its world handles `:inference/choose`: it
  is published, and a trace policy decides and scores it (`inference.trace`).
  Otherwise it speaks the coordinator protocol."
  [runtime args resolve reject]
  (let [ctx rtc/*execution-context*]
    (if (sp/handled? ctx :inference/choose)
      (let [{:keys [source options spin-id source-loc]} args
            {:keys [id observe]} options]
        (sp/publish! ctx
                     {:site :inference/choose
                      :payload {:dist source
                                :observed? (some? observe)
                                :value observe
                                :options (dissoc options :id :observe)}
                      :opts (when id {:id id})
                      :spin-id spin-id
                      :source-loc source-loc}
                     resolve reject))
      (coordinator-choose-fn runtime args resolve reject))))

;; Wrap handler function with async-effect to create PEffectHandler
(def choose-handler
  "PEffectHandler implementation for choose effect."
  (eff/async-effect choose-handler-fn))

;; =============================================================================
;; Deterministic Tracking and Interventions
;; =============================================================================

(defn track-deterministic!
  "Track deterministic intermediate value for amortized inference.

  This stores values that depend on random choices but are themselves
  deterministic computations. Useful for neural network proposals, etc.

  Example:
    (let [z (choose (normal 0 1))]
      (track-deterministic! :embedding (embed z))
      (choose (normal (embed z) 1) :observe y))"
  [address value]
  (rtp/swap-state! rtc/*execution-context* [:inference :deterministic]
                   (fn [det] (assoc (or det {}) address value)))
  value)

(defn intervene!
  "Set intervention value (Pearl's do-operator).

  This cuts the connection to parent nodes in the graphical model.
  Used for causal inference and counterfactual queries.

  Example:
    (intervene! :treatment 1.0)  ; Force treatment = 1.0
    (let [outcome (choose (normal treatment 1))]
      outcome)"
  [address value]
  (rtp/swap-state! rtc/*execution-context* [:inference :interventions]
                   (fn [int] (assoc (or int {}) address value)))
  nil)

;; =============================================================================
;; Effect Registration
;; =============================================================================

(defn choose-adapter
  "Adapter for choose effect: (choose dist & opts) -> {source, options}"
  [args]
  (let [[source & opts] args
        options (apply hash-map opts)]
    {:source source
     :options options}))

(defn sample-adapter
  "Adapter for sample effect: (sample dist & opts) -> {source, options}"
  [args]
  ;; Same as choose adapter - sample is just choose without :observe
  (let [[source & opts] args
        options (apply hash-map opts)]
    {:source source
     :options options}))

(defn observe-adapter
  "Adapter for observe effect: (observe dist value & opts) -> {source, options with :observe}"
  [args]
  ;; observe has different syntax: (observe dist value & opts)
  (let [[source value & opts] args
        options (assoc (apply hash-map opts) :observe value)]
    {:source source
     :options options}))

(defn factor
  "Multiply the weight of this execution by exp(`log-weight`): a score that is
  not the density of a value (a soft constraint, a reward, a likelihood that
  was computed elsewhere).

  Must only be called inside a spin; outside, this throws."
  [& _]
  (throw (ex-info "factor called outside of spin context (should be CPS-transformed)" {})))

(defn- factor-handler-fn
  [_runtime args resolve reject]
  (let [ctx rtc/*execution-context*
        {:keys [log-weight spin-id source-loc]} args]
    (if (sp/handled? ctx :inference/factor)
      (sp/publish! ctx {:site :inference/factor
                        :payload {:log-weight log-weight}
                        :spin-id spin-id
                        :source-loc source-loc}
                   resolve reject)
      (do (rtp/swap-state! ctx [:inference :log-weight]
                           (fn [w] (+ (or w 0.0) log-weight)))
          (spin-core/resume resolve nil)))))

(def factor-handler
  (eff/async-effect factor-handler-fn))

(defn factor-adapter [args]
  {:log-weight (first args)})

(defn register-probabilistic-effects!
  "Register probabilistic effects with spindel effect system.

  Registers choose, sample, and observe effects.
  This should be called at library initialization time."
  []
  ;; Register unified choose effect
  ;; NOTE: We use dispatched path (no 4th arg) so adapter is called
  ;; Direct handler path bypasses adapter and expects different signature
  (eff/register-effect-by-symbol!
   'org.replikativ.spindel.inference.effects/choose
   choose-handler  ; PEffectHandler instance
   'org.replikativ.spindel.inference.effects/choose-adapter)

  ;; Register sample (convenience wrapper) - same as choose
  (eff/register-effect-by-symbol!
   'org.replikativ.spindel.inference.effects/sample
   choose-handler
   'org.replikativ.spindel.inference.effects/sample-adapter)

  (eff/register-effect-by-symbol!
   'org.replikativ.spindel.inference.effects/factor
   factor-handler
   'org.replikativ.spindel.inference.effects/factor-adapter)

  ;; Register observe (different syntax: observe dist value)
  (eff/register-effect-by-symbol!
   'org.replikativ.spindel.inference.effects/observe
   choose-handler
   'org.replikativ.spindel.inference.effects/observe-adapter))

;; Auto-register on namespace load
(register-probabilistic-effects!)

;; =============================================================================
;; Resume Particle (Called by Coordinator)
;; =============================================================================

(defn resume-particle!
  "Resume particle execution from checkpoint with value.

  Called by InferenceCoordinator to provide value and resume execution.
  Updates trace and weight, then resumes continuation.

  For MCMC: Implements incremental weight updates (subtract old, add new)."
  [context checkpoint value]
  (let [{:keys [resolve reject address source options]} checkpoint
        {:keys [observe]} options]

    (log/debug :resume-particle/called {:address address :value value})

    ;; Update trace
    (let [old-value (get (or (rtp/get-state context [:inference :trace]) {}) address)]
      (rtp/swap-state! context [:inference :trace]
                       (fn [trace] (assoc (or trace {}) address value)))

      ;; Update weight incrementally for MCMC
      (when (or observe old-value)
        (let [old-log-prob (when old-value (ar/observe* source old-value))
              new-log-prob (if observe
                             (ar/observe* source observe)
                             0.0)]
          (rtp/swap-state! context [:inference :log-weight]
                           (fn [w]
                             (-> (or w 0.0)
                                 (- (or old-log-prob 0.0))  ; Subtract old contribution
                                 (+ new-log-prob)))))))     ; Add new contribution

    ;; Resume continuation with new value
    ;; CRITICAL: Set *in-trampoline* false - we're re-entering from coordinator
    (binding [pcps-async/*in-trampoline* false]
      (spin-core/resume resolve value))))
