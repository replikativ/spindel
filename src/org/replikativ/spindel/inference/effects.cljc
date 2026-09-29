(ns org.replikativ.spindel.inference.effects
  "Probabilistic programming effects: unified choose primitive.

  This provides the fundamental primitive for compositional probabilistic programming:
  - choose: Unified effect for both sampling and observation

  A choose site is a savepoint when its world handles `:inference/choose`
  (inference: `inference.smc`, `inference.trace`); otherwise it is forward
  simulation."
  (:require [org.replikativ.spindel.engine.core :as rtc]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.engine.effects :as eff]
            [org.replikativ.spindel.inference.address :as addr]
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

(defn- forward-choose-fn
  "A choose site outside inference: forward simulation. An observed site
  takes its value and scores it into the world's weight; a latent site takes
  its intervention (`intervene!`), the value a pre-populated trace holds for
  it, or a draw from its distribution. Every site is recorded in the world's
  trace."
  [_runtime args resolve _reject]
  (let [{:keys [source options source-loc]} args
        {:keys [id observe]} options
        ctx rtc/*execution-context*
        address (or id (addr/make-address ctx source-loc))]
    (if-let [intervention-value (get (rtp/get-state ctx [:inference :interventions]) address)]
      ;; Pearl's do-operator: the value is fixed, nothing is scored or traced
      (spin-core/resume resolve intervention-value)
      (let [existing (get (rtp/get-state ctx [:inference :trace]) address)
            existing-value (if (map? existing) (:value existing) existing)
            value (cond
                    ;; observe can be boolean false
                    (some? observe) observe
                    (some? existing-value) existing-value
                    :else (ar/sample* source))]
        (log/trace :choose/forward-sampling {:address address :value value
                                             :from-trace? (some? existing-value)})
        (rtp/swap-state! ctx [:inference :trace]
                         (fn [trace] (assoc (or trace {}) address
                                            {:value value
                                             :distribution source
                                             :observed? (some? observe)})))
        (when (some? observe)
          (rtp/swap-state! ctx [:inference :log-weight]
                           (fn [w] (+ (or w 0.0) (ar/observe* source observe)))))
        (spin-core/resume resolve value)))))

(defn- choose-handler-fn
  "A choose site is a savepoint when its world handles `:inference/choose`: it
  is published, and a trace policy decides and scores it (`inference.trace`).
  Otherwise it is forward simulation."
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
      (forward-choose-fn runtime args resolve reject))))

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
