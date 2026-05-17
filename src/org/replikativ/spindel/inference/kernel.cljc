(ns org.replikativ.spindel.inference.kernel
  "Kernel abstraction for compositional inference.

  Kernels are measure-preserving transformations that form the building
  blocks of inference algorithms. Sequential composition of kernels
  implements complex inference strategies like SMC.

  This namespace also defines PInferenceKernel - kernels that operate
  at checkpoints during execution (not post-processing on measures).
  See KERNEL_INFERENCE_DESIGN.md for the full architecture."
  (:require [org.replikativ.spindel.inference.measure :as m]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [replikativ.logging :as log]
            [anglican.runtime :as ar]))

;; =============================================================================
;; PKernel Protocol
;; =============================================================================

(defprotocol PKernel
  "Protocol for measure-preserving kernels.

  Kernels transform measures while (ideally) preserving the target distribution.
  Different kernels implement different inference operations:
  - ImportanceKernel: Forward execution with weight updates
  - ResampleKernel: Low-variance resampling
  - MCMCKernel: Metropolis-Hastings proposals
  - (Future) RejuvenateKernel: MCMC moves between resampling"

  (apply-kernel [this measure]
    "Apply this kernel to a measure, returning a new measure.

    This is the core operation for inference composition.
    Kernels should be stateless - all state lives in measures."))

;; =============================================================================
;; Kernel Composition
;; =============================================================================

(defn compose-kernels
  "Sequentially compose kernels: (k3 . k2 . k1)(measure).

  Returns a new kernel that applies kernels left-to-right."
  [& kernels]
  (reify PKernel
    (apply-kernel [_ measure]
      (reduce (fn [m kernel]
                (apply-kernel kernel m))
              measure
              kernels))))

(defn conditional-kernel
  "Apply kernel only if predicate on measure returns true.

  pred: (fn [measure] -> boolean)
  If pred returns false, returns measure unchanged."
  [pred kernel]
  (reify PKernel
    (apply-kernel [_ measure]
      (if (pred measure)
        (apply-kernel kernel measure)
        measure))))

;; =============================================================================
;; ImportanceKernel - Forward Execution with Weighting
;; =============================================================================

(defrecord ImportanceKernel [exec-fn]
  PKernel

  (apply-kernel [_ measure]
    (case (m/measure-type measure)
      :dirac
      (let [context (:context measure)
            new-context (exec-fn context)]
        (m/dirac new-context))

      :empirical
      (let [new-particles
            (mapv (fn [[ctx log-weight]]
                    (let [new-ctx (exec-fn ctx)
                          new-log-weight (get-in new-ctx [:inference :log-weight] 0.0)]
                      [new-ctx new-log-weight]))
                  (:particles measure))]
        (m/empirical new-particles)))))

(defn importance-kernel
  "Create importance sampling kernel with execution function."
  [exec-fn]
  (->ImportanceKernel exec-fn))

;; =============================================================================
;; ResampleKernel - Particle Resampling
;; =============================================================================

(defrecord ResampleKernel [threshold]
  PKernel

  (apply-kernel [_ measure]
    (case (m/measure-type measure)
      :dirac
      measure

      :empirical
      (m/resample-if-needed measure threshold))))

(defn resample-kernel
  "Create resampling kernel with ESS threshold."
  [threshold]
  {:pre [(and (> threshold 0) (<= threshold 1))]}
  (->ResampleKernel threshold))

;; =============================================================================
;; MCMCKernel - Metropolis-Hastings Proposals
;; =============================================================================

(defn mh-chain
  "Run Metropolis-Hastings chain for steps iterations."
  [proposal-fn context steps]
  (loop [current-ctx context
         step 0]
    (if (>= step steps)
      current-ctx
      (let [proposed-ctx (proposal-fn current-ctx)
            current-log-weight (get-in current-ctx [:inference :log-weight] 0.0)
            proposed-log-weight (get-in proposed-ctx [:inference :log-weight] 0.0)
            log-accept-ratio (- proposed-log-weight current-log-weight)
            accept? (or (>= log-accept-ratio 0)
                       (< (Math/log (rand)) log-accept-ratio))]
        (log/trace :mcmc/mh-step {:step step
                            :accept? accept?
                            :log-accept-ratio log-accept-ratio})
        (recur (if accept? proposed-ctx current-ctx)
               (inc step))))))

(defrecord MCMCKernel [proposal-fn steps]
  PKernel

  (apply-kernel [_ measure]
    (case (m/measure-type measure)
      :dirac
      (let [context (:context measure)
            new-context (mh-chain proposal-fn context steps)]
        (m/dirac new-context))

      :empirical
      (let [new-particles
            (mapv (fn [[ctx log-weight]]
                    (let [new-ctx (mh-chain proposal-fn ctx steps)
                          new-log-weight (get-in new-ctx [:inference :log-weight] 0.0)]
                      [new-ctx new-log-weight]))
                  (:particles measure))]
        (m/empirical new-particles)))))

(defn mcmc-kernel
  "Create MCMC kernel with proposal function."
  [proposal-fn steps]
  {:pre [(> steps 0)]}
  (->MCMCKernel proposal-fn steps))

;; =============================================================================
;; Conditional Resample Kernel (Common Pattern)
;; =============================================================================

(defn conditional-resample
  "Resample kernel that only triggers when ESS is low."
  [threshold]
  (conditional-kernel
   (fn [measure]
     (and (= :empirical (m/measure-type measure))
          (let [n (count (:particles measure))
                ess (m/effective-sample-size measure)]
            (< ess (* threshold n)))))
   (resample-kernel threshold)))

;; =============================================================================
;; Utility Kernels
;; =============================================================================

(defn map-contexts
  "Create kernel that maps function over contexts."
  [f]
  (reify PKernel
    (apply-kernel [_ measure]
      (case (m/measure-type measure)
        :dirac
        (m/dirac (f (:context measure)))

        :empirical
        (let [new-particles
              (mapv (fn [[ctx log-weight]]
                      [(f ctx) log-weight])
                    (:particles measure))]
          (m/empirical new-particles))))))

(defn reset-weights
  "Create kernel that resets all log-weights to 0."
  []
  (map-contexts
   (fn [ctx]
     (assoc-in ctx [:inference :log-weight] 0.0))))

(defn filter-particles
  "Create kernel that filters particles by predicate."
  [pred]
  (reify PKernel
    (apply-kernel [_ measure]
      (case (m/measure-type measure)
        :dirac
        (if (pred (:context measure))
          measure
          (throw (ex-info "Dirac measure filtered out" {})))

        :empirical
        (let [filtered (filterv (fn [[ctx _]] (pred ctx))
                               (:particles measure))]
          (when (empty? filtered)
            (throw (ex-info "All particles filtered out" {})))
          (m/empirical filtered))))))

;; =============================================================================
;; InferenceKernel Protocol - Checkpoint-Level Inference Control
;; =============================================================================

(defprotocol PInferenceKernel
  "Protocol for kernels that operate at checkpoints during program execution.

  Unlike PKernel (which transforms measures post-hoc), PInferenceKernel
  controls execution at each random variable/observation point:

  - Decides what value to assign at the current checkpoint
  - Can modify previously assigned values (triggering re-execution)
  - Controls iteration after program completes"

  (kernel-id [this]
    "Unique identifier for this kernel type (e.g., :prior, :single-site-mh).")

  (step [this ctx checkpoint trace]
    "Process a checkpoint with the current trace.

    Returns one of:
      {:action :assign, :value v}
      {:action :modify, :updates {addr new-value, ...}}
      {:action :assign-and-modify, :value v, :updates {addr new-value, ...}}")

  (on-complete [this ctx trace result]
    "Called when program execution completes.

    Returns one of:
      {:action :done, :trace trace, :result result, :log-weight w}
      {:action :iterate, :updates {addr new-value, ...}}"))

;; =============================================================================
;; PriorKernel - Simple Forward Sampling (Importance Sampling)
;; =============================================================================

(defrecord PriorKernel []
  PInferenceKernel

  (kernel-id [_] :prior)

  (step [_ ctx checkpoint trace]
    (let [{:keys [source options]} checkpoint
          {:keys [observe init]} options
          value (cond
                  (some? observe) observe
                  (some? init) init
                  :else (ar/sample* source))]
      {:action :assign, :value value}))

  (on-complete [_ ctx trace result]
    {:action :done
     :trace trace
     :result result
     :log-weight (or (rtp/get-state ctx [:inference :log-weight]) 0.0)}))

(defn prior-kernel
  "Create a PriorKernel for simple importance sampling."
  []
  (->PriorKernel))

;; =============================================================================
;; SingleSiteMHKernel - Lightweight Metropolis-Hastings
;; =============================================================================

(defn- get-mcmc-state
  [ctx]
  (or (rtp/get-state ctx [:inference :mcmc])
      {:completed-iterations 0
       :accepted-trace nil
       :accepted-log-weight 0.0
       :accepted-result nil
       :pending-proposal? false}))

(defn- set-mcmc-state!
  [ctx state]
  (rtp/swap-state! ctx [:inference :mcmc] (constantly state)))

(defrecord SingleSiteMHKernel [num-iterations]
  PInferenceKernel

  (kernel-id [_] :single-site-mh)

  (step [_this ctx checkpoint trace]
    (let [{:keys [source options address]} checkpoint
          {:keys [observe init]} options]
      (cond
        (some? observe)
        {:action :assign, :value observe}

        (not (contains? trace address))
        {:action :assign, :value (if (some? init) init (ar/sample* source))}

        :else
        {:action :assign, :value (get-in trace [address :value])})))

  (on-complete [_this ctx trace result]
    (let [current-log-weight (or (rtp/get-state ctx [:inference :log-weight]) 0.0)
          mcmc-state (get-mcmc-state ctx)
          {:keys [completed-iterations accepted-trace accepted-log-weight
                  accepted-result pending-proposal?]} mcmc-state]

      (cond
        ;; First run - establish baseline
        (nil? accepted-trace)
        (let [new-state {:completed-iterations 0
                         :accepted-trace trace
                         :accepted-log-weight current-log-weight
                         :accepted-result result
                         :pending-proposal? false}]

          (log/debug :mh/first-run {:log-weight current-log-weight
                              :trace-size (count trace)})

          (if (>= 0 num-iterations)
            (do
              (set-mcmc-state! ctx new-state)
              {:action :done
               :trace trace
               :result result
               :log-weight current-log-weight})

            (let [sample-addrs (vec (keys (filter (fn [[_ entry]] (not (:observed? entry))) trace)))]
              (if (empty? sample-addrs)
                (do
                  (set-mcmc-state! ctx new-state)
                  {:action :done
                   :trace trace
                   :result result
                   :log-weight current-log-weight})

                (let [addr (rand-nth sample-addrs)
                      entry (get trace addr)
                      proposed (ar/sample* (:distribution entry))]

                  (set-mcmc-state! ctx (assoc new-state :pending-proposal? true))

                  (log/debug :mh/propose {:iteration 0
                                      :addr addr
                                      :old-value (:value entry)
                                      :proposed proposed})
                  {:action :iterate
                   :updates {addr proposed}})))))

        ;; Evaluating a proposal
        pending-proposal?
        (let [log-accept-ratio (- current-log-weight accepted-log-weight)
              u (Math/log (rand))
              accept? (or (>= log-accept-ratio 0)
                         (< u log-accept-ratio))
              new-completed (inc completed-iterations)

              new-accepted-trace (if accept? trace accepted-trace)
              new-accepted-log-weight (if accept? current-log-weight accepted-log-weight)
              new-accepted-result (if accept? result accepted-result)]

          (log/debug :mh/acceptance {:iteration completed-iterations
                              :log-accept-ratio log-accept-ratio
                              :accept? accept?
                              :current-log-weight current-log-weight
                              :accepted-log-weight accepted-log-weight})

          (if (>= new-completed num-iterations)
            (do
              (set-mcmc-state! ctx {:completed-iterations new-completed
                                    :accepted-trace new-accepted-trace
                                    :accepted-log-weight new-accepted-log-weight
                                    :accepted-result new-accepted-result
                                    :pending-proposal? false})
              {:action :done
               :trace new-accepted-trace
               :result new-accepted-result
               :log-weight new-accepted-log-weight})

            (let [sample-addrs (vec (keys (filter (fn [[_ entry]] (not (:observed? entry))) new-accepted-trace)))
                  addr (rand-nth sample-addrs)
                  entry (get new-accepted-trace addr)
                  proposed (ar/sample* (:distribution entry))]

              (set-mcmc-state! ctx {:completed-iterations new-completed
                                    :accepted-trace new-accepted-trace
                                    :accepted-log-weight new-accepted-log-weight
                                    :accepted-result new-accepted-result
                                    :pending-proposal? true})

              (log/debug :mh/propose {:iteration new-completed
                                  :addr addr
                                  :old-value (:value entry)
                                  :proposed proposed})

              {:action :iterate
               :updates {addr proposed}})))

        :else
        (throw (ex-info "Unexpected on-complete state in SingleSiteMHKernel"
                        {:trace trace
                         :mcmc-state mcmc-state}))))))

(defn single-site-mh-kernel
  "Create SingleSiteMHKernel for lightweight Metropolis-Hastings."
  [num-iterations]
  {:pre [(pos-int? num-iterations)]}
  (->SingleSiteMHKernel num-iterations))

;; =============================================================================
;; RandomWalkMHKernel
;; =============================================================================

(defn- get-rw-mcmc-state
  [ctx]
  (or (rtp/get-state ctx [:inference :rw-mcmc])
      {:completed-iterations 0
       :accepted-trace nil
       :accepted-log-weight 0.0
       :accepted-result nil
       :pending-proposal? false
       :acceptance-count 0}))

(defn- set-rw-mcmc-state!
  [ctx state]
  (rtp/swap-state! ctx [:inference :rw-mcmc] (constantly state)))

(defn- continuous-sample-addrs
  [trace]
  (vec (keys (filter (fn [[_ entry]]
                       (and (not (:observed? entry))
                            true))
                     trace))))

(defn- random-walk-propose
  [current-value step-size]
  (+ current-value (* step-size (ar/sample* (ar/normal 0 1)))))

(defrecord RandomWalkMHKernel [num-iterations step-size]
  PInferenceKernel

  (kernel-id [_] :random-walk-mh)

  (step [_this ctx checkpoint trace]
    (let [{:keys [source options address]} checkpoint
          {:keys [observe init]} options]
      (cond
        (some? observe)
        {:action :assign, :value observe}

        (not (contains? trace address))
        {:action :assign, :value (if (some? init) init (ar/sample* source))}

        :else
        {:action :assign, :value (get-in trace [address :value])})))

  (on-complete [_this ctx trace result]
    (let [current-log-weight (or (rtp/get-state ctx [:inference :log-weight]) 0.0)
          mcmc-state (get-rw-mcmc-state ctx)
          {:keys [completed-iterations accepted-trace accepted-log-weight
                  accepted-result pending-proposal? acceptance-count]} mcmc-state]

      (cond
        (nil? accepted-trace)
        (let [new-state {:completed-iterations 0
                         :accepted-trace trace
                         :accepted-log-weight current-log-weight
                         :accepted-result result
                         :pending-proposal? false
                         :acceptance-count 0}]

          (log/debug :rw-mh/first-run {:log-weight current-log-weight
                              :trace-size (count trace)})

          (if (>= 0 num-iterations)
            (do
              (set-rw-mcmc-state! ctx new-state)
              {:action :done
               :trace trace
               :result result
               :log-weight current-log-weight})

            (let [sample-addrs (continuous-sample-addrs trace)]
              (if (empty? sample-addrs)
                (do
                  (set-rw-mcmc-state! ctx new-state)
                  {:action :done
                   :trace trace
                   :result result
                   :log-weight current-log-weight})

                (let [addr (rand-nth sample-addrs)
                      entry (get trace addr)
                      current-value (:value entry)
                      proposed (random-walk-propose current-value step-size)]

                  (set-rw-mcmc-state! ctx (assoc new-state :pending-proposal? true))

                  (log/debug :rw-mh/propose {:iteration 0
                                      :addr addr
                                      :current-value current-value
                                      :proposed proposed
                                      :step-size step-size})
                  {:action :iterate
                   :updates {addr proposed}})))))

        pending-proposal?
        (let [log-accept-ratio (- current-log-weight accepted-log-weight)
              u (Math/log (rand))
              accept? (or (>= log-accept-ratio 0)
                         (< u log-accept-ratio))
              new-completed (inc completed-iterations)
              new-acceptance-count (if accept? (inc acceptance-count) acceptance-count)

              new-accepted-trace (if accept? trace accepted-trace)
              new-accepted-log-weight (if accept? current-log-weight accepted-log-weight)
              new-accepted-result (if accept? result accepted-result)]

          (log/debug :rw-mh/acceptance {:iteration completed-iterations
                              :log-accept-ratio log-accept-ratio
                              :accept? accept?
                              :acceptance-rate (/ new-acceptance-count new-completed)})

          (if (>= new-completed num-iterations)
            (do
              (set-rw-mcmc-state! ctx {:completed-iterations new-completed
                                       :accepted-trace new-accepted-trace
                                       :accepted-log-weight new-accepted-log-weight
                                       :accepted-result new-accepted-result
                                       :pending-proposal? false
                                       :acceptance-count new-acceptance-count})
              (log/debug :rw-mh/complete {:total-iterations new-completed
                                  :acceptance-rate (/ new-acceptance-count new-completed)})
              {:action :done
               :trace new-accepted-trace
               :result new-accepted-result
               :log-weight new-accepted-log-weight})

            (let [sample-addrs (continuous-sample-addrs new-accepted-trace)
                  addr (rand-nth sample-addrs)
                  entry (get new-accepted-trace addr)
                  current-value (:value entry)
                  proposed (random-walk-propose current-value step-size)]

              (set-rw-mcmc-state! ctx {:completed-iterations new-completed
                                       :accepted-trace new-accepted-trace
                                       :accepted-log-weight new-accepted-log-weight
                                       :accepted-result new-accepted-result
                                       :pending-proposal? true
                                       :acceptance-count new-acceptance-count})

              (log/debug :rw-mh/propose {:iteration new-completed
                                  :addr addr
                                  :current-value current-value
                                  :proposed proposed})

              {:action :iterate
               :updates {addr proposed}})))

        :else
        (throw (ex-info "Unexpected on-complete state in RandomWalkMHKernel"
                        {:trace trace
                         :mcmc-state mcmc-state}))))))

(defn random-walk-mh-kernel
  "Create RandomWalkMHKernel for continuous variables."
  [num-iterations & [{:keys [step-size] :or {step-size 0.1}}]]
  {:pre [(pos-int? num-iterations) (pos? step-size)]}
  (->RandomWalkMHKernel num-iterations step-size))

;; =============================================================================
;; BlockGibbsKernel
;; =============================================================================

(defprotocol PBlockSelector
  "Protocol for selecting which block to update at each iteration."
  (select-block [this trace iteration]
    "Returns block-id (keyword) for which block to update this iteration."))

(defprotocol PBlockKernel
  "Protocol for block-level proposal kernels."
  (propose-block [this trace block-addresses]
    "Returns {addr -> proposed-value} for addresses in this block."))

(defrecord RoundRobinSelector [block-ids]
  PBlockSelector
  (select-block [_ _trace iteration]
    (nth block-ids (mod iteration (count block-ids)))))

(defn round-robin-selector
  [block-ids]
  {:pre [(seq block-ids) (every? keyword? block-ids)]}
  (->RoundRobinSelector (vec block-ids)))

(defrecord RandomSelector [block-ids]
  PBlockSelector
  (select-block [_ _trace _iteration]
    (rand-nth block-ids)))

(defn random-selector
  [block-ids]
  {:pre [(seq block-ids) (every? keyword? block-ids)]}
  (->RandomSelector (vec block-ids)))

(defrecord PriorBlockKernel []
  PBlockKernel
  (propose-block [_ trace block-addresses]
    (into {}
          (map (fn [addr]
                 (let [entry (get trace addr)
                       dist (:distribution entry)]
                   [addr (ar/sample* dist)]))
               block-addresses))))

(defn prior-block-kernel [] (->PriorBlockKernel))

(defrecord RandomWalkBlockKernel [step-size]
  PBlockKernel
  (propose-block [_ trace block-addresses]
    (into {}
          (map (fn [addr]
                 (let [entry (get trace addr)
                       current (:value entry)
                       proposed (random-walk-propose current step-size)]
                   [addr proposed]))
               block-addresses))))

(defn random-walk-block-kernel
  [& [{:keys [step-size] :or {step-size 0.1}}]]
  {:pre [(pos? step-size)]}
  (->RandomWalkBlockKernel step-size))

(defn- get-block-gibbs-state
  [ctx]
  (or (rtp/get-state ctx [:inference :block-gibbs])
      {:completed-iterations 0
       :accepted-trace nil
       :accepted-log-weight 0.0
       :accepted-result nil
       :pending-proposal? false
       :current-block nil}))

(defn- set-block-gibbs-state!
  [ctx state]
  (rtp/swap-state! ctx [:inference :block-gibbs] (constantly state)))

(defrecord BlockGibbsKernel
  [num-iterations block-selector block-kernels address-classifier]

  PInferenceKernel

  (kernel-id [_] :block-gibbs)

  (step [_this ctx checkpoint trace]
    (let [{:keys [source options address]} checkpoint
          {:keys [observe init]} options]
      (cond
        (some? observe)
        {:action :assign, :value observe}

        (not (contains? trace address))
        {:action :assign, :value (if (some? init) init (ar/sample* source))}

        :else
        {:action :assign, :value (get-in trace [address :value])})))

  (on-complete [_this ctx trace result]
    (let [current-log-weight (or (rtp/get-state ctx [:inference :log-weight]) 0.0)
          state (get-block-gibbs-state ctx)
          {:keys [completed-iterations accepted-trace accepted-log-weight
                  accepted-result pending-proposal? current-block]} state

          classify-trace (fn [trace]
                           (reduce-kv
                             (fn [acc addr entry]
                               (if-let [block-id (address-classifier addr entry)]
                                 (update acc block-id (fnil conj #{}) addr)
                                 acc))
                             {}
                             trace))]

      (cond
        (nil? accepted-trace)
        (let [new-state {:completed-iterations 0
                         :accepted-trace trace
                         :accepted-log-weight current-log-weight
                         :accepted-result result
                         :pending-proposal? false
                         :current-block nil}]

          (log/debug :block-gibbs/first-run {:log-weight current-log-weight
                              :trace-size (count trace)})

          (if (>= 0 num-iterations)
            (do
              (set-block-gibbs-state! ctx new-state)
              {:action :done
               :trace trace
               :result result
               :log-weight current-log-weight})

            (let [block-map (classify-trace trace)
                  block-id (select-block block-selector trace 0)
                  block-addrs (get block-map block-id #{})
                  block-kernel (get block-kernels block-id)]

              (if (or (empty? block-addrs) (nil? block-kernel))
                (do
                  (log/debug :block-gibbs/skip-block {:block-id block-id
                                      :reason (if (empty? block-addrs)
                                                :no-addresses
                                                :no-kernel)})
                  (set-block-gibbs-state! ctx new-state)
                  {:action :done
                   :trace trace
                   :result result
                   :log-weight current-log-weight})

                (let [proposals (propose-block block-kernel trace block-addrs)]
                  (set-block-gibbs-state! ctx (assoc new-state
                                                     :pending-proposal? true
                                                     :current-block block-id))
                  (log/debug :block-gibbs/propose {:iteration 0
                                      :block-id block-id
                                      :num-proposals (count proposals)})
                  {:action :iterate
                   :updates proposals})))))

        pending-proposal?
        (let [log-accept-ratio (- current-log-weight accepted-log-weight)
              u (Math/log (rand))
              accept? (or (>= log-accept-ratio 0)
                         (< u log-accept-ratio))
              new-completed (inc completed-iterations)

              new-accepted-trace (if accept? trace accepted-trace)
              new-accepted-log-weight (if accept? current-log-weight accepted-log-weight)
              new-accepted-result (if accept? result accepted-result)]

          (log/debug :block-gibbs/acceptance {:iteration completed-iterations
                              :block-id current-block
                              :log-accept-ratio log-accept-ratio
                              :accept? accept?})

          (if (>= new-completed num-iterations)
            (do
              (set-block-gibbs-state! ctx {:completed-iterations new-completed
                                           :accepted-trace new-accepted-trace
                                           :accepted-log-weight new-accepted-log-weight
                                           :accepted-result new-accepted-result
                                           :pending-proposal? false
                                           :current-block nil})
              {:action :done
               :trace new-accepted-trace
               :result new-accepted-result
               :log-weight new-accepted-log-weight})

            (let [block-map (classify-trace new-accepted-trace)
                  block-id (select-block block-selector new-accepted-trace new-completed)
                  block-addrs (get block-map block-id #{})
                  block-kernel (get block-kernels block-id)]

              (if (or (empty? block-addrs) (nil? block-kernel))
                (do
                  (log/debug :block-gibbs/skip-block {:block-id block-id})
                  (set-block-gibbs-state! ctx {:completed-iterations new-completed
                                               :accepted-trace new-accepted-trace
                                               :accepted-log-weight new-accepted-log-weight
                                               :accepted-result new-accepted-result
                                               :pending-proposal? false
                                               :current-block nil})
                  {:action :done
                   :trace new-accepted-trace
                   :result new-accepted-result
                   :log-weight new-accepted-log-weight})

                (let [proposals (propose-block block-kernel new-accepted-trace block-addrs)]
                  (set-block-gibbs-state! ctx {:completed-iterations new-completed
                                               :accepted-trace new-accepted-trace
                                               :accepted-log-weight new-accepted-log-weight
                                               :accepted-result new-accepted-result
                                               :pending-proposal? true
                                               :current-block block-id})

                  (log/debug :block-gibbs/propose {:iteration new-completed
                                      :block-id block-id
                                      :num-proposals (count proposals)})
                  {:action :iterate
                   :updates proposals})))))

        :else
        (throw (ex-info "Unexpected on-complete state in BlockGibbsKernel"
                        {:trace trace
                         :state state}))))))

(defn block-gibbs-kernel
  "Create a BlockGibbsKernel for block Gibbs sampling."
  [num-iterations block-selector block-kernels address-classifier]
  {:pre [(pos-int? num-iterations)
         (satisfies? PBlockSelector block-selector)
         (map? block-kernels)
         (fn? address-classifier)]}
  (->BlockGibbsKernel num-iterations block-selector block-kernels address-classifier))
