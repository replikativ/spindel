(ns org.replikativ.spindel.inference.hmc
  "Hamiltonian Monte Carlo on block sites (`inference.block`), within Gibbs.

  A block supplies the gradient of its log target; the move is spindel's. The
  momentum is drawn from the site's stream, leapfrog integrates with the
  block's `:value+grad`, and the endpoint is proposed by replaying the
  computation from the block site. It is accepted on the change of the FULL
  trace log joint plus the kinetic energy, not on the block's own value:

    log α = [log p(trace') − K(p')] − [log p(trace) − K(p)]

  Leapfrog is volume preserving and reversible for any position-dependent
  force, so the move is exact whatever the block's target covers. A block
  whose target misses factors its latents affect (a downstream observe, a
  dependent site) mixes worse, and the step says so: `:incomplete-target?`
  is true when the replay changed the log probability of anything outside the
  block."
  (:require [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.inference.trace :as itrace]
            [org.replikativ.spindel.inference.block :as block]
            [org.replikativ.spindel.inference.measure :as m]
            [org.replikativ.spindel.inference.random :as random]
            [anglican.runtime :as ar]))

(defn- kinetic [p] (* 0.5 (reduce + 0.0 (map #(* % %) p))))

(defn- axpy "a·x + y" [a x y] (mapv #(+ (* a %1) %2) x y))

(defn- finite-vector? [v] (every? #(not (or (NaN? %) (infinite? %))) v))

(defn- leapfrog
  "`steps` leapfrog steps of size `eps` from (q, p) under the block's force."
  [dist q p eps steps]
  (let [grad #(second (block/value+grad dist %))]
    (loop [q q
           p (axpy (* 0.5 eps) (grad q) p)
           i 1]
      (let [q (axpy eps p q)]
        (cond
          (not (finite-vector? q)) [q p]
          (= i steps) [q (axpy (* 0.5 eps) (grad q) p)]
          :else (recur q (axpy eps (grad q) p) (inc i)))))))

(defn block-site?
  "Whether the trace entry at `address` is a block site."
  [trace address]
  (block/block-dist? (get-in trace [:trace/entries address :note :dist])))

(defn- entry-log-prob [trace address]
  (get-in trace [:trace/entries address :note :log-prob]))

(defn hmc-step
  "One HMC move of the block site at `address` of `trace`.

  Options: `:step-size`, `:steps` (leapfrog steps), `:iteration`,
  `:constraints` (the chain's conditioning, as for `mh-step`). Returns a CPS
  operation resolving {:trace :accepted? :log-ratio :incomplete-target?}."
  [trace {:keys [address step-size steps iteration constraints]
          :or {step-size 0.1 steps 10 iteration 0}}]
  (fn [resolve reject]
    (try
      (let [{q0 :value {dist :dist} :note} (get-in trace [:trace/entries address])
            _ (when-not (block/block-dist? dist)
                (throw (ex-info "HMC moves block sites only"
                                {:type ::not-a-block :address address})))
            p0 (random/in-world-stream
                (:trace/world trace) [::momentum address iteration]
                #(vec (repeatedly (count q0) (fn [] (ar/sample* (ar/normal 0.0 1.0))))))
            [q1 p1] (leapfrog dist q0 p0 step-size steps)]
        (if-not (finite-vector? q1)
          (resolve {:trace trace :accepted? false :log-ratio ##-Inf :incomplete-target? false})
          (let [move (itrace/policy
                      {:keep? true
                       :constraints constraints
                       :draw (fn [sp _]
                               (when (= address (:savepoint/address sp))
                                 {:value q1 :symmetric? true}))})]
            ((trace/replay trace address move {:anchor? itrace/anchor?})
             (fn [proposed]
               (try
                 (let [joint-delta (if (:trace/error proposed)
                                     ##-Inf
                                     (- (itrace/log-joint proposed) (itrace/log-joint trace)))
                       block-delta (- (or (entry-log-prob proposed address) ##-Inf)
                                      (entry-log-prob trace address))
                       ratio (+ joint-delta (- (kinetic p0) (kinetic p1)))
                       accept? (and (not (NaN? ratio))
                                    (or (>= ratio 0.0)
                                        (< (Math/log (random/in-world-stream
                                                      (:trace/world proposed) ::accept
                                                      m/uniform01))
                                           ratio)))]
                   (if accept?
                     (trace/release! trace proposed)
                     (trace/release! proposed trace))
                   (resolve {:trace (if accept? proposed trace)
                             :accepted? accept?
                             :log-ratio ratio
                             :incomplete-target? (and (not (infinite? joint-delta))
                                                      (> (Math/abs (- joint-delta block-delta)) 1e-9))}))
                 (catch #?(:clj Throwable :cljs :default) error
                   (reject error))))
             reject))))
      (catch #?(:clj Throwable :cljs :default) error
        (reject error)))))

(defn within-gibbs
  "A step for `inference.trace/mh-chain` (`:step`): an HMC move of every
  block site, then one single-site MH move of a latent that is not a block
  site, if there is one. `opts`: `:step-size`, `:steps`. The step counts as
  accepted when the block moves were."
  [{:keys [step-size steps] :as opts}]
  (fn [trace {:keys [iteration] :as chain-opts}]
    (fn [resolve reject]
      (let [blocks (filterv #(block-site? trace %) (itrace/latent-addresses trace))]
        (letfn [(others [t] (vec (remove #(block-site? t %) (itrace/latent-addresses t))))
                (go [t [address & more] accepted? incomplete?]
                    (if address
                      ((hmc-step t (merge chain-opts opts {:address address :iteration iteration
                                                           :step-size step-size :steps steps}))
                       (fn [r] (go (:trace r) more (or accepted? (:accepted? r))
                                   (or incomplete? (:incomplete-target? r))))
                       reject)
                      (let [done #(resolve {:trace % :accepted? accepted?
                                            :incomplete-target? incomplete?})]
                        (if (seq (others t))
                          ((itrace/mh-step t (assoc chain-opts
                                                    :select (fn [t' _]
                                                              {:targets #{(m/pick-uniformly (others t'))}
                                                               :log-selection #(- (Math/log (double (count (others %)))))})))
                           (fn [r] (done (:trace r)))
                           reject)
                          (done t)))))]
          (go trace blocks false false))))))
