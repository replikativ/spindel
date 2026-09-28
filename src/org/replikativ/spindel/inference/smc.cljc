(ns org.replikativ.spindel.inference.smc
  "Sequential Monte Carlo as a savepoint handler.

  The program runs once in a session. The first savepoint it reaches is
  forked into N worlds, one per particle; every sample site is decided by
  the scoring policy of `inference.trace` and recorded in its world's trace;
  every observe is scored and then PARKED — its savepoint left pending. When
  every particle is parked or has returned, the population is resampled
  (when its ESS is below the threshold, folding the log mean weight into the
  evidence): the parked savepoints of the chosen ancestors are forked into
  the next generation's worlds, the old ones are abandoned, and the new ones
  resume. A particle that returned early is carried along with its final
  weight. No coordinator, no barrier thread: the barrier is the arrival of
  the last particle.

  Worlds are forks of savepoints, so particles are frozen, coherent worlds
  (see docs/forking.md) and inherit whatever world state the program holds."
  (:require [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.inference.trace :as itrace]
            [org.replikativ.spindel.inference.measure :as m]
            [anglican.runtime :as ar]
            [replikativ.logging :as log]))

(defn- slot-of [world] (rtp/get-state world [:inference :slot]))
(defn- weight-of [world] (or (rtp/get-state world [:inference :log-weight]) 0.0))

(defn- sample-of
  "The measure's particle for a world that returned `result`."
  [world result]
  (m/sample-particle result (itrace/legacy-trace (rtp/get-state world [:savepoint/trace]))))

(defn- decide!
  "Decide `sp` under `policy` and record it in its world's trace. Returns
  the decision."
  [policy sp]
  (let [decision (policy sp nil)]
    (trace/record! (:savepoint/world sp) sp decision nil)
    decision))

(defn- all-forked
  "Fork each of `sps` (a vector) into a world; resolves the child savepoints
  in order. The forks are issued together and counted in, not chained: a
  fork may resolve inline, and a chain of a few hundred would exhaust the
  stack."
  [sps]
  (fn [resolve reject]
    (let [n (count sps)
          children (object-array n)
          remaining (atom n)
          failed? (atom false)]
      (if (zero? n)
        (resolve [])
        (dotimes [i n]
          ((sp/fork (nth sps i))
           (fn [child]
             (aset children i child)
             (when (zero? (swap! remaining dec))
               (resolve (vec children))))
           (fn [e] (when (compare-and-set! failed? false true) (reject e)))))))))

(defn- retained-policy
  "The policy of the retained particle: a sample site whose address `retained`
  holds takes that value, drawn — for the weight — with its own density as the
  proposal, so it contributes nothing to the weight; any other site is drawn
  from its prior."
  [retained]
  (itrace/policy
   {:draw (fn [sp _]
            (let [address (:savepoint/address sp)]
              (when (contains? retained address)
                (let [v (get retained address)]
                  {:value v :log-proposal (ar/observe* (:dist (:savepoint/payload sp)) v)}))))}))

(defn- stream-site?
  "A sample site whose value arrives from outside (`(sample d :stream true)`),
  see `stream`."
  [sp]
  (and (= itrace/choose-site (:savepoint/site sp))
       (:stream (:options (:savepoint/payload sp)))))

(defn- run-particles
  "The particle machinery shared by `smc` and `stream`. Starts `model` with
  `n` particles and returns `{:supply! (fn [value])}`.

  Particles run until each is parked or has returned. Parked at an observe:
  when all are, the population is resampled (see `smc`) and resumed. Parked
  at a stream site: when all particles are parked there or have returned,
  `on-idle` gets the current measure; `supply!` then scores every stream site
  with the value, which turns them into an ordinary barrier. When all have
  returned, `on-done` gets the final measure; `on-error` any failure."
  [model n {:keys [resample-threshold policy executor retained ancestor-sampling?] :as opts}
   {:keys [on-idle on-done on-error]}]
  (let [threshold (or resample-threshold 0.5)
        policy (or policy (itrace/policy))
        policy-of (if retained
                    (let [rp (retained-policy retained)]
                      (fn [slot] (if (= 0 slot) rp policy)))
                    (constantly policy))
        root (if executor
               (ctx/create-execution-context :executor executor)
               (ctx/create-execution-context))
        session (sp/open! root (merge {:purpose :smc
                                       :fork-opts {:systems :none}
                                       :retain-released? false}
                                      (dissoc opts :resample-threshold :policy :executor :retained :ancestor-sampling?)))
        ;; {:parked {slot {:sp sp :value v}}  at an observe (or a supplied stream
        ;;                                    site), resumed with v after the barrier
        ;;  :streaming {slot sp}               at a stream site, waiting for a value
        ;;  :done {slot {:sample s :log-weight w}}
        ;;  :log-z accumulated :in-barrier? :finished?}
        state (atom {:parked {} :streaming {} :done {} :log-z 0.0})
        close! (fn []
                 ((sp/close! session)
                  (fn [_] nil)
                  (fn [e] (log/warn :smc/close-failed {:error e}))))
        finish! (fn [callback outcome]
                  (when-not (:finished? (first (swap-vals! state assoc :finished? true)))
                    (callback outcome)
                    (close!)))
        fail! #(finish! on-error %)
        measure (fn [{:keys [parked streaming done log-z]}]
                  (assoc (m/empirical
                          (mapv (fn [slot]
                                  (if-let [d (get done slot)]
                                    [(:sample d) (:log-weight d)]
                                    (let [w (:savepoint/world (or (:sp (get parked slot))
                                                                  (get streaming slot)))]
                                      [(sample-of w nil) (weight-of w)])))
                                (range n)))
                         :log-normalizer log-z))]
    (letfn [(arrived! []
              ;; the last arrival claims the barrier, atomically: two particles
              ;; may arrive on two executor threads at once
              (let [[before after]
                    (swap-vals! state
                                (fn [{:keys [parked streaming done in-barrier?] :as st}]
                                  (if (and (not in-barrier?)
                                           (= n (+ (count parked) (count streaming) (count done))))
                                    (assoc st :in-barrier? true)
                                    st)))]
                (when (and (:in-barrier? after) (not (:in-barrier? before)))
                  (let [{:keys [parked streaming]} after]
                    (cond
                      (seq parked) (barrier!)
                      (seq streaming) (do (swap! state assoc :in-barrier? false)
                                          (on-idle (measure after)))
                      :else (finish! on-done (measure after)))))))

            (run-site! [sp]
              (try
                (let [slot (slot-of (:savepoint/world sp))]
                  (if (stream-site? sp)
                    (do (swap! state assoc-in [:streaming slot] sp)
                        (arrived!))
                    (let [{:keys [value]} (decide! (policy-of slot) sp)]
                      (if (:observed? (:savepoint/payload sp))
                        (do (swap! state assoc-in [:parked slot] {:sp sp :value value})
                            (arrived!))
                        (sp/resume sp value)))))
                (catch #?(:clj Throwable :cljs :default) e (fail! e))))

            (spawn! [first-sp]
              ;; the root's first savepoint becomes N particle worlds
              ((all-forked (vec (repeat n first-sp)))
               (fn [children]
                 (sp/abandon first-sp)
                 (doseq [[slot child] (map-indexed vector children)]
                   (rtp/swap-state! (:savepoint/world child) [:inference :slot] (constantly slot))
                   (run-site! child)))
               fail!))

            (barrier! []
              (if (and retained ancestor-sampling? (contains? (:parked @state) 0))
                ;; PGAS: the retained particle redraws the past it continues
                ;; from, ∝ w_i · p(retained future | particle i's past)
                (let [parked (:parked @state)
                      candidates (vec (sort (keys parked)))]
                  ((score-futures (mapv #(get parked %) candidates))
                   (fn [scores]
                     (let [combined (mapv (fn [slot score]
                                            (+ (weight-of (:savepoint/world (:sp (get parked slot)))) score))
                                          candidates scores)]
                       (resample-with! (nth candidates
                                            (m/sample-categorical (m/normalize-log-weights combined))))))
                   fail!))
                (resample-with! 0)))

            (score-futures [entries]
              ;; each parked particle's future replayed on the retained values
              ;; in a fork under a handler table of its own; its final weight
              ;; (from 0) is log p(retained latents, observations | its past)
              (fn [resolve reject]
                (let [k (count entries)
                      scores (object-array k)
                      remaining (atom k)
                      failed? (atom false)
                      scoring (itrace/policy {:constraints retained})
                      done! (fn [i score]
                              (aset scores i score)
                              (when (zero? (swap! remaining dec))
                                (resolve (vec scores))))]
                  (dotimes [i k]
                    (let [{:keys [sp value]} (nth entries i)]
                      ((sp/fork sp {:handlers
                                    {sp/any-site (fn [s] (sp/resume s (:value (decide! scoring s))))
                                     sp/result-site (fn [{w :savepoint/world}]
                                                      (let [score (weight-of w)]
                                                        (sp/release-world! session w)
                                                        (done! i score)))
                                     sp/error-site (fn [{w :savepoint/world}]
                                                     (sp/release-world! session w)
                                                     (done! i ##-Inf))
                                     sp/abandoned-site (fn [_] nil)}})
                       (fn [child]
                         (rtp/swap-state! (:savepoint/world child) [:inference :log-weight] (constantly 0.0))
                         (sp/resume child value))
                       (fn [e] (when (compare-and-set! failed? false true) (reject e)))))))))

            (resample-with! [retained-ancestor]
              (let [{:keys [parked streaming done]} @state
                    slots (vec (range n))
                    world-of (fn [slot] (:savepoint/world (or (:sp (get parked slot))
                                                              (get streaming slot))))
                    log-ws (mapv #(if-let [d (get done %)] (:log-weight d) (weight-of (world-of %)))
                                 slots)
                    weights (m/normalize-log-weights log-ws)
                    resample? (or (some? retained)
                                  (< (m/compute-ess weights) (* threshold n)))]
                (if-not resample?
                  (do (swap! state assoc :parked {} :in-barrier? false)
                      (doseq [[_ {:keys [sp value]}] (sort-by key parked)]
                        (sp/resume sp value)))
                  (let [ancestors (if retained
                                    ;; conditional: slot 0 continues from its own
                                    ;; lineage, or the past PGAS drew for it
                                    (into [retained-ancestor]
                                          (repeatedly (dec n) #(m/sample-categorical weights)))
                                    (m/systematic-resample weights n))
                        live? #(or (contains? parked %) (contains? streaming %))
                        forked-slots (filterv #(live? (nth ancestors %)) slots)
                        source (fn [a] (or (:sp (get parked a)) (get streaming a)))]
                    (swap! state update :log-z + (m/log-mean-exp log-ws))
                    ((all-forked (mapv #(source (nth ancestors %)) forked-slots))
                     (fn [children]
                       (let [carried (into {} (keep (fn [slot]
                                                      (when-let [d (get done (nth ancestors slot))]
                                                        [slot (assoc d :log-weight 0.0)])))
                                           slots)
                             placed (map (fn [slot child]
                                           (let [a (nth ancestors slot)
                                                 w (:savepoint/world child)]
                                             (rtp/swap-state! w [:inference :slot] (constantly slot))
                                             (rtp/swap-state! w [:inference :log-weight] (constantly 0.0))
                                             [slot child (get parked a)]))
                                         forked-slots children)
                             parked' (into {} (keep (fn [[slot child p]]
                                                      (when p [slot {:sp child :value (:value p)}])))
                                           placed)
                             streaming' (into {} (keep (fn [[slot child p]] (when-not p [slot child])))
                                              placed)]
                         (doseq [[_ {:keys [sp]}] parked] (sp/abandon sp))
                         (doseq [[_ s] streaming] (sp/abandon s))
                         (swap! state assoc :parked {} :streaming streaming' :done carried
                                :in-barrier? false)
                         (if (empty? parked')
                           (arrived!)
                           (doseq [[_ {:keys [sp value]}] (sort-by key parked')]
                             (sp/resume sp value)))))
                     fail!)))))

            (supply! [value]
              ;; every particle waiting at a stream site scores `value` there;
              ;; that is an ordinary barrier from here on
              (try
                (let [{:keys [streaming]} @state
                      parked (into {} (map (fn [[slot sp]]
                                             (let [policy (itrace/policy
                                                           {:constraints {(:savepoint/address sp) value}})]
                                               (decide! policy sp)
                                               [slot {:sp sp :value value}])))
                                   streaming)]
                  (swap! state assoc :streaming {} :parked parked)
                  (arrived!))
                (catch #?(:clj Throwable :cljs :default) e (fail! e))))]
      (try
        (sp/install-handlers!
         root
         {sp/any-site
          (fn [s]
            (if (nil? (slot-of (:savepoint/world s)))
              (spawn! s)
              (run-site! s)))
          sp/result-site
          (fn [{world :savepoint/world result :savepoint/payload}]
            (if-let [slot (slot-of world)]
              (do (swap! state assoc-in [:done slot] {:sample (sample-of world result)
                                                      :log-weight (weight-of world)})
                  ;; the Sample holds what the measure needs; give the world
                  ;; back now instead of holding every finished particle until
                  ;; the session closes
                  (sp/release-world! session world)
                  (arrived!))
              ;; a program without savepoints: one deterministic particle
              (finish! on-done (m/empirical (vec (repeat n [(sample-of world result) 0.0]))))))
          sp/error-site
          (fn [{error :savepoint/payload}] (fail! error))
          sp/abandoned-site (fn [_] nil)})
        (sp/start! session model)
        (catch #?(:clj Throwable :cljs :default) e
          (log/error :smc/start-failed {:error e})
          (fail! e)))
      {:supply! supply! :close! close!})))

(defn smc
  "Run `model` (a spin) with `n` particles. Options: `:resample-threshold`
  (ESS fraction, default 0.5), `:policy` (an `inference.trace/policy`,
  default the prior with no options), `:executor` for the root world, and
  session options (`effects.savepoint/open!`).

  `:retained` {address value} makes it CONDITIONAL SMC (particle Gibbs):
  particle 0 follows those choices, every barrier resamples, and particle 0
  keeps its own lineage while the other n−1 draw their ancestors. With
  `:ancestor-sampling? true` particle 0 instead redraws its ancestor at every
  barrier, ∝ w_i · p(retained future | particle i's past), the future scored
  by replaying each particle in a fork on the retained values (PGAS).

  Resolves an `EmpiricalMeasure` of `Sample`s (result + trace) whose
  `log-marginal` is the SMC evidence estimate. A model with stream sites
  runs with `stream` instead."
  [model n & [opts]]
  (fn [resolve reject]
    (let [[resolve reject] (sp/in-callers-world resolve reject)]
      (run-particles model n opts
                     {:on-done resolve
                      :on-error reject
                      :on-idle (fn [_]
                                 (reject (ex-info "The model has stream sites; run it with smc/stream"
                                                  {:type ::stream-sites})))}))))

(defn stream
  "Online SMC: `model` marks the sites whose values arrive from outside as
  stream sites — `(sample (normal x 1) :id [:y t] :stream true)` — and
  particles run until each waits at its next one. Resolves a step

    {:measure  the posterior over the trajectories so far
     :push     (fn [y]) -> CPS resolving the next step, after every particle
               scored y at its stream site, the population was resampled as
               needed, and each ran on to its next stream site (or returned)
     :done?    true once every particle has returned (no :push then)
     :close    (fn []) giving the worlds back}

  Each push costs the particles' work up to their next stream site; nothing
  already seen is re-run. `opts` as for `smc`."
  [model n & [opts]]
  (fn [resolve reject]
    (let [waiting (atom (sp/in-callers-world resolve reject))
          controller (atom nil)
          step (fn [done? m]
                 (let [[res _] @waiting]
                   (res (cond-> {:measure m :done? done?
                                 :close (fn [] ((:close! @controller)))}
                          (not done?)
                          (assoc :push (fn [y]
                                         (fn [res' rej']
                                           (reset! waiting (sp/in-callers-world res' rej'))
                                           ((:supply! @controller) y))))))))]
      (reset! controller
              (run-particles model n opts
                             {:on-idle #(step false %)
                              :on-done #(step true %)
                              :on-error (fn [e] ((second @waiting) e))})))))

;; =============================================================================
;; Particle MCMC on savepoint SMC
;; =============================================================================

(defn- normalized
  "A measure's particles with their weights normalized to sum to one."
  [measure]
  (let [ps (m/get-particles measure)
        lse (m/log-sum-exp (mapv second ps))]
    (mapv (fn [[s lw]] [s (- lw lse)]) ps)))

(defn retained-choices
  "{address value} of the unobserved sample sites of `trace` (a Sample's):
  the `:retained` of a conditional sweep that keeps that trajectory."
  [trace]
  (into {} (keep (fn [[a e]] (when-not (:observed? e) [a (:value e)]))) trace))

(defn- choices-of [sample] (retained-choices (m/get-trace sample)))

(defn- sweeps
  "Run `step` — (fn [state]) -> CPS resolving [state' samples] — `k` times,
  pooling the samples. Resolves an EmpiricalMeasure."
  [k init step]
  (fn [resolve reject]
    (letfn [(go [i state acc]
                (if (= i k)
                  (resolve (m/empirical acc))
                  ((step state)
                   (fn [[state' samples]] (go (inc i) state' (into acc samples)))
                   reject)))]
      (go 0 init []))))

(defn pgibbs
  "Particle Gibbs (Andrieu et al. 2010) as iterated conditional SMC: each
  sweep keeps the trajectory drawn from the previous one, and every sweep's
  particles are pooled, normalized per sweep. `opts` as for `smc`."
  [model n iterations & [opts]]
  (fn [resolve reject]
    ((smc model n opts)
     (fn [initial]
       (let [pick (fn [measure]
                    (let [ps (m/get-particles measure)]
                      (choices-of (first (nth ps (m/sample-categorical
                                                  (m/normalize-log-weights (mapv second ps))))))))]
         ((sweeps iterations (pick initial)
                  (fn [retained]
                    (fn [res rej]
                      ((smc model n (assoc opts :retained retained))
                       (fn [sweep] (res [(pick sweep) (normalized sweep)]))
                       rej))))
          resolve reject)))
     reject)))

(defn pgas
  "Particle Gibbs with ancestor sampling (Lindsten et al. 2014): `pgibbs`
  whose retained particle redraws its ancestor at every barrier. Improves
  mixing where plain particle Gibbs degenerates; costs a replay of the
  retained future per parked particle per barrier."
  [model n iterations & [opts]]
  (pgibbs model n iterations (assoc opts :ancestor-sampling? true)))

(defn pimh
  "Particle independent Metropolis-Hastings: each iteration proposes a fresh
  SMC sweep and accepts it on the ratio of evidence estimates; the current
  sweep's particles, normalized, are emitted every iteration. `opts` as for
  `smc`."
  [model n iterations & [opts]]
  (fn [resolve reject]
    ((smc model n opts)
     (fn [initial]
       ((sweeps iterations [(normalized initial) (m/log-marginal initial)]
                (fn [[current log-z]]
                  (fn [res rej]
                    ((smc model n opts)
                     (fn [proposed]
                       (let [log-z' (m/log-marginal proposed)
                             ratio (- log-z' log-z)
                             accept? (or (>= ratio 0.0) (< (Math/log (m/uniform01)) ratio))
                             state' (if accept? [(normalized proposed) log-z'] [current log-z])]
                         (res [state' (first state')])))
                     rej))))
        resolve reject))
     reject)))
