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

(defn smc
  "Run `model` (a spin) with `n` particles. Options: `:resample-threshold`
  (ESS fraction, default 0.5), `:policy` (an `inference.trace/policy`,
  default the prior with no options), `:executor` for the root world, and
  session options (`effects.savepoint/open!`).

  Resolves an `EmpiricalMeasure` of `Sample`s (result + trace) whose
  `log-marginal` is the SMC evidence estimate."
  [model n & [{:keys [resample-threshold policy executor] :as opts}]]
  (let [threshold (or resample-threshold 0.5)
        policy (or policy (itrace/policy))]
    (fn [resolve reject]
      (let [root (if executor
                   (ctx/create-execution-context :executor executor)
                   (ctx/create-execution-context))
            session (sp/open! root (merge {:purpose :smc
                                           :fork-opts {:systems :none}
                                           :retain-released? false}
                                          (dissoc opts :resample-threshold :policy :executor)))
            ;; {:waiting {slot sp} :done {slot {:sample s :log-weight w}}
            ;;  :log-z accumulated :spawned? bool :finished? bool}
            state (atom {:waiting {} :done {} :log-z 0.0})
            finish! (fn [outcome deliver]
                      (when-not (:finished? (first (swap-vals! state assoc :finished? true)))
                        (deliver outcome)
                        ((sp/close! session)
                         (fn [_] nil)
                         (fn [e] (log/warn :smc/close-failed {:error e})))))
            fail! #(finish! % reject)]
        (letfn [(arrived! []
                  ;; the last arrival claims the barrier, atomically: two
                  ;; particles may arrive on two executor threads at once
                  (let [[before after]
                        (swap-vals! state
                                    (fn [{:keys [waiting done in-barrier?] :as st}]
                                      (if (and (not in-barrier?)
                                               (= n (+ (count waiting) (count done))))
                                        (assoc st :in-barrier? true)
                                        st)))]
                    (when (and (:in-barrier? after) (not (:in-barrier? before)))
                      (barrier!))))

                (run-site! [sp]
                  (try
                    (let [{:keys [value]} (decide! policy sp)]
                      (if (:observed? (:savepoint/payload sp))
                        (do (swap! state assoc-in [:waiting (slot-of (:savepoint/world sp))] sp)
                            (arrived!))
                        (sp/resume sp value)))
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
                  (let [{:keys [waiting done]} @state]
                    (if (empty? waiting)
                      (finish! (assoc (m/empirical (mapv (fn [slot] [(get-in done [slot :sample])
                                                                     (get-in done [slot :log-weight])])
                                                         (range n)))
                                      :log-normalizer (:log-z @state))
                               resolve)
                      (let [slots (vec (range n))
                            log-ws (mapv #(if-let [s (get waiting %)]
                                            (weight-of (:savepoint/world s))
                                            (get-in done [% :log-weight]))
                                         slots)
                            weights (m/normalize-log-weights log-ws)
                            resample? (< (m/compute-ess weights) (* threshold n))]
                        (if-not resample?
                          (do (swap! state assoc :waiting {} :in-barrier? false)
                              (doseq [[_ s] (sort-by key waiting)]
                                (sp/resume s (:value (:savepoint/payload s)))))
                          (let [ancestors (m/systematic-resample weights n)
                                forked-slots (filterv #(contains? waiting (nth ancestors %)) slots)]
                            (swap! state update :log-z + (m/log-mean-exp log-ws))
                            ((all-forked (mapv #(get waiting (nth ancestors %)) forked-slots))
                             (fn [children]
                               (let [carried (into {} (keep (fn [slot]
                                                              (when-let [d (get done (nth ancestors slot))]
                                                                [slot (assoc d :log-weight 0.0)])))
                                                   slots)]
                                 (doseq [[_ s] waiting] (sp/abandon s))
                                 (swap! state assoc :waiting {} :done carried :in-barrier? false)
                                 (doseq [[slot child] (map vector forked-slots children)]
                                   (let [w (:savepoint/world child)]
                                     (rtp/swap-state! w [:inference :slot] (constantly slot))
                                     (rtp/swap-state! w [:inference :log-weight] (constantly 0.0))))
                                 (if (empty? children)
                                   (arrived!)
                                   (doseq [child children]
                                     (sp/resume child (:value (:savepoint/payload child)))))))
                             fail!)))))))]
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
                      ;; the Sample holds what the measure needs; give the
                      ;; world back now instead of holding every finished
                      ;; particle until the session closes
                      (sp/release-world! session world)
                      (arrived!))
                  ;; a program without savepoints: one deterministic particle
                  (finish! (m/empirical (vec (repeat n [(sample-of world result) 0.0]))) resolve)))
              sp/error-site
              (fn [{error :savepoint/payload}] (fail! error))
              sp/abandoned-site (fn [_] nil)})
            (sp/start! session model)
            (catch #?(:clj Throwable :cljs :default) e
              (log/error :smc/start-failed {:error e})
              (fail! e))))))))
