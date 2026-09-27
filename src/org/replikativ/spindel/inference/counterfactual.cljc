(ns org.replikativ.spindel.inference.counterfactual
  "Counterfactual queries by abduction, action and prediction (Pearl).

  A program's sample and observe sites are structural equations
  (`inference.mechanism`). Given evidence and interventions:

  1. abduction — condition the program on the evidence (importance sampling
     by `gfi/generate`) and read each weighted factual trace's exogenous
     noise off its sites;
  2. action — install the interventions;
  3. prediction — run the program again in a world of its own with every
     other site fed its factual noise, aligned by address.

  The result pairs each factual world with its counterfactual twin, under
  the factual weight: a joint measure, so quantities that need both worlds
  (probability of necessity, effect of treatment on the treated) are
  expectations over it. A site that exists only in the counterfactual world
  draws fresh noise and is listed as `:unaligned`: its answer is
  interventional, not counterfactual."
  (:require [org.replikativ.spindel.inference.gfi :as gfi]
            [org.replikativ.spindel.inference.trace :as itrace]
            [org.replikativ.spindel.inference.mechanism :as mech]))

(defn noise-of
  "{address u} of the sample and observe sites of `trace` whose law is a
  mechanism, and the addresses of those that are not."
  [trace]
  (reduce (fn [[noise unsupported] {:keys [address value note site]}]
            (if (= itrace/choose-site site)
              (if (and (:dist note) (mech/mechanism? (:dist note)))
                [(assoc noise address (mech/abduct (:dist note) value)) unsupported]
                [noise (conj unsupported address)])
              [noise unsupported]))
          [{} []]
          (itrace/entries trace)))

(defn- then [operation f]
  (fn [resolve reject]
    (operation (fn [x] (try (f x resolve reject)
                            (catch #?(:clj Throwable :cljs :default) e (reject e))))
               reject)))

(defn- twin
  "One factual world and its counterfactual twin."
  [model evidence interventions opts]
  (then (gfi/generate model evidence opts)
        (fn [{t :trace w :weight} resolve reject]
          (let [[noise unsupported] (noise-of t)
                factual (:trace/result t)]
            ((then (gfi/run-policy model (itrace/policy {:interventions interventions :noise noise}) opts)
                   (fn [t' resolve reject]
                     (let [unaligned (into (vec unsupported)
                                           (comp (filter (comp :unaligned? :note)) (map :address))
                                           (itrace/entries t'))
                           out {:factual factual
                                :counterfactual (:trace/result t')
                                :weight w
                                :unaligned unaligned}]
                       ((gfi/close! t') (fn [_] ((gfi/close! t) (fn [_] (resolve out)) reject)) reject))))
             resolve reject)))))

(defn counterfactual
  "Pairs of factual and counterfactual results of `model` (a zero-argument
  function returning a fresh model spin) given `:evidence` ({address value},
  fixed in the factual world) and `:interventions` ({selector transform}, as
  for `inference.trace/policy`), from `:particles` importance-weighted
  factual worlds (default 1: enough when the evidence fixes every noise).

  Resolves a vector of {:factual r :counterfactual r' :weight log-w
  :unaligned [address …]}."
  [model {:keys [evidence interventions particles] :or {particles 1}} & [opts]]
  (fn [resolve reject]
    (letfn [(step [i acc]
              (if (= i particles)
                (resolve acc)
                ((twin (model) evidence interventions opts)
                 (fn [pair] (step (inc i) (conj acc pair)))
                 reject)))]
      (step 0 []))))
