(ns org.replikativ.spindel.inference.gfi
  "Gen's generative function interface over savepoint traces.

  Each operation is `spindel.trace/run` or `replay` under a policy of
  `inference.trace`; what this namespace adds is the weight each operation
  returns and the discard of `update`, with Gen's identities (Cusumano-Towner
  et al. 2019, q the model's internal proposal, here the prior):

    generate(c)       w = log p(t) − log q(t; c)     = Σ log p of constrained and observed sites
    assess(choices)   w = log p(choices)             = the log joint
    update(t, c)      w = log p(t') − log p(t) − log q(fresh choices of t')
    regenerate(t, s)  w = log p(t')/p(t) + log q(t | t')/q(t' | t)

  so importance sampling is `generate`, and MH with a selection is
  `regenerate` accepted on its weight. A model is a spin whose sample sites
  are named with `:id` (or addressed structurally, see `addressing/site-address!`);
  constraints are keyed by those addresses.

  Every operation returns a CPS operation `(fn [resolve reject])`.
  `simulate`, `generate` and `assess` run in a root world and savepoint session
  of their own (a session runs one computation, and a world hosts one
  session); the worlds live until `close!`.
  `update` and `regenerate` replay inside the session of the trace they are
  given and leave that trace intact: the caller keeps one of the two and gives
  the other back with `spindel.trace/release!`."
  (:refer-clojure :exclude [update])
  (:require [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.select :as sel]
            [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.inference.trace :as itrace]
            [org.replikativ.spindel.inference.measure :as m]))

(defn- then [operation f]
  (fn [resolve reject]
    (operation (fn [x] (try (resolve (f x))
                            (catch #?(:clj Throwable :cljs :default) e (reject e))))
               reject)))

(defn- run
  "Run `model` under `policy` in a new root world and session. Options:
  `:executor` for the root world, the rest are session options
  (`effects.savepoint/open!`). A run that fails closes its session."
  [model policy {:keys [executor] :as opts}]
  (let [root (if executor
               (ctx/create-execution-context :executor executor)
               (ctx/create-execution-context))
        session (sp/open! root (merge {:purpose :gfi
                                       :fork-opts {:systems :none}
                                       :retain-released? false}
                                      (dissoc opts :executor)))]
    (fn [resolve reject]
      ((trace/run session model policy {:anchor? itrace/anchor?})
       resolve
       (fn [error]
         ((sp/close! session) (fn [_] (reject error)) (fn [_] (reject error))))))))

(defn run-policy
  "Run `model` under any `inference.trace/policy` in a root world and session
  of its own (options as for `simulate`). Resolves the trace."
  ([model policy] (run-policy model policy nil))
  ([model policy opts] (run model policy opts)))

(defn close!
  "Give back every world of `trace`'s session: the trace and every trace
  replayed from it. Returns a CPS operation."
  [trace]
  (sp/close! (:trace/session trace)))

(defn- entry-map [trace]
  (into {} (map (juxt :address identity)) (itrace/entries trace)))

(defn- fresh-log-q
  "Σ log q of the latent choices `new` drew afresh: not shared with `old`
  (upstream of a replay the entries are the same objects), not kept, not
  constrained."
  [old new]
  (let [old-by (entry-map old)]
    (transduce (comp (filter itrace/latent?)
                     (remove #(identical? (:note %) (:note (get old-by (:address %)))))
                     (remove (comp :kept? :note))
                     (map (comp :log-proposal :note)))
               + 0.0 (itrace/entries new))))

(defn simulate
  "Run `model` (a spin) drawing every sample site from its prior. Resolves the
  trace. Options as for `run`: `:executor` and session options."
  ([model] (simulate model nil))
  ([model opts]
   (run model (itrace/policy) opts)))

(defn generate
  "Run `model` with the sample sites in `constraints` ({address value}) fixed.
  Resolves {:trace t :weight w}, w = Σ log p of the constrained and observed
  sites: an importance weight for the prior as proposal."
  ([model constraints] (generate model constraints nil))
  ([model constraints opts]
   (then (run model (itrace/policy {:constraints constraints}) opts)
         (fn [t] {:trace t :weight (itrace/log-weight t)}))))

(defn assess
  "log p of `choices` ({address value}), which must fix every sample site the
  run reaches. Resolves {:weight w :result r}; the run's session is closed."
  ([model choices] (assess model choices nil))
  ([model choices opts]
   (let [op (run model (itrace/policy {:constraints choices}) opts)]
     (fn [resolve reject]
       (op (fn [t]
             (let [free (itrace/latent-addresses t)
                   out {:weight (itrace/log-joint t) :result (:trace/result t)}]
               ((close! t)
                (fn [_]
                  (if (seq free)
                    (reject (ex-info "assess needs a value for every sample site"
                                     {:type ::unconstrained-choices :addresses free}))
                    (resolve out)))
                reject)))
           reject)))))

(defn- replay-from [trace addresses]
  (or (trace/earliest trace addresses)
      (first (itrace/latent-addresses trace))))

(defn update
  "Change the sample sites in `constraints` ({address value}) and run the
  computation again from the earliest of them; every other site keeps its
  value, rescored under its distribution as it is now, and a site the
  changed control flow reaches for the first time is drawn from its prior.

  Resolves {:trace t' :weight w :discard d} where
    w = log p(t') − log p(t) − Σ log q of what t' drew afresh
    d = {address value} of the choices of t that t' does not keep: the
        overwritten values of constrained sites, and the sites no longer
        reached.
  A constraint on a site `trace` never reached replays from its first
  sample site, so the program can get there."
  [trace constraints]
  (let [from (replay-from trace (filter #(contains? (entry-map trace) %) (keys constraints)))]
    (if-not from
      (fn [_ reject]
        (reject (ex-info "update: the trace has no sample site to replay from"
                         {:type ::nothing-to-replay})))
      (then (trace/replay trace from
                          (itrace/policy {:keep? true :constraints constraints})
                          {:anchor? itrace/anchor?})
            (fn [t']
              (let [new-by (entry-map t')
                    discard (into {}
                                  (keep (fn [{:keys [address value] :as e}]
                                          (when (and (= itrace/choose-site (:site e))
                                                     (not (:observed? (:note e)))
                                                     (or (not (contains? new-by address))
                                                         (contains? constraints address)))
                                            [address value])))
                                  (itrace/entries trace))]
                {:trace t'
                 :weight (- (itrace/log-joint t') (itrace/log-joint trace) (fresh-log-q trace t'))
                 :discard discard}))))))

(defn- selected [trace selection]
  (let [entries (:trace/entries trace)]
    (filterv (if (set? selection)
               selection
               #(sel/selects? selection (sel/describe % (get entries %))))
             (itrace/latent-addresses trace))))

(defn regenerate
  "Draw the selected sample sites afresh from their priors and run the
  computation again from the earliest of them, keeping every other site.
  `selection` is a set of addresses or a selector (`spindel.select`).

  Resolves {:trace t' :weight w}, w = the Metropolis-Hastings log ratio of
  the move without a site-selection term: accepting on it is MH with this
  (fixed) selection. Nothing selected resolves {:trace trace :weight 0.0}."
  [trace selection]
  (let [targets (set (selected trace selection))
        from (trace/earliest trace targets)]
    (if-not from
      (fn [resolve _] (resolve {:trace trace :weight 0.0}))
      (then (trace/replay trace from
                          (itrace/policy {:keep? true
                                          :draw (fn [sp old-entry]
                                                  (when (contains? targets (:savepoint/address sp))
                                                    (itrace/prior-proposal sp old-entry)))})
                          {:anchor? itrace/anchor?})
            (fn [t'] {:trace t' :weight (itrace/mh-log-ratio trace t' (constantly 0.0))})))))

(defn mh
  "One Metropolis-Hastings move: `regenerate` the selection and accept on its
  weight. The loser's worlds are given back. Resolves {:trace t :accepted? b}."
  [trace selection]
  (then (regenerate trace selection)
        (fn [{t' :trace w :weight}]
          (let [accept? (and (not (identical? t' trace))
                             (not (#?(:clj Double/isNaN :cljs js/isNaN) w))
                             (or (>= w 0.0) (< (Math/log (m/uniform01)) w)))]
            (cond
              (identical? t' trace) nil
              accept? (trace/release! trace t')
              :else (trace/release! t' trace))
            {:trace (if accept? t' trace) :accepted? accept?}))))
