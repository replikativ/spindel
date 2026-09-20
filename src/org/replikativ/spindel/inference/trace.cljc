(ns org.replikativ.spindel.inference.trace
  "Probabilistic programs as traced computations.

  `sample`, `observe` and `factor` publish savepoints (sites
  `:inference/choose` and `:inference/factor`), so a probabilistic program is
  run and replayed by `spindel.trace` like any other computation. This
  namespace adds what is specific to inference and nothing else: a policy that
  scores, pure functions over scored traces, and Metropolis-Hastings as replay
  plus an accept step.

  Every entry's `:note` carries

    :dist          the site's distribution (nil for a factor)
    :log-prob      log density of the entry's value under :dist, for EVERY
                   site, sampled ones included (a factor's weight)
    :log-proposal  log density under whatever drew the value; absent when the
                   value was not drawn (observed, constrained, kept)
    :observed? :constrained? :kept? :symmetric? :factor?

  and the world accumulates the importance weight at `[:inference
  :log-weight]`: `log p` of what was observed, constrained or factored, and
  `log p - log q` of what a proposal drew. A policy writes it to the world it
  is about to resume, so the weight of a fork starts from the weight at its
  site."
  (:require [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.inference.measure :as m]
            [anglican.runtime :as ar]))

(def choose-site :inference/choose)
(def factor-site :inference/factor)

;; =============================================================================
;; The scoring policy
;; =============================================================================

(defn- add-weight! [world w]
  (rtp/swap-state! world [:inference :log-weight] (fn [x] (+ (or x 0.0) w))))

(defn- finite? [x]
  (and (number? x)
       #?(:clj (not (Double/isInfinite (double x))) :cljs (js/isFinite x))
       #?(:clj (not (Double/isNaN (double x))) :cljs true)))

(defn- decide-choose
  [{:keys [constraints keep? draw init?]} sp old-entry]
  (let [{:keys [dist observed? value]} (:savepoint/payload sp)
        world (:savepoint/world sp)
        address (:savepoint/address sp)]
    (cond
      ;; Pearl's do-operator: the site takes the value and scores nothing.
      (contains? (rtp/get-state world [:inference :interventions]) address)
      {:value (get (rtp/get-state world [:inference :interventions]) address)
       :note {:dist dist :log-prob 0.0 :intervened? true :constrained? true}}

      observed?
      (let [lp (ar/observe* dist value)]
        (add-weight! world lp)
        {:value value :note {:dist dist :log-prob lp :observed? true}})

      (contains? constraints address)
      (let [v (get constraints address)
            lp (ar/observe* dist v)]
        (add-weight! world lp)
        {:value v :note {:dist dist :log-prob lp :constrained? true}})

      :else
      (let [drawn (when draw (draw sp old-entry))
            kept-lp (when (and (not drawn) keep? old-entry
                               (not (:observed? (:note old-entry))))
                      (ar/observe* dist (:value old-entry)))]
        (cond
          drawn
          (let [_ (when-not (or (:symmetric? drawn) (number? (:log-proposal drawn)))
                    (throw (ex-info "A proposal returns :log-proposal or :symmetric? true"
                                    {:type ::malformed-proposal
                                     :address address
                                     :proposal (dissoc drawn :value)})))
                lp (ar/observe* dist (:value drawn))]
            (when-not (:symmetric? drawn)
              (add-weight! world (- lp (:log-proposal drawn))))
            {:value (:value drawn)
             :note (cond-> {:dist dist :log-prob lp
                            :log-proposal (:log-proposal drawn)}
                     (:symmetric? drawn) (assoc :symmetric? true))})

          ;; A kept value outside the new distribution's support is drawn
          ;; again instead (the site's parents moved it out from under it).
          (finite? kept-lp)
          {:value (:value old-entry)
           :note {:dist dist :log-prob kept-lp :kept? true}}

          :else
          (let [init (when init? (:init (:options (:savepoint/payload sp))))
                v (if (some? init) init (ar/sample* dist))
                lp (ar/observe* dist v)]
            {:value v
             :note (cond-> {:dist dist :log-prob lp :log-proposal lp}
                     ;; The old value was there and could not be kept. The
                     ;; reverse move must be able to do the same; see
                     ;; `mh-log-ratio`.
                     (and keep? old-entry) (assoc :redrawn? true))}))))))

(defn policy
  "The scoring policy.

  Options:
    :constraints {address value} fix those sample sites; their density enters
                 the weight
    :keep?       reuse the value a sample site had in the replayed trace,
                 rescored under the site's distribution NOW
    :draw        (fn [sp old-entry]) -> nil (not my site) or
                 {:value v :log-proposal lq}, or {:value v :symmetric? true}
                 for a symmetric move around the old value
    :init?       start a sample site at its `:init` option. Only for the
                 first state of a Markov chain, which may be anything; an
                 `:init` value is not a draw, so it has no place in a move or
                 in a weighted sample.
    :else        policy for every other site (default: its payload)

  With no options every sample site is drawn from its prior: forward
  simulation, likelihood weighting."
  ([] (policy nil))
  ([{fallback :else :as opts}]
   (let [fallback (or fallback trace/payload-policy)]
     (fn [sp old-entry]
       (let [site (:savepoint/site sp)]
         (cond
           (= choose-site site) (decide-choose opts sp old-entry)

           (= factor-site site)
           (let [w (:log-weight (:savepoint/payload sp))]
             (add-weight! (:savepoint/world sp) w)
             {:value nil :note {:log-prob w :factor? true}})

           :else (fallback sp old-entry)))))))

;; =============================================================================
;; Scored traces
;; =============================================================================

(defn entries
  "The inference entries of `trace` in program order, each with its :address."
  [trace]
  (into []
        (comp (map (fn [address]
                     (assoc (get-in trace [:trace/entries address]) :address address)))
              (filter #(#{choose-site factor-site} (:site %))))
        (:trace/order trace)))

(defn anchor?
  "Whether a site is worth an anchor: only a site a move can start from. An
  observe or a factor is never replayed from, and an anchor is a forked
  world. Pass as `:anchor?` to `trace/run` and `trace/replay`."
  [sp]
  (and (= choose-site (:savepoint/site sp))
       (not (:observed? (:savepoint/payload sp)))))

(defn- latent? [entry]
  (and (= choose-site (:site entry))
       (not (:observed? (:note entry)))
       (not (:constrained? (:note entry)))))

(defn latent-addresses
  "Addresses of the sample sites of `trace` that inference may move."
  [trace]
  (into [] (comp (filter latent?) (map :address)) (entries trace)))

(defn choices
  "{address value} of the sample sites of `trace`."
  [trace]
  (into {} (comp (filter #(and (= choose-site (:site %))
                               (not (:observed? (:note %)))))
                 (map (juxt :address :value)))
        (entries trace)))

(defn log-joint
  "log p(choices, observations) of `trace`: the sum of every entry's
  :log-prob."
  [trace]
  (transduce (map (comp :log-prob :note)) + 0.0 (entries trace)))

(defn log-weight
  "The importance weight the world of `trace` accumulated."
  [trace]
  (or (rtp/get-state (:trace/world trace) [:inference :log-weight]) 0.0))

;; =============================================================================
;; Metropolis-Hastings: replay plus accept
;; =============================================================================

(defn mh-log-ratio
  "Log acceptance ratio of moving from `old` to `new`, where `new` is `old`
  replayed from its earliest target with kept values elsewhere.

    log a = [log p(new) - log p(old)]
            + [log q(old | new) - log q(new | old)]
            + [log s(targets | new) - log s(targets | old)]

  q(new | old) is the density of everything `new` drew afresh; q(old | new) is
  the density of everything of `old` that `new` did not keep, which the
  reverse move would have to draw (from the prior, hence its :log-prob). A
  symmetric move cancels on both sides. s is the probability of selecting the
  targets, `log-selection`; it differs between the traces when the move
  changed how many sites there are to select from.

  A kept value that fell out of its site's support is drawn again
  (`:redrawn?`). That is reversible only if the reverse move would redraw there
  too, i.e. if the new value is outside the OLD support; otherwise the reverse
  keeps it, the old state cannot be reached back, and the move is impossible.

  Entries upstream of the replayed address are the SAME entries in both
  traces and cancel everywhere. That relies on a fork sharing the notes of its
  source by reference, which holds for the in-process worlds a session forks
  and would not survive a serialized trace."
  [old new log-selection]
  (let [old-entries (entries old)
        new-entries (entries new)
        old-by-address (into {} (map (juxt :address identity)) old-entries)
        new-by-address (into {} (map (juxt :address identity)) new-entries)
        same? (fn [a b] (and a b (identical? (:note a) (:note b))))
        forward (transduce
                 (comp (filter latent?)
                       (remove #(same? % (get old-by-address (:address %))))
                       (remove (comp :kept? :note))
                       (remove (comp :symmetric? :note))
                       (map (comp :log-proposal :note)))
                 + 0.0 new-entries)
        backward (transduce
                  (comp (filter latent?)
                        (remove #(same? % (get new-by-address (:address %))))
                        (remove #(:kept? (:note (get new-by-address (:address %)))))
                        (remove #(:symmetric? (:note (get new-by-address (:address %)))))
                        (map (comp :log-prob :note)))
                  + 0.0 old-entries)
        irreversible? (some (fn [entry]
                              (and (:redrawn? (:note entry))
                                   (when-let [was (get old-by-address (:address entry))]
                                     (finite? (ar/observe* (:dist (:note was))
                                                           (:value entry))))))
                            new-entries)]
    (if irreversible?
      ##-Inf
      (+ (- (log-joint new) (log-joint old))
         (- backward forward)
         (- (log-selection new) (log-selection old))))))

(defn uniform-site
  "Select one latent site uniformly. A selection is
  {:targets #{address} :log-selection (fn [trace])}."
  [trace _iteration]
  {:targets #{(m/pick-uniformly (latent-addresses trace))}
   :log-selection (fn [t] (- (Math/log (double (count (latent-addresses t))))))})

(defn prior-proposal
  "Propose a fresh draw from a target site's own distribution."
  [sp _old-entry]
  (let [dist (:dist (:savepoint/payload sp))
        v (ar/sample* dist)]
    {:value v :log-proposal (ar/observe* dist v)}))

(defn random-walk-proposal
  "A symmetric Gaussian step of `step-size` around a target's old value."
  [step-size]
  (fn [_sp old-entry]
    {:value (+ (:value old-entry) (* step-size (ar/sample* (ar/normal 0.0 1.0))))
     :symmetric? true}))

(defn mh-step
  "One Metropolis-Hastings move on `trace`.

  Options:
    :select    (fn [trace iteration]) -> {:targets #{address}
               :log-selection (fn [trace])}, the sites to move together and
               the log probability of selecting them in a given trace
               (default: `uniform-site`)
    :propose   (fn [sp old-entry]) -> {:value v :log-proposal lq} or
               {:value v :symmetric? true}, for each target (default:
               `prior-proposal`). The reverse move is scored under the prior,
               so a proposal must be the prior or symmetric.
    :constraints as for `policy`; the conditioning of the chain, which
               every move must repeat
    :iteration passed to :select

  The computation is replayed from the earliest target; every other site
  keeps its value and is rescored under its distribution as it is now. The
  loser's worlds are released. Returns a CPS operation resolving
  {:trace t :accepted? boolean :log-ratio r}; a trace with nothing to move
  resolves unchanged."
  ([trace] (mh-step trace nil))
  ([trace {:keys [select propose iteration constraints]
           :or {select uniform-site propose prior-proposal iteration 0}}]
   (fn [resolve reject]
     (let [{:keys [targets log-selection]}
           (when (seq (latent-addresses trace)) (select trace iteration))
           from (trace/earliest trace targets)]
       (if-not from
         (resolve {:trace trace :accepted? false :log-ratio 0.0})
         (let [move (policy {:keep? true
                             :constraints constraints
                             :draw (fn [sp old-entry]
                                     (when (contains? targets (:savepoint/address sp))
                                       (propose sp old-entry)))})]
           ((trace/replay trace from move {:anchor? anchor?})
            (fn [proposed]
              (try
                (let [ratio (if (:trace/error proposed)
                              ##-Inf
                              (mh-log-ratio trace proposed log-selection))
                      accept? (and (not (#?(:clj Double/isNaN :cljs js/isNaN) ratio))
                                   (or (>= ratio 0.0)
                                       (< (Math/log (m/uniform01)) ratio)))]
                  (if accept?
                    (trace/release! trace proposed)
                    (trace/release! proposed trace))
                  (resolve {:trace (if accept? proposed trace)
                            :accepted? accept?
                            :log-ratio ratio}))
                (catch #?(:clj Throwable :cljs :default) error
                  (reject error))))
            reject)))))))

(defn mh-chain
  "`n` Metropolis-Hastings moves from `trace`; `opts` as for `mh-step`.
  Returns a CPS operation resolving {:trace final :accepted k}. `:on-step`
  (fn [step-result]) sees every move."
  ([trace n] (mh-chain trace n nil))
  ([trace n {:keys [on-step] :as opts}]
   (fn [resolve reject]
     (letfn [(step [current i accepted]
               (if (= i n)
                 (resolve {:trace current :accepted accepted})
                 ((mh-step current (assoc opts :iteration i))
                  (fn [{:keys [accepted?] next-trace :trace :as result}]
                    (when on-step (on-step result))
                    (step next-trace (inc i) (if accepted? (inc accepted) accepted)))
                  reject)))]
       (step trace 0 0)))))

(defn legacy-trace
  "`trace` in the shape the coordinator keeps at `[:inference :trace]`:
  {address {:value :distribution :log-prob :observed?}}."
  [trace]
  (into {}
        (comp (filter #(= choose-site (:site %)))
              (map (fn [{:keys [address value note]}]
                     [address {:value value
                               :distribution (:dist note)
                               :log-prob (:log-prob note)
                               :observed? (boolean (:observed? note))}])))
        (entries trace)))
