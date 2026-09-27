(ns org.replikativ.spindel.inference.involutive
  "Involutive MCMC over savepoint traces (Neklyudov et al. 2020; Gen's
  `involutive_mh`).

  A move draws auxiliary variables u ~ q(· ; x) from the current choices x,
  maps (x, u) through an involution h to (x', u'), replays the program with
  x', and accepts with

    log α = log p(x') − log p(x) + log q(u' ; x') − log q(u ; x) + log |det ∂h/∂(x,u)|

  Random-walk, scale, swap and data-driven moves are all such pairs (q, h).
  The Jacobian term is the caller's (`:log-jacobian` from the involution);
  `fd-log-jacobian` computes it numerically for real-valued maps — raster's AD
  is the intended replacement.

  Scope: moves that keep the set of sites (fixed dimension). A site the
  replay reaches afresh is drawn from its prior and one it no longer reaches
  is dropped, both scored as in single-site MH; moves that create or remove
  sites through the involution itself (reversible jump) are future work."
  (:require [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.inference.trace :as itrace]
            [org.replikativ.spindel.inference.measure :as m]))

(defn- entry-map [t]
  (into {} (map (juxt :address identity)) (itrace/entries t)))

(defn- prior-terms
  "Σ log p of the stale latents of `old` minus Σ log p of the latents `new`
  drew from their prior: sites outside the involution that the replay
  dropped or reached afresh."
  [old new]
  (let [old-by (entry-map old)
        new-by (entry-map new)
        fresh (filter (fn [e] (and (itrace/latent? e)
                                   (not (identical? (:note e) (:note (get old-by (:address e)))))
                                   (not (:kept? (:note e)))
                                   (not (:symmetric? (:note e)))))
                      (itrace/entries new))
        stale (filter (fn [e] (and (itrace/latent? e) (not (contains? new-by (:address e)))))
                      (itrace/entries old))]
    (- (reduce + 0.0 (map (comp :log-prob :note) stale))
       (reduce + 0.0 (map (comp :log-prob :note) fresh)))))

(defn step
  "One involutive MH move on `trace`.

    :propose    (fn [choices]) -> {:aux u :log-q log q(u ; x)}
    :log-q      (fn [choices u]) -> log q(u ; x), for the reverse move
    :involution (fn [choices u]) -> {:choices x' :aux u' :log-jacobian l}
                where x' gives new values for some addresses of `choices`

  `choices` is `inference.trace/choices` of the trace ({address value}).
  Resolves {:trace t :accepted? b :log-ratio r}; the loser's worlds are
  given back."
  [trace {:keys [propose log-q involution]}]
  (fn [resolve reject]
    (try
      (let [x (itrace/choices trace)
            {u :aux lq-fwd :log-q} (propose x)
            {x' :choices u' :aux lj :log-jacobian} (involution x u)
            changed (into {} (filter (fn [[a v]] (not= v (get x a)))) x')
            from (trace/earliest trace (keys changed))]
        (if-not from
          (resolve {:trace trace :accepted? false :log-ratio 0.0})
          ((trace/replay trace from
                         (itrace/policy {:keep? true
                                         :draw (fn [sp _]
                                                 (let [a (:savepoint/address sp)]
                                                   (when (contains? changed a)
                                                     {:value (get changed a) :symmetric? true})))})
                         {:anchor? itrace/anchor?})
           (fn [t']
             (try
               (let [ratio (if (:trace/error t')
                             ##-Inf
                             (+ (- (itrace/log-joint t') (itrace/log-joint trace))
                                (prior-terms trace t')
                                (- (log-q (itrace/choices t') u') lq-fwd)
                                (or lj 0.0)))
                     accept? (and (not (#?(:clj Double/isNaN :cljs js/isNaN) ratio))
                                  (or (>= ratio 0.0) (< (Math/log (m/uniform01)) ratio)))]
                 (if accept? (trace/release! trace t') (trace/release! t' trace))
                 (resolve {:trace (if accept? t' trace) :accepted? accept? :log-ratio ratio}))
               (catch #?(:clj Throwable :cljs :default) e (reject e))))
           reject)))
      (catch #?(:clj Throwable :cljs :default) e (reject e)))))

;; =============================================================================
;; Numerical Jacobian
;; =============================================================================

(defn- log-abs-det
  "log |det A| by Gaussian elimination with partial pivoting."
  [rows]
  (let [n (count rows)]
    (loop [a (mapv vec rows) col 0 acc 0.0]
      (if (= col n)
        acc
        (let [pivot (apply max-key #(Math/abs (double (get-in a [% col]))) (range col n))
              a (if (= pivot col) a (assoc a col (a pivot) pivot (a col)))
              p (double (get-in a [col col]))]
          (if (zero? p)
            ##-Inf
            (recur (reduce (fn [a r]
                             (let [f (/ (get-in a [r col]) p)]
                               (assoc a r (mapv - (a r) (mapv #(* f %) (a col))))))
                           a (range (inc col) n))
                   (inc col)
                   (+ acc (Math/log (Math/abs p))))))))))

(defn fd-log-jacobian
  "log |det ∂f/∂v| at `v` by central differences, for `f` from vectors of
  reals to vectors of the same length."
  ([f v] (fd-log-jacobian f v 1e-6))
  ([f v eps]
   (let [n (count v)
         columns (for [j (range n)]
                   (let [h (* eps (max 1.0 (Math/abs (double (nth v j)))))
                         plus (f (update v j + h))
                         minus (f (update v j - h))]
                     (mapv #(/ (- %1 %2) (* 2 h)) plus minus)))]
     (log-abs-det (apply mapv vector columns)))))
