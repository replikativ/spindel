(ns org.replikativ.spindel.inference.block
  "Numerical blocks as choice sites (the spindel side of the spindel ↔ raster
  block contract, spindel-raster doc/contract.md).

  A block is a fixed-shape group of latent variables with the density factors
  they touch, given as a description (data) and capabilities (functions over
  primitive arrays):

    (block {:block/id :gauss
            :block/latents [{:name :mu :shape [2] :support :real}]
            :block/target :complete-conditional}
           {:log-density (fn [^doubles theta inputs] lp)
            :value+grad  (fn [^doubles theta inputs] [lp ^doubles grad])})

  `(block-dist b inputs)` is the block at its inputs as a distribution whose
  density is the block's log target, so a block site is an ordinary choice
  site: `(sample (block-dist b inputs) :id :mu :init [0.0 0.0])`. Its value is
  θ, the latents flattened in declared order, as a vector of doubles.

  The target includes every factor the latents touch: their priors and the
  observations that depend on them, which must then not be observed again as
  sites of their own. A block without `:sample` cannot be drawn from; start
  it at an `:init`.

  Draft 0 supports unconstrained real latents only; transforms of constrained
  ones (`:constrain`, `:unconstrain` with their Jacobians) come with raster's
  bijectors."
  (:require [anglican.runtime :as ar]))

(def ^:private required-capabilities #{:log-density :value+grad})

(defn- size [shape] (reduce * 1 shape))

(defrecord Block [description capabilities offsets dimension])

(defn block
  "A block from its `description` and `capabilities` (see the namespace)."
  [description capabilities]
  (let [latents (:block/latents description)
        missing (remove (set (keys capabilities)) required-capabilities)]
    (when (seq missing)
      (throw (ex-info "A block lacks required capabilities"
                      {:type ::missing-capabilities :block (:block/id description)
                       :missing (vec missing)})))
    (when-let [constrained (seq (remove #(= :real (:support % :real)) latents))]
      (throw (ex-info "Constrained latents need transforms, not in draft 0"
                      {:type ::unsupported-support :block (:block/id description)
                       :latents (mapv :name constrained)})))
    (let [sizes (mapv #(size (:shape %)) latents)
          offsets (zipmap (map :name latents) (reductions + 0 sizes))]
      (->Block description capabilities offsets (reduce + 0 sizes)))))

(defn dimension "The length of θ." [b] (:dimension b))

(defn capability
  "The capability `k` of block `b`, or nil."
  [b k]
  (get (:capabilities b) k))

(defn latent
  "The latent `name` of θ: a double for a scalar, a vector otherwise."
  [b theta name]
  (let [{:keys [shape]} (first (filter #(= name (:name %)) (:block/latents (:description b))))
        at (get (:offsets b) name)]
    (if (empty? shape)
      (nth theta at)
      (subvec (vec theta) at (+ at (size shape))))))

(defn- theta-array ^doubles [theta] (double-array theta))

(defrecord BlockDist [block inputs]
  ar/distribution
  (sample* [_]
    (if-let [sample (capability block :sample)]
      (vec (sample inputs))
      (throw (ex-info "A block that cannot be sampled starts from an :init"
                      {:type ::no-sample :block (:block/id (:description block))}))))
  (observe* [_ theta]
    (if (= (dimension block) (count theta))
      ((capability block :log-density) (theta-array theta) inputs)
      ##-Inf)))

(defn block-dist
  "Block `b` at `inputs`, as the distribution of its site."
  [b inputs]
  (->BlockDist b inputs))

(defn block-dist? [d] (instance? BlockDist d))

(defn value+grad
  "[log target, gradient] of `dist` (a `block-dist`) at θ, both from the
  block's `:value+grad`; the gradient as a vector."
  [dist theta]
  (let [[lp g] ((capability (:block dist) :value+grad) (theta-array theta) (:inputs dist))]
    [(double lp) (vec g)]))
