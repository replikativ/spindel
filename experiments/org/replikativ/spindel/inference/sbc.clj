(ns org.replikativ.spindel.inference.sbc
  "Simulation-based calibration (Talts et al. 2018) of HMC on block sites.

  Not part of the test suite: a seeded statistical experiment with explicit
  thresholds, run with `clojure -M:sbc [simulations]`.

  For each simulation: θ* from the prior, data from the model at θ*, an HMC
  chain on the data, thinned to `draws` posterior draws, and the rank of θ*
  among them in every dimension. For a correct sampler the ranks are uniform
  on {0, …, draws}. Each dimension's ranks are binned and tested against
  uniformity with a χ² test at level α, Bonferroni-corrected over all the
  dimensions tested. Finite samples never give exactly uniform ranks; the
  test decides whether they are too far from it. Exits 1 if any fails."
  (:require [org.replikativ.spindel.inference.benchmark-test :refer [run-infer]]
            [org.replikativ.spindel.inference.block :as block]
            [org.replikativ.spindel.inference.inference :as infer]
            [org.replikativ.spindel.inference.kernel :as k]
            [org.replikativ.spindel.inference.measure :as m]
            [org.replikativ.spindel.inference.effects :refer [sample]]
            [org.replikativ.spindel.spin.cps :refer [spin]])
  (:import [org.apache.commons.math3.distribution ChiSquaredDistribution]))

(def ^:private alpha 0.01)
(def ^:private bins 10)
(def ^:private draws 99)   ; ranks in {0 … 99}: 100 values, 10 per bin

;; --- models: prior sampler, data simulator, block ----------------------------

(defn- sigmoid [x] (/ 1.0 (+ 1.0 (Math/exp (- x)))))

(defn- gaussian-model
  "μ ∈ R², μ_j ~ N(0, 3²), 10 observations y_ij ~ N(μ_j, 1) simulated; the
  block assumes noise sd `assumed` (1 is correct)."
  [name assumed]
  {:name name
   :prior (fn [^java.util.Random r] [(* 3.0 (.nextGaussian r)) (* 3.0 (.nextGaussian r))])
   :simulate (fn [^java.util.Random r [m0 m1]]
               {:ys (vec (repeatedly 10 #(vector (+ m0 (.nextGaussian r)) (+ m1 (.nextGaussian r)))))})
   :hmc {:step-size 0.15 :steps 8}
   :block (let [lp+grad (fn [^doubles mu {:keys [ys]}]
                          (let [m (vec mu)
                                v (* assumed assumed)
                                lp (- (+ (/ (reduce + (map #(* % %) m)) 18.0)
                                         (reduce + 0.0 (for [y ys j [0 1]]
                                                         (let [r (- (nth y j) (nth m j))] (/ (* r r) (* 2.0 v)))))))
                                g (double-array (for [j [0 1]]
                                                  (+ (- (/ (nth m j) 9.0))
                                                     (/ (reduce + 0.0 (map #(- (nth % j) (nth m j)) ys)) v))))]
                            [lp g]))]
            (block/block {:block/id :gaussian
                          :block/latents [{:name :mu :shape [2] :support :real}]
                          :block/target :complete-conditional}
                         {:log-density (fn [mu in] (first (lp+grad mu in)))
                          :value+grad lp+grad}))})

(def ^:private gaussian (gaussian-model "gaussian" 1.0))

(def ^:private logistic
  ;; β ∈ R², β ~ N(0, 1²), 30 observations y_i ~ Bernoulli(σ(b0 + b1 x_i))
  {:name "logistic"
   :prior (fn [^java.util.Random r] [(.nextGaussian r) (.nextGaussian r)])
   :simulate (fn [^java.util.Random r [b0 b1]]
               (let [xs (vec (repeatedly 30 #(.nextGaussian r)))]
                 {:xs xs :ys (mapv #(if (< (.nextDouble r) (sigmoid (+ b0 (* b1 %)))) 1 0) xs)}))
   :hmc {:step-size 0.25 :steps 8}
   :block (let [lp+grad (fn [^doubles b {:keys [xs ys]}]
                          (let [b0 (aget b 0) b1 (aget b 1)]
                            (loop [i 0 lp (- (/ (+ (* b0 b0) (* b1 b1)) 2.0)) g0 (- b0) g1 (- b1)]
                              (if (= i (count xs))
                                [lp (double-array [g0 g1])]
                                (let [x (nth xs i) y (nth ys i) eta (+ b0 (* b1 x)) r (- y (sigmoid eta))]
                                  (recur (inc i) (+ lp (- (* y eta) (Math/log1p (Math/exp eta))))
                                         (+ g0 r) (+ g1 (* r x))))))))]
            (block/block {:block/id :logistic
                          :block/latents [{:name :beta :shape [2] :support :real}]
                          :block/target :complete-conditional}
                         {:log-density (fn [b in] (first (lp+grad b in)))
                          :value+grad lp+grad}))})

;; --- one simulation ------------------------------------------------------------

(def ^:private thin 5)
(def ^:private burn 100)

(defn- posterior-draws
  "`draws` thinned HMC draws of θ given `data`."
  [{:keys [block hmc]} data init seed]
  (let [iterations (+ burn (* thin draws))
        meas (run-infer seed #(infer/kernel-infer
                               (spin (sample (block/block-dist block data) :id :theta :init init))
                               (k/hmc-kernel iterations (assoc hmc :samples :all :burn burn))
                               1 {}))
        chain (mapv (comp m/get-value first) (m/get-particles meas))]
    (vec (take draws (take-nth thin chain)))))

(defn- ranks
  "Rank of θ* among the draws, per dimension."
  [theta* samples]
  (vec (for [j (range (count theta*))]
         (count (filter #(< (nth % j) (nth theta* j)) samples)))))

(defn- chi-square
  "χ² statistic of `ranks` (in {0 … draws}) over `bins` equal bins."
  [ranks]
  (let [per-bin (/ (inc draws) bins)
        counts (frequencies (map #(quot % per-bin) ranks))
        expected (/ (count ranks) (double bins))]
    (reduce + (for [b (range bins)]
                (let [o (get counts b 0)] (/ (* (- o expected) (- o expected)) expected))))))

(defn calibrate
  "Run `simulations` SBC simulations of `model`. Returns per-dimension
  {:chi2 :p :ranks}."
  [model simulations seed]
  (let [r (java.util.Random. seed)
        all (vec (for [s (range simulations)]
                   (let [theta* ((:prior model) r)
                         data ((:simulate model) r theta*)]
                     (ranks theta* (posterior-draws model data [0.0 0.0] (+ seed s))))))
        chi2 (ChiSquaredDistribution. (double (dec bins)))]
    (vec (for [j (range 2)]
           (let [rs (mapv #(nth % j) all)
                 stat (chi-square rs)]
             {:chi2 stat :p (- 1.0 (.cumulativeProbability chi2 stat)) :ranks rs})))))

(defn -main
  "`[simulations]`; `control` as a second argument runs the negative control
  instead: a block that assumes the wrong noise, which must FAIL."
  [& [simulations control]]
  (let [simulations (if simulations (Long/parseLong simulations) 200)
        models (if (= "control" control)
                 [(gaussian-model "gauss-sd2" 2.0)]
                 [gaussian logistic])
        tests (* 2 (count models))
        level (/ alpha tests)
        results (for [model models
                      [j res] (map-indexed vector (calibrate model simulations 42))]
                  (assoc res :model (:name model) :dim j))
        failed (filter #(< (:p %) level) results)]
    (println (format "SBC: %d simulations, %d draws each, %d bins, alpha %.3f (Bonferroni over %d: %.4f)"
                     simulations draws bins alpha tests level))
    (doseq [{:keys [model dim chi2 p ranks]} results]
      (println (format "  %-9s θ%d  chi2 %6.2f  p %.4f  %s  bins %s"
                       model dim chi2 p (if (< p level) "FAIL" "ok")
                       (vec (map #(get (frequencies (map (fn [x] (quot x (/ (inc draws) bins))) ranks)) % 0)
                                 (range bins))))))
    (shutdown-agents)
    (System/exit (if (seq failed) 1 0))))
