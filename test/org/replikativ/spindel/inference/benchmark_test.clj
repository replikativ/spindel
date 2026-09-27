(ns org.replikativ.spindel.inference.benchmark-test
  "Correctness harness for the inference algorithms.

   Every check compares an algorithm's output against a known answer:
   Anglican's benchmark models (gaussian, hmm, branching — same models,
   same ground truths as anglican's algorithm_test), closed-form evidence of
   a conjugate model, and small models built to exercise one mechanism each
   — an observe upstream of a proposed site, a latent whose prior depends
   on another latent, a branch that changes which sites exist, and
   particles that reach different numbers of observes.

   Runs are seeded through anglican's RNG and every algorithm runs its
   particles on one single-threaded executor, so the particle methods (IS,
   SMC, PIMH, PGibbs, PGAS) repeat exactly. MH chains and IPMCMC nodes run
   concurrently and share the one generator, so their draws interleave in
   scheduling order; their budgets leave room for that."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.inference.inference :as infer]
            [org.replikativ.spindel.inference.kernel :as k]
            [org.replikativ.spindel.inference.measure :as m]
            [org.replikativ.spindel.inference.effects :refer [sample observe]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :as aw]
            [org.replikativ.spindel.engine.core :as rtc]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.executor :as executor]
            [anglican.runtime :as ar]))

;; =============================================================================
;; Running and reading measures
;; =============================================================================

(defonce ^:private serial-executor (executor/thread-pool-executor {:threads 1}))

(defn run-infer
  "Run `(make-inference)` (a spin-returning inference call) to its measure
   under a fresh root context, seeded."
  [seed make-inference]
  (.setSeed ^org.apache.commons.math3.random.RandomGenerator ar/RNG (long seed))
  (let [root (ctx/create-execution-context)]
    (try (binding [rtc/*execution-context* root]
           (let [r (deref (future @(spin (aw/await (make-inference)))) 300000 ::timeout)]
             (when (= r ::timeout) (throw (ex-info "inference timed out" {})))
             r))
         (finally (ctx/stop-context! root)))))

(defn weighted-values
  "[[value normalized-weight] …] of a measure's program results."
  [measure]
  (let [ps (m/get-particles measure)
        ws (m/normalize-log-weights (mapv second ps))]
    (mapv (fn [[c _] w] [(m/get-value c) w]) ps ws)))

(defn w-mean [f wv] (reduce + (map (fn [[v w]] (* w (double (f v)))) wv)))

(defn w-mean-sd [f wv]
  (let [mu (w-mean f wv)]
    [mu (Math/sqrt (w-mean #(let [d (- (double (f %)) mu)] (* d d)) wv))]))

(defn w-distribution [f wv]
  (reduce (fn [acc [v w]] (update acc (f v) (fnil + 0.0) w)) {} wv))

(defn kl-categorical
  "KL(p ‖ q) for {category weight} maps; p is normalized here."
  [p q]
  (let [zp (reduce + (vals p)) zq (reduce + (vals q))]
    (reduce + (for [[c w] p :when (pos? w)]
                (let [pc (/ w zp) qc (/ (get q c 0.0) zq)]
                  (* pc (Math/log (/ pc qc))))))))

(defn kl-normal [[pm ps] [qm qs]]
  (+ (- (Math/log qs) (Math/log ps))
     (/ (+ (* ps ps) (let [d (- pm qm)] (* d d))) (* 2 qs qs))
     -0.5))

;; =============================================================================
;; Anglican benchmark models
;; =============================================================================

(defn gaussian-model [observations sigma mu0 sigma0]
  (spin
   (let [mu (sample (ar/normal mu0 sigma0))]
     (loop [os observations]
       (when (seq os)
         (observe (ar/normal mu sigma) (first os))
         (recur (rest os))))
     mu)))

(def gaussian-args [[9.0 8.0] (Math/sqrt 2.0) 1.0 (Math/sqrt 5.0)])
(def gaussian-truth [7.25 (Math/sqrt (/ 1.0 1.2))])

(defn hmm-model [observations init-dist trans-dists obs-dists]
  (spin
   (loop [os observations
          states [(sample init-dist)]]
     (if (empty? os)
       states
       (let [state (sample (get trans-dists (peek states)))]
         (observe (get obs-dists state) (first os))
         (recur (rest os) (conj states state)))))))

(def hmm-args
  [[0.9 0.8 0.7 0.0 -0.025 -5.0 -2.0 -0.1 0.0 0.13 0.45 6 0.2 0.3 -1 -1]
   (ar/discrete [1.0 1.0 1.0])
   {0 (ar/discrete [0.1 0.5 0.4])
    1 (ar/discrete [0.2 0.2 0.6])
    2 (ar/discrete [0.15 0.15 0.7])}
   {0 (ar/normal -1 1)
    1 (ar/normal 1 1)
    2 (ar/normal 0 1)}])

(def hmm-truth
  [[0.3775 0.3092 0.3133] [0.0416 0.4045 0.5539] [0.0541 0.2552 0.6907]
   [0.0455 0.2301 0.7244] [0.1062 0.1217 0.7721] [0.0714 0.1732 0.7554]
   [0.9300 0.0001 0.0699] [0.4577 0.0452 0.4971] [0.0926 0.2169 0.6905]
   [0.1014 0.1359 0.7626] [0.0985 0.1575 0.744] [0.1781 0.2198 0.6022]
   [0.0000 0.9848 0.0152] [0.1130 0.1674 0.7195] [0.0557 0.1848 0.7595]
   [0.2017 0.0472 0.7511] [0.2545 0.0611 0.6844]])

(defn hmm-error
  "RMS error of the posterior state marginals against the truth."
  [wv]
  (let [marg (for [t (range 17) s (range 3)]
               (w-mean #(if (= s (nth % t)) 1.0 0.0) wv))
        truth (flatten hmm-truth)]
    (Math/sqrt (/ (reduce + (map #(let [d (- %1 %2)] (* d d)) marg truth))
                  (count truth)))))

(defn- fib [n] (loop [a 0 b 1 m 0] (if (= m n) a (recur b (+ a b) (inc m)))))

(defn branching-model []
  (spin
   (let [count-prior (ar/poisson 4)
         r (sample count-prior)
         l (if (< 4 r)
             6
             (+ 1 (fib (* 3 r)) (sample count-prior)))]
     (observe (ar/poisson l) 6)
     r)))

(def branching-truth
  ;; exact enumeration of p(r | obs) (anglican's truth is a Monte-Carlo of this)
  (let [cp (ar/poisson 4)
        joint (for [r (range 40)]
                [r (if (< 4 r)
                     (+ (ar/observe* cp r) (ar/observe* (ar/poisson 6) 6))
                     (m/log-sum-exp
                      (for [s (range 60)]
                        (+ (ar/observe* cp r) (ar/observe* cp s)
                           (ar/observe* (ar/poisson (+ 1 (fib (* 3 r)) s)) 6)))))])
        z (m/log-sum-exp (map second joint))]
    (into {} (map (fn [[r lp]] [r (Math/exp (- lp z))]) joint))))

;; =============================================================================
;; Mechanism models (each isolates one thing an algorithm must get right)
;; =============================================================================

(defn conjugate-model
  "x ~ N(0,1), ten observations y=1 ~ N(x,1). Closed-form evidence."
  []
  (spin
   (let [x (sample (ar/normal 0 1))]
     (loop [i 0] (when (< i 10) (observe (ar/normal x 1) 1.0) (recur (inc i))))
     x)))

(def conjugate-log-evidence
  ;; y ~ N(0, I + 11ᵀ): det = 1+n, quad = Σy² − (Σy)²/(1+n)
  (let [n 10.0 quad (- n (/ (* n n) (+ 1.0 n)))]
    (- (* -0.5 n (Math/log (* 2 Math/PI))) (* 0.5 (Math/log (+ 1.0 n))) (* 0.5 quad))))

(defn interleaved-model
  "An observe sits between the two latents: a move on z must still see y₁."
  []
  (spin
   (let [x (sample (ar/normal 0 1))]
     (observe (ar/normal x 1) 2.0)
     (let [z (sample (ar/normal 0 1))]
       (observe (ar/normal z 1) -2.0)
       [x z]))))

(defn hierarchical-model
  "z's prior depends on x: a move on x changes z's density.
   Posterior of x: y = x + e₁ + e₂ with y = 2 → N(2/3, 2/3)."
  []
  (spin
   (let [x (sample (ar/normal 0 1))
         z (sample (ar/normal x 1))]
     (observe (ar/normal z 1) 2.0)
     x)))

(defn switch-model
  "Which latent exists depends on b. p(b | y=5) ∝ ½N(5;0,√2) vs ½N(5;5,√2)."
  []
  (spin
   (let [b (sample (ar/flip 0.5))
         v (if b (sample (ar/normal 0 1)) (sample (ar/normal 5 1)))]
     (observe (ar/normal v 1) 5.0)
     b)))

(def switch-truth
  (let [l (fn [mu] (Math/exp (/ (- (* (- 5 mu) (- 5 mu))) 4.0)))]
    (/ (l 0) (+ (l 0) (l 5)))))

(defn varlen-model
  "Particles reach one or two observes depending on b.
   p(b | …) ∝ ½·N(0.5;0,1) vs ½ — b=true pays the extra observe."
  []
  (spin
   (let [b (sample (ar/flip 0.5))]
     (when b (observe (ar/normal 0 1) 0.5))
     (observe (ar/normal 0 1) 0.1)
     b)))

(def varlen-truth
  (let [a (Math/exp (ar/observe* (ar/normal 0 1) 0.5))]
    (/ a (+ a 1.0))))

;; =============================================================================
;; Evidence
;; =============================================================================

(deftest evidence-is-estimated
  (testing "importance sampling: log mean weight, not log sum"
    (let [meas (run-infer 1 #(infer/importance-sampling (conjugate-model) 2000 {:executor serial-executor}))]
      (is (< (Math/abs (- (m/log-marginal meas) conjugate-log-evidence)) 0.3)
          (str (m/log-marginal meas) " vs " conjugate-log-evidence))))
  (testing "SMC: the normalizer accumulated across resampling"
    (let [meas (run-infer 2 #(infer/smc-infer (conjugate-model) 500 {:executor serial-executor}))]
      (is (< (Math/abs (- (m/log-marginal meas) conjugate-log-evidence)) 0.3)
          (str (m/log-marginal meas) " vs " conjugate-log-evidence)))))

;; =============================================================================
;; Posterior accuracy per algorithm
;; =============================================================================

(def algorithms
  "name → (fn [model-fn budget] spin-returning inference). `budget` scales
   the work so each algorithm gets comparable effort; the particle-MCMC
   methods get more, shorter sweeps — a static parameter only moves between
   sweeps."
  (let [o {:executor serial-executor}]
    {:importance (fn [mf n] (infer/importance-sampling (mf) n o))
     :smc        (fn [mf n] (infer/smc-infer (mf) (quot n 4) o))
     :lmh        (fn [mf n] (infer/kernel-infer (mf) (k/single-site-mh-kernel (quot n 4) {:samples :all :burn (quot n 8)}) 4 o))
     :rmh        (fn [mf n] (infer/kernel-infer (mf) (k/random-walk-mh-kernel (quot n 4) {:step-size 0.5 :samples :all :burn (quot n 8)}) 4 o))
     :pimh       (fn [mf n] (infer/pimh-infer (mf) 20 (quot n 40) o))
     :pgibbs     (fn [mf n] (infer/pgibbs-infer (mf) 20 (quot n 40) o))
     :pgas       (fn [mf n] (infer/pgas-infer (mf) 30 (quot n 60) o))
     :ipmcmc     (fn [mf n] (infer/ipmcmc-infer (mf) 20 (quot n 160) (assoc o :num-nodes 4)))}))

(defn check [algo model-fn budget seed]
  (weighted-values (run-infer seed #((get algorithms algo) model-fn budget))))

(deftest gaussian-benchmark
  ;; not :lmh — its prior proposals N(1, √5) land in the posterior
  ;; N(7.25, 0.91) about once in a hundred tries, so its effective sample
  ;; size at this budget is too small to meet the threshold. Its correctness
  ;; is covered by the models below.
  (doseq [algo (remove #{:lmh} (keys algorithms))]
    (testing algo
      (let [kl (kl-normal (w-mean-sd identity (check algo #(apply gaussian-model gaussian-args) 12000 11))
                          gaussian-truth)]
        (is (< kl 0.1) (str algo " KL " kl))))))

(deftest hierarchical-latents
  (doseq [algo (keys algorithms)]
    (testing algo
      (let [[mu sd] (w-mean-sd identity (check algo hierarchical-model 16000 12))]
        (is (< (Math/abs (- mu (/ 2.0 3))) 0.12) (str algo " mean " mu))
        (is (< (Math/abs (- sd (Math/sqrt (/ 2.0 3)))) 0.12) (str algo " sd " sd))))))

(deftest observe-upstream-of-a-move
  (doseq [algo (keys algorithms)]
    (testing algo
      (let [wv (check algo interleaved-model 8000 13)
            [xm xs] (w-mean-sd first wv)
            [zm zs] (w-mean-sd second wv)]
        (is (< (Math/abs (- xm 1.0)) 0.12) (str algo " x mean " xm))
        (is (< (Math/abs (- zm -1.0)) 0.12) (str algo " z mean " zm))
        (is (< (Math/abs (- xs (Math/sqrt 0.5))) 0.12) (str algo " x sd " xs))
        (is (< (Math/abs (- zs (Math/sqrt 0.5))) 0.12) (str algo " z sd " zs))))))

(deftest structure-changing-branch
  (doseq [algo (keys algorithms)]
    (testing algo
      (let [p (w-mean #(if % 1.0 0.0) (check algo switch-model 4000 14))]
        (is (< (Math/abs (- p switch-truth)) 0.03) (str algo " p(b) " p " vs " switch-truth))))))

(deftest branching-benchmark
  (doseq [algo (keys algorithms)]
    (testing algo
      (let [kl (kl-categorical (w-distribution identity (check algo branching-model 4000 15))
                               branching-truth)]
        (is (< kl 0.05) (str algo " KL " kl))))))

(deftest particles-reach-different-numbers-of-observes
  (doseq [algo [:smc :pimh :pgibbs]]
    (testing algo
      (let [p (w-mean #(if % 1.0 0.0) (check algo varlen-model 4000 16))]
        (is (< (Math/abs (- p varlen-truth)) 0.05) (str algo " p(b) " p " vs " varlen-truth))))))

(deftest hmm-benchmark
  (doseq [algo [:smc :pgibbs :pgas :lmh]]
    (testing algo
      (let [err (hmm-error (check algo #(apply hmm-model hmm-args) 12000 17))]
        (is (< err 0.05) (str algo " rms " err))))))

(deftest bbvi-learns-the-posterior
  (testing "gaussian: q converges to the conjugate posterior"
    (let [meas (run-infer 18 #(infer/bbvi-infer (apply gaussian-model gaussian-args) 100 60 {:executor serial-executor}))
          [q] (vals (infer/get-variational-dists meas))
          kl (kl-normal (w-mean-sd identity (weighted-values meas)) gaussian-truth)]
      (is (< (Math/abs (- (:mean q) 7.25)) 0.3) (str "q " q))
      (is (< kl 0.1) (str "weighted samples KL " kl))))
  (testing "its weighted samples estimate the evidence"
    (let [meas (run-infer 19 #(infer/bbvi-infer (conjugate-model) 200 40 {:executor serial-executor}))]
      (is (< (Math/abs (- (m/log-marginal meas) conjugate-log-evidence)) 0.2)
          (str (m/log-marginal meas))))))
