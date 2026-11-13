(ns spindel.v2.progress-test
  "Loading spindel.v2.progress kernel-checks L2 (the join measure: no step raises a done run's
  measure, finalizer exits, slice returns and acknowledgements lower it, the run is retired when it
  reaches (0, 0)) and the safety half of L5. Here: a scenario through every decreasing event, the
  measure's non-increase on the random drivers of engine-test, and L5's conclusion (with its three
  state facts as a tripwire) at every quiescent point of those drivers."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.p3 :as p3]
            [spindel.v2.progress :as pr]
            [spindel.v2.engine-test :as et :refer [step! find-row stamp root]]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[mb-run-upd mb-run-upd-ne mb-run-upd-q mb-run-ins raw-mb mb-normalize mb-rule-r step-mb step-mb-total
    sok-empty step-sok mb-of-done step-mu-le finally-exit-dec slice-exit-dec slice-exit-retires ack-dec ack-retires
    mb-retire-gone l5-step l5-core l5-safety l5-dirty])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

(defn mu [w rid] (when-let [r (find-row w :runs rid)] [(pr/mu-f r) (pr/mu-z r)]))

(deftest l2-events
  (let [w s/empty-world
        y (:next-id w)
        w (step! w (et/create-source-top root s/sk-deferred 0 y))
        [k rk w] (et/task-with-slice w)
        w (step! w (et/finally-enter (stamp w rk)))
        w (step! w (et/finally-enter (stamp w rk)))
        z (:next-id w)
        w (step! w (et/arm (stamp w rk) s/rk-offload 5 z))           ; Z#55: the offload parks the run
        _ (is (= s/act-parked (:act (find-row w :runs rk))))
        _ (is (= [3 1] (mu w rk)) "alive (not yet in the measure): two regions + their cleanup slice, one resource")
        w (step! w (et/cancel rk))
        m0 (mu w rk)
        _ (is (= [3 1] m0) "cancelled: 2 finalizers + the cleanup slice to return, 1 resource")
        w (step! w (et/finalize rk))
        _ (is (= m0 (mu w rk)) "finalize schedules the cleanup slice: mu unchanged")
        w (step! w (et/finally-exit (stamp w rk)))
        _ (is (= [2 1] (mu w rk)) "finalizer exit: mu-f - 1 (finally-exit-dec)")
        w (step! w (et/finally-exit (stamp w rk)))
        _ (is (= [1 1] (mu w rk)) "the last region exits; the slice still runs the outermost block")
        w (step! w (et/slice-exit rk))
        _ (is (= [0 1] (mu w rk)) "slice return: mu-f 0 (slice-exit-dec); a resource is outstanding: not retired")
        _ (is (= s/act-done (:act (find-row w :runs rk))))
        _ (is (= s/rp-cancelling (:phase (find-row w :res z))))
        _ (step! w (et/resource-fire z s/res-ok 1) :refused)                ; a cancelling resource does not fire (Z#14)
        w (step! w (et/resource-ack z))]
    (is (nil? (mu w rk)) "the acknowledgement brings mu to (0, 0) and retires the run in the same step (ack-retires)")
    (is (empty? (:cleanup w)))))

(deftest l2-slice-exit-retires
  (let [w s/empty-world
        y (:next-id w)
        w (step! w (et/create-source-top root s/sk-deferred 0 y))
        [k rk w] (et/task-with-slice w)
        w (step! w (et/finally-enter (stamp w rk)))
        w (step! w (et/await* (stamp w rk) [y] s/am-one 1 (:next-id w) []))
        w (step! w (et/cancel rk))
        _ (is (= [2 0] (mu w rk)))
        w (step! w (et/finalize rk))
        w (step! w (et/finally-exit (stamp w rk)))
        _ (is (= [1 0] (mu w rk)))
        w (step! w (et/slice-exit rk))]
    (is (nil? (mu w rk)) "slice-exit-retires")))

;; ---- random drivers: (b) per done run, and L5 at quiescent points

(defn done-runs [w] (filter #(= s/act-done (:act %)) (:runs w)))

(defn mu-ok? [w w2]
  (every? (fn [r] (every? (fn [r2] (and (= s/act-done (:act r2)) (<= (pr/mu-f r2) (pr/mu-f r)) (<= (pr/mu-z r2) (pr/mu-z r))))
                          (filter #(= (:id r) (:id %)) (:runs w2))))
          (done-runs w)))

(defn cone [w c0]
  (loop [todo [c0] seen #{}]
    (if-let [x (first todo)]
      (if (seen x) (recur (rest todo) seen) (recur (concat (rest todo) (pr/csucc w x)) (conj seen x)))
      seen)))

(defn l5-holds? [w c0]
  (let [bl (set (en/blocked-set w))
        cn (cone w c0)]
    (or (some bl cn)
        (some (fn [x] (when-let [c (find-row w :comps x)]
                        (and (not (:idle c)) (en/needs-run w c) (en/eligible w c)))) cn)
        (some (fn [x] (and (some? (find-row w :tasks x)) (en/blk-base w x) (not (bl x)))) cn))))

(def l5-stats (atom {:quiescent 0 :waiting 0}))

(defn check-step [w item w2 tag]
  (is (true? (pr/sok w2)) (str "sok " tag " " (pr-str item)))
  (is (mu-ok? w w2) (str "mu non-increase " tag " " (pr-str item)))
  (when (pr/quiescent w2)
    (swap! l5-stats update :quiescent inc)
    (is (true? (pr/h-cur w2)) (str "h-cur " tag))
    (is (true? (pr/h-mark w2)) (str "h-mark " tag))
    (is (true? (pr/h-mem w2)) (str "h-mem " tag))
    (is (true? (en/blocked-converged w2)) (str "blocked converged " tag))
    (doseq [c (:comps w2) :when (pr/comp-waiting c)]
      (swap! l5-stats update :waiting inc)
      (is (l5-holds? w2 (:id c)) (str "L5 " tag " comp " (:id c))))))

(defn drive [seed runs steps d0?]
  (let [rng (java.util.Random. seed)]
    (dotimes [run runs]
      (loop [i 0 w (et/prefix-world)]
        (when (< i steps)
          (let [item (loop [k 0]
                       (let [x (et/random-item rng w)]
                         (if (or (not d0?) (it/d0-ok? w x) (> k 50)) x (recur (inc k)))))
                w2 (:world (en/world-step w item))]
            (check-step w item w2 (str "seed " seed " run " run " step " i))
            (recur (inc i) w2)))))))

(deftest progress-random
  (is (true? (pr/sok (et/prefix-world))))
  (reset! l5-stats {:quiescent 0 :waiting 0})
  (drive 20261121 20 60 false)
  (drive 20261122 20 60 true)
  (testing "the L5 check is not vacuous"
    (is (pos? (:quiescent @l5-stats)))
    (is (pos? (:waiting @l5-stats)))))
