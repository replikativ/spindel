(ns spindel.v2.reach-test
  "Requiring spindel.v2.reach kernel-checks every theorem in it. These tests run
  the compiled `reach-run` / `derive-run` on small graphs and compare them with
  a plain Clojure BFS and a plain least-fixpoint iteration."
  (:require [clojure.test :refer [deftest is testing]]
            [spindel.v2.reach :as r]))

;; ---------------------------------------------------------------------------
;; Plain Clojure references

(defn- bfs [g roots]
  (loop [seen #{} work (vec roots)]
    (if-let [x (first work)]
      (if (seen x)
        (recur seen (subvec work 1))
        (recur (conj seen x) (into (subvec work 1) (get g x []))))
      seen)))

(defn- succ-fn [g] (fn [x] (get g x [])))

(defn- fuel-for [g roots]
  (+ 1 (count roots) (reduce + 0 (map count (vals g)))))

(defn- reach [g roots fuel]
  (let [res (r/reach-run fuel (succ-fn g) roots)]
    {:visited (set (:visited res)) :converged (:converged res)}))

(defn- lfp-derive [base deps leaf nodes]
  (loop [d #{}]
    (let [d' (into d (filter (fn [x] (and (base x)
                                          (every? #(or (leaf %) (d %)) (deps x))))
                             nodes))]
      (if (= d d') d (recur d')))))

(defn- run-derive [base deps leaf nodes fuel]
  (let [res (r/derive-run fuel base deps leaf nodes)]
    {:derived (set (:derived res)) :converged (:converged res)}))

;; ---------------------------------------------------------------------------
;; Reach

(deftest reach-small-graphs
  (doseq [[label g roots] [["cycle" {1 [2] 2 [3] 3 [1]} [1]]
                           ["diamond" {1 [2 3] 2 [4] 3 [4]} [1]]
                           ["unreachable node" {1 [2] 5 [1] 2 []} [1]]
                           ["self loop" {7 [7]} [7]]
                           ["several roots, shared tail" {1 [3] 2 [3] 3 [4 1]} [1 2]]
                           ["duplicate roots" {1 [2]} [1 1 1]]
                           ["no roots" {1 [2]} []]]]
    (testing label
      (let [{:keys [visited converged]} (reach g roots (fuel-for g roots))]
        (is (true? converged))
        (is (= (bfs g roots) visited))))))

(deftest reach-unreachable-excluded
  (let [{:keys [visited]} (reach {1 [2] 5 [1]} [1] 10)]
    (is (not (contains? visited 5)))))

(deftest reach-fuel-too-small
  (let [g {1 [2 3] 2 [4] 3 [4] 4 [5]}
        {:keys [visited converged]} (reach g [1] 2)]
    (is (false? converged))
    ;; soundness holds regardless of fuel
    (is (every? (bfs g [1]) visited)))
  (testing "zero fuel converges only for an empty worklist"
    (is (true? (:converged (reach {} [] 0))))
    (is (false? (:converged (reach {1 []} [1] 0))))))

(deftest reach-random-graphs
  (let [rng (java.util.Random. 42)]
    (dotimes [_ 200]
      (let [n (inc (.nextInt rng 12))
            g (into {} (for [x (range n)]
                         [x (vec (repeatedly (.nextInt rng 4) #(.nextInt rng n)))]))
            roots (vec (repeatedly (.nextInt rng 3) #(.nextInt rng n)))
            ref (bfs g roots)
            {:keys [visited converged]} (reach g roots (fuel-for g roots))
            small (reach g roots (.nextInt rng 4))]
        (is (true? converged))
        (is (= ref visited))
        (is (every? ref (:visited small)))
        (when (:converged small) (is (= ref (:visited small))))))))

;; ---------------------------------------------------------------------------
;; Derive (blockedness)

(deftest derive-small
  ;; 1 waits on 2 and the leaf 9; 2 waits on 3; 3 waits on nothing; 4 waits on
  ;; itself (a cyclic wait: deadlock, not blocked); 5 is not parked (base false);
  ;; 6 waits on 5.
  (let [base #(contains? #{1 2 3 4 6} %)
        dm {1 [2 9] 2 [3] 3 [] 4 [4] 5 [] 6 [5]}
        deps #(get dm % [])
        leaf #(= % 9)
        nodes [1 2 3 4 5 6]
        {:keys [derived converged]} (run-derive base deps leaf nodes (inc (count nodes)))]
    (is (true? converged))
    (is (= #{1 2 3} derived))
    (is (= (lfp-derive base deps leaf nodes) derived))
    (testing "too few rounds"
      (let [{:keys [derived converged]} (run-derive base deps leaf nodes 1)]
        (is (false? converged))
        (is (every? #{1 2 3} derived))))))

(deftest derive-random
  (let [rng (java.util.Random. 7)]
    (dotimes [_ 200]
      (let [n (inc (.nextInt rng 10))
            nodes (vec (range n))
            bs (set (filter (fn [_] (< (.nextInt rng 4) 3)) nodes))
            leaves #{100 101}
            dm (into {} (for [x nodes]
                          [x (vec (repeatedly (.nextInt rng 3)
                                              #(if (zero? (.nextInt rng 3))
                                                 (+ 100 (.nextInt rng 2))
                                                 (.nextInt rng n))))]))
            base #(contains? bs %) deps #(get dm % []) leaf #(contains? leaves %)
            ref (lfp-derive base deps leaf nodes)
            {:keys [derived converged]} (run-derive base deps leaf nodes (inc n))
            res-l (r/derive-run-l (vec (repeat (inc n) 0)) base deps leaf nodes)]
        (is (true? converged))
        (is (= ref derived))
        (is (= [(set (:derived res-l)) (:converged res-l)] [derived converged]) "derive-run-l = derive-run")))))
