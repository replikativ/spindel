(ns spindel.v2.i14-test
  "Loading spindel.v2.i14 kernel-checks I14 (the validity graph over idle computations has no cycle)
  through `world-step`: the step invariant `v14` (iv14 over the model-only (stamp, crank) of validity
  entries, and no dep edge on an idle computation) with `step-p3k` (p3k = p3j && v14, no honest
  hypothesis) and `i14-acyclic` / `step-i14-total`. Tripwires: `v14` and the literal I14 (a DFS over
  the validity graph) after every step of the random drivers and every commit of the oracle samples
  7-13; a validity chain demoted in one Rule R pass (equal stamps, cranks strictly decreasing along
  the chain) and reactivated."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.i14 :as i14]
            [spindel.v2.i8 :as i8]
            [spindel.v2.oracle :as o]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[dom14-key cpres-upd iv14-pres iv14-next vqk-frame vqk-up vrk-frame vq-insert-edge-fresh vq-comp-ins-fresh
    ivs14-pres iv-of-ivs vq-set-rank vq-raise-loop vq-react-one vq-r8 vq-demand vq-demand-fold vq-await-pre
    vq-await-step vq-await-raw vq-track-raw t22-vq t8-full-vq vq-take-park raw-vq
    deb-new-all deb-old-all iv14-make-idle vrk-make-idle vent-edge vent-all vr-demote-tail vr-demote
    vr-pass-start vr-pass-end vr-fold vr-norm-round vr-normalize vr-rule-r
    step-v14 v14-empty step-p3k p3k-empty prec-trans prec-irrefl reach-above i14-acyclic step-i14-total
    nat-max-cases oec-reach scope-open-of-row cur-open-of-run-scope cur-open-of-rso])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

;; ---- the literal I14: depth-first search over the validity graph of the idle computations
(defn validity-graph [w]
  (let [idle (into {} (map (juxt :id identity) (filter :idle (:comps w))))]
    (into {} (for [[id c] idle] [id (set (filter idle (map :debtor (:validity c))))]))))
(defn acyclic? [g]
  (let [state (atom {})]
    (letfn [(visit [n]
              (case (get @state n)
                :done true
                :open false
                (do (swap! state assoc n :open)
                    (let [ok (every? visit (get g n))]
                      (swap! state assoc n :done)
                      ok))))]
      (every? visit (keys g)))))

;; P10 (reduced by `cur-open-of-rso` to `rso`): an alive normal task run's run scope is open, and the
;; structural facts the remaining proof plan uses (notes/PLAN.md, branch i14): (c) a task run's scope has
;; the task's owner as parent or a parent that is no scope, (d) distinct runs have distinct scopes, (e) run
;; scopes have kind run, (si) a closed run scope of an alive task run has a closed parent scope
(defn p10-facts [w]
  (let [scope (into {} (map (juxt :id identity) (:scopes w)))
        task (into {} (map (juxt :id identity) (:tasks w)))
        task-runs (filter #(task (:of %)) (:runs w))
        alive? #(not= s/act-done (:act %))]
    {:rso (every? (fn [r] (or (not (alive? r)) (not= s/mode-normal (:mode r))
                              (:open (scope (:scope r)) false)))
                  task-runs)
     :c (every? (fn [r] (let [sc (scope (:scope r))]
                          (or (nil? sc) (= (:parent sc) (:owner (task (:of r)))) (nil? (scope (:parent sc))))))
                task-runs)
     :d (apply distinct? (cons -1 (map :scope (:runs w))))
     :e (every? (fn [r] (let [sc (scope (:scope r))] (or (nil? sc) (= s/scope-run (:kind sc))))) (:runs w))
     :si (every? (fn [r] (let [sc (scope (:scope r))]
                           (or (nil? sc) (:open sc) (not (alive? r))
                               (let [p (scope (:parent sc))] (and p (not (:open p)))))))
                 task-runs)}))

(defn- checks [w tag]
  (is (true? (i14/v14 w)) (str "v14 " tag))
  (is (acyclic? (validity-graph w)) (str "I14 " tag))
  (is (true? (i8/cur-open-ok w)) (str "cur-open-ok " tag))
  (is (= {:rso true :c true :d true :e true :si true} (p10-facts w)) (str "P10 facts " tag)))

(defn drive [seed runs steps d0?]
  (let [rng (java.util.Random. seed)]
    (dotimes [run runs]
      (loop [i 0 w (et/prefix-world)]
        (when (< i steps)
          (let [item (loop [k 0]
                       (let [x (et/random-item rng w)]
                         (if (or (not d0?) (it/d0-ok? w x) (> k 50)) x (recur (inc k)))))
                w2 (:world (en/world-step w item))]
            (checks w2 (str "seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))))

(deftest i14-random
  (drive 20261901 12 80 false)
  (drive 20261902 12 80 true))

(deftest i14-oracle
  (doseq [n [7 8 9 10 11 12 13]]
    (let [log (o/read-log (str "test/spindel/v2/oracle/log-sample-" n ".edn"))]
      (reduce (fn [w [i c]]
                (let [w2 (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c)))))]
                  (checks w2 (str "sample " n " commit " i))
                  w2))
              s/empty-world (map-indexed vector log)))))

;; ---- a chain demoted in ONE Rule R pass (as react_test's p6-chain, then only the top keeps its observer)
(defn- step! [w item]
  (let [o (en/world-step w item)] (is (true? (:accepted o)) (pr-str item)) (:world o)))
(defn- chain [n m]
  (let [mk (fn [w] (let [c (:next-id w) w (step! w [14 2 c [1] 1]) ob (:next-id w) w (step! w [4 c 1 ob])
                         r (:next-id w) w (step! w [17 c r]) w (step! w [21 r])] [w c ob r]))
        [w c0 ob0 r0] (mk (reduce step! s/empty-world it/base))
        w (step! w [3 r0 3 1 (:next-id w)])
        w (step! w [20 r0 1 5])]
    (loop [i 0 w w prev c0 obs [ob0] cs [c0]]
      (if (= i n)
        [w obs cs]
        (let [[w c ob r] (mk w)
              w (reduce (fn [w _] (step! w [18 r [prev] 0 1 (:next-id w) []])) w (range m))
              w (step! w [20 r 1 (+ 6 i)])]
          (recur (inc i) w c (conj obs ob) (conj cs c)))))))
(deftest i14-one-pass-chain
  (let [[w obs cs] (chain 3 2)
        ;; the lower observers go first: their computations stay live through the dep edges above them
        w (reduce (fn [w ob] (step! w [5 ob])) w (butlast obs))
        _ (is (not-any? :idle (filter #((set cs) (:id %)) (:comps w))) "still live through the chain")
        w (step! w [5 (last obs)])
        row (fn [w id] (first (filter #(= id (:id %)) (:comps w))))]
    (checks w "after the one-pass demotion")
    (is (every? #(:idle (row w %)) cs) "the whole chain is idle")
    (let [g (validity-graph w)]
      (is (= (set (rest cs)) (set (keys (filter (comp seq val) g)))) "each upper computation has validity on the one below")
      (doseq [[a b] (partition 2 1 cs)]
        (is (contains? (get g b) a) (str b " -> " a))
        (let [stamps (set (map :stamp (concat (:validity (row w a)) (:validity (row w b)))))]
          (when (seq (:validity (row w a)))
            (is (= 1 (count stamps)) "one pass: one stamp"))
          (is (every? (fn [u] (every? #(< (:crank u) (:crank %)) (:validity (row w b)))) (:validity (row w a)))
              "cranks strictly decrease down the chain"))))
    (let [w2 (step! w [4 (last cs) 1 (:next-id w)])]
      (checks w2 "after reactivation")
      (is (not-any? #(:idle (row w2 %)) cs) "the chain is reactivated"))))
