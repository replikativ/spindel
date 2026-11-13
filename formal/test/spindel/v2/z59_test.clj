(ns spindel.v2.z59-test
  "Loading spindel.v2.z59 kernel-checks Z#59's two halves: T11 leaves no fired dep edge of the
  re-entered computation (`z59-t11-no-fired`, on the world the entry is taken from) and a fired edge
  on a written source starts no marking (`z59-fired-starts-none`). Tripwires on the random drivers
  of engine-test and every commit of the oracle samples 7-13:
    - after every accepted T11 dispatch (item 19) through `world-step`, the computation has no fired
      dep edge (the theorem, through the predecessor's cancel and Rule R);
    - the auxiliary facts an h-mark proof needs (notes/PLAN.md, branch z59): `dle` (done-epoch <=
      epoch) and `cde` (a computation whose current run is alive has done-epoch /= epoch);
    - branch l5b: `dna` (no dep edge has an idle computation as its debtor) and `nms` (no unfilled
      activation member is an ARMED dep edge on a signal or cell (a stale run's member is fired): T6's fast path fills those at once, so a
      write never delivers through a dep edge)."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.z59 :as z]
            [spindel.v2.oracle :as o]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems
  '[z59-earliest-min z59-entry-least z59-cut-p1 z59-cut-edges z59-t11-no-fired z59-armed-creditors-mem
    z59-fired-starts-none])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

(defn- run-of [w id] (first (filter #(= id (:id %)) (:runs w))))
(defn aux-ok? [w]
  (every? (fn [c]
            (and (<= (:done-epoch c) (:epoch c))
                 (let [r (run-of w (:run c))]
                   (not (and r (= (:epoch r) (:epoch c)) (not= (:act r) s/act-done) (= (:done-epoch c) (:epoch c)))))))
          (:comps w)))
(defn dna-ok? [w]
  (every? (fn [e] (not (and (= s/ek-dep (:kind e))
                            (some #(and (= (:id %) (:debtor e)) (:idle %)) (:comps w)))))
          (:edges w)))
(defn nms-ok? [w]
  (let [sc (set (map :id (filter #(contains? #{s/sk-signal s/sk-cell} (:kind %)) (:sources w))))
        deb (into {} (map (juxt :id :debtor) (filter #(and (= s/ek-dep (:kind %)) (= s/ph-armed (:phase %))) (:edges w))))]
    (every? (fn [a] (every? #(not (sc (deb (:edge %)))) (:members a))) (:acts w))))
(defn- no-fired-dep? [w c]
  (not-any? #(and (= s/ek-dep (:kind %)) (= c (:creditor %)) (= s/ph-fired (:phase %))) (:edges w)))

(defn- checks [w item o tag]
  (is (aux-ok? (:world o)) (str "dle/cde " tag))
  (is (dna-ok? (:world o)) (str "dna " tag))
  (is (nms-ok? (:world o)) (str "nms " tag))
  (when (and (:accepted o) (= 19 (first item)))
    (is (no-fired-dep? (:world o) (second item)) (str "T11 left a fired dep edge " tag))))

(defn drive [seed runs steps d0?]
  (let [rng (java.util.Random. seed)]
    (dotimes [run runs]
      (loop [i 0 w (et/prefix-world)]
        (when (< i steps)
          (let [item (loop [k 0]
                       (let [x (et/random-item rng w)]
                         (if (or (not d0?) (it/d0-ok? w x) (> k 50)) x (recur (inc k)))))
                o (en/world-step w item)]
            (checks w item o (str "seed " seed " run " run " step " i " " (pr-str item)))
            (recur (inc i) (:world o))))))))

(deftest z59-random
  (drive 20261591 15 80 false)
  (drive 20261592 15 80 true))

(deftest z59-oracle
  (doseq [n [7 8 9 10 11 12 13]]
    (let [log (o/read-log (str "test/spindel/v2/oracle/log-sample-" n ".edn"))]
      (reduce (fn [w [i c]]
                (let [item (o/adapt :table {:post (:proj c) :w w} (:item c))
                      o (en/world-step w (:item item))]
                  (checks w (:item item) o (str "sample " n " commit " i))
                  (:world o)))
              s/empty-world (map-indexed vector log)))))
