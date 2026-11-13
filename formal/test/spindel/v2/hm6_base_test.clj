(ns spindel.v2.hm6-base-test
  "Kernel certification plus independent field checks for the attached AR/EKB
   premises. These finite observations do not prove unmodelled runtime behavior."
  (:require [clojure.test :refer [deftest is testing]]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as engine]
            [spindel.v2.ar :as ar]
            [spindel.v2.hm6 :as hm6]
            [spindel.v2.hm6-base :as base]
            [spindel.v2.hm6-test :as certification]
            [spindel.v2.engine-test :as fixtures]))

(def theorems
  '[p3la-parts p3la-p3l p3la-ar p3la-ekb p3la-p3i p3la-p3b p3la-g7 p3la-ga p3la-empty step-p3la])

(deftest integration-theorems-kernel-checked
  (doseq [name theorems] (certification/checked-declaration name))
  (is (= {:parameters '[w :- World, it :- Item]
          :statement '(=> (= (p3la w) true) (= (p3la (:world (world-step w it))) true))}
         (certification/source-statement "spindel/v2/hm6_base.clj" 'step-p3la)))
  (is (true? (base/p3la s/empty-world))))

(defn- current-computation-runs? [w]
  (every? (fn [run]
            (or (= s/act-done (:act run))
                (and (< (:of run) (:next-id w))
                     (every? (fn [comp]
                               (or (not= (:id comp) (:of run))
                                   (= (:id run) (:run comp))))
                             (:comps w)))))
          (:runs w)))

(defn- layer-one-edge-kinds? [w]
  (every? (fn [edge]
            (or (= s/ek-wait (:kind edge))
                (= s/ek-dep (:kind edge))
                (and (= s/ek-observe (:kind edge)) (zero? (:creditor edge)))))
          (:edges w)))

(defn- check-fields [w]
  (is (= (current-computation-runs? w) (ar/ar-rest w)))
  (is (= (layer-one-edge-kinds? w) (hm6/ekb-rest w))))

(deftest predicates-reject-malformed-premises
  (let [w (fixtures/prefix-world)]
    (is (seq (:runs w)))
    (is (seq (:comps w)))
    (is (seq (:edges w)))
    (check-fields w)
    (testing "an alive computation run must be its computation's current run"
      (let [bad (update w :comps (fn [rows] (mapv #(assoc % :run 0) rows)))]
        (check-fields bad)
        (is (false? (current-computation-runs? bad)))
        (is (false? (ar/ar-rest bad)))
        (let [dead (update bad :runs (fn [rows] (mapv #(assoc % :act s/act-done) rows)))]
          (check-fields dead)
          (is (true? (current-computation-runs? dead))))))
    (testing "savepoint and non-host observation edges are outside layer one"
      (doseq [edge [(assoc (first (:edges w)) :kind s/ek-savepoint)
                    (assoc (first (:edges w)) :kind s/ek-observe :creditor 4)]]
        (let [bad (assoc w :edges [edge])]
          (check-fields bad)
          (is (false? (layer-one-edge-kinds? bad)))
          (is (false? (hm6/ekb-rest bad))))))
    (testing "live run references must lie inside the allocator"
      (let [bad (update w :runs (fn [rows] (mapv #(assoc % :of (:next-id w) :act s/act-active) rows)))]
        (check-fields bad)
        (is (false? (current-computation-runs? bad)))))))

(deftest reachable-steps-preserve-independent-premises
  (let [rng (java.util.Random. 20261105)
        counts (atom {:accepted 0 :refused 0})]
    (loop [w (fixtures/prefix-world) n 0]
      (check-fields w)
      (is (current-computation-runs? w))
      (is (layer-one-edge-kinds? w))
      (is (true? (base/p3la w)))
      (when (< n 160)
        (let [item (if (zero? n) (fixtures/host-unawait 999999) (fixtures/random-item rng w))
              result (engine/world-step w item)]
          (swap! counts update (if (:accepted result) :accepted :refused) inc)
          (when-not (:accepted result) (is (= w (:world result))))
          (recur (:world result) (inc n)))))
    (is (pos? (:accepted @counts)))
    (is (pos? (:refused @counts)))))
