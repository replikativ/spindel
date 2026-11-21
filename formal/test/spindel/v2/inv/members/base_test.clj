(ns spindel.v2.inv.members.base-test
  "Kernel certification plus independent field checks for the attached AR/EKB
   premises. These finite observations do not prove unmodelled runtime behavior."
  (:require [clojure.test :refer [deftest is testing]]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as engine]
            [spindel.v2.inv.alive-runs :as ar]
            [spindel.v2.inv.members.cascade :as hm6]
            [spindel.v2.inv.members.base :as base]
            [spindel.v2.inv.members.cascade-test :as certification]
            [spindel.v2.engine-test :as fixtures]))

(def theorems
  '[chain-to-edge-kinds-parts chain-to-edge-kinds-prev chain-to-edge-kinds-alive-run-latest chain-to-edge-kinds-edge-kinds chain-to-edge-kinds-implies-chain-to-i8-closed chain-to-edge-kinds-implies-chain-start chain-to-edge-kinds-i7-idle chain-to-edge-kinds-acts-parked chain-to-edge-kinds-empty step-chain-to-edge-kinds])

(deftest integration-theorems-kernel-checked
  (doseq [name theorems] (certification/checked-declaration name))
  (is (= {:parameters '[w :- World, it :- Item]
          :statement '(=> (= (chain-to-edge-kinds w) true) (= (chain-to-edge-kinds (:world (world-step w it))) true))}
         (certification/source-statement "spindel/v2/inv/members/base.clj" 'step-chain-to-edge-kinds)))
  (is (true? (base/chain-to-edge-kinds s/empty-world))))

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
  (is (= (current-computation-runs? w) (ar/alive-run-latest-rest w)))
  (is (= (layer-one-edge-kinds? w) (hm6/edge-kinds-rest w))))

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
        (is (false? (ar/alive-run-latest-rest bad)))
        (let [dead (update bad :runs (fn [rows] (mapv #(assoc % :act s/act-done) rows)))]
          (check-fields dead)
          (is (true? (current-computation-runs? dead))))))
    (testing "savepoint and non-host observation edges are outside layer one"
      (doseq [edge [(assoc (first (:edges w)) :kind s/ek-savepoint)
                    (assoc (first (:edges w)) :kind s/ek-observe :creditor 4)]]
        (let [bad (assoc w :edges [edge])]
          (check-fields bad)
          (is (false? (layer-one-edge-kinds? bad)))
          (is (false? (hm6/edge-kinds-rest bad))))))
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
      (is (true? (base/chain-to-edge-kinds w)))
      (when (< n 160)
        (let [item (if (zero? n) (fixtures/host-unawait 999999) (fixtures/random-item rng w))
              result (engine/world-step w item)]
          (swap! counts update (if (:accepted result) :accepted :refused) inc)
          (when-not (:accepted result) (is (= w (:world result))))
          (recur (:world result) (inc n)))))
    (is (pos? (:accepted @counts)))
    (is (pos? (:refused @counts)))))
