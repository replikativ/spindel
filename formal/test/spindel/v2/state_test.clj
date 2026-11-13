(ns spindel.v2.state-test
  "Loading spindel.v2.state and spindel.v2.edits kernel-checks every lemma in them (a failing
  proof throws at load). The deftests check that the named theorems are in the kernel env and
  run the compiled edits on small worlds, checking the invariants at runtime."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.edits :as e]))

(def theorems
  '[tbl-count-upd tbl-count-del tbl-all-upd tbl-all-del tbl-all-mono tbl-all-mono2
    tbl-has-upd tbl-has-del-ne tbl-upd-absent tbl-del-absent tbl-find-id tbl-ids-upd
    tbl-count-upd-same tbl-all-congr nat-nodup-mid ids-fresh-insert
    marked-in-mark marked-in-unmark marked-in-del marked-in-ins-unmarked
    pe-same pe-down pe-mark-core pe-unmark-core pe-remove-marked-core pe-remove-unmarked-core
    mark-edge-pending-exact unmark-edge-pending-exact remove-edge-pending-exact
    insert-edge-pending-exact insert-edge-fresh-pending-exact
    pending-exact-frame pending-exact-run-upd pending-exact-scope-ins pending-exact-bump
    pending-exact-comp-upd pending-exact-comp-del pending-exact-comp-ins pending-exact-edge-upd
    edges-ref-ok-frame edges-ref-ok-run-ins edges-ref-ok-bump
    insert-edge-edges-ref-ok insert-edge-fresh-edges-ref-ok mark-edge-edges-ref-ok
    unmark-edge-edges-ref-ok remove-edge-edges-ref-ok comp-del-edges-ref-ok comp-upd-edges-ref-ok
    ids-ok-empty ids-unique-edges ids-ok-edges
    scope-ins-fresh-ids-ok comp-ins-fresh-ids-ok task-ins-fresh-ids-ok run-ins-fresh-ids-ok
    source-ins-fresh-ids-ok edge-ins-fresh-ids-ok act-ins-fresh-ids-ok resource-ins-fresh-ids-ok
    pub-ins-fresh-ids-ok fork-ins-fresh-ids-ok insert-edge-fresh-ids-ok
    mark-edge-ids-ok unmark-edge-ids-ok
    inv-sample-empty mark-edge-inv-sample unmark-edge-inv-sample insert-edge-fresh-inv-sample])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t))))
        (str t))))

;; ---------------------------------------------------------------------------
;; Runtime

(def no-result (s/->RunResult s/res-none 0))

(defn comp-row [id] (s/->CompRow id 0 [] 0 0 1 0 0 0 0 no-result false [] [] [] [] 0))
(defn edge-row [kind creditor debtor] (s/->EdgeRow 0 kind creditor debtor s/cont-restart 0 s/ph-armed false false 0 false 0 0))

(defn fresh-comp [w]
  (let [id (:next-id w)] [id (s/bump (s/comp-ins w (comp-row id)))]))
(defn fresh-source [w]
  (let [id (:next-id w)] [id (s/bump (s/source-ins w (s/->SourceRow id 0 s/sk-signal 0 0 true 1 [])))]))
(defn fresh-edge [w row]
  (let [id (:next-id w)] [id (e/insert-edge-fresh w row)]))

(defn reference-pending
  "Clojure-side recomputation of exact pending, per comp id."
  [w]
  (into {} (for [c (:comps w)]
             [(:id c) (count (filter #(and (= (:creditor %) (:id c)) (:marked %)) (:edges w)))])))

(defn checks [w]
  {:pending-exact (e/pending-exact w) :edges-ref-ok (e/edges-ref-ok w) :ids-ok (e/ids-ok w)
   :inv-sample (e/inv-sample w)
   :reference (= (reference-pending w) (into {} (map (juxt :id :pending) (:comps w))))})

(def all-true {:pending-exact true :edges-ref-ok true :ids-ok true :inv-sample true :reference true})

(deftest small-world
  (let [w0 s/empty-world
        [c1 w] (fresh-comp w0)
        [c2 w] (fresh-comp w)
        [x w] (fresh-source w)
        [e1 w] (fresh-edge w (edge-row s/ek-dep c1 x))   ; c1 tracks x
        [e2 w] (fresh-edge w (edge-row s/ek-dep c2 c1))  ; c2 depends on c1
        [e3 w] (fresh-edge w (edge-row s/ek-dep c2 x))]
    (is (= all-true (checks w0)))
    (is (= all-true (checks w)))
    (is (= [3 4 5 6 7 8] [c1 c2 x e1 e2 e3]))
    (testing "mark increments the creditor once; marking again is a no-op"
      (let [w1 (e/mark-edge w e2) w2 (e/mark-edge w1 e2) w3 (e/mark-edge w2 e3)]
        (is (= {c1 0 c2 1} (reference-pending w1)))
        (is (= (:comps w1) (:comps w2)))
        (is (= {c1 0 c2 2} (into {} (map (juxt :id :pending) (:comps w3)))))
        (is (every? #(= all-true (checks %)) [w1 w2 w3]))
        (testing "unmark and remove decrement in the same edit"
          (let [w4 (e/unmark-edge w3 e2) w5 (e/remove-edge w3 e3) w6 (e/remove-edge w5 e2)]
            (is (= {c1 0 c2 1} (into {} (map (juxt :id :pending) (:comps w4)))))
            (is (= {c1 0 c2 1} (into {} (map (juxt :id :pending) (:comps w5)))))
            (is (= {c1 0 c2 0} (into {} (map (juxt :id :pending) (:comps w6)))))
            (is (every? #(= all-true (checks %)) [w4 w5 w6]))))
        (testing "unmarking an unmarked edge and editing absent ids change nothing"
          (is (= w (e/unmark-edge w e1)))
          (is (= w (e/mark-edge w 99)))
          (is (= w (e/remove-edge w 99))))))
    (testing "edges-ref-ok: dangling endpoints are caught; removing an unreferenced comp is fine"
      (is (false? (e/edges-ref-ok (e/insert-edge w (edge-row s/ek-dep 42 x)))))
      (is (false? (e/edges-ref-ok (e/insert-edge w (edge-row s/ek-dep c1 42)))))
      (is (false? (e/edges-ref-ok (e/insert-edge w (edge-row s/ek-wait c1 x)))) "wait creditor must be an activation")
      (is (true? (e/edges-ref-ok (e/insert-edge w (edge-row s/ek-observe 0 x)))) "observe creditor is the host")
      (is (false? (e/unreferenced w c1)))
      (let [[c3 w'] (fresh-comp w)]
        (is (true? (e/unreferenced w' c3)))
        (is (= all-true (checks (s/comp-del w' c3))))
        (is (false? (e/edges-ref-ok (s/comp-del w' c1))))))
    (testing "ids-ok rejects a duplicate id and an id at or above next-id"
      (is (false? (e/ids-ok (s/comp-ins w (comp-row c1)))))
      (is (false? (e/ids-ok (s/comp-ins w (comp-row (:next-id w)))))))))

(deftest random-edge-edits
  (let [rng (java.util.Random. 20261103)]
    (dotimes [_ 30]
      (let [[cs w] (reduce (fn [[ids w] _] (let [[id w] (fresh-comp w)] [(conj ids id) w]))
                           [[] s/empty-world] (range 4))
            [x w] (fresh-source w)
            pick (fn [xs] (nth xs (.nextInt rng (count xs))))]
        (loop [i 0 w w edges []]
          (when (< i 40)
            (let [op (.nextInt rng 4)
                  [w edges] (case op
                              0 (let [[id w] (fresh-edge w (edge-row s/ek-dep (pick cs) (pick (conj cs x))))]
                                  [w (conj edges id)])
                              1 [(if (seq edges) (e/mark-edge w (pick edges)) w) edges]
                              2 [(if (seq edges) (e/unmark-edge w (pick edges)) w) edges]
                              3 (if (seq edges)
                                  (let [id (pick edges)] [(e/remove-edge w id) (vec (remove #{id} edges))])
                                  [w edges]))]
              (is (= all-true (checks w)) (str "step " i " op " op))
              (recur (inc i) w edges))))))))
