(ns spindel.v2.cow-test
  "Loading spindel.v2.cow kernel-checks the physical copy-on-write model (notes/LAYER2.md): a fork
  (epoch rotation), a copy on access and a write of one world leave every other world's view
  unchanged, and the invariants those theorems need are kept by the three operations. The scenario
  below runs the compiled model: parent and child fork, the child copies and writes a row."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.cow :as c]))

(def theorems
  '[fork-view copy-view-self copy-view-other write-view-other write-view-self write-isolated
    copy-keeps-self copy-keeps-other
    wf-copy-self wf-copy-other own-copy-self own-copy-other excl-copy-other excl-copy-self
    wf-write own-write excl-write wf-rotate own-rotate excl-fresh excl-rotate rv-fast
    alloc-view-other wf-alloc-self wf-alloc-other own-alloc-self own-alloc-other excl-alloc-self excl-alloc-other
    rv-slow ro-copy-self ro-copy-other ro-write-self ro-write-other ro-rotate ro-alloc-self ro-alloc-other
    fin1-copy fin2-copy fin1-write fin2-write fam-write-isolated fin1-reepoch fin2-reepoch reepoch-self
    fin1-spawn fin2-spawn fin1-alloc fin2-alloc fin1-release fin2-release fin1-empty fin2-single])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

(deftest fork-copy-write-scenario
  (let [;; rows 1 and 2 (ids 1, 2) created in epoch 1; row 1 refers to row 2
        h0 (fn [a] (case (long a) 1 (c/->PRow 1 1 10 '(2)) 2 (c/->PRow 2 1 20 '()) (c/->PRow 0 0 0 '())))
        orig identity
        w (c/->PView 1 (fn [_] 0))
        ;; fork: parent takes epoch 2, child epoch 3
        p (c/rotate w 2)
        k (c/rotate w 3)
        tbl (fn [h v] (mapv #(c/view h orig v %) [1 2]))
        before (tbl h0 w)]
    (is (= before (tbl h0 p) (tbl h0 k)))
    ;; the child copies row 2 to address 3 and writes it
    (let [h1 (c/copy-heap h0 orig 3 k 2)
          k1 (c/copy-view 3 k 2)]
      (is (= before (tbl h1 p) (tbl h1 k1)))
      (is (= 3 (c/ver orig k1 2)))
      (is (= 3 (:epoch (h1 3))))
      (let [h2 (c/write-heap h1 3 99 '())]
        (is (= before (tbl h2 p)))
        (is (= 99 (:val (c/view h2 orig k1 2))))
        (is (= (c/view h1 orig k1 1) (c/view h2 orig k1 1)))))))
