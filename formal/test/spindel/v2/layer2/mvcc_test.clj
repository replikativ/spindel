(ns spindel.v2.layer2.mvcc-test
  "Loading spindel.v2.layer2.mvcc kernel-checks the MVCC fork representation (notes/LAYER2.md §9): every
  family state the engine's operations reach reads, in every active world, exactly the value-copy
  tables; the barrier, pruning, token ends and the row monitor protocol are what makes it so.

  The compiled model is also run on the family-log sample shapes agreed in notes/history/PLAN.md (a fork while
  work is in flight, a nested fork whose intermediate world finished, savepoint instances after the
  owner wrote, a finished fork's token ending) with the refinement checked after every step and
  after pruning every row, and on two mutants each check must reject."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [spindel.v2.layer2.mvcc :as m]))

(def theorems
  '[mv-vat-pres mv-look-prune mv-prune-covered
    mv-write-ref mv-write-inv mv-prune-ref mv-prune-inv mv-copy-inv mv-create-inv
    mv-fork-res-c mv-fork-inv mv-inst-res-c mv-inst-inv mv-finish-inv mv-drop-inv mv-collect-inv
    mv-reach-good mv-init-good mv-refinement mv-no-missing-version mv-tokens-live
    mi-reach-inv mi-protocol mi-start])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

;; ---------------------------------------------------------------------------
;; Running the compiled model

(def ^:private worlds (range 0 12))
(def ^:private ids (range 1 6))

(defn- rd [s w i] (m/mv-res (:h s) (:home s) w ((:fam s) w) i))

(defn- ref-bad
  "Every (world, id, read, table) where an active world does not read its table."
  [s]
  (vec (for [w worlds :when ((:act s) w) i ids :when (((:dom s) w) i)
             :let [r (rd s w i) t (((:tab s) w) i)] :when (not= r t)]
         [w i r t])))

(defn- prune-all [s] (reduce m/mv-prune s (range 1 (:n s))))

(defn- step-ok? [s] (and (empty? (ref-bad s)) (empty? (ref-bad (prune-all s)))))

;; `resolve-row` then the change: own-copy! first when the world has neither the row nor a copy
(defn- wr [s w i y]
  (let [own? (= w (:ow ((:h s) ((:home s) i))))
        s (if (or own? (not= 0 ((:fwd ((:fam s) w)) i))) s (m/mv-copy s w i (rd s w i)))]
    (m/mv-write s w i y)))

(def ^:private s0 m/mv-init)

(defn- run-checked [s steps]
  (reduce (fn [s [label f]]
            (let [s (f s)]
              (is (step-ok? s) label)
              s))
          s steps))

(deftest fork-while-work-is-in-flight
  (let [s (run-checked s0 [["create 1" #(m/mv-create % 0 1 10)] ["create 2" #(m/mv-create % 0 2 20)]
                           ["fork" #(m/mv-fork % 0 1 100 false)]
                           ["parent writes 1" #(wr % 0 1 11)] ["child writes 2" #(wr % 1 2 21)]
                           ["parent writes 2" #(wr % 0 2 22)] ["parent writes 1 again" #(wr % 0 1 12)]])]
    (is (= [10 21 12 22] [(rd s 1 1) (rd s 1 2) (rd s 0 1) (rd s 0 2)]))))

(deftest nested-fork-with-a-released-intermediate
  (let [s (run-checked s0 [["create" #(-> % (m/mv-create 0 1 10) (m/mv-create 0 2 20) (m/mv-create 0 3 30))]
                           ["B" #(m/mv-fork % 0 1 100 false)] ["B copies 1" #(wr % 1 1 11)]
                           ["B forks C" #(m/mv-fork % 1 2 101 false)] ["B writes 1 after C" #(wr % 1 1 111)]
                           ["B finishes (its token is shared: C reads through it)" #(m/mv-finish % 1)]
                           ["root writes 2" #(wr % 0 2 22)] ["root writes 1" #(wr % 0 1 13)]
                           ["B collected" #(m/mv-drop % 1)] ["C writes 3" #(wr % 2 3 33)]])]
    (is (= [11 20 33] [(rd s 2 1) (rd s 2 2) (rd s 2 3)]))
    (is (= 1 ((:ts s) 100)) "B's token stays shared (sticky)")))

(deftest savepoint-instances-after-the-owner-writes
  (let [s (run-checked s0 [["create" #(-> % (m/mv-create 0 1 10) (m/mv-create 0 2 20))]
                           ["publish: basis 1" #(m/mv-fork % 0 1 100 true)] ["owner writes 1" #(wr % 0 1 11)]
                           ["instance 2" #(m/mv-inst % 1 2)] ["instance writes 1" #(wr % 2 1 12)]
                           ["owner writes 2" #(wr % 0 2 21)] ["instance 3" #(m/mv-inst % 1 3)]
                           ["dispose the basis" #(m/mv-drop % 1)] ["owner writes 2 again" #(wr % 0 2 23)]])]
    (is (= [12 20 10 20] [(rd s 2 1) (rd s 2 2) (rd s 3 1) (rd s 3 2)]))))

(deftest a-finished-unshared-fork-keeps-no-version
  (let [s (run-checked s0 [["create" #(m/mv-create % 0 1 10)] ["fork" #(m/mv-fork % 0 1 100 false)]
                           ["child finishes" #(m/mv-finish % 1)] ["parent writes" #(wr % 0 1 11)]])]
    (is (= 2 ((:ts s) 100)) "the token ended")
    (is (empty? (:vers ((:h s) 1))) "the owner saved no version for it")))

(deftest the-checks-reject-mutants
  (testing "finishing a shared token strands the grandchild"
    (with-redefs [m/mv-fin (fn [ts l] (if (seq l) (m/mv-upd ts (:tok (first l)) 2) ts))]
      (let [s (-> s0 (m/mv-create 0 1 10) (m/mv-create 0 2 20) (m/mv-fork 0 1 100 false)
                  (m/mv-fork 1 2 101 false) (m/mv-finish 1) (wr 0 2 22))]
        (is (= [[2 2 nil 20]] (ref-bad s)) "no version for a live fork"))))
  (testing "a write without the barrier shows the child the parent's newer value"
    (with-redefs [m/mv-pres (fn [cs ts o x] x)]
      (let [s (-> s0 (m/mv-create 0 1 10) (m/mv-fork 0 1 100 false) (wr 0 1 11))]
        (is (= [[1 1 11 10]] (ref-bad s)))))))
