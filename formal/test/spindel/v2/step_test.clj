(ns spindel.v2.step-test
  "Loading spindel.v2.step kernel-checks every transition lemma (a failing proof throws at
  load). The deftests check the named theorems are in the kernel env, run scripted scenarios
  through the compiled `dispatch`, and drive it with random items, checking inv-sample after
  every step and that every refusal leaves the world unchanged."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.edits :as e]
            [spindel.v2.step :as st]))

(def theorems
  '[;; appended to edits.clj
    tbl-del-filter tbl-all-filter tbl-all-filter-self filter-ids-nodup-mid filter-ids-range-mid
    scope-filter-ids-ok run-filter-ids-ok edge-filter-ids-ok act-filter-ids-ok resource-filter-ids-ok
    run-del-ids-ok edge-del-ids-ok act-del-ids-ok resource-del-ids-ok
    comp-upd-ids-ok run-upd-ids-ok edge-upd-ids-ok source-upd-ids-ok fork-upd-ids-ok
    ids-ok-cleanup-del ids-ok-set-pins source-upd-edges-ref-ok task-upd-edges-ref-ok
    act-upd-edges-ref-ok source-ins-edges-ref-ok remove-edge-ids-ok
    marked-in-filter-ne marked-in-filter-eq drop-cred-pending-exact drop-cred-edges-ref-ok
    drop-cred-ids-ok act-del-edges-ref-ok
    inv-run-upd inv-scope-upd inv-resource-upd inv-pub-upd inv-source-upd inv-task-upd
    inv-act-upd inv-comp-upd inv-edge-upd inv-cleanup-upd inv-cleanup-del inv-set-pins
    inv-run-del inv-resource-del inv-source-ins-fresh inv-resource-ins-fresh
    inv-remove-edge inv-drop-cred inv-drop-act nat-fold-inv tbl-find-has
    ;; step.clj
    run-tok-none res-tok-none inv-resume inv-fill-slot inv-invalidate inv-fire-dep
    inv-fire-wait inv-fire-observe inv-fire-edge inv-create-source-raw inv-write-raw
    inv-track-raw track-edge-ok inv-retire inv-retire-check inv-ack-raw
    t1-inv t1-refuse t1-l4 t1-top-inv t1-top-refuse t2-inv t2-refuse t7-inv t7-refuse t7-l4
    t8-observe-inv t8-observe-refuse t8-unobserve-inv t8-unobserve-refuse
    t9-inv t9-refuse t9-l4 t15-inv t15-refuse t15-l4 t17-inv t17-refuse t17-l4
    t18-inv t18-refuse t18-l4 t19-inv t19-refuse t20-pin-inv t20-pin-refuse t20-unpin-inv t20-unpin-refuse pin-count-pos
    dispatch-inv dispatch-refuse dispatch-l4 run-items-inv run-items-from-empty])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t))))
        (str t))))

;; ---------------------------------------------------------------------------
;; Items (tagged runtime representation: [constructor-index field ...])

(defn create-source [st kind v fresh] [0 st kind v fresh])
(defn create-source-top [scope kind v fresh] [1 scope kind v fresh])
(defn write [x v] [2 x v])
(defn track [st x k fresh] [3 st x k fresh])
(defn observe [d cb fresh] [4 d cb fresh])
(defn unobserve [ed] [5 ed])
(defn fire [ed tag v] [6 ed tag v])
(defn resource-ack [z] [7 z])
(defn arm [st kind k fresh] [8 st kind k fresh])
(defn resource-fire [z tag v] [9 z tag v])
(defn handle-drop [x] [10 x])
(defn pin [x] [11 x])
(defn unpin [x] [12 x])

;; ---------------------------------------------------------------------------
;; World construction (rows the batch's items cannot create yet: scopes, comps, tasks, runs,
;; activations, comp->comp dep edges), always with the fresh id from the allocator

(def no-result (s/->RunResult s/res-none 0))

(defn add-row [w ins mk] (let [id (:next-id w)] [id (s/bump (ins w (mk id)))]))
(defn add-scope [w parent kind] (add-row w s/scope-ins #(s/->ScopeRow % parent kind true)))
(defn add-comp [w owner]
  (add-row w s/comp-ins #(s/->CompRow % owner [] 0 0 1 1 0 0 0 no-result false [] [] [] [] 1)))
(defn add-task [w owner] (add-row w s/task-ins #(s/->TaskRow % owner 0 no-result 1 [])))
;; stamp = 1000 + id, so stamps and ids differ
(defn add-run [w of scope & {:keys [slice act epoch] :or {slice true act s/act-active epoch 1}}]
  (add-row w s/run-ins #(s/->RunRow % of (+ 1000 %) epoch scope act s/mode-normal slice 0 [] [])))
(defn add-act [w run members]
  (add-row w s/act-ins #(s/->ActRow % run s/am-one (vec (map-indexed (fn [i m] (s/->Member m i)) members)) (vec (repeat (count members) (s/->RunResult s/res-none 0))) (count members) 77 [])))
(defn edge-row [kind creditor debtor]
  (s/->EdgeRow 0 kind creditor debtor s/cont-restart 0 s/ph-armed false false 0 false 0 0))
(defn add-edge [w kind creditor debtor]
  (let [id (:next-id w)] [id (e/insert-edge-fresh w (edge-row kind creditor debtor))]))
(defn set-comp-run [w c r]
  (s/comp-upd w c (fn [row] (assoc row :run r))))

(defn find-row [w field id] (first (filter #(= id (:id %)) (get w field))))
(defn stamp [w r] (:stamp (find-row w :runs r)))

(defn reference-pending [w]
  (into {} (for [c (:comps w)]
             [(:id c) (count (filter #(and (= (:creditor %) (:id c)) (:marked %)) (:edges w)))])))

(defn ok? [w]
  (and (e/inv-sample w) (= (reference-pending w) (into {} (map (juxt :id :pending) (:comps w))))))

(defn step [w item] (st/dispatch w item))

(defn base-world
  "root scope 1; computations C (run RC) and D (run RD); task K (run RK, own run scope)."
  []
  (let [w s/empty-world
        root s/root-scope-id
        [c w] (add-comp w root)
        [rc w] (add-run w c root)
        w (set-comp-run w c rc)
        [d w] (add-comp w root)
        [rd w] (add-run w d root :slice false)
        w (set-comp-run w d rd)
        [k w] (add-task w root)
        [sk w] (add-scope w root s/scope-run)
        [rk w] (add-run w k sk)]
    {:w w :root root :c c :rc rc :d d :rd rd :k k :sk sk :rk rk}))

;; ---------------------------------------------------------------------------
;; Scripted scenarios

(deftest create-track-write
  (let [{:keys [w root c rc d]} (base-world)]
    (is (ok? w))
    (testing "T1 top level: a signal owned by the given scope"
      (let [x (:next-id w)
            o (step w (create-source-top root s/sk-signal 10 x))
            w (:world o)
            src (find-row w :sources x)]
        (is (:accepted o))
        (is (= [root s/sk-signal 10 0 true 1]
               ((juxt :owner :kind :state :version :open :handles) src)))
        (is (ok? w))
        (testing "T7 inside a computation: dep edge with baseline, effect-index advances"
          (let [ed (:next-id w)
                o (step w (track (stamp w rc) x 55 ed))
                w (:world o)
                edge (find-row w :edges ed)]
            (is (:accepted o))
            (is (= [s/ek-dep c x 55 0 s/ph-armed false true 10 0]
                   ((juxt :kind :creditor :debtor :cont :at :phase :marked :has-base :base-value :base-version) edge)))
            (is (= 1 (:effect-index (find-row w :runs rc))))
            (is (ok? w))
            (testing "T2 write: the track edge fires (invalidation) and D's in-edge on C is marked"
              (let [[dc w] (add-edge w s/ek-dep d c)   ; D depends on C
                    ob (:next-id w)
                    w (:world (step w (observe x 99 ob)))
                    o (step w (write x 11))
                    w2 (:world o)]
                (is (:accepted o))
                (is (= [11 1] ((juxt :state :version) (find-row w2 :sources x))))
                (is (= s/ph-fired (:phase (find-row w2 :edges ed))) "track edge fired, stays as re-entry point")
                (is (= 2 (:epoch (find-row w2 :comps c))) "invalidation is an epoch step")
                (is (true? (:marked (find-row w2 :edges dc))))
                (is (= 1 (:pending (find-row w2 :comps d))))
                (is (= 0 (:pending (find-row w2 :comps c))) "the edge onto a source is not marked")
                (is (= 1 (:seen (find-row w2 :edges ob))) "observe edge delivered version 1")
                (is (= s/ph-armed (:phase (find-row w2 :edges ob))) "observe edges are persistent")
                (is (true? (:converged (st/dirty-run w x))))
                (is (= #{c d} (set (st/dirty-set w x))))
                (is (ok? w2))
                (testing "a second write: the fired edge does not fire again; marking is idempotent"
                  (let [w3 (:world (step w2 (write x 12)))]
                    (is (= 2 (:epoch (find-row w3 :comps c))))
                    (is (= 1 (:pending (find-row w3 :comps d))))
                    (is (= 2 (:seen (find-row w3 :edges ob))))
                    (is (ok? w3))))
                (testing "unobserve removes the observe edge; unobserve of a dep edge refuses"
                  (let [o (step w2 (unobserve ob))]
                    (is (:accepted o))
                    (is (nil? (find-row (:world o) :edges ob)))
                    (is (ok? (:world o))))
                  (is (false? (:accepted (step w2 (unobserve dc))))))))))))))

(deftest create-source-in-runs
  (let [{:keys [w c rc rk sk]} (base-world)]
    (testing "inside a computation run: owner = the computation, recorded in its basis"
      (let [x (:next-id w)
            w (:world (step w (create-source (stamp w rc) s/sk-cell 3 x)))]
        (is (= c (:owner (find-row w :sources x))))
        (is (= [[x 0]] (map (juxt :id :at) (:basis (find-row w :comps c)))))
        (is (ok? w))))
    (testing "inside a task run: owner = the run scope, no basis"
      (let [x (:next-id w)
            w (:world (step w (create-source (stamp w rk) s/sk-mailbox 3 x)))]
        (is (= sk (:owner (find-row w :sources x))))
        (is (ok? w))))
    (testing "T7 inside a task: snapshot read, no edge"
      (let [x (:next-id w)
            w (:world (step w (create-source-top 2 s/sk-signal 0 x)))
            o (step w (track (stamp w rk) x 5 0))]
        (is (:accepted o))
        (is (= (:edges w) (:edges (:world o))))
        (is (= 1 (:effect-index (find-row (:world o) :runs rk))))))))

(deftest await-fire-resume
  (testing "T9 on a wait edge of a `one` activation resumes the run"
    (let [{:keys [w k rk]} (base-world)
          [k2 w] (add-task w 2)
          [a w] (add-act w rk [])
          [ed w] (add-edge w s/ek-wait a k2)
          w (s/act-upd w a #(assoc % :members [(s/->Member ed 0)]))
          w (s/run-upd w rk #(assoc % :act s/act-parked))
          _ (is (ok? w))
          o (step w (fire ed s/res-ok 7))
          w2 (:world o)]
      (is (:accepted o))
      (is (nil? (find-row w2 :acts a)) "activation removed on resume")
      (is (nil? (find-row w2 :edges ed)) "wait member removed with it")
      (is (= s/act-active (:act (find-row w2 :runs rk))))
      (is (ok? w2))
      (testing "fire token: a missing or already fired edge is a no-op"
        (is (= w2 (:world (step w2 (fire ed s/res-ok 7)))))
        (is (false? (:accepted (step w2 (fire ed s/res-ok 7))))))))
  (testing "T9 on a dep edge that is a member of the current run's activation: delivery"
    (let [{:keys [w c rc]} (base-world)
          x (:next-id w)
          w (:world (step w (create-source-top 2 s/sk-signal 4 x)))
          [ed w] (add-edge w s/ek-dep c x)
          [a w] (add-act w rc [ed])
          w (s/run-upd w rc #(assoc % :act s/act-parked))
          w (s/source-upd w x #(assoc % :state 9 :version 3))
          w2 (:world (step w (fire ed s/res-ok 9)))
          edge (find-row w2 :edges ed)]
      (is (= [s/ph-armed true 9 3] ((juxt :phase :has-base :base-value :base-version) edge))
          "re-armed with the new baseline")
      (is (nil? (find-row w2 :acts a)))
      (is (= 1 (:epoch (find-row w2 :comps c))) "a delivery is not an epoch step")
      (is (= s/act-active (:act (find-row w2 :runs rc))))
      (is (ok? w2))))
  (testing "a wait fire into a stale run is not delivered: the edge stays fired"
    (let [{:keys [w c rc]} (base-world)
          [k2 w] (add-task w 2)
          [a w] (add-act w rc [])
          [ed w] (add-edge w s/ek-wait a k2)
          w (s/comp-upd w c #(assoc % :epoch 5))
          w2 (:world (step w (fire ed s/res-ok 1)))]
      (is (= s/ph-fired (:phase (find-row w2 :edges ed))))
      (is (some? (find-row w2 :acts a)))
      (is (ok? w2)))))

(deftest arm-fire-ack-retire
  ;; Z#55: the `arm` item (resource + park) is engine's; here the resource part `arm-raw` (T17
  ;; proper), then T18/T15 through dispatch
  (let [{:keys [w rk sk]} (base-world)
        z (:next-id w)
        w (st/arm-raw w (find-row w :runs rk) s/rk-timer)]
    (is (= [rk s/rk-timer 0 s/rp-armed] ((juxt :owner :kind :at :phase) (find-row w :res z))))
    (is (= [z] (:resources (find-row w :runs rk))))
    (is (ok? w))
    (testing "T18: armed -> fired exactly once"
      (let [o (step w (resource-fire z s/res-ok 1))
            w2 (:world o)]
        (is (:accepted o))
        (is (= s/rp-fired (:phase (find-row w2 :res z))))
        (is (false? (:accepted (step w2 (resource-fire z s/res-ok 1)))))
        (is (ok? w2))
        (testing "T15 + T13: the run completed, the last resource joins, the run retires"
          (let [w3 (s/run-upd w2 rk #(assoc % :act s/act-done :slice false))
                w3 (s/cleanup-ins w3 (s/->CleanupRow rk [z]))
                o (step w3 (resource-ack z))
                w4 (:world o)]
            (is (:accepted o))
            (is (nil? (find-row w4 :res z)))
            (is (nil? (find-row w4 :runs rk)) "retired: run row removed")
            (is (empty? (filter #(= rk (:run %)) (:cleanup w4))) "cleanup[R] removed")
            (is (false? (:open (find-row w4 :scopes sk))) "run scope closed (shallow T16 stub)")
            (is (ok? w4))))
        (testing "T15 on a running run: resource removed, run not retired"
          (let [w4 (:world (step w2 (resource-ack z)))]
            (is (nil? (find-row w4 :res z)))
            (is (= [] (vec (:resources (find-row w4 :runs rk)))))
            (is (some? (find-row w4 :runs rk)))
            (is (ok? w4))))))
    (testing "T18 fires the wait edge parked on the resource (outside edges-ref-ok, see ns doc)"
      (let [[a w] (add-act w rk [])
            [ed w] (add-edge w s/ek-wait a z)
            w2 (:world (step w (resource-fire z s/res-ok 1)))]
        (is (true? (e/edges-ref-ok w)) "Z#6: a wait edge admits a resource debtor")
        (is (false? (st/ack-tok-ok w z)) "Z#6: no acknowledgement while an edge is on Z")
        (is (false? (:accepted (step w (resource-ack z)))))
        (is (nil? (find-row w2 :acts a)))
        (is (nil? (find-row w2 :edges ed)))))))

(deftest pins-and-handles
  (let [{:keys [w c]} (base-world)
        x (:next-id w)
        w (:world (step w (create-source-top 2 s/sk-signal 0 x)))]
    (testing "T20 (Z#16): pins count; unknown ids refuse; unpin decrements; unpin at 0 refuses"
      (let [w1 (:world (step w (pin x)))
            w2 (:world (step w1 (pin x)))
            w3 (:world (step w2 (pin c)))
            w4 (:world (step w3 (unpin x)))]
        (is (= [x] (vec (:pins w1))))
        (is (= 2 (st/pin-count x (:pins w2))))
        (is (= {x 2 c 1} (frequencies (:pins w3))))
        (is (false? (:accepted (step w (pin 999)))))
        (is (= {x 1 c 1} (frequencies (:pins w4))))
        (is (= {c 1} (frequencies (:pins (:world (step w4 (unpin x)))))))
        (is (false? (:accepted (step w (unpin x)))) "count 0")
        (is (every? ok? [w1 w2 w3 w4]))))
    (testing "T19 handle-drop decrements; at 0 it refuses"
      (let [o1 (step w (handle-drop x))
            o2 (step (:world o1) (handle-drop x))
            o3 (step w (handle-drop c))]
        (is (:accepted o1))
        (is (= 0 (:handles (find-row (:world o1) :sources x))))
        (is (false? (:accepted o2)))
        (is (= 0 (:handles (find-row (:world o3) :comps c))))
        (is (false? (:accepted (step w (handle-drop 999)))))))))

(deftest invalid-tokens-and-fresh-ids
  (let [{:keys [w rc rd]} (base-world)
        x (:next-id w)
        w (:world (step w (create-source-top 2 s/sk-signal 0 x)))
        n (:next-id w)
        refused-unchanged (fn [item]
                            (let [o (step w item)]
                              (is (false? (:accepted o)) (pr-str item))
                              (is (= w (:world o)) (pr-str item))))]
    (testing "L4: invalid tokens"
      (is (false? (st/run-tok-ok w 424242)))
      (refused-unchanged (track 424242 x 1 n))
      (refused-unchanged (create-source 424242 s/sk-signal 0 n))
      (refused-unchanged (arm 424242 s/rk-timer 0 n))
      (is (false? (st/run-tok-ok w (stamp w rd))) "a run without a slice holds no valid token")
      (refused-unchanged (track (stamp w rd) x 1 n))
      (refused-unchanged (fire 424242 s/res-ok 0))
      (refused-unchanged (resource-ack 424242))
      (refused-unchanged (resource-fire 424242 s/res-ok 0)))
    (testing "an unwinding run is valid only with a head finalizer"
      (let [w1 (s/run-upd w rc #(assoc % :mode s/mode-unwinding))
            w2 (s/run-upd w1 rc #(assoc % :finalizers [(s/->Finalizer 9 0 [])]))]
        (is (false? (st/run-tok-ok w1 (stamp w rc))))
        (is (true? (st/run-tok-ok w2 (stamp w rc))))))
    (testing "a fresh id other than next-id refuses"
      (refused-unchanged (create-source (stamp w rc) s/sk-signal 0 (inc n)))
      (refused-unchanged (create-source-top 2 s/sk-signal 0 (inc n)))
      (refused-unchanged (track (stamp w rc) x 1 (inc n)))
      (refused-unchanged (observe x 1 (inc n)))
      (refused-unchanged (arm (stamp w rc) s/rk-timer 0 (inc n)))
      (refused-unchanged (arm (stamp w rc) s/rk-timer 0 n)) "Z#55: dispatch refuses arm (it needs engine's park)")
    (testing "other refusals"
      (refused-unchanged (write 999 1))
      (refused-unchanged (create-source-top 2 9 0 n))
      (refused-unchanged (observe 999 1 n))
      (refused-unchanged (track (stamp w rc) 999 1 n)))))

;; ---------------------------------------------------------------------------
;; Random items

(defn random-world [rng]
  (let [{:keys [w c d k rc rk]} (base-world)
        [e1 w] (add-edge w s/ek-dep d c)
        [k2 w] (add-task w 2)
        [r2 w] (add-run w k2 2)
        [a w] (add-act w rk [])
        [ew w] (add-edge w s/ek-wait a k2)
        w (s/act-upd w a #(assoc % :members [(s/->Member ew 0)]))
        ;; Z#55: dispatch refuses `arm` (engine's item), so T15/T18 get a resource of rc's from T17 proper
        w (st/arm-raw w (find-row w :runs rc) s/rk-timer)]
    w))

(defn random-item [rng w]
  (let [pick (fn [xs] (if (seq xs) (nth (vec xs) (.nextInt rng (count xs))) 0))
        n (:next-id w)
        fresh (if (< (.nextInt rng 10) 8) n (inc n))
        id (fn [] (if (< (.nextInt rng 10) 8) (pick (s/all-ids w)) (+ n (.nextInt rng 3))))
        st (fn [] (if (< (.nextInt rng 10) 8) (pick (map :stamp (:runs w))) 4242))
        srcs (map :id (:sources w))
        src (fn [] (if (and (seq srcs) (< (.nextInt rng 10) 8)) (pick srcs) (id)))
        edges (map :id (:edges w))
        res (map :id (:res w))
        v (.nextInt rng 20)]
    (case (.nextInt rng 13)
      0 (create-source (st) (.nextInt rng 6) v fresh)
      1 (create-source-top (pick (map :id (:scopes w))) (.nextInt rng 6) v fresh)
      2 (write (src) v)
      3 (track (st) (src) v fresh)
      4 (observe (id) v fresh)
      5 (unobserve (pick edges))
      6 (fire (if (seq edges) (pick edges) (id)) s/res-ok v)
      7 (resource-ack (if (seq res) (pick res) (id)))
      8 (arm (st) (.nextInt rng 5) v fresh)
      9 (resource-fire (if (seq res) (pick res) (id)) s/res-ok v)
      10 (handle-drop (id))
      11 (pin (id))
      12 (unpin (pick (:pins w))))))

(deftest random-items
  (let [rng (java.util.Random. 20261104)
        accepted (atom (vec (repeat 13 0)))]
    (dotimes [run 25]
      (loop [i 0 w (random-world rng)]
        (when (< i 60)
          (let [item (random-item rng w)
                o (step w item)
                w2 (:world o)]
            (when (:accepted o) (swap! accepted update (first item) inc))
            (when-not (:accepted o)
              (is (= w w2) (str "refusal changed the world: " (pr-str item))))
            (when (= 2 (first item))
              (is (true? (:converged (st/dirty-run w (second item))))))
            (is (ok? w2) (str "run " run " step " i " " (pr-str item)))
            (recur (inc i) w2)))))
    (testing "every item kind but arm (Z#55: engine's item, refused by dispatch) was accepted at least once"
      (is (every? pos? (assoc @accepted 8 1)) (pr-str @accepted))
      (is (zero? (nth @accepted 8))))))
