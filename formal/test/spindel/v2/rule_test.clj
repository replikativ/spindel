(ns spindel.v2.rule-test
  "Loading spindel.v2.rule kernel-checks the cancel family, Rule R normalization and the step
  theorems. The deftests run scripted scenarios through the compiled transitions and drive
  `world-step` (and T14/T16 followed by Rule R) with random items, checking after every step:
  inv-sample with a plain pending count, the honest hypotheses (live converged before and after
  the filter, the loop's `normalized` flag, `filter-safe`, the cascade emptied its worklist),
  I3 and I4 against the plain-Clojure BFS of spindel.v2.retain-test, and that every
  normalization round strictly decreases #non-done runs + #non-idle computations."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.set :as set]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.edits :as e]
            [spindel.v2.retain :as rt]
            [spindel.v2.step :as st]
            [spindel.v2.rule :as r]
            [spindel.v2.engine :as en]
            [spindel.v2.retain-test :as rtt]))

(def theorems
  '[resync-exact resync-ids resync-has inv-drop-edges drop-edges-avoids inv-comp-del-unref
    inv-scope-del inv-cleanup-ins
    inv-close-local inv-remove-if-empty inv-debtor-side inv-cancel-run-local inv-clear-comp-run
    inv-retire-local inv-close-scope-local inv-job-apply inv-cascade inv-run-cascade
    t14-inv t14-refuse t16-inv t16-refuse t15-full-inv t15-full-refuse t15-full-l4
    inv-demote-finish inv-demote inv-detach inv-norm-round inv-norm-loop inv-normalize
    raw-inv raw-refuse raw-l4 step-refuse step-l4 step-accepted
    tbl-all-keep tbl-all-keep2 tbl-has-keep marked-in-keep edge-ok-keep ids-keep all-ids-keep
    nodup-filter ids-ok-keep inv-filter-world inv-rule-r-filter inv-rule-r step-inv
    tbl-all-mem normalized-runs normalized-comps rule-r-filter-normalized rule-r-i3-step
    rule-r-normalized step-i3 step-normalized step-i4
    inv-fin-loop inv-finalize-one inv-clear-task-run inv-detach-comp inv-rule-r-round rr-loop-eq rule-r-eq
    inv-rr-loop])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t))))
        (str t))))

;; ---------------------------------------------------------------------------
;; World construction (fresh ids from the allocator)

(def no-result (s/->RunResult s/res-none 0))
(def ok-result (s/->RunResult s/res-ok 3))

(defn add-row [w ins mk] (let [id (:next-id w)] [id (s/bump (ins w (mk id)))]))
(defn add-scope [w parent kind] (add-row w s/scope-ins #(s/->ScopeRow % parent kind true)))
(defn add-comp [w owner & {:keys [handles result] :or {handles 1 result no-result}}]
  (add-row w s/comp-ins #(s/->CompRow % owner [] 0 0 1 (if (= s/res-none (:tag result)) 0 1) 0 0 0
                                      result false [] [] [] [] handles)))
(defn add-task [w owner] (add-row w s/task-ins #(s/->TaskRow % owner 0 no-result 1 [])))
(defn add-run [w of scope & {:keys [slice act epoch] :or {slice false act s/act-active epoch 1}}]
  (add-row w s/run-ins #(s/->RunRow % of (+ 1000 %) epoch scope act s/mode-normal slice 0 [] [])))
(defn add-act [w run] (add-row w s/act-ins #(s/->ActRow % run s/am-one [] [(s/->RunResult s/res-none 0)] 1 77 [])))
(defn edge-row [kind creditor debtor] (s/->EdgeRow 0 kind creditor debtor s/cont-restart 0 s/ph-armed false false 0 false 0 0))
(defn add-edge [w kind creditor debtor]
  (let [id (:next-id w)] [id (e/insert-edge-fresh w (edge-row kind creditor debtor))]))
(defn add-source [w owner] (let [x (:next-id w)] [x (:world (st/dispatch w [1 owner s/sk-signal 0 x]))]))
(defn add-resource [w run]
  (let [z (:next-id w)]
    [z (s/run-upd (s/bump (s/resource-ins w (s/->ResRow z run s/rk-timer 0 s/rp-armed))) run
                  #(update % :resources conj z))]))

;; a task with a run and its own run scope under `owner`
(defn add-task-run [w owner & opts]
  (let [[k w] (add-task w owner)
        [sk w] (add-scope w owner s/scope-run)
        [rk w] (apply add-run w k sk opts)
        w (s/task-upd w k #(assoc % :run rk))]
    [k sk rk w]))
;; a computation with its current run (own run scope)
(defn add-comp-run [w owner & {:keys [handles result act] :or {handles 1 result no-result act s/act-parked}}]
  (let [[c w] (add-comp w owner :handles handles :result result)
        [sc w] (add-scope w owner s/scope-run)
        [rc w] (add-run w c sc :act act)
        w (s/comp-upd w c #(assoc % :run rc))]
    [c sc rc w]))
;; park run `run` on a one-activation with a wait edge on `debtor`
(defn park-on [w run debtor]
  (let [[a w] (add-act w run)
        [ed w] (add-edge w s/ek-wait a debtor)
        w (s/act-upd w a #(assoc % :members [(s/->Member ed 0)]))
        w (s/run-upd w run #(assoc % :act s/act-parked))]
    [a ed w]))

(defn find-row [w field id] (first (filter #(= id (:id %)) (get w field))))
(defn ids [w] (set (s/all-ids w)))

(defn reference-pending [w]
  (into {} (for [c (:comps w)]
             [(:id c) (count (filter #(and (= (:creditor %) (:id c)) (:marked %)) (:edges w)))])))
(defn ok? [w]
  (and (e/inv-sample w) (= (reference-pending w) (into {} (map (juxt :id :pending) (:comps w))))))

;; I3 / I4 / normalized against the plain BFS of retain-test
(defn ref-i3? [w] (set/subset? (ids w) (rtt/ref-keep w)))
(defn ref-normalized? [w]
  (let [lv (rtt/ref-live w)]
    (and (every? #(or (= s/act-done (:act %)) (lv (:id %))) (:runs w))
         (every? #(or (:idle %) (lv (:id %))) (:comps w)))))

(defn rule-r-checks
  "The honest hypotheses and the conclusions for Rule R applied to w (an accepted raw world)."
  [w msg]
  (let [pre (r/rule-r-pre w)
        n (r/normalize pre)
        w' (rt/rule-r-filter n)]
    (is (= w' (r/rule-r w)) msg)
    (is (true? (r/rule-r-safe w)) (str "filter-safe in every round " msg))
    (is (true? (r/no-orphans w')) (str "no orphan after the final detach (Z#25) " msg))
    (is (true? (rt/live-converged n)) (str "converged before the filter " msg))
    (is (true? (rt/live-converged w')) (str "converged after the filter " msg))
    (is (true? (r/normalized n)) (str "normalized flag " msg))
    (is (true? (r/filter-safe n)) (str "filter-safe " msg))
    (is (ok? w') (str "inv-sample " msg))
    (is (ref-i3? w') (str "I3 " msg))
    (is (ref-normalized? w') (str "I4 + no stray computation " msg))
    (is (= (rtt/ref-live n) (set (rt/live-list n))) (str "live = reference " msg))
    (testing "each round strictly decreases the measure; the fuel suffices"
      (let [w0 (r/detach pre)
            ms (loop [x w0 acc [] k 0]
                 (if (or (r/normalized x) (> k 40)) (conj acc (r/norm-measure x))
                     (recur (r/norm-round x) (conj acc (r/norm-measure x)) (inc k))))]
        (is (apply > (conj ms -1)) (str "measure " ms " " msg))
        (is (<= (count ms) (count (r/norm-fuel w0))) msg)))
    w'))

;; ---------------------------------------------------------------------------
;; Scripted scenarios

(deftest cancel-parked-task-run
  ;; task K (run RK, parked on a source, holding a resource) is awaited by task K3
  (let [w s/empty-world
        root s/root-scope-id
        [x w] (add-source w root)
        [k sk rk w] (add-task-run w root)
        [a ew w] (park-on w rk x)
        [z w] (add-resource w rk)
        [k3 sk3 rk3 w] (add-task-run w root)
        [a3 e3 w] (park-on w rk3 k)
        _ (is (ok? w))
        o (r/t14-cancel w rk false)
        w2 (:world o)]
    (is (:accepted o))
    (is (true? (r/casc-done w [[0 rk false]])))
    (is (= [s/act-done s/mode-unwinding] ((juxt :act :mode) (find-row w2 :runs rk))))
    (is (nil? (find-row w2 :acts a)) "R's activation removed")
    (is (nil? (find-row w2 :edges ew)) "with its wait member")
    (is (= s/rp-cancelling (:phase (find-row w2 :res z))) "resource told to cancel")
    (is (some #(= rk (:run %)) (:cleanup w2)) "cleanup[R] (not retirable: a resource is outstanding)")
    (is (= [s/res-err r/cancelled-code] ((juxt :tag :val) (:result (find-row w2 :tasks k))))
        "the task completes with err ::cancelled")
    (is (nil? (find-row w2 :acts a3)) "the wait creditor received the error: its one-activation resumed")
    (is (= s/act-active (:act (find-row w2 :runs rk3))))
    (is (ok? w2))
    (is (false? (:accepted (r/t14-cancel w2 rk false))) "a done run is not cancelled again")
    (testing "Z#14: a cancelling resource does not fire; T15 then retires the run (Z#18)"
      (is (false? (:accepted (en/world-step w2 [9 z s/res-ok 0]))))
      (let [o (en/raw w2 [7 z])
            w3 (:world o)]
        (is (:accepted o))
        (is (nil? (find-row w3 :runs rk)) "retired")
        (is (not-any? #(= rk (:run %)) (:cleanup w3)) "cleanup[R] removed")
        (is (nil? (find-row w3 :scopes sk)) "its empty run scope removed")
        (is (ok? w3))
        (rule-r-checks w3 "after ack")))
    (testing "Z#6: an acknowledgement with an edge on the resource refuses"
      (let [[a4 e4 w4] (park-on w2 rk3 z)]
        (is (false? (st/ack-tok-ok w4 z)))
        (is (= (st/->Outcome w4 false) (en/world-step w4 [7 z])) "L4: refused, unchanged")))
    ;; Y#2: cancel(R, replace) is T11's replacement of a computation's run ("the computation's
    ;; creditors keep waiting"); it is never issued for a task run, where the model applies the
    ;; ordinary debtor side (the task gets err ::cancelled), so a cancelled task always has its
    ;; result (literal I10, spindel.v2.lit). Before branch `lit` this test asserted no debtor side.
    (testing "a replacement cancel of a task run is an ordinary cancel"
      (let [w5 (:world (r/t14-cancel w rk true))
            w6 (:world (r/t14-cancel w rk false))]
        (is (= (:result (find-row w6 :tasks k)) (:result (find-row w5 :tasks k))))
        (is (= s/res-err (:tag (:result (find-row w5 :tasks k)))))
        (is (ok? w5))))))

(deftest cascade-through-scope-tree
  ;; root > task K1 (run R1, scope S1) > explicit scope E > task K2 (R2, S2) > task K3 (R3, S3)
  (let [w s/empty-world
        root s/root-scope-id
        [k1 s1 r1 w] (add-task-run w root)
        [ex w] (add-scope w s1 s/scope-explicit)
        [k2 s2 r2 w] (add-task-run w ex)
        [k3 s3 r3 w] (add-task-run w s2)
        [x w] (add-source w s2)]
    (is (= #{s1 ex s2 s3} (set (r/scope-subtree w s1))))
    (is (= #{r2 r3} (set (r/owned-runs w (r/scope-subtree w s1)))))
    (testing "no finalizers: every run is cancelled and retires; the subtree goes"
      (let [w2 (:world (r/t14-cancel w r1 false))]
        (is (true? (r/casc-done w [[0 r1 false]])))
        (is (empty? (:runs w2)))
        (is (every? #(= s/res-err (:tag (:result (find-row w2 :tasks %)))) [k1 k2 k3]))
        (is (false? (:open (find-row w2 :sources x))) "a source owned by the subtree is closed")
        (is (nil? (find-row w2 :scopes s3)) "an empty run scope is removed")
        (is (false? (:open (find-row w2 :scopes s1))) "a scope still owning tasks stays closed")
        (is (ok? w2))
        (rule-r-checks w2 "cascade")))
    (testing "R2 holds a finalizer: it stays unwinding in cleanup; its scope keeps the tree"
      (let [w (s/run-upd w r2 #(assoc % :finalizers [(s/->Finalizer 9 0 [x])]))
            w2 (:world (r/t14-cancel w r1 false))]
        (is (= [s/act-done s/mode-unwinding] ((juxt :act :mode) (find-row w2 :runs r2))))
        (is (some #(= r2 (:run %)) (:cleanup w2)))
        (is (nil? (find-row w2 :runs r1)))
        (is (nil? (find-row w2 :runs r3)))
        (is (some? (find-row w2 :scopes s1)) "R2's run scope is in S1's subtree")
        (is (ok? w2))
        (let [w3 (rule-r-checks w2 "unwinding child")]
          (is (some? (find-row w3 :runs r2)) "kept by its cleanup entry")
          (is (some? (find-row w3 :sources x)) "the finalizer ref is kept"))))))

(deftest demote-unobserved-computation
  (doseq [[handles result] [[0 no-result] [1 no-result] [0 ok-result] [1 ok-result]]]
    (testing (str "handles " handles " result " (:tag result))
      (let [w s/empty-world
            root s/root-scope-id
            [x w] (add-source w root)
            [c sc rc w] (add-comp-run w root :handles handles :result result)
            [d w] (add-edge w s/ek-dep c x)
            _ (is (= [0 0] ((juxt :debtor :version) (r/edge-valid w (find-row w :edges d)))) "Z#24: never consumed -> failing entry")
            w (s/edge-upd w d #(assoc % :has-seen true :seen 0))   ; the edge consumed version 0
            [ob w] (add-edge w s/ek-observe 0 c)
            _ (is (r/normalized w))
            o (en/world-step w [5 ob])
            raw-w (:world (en/raw w [5 ob]))
            n (r/normalize raw-w)
            w2 (:world o)]
        (is (:accepted o))
        (rule-r-checks raw-w "demote")
        (is (nil? (find-row n :runs rc)) "its run is cancelled and retires")
        (is (nil? (find-row n :edges d)) "its dep edges are removed")
        (if (or (pos? handles) (= s/res-ok (:tag result)))
          (let [row (find-row n :comps c)]
            (is (true? (:idle row)))
            (is (= [0 [] [[x 0]]] [(:run row) (vec (:basis row)) (mapv (juxt :debtor :version) (:validity row))]))
            (is (= (pos? handles) (some? (find-row w2 :comps c))) "§3.4: kept while handles > 0"))
          (is (nil? (find-row n :comps c)) "no result, no handle: removed"))
        (is (some? (find-row w2 :sources x)))))))

(deftest close-scope-with-owned-sources
  (let [w s/empty-world
        root s/root-scope-id
        [ex w] (add-scope w root s/scope-explicit)
        [x w] (add-source w ex)]
    (testing "only a source: the scope closes and goes, the source is detached and closed"
      (let [w2 (:world (r/t16-close-scope w ex))]
        (is (nil? (find-row w2 :scopes ex)))
        (is (= [ex false] ((juxt :owner :open) (find-row w2 :sources x))))
        (let [w3 (rule-r-checks w2 "close")]
          (is (= [0 false] ((juxt :owner :open) (find-row w3 :sources x))) "detached, closed, kept by its handle"))))
    (testing "with a running task: its run is cancelled, the scope stays closed"
      (let [[k sk rk w] (add-task-run w ex)
            [y w] (add-source w sk)
            w2 (:world (r/t16-close-scope w ex))]
        (is (false? (:open (find-row w2 :scopes ex))))
        (is (nil? (find-row w2 :runs rk)))
        (is (false? (:open (find-row w2 :sources x))))
        (is (false? (:open (find-row w2 :sources y))))
        (is (ok? w2))
        (rule-r-checks w2 "close with task")))
    (is (false? (:accepted (r/t16-close-scope w 999))))))

(deftest stale-run-replaced
  ;; C (epoch 2) has a stale parked run RS and a current run RC; D depends on C; task T waits on C
  (let [w s/empty-world
        root s/root-scope-id
        [c sc rs w] (add-comp-run w root :act s/act-parked)
        [sc2 w] (add-scope w root s/scope-run)
        [rc w] (add-run w c sc2 :epoch 2 :act s/act-parked)
        w (s/comp-upd w c #(assoc % :epoch 2 :run rc))
        [d sd rd w] (add-comp-run w root)
        [dc w] (add-edge w s/ek-dep d c)
        [t st0 rt0 w] (add-task-run w root)
        [a et w] (park-on w rt0 c)]
    (testing "replace of the stale run: only the run itself"
      (let [w2 (:world (r/t14-cancel w rs true))]
        (is (nil? (find-row w2 :runs rs)) "cancelled and retired")
        (is (= 1 (:epoch (find-row w2 :comps d))))
        (is (= s/ph-armed (:phase (find-row w2 :edges dc))))
        (is (some? (find-row w2 :acts a)))
        (is (= rc (:run (find-row w2 :comps c))) "C.run is the current run, untouched")
        (is (ok? w2))))
    (testing "ordinary cancel of the stale run: no invalidation either"
      (let [w2 (:world (r/t14-cancel w rs false))]
        (is (= 1 (:epoch (find-row w2 :comps d))))
        (is (some? (find-row w2 :acts a)))))
    (testing "ordinary cancel of the current run: dependents invalidated, waiters get the error"
      (let [w2 (:world (r/t14-cancel w rc false))]
        (is (= 2 (:epoch (find-row w2 :comps d))) "epoch step of the dep creditor")
        (is (= s/ph-fired (:phase (find-row w2 :edges dc))))
        (is (nil? (find-row w2 :acts a)) "the waiting task resumed with err ::cancelled")
        (is (= 0 (:run (find-row w2 :comps c))) "T13 step 1: C.run := none")
        (is (ok? w2))))))

(deftest retain-test-worlds
  (testing "Rule R on the retain-test worlds normalizes them"
    (doseq [w [rtt/w1 rtt/w2]]
      (let [n (r/normalize w)]
        (is (true? (r/normalized n)))
        (is (ref-normalized? (rt/rule-r-filter n)))
        (is (ref-i3? (r/rule-r w)))))))

;; ---------------------------------------------------------------------------
;; Random operations

(defn random-world [^java.util.Random rng]
  (let [w s/empty-world
        root s/root-scope-id
        [ex w] (add-scope w root s/scope-explicit)
        [x w] (add-source w root)
        [y w] (add-source w ex)
        [c sc rc w] (add-comp-run w root :act s/act-active)
        w (s/run-upd w rc #(assoc % :slice true))                     ; its slice holds the token
        [cd w] (add-edge w s/ek-dep c x)
        [ob w] (add-edge w s/ek-observe 0 c)
        [d sd rd w] (add-comp-run w ex :handles 0 :result ok-result)
        [dd w] (add-edge w s/ek-dep d c)
        w (if (.nextBoolean rng) (:world (st/dispatch w [11 d])) w)  ; pin D
        [k sk rk w] (add-task-run w root)
        [k2 sk2 rk2 w] (add-task-run w sk)
        [a ew w] (park-on w rk k2)
        [k3 sk3 rk3 w] (add-task-run w ex)
        [a3 e3 w] (park-on w rk3 y)
        [z w] (add-resource w rk2)
        [e2 w] (add-comp w ex :handles 1)
        [cdd w] (add-edge w s/ek-dep e2 d)]
    w))

(defn random-op [^java.util.Random rng w]
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
    (case (.nextInt rng 16)
      0 [:item [0 (st) (.nextInt rng 6) v fresh]]
      1 [:item [1 (pick (map :id (:scopes w))) (.nextInt rng 6) v fresh]]
      2 [:item [2 (src) v]]
      3 [:item [3 (st) (src) v fresh]]
      4 [:item [4 (id) v fresh]]
      5 [:item [5 (pick edges)]]
      6 [:item [6 (if (seq edges) (pick edges) (id)) s/res-ok v]]
      7 [:item [7 (if (seq res) (pick res) (id))]]
      8 [:item [8 (st) (.nextInt rng 5) v fresh]]
      9 [:item [9 (if (seq res) (pick res) (id)) s/res-ok v]]
      10 [:item [10 (id)]]
      11 [:item [11 (id)]]
      12 [:item [12 (pick (:pins w))]]
      13 [:cancel (pick (map :id (:runs w))) (.nextBoolean rng)]
      14 [:close (pick (map :id (:scopes w)))]
      15 [:item [10 (id)]])))

(defn apply-op [w [kind a b]]
  (case kind
    :item {:raw (en/raw w a) :step (en/world-step w a) :tok (en/raw-token-ok w a)}
    :cancel (let [o (r/t14-cancel w a b)]
              (is (true? (r/casc-done w [[0 a b]])) "cascade worklist emptied")
              {:raw o :step (en/finish o) :tok true})
    :close (let [o (r/t16-close-scope w a)]
             (is (true? (r/casc-done w [[2 a]])) "cascade worklist emptied")
             {:raw o :step (en/finish o) :tok true})))

(deftest random-steps
  (let [rng (java.util.Random. 20261105)
        accepted (atom {})]
    (dotimes [run 15]
      (loop [i 0 w (random-world rng)]
        (when (< i 30)
          (let [op (random-op rng w)
                {:keys [raw step tok]} (apply-op w op)
                w2 (:world step)
                msg (str "run " run " step " i " " (pr-str op))]
            (is (ok? (:world raw)) (str "raw inv " msg))
            (if (:accepted raw)
              (do (swap! accepted update (if (= :item (first op)) (first (second op)) (first op)) (fnil inc 0))
                  (is (= w2 (rule-r-checks (:world raw) msg)) msg))
              (do (is (= w2 w) (str "refusal changed the world " msg))
                  (is (= raw step))))
            (when (false? tok) (is (= (st/->Outcome w false) step) (str "L4 " msg)))
            (is (ok? w2) msg)
            (recur (inc i) w2)))))
    (testing "the operations that matter were accepted"
      (is (every? #(pos? (get @accepted % 0)) [0 1 2 3 5 6 7 8 9 10 11 12 :cancel :close]) (pr-str @accepted)))))
