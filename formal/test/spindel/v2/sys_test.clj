(ns spindel.v2.sys-test
  "Loading spindel.v2.sys kernel-checks the system of worlds (notes/LAYER2.md): every live world
  keeps the layer-1 bundle through a step, a fork, the fix-up of inherited resources and a drop, and
  a step or a fork changes no other cell."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.oracle :as o]
            [spindel.v2.state :as s]
            [spindel.v2.ledger :as lg]
            [spindel.v2.sys :as sys]))

(def theorems
  '[sinv-put step-frame sinv-step fork-refused fork-effect-refused fork-frame fork-copy sinv-fork p3l-fork-effect-world
    fork-effect-frame sinv-fork-effect
    p3l-fire-ack p3l-wake-one p3l-wake-all sinv-wake
    sinv-drop sinv-init pinv-publish sinv-resume instantiate-frame instantiate-copy instantiate-indep
    sinv-instantiate sinv-activate activate-born activate-once pinv-abandon
    p3l-items-run p3l-merge-world merge-refused diff-ids-self merge-unchanged merge-frame sinv-merge
    sinv-idle-release drop-step-comm
    cinv-step-q cinv-wake-q cinv-resume-q cinv-merge-q cinv-publish-q cinv-abandon-q
    qsinv-init qpinv-none qsinv-step qsinv-wake qsinv-resume qsinv-merge qsinv-publish qsinv-abandon qsinv-accept
    qsinv-complete qsinv-drop qsinv-idle-release qsinv-release-unborn qsinv-activate qsinv-fork qsinv-fork-effect
    qsinv-instantiate qpinv-publish qpinv-abandon
    ;; C1c stage A, proof stage
    jinv-init jinv-join jinv-deliver jinv-withdraw jinv-complete jinv-step jinv-publish jinv-abandon jinv-wake jinv-accept
    jinv-release-unborn jinv-drop jinv-idle-release jinv-resume jinv-activate jinv-merge jinv-fork jinv-fork-effect
    jinv-instantiate deliver-pending sinv-join sinv-deliver sinv-withdraw qsinv-join qsinv-deliver qsinv-withdraw
    cinv-join cinv-deliver cinv-withdraw once-deliver once-withdraw once-complete once-join final-stays
    complete-born-ledger born-complete-delivered born-abandon-none
    ;; C1c stage B, proof stage (HB discharged: the three are layer-1 items)
    owned-done-none drain-none own-released internal-refused hb-step hb-own hb-owned-done hb-drain own-is-step owned-done-is-step
    drain-clean sys-drain-clean fold-del-out gnf-rule-r
    t-own-inv t-owned-done-inv t-drain-inv t-own-gw t-own-esb inv-fork-del inv-fork-ins-fresh fork-del-ids-ok
    sinv-own sinv-owned-done sinv-drain qsinv-own qsinv-owned-done qsinv-drain cinv-own cinv-owned-done cinv-drain
    jinv-own jinv-owned-done jinv-drain complete-no-markers
    ;; C2: seal, resolver, transfer (R6), descendant (R2)
    p3l-cstep wq-cstep rel-cstep qid-cstep qinv-cstep sealed-write sinv-seal cinv-seal qsinv-seal jinv-seal
    merge-out-world merge-unsealed writes-refused writes-default-ok writes-default-no run-wr merge-default
    merge-release-refused sinv-merge-release cinv-merge-release-q qsinv-merge-release jinv-merge-release
    descendant-refl descendant-fork descendant-par par-xfer-reserve par-xfer-move descendant-xfer-reserve
    descendant-xfer-move
    tbl-all-nat-del cinv-disown-any sinv-xfer-reserve cinv-xfer-reserve qsinv-xfer-reserve jinv-xfer-reserve
    sinv-xfer-move cinv-xfer-move qsinv-xfer-move jinv-xfer-move
    sinv-unseal cinv-unseal qsinv-unseal jinv-unseal merge-seal-same])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

;; The invariant theorems hold of refused transitions too (a refusal changes nothing), so the
;; compiled model is run: a published savepoint parks its run on an armed resource, a resume
;; (or an instance's activation) makes the run active outside its slice, and the child of a fork
;; effect starts with its run resumed. `arm` admits timers and offloads only: another kind for a
;; savepoint is refused, which would make every savepoint statement empty.
(deftest savepoint-and-fork-effect-are-not-refused
  (let [it (fn [tag & fs] (into [(o/ctor-idx tag)] fs))
        w0 (:world (en/world-step s/empty-world (it :spawn-top s/root-scope-id 0 (:next-id s/empty-world) [])))
        r (first (:runs w0))
        w1 (:world (en/world-step w0 (it :schedule (:id r))))
        run (fn [w] ((juxt :act :slice :resources) (first (s/run-find w (:id r)))))
        z (:next-id w1)
        p (en/world-step w1 (sys/publish-item (:stamp r) 0 z))
        w2 (:world p)]
    (is (= [s/act-active true nil] (run w1)) "the run holds its slice")
    (is (true? (:accepted p)) "publish is accepted")
    (is (false? (:accepted (en/world-step w1 (it :arm (:stamp r) s/rk-native 0 z)))) "a resource kind layer 1 does not arm is refused")
    (is (= [s/act-parked false [z]] (run w2)) "the run is parked on the savepoint")
    (is (= [[z s/rk-offload s/rp-armed]] (map (juxt :id :kind :phase) (:res w2))))
    (let [w3 (sys/fire-ack w2 z s/res-ok 7)]
      (is (= [s/act-active false nil] (run w3)) "resumed: active, outside its slice")
      (is (empty? (:res w3))) (is (empty? (:acts w3)))
      (is (true? (:accepted (en/world-step w3 (it :schedule (:id r))))) "and schedulable"))
    (let [wf (sys/fork-effect-world w1 (:stamp r) 0 7)]
      (is (= [s/act-active false nil] (run wf)) "the fork effect's child: the run resumed at the effect")
      (is (empty? (:res wf)))
      (is (true? (:accepted (en/world-step wf (it :schedule (:id r)))))))))

;; Merge and idle release, run on the worlds of the fork sample 14 (the parent at the fork commit
;; is the basis; the child wrote signal 3 and is quiescent at the end of its log).
(defn- fork-worlds []
  (let [pl (o/read-log "test/spindel/v2/oracle/log-sample-14-parent.edn")
        cl (vec (filter :proj (o/read-log "test/spindel/v2/oracle/log-sample-14-child.edn")))
        at (first (keep-indexed (fn [i c] (when (= :fork-host (first (:item c))) i)) pl))
        pr (o/replay pl :family? true :worlds? true)
        basis (nth (:worlds pr) at)
        cr (o/replay cl :family? true :init basis :worlds? true)]
    {:basis basis :parent (peek (:worlds pr)) :child (peek (:worlds cr))}))

(deftest merge-is-not-refused-and-refuses-a-conflict
  (let [{:keys [basis parent child]} (fork-worlds)
        it (fn [tag & fs] (into [(o/ctor-idx tag)] fs))
        src (fn [w x] ((juxt :state :version) (first (s/source-find w x))))
        merged (sys/merge-world parent child basis sys/refuse-all true)]
    (is (= [3] (sys/diff child basis)) "the child changed signal 3")
    (is (empty? (sys/diff basis basis)))
    (is (true? (sys/merge-ok parent child basis sys/refuse-all true)) "a quiescent child, no parent write since the fork")
    (is (= (first (src child 3)) (first (src merged 3))) "the parent takes the child's value")
    (is (= (inc (second (src parent 3))) (second (src merged 3))) "as one write")
    (is (not= parent merged))
    (let [p2 (:world (en/world-step parent (it :write 3 99)))]
      (is (false? (sys/merge-ok p2 child basis sys/refuse-all true)) "the parent wrote the same source since the fork")
      (is (= p2 (sys/merge-world p2 child basis sys/refuse-all true)) "a refused merge changes nothing"))))

;; the compiled model applies a function argument one argument at a time
(defn- cur4 [f] (fn [x] (fn [b] (fn [p] (fn [c] (f x b p c))))))

;; C2 (option C): the resolver is asked for a conflicting source only, with (source base parent-value
;; child-value); its value is written, its refusal refuses the merge; an unsealed child is never merged
(deftest c2-resolver
  (let [{:keys [basis parent child]} (fork-worlds)
        it (fn [tag & fs] (into [(o/ctor-idx tag)] fs))
        src (fn [w x] ((juxt :state :version) (first (s/source-find w x))))
        calls (atom [])
        rv (cur4 (fn [x b pv cv] (swap! calls conj [x b pv cv]) [(+ pv cv)]))
        p2 (:world (en/world-step parent (it :write 3 99)))]
    (is (false? (sys/merge-ok parent child basis sys/refuse-all false)) "unsealed: refused")
    (is (= parent (sys/merge-world parent child basis rv false)))
    (is (true? (sys/merge-ok parent child basis rv true)))
    (is (empty? @calls) "no conflict: the resolver is not asked")
    (is (= (sys/merge-world parent child basis sys/refuse-all true) (sys/merge-world parent child basis rv true)))
    (let [m (sys/merge-world p2 child basis rv true)]
      (is (= [[3 (first (src basis 3)) 99 (first (src child 3))]] (distinct @calls))
          "asked once per conflicting source: (source base parent-value child-value)")
      (is (= (+ 99 (first (src child 3))) (first (src m 3))) "the resolver's value is written")
      (is (= (inc (second (src p2 3))) (second (src m 3))) "as one write"))
    (is (false? (sys/merge-ok p2 child basis (cur4 (fn [_ _ _ _] nil)) true)) "a resolver refusal refuses the merge")
    (is (= p2 (sys/merge-world p2 child basis (cur4 (fn [_ _ _ _] nil)) true)) "and changes nothing")))

;; C2 seal (spec §9): a sealed cell refuses host admissions and host source changes, takes the rest;
;; merge! (the parent side, then the child's release) needs the child sealed
(deftest c2-seal-and-merge-release
  (let [{:keys [basis parent child]} (fork-worlds)
        it (fn [tag & fs] (into [(o/ctor-idx tag)] fs))
        cell (fn [w sealed] (sys/->Cell w true 1 s/root-scope-id [] false 0 [] false [] [] sealed))
        cells (fn [sealed] (fn [k] (case (long k) 1 (cell parent false) 2 (cell child sealed) (cell s/empty-world false))))
        sealed ((sys/sys-seal (cells false) 2) 2)
        w (:world sealed)]
    (is (true? (:sealed sealed)))
    (is (false? (en/slice-held w)) "the host acts between slices")
    (is (= w (:world (sys/cell-step sealed (it :write 3 7)))) "a host write is refused")
    (is (not= w (:world (sys/cell-step (cell child false) (it :write 3 7)))) "unsealed it is taken")
    (is (= w (:world (sys/cell-step sealed (it :spawn-top s/root-scope-id 1 (:next-id w) [])))) "a spawn is refused")
    (is (true? (:released (:world (sys/cell-step sealed (it :release-world))))) "release is taken")
    (let [c0 (cells false) c1 (sys/sys-merge-release c0 1 2 basis sys/refuse-all)]
      (is (= (map c0 [1 2]) (map c1 [1 2])) "unsealed: the system is unchanged"))
    (let [c0 (sys/sys-seal (cells false) 2) c1 (sys/sys-merge-release c0 1 2 basis sys/refuse-all)]
      (is (= (sys/merge-world parent child basis sys/refuse-all true) (:world (c1 1))) "the parent is merged")
      (is (true? (:released (:world (c1 2)))) "the child is released")
      (is (= (map c0 [1 2]) (map (sys/sys-merge-release c0 2 2 basis sys/refuse-all) [1 2])) "into itself: refused"))))

(deftest idle-release-fires-on-an-idle-world-only
  (let [{:keys [child]} (fork-worlds)
        it (fn [tag & fs] (into [(o/ctor-idx tag)] fs))
        cell (fn [w] (sys/->Cell w true 1 s/root-scope-id [] false 0 [] false [] [] false))
        cells (fn [w] (fn [k] (cell (if (= k 2) w s/empty-world))))
        step (fn [w i] (let [o (en/world-step w i)] (is (:accepted o) (pr-str i)) (:world o)))
        ;; the host lets go: every handle dropped, every host edge removed
        w1 (reduce step child (for [x (concat (:comps child) (:tasks child) (:sources child)) _ (range (:handles x))]
                                (it :handle-drop (:id x))))
        w2 (reduce step w1 (for [e (:edges w1) :when (s/host-cred e)]
                             (if (= s/ek-observe (:kind e)) (it :unobserve (:id e)) (it :host-unawait (:id e)))))]
    (is (true? (sys/idle-world s/empty-world)))
    (is (false? (sys/idle-world child)) "the host still holds handles")
    (is (true? (:live ((sys/sys-idle-release (cells child) 2) 2))) "not idle: nothing is released")
    (is (true? (sys/idle-world w2)) "idle once the host let go")
    (is (false? (:live ((sys/sys-idle-release (cells w2) 2) 2))) "an idle world is released")
    (is (true? (:live ((sys/sys-idle-release (cells w2) 2) 3))) "and no other cell")))

;; sample 17 (engine feat/v2-merge): a mergeable host fork. The child writes s (twice) and t and its
;; observed computation reruns; the parent writes u; `merge!` adopts s and t as two host writes in
;; the parent (ascending id) and releases the child. The model's `merge-world` of the parent's
;; world before the merge, the child's last world and the basis is the engine's world after the
;; two writes.
(deftest sample-17-merge
  (let [pl (o/read-log "test/spindel/v2/oracle/log-sample-17-parent.edn")
        cl (vec (filter :proj (o/read-log "test/spindel/v2/oracle/log-sample-17-child.edn")))
        pr (o/replay pl :family? true :worlds? true)
        at (first (keep-indexed (fn [i c] (when (= :fork-host (first (:item c))) i)) pl))
        basis (nth (:worlds pr) at)
        cr (o/replay cl :family? true :init basis :worlds? true)
        child (peek (:worlds cr))
        before (nth (:worlds pr) (inc at))
        after (nth (:worlds pr) (+ at 3))]
    (is (= [19 0 0] ((juxt :checked :n-divergences :resyncs) pr)) "the parent, across fork and merge")
    (is (= [15 0 0] ((juxt :checked :n-divergences :resyncs) cr)) "the child, from the basis")
    (is (= [[:write 5 20] [:write 3 15] [:write 4 18]] (map :item (subvec pl (inc at) (+ at 4))))
        "the parent's own write, then the merge's two writes by ascending id")
    (is (= #{3 4} (set (sys/diff child basis))) "the child changed s and t")
    (is (true? (sys/merge-ok before child basis sys/refuse-all true)))
    (is (= (o/world->proj after) (o/world->proj (sys/merge-world before child basis sys/refuse-all true)))
        "the model's merge is the engine's world after the merge")
    (is (false? (sys/merge-ok after child basis sys/refuse-all true)) "a second merge conflicts: the parent's s and t moved")))

;; C0 (spec §4.3 Links and forks, L12): links are not part of a mergeable fork's basis; a stream the
;; fork appended to is, so that merge is refused
(deftest c0-merge-links-out-streams-in
  (let [it (fn [tag & fs] (into [(o/ctor-idx tag)] fs))
        step (fn [w i] (let [o (en/world-step w i)] (is (:accepted o) (pr-str i)) (:world o)))
        root s/root-scope-id
        l (:next-id s/empty-world)
        b1 (step s/empty-world (it :create-link-top root l))
        sx (:next-id b1)
        basis (step b1 (it :create-source-top root s/sk-stream 0 sx))
        tail (:tail (first (s/source-find basis sx)))
        child (step basis (it :link-realize l 0 0 0))
        child2 (step basis (it :append sx 5 (:next-id basis)))]
    (is (pos? (:version (first (s/source-find child l)))) "the child realized the link")
    (is (empty? (sys/diff child basis)) "a realized link is not in the diff")
    (is (true? (sys/merge-ok basis child basis sys/refuse-all true)))
    (is (= basis (sys/merge-world basis child basis sys/refuse-all true)) "nothing to adopt")
    (is (= [sx] (sys/diff child2 basis)) "an appended stream is")
    (is (pos? tail))
    (is (false? (sys/merge-ok basis child2 basis sys/refuse-all true)) "so that merge is refused (stream merge: later in C2)")))

;; ---------------------------------------------------------------------------
;; C1 (T21 completion, Z#67): accepted children, completion, E4, inherited resources (R1)

;; sample 27's world at its release: the cancelled run waits for its offload (one unretired run)
(defn- released-busy []
  (let [l (vec (filter :proj (o/read-log "test/spindel/v2/oracle/log-sample-27-w.edn")))]
    (:world (en/world-step (reduce (fn [w c] (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c))))))
                                   s/empty-world (subvec l 0 3))
                           [(o/ctor-idx :release-world)]))))

;; a world with a task run parked on a deferred (one unretired run)
(defn- prefix-world-c1 []
  (let [it (fn [tag & fs] (into [(o/ctor-idx tag)] fs))
        w0 s/empty-world k (:next-id w0)
        w1 (:world (en/world-step w0 (it :spawn-top s/root-scope-id 0 k [])))
        r (:run (first (filter #(= k (:id %)) (:tasks w1))))
        w2 (:world (en/world-step w1 (it :schedule r)))
        st (:stamp (first (filter #(= r (:id %)) (:runs w2))))
        w3 (:world (en/world-step w2 (it :create-source st s/sk-deferred 0 (:next-id w2))))]
    (:world (en/world-step w3 (it :await st [(dec (:next-id w3))] s/am-one 1 (:next-id w3) [])))))

(defn- c1-cell [w & {:keys [parent unborn pending] :or {parent 0 unborn false pending 0}}]
  (sys/->Cell w true parent s/root-scope-id [] unborn pending [] false [] [] false))
(defn- c1-cells [m] (fn [k] (get m k (c1-cell s/empty-world))))
(defn- released [w] (:world (en/world-step w [(o/ctor-idx :release-world)])))

(deftest c1-completion-and-acceptance
  (let [quiet (released s/empty-world)
        cells (c1-cells {1 (c1-cell quiet) 2 (c1-cell quiet :parent 1)})]
    (testing "a child completed before its acceptance: acknowledged at the acceptance (sample 23a)"
      (let [c1 (sys/sys-complete cells 2)
            c2 (sys/sys-accept c1 1 2)
            c3 (sys/sys-complete c2 1)]
        (is (true? (:complete (c1 2))))
        (is (= [2] (:kids (c2 1))))
        (is (true? (:complete (c3 1))) "the owner completes: its only child is done")))
    (testing "an accepted, unfinished child holds its owner"
      (let [c1 (sys/sys-accept cells 1 2)
            c2 (sys/sys-complete c1 1)
            c3 (sys/sys-complete (sys/sys-complete c2 2) 1)]
        (is (false? (:complete (c2 1))))
        (is (true? (:complete (c3 1))))))
    (testing "a collected child is done; a complete owner takes no new obligation"
      (let [c1 (sys/sys-accept cells 1 2)
            c2 (sys/sys-complete (sys/sys-drop c1 2) 1)
            c3 (sys/sys-accept c2 1 3)]
        (is (true? (:complete (c2 1))))
        (is (= [2] (:kids (c3 1))))))
    (testing "a world with runs left is not complete"
      (let [busy (released-busy)]
        (is (pos? (en/world-runs busy)))
        (is (false? (:complete ((sys/sys-complete (c1-cells {1 (c1-cell busy)}) 1) 1))))))))

(deftest c1-unborn-release
  (let [w (prefix-world-c1)
        cells (c1-cells {3 (c1-cell w :parent 1 :unborn true :pending 99)})
        c1 (sys/sys-release-unborn cells 3)
        c2 (sys/sys-complete c1 3)]
    (is (true? (:released (:world (c1 3)))))
    (is (= (dissoc w :released) (dissoc (:world (c1 3)) :released)) "nothing in it runs")
    (is (true? (:complete (c2 3))) "complete at once (sample 24), with its copied runs")
    (is (false? (sys/act-ok (c2 3))) "a later activation is refused")))

(deftest c1-fork-discharge
  (let [w (released-busy)
        z (:id (first (:res w)))
        cells (sys/sys-fork (c1-cells {1 (c1-cell w)}) 1 2 s/root-scope-id)
        woken (sys/sys-wake cells 2)]
    (is (= s/rp-cancelling (:phase (first (:res w)))) "released with a cancelling offload")
    (is (some #{z} (:dormant (cells 2))) "inherited by the fork")
    (is (empty? (:res (:world (woken 2)))) "acknowledged at the fork's first turn (R1)")
    (is (= (:res w) (:res (:world (woken 1)))) "never touching the parent")))

;; question 9 (engine-v2 54e3df1): neither fork form is taken from an unborn instance, E4-released or
;; not (host `fork!` throws while W-UNBORN is set; the `(fork)` effect needs a run in a slice, and an
;; unborn instance drains none). The model refuses both: the system is unchanged.
(deftest c1-fork-of-unborn-refused
  (let [w (prefix-world-c1)
        r (first (:runs w))
        unborn (c1-cells {3 (c1-cell w :parent 1 :unborn true :pending 99)})
        e4 (sys/sys-release-unborn unborn 3)
        born (c1-cells {3 (c1-cell w :parent 1)})]
    (is (true? (:unborn (e4 3)))) (is (true? (:released (:world (e4 3)))) "E4: released, still unborn")
    (doseq [[label cells] [["an unborn instance" unborn] ["an E4-released instance" e4]]]
      (testing label
        (let [f (sys/sys-fork cells 3 4 s/root-scope-id)
              fe (sys/sys-fork-effect cells 3 4 s/root-scope-id (:stamp r) 0 7)]
          (is (= [(cells 3) (cells 4)] [(f 3) (f 4)]) "host fork refused: no child, the source unchanged")
          (is (= [(cells 3) (cells 4)] [(fe 3) (fe 4)]) "fork effect refused"))))
    (testing "a born cell forks (both forms)"
      (let [f (sys/sys-fork born 3 4 s/root-scope-id)
            fe (sys/sys-fork-effect born 3 4 s/root-scope-id (:stamp r) 0 7)]
        (is (= w (:world (f 4))) "the child starts from the parent's world")
        (is (= [3 3] [(:parent (f 4)) (:parent (fe 4))]))
        (is (= (born 3) (f 3) (fe 3)) "the parent unchanged")))))

;; ---------------------------------------------------------------------------
;; C1c stage A (spec Z#70): host joins (`on-joined` / `await-joined`): a cell's pending joins, admitted with no
;; row, edge, handle, id or item and also after release, delivered once the target task is complete or the world
;; is (abandonment), never inherited

;; prefix-world-c1's task (id 3) and the items that let it finish: the host delivers its deferred, the run takes
;; its slice and completes (T12 retires it; its run scope, which owns the deferred, is closed and removed)
(defn- finish-task [w]
  (let [it (fn [tag & fs] (into [(o/ctor-idx tag)] fs))
        k (:id (first (:tasks w)))
        r (:run (first (:tasks w)))
        d (:id (first (filter #(= s/sk-deferred (:kind %)) (:sources w))))]
    [k [(it :deliver d 5) (it :schedule r) (it :complete (:stamp (first (filter #(= r (:id %)) (:runs w)))) s/res-ok 1)]]))

;; the targets of a cell's live (pending) joins
(defn- pj [c] (mapv :target (filter #(= sys/js-pending (:st %)) (:joins c))))

(deftest c1c-join-delivered-at-target-completion
  (let [w (prefix-world-c1)
        [k items] (finish-task w)
        cells (sys/sys-join (c1-cells {1 (c1-cell w)}) 1 k)
        stepped (reduce (fn [cs i] (sys/sys-step cs 1 i)) cells items)
        w2 (:world (stepped 1))]
    (is (= [k] (pj (cells 1))) "pending: the task is running")
    (is (= (:world (cells 1)) w) "admission changes no row (no edge, handle or id)")
    (is (= [k] (pj ((sys/sys-deliver cells 1) 1))) "not delivered before the target completes")
    (is (true? (lg/task-complete w2 k)) "done, retired, its run scope removed")
    (is (= [k] (pj (stepped 1))) "a layer-1 step delivers nothing by itself")
    (is (= [] (pj ((sys/sys-deliver stepped 1) 1))) "delivered once the target is complete")
    (is (= [] (pj ((sys/sys-join (sys/sys-deliver stepped 1) 1 k) 1))) "a join on a complete target is delivered at once")))

;; sample 31b: an unborn instance's copy of a task never runs; a join on it is delivered with the instance's
;; completion (E4: released before its activation, complete at once)
(deftest c1c-abandoned-join-delivered-at-completion
  (let [w (prefix-world-c1)
        k (:id (first (:tasks w)))
        c0 (sys/sys-join (c1-cells {3 (c1-cell w :parent 1 :unborn true :pending 99)}) 3 k)
        c1 (sys/sys-deliver (sys/sys-release-unborn c0 3) 3)
        c2 (sys/sys-complete c1 3)]
    (is (= [k] (pj (c0 3))))
    (is (= [k] (pj (c1 3))) "released, not complete: the target never completes")
    (is (false? (lg/task-complete (:world (c2 3)) k)))
    (is (true? (:complete (c2 3))))
    (is (= [] (pj (c2 3))) "delivered with the completion (abandonment)")))

;; sample 32 and the released half: admission has no released guard
(deftest c1c-join-after-release
  (let [busy (released-busy)
        kb (:id (first (:tasks busy)))
        cb (sys/sys-join (c1-cells {1 (c1-cell busy)}) 1 kb)
        w (prefix-world-c1)
        [k items] (finish-task w)
        done (released (reduce (fn [w i] (:world (en/world-step w i))) w items))
        cd (sys/sys-complete (c1-cells {1 (c1-cell done)}) 1)]
    (is (true? (:released busy)))
    (is (false? (lg/task-complete busy kb)) "cancelled, its run still in cleanup (the offload)")
    (is (= [kb] (pj (cb 1))) "admitted after release, pending")
    (is (true? (lg/task-complete done k)))
    (is (= [] (pj ((sys/sys-join (c1-cells {1 (c1-cell done)}) 1 k) 1))) "after release, complete target: at once")
    (is (true? (:complete (cd 1))))
    (is (= [] (pj ((sys/sys-join cd 1 k) 1))) "on a complete world: at once")
    (is (= [] (pj ((sys/sys-join cd 1 kb) 1))) "on a complete world, whatever the target")
    (testing "refused (unchanged): an id no handle names, a collected world"
      (is (= (cb 1) ((sys/sys-join cb 1 (:next-id busy)) 1)))
      (let [dropped (sys/sys-drop (c1-cells {1 (c1-cell w)}) 1)]
        (is (= (dropped 1) ((sys/sys-join dropped 1 k) 1)))))))

(deftest c1c-joins-not-inherited
  (let [w (prefix-world-c1)
        r (first (:runs w))
        k (:id (first (:tasks w)))
        cells (sys/sys-join (c1-cells {1 (c1-cell w)}) 1 k)
        f (sys/sys-fork cells 1 2 s/root-scope-id)
        fe (sys/sys-fork-effect cells 1 2 s/root-scope-id (:stamp r) 0 7)
        inst (sys/sys-instantiate cells (fn [_] (sys/->Pub 1 99 (:id r) w true)) 0 2 s/root-scope-id)]
    (is (= [k] (pj (cells 1))))
    (is (= [0 0 0] (map #(count (:joins (% 2))) [f fe inst])) "a fork, a fork effect and an instance start with none")
    (is (= [[k] [k] [k]] (map #(pj (% 1)) [f fe inst])) "the parent keeps its own")
    (is (= w (:world (f 2))) "the fork copies the rows (the task with them)")))

;; question 12 / sample 33: withdrawal is a host-side mark on a pending join; delivery skips it, and a delivered join
;; stays delivered (the race's winner is final). Join ids count the admitted joins.
(deftest c1c-join-withdrawal
  (let [w (prefix-world-c1)
        [k items] (finish-task w)
        st (fn [c] (into {} (map (juxt :id :st) (:joins c))))
        c2 (-> (c1-cells {1 (c1-cell w)}) (sys/sys-join 1 k) (sys/sys-join 1 k))
        c1 (sys/sys-withdraw c2 1 0)
        stepped (reduce (fn [cs i] (sys/sys-step cs 1 i)) c1 items)
        done (sys/sys-deliver stepped 1)]
    (is (= [2 1] (map #(sys/pending-joins (:joins (% 1))) [c2 c1])) "2, then 1 live join")
    (is (= {0 sys/js-withdrawn 1 sys/js-pending} (st (c1 1))))
    (is (= (:world (c1 1)) w) "withdrawal changes no row")
    (is (= {0 sys/js-withdrawn 1 sys/js-delivered} (st (done 1))) "only the live join is delivered")
    (is (= 0 (sys/pending-joins (:joins (done 1)))))
    (is (= (st (done 1)) (st ((sys/sys-withdraw done 1 1) 1))) "a delivered join stays delivered")
    (is (= (st (done 1)) (st ((sys/sys-deliver done 1) 1))) "delivered at most once")
    (is (= (c2 1) ((sys/sys-join c2 1 0) 1)) "a join on id 0 (none) is refused")))

;; ---------------------------------------------------------------------------
;; C1c stage B (Z#71, spindel.v2.owned): owned forks. prefix-world-c1's task forks with the `(fork)` effect: the
;; child is counted on the forking run's current scope (its run scope), a fork marker in the parent's world.

(defn- marker-owners [w] (mapv :owner (:forks w)))
(defn- scope-row [w x] (first (filter #(= x (:id %)) (:scopes w))))

;; cell 1 runs prefix-world-c1; its task's run forks child cell 2 (the fork effect, its acceptance and count)
(defn- forked []
  (let [w (prefix-world-c1)
        r (first (:runs w))
        sc (en/cur-scope w r)
        c0 (c1-cells {1 (c1-cell w)})
        c1 (-> c0 (sys/sys-fork-effect 1 2 sc (:stamp r) 0 7) (sys/sys-accept 1 2) (sys/sys-own 1 sc 2))]
    {:w w :sc sc :mid (:next-id w) :cells c1}))

(deftest c1c-owned-fork-holds-its-scope
  (let [{:keys [w sc mid cells]} (forked)
        [k items] (finish-task w)
        done (reduce (fn [cs i] (sys/sys-step cs 1 i)) cells items)
        w2 (:world (done 1))
        od (sys/sys-owned-done done 1 sc mid)]
    (is (= (lg/task-srow k) sc) "the run's current scope is its run scope")
    (is (= [sc] (marker-owners (:world (cells 1)))) "counted: one marker on the run scope")
    (is (= [mid] (map :id (:forks (:world (cells 1))))) "the marker's id is the parent's fresh id (the child world's)")
    (is (empty? (:forks (:world (cells 2)))) "the child does not inherit its own marker (copied before the count)")
    (is (= 0 (en/world-runs w2)) "the task's run retired")
    (is (some? (scope-row w2 sc)) "its run scope stays: the owned fork holds it")
    (is (false? (:open (scope-row w2 sc))))
    (is (false? (lg/task-complete w2 k)) "so the task is not complete")
    (is (= [k] (pj ((sys/sys-deliver (sys/sys-join done 1 k) 1) 1))) "a host join waits")
    (is (= (:world (done 1)) (:world ((sys/sys-owned-done done 1 sc (inc mid)) 1))) "owned-done of no marker: unchanged")
    (is (empty? (:forks (:world (od 1)))) "[:owned-done s child] drops the marker")
    (is (nil? (scope-row (:world (od 1)) sc)) "and the scope goes")
    (is (true? (lg/task-complete (:world (od 1)) k)) "the task completes")))

(deftest c1c-owned-fork-early-branch-not-counted
  (let [w (prefix-world-c1)
        r (first (:runs w))
        sc (en/cur-scope w r)]
    (is (= [sc] (marker-owners (:world ((sys/sys-own (c1-cells {1 (c1-cell w)}) 1 sc 2) 1)))))
    (is (empty? (:forks (:world ((sys/sys-own (c1-cells {1 (c1-cell (released w))}) 1 sc 2) 1)))) "released")
    (is (empty? (:forks (:world ((sys/sys-own (c1-cells {1 (c1-cell w)}) 1 99 2) 1)))) "no open scope 99")))

;; question 16: W-KIDS reaches zero (the child is collected) before the owner runs [:owned-done]: no completion
(deftest c1c-completion-waits-for-the-count
  (let [{:keys [w sc mid cells]} (forked)
        [_ items] (finish-task w)
        done (reduce (fn [cs i] (sys/sys-step cs 1 i)) cells items)
        rel (-> done (sys/sys-step 1 [(o/ctor-idx :release-world)]) (sys/sys-drop 2))
        c1 (sys/sys-complete rel 1)
        c2 (sys/sys-owned-done rel 1 sc mid)]
    (is (true? (:released (:world (rel 1)))))
    (is (= 0 (en/world-runs (:world (rel 1)))))
    (is (true? (sys/kid-done rel 2)) "the only accepted child is collected")
    (is (false? (:complete (c1 1))) "the count holds the completion")
    (is (true? (:complete (c2 1))) "owned-done ends with maybe-complete!")))

;; v4 L2 normalization: a fork of the parent inherits its markers (W-NORMALIZE); a scope kept only by them is
;; removed by the child's drain ([:normalize]); question 15: the child does not complete before it
(deftest c1c-normalization
  (let [{:keys [w sc mid cells]} (forked)
        [k items] (finish-task w)
        done (reduce (fn [cs i] (sys/sys-step cs 1 i)) cells items)
        f (sys/sys-fork done 1 3 s/root-scope-id)
        rel (sys/sys-step f 3 [(o/ctor-idx :release-world)])
        dr (sys/sys-drain rel 3)]
    (is (= [mid] (:norm (f 3))) "the inherited marker is the child's W-NORMALIZE")
    (is (some? (scope-row (:world (f 3)) sc)) "the inherited scope stays in the child")
    (is (false? (lg/task-complete (:world (f 3)) k)))
    (is (false? (:complete ((sys/sys-complete rel 3) 3))) "released first (fast path): not complete before the drain")
    (is (empty? (:forks (:world (dr 3)))))
    (is (nil? (scope-row (:world (dr 3)) sc)) "the drain removes the scope")
    (is (true? (lg/task-complete (:world (dr 3)) k)))
    (is (true? (:complete (dr 3))) "the drain ends with maybe-complete!")
    (is (empty? (:norm (dr 3))))
    (is (= (dr 1) (rel 1) (done 1)) "the parent keeps its count")
    (testing "the parent's pending W-NORMALIZE is inherited too (a fork of the undrained child)"
      (is (= [mid] (:norm ((sys/sys-fork rel 3 4 s/root-scope-id) 4)))))
    (testing "an unborn cell does not drain"
      (let [u (c1-cells {5 (assoc (c1-cell (:world (f 3)) :unborn true :pending 99) :norm [mid])})]
        (is (= (u 5) ((sys/sys-drain u 5) 5)))))))

;; C2 R6, the engine's protocol: reserve in the new owner, then move; a completion in between, a counted fork
;; or a cycle undoes or refuses it; lineage stays; unseal clears the flag unless released
(deftest c2-transfer-protocol
  (let [cell (fn [parent owner kids] (sys/->Cell s/empty-world true parent owner [] false 0 kids false [] [] false))
        cells (fn [k] (case (long k) 1 (cell 0 0 [2 3]) 2 (cell 1 1 []) 3 (cell 1 1 []) (cell 0 0 [])))
        fuel [0 0 0 0]
        root s/root-scope-id
        r (sys/sys-xfer-reserve cells 2 3 fuel)
        mv (sys/sys-xfer-move r 2 3)]
    (is (= [2] (:kids (r 3))) "reserved: the new owner holds a token")
    (is (= [2 3] (:kids (r 1))) "the old one still holds its own")
    (is (= [3 [3] [2]] [(:owner (mv 2)) (:kids (mv 1)) (:kids (mv 3))]) "moved")
    (let [done (fn [k] (if (= k 2) (assoc (r 2) :complete true) (r k)))
          u (sys/sys-xfer-move done 2 3)]
      (is (= [1 nil] [(:owner (u 2)) (seq (:kids (u 3)))]) "completed meanwhile: the reservation is undone"))
    (is (= (map cells (range 4)) (map (sys/sys-xfer-reserve cells 2 1 fuel) (range 4))) "to the current owner: refused")
    (is (= 1 (:parent (mv 2))) "the lineage stays")
    (is (= (for [a (range 4) d (range 4)] (sys/descendant cells a d fuel))
           (for [a (range 4) d (range 4)] (sys/descendant mv a d fuel))) "no lineage answer changes")
    ;; 2 forked 4 (owner 2): a transfer of 2 into its own owned subtree is refused
    (let [c4 (fn [k] (case (long k) 2 (cell 1 1 [4]) 4 (cell 2 2 []) (cells k)))]
      (is (true? (sys/descendant c4 1 4 fuel)))
      (is (= (map c4 (range 5)) (map (sys/sys-xfer-reserve c4 2 4 fuel) (range 5))) "a cycle: refused"))
    ;; a counted fork: the old owner's world holds its marker; the move undoes the reservation
    (let [w1 (assoc s/empty-world :forks [(s/->ForkRow 9 2 7)])
          cc (fn [k] (if (= k 1) (assoc (r 1) :world w1) (r k)))
          u (sys/sys-xfer-move cc 2 3)]
      (is (= [1 nil] [(:owner (u 2)) (seq (:kids (u 3)))]) "a counted (fork)-effect child does not move"))
    (let [sealed ((sys/sys-seal cells 2) 2)]
      (is (false? (:sealed ((sys/sys-unseal (fn [k] (if (= k 2) sealed (cells k))) 2) 2))) "unsealed")
      (let [rel (assoc sealed :world (assoc s/empty-world :released true))]
        (is (true? (:sealed ((sys/sys-unseal (fn [k] (if (= k 2) rel (cells k))) 2) 2))) "released: refused")))))

