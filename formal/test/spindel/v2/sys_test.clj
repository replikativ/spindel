(ns spindel.v2.sys-test
  "Loading spindel.v2.sys kernel-checks the system of worlds (notes/LAYER2.md): every live world
  keeps the layer-1 bundle through a step, a fork, the fix-up of inherited resources and a drop, and
  a step or a fork changes no other cell."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.oracle :as o]
            [spindel.v2.state :as s]
            [spindel.v2.sys :as sys]))

(def theorems
  '[sinv-put step-frame sinv-step fork-refused fork-effect-refused fork-frame fork-copy sinv-fork p3l-fork-effect-world
    fork-effect-frame sinv-fork-effect
    p3l-fire-ack p3l-wake-one p3l-wake-all sinv-wake
    sinv-drop sinv-init pinv-publish sinv-resume instantiate-frame instantiate-copy instantiate-indep
    sinv-instantiate sinv-activate activate-born activate-once pinv-abandon
    p3l-apply-diff p3l-merge-world merge-refused diff-ids-self merge-unchanged merge-frame sinv-merge
    sinv-idle-release drop-step-comm
    cinv-step-q cinv-wake-q cinv-resume-q cinv-merge-q cinv-publish-q cinv-abandon-q
    qsinv-init qpinv-none qsinv-step qsinv-wake qsinv-resume qsinv-merge qsinv-publish qsinv-abandon qsinv-accept
    qsinv-complete qsinv-drop qsinv-idle-release qsinv-release-unborn qsinv-activate qsinv-fork qsinv-fork-effect
    qsinv-instantiate qpinv-publish qpinv-abandon])

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
        merged (sys/merge-world parent child basis)]
    (is (= [3] (sys/diff child basis)) "the child changed signal 3")
    (is (empty? (sys/diff basis basis)))
    (is (true? (sys/merge-ok parent child basis)) "a quiescent child, no parent write since the fork")
    (is (= (first (src child 3)) (first (src merged 3))) "the parent takes the child's value")
    (is (= (inc (second (src parent 3))) (second (src merged 3))) "as one write")
    (is (not= parent merged))
    (let [p2 (:world (en/world-step parent (it :write 3 99)))]
      (is (false? (sys/merge-ok p2 child basis)) "the parent wrote the same source since the fork")
      (is (= p2 (sys/merge-world p2 child basis)) "a refused merge changes nothing"))))

(deftest idle-release-fires-on-an-idle-world-only
  (let [{:keys [child]} (fork-worlds)
        it (fn [tag & fs] (into [(o/ctor-idx tag)] fs))
        cell (fn [w] (sys/->Cell w true 1 s/root-scope-id [] false 0 [] false))
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
    (is (true? (sys/merge-ok before child basis)))
    (is (= (o/world->proj after) (o/world->proj (sys/merge-world before child basis)))
        "the model's merge is the engine's world after the merge")
    (is (false? (sys/merge-ok after child basis)) "a second merge conflicts: the parent's s and t moved")))

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
    (is (true? (sys/merge-ok basis child basis)))
    (is (= basis (sys/merge-world basis child basis)) "nothing to adopt")
    (is (= [sx] (sys/diff child2 basis)) "an appended stream is")
    (is (pos? tail))
    (is (false? (sys/merge-ok basis child2 basis)) "so that merge is refused (stream merge: C2)")))

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
  (sys/->Cell w true parent s/root-scope-id [] unborn pending [] false))
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
