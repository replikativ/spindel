(ns spindel.v2.sys-test
  "Loading spindel.v2.sys kernel-checks the system of worlds (notes/LAYER2.md): every live world
  keeps the layer-1 bundle through a step, a fork, the fix-up of inherited resources and a drop, and
  a step or a fork changes no other cell."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.engine :as en]
            [spindel.v2.oracle :as o]
            [spindel.v2.state :as s]
            [spindel.v2.sys :as sys]))

(def theorems
  '[sinv-put step-frame sinv-step fork-frame fork-copy sinv-fork p3l-fork-effect-world fork-effect-frame sinv-fork-effect
    p3l-fire-ack p3l-wake-one p3l-wake-all sinv-wake
    sinv-drop sinv-init pinv-publish sinv-resume instantiate-frame instantiate-copy instantiate-indep
    sinv-instantiate sinv-activate activate-born activate-once pinv-abandon
    p3l-apply-diff p3l-merge-world merge-refused diff-ids-self merge-unchanged merge-frame sinv-merge
    sinv-idle-release drop-step-comm])

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
    (is (false? (:accepted (en/world-step w1 (it :arm (:stamp r) 4 0 z)))) "a resource kind layer 1 does not arm is refused")
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
        cell (fn [w] (sys/->Cell w true 1 s/root-scope-id [] false 0))
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
