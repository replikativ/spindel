(ns spindel.v2.engine-test
  "Loading spindel.v2.engine kernel-checks T3-T6, T11, T12, T22, the settle, validation and
  the model's step theorems. The deftests run scenarios built from items only (starting at
  `empty-world`) through the compiled `world-step`, and drive it with random items of every
  kind, checking after every step: inv-sample with a plain pending count, Rule R's honest
  hypotheses, I3/I4 against the plain BFS of spindel.v2.retain-test, that a refusal leaves the
  world unchanged and that an invalid token is refused (L4)."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.step :as st]
            [spindel.v2.rule :as r]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.rule-test :as rlt]))

(def theorems
  '[cred-ok-mono deb-ok-mono comp-ins-edges-ref-ok task-ins-edges-ref-ok act-ins-edges-ref-ok
    inv-scope-ins-fresh inv-run-ins-fresh inv-task-ins-fresh inv-act-ins-fresh inv-comp-ins-fresh
    inv-insert-edge-checked inv-add-run-scope inv-react-one inv-react-loop inv-demand-reactive
    inv-spawn-rows t4-inv t4-refuse t4-top-inv t4-top-refuse inv-start-raw t5-inv t5-refuse
    inv-mark-from inv-create-comp-raw t3-inv t3-refuse t3-top-inv t3-top-refuse
    inv-cancel-pred inv-cut-suffix inv-consume-entry inv-new-run-of inv-dispatch-raw t11-inv t11-refuse
    inv-settle-edge inv-settle-one inv-settle-loop inv-settle inv-complete-body inv-retire-after
    inv-complete-raw t12-inv t12-refuse
    inv-await-step inv-await-wire inv-fast-fill inv-fin-if-final inv-park-if inv-await-pre
    inv-await-post inv-await-raw t6-inv t6-refuse
    inv-host-await-raw t22-inv t22-refuse t22-un-inv t22-un-refuse t8-full-inv t8-full-refuse
    sched-inv sched-refuse t-handle-new-inv t-handle-new-refuse inv-cancel-losers
    raw0-inv raw0-refuse raw-inv raw-refuse raw0-l4 raw-l4 step-refuse step-l4 step-accepted
    step-inv step-i3 step-normalized step-i4 step-i3-total step-normalized-total step-i4-total
    ;; sources, finalizers, host items, ranks, Blocked
    ids-ok-bump inv-bump t-deliver-inv t-deliver-refuse inv-serve-or t-post-inv t-post-refuse
    t-release-inv t-release-refuse inv-take-park inv-take-now t-take-inv t-take-refuse t-take-l4
    t-finally-enter-inv t-finally-enter-refuse t-finally-enter-l4 t-finally-exit-inv t-finally-exit-refuse
    t-finally-exit-l4 t-slice-exit-inv t-slice-exit-refuse inv-deliver-fire inv-dep-consumed t-finalize-inv t-finalize-refuse t-cancel-inv t-cancel-refuse
    t-open-scope-inv t-open-scope-refuse t-open-scope-l4 t-close-scope-inv t-close-scope-refuse
    t-detach-inv t-detach-refuse inv-zero-handles inv-revoke-roots t-release-world-inv
    t-release-world-refuse inv-raise-loop inv-raise-for inv-react-add blocked-sound blocked-complete
    inv-create-source-cur t1-full-inv t1-full-refuse comp-demand-row-id])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t))))
        (str t))))

;; ---------------------------------------------------------------------------
;; Items (tagged runtime representation [constructor-index field ...]; see step's table)

(defn create-source [st kind v fresh] [0 st kind v fresh])
(defn create-source-top [scope kind v fresh] [1 scope kind v fresh])
(defn write [x v] [2 x v])
(defn track [st x k fresh] [3 st x k fresh])
(defn observe [d cb fresh] [4 d cb fresh])
(defn unobserve [e] [5 e])
(defn fire [e tag v] [6 e tag v])
(defn resource-ack [z] [7 z])
(defn arm [st kind k fresh] [8 st kind k fresh])
(defn resource-fire [z tag v] [9 z tag v])
(defn handle-drop [x] [10 x])
(defn pin [x] [11 x])
(defn unpin [x] [12 x])
(defn create-comp [st c i b] [13 st c (if (sequential? i) (vec i) [i]) b])
(defn create-comp-top [scope c i b] [14 scope c (if (sequential? i) (vec i) [i]) b])
(defn spawn ([st b fresh] (spawn st b fresh [])) ([st b fresh ins] [15 st b fresh (vec ins)]))
(defn spawn-top ([scope b fresh] (spawn-top scope b fresh [])) ([scope b fresh ins] [16 scope b fresh (vec ins)]))
(defn start [c fresh] [17 c fresh])
(defn await* [st ds mode k fresh mine] [18 st (vec ds) mode k fresh (vec mine)])
(defn dispatch-comp [c fresh] [19 c fresh])
(defn complete [st tag v] [20 st tag v])
(defn schedule [r] [21 r])
(defn host-await [d fresh] [22 d fresh])
(defn host-unawait [e] [23 e])
(defn handle-new [x] [24 x])
(defn deliver [x v] [25 x v])
(defn post [x v] [26 x v])
(defn take* [st x k fresh] [27 st x k fresh])
(defn release [x] [28 x])
(defn finalize [r] [29 r])
(defn cancel [r] [30 r])
(defn release-world [] [31])
(defn open-scope [st s] [32 st s])
(defn close-scope [s] [33 s])
(defn detach [k s] [34 k s])
(defn finally-enter [st] [35 st])
(defn finally-exit [st] [36 st])
(defn slice-exit [r] [37 r])

(def root s/root-scope-id)
(defn find-row [w field id] (first (filter #(= id (:id %)) (get w field))))
(defn stamp [w rid] (:stamp (find-row w :runs rid)))

(defn step!
  "world-step with the per-step checks; returns the new world (asserts acceptance unless
  :refused is given)"
  ([w item] (step! w item nil))
  ([w item expect]
   (let [raw (en/raw w item)
         o (en/world-step w item)]
     (if (= expect :refused)
       (do (is (false? (:accepted o)) (str "refused " (pr-str item)))
           (is (= w (:world o))))
       (do (is (true? (:accepted o)) (str "accepted " (pr-str item)))
           (when (:accepted raw) (rlt/rule-r-checks (:world raw) (pr-str item)))
           (is (true? (en/ranks-ok (:world o))) (str "I12 ranks-ok " (pr-str item)))))
     (:world o))))

;; a task with a run holding the slice (top level, owned by the root scope)
(defn task-with-slice [w]
  (let [k (:next-id w)
        w (step! w (spawn-top root 7 k))
        w (step! w (schedule (inc k)))]
    [k (inc k) w]))

;; ---------------------------------------------------------------------------
;; Scenarios

(deftest spawn-schedule-complete
  (let [w s/empty-world
        _ (is (= [2 3] [(:id (first (:scopes w))) (:next-id w)]) "id convention")
        [k rk w] (task-with-slice w)
        sk (+ k 2)]
    (testing "T4: task, run, run scope in that order; stamp = run id; scope parent = owner (Z#26)"
      (is (= [root rk 1] ((juxt :owner :run :handles) (find-row w :tasks k))))
      (is (= [k rk sk s/act-active true] ((juxt :of :stamp :scope :act :slice) (find-row w :runs rk))))
      (is (= root (:parent (find-row w :scopes sk)))))
    (testing "the scheduling choice is refused while a run holds the slice"
      (let [[k2 rk2 w2] [(:next-id w) (inc (:next-id w)) (step! w (spawn-top root 8 (:next-id w)))]]
        (step! w2 (schedule rk2) :refused)))
    (testing "T12 on a task: result, run retired (Z#25: K.run cleared), its scope removed"
      (let [w2 (step! w (complete (stamp w rk) s/res-ok 42))]
        (is (= [s/res-ok 42] ((juxt :tag :val) (:result (find-row w2 :tasks k)))))
        (is (nil? (find-row w2 :runs rk)))
        (is (= 0 (:run (find-row w2 :tasks k))))
        (is (nil? (find-row w2 :scopes sk)))))))

(deftest task-completion-wakes-waiter
  (let [w s/empty-world
        [k rk w] (task-with-slice w)
        ;; K spawns child C (owned by K's run scope) and awaits it
        c (:next-id w)
        w (step! w (spawn (stamp w rk) 9 c))
        a (:next-id w)
        w (step! w (await* (stamp w rk) [c] s/am-one 77 a [c]))]
    (is (= [s/act-parked false] ((juxt :act :slice) (find-row w :runs rk))))
    (is (= [(s/->Member (inc a) 0)] (vec (:members (find-row w :acts a)))) "edge id = act + 1")
    (testing "the child runs and completes; its wait creditor resumes"
      (let [w (step! w (schedule (inc c)))
            w (step! w (complete (stamp w (inc c)) s/res-ok 5))]
        (is (nil? (find-row w :acts a)) "activation removed on resume")
        (is (nil? (find-row w :edges (inc a))) "wait member consumed")
        (is (= s/act-active (:act (find-row w :runs rk))))))))

(deftest await-all-duplicate-debtors
  (let [w s/empty-world
        [k rk w] (task-with-slice w)
        c (:next-id w)
        w (step! w (spawn (stamp w rk) 9 c))
        a (:next-id w)
        w (step! w (await* (stamp w rk) [c c] s/am-all 77 a []))]
    (testing "one edge for the duplicate debtor, listed at both indices (Z#7)"
      (let [act (find-row w :acts a)]
        (is (= [(s/->Member (inc a) 0) (s/->Member (inc a) 1)] (vec (:members act))))
        (is (= 2 (:remaining act)))
        (is (= (+ a 2) (:next-id w)) "only one edge allocated")))
    (testing "one fire fills both slots and resumes"
      (let [w (step! w (schedule (inc c)))
            w (step! w (complete (stamp w (inc c)) s/res-ok 5))]
        (is (nil? (find-row w :acts a)))
        (is (= s/act-active (:act (find-row w :runs rk))))))))

(deftest await-any-cancels-losers
  (let [w s/empty-world
        [k rk w] (task-with-slice w)
        k1 (:next-id w)
        w (step! w (spawn (stamp w rk) 1 k1))
        k2 (:next-id w)
        w (step! w (spawn (stamp w rk) 2 k2))
        a (:next-id w)
        w (step! w (await* (stamp w rk) [k1 k2] s/am-any 77 a [k1 k2]))
        w (step! w (schedule (inc k1)))
        w (step! w (complete (stamp w (inc k1)) s/res-ok 1))]
    (is (nil? (find-row w :acts a)) "any resumes on the first fill")
    (is (= s/act-active (:act (find-row w :runs rk))))
    (is (empty? (filter #(= k2 (:debtor %)) (:edges w))) "loser wait edge removed")
    (is (= [s/res-err r/cancelled-code] ((juxt :tag :val) (:result (find-row w :tasks k2))))
        "the loser task R created for this await is cancelled")
    (is (nil? (find-row w :runs (inc k2))))))

(deftest create-comp-adopt-replace
  (let [w s/empty-world
        c (:next-id w)
        w (step! w (create-comp-top root c 10 100))
        _ (is (= [root 1 0 1 true] ((juxt :owner :epoch :done-epoch :handles :idle) (find-row w :comps c)))
              "undemanded: Rule R demotes it to idle; done-epoch none = fresh (§2)")
        ;; D depends on C: D created, started; D awaits C ... built with T5 + T6 below
        x (:next-id w)
        w (step! w (create-source-top root s/sk-signal 0 x))
        w (step! w (observe c 55 (:next-id w)))         ; keeps C demanded
        rc (:next-id w)
        w (step! w (start c rc))
        w (step! w (schedule rc))
        _ (is (= [rc rc 1 0] ((juxt :run :stamp :epoch :effect-index)
                              (merge (find-row w :comps c) (select-keys (find-row w :runs rc) [:stamp :effect-index])))))
        w (step! w (track (stamp w rc) x 9 (:next-id w)))
        w (step! w (complete (stamp w rc) s/res-ok 3))]
    (is (true? (st/comp-live (find-row w :comps c))))
    (testing "adoption: equal inputs, nothing changes (Z#29: handles unchanged)"
      (let [w2 (step! w (create-comp-top root c 10 100))]
        (is (= (find-row w :comps c) (find-row w2 :comps c)))))
    (testing "replacement: different inputs, epoch step, needs-run; then T11 restarts from the body"
      (let [w2 (step! w (create-comp-top root c 11 101))
            row (find-row w2 :comps c)]
        (is (= [[11] 101 2 1] ((juxt (comp vec :inputs) :body :epoch :handles) row)))
        (is (true? (en/needs-run w2 row)))
        (let [rn (:next-id w2)
              w3 (step! w2 (dispatch-comp c rn))]
          (is (= rn (:run (find-row w3 :comps c))))
          (is (= [2 0] ((juxt :epoch :effect-index) (find-row w3 :runs rn))) "restart: effect-index 0")
          (is (empty? (filter #(and (= c (:creditor %)) (= s/ek-dep (:kind %))) (:edges w3)))
              "no entry edge: every site is suffix, its edge removed")
          (is (= [(s/->AdoptBase 0 x 0 0)] (vec (:adopt-baselines (find-row w3 :comps c))))
              "the suffix baseline moved to the adoption"))))))

(deftest dispatch-resume-restart-and-stale
  (let [w s/empty-world
        c (:next-id w)
        w (step! w (create-comp-top root c 1 1))
        x (:next-id w)
        w (step! w (create-source-top root s/sk-signal 0 x))
        w (step! w (observe c 55 (:next-id w)))
        rc (:next-id w)
        w (step! w (start c rc))
        w (step! w (schedule rc))
        ed (:next-id w)
        w (step! w (track (stamp w rc) x 9 ed))]
    (testing "a write before completion: invalidation, the running run is stale; its completion is discarded"
      (let [w2 (step! w (write x 5))
            _ (is (= 2 (:epoch (find-row w2 :comps c))))
            w3 (step! w2 (complete (stamp w2 rc) s/res-ok 1))]
        (is (= s/res-none (:tag (:result (find-row w3 :comps c)))) "stale result discarded")
        (is (nil? (find-row w3 :runs rc)) "the stale run retires")))
    (let [w (step! w (complete (stamp w rc) s/res-ok 1))
          w (step! w (write x 5))
          _ (is (= s/ph-fired (:phase (find-row w :edges ed))))
          rn (:next-id w)
          w2 (step! w (dispatch-comp c rn))]
      (testing "T11 resume: E.cont = k, effect-index E.at + 1 (Z#12), E re-armed with the new baseline"
        (is (= [1 2] ((juxt :effect-index :epoch) (find-row w2 :runs rn))))
        (is (= [s/ph-armed 5 1] ((juxt :phase :base-value :base-version) (find-row w2 :edges ed))))))
    (testing "T11 restart: a track while holding a resource has cont restart; E keeps its old baseline (Z#22)"
      (let [z (:next-id w)
            w (step! w (arm (stamp w rc) s/rk-timer 7 z))
            _ (is (= s/act-parked (:act (find-row w :runs rc))) "Z#55: the arm parks the run")
            w (step! w (resource-fire z s/res-ok 0))
            w (step! w (schedule rc))
            e2 (:next-id w)
            w (step! w (track (stamp w rc) x 9 e2))
            _ (is (= s/cont-restart (:cont (find-row w :edges e2))))
            w (step! w (complete (stamp w rc) s/res-ok 1))
            w (step! w (write x 6))
            rn (:next-id w)
            w2 (step! w (dispatch-comp c rn))]
        (is (= 1 (:effect-index (find-row w2 :runs rn))) "the earliest fired edge is the first (cont k)")
        (is (some? (find-row w2 :edges ed)))))))

(deftest settle-delivers-to-parked-member
  ;; C awaits D (D not yet run: C parks); D runs and settles changed: C's member is delivered;
  ;; a write to D's source dirties both; D re-runs and settles unchanged: C live again
  (let [w s/empty-world
        x (:next-id w)
        w (step! w (create-source-top root s/sk-signal 0 x))
        d (:next-id w)
        w (step! w (create-comp-top root d 1 1))
        c (:next-id w)
        w (step! w (create-comp-top root c 2 2))
        w (step! w (observe c 55 (:next-id w)))
        rc (:next-id w)
        w (step! w (start c rc))
        w (step! w (schedule rc))
        a (:next-id w)
        w (step! w (await* (stamp w rc) [d] s/am-one 9 a []))
        _ (is (= s/act-parked (:act (find-row w :runs rc))) "D is fresh: C parks")
        _ (is (= (inc a) (:id (first (filter #(= d (:debtor %)) (:edges w))))))
        rd (:next-id w)
        w (step! w (start d rd))
        w (step! w (schedule rd))
        w (step! w (track (stamp w rd) x 9 (:next-id w)))
        w (step! w (complete (stamp w rd) s/res-ok 7))]
    (is (nil? (find-row w :acts a)) "changed settle of D delivers to C's member")
    (is (= s/act-active (:act (find-row w :runs rc))))
    (is (= [true 1] ((juxt :has-seen :seen) (find-row w :edges (inc a)))) "the member consumed D's version 1")
    (let [w (step! w (schedule rc))
          w (step! w (complete (stamp w rc) s/res-ok 8))]
      (is (true? (st/comp-live (find-row w :comps c))))
      (testing "write: C's edge on D is marked, D re-runs, completes unchanged, C settles live"
        (let [w (step! w (write x 1))
              _ (is (= 1 (:pending (find-row w :comps c))))
              _ (is (false? (st/comp-live (find-row w :comps c))))
              rd2 (:next-id w)
              w (step! w (dispatch-comp d rd2))
              _ (is (= 1 (:effect-index (find-row w :runs rd2))) "resumed after the track site")
              w (step! w (schedule rd2))
              w (step! w (complete (stamp w rd2) s/res-ok 7))]
          (is (= 0 (:pending (find-row w :comps c))))
          (is (= 1 (:version (find-row w :comps d))) "unchanged: no version step")
          (is (true? (st/comp-live (find-row w :comps c))) "unchanged settle: C live again without running"))))))

(deftest host-await-observe-handle-new
  (let [w s/empty-world
        [k rk w] (task-with-slice w)
        h (:next-id w)
        w (step! w (host-await k h))
        _ (is (= [s/ek-wait 0 k] ((juxt :kind :creditor :debtor) (find-row w :edges h))) "a pending host wait (root 7)")
        w (step! w (complete (stamp w rk) s/res-ok 3))]
    (is (nil? (find-row w :edges h)) "consumed when the task completes")
    (let [h2 (:next-id w)
          w (step! w (host-await k h2))]
      (is (nil? (find-row w :edges h2)) "fast path: a completed task is final"))
    (let [x (:next-id w)
          w (step! w (create-source-top root s/sk-signal 4 x))
          ob (:next-id w)
          w (step! w (observe x 1 ob))]
      (testing "T8: an observe on a source delivers at once (Z#15)"
        (is (= [true 0] ((juxt :has-seen :seen) (find-row w :edges ob)))))
      (testing "handle-new (Z#29): 0 -> 1 only (the observed source stays without a handle)"
        (let [w (step! w (handle-drop x))
              _ (is (= 0 (:handles (find-row w :sources x))))
              w (step! w (handle-new x))]
          (is (= 1 (:handles (find-row w :sources x))))
          (step! w (handle-new x) :refused))))))


;; ---------------------------------------------------------------------------
;; Sources (§4.3), finalizers (B3/B8), host cancel, scopes, release-world, ranks, Blocked

(defn src-row [w x] (find-row w :sources x))
(defn parked-task-on
  "a top-level task whose run awaits (T6 one) debtor d and parks; returns [k rk a w]"
  [w d]
  (let [[k rk w] (task-with-slice w)
        a (:next-id w)
        w (step! w (await* (stamp w rk) [d] s/am-one 1 a []))]
    [k rk a w]))

(deftest deliver-to-two-waiters
  (let [w s/empty-world
        x (:next-id w)
        w (step! w (create-source-top root s/sk-deferred 0 x))
        [k1 r1 a1 w] (parked-task-on w x)
        [k2 r2 a2 w] (parked-task-on w x)
        _ (is (= [s/act-parked s/act-parked] (mapv #(:act (find-row w :runs %)) [r1 r2])))
        w (step! w (deliver x 5))]
    (is (= [5 1 true] ((juxt :state :version :open) (src-row w x))) "delivered once: version 1, still open")
    (is (every? nil? [(find-row w :acts a1) (find-row w :acts a2)]) "both waiters resumed")
    (is (= [s/act-active s/act-active] (mapv #(:act (find-row w :runs %)) [r1 r2])))
    (is (empty? (filter #(= x (:debtor %)) (:edges w))) "every wait edge consumed")
    (step! w (deliver x 6) :refused)
    (testing "an await after delivery is fast (final, D1)"
      (let [w (step! w (schedule r1))
            a (:next-id w)
            w (step! w (await* (stamp w r1) [x] s/am-one 1 a []))]
        (is (nil? (find-row w :acts a)))
        (is (= s/act-active (:act (find-row w :runs r1))))))))

(deftest mailbox-fifo-skips-cancelled
  (let [w s/empty-world
        m (:next-id w)
        w (step! w (create-source-top root s/sk-mailbox 0 m))
        take-park (fn [w]
                    (let [[k rk w] (task-with-slice w)
                          a (:next-id w)
                          w (step! w (take* (stamp w rk) m 1 a))]
                      [k rk a w]))
        [k1 r1 a1 w] (take-park w)
        _ (is (= [s/act-parked [(s/->Member (inc a1) 0)]] [(:act (find-row w :runs r1)) (vec (:members (find-row w :acts a1)))]))
        [k2 r2 a2 w] (take-park w)
        [k3 r3 a3 w] (take-park w)
        w (step! w (cancel r1))
        _ (is (nil? (find-row w :acts a1)) "the cancelled waiter is gone")
        _ (is (= [s/res-err r/cancelled-code] ((juxt :tag :val) (:result (find-row w :tasks k1)))))
        w (step! w (post m 10))]
    (is (nil? (find-row w :acts a2)) "the oldest live waiter gets the first message")
    (is (some? (find-row w :acts a3)))
    (is (= s/act-active (:act (find-row w :runs r2))))
    (let [w (step! w (post m 11))
          _ (is (nil? (find-row w :acts a3)) "the next waiter gets the next one")
          w (step! w (post m 12))
          w (step! w (post m 13))]
      (is (= [12 13] (vec (:queue (src-row w m)))) "no waiter: queued in order")
      (is (= 4 (:version (src-row w m))))
      (testing "a take with queued messages consumes the head at once (two ids allocated)"
        (let [w (step! w (schedule r2))
              n (:next-id w)
              w (step! w (take* (stamp w r2) m 1 n))]
          (is (= [13] (vec (:queue (src-row w m)))))
          (is (= (+ n 2) (:next-id w)))
          (is (= [s/act-active true] ((juxt :act :slice) (find-row w :runs r2)))))))))

(deftest semaphore-release
  (let [w s/empty-world
        x (:next-id w)
        w (step! w (create-source-top root s/sk-semaphore 0 x))
        w (step! w (release x))
        _ (is (= [1 1] ((juxt :state :version) (src-row w x))) "no waiter: a permit")
        [k rk w] (task-with-slice w)
        w (step! w (take* (stamp w rk) x 1 (:next-id w)))
        _ (is (= [0 true] [(:state (src-row w x)) (:slice (find-row w :runs rk))]) "acquired at once")
        a (:next-id w)
        w (step! w (take* (stamp w rk) x 1 a))
        _ (is (= s/act-parked (:act (find-row w :runs rk))) "no permit: parks")
        w (step! w (release x))]
    (is (nil? (find-row w :acts a)) "the waiter gets the permit")
    (is (= 0 (:state (src-row w x))) "the count is unchanged")
    (is (= s/act-active (:act (find-row w :runs rk))))))

(deftest finalize-slices-until-retire
  (let [w s/empty-world
        y (:next-id w)
        w (step! w (create-source-top root s/sk-deferred 0 y))
        sg (:next-id w)
        w (step! w (create-source-top root s/sk-signal 0 sg))
        [k rk w] (task-with-slice w)
        w (step! w (finally-enter (stamp w rk)))
        w (step! w (track (stamp w rk) sg 1 (:next-id w)))
        w (step! w (finally-enter (stamp w rk)))
        _ (is (= [1 0] (mapv :at (:finalizers (find-row w :runs rk)))) "innermost first")
        _ (step! w (complete (stamp w rk) s/res-ok 1) :refused)         ; Z#43: open regions
        a (:next-id w)
        w (step! w (await* (stamp w rk) [y] s/am-one 1 a []))
        _ (step! w (finalize rk) :refused)
        _ (step! w (slice-exit rk) :refused)                             ; not done, no slice
        w (step! w (cancel rk))
        run (find-row w :runs rk)]
    (testing "host cancel of a parked task with finalizers: done, unwinding, cleanup entry, not retired"
      (is (= [s/act-done s/mode-unwinding false] ((juxt :act :mode :slice) run)))
      (is (some? (first (filter #(= rk (:run %)) (:cleanup w)))))
      (is (nil? (find-row w :acts a))))
    (let [w (step! w (finalize rk))
          _ (is (true? (:slice (find-row w :runs rk))) "the cleanup slice")
          _ (step! w (spawn (stamp w rk) 1 (:next-id w)) :refused)    ; B8
          _ (step! w (finally-enter (stamp w rk)) :refused)            ; B8: no new region
          _ (step! w (await* (stamp w rk) [sg] s/am-one 1 (:next-id w) []) :refused)
          ;; Z#40: a finalizer may only write, deliver, post, release and close
          _ (step! w (create-source (stamp w rk) s/sk-signal 0 (:next-id w)) :refused)
          _ (step! w (track (stamp w rk) sg 1 (:next-id w)) :refused)
          _ (step! w (arm (stamp w rk) s/rk-offload 0 (:next-id w)) :refused)
          _ (step! w (slice-exit rk) :refused)                           ; a region is still open
          w (step! w (finally-exit (stamp w rk)))                          ; commits at the block's start
          w (step! w (write sg 4))                                       ; a finalizer may write
          _ (is (= [[0] true] [(mapv :at (:finalizers (find-row w :runs rk))) (:slice (find-row w :runs rk))])
                "Z#35: the whole chain runs in the one cleanup slice")
          w (step! w (finally-exit (stamp w rk)))
          _ (is (= [[] true] [(mapv :at (:finalizers (find-row w :runs rk))) (:slice (find-row w :runs rk))])
                "the outermost block still runs in the slice")
          _ (step! w (finally-exit (stamp w rk)) :refused)                 ; no region: invalid token (L4)
          _ (step! w (finalize rk) :refused)
          w (step! w (slice-exit rk))]
      (is (nil? (find-row w :runs rk)) "the slice's return retires the run (T13, L2)")
      (is (empty? (:cleanup w))))))

(deftest scopes-and-detach
  (let [w s/empty-world
        [k rk w] (task-with-slice w)
        sx (:next-id w)
        w (step! w (open-scope (stamp w rk) sx))
        _ (is (= [(+ k 2) s/scope-explicit true] ((juxt :parent :kind :open) (find-row w :scopes sx))))
        c1 (:next-id w)
        w (step! w (spawn (stamp w rk) 1 c1 [7]))
        _ (is (= [sx [7]] ((juxt :owner (comp vec :inputs)) (find-row w :tasks c1))) "owned by the current scope")
        c2 (:next-id w)
        w (step! w (spawn (stamp w rk) 2 c2))
        w (step! w (detach c2 root))
        _ (is (= root (:owner (find-row w :tasks c2))))
        w (step! w (close-scope sx))]
    (is (= [s/res-err r/cancelled-code] ((juxt :tag :val) (:result (find-row w :tasks c1)))) "close cancels the scope's work")
    (is (= s/act-active (:act (find-row w :runs (inc c2)))) "the detached task survives")))

(deftest release-world-reclaims
  (let [w s/empty-world
        x (:next-id w)
        w (step! w (create-source-top root s/sk-signal 0 x))
        c (:next-id w)
        w (step! w (create-comp-top root c 1 1))
        w (step! w (observe c 1 (:next-id w)))
        w (step! w (pin x))
        y (:next-id w)
        w (step! w (create-source-top root s/sk-deferred 0 y))
        [k rk w] (task-with-slice w)
        w (step! w (finally-enter (stamp w rk)))
        w (step! w (await* (stamp w rk) [y] s/am-one 1 (:next-id w) []))
        h (:next-id w)
        w (step! w (host-await k h))
        w (step! w (release-world))]
    (is (true? (:released w)))
    (step! w (release-world) :refused)
    (testing "only the cleanup entry of the unwinding task run and its rows remain (with the run
              scope's ancestor, the root scope, Z#38)"
      (is (= #{rk (+ k 2) k root} (set (s/all-ids w))) (pr-str (s/all-ids w)))
      (is (= [rk] (mapv :run (:cleanup w)))))
    (let [w (step! w (finalize rk))
          w (step! w (finally-exit (stamp w rk)))
          w (step! w (slice-exit rk))]
      (is (= [root] (s/all-ids w)) "Z#56: everything but the root scope is reclaimed; the root scope stays")
      (is (empty? (:cleanup w))))))

;; Z#56 (2): a done task leaves its owner scope's task set at T13 retirement. The model keeps the
;; owner field until the row goes (T12/T14 drop nothing), so a retired child held by its handle keeps
;; its run's scope non-empty for `remove-if-empty`; Rule R's filter removes that closed scope in the
;; same step and detach clears the child's owner: the engine's end state, literal I1 throughout.
(deftest z56-retired-task-ownership
  (let [w s/empty-world
        [k rk w] (task-with-slice w)
        sk (+ k 2)
        b (:next-id w)
        w (step! w (spawn (stamp w rk) 9 b))
        w (step! w (await* (stamp w rk) [b] s/am-one 1 (:next-id w) [b]))
        w (step! w (schedule (inc b)))
        w (step! w (complete (stamp w (inc b)) s/res-ok 5))
        _ (is (= [sk 0] ((juxt :owner :run) (find-row w :tasks b))) "retired: K.run cleared, owner kept")
        _ (is (true? (inv/lit-i1-scope w)))
        w (step! w (schedule rk))
        w (step! w (complete (stamp w rk) s/res-ok 6))]
    (is (nil? (find-row w :scopes sk)) "rk's run scope goes at rk's retirement")
    (is (= [0 1] ((juxt :owner :handles) (find-row w :tasks b))) "the held child is detached")
    (is (true? (inv/lit-i1-scope w)))
    (is (true? (inv/inv-all w)))))

;; Z#56: (1) after T21 only the host's admissions are revoked (`host-shut`: a host item while no run
;; holds the slice); a cleanup slice's own effects (Z#44: host items while the slice is held) and
;; resource completions (fire, then ack) stay accepted,
;; so L2 can still join; (3) the root scope is never removed
(deftest release-world-keeps-cleanup-working
  (let [w s/empty-world
        [k rk w] (task-with-slice w)
        d (:next-id w)
        w (step! w (create-source (stamp w rk) s/sk-deferred 0 d))   ; owned by rk's run scope
        w (step! w (finally-enter (stamp w rk)))
        z (:next-id w)
        w (step! w (arm (stamp w rk) s/rk-offload 3 z))
        w (step! w (resource-fire z s/res-ok 1))                     ; f returned: rk resumes, z fired
        w (step! w (schedule rk))
        y (:next-id w)
        w (step! w (create-source-top root s/sk-deferred 0 y))
        w (step! w (await* (stamp w rk) [y] s/am-one 1 (:next-id w) []))
        w (step! w (release-world))
        _ (is (= [s/act-done s/mode-unwinding] ((juxt :act :mode) (find-row w :runs rk))))
        _ (is (= s/rp-fired (:phase (find-row w :res z))) "a fired resource waits for its acknowledgement")
        _ (step! w (pin d) :refused)                                  ; Z#56: a host admission, refused once released
        _ (step! w (spawn-top root 1 (:next-id w)) :refused)
        _ (step! w (create-source-top root s/sk-signal 0 (:next-id w)) :refused)
        w (step! w (finalize rk))
        w (step! w (pin d))                                           ; the cleanup slice's own effect (Z#44)
        w (step! w (unpin d))
        w (step! w (finally-exit (stamp w rk)))
        w (step! w (slice-exit rk))
        _ (is (some? (find-row w :runs rk)) "the outstanding resource holds the run")
        w (step! w (resource-ack z))]
    (is (nil? (find-row w :runs rk)) "the acknowledgement retires the run after release (L2)")
    (is (= [root] (s/all-ids w)) "the root scope is never removed")
    (is (false? (:open (find-row w :scopes root))) "closed by T21, kept as a row")))

(deftest await-cycle-refused-and-ranks
  (let [w s/empty-world
        c (:next-id w)
        w (step! w (create-comp-top root c 1 1))
        d (inc c)
        w (step! w (create-comp-top root d 2 2))
        w (step! w (observe c 1 (:next-id w)))
        rc (:next-id w)
        w (step! w (start c rc))
        w (step! w (schedule rc))
        w (step! w (await* (stamp w rc) [d] s/am-one 1 (:next-id w) []))
        _ (is (> (:rank (find-row w :comps c)) (:rank (find-row w :comps d))) "I12: rank(C) > rank(D)")
        rd (:next-id w)
        w (step! w (start d rd))
        w (step! w (schedule rd))]
    (step! w (await* (stamp w rd) [c] s/am-one 1 (:next-id w) []) :refused)
    (step! w (await* (stamp w rd) [d] s/am-one 1 (:next-id w) []) :refused)))

(defn blocked-chain
  "A, B, C observed; B (completed, then invalidated) re-runs and parks awaiting A; A parks on
  `a-on` (a deferred: blocked; a never-started computation: not blocked); C (completed, reading
  x and B) is invalidated by a write to x. Returns [w a b c]."
  [a-on-deferred?]
  (let [w s/empty-world
        x (:next-id w) w (step! w (create-source-top root s/sk-signal 0 x))
        z (:next-id w) w (step! w (create-source-top root s/sk-signal 0 z))
        y (:next-id w) w (step! w (create-source-top root s/sk-deferred 0 y))
        d (:next-id w) w (step! w (create-comp-top root d 9 9))
        a (:next-id w) w (step! w (create-comp-top root a 1 1))
        b (:next-id w) w (step! w (create-comp-top root b 2 2))
        c (:next-id w) w (step! w (create-comp-top root c 3 3))
        w (reduce (fn [w e] (step! w (observe e 1 (:next-id w)))) w [a b c])
        ra (:next-id w) w (step! w (start a ra)) w (step! w (schedule ra))
        w (step! w (await* (stamp w ra) [(if a-on-deferred? y d)] s/am-one 1 (:next-id w) []))
        rb (:next-id w) w (step! w (start b rb)) w (step! w (schedule rb))
        w (step! w (track (stamp w rb) z 1 (:next-id w)))
        w (step! w (complete (stamp w rb) s/res-ok 1))
        rc (:next-id w) w (step! w (start c rc)) w (step! w (schedule rc))
        w (step! w (track (stamp w rc) x 1 (:next-id w)))
        w (step! w (await* (stamp w rc) [b] s/am-one 1 (:next-id w) []))
        w (step! w (complete (stamp w rc) s/res-ok 2))
        w (step! w (write z 1))
        rb2 (:next-id w) w (step! w (dispatch-comp b rb2)) w (step! w (schedule rb2))
        w (step! w (await* (stamp w rb2) [a] s/am-one 1 (:next-id w) []))
        w (step! w (write x 1))]
    [w a b c]))

;; Z#55: a resource effect is ONE item `arm st kind k fresh`: resource fresh, `one` activation
;; fresh + 1 (cont k), its wait edge fresh + 2 on the resource; the run parks; effect-index + 1
(deftest z55-arm-one-effect
  (let [w s/empty-world
        [k rk w] (task-with-slice w)
        z (:next-id w)
        ei (:effect-index (find-row w :runs rk))
        w (step! w (arm (stamp w rk) s/rk-timer 9 z))]
    (testing "the allocation order and the park"
      (is (= [rk s/rk-timer ei s/rp-armed] ((juxt :owner :kind :at :phase) (find-row w :res z))))
      (is (= [rk s/am-one 9 [[(+ z 2) 0]]]
             ((juxt :run :mode :cont #(mapv (juxt :edge :idx) (:members %))) (find-row w :acts (inc z)))))
      (is (= [s/ek-wait (inc z) z ei] ((juxt :kind :creditor :debtor :at) (find-row w :edges (+ z 2)))))
      (is (= [s/act-parked false (inc ei) [z]] ((juxt :act :slice :effect-index (comp vec :resources)) (find-row w :runs rk))))
      (is (= (+ z 3) (:next-id w))))
    (testing "the fire resumes the run; the fired resource waits for its acknowledgement"
      (let [w2 (step! w (resource-fire z s/res-ok 1))]
        (is (= s/act-active (:act (find-row w2 :runs rk))))
        (is (nil? (find-row w2 :acts (inc z))))
        (is (= s/rp-fired (:phase (find-row w2 :res z))))
        (let [w3 (step! (step! w2 (schedule rk)) (complete (stamp (step! w2 (schedule rk)) rk) s/res-ok 3))]
          (is (some? (find-row w3 :runs rk)) "done, but the resource is outstanding")
          (is (nil? (find-row (step! w3 (resource-ack z)) :runs rk)) "T15 retires it within the item"))))
    (testing "T15 any time after T14 put the resource in cancelling (Z#55)"
      (let [w2 (step! w (cancel rk))]
        (is (= s/rp-cancelling (:phase (find-row w2 :res z))))
        (is (nil? (find-row w2 :acts (inc z))) "the activation goes with its wait edge")
        (is (nil? (find-row (step! w2 (resource-ack z)) :runs rk)) "the ack retires the run within the item")))
    (testing "kinds: timer (0) and offload (2) only; a fresh id other than next-id refuses"
      (let [k2 (:next-id w)
            w2 (step! (step! w (spawn-top root 1 k2)) (schedule (inc k2)))]
        (step! w2 (arm (stamp w2 (inc k2)) s/rk-external 0 (:next-id w2)) :refused)
        (step! w2 (arm (stamp w2 (inc k2)) s/rk-native 0 (:next-id w2)) :refused)
        (step! w2 (arm (stamp w2 (inc k2)) s/rk-offload 0 (inc (:next-id w2))) :refused)
        (step! w2 (arm (stamp w2 (inc k2)) s/rk-offload 0 (:next-id w2)))))))

;; Z#53: closing a source wakes its waiters and fills its unfilled members: a mailbox, a semaphore or
;; an undelivered deferred gives err ::closed (Nat 2); a signal, a cell or a delivered deferred its
;; value. Z#54: await/track/host-await by source kind.
(deftest z53-close-wakes-z54-kinds
  (let [w s/empty-world
        d0 (:next-id w)
        w (step! w (create-source-top root s/sk-deferred 0 d0))
        [k rk w] (task-with-slice w)
        y (:next-id w)
        w (step! w (create-source (stamp w rk) s/sk-deferred 0 y))      ; owned by rk's run scope
        m (:next-id w)
        w (step! w (create-source (stamp w rk) s/sk-semaphore 0 m))
        mb (:next-id w)
        w (step! w (create-source (stamp w rk) s/sk-mailbox 0 mb))
        _ (testing "Z#54: refused with no commit"
            (step! w (await* (stamp w rk) [m] s/am-one 1 (:next-id w) []) :refused)
            (step! w (await* (stamp w rk) [mb] s/am-one 1 (:next-id w) []) :refused)
            (step! w (await* (stamp w rk) [y mb] s/am-all 1 (:next-id w) []) :refused)
            (step! w (await* (stamp w rk) [y m] s/am-any 1 (:next-id w) []) :refused)
            (step! w (track (stamp w rk) y 1 (:next-id w)) :refused)
            (step! w (track (stamp w rk) mb 1 (:next-id w)) :refused)
            (step! w (host-await m (:next-id w)) :refused)
            (step! w (host-await mb (:next-id w)) :refused))
        w (step! w (await* (stamp w rk) [d0] s/am-one 1 (:next-id w) []))  ; rk parks
        k2 (:next-id w)
        w (step! w (spawn-top root 2 k2))
        r2 (inc k2)
        w (step! w (schedule r2))
        w (step! w (take* (stamp w r2) m 5 (:next-id w)))                ; r2 waits for a permit
        c (:next-id w)
        w (step! w (create-comp-top root c 1 1))
        w (step! w (observe c 1 (:next-id w)))
        rc (:next-id w)
        w (step! w (start c rc))
        w (step! w (schedule rc))
        a (:next-id w)
        w (step! w (await* (stamp w rc) [y] s/am-one 6 a []))            ; rc: dep member (inc a) on y
        _ (is (= [s/ek-dep y] ((juxt :kind :debtor) (find-row w :edges (inc a)))))
        h (:next-id w)
        w (step! w (host-await y h))
        _ (is (every? #(= s/act-parked (:act (find-row w :runs %))) [r2 rc]))
        w (step! w (cancel rk))]
    (testing "cancelling k closes its run scope's sources and wakes every waiter"
      (is (every? #(false? (:open (find-row w :sources %))) [y m mb]))
      (is (every? #(= s/act-active (:act (find-row w :runs %))) [r2 rc]) "the take and the member woke")
      (is (nil? (find-row w :edges (inc a))) "the member edge is consumed")
      (is (nil? (find-row w :edges h)) "the host wait is delivered")
      (is (= (s/->RunResult s/res-err 2) (st/deb-result w y)) "err ::closed")
      (is (true? (inv/lit-i5-dep-final w))))
    (testing "a closed source with a value delivers it"
      (is (= (s/->RunResult s/res-ok 7) (st/src-result (s/->SourceRow 1 0 s/sk-signal 7 3 false 1 []))))
      (is (= (s/->RunResult s/res-ok 7) (st/src-result (s/->SourceRow 1 0 s/sk-deferred 7 1 false 1 []))))
      (is (= (s/->RunResult s/res-err 2) (st/src-result (s/->SourceRow 1 0 s/sk-deferred 0 0 false 1 []))))
      (is (= (s/->RunResult s/res-ok 0) (st/src-result (s/->SourceRow 1 0 s/sk-mailbox 0 0 true 1 [])))
          "an open source: its state"))))

(deftest blocked-least-fixpoint
  (let [[w a b c] (blocked-chain true)]
    (is (true? (en/blocked-converged w)))
    (is (= #{a b} (set (filter #{a b c} (en/blocked-set w)))) "A blocked on a source, B transitively through A")
    (is (true? (en/needs-run w (find-row w :comps c))))
    (is (true? (en/eligible w (find-row w :comps c))) "C's dirty debtor B is blocked")
    (step! w (dispatch-comp c (:next-id w))))
  (let [[w a b c] (blocked-chain false)]
    (is (empty? (filter #{a b} (en/blocked-set w))) "A waits for a computation that is not blocked")
    (is (false? (en/eligible w (find-row w :comps c))))
    (step! w (dispatch-comp c (:next-id w)) :refused)))

;; ---------------------------------------------------------------------------
;; Random items of every kind

(defn random-item [^java.util.Random rng w]
  (let [pick (fn [xs] (if (seq xs) (nth (vec xs) (.nextInt rng (count xs))) 0))
        n (:next-id w)
        fresh (if (< (.nextInt rng 10) 9) n (inc n))
        id (fn [] (if (< (.nextInt rng 10) 8) (pick (s/all-ids w)) (+ n (.nextInt rng 3))))
        slice-runs (filter :slice (:runs w))
        st (fn [] (if (and (seq slice-runs) (< (.nextInt rng 10) 9)) (pick (map :stamp slice-runs))
                      (pick (map :stamp (:runs w)))))
        srcs (map :id (:sources w))
        src (fn [] (if (and (seq srcs) (< (.nextInt rng 10) 8)) (pick srcs) (id)))
        of-kind (fn [k] (let [xs (map :id (filter #(= k (:kind %)) (:sources w)))]
                          (if (and (seq xs) (< (.nextInt rng 10) 9)) (pick xs) (src))))
        comps (map :id (:comps w))
        cmp (fn [] (if (and (seq comps) (< (.nextInt rng 10) 8)) (pick comps) (id)))
        debtor (fn [] (pick (concat comps (map :id (:tasks w)) srcs (map :id (:res w)))))
        edges (map :id (:edges w))
        res (map :id (:res w))
        scopes (map :id (:scopes w))
        v (.nextInt rng 4)
        runnable (map :id (filter #(and (= s/act-active (:act %)) (not (:slice %))) (:runs w)))
        fresh-comps (map :id (filter #(zero? (:done-epoch %)) (:comps w)))
        unwinding (map :id (filter #(and (= s/mode-unwinding (:mode %)) (seq (:finalizers %))) (:runs w)))
        exiting (map :id (filter #(and (= s/act-done (:act %)) (:slice %) (empty? (:finalizers %))) (:runs w)))
        task-runs (map :run (filter #(pos? (:run %)) (:tasks w)))
        kinds (concat [0 1 2 2 3 3 4 4 5 6 7 8 9 10 11 12 13 13 14 14 15 15 16 16 17 17 17 18 18 18 18 19 19 19
                       20 20 20 20 21 21 21 21 22 23 24]
                      [25 25 26 26 27 27 27 28 28 29 29 29 29 29 29 30 30 30 32 32 33 33 34 35 35 35 35 36 36
                       37 37 37]
                      (when (zero? (.nextInt rng 8)) [31]))]
    (case (nth kinds (.nextInt rng (count kinds)))
      0 (create-source (st) (.nextInt rng 5) v fresh)
      1 (create-source-top (pick scopes) (.nextInt rng 5) v fresh)
      2 (write (src) v)
      3 (track (st) (src) (inc v) fresh)
      4 (observe (if (zero? (.nextInt rng 3)) (src) (cmp)) v fresh)
      5 (unobserve (pick edges))
      6 (fire (if (seq edges) (pick edges) (id)) s/res-ok v)
      7 (resource-ack (if (seq res) (pick res) (id)))
      8 (arm (st) (.nextInt rng 4) v fresh)
      9 (resource-fire (if (seq res) (pick res) (id)) s/res-ok v)
      10 (handle-drop (id))
      11 (pin (id))
      12 (unpin (pick (:pins w)))
      13 (create-comp (st) (if (zero? (.nextInt rng 2)) n (cmp)) (.nextInt rng 2) 1)
      14 (create-comp-top (pick scopes) (if (zero? (.nextInt rng 2)) n (cmp)) (.nextInt rng 2) 1)
      15 (spawn (st) 1 fresh)
      16 (spawn-top (pick scopes) 1 fresh)
      17 (start (if (seq fresh-comps) (pick fresh-comps) (cmp)) fresh)
      18 (let [ds (vec (repeatedly (inc (.nextInt rng 2)) debtor))
               mode (if (= 1 (count ds)) (.nextInt rng 3) (inc (.nextInt rng 2)))]
           (await* (st) ds mode (inc v) fresh (filter (set (map :id (:tasks w))) ds)))
      19 (dispatch-comp (cmp) fresh)
      20 (complete (st) s/res-ok v)
      21 (schedule (if (seq runnable) (pick runnable) (pick (map :id (:runs w)))))
      22 (host-await (debtor) fresh)
      23 (host-unawait (pick edges))
      24 (handle-new (id))
      25 (deliver (of-kind s/sk-deferred) v)
      26 (post (of-kind s/sk-mailbox) v)
      27 (take* (st) (of-kind (if (zero? (.nextInt rng 2)) s/sk-mailbox s/sk-semaphore)) (inc v) fresh)
      28 (release (of-kind s/sk-semaphore))
      29 (if (and (seq unwinding) (seq slice-runs) (not= s/mode-unwinding (:mode (first slice-runs))))
           (complete (:stamp (first slice-runs)) s/res-ok v)      ; free the slice for a cleanup slice
           (finalize (if (seq unwinding) (pick unwinding) (pick (map :id (:runs w))))))
      30 (cancel (if (seq task-runs) (pick task-runs) (pick (map :id (:runs w)))))
      31 (release-world)
      32 (open-scope (st) fresh)
      33 (close-scope (let [xs (map :id (filter #(= s/scope-explicit (:kind %)) (:scopes w)))]
                        (if (seq xs) (pick xs) (pick scopes))))
      34 (detach (pick (map :id (:tasks w))) (pick scopes))
      35 (finally-enter (st))
      36 (finally-exit (st))
      37 (slice-exit (if (seq exiting) (pick exiting) (pick (map :id (:runs w))))))))

;; a source x (3), an observed computation C (4) with a run (6) holding the slice, a task (9)
(defn prefix-world []
  (reduce (fn [w it] (:world (en/world-step w it))) s/empty-world
          [(create-source-top root s/sk-signal 0 3) (create-comp-top root 4 1 1) (observe 4 1 5)
           (start 4 6) (schedule 6) (spawn-top root 1 8)
           (create-source-top root s/sk-deferred 0 11) (create-source-top root s/sk-mailbox 0 12)
           (create-source-top root s/sk-semaphore 1 13)]))

(deftest random-steps
  ;; 60 runs (Z#55: arm parks its run, so tracks and slice exits got rarer on this seed)
  (let [rng (java.util.Random. 20261106)
        accepted (atom {})]
    (dotimes [run 60]
      (loop [i 0 w (prefix-world)]
        (when (< i 50)
          (let [item (random-item rng w)
                raw (en/raw w item)
                o (en/world-step w item)
                w2 (:world o)
                msg (str "run " run " step " i " " (pr-str item))]
            (is (rlt/ok? (:world raw)) (str "raw inv " msg))
            (if (:accepted raw)
              (do (swap! accepted update (first item) (fnil inc 0))
                  (is (= w2 (rlt/rule-r-checks (:world raw) msg)) msg))
              (do (is (= w2 w) (str "refusal changed the world " msg))
                  (is (= raw o))))
            (when (false? (en/raw-token-ok w item)) (is (= (st/->Outcome w false) o) (str "L4 " msg)))
            (is (rlt/ok? w2) msg)
            (is (true? (en/ranks-ok w2)) (str "I12 " msg))
            (is (true? (inv/inv-all w2)) (str "I1 I5 I7 I9 I10 I11a (spindel.v2.inv) " msg))
            (is (true? (en/blocked-converged w2)) (str "Blocked converged " msg))
            (recur (inc i) w2)))))
    (testing "the item kinds that matter were accepted"
      (is (every? #(pos? (get @accepted % 0)) [1 2 3 4 13 14 15 16 17 18 19 20 21 22 25 26 27 28 29 30 31 32 33 34 35 36 37])
          (pr-str (into (sorted-map) @accepted))))))
