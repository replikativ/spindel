(ns spindel.v2.engine-test
  "Loading spindel.v2.engine kernel-checks T3-T6, T11, T12, T22, the settle, validation and
  the model's step theorems. The deftests run scenarios built from items only (starting at
  `empty-world`) through the compiled `world-step`, and drive it with random items of every
  kind, checking after every step: well-formed with a plain pending count, Rule R's honest
  hypotheses, I3/I4 against the plain BFS of spindel.v2.retain-test, that a refusal leaves the
  world unchanged and that an invalid token is refused (L4)."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.step :as st]
            [spindel.v2.rule :as r]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.ledger :as lg]
            [spindel.v2.rule-test :as rlt]))

(def theorems
  '[cred-ok-mono deb-ok-mono comp-ins-edges-ref-ok task-ins-edges-ref-ok act-ins-edges-ref-ok
    well-formed-scope-ins-fresh well-formed-run-ins-fresh well-formed-task-ins-fresh well-formed-act-ins-fresh well-formed-comp-ins-fresh
    well-formed-insert-edge-checked well-formed-add-run-scope well-formed-react-one well-formed-react-loop well-formed-demand-reactive
    well-formed-spawn-rows well-formed-t4-spawn t4-spawn-refuse well-formed-t4-spawn-top t4-spawn-top-refuse well-formed-start-raw well-formed-t5-start t5-start-refuse
    well-formed-mark-from well-formed-create-comp-raw well-formed-t3-create t3-create-refuse well-formed-t3-create-top t3-create-top-refuse
    well-formed-cancel-pred well-formed-cut-suffix well-formed-consume-entry well-formed-new-run-of well-formed-dispatch-raw well-formed-t11-dispatch t11-dispatch-refuse
    well-formed-settle-edge well-formed-settle-one well-formed-settle-loop well-formed-settle well-formed-complete-body well-formed-retire-after
    well-formed-complete-raw well-formed-t12-complete t12-complete-refuse
    well-formed-await-step well-formed-await-wire well-formed-fast-fill well-formed-finalize-if-final well-formed-park-if well-formed-await-pre
    well-formed-await-post well-formed-await-raw well-formed-t6-await t6-await-refuse
    well-formed-host-await-raw well-formed-t22-host-await t22-host-await-refuse well-formed-t22-host-unawait t22-host-unawait-refuse well-formed-t8-observe-any-kind t8-observe-any-kind-refuse
    well-formed-t-schedule t-schedule-refuse well-formed-t-handle-new t-handle-new-refuse well-formed-cancel-losers
    well-formed-transition transition-refuse well-formed-raw raw-refuse transition-l4 raw-l4 step-refuse step-l4 step-accepted
    step-well-formed step-i3 step-normalized step-i4 step-i3-total step-normalized-total step-i4-total
    ;; sources, finalizers, host items, ranks, Blocked
    ids-ok-bump well-formed-bump well-formed-t-deliver t-deliver-refuse well-formed-serve-or well-formed-t-post t-post-refuse
    well-formed-t-release t-release-refuse well-formed-take-park well-formed-take-now well-formed-t-take t-take-refuse t-take-l4
    well-formed-t-finally-enter t-finally-enter-refuse t-finally-enter-l4 well-formed-t-finally-exit t-finally-exit-refuse
    t-finally-exit-l4 well-formed-t-finally-leave t-finally-leave-refuse t-finally-leave-l4 well-formed-t-slice-exit t-slice-exit-refuse well-formed-deliver-fire well-formed-dep-consumed well-formed-t-finalize t-finalize-refuse well-formed-t14-host-cancel t14-host-cancel-refuse
    well-formed-t-open-scope t-open-scope-refuse t-open-scope-l4 well-formed-t-close-scope t-close-scope-refuse
    well-formed-t-detach t-detach-refuse well-formed-zero-handles well-formed-revoke-roots well-formed-t21-release-world
    t21-release-world-refuse well-formed-raise-loop well-formed-raise-for well-formed-react-add blocked-sound blocked-complete
    well-formed-create-source-in-run well-formed-t1-create-nonstream t1-create-nonstream-refuse comp-demand-row-id
    ;; §2 re-entrant sites: the cont T6 writes, and the rule for both definitions
    await-cont-restart-with-finalizer await-cont-restart-with-resource await-cont-restart-unless-mode-one
    await-cont-reentrant-needs-no-finalizer reentrant-cont-needs-no-finalizer
    await-edge-cont edge-reawait-cont t6-await-reentrant-needs-no-finalizer])

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
(defn spawn ([st b fresh] (spawn st b fresh [])) ([st b fresh ins] [15 st b fresh (vec ins) false]))
(defn spawn-top ([scope b fresh] (spawn-top scope b fresh [])) ([scope b fresh ins] [16 scope b fresh (vec ins) false]))
(defn start [c fresh] [17 c fresh])
(defn await* [st ds mode k fresh mine] [18 st (vec ds) mode k fresh (vec mine)])
(defn dispatch-comp [c fresh] [19 c fresh])
(defn complete [st tag v] [20 st tag v])
(defn schedule [r] [21 r])
(defn host-await [d fresh] [22 d fresh])
(defn host-unawait [e] [23 e])
(defn handle-new [x] [24 x])
(defn deliver [x v] [25 x v])
(defn then-cancel-losers [x v] [26 x v])
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
(defn create-link [st l] [38 st l])
(defn create-link-top [scope l] [39 scope l])
(defn link-demand [l k] [40 l k])
(defn link-realize [l tag v n] [41 l tag v n])
(defn append* [x v t] [42 x v t])
(defn close* [x tag v] [43 x tag v])
(defn finally-leave [st] [44 st])

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
        w (step! w (then-cancel-losers m 10))]
    (is (nil? (find-row w :acts a2)) "the oldest live waiter gets the first message")
    (is (some? (find-row w :acts a3)))
    (is (= s/act-active (:act (find-row w :runs r2))))
    (let [w (step! w (then-cancel-losers m 11))
          _ (is (nil? (find-row w :acts a3)) "the next waiter gets the next one")
          w (step! w (then-cancel-losers m 12))
          w (step! w (then-cancel-losers m 13))]
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
  ;; Z#62: a semaphore starts with n > 0 permits, its maximum; a release at the maximum is refused
  (let [w s/empty-world
        x (:next-id w)
        w (step! w (create-source-top root s/sk-semaphore 1 x))
        _ (step! w (release x) :refused)
        [k rk w] (task-with-slice w)
        w (step! w (take* (stamp w rk) x 1 (:next-id w)))
        _ (is (= [0 true] [(:state (src-row w x)) (:slice (find-row w :runs rk))]) "acquired at once")
        w (step! w (release x))
        _ (is (= 1 (:state (src-row w x))) "no waiter: the permit returns")
        w (step! w (take* (stamp w rk) x 1 (:next-id w)))
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
          _ (step! w (slice-exit rk) :refused)                           ; C1: its clause runs
          _ (step! w (finally-exit (stamp w rk)) :refused)                 ; the head is the running clause
          w (step! w (write sg 4))                                       ; a finalizer may write
          w (step! w (finally-leave (stamp w rk)))                         ; C1: the clause ends
          _ (is (= [[0] true] [(mapv :at (:finalizers (find-row w :runs rk))) (:slice (find-row w :runs rk))])
                "Z#35: the whole chain runs in the one cleanup slice")
          _ (step! w (finally-leave (stamp w rk)) :refused)                ; no running clause
          w (step! w (finally-exit (stamp w rk)))
          w (step! w (finally-leave (stamp w rk)))
          _ (is (= [[] true] [(mapv :at (:finalizers (find-row w :runs rk))) (:slice (find-row w :runs rk))])
                "the outermost block ran in the slice")
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
          w (step! w (finally-leave (stamp w rk)))
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

;; Z#56: (1) after T21 only the host's admissions are revoked (`host-item-refused`: a host item while no run
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
        _ (step! w (pin d) :refused)                                  ; C1 Q5 (#269): no new root after T21, also from the cleanup slice
        w (step! w (finally-exit (stamp w rk)))
        w (step! w (finally-leave (stamp w rk)))
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
    (testing "kinds: timer, external (Z#63), offload and op; native refuses; a fresh id other than next-id refuses"
      (let [k2 (:next-id w)
            w2 (step! (step! w (spawn-top root 1 k2)) (schedule (inc k2)))]
        (step! w2 (arm (stamp w2 (inc k2)) s/rk-native 0 (:next-id w2)) :refused)
        (step! w2 (arm (stamp w2 (inc k2)) s/rk-external 0 (:next-id w2)))
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
      (is (= (s/->RunResult s/res-ok 7) (st/source-result (s/->SourceRow 1 0 s/sk-signal 7 3 false 1 [] 0 0 0 false 0))))
      (is (= (s/->RunResult s/res-ok 7) (st/source-result (s/->SourceRow 1 0 s/sk-deferred 7 1 false 1 [] 0 0 0 false 0))))
      (is (= (s/->RunResult s/res-err 2) (st/source-result (s/->SourceRow 1 0 s/sk-deferred 0 0 false 1 [] 0 0 0 false 0))))
      (is (= (s/->RunResult s/res-ok 0) (st/source-result (s/->SourceRow 1 0 s/sk-mailbox 0 0 true 1 [] 0 0 0 false 0)))
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
                       37 37 37 44 44 44]
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
      26 (then-cancel-losers (of-kind s/sk-mailbox) v)
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
      37 (slice-exit (if (seq exiting) (pick exiting) (pick (map :id (:runs w)))))
      44 (finally-leave (st)))))

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

;; C0 (links and streams): random items with the C0 kinds mixed in, same per-step checks
(defn random-c0-item [^java.util.Random rng w]
  (let [pick (fn [xs] (if (seq xs) (nth (vec xs) (.nextInt rng (count xs))) 0))
        n (:next-id w)
        links (filter #(= s/sk-link (:kind %)) (:sources w))
        pending (map :id (filter #(and (zero? (:version %)) (zero? (:tail %))) links))
        streams (map :id (filter #(= s/sk-stream (:kind %)) (:sources w)))
        slice-runs (filter :slice (:runs w))
        st (if (seq slice-runs) (:stamp (first slice-runs)) (pick (map :stamp (:runs w))))
        v (+ 3 (.nextInt rng 4))
        lk (fn [] (if (and (seq pending) (< (.nextInt rng 10) 8)) (pick pending) (pick (map :id links))))]
    (case (.nextInt rng 12)
      0 (create-link st (if (< (.nextInt rng 10) 8) n (pick (map :id links))))
      1 (create-link-top root n)
      2 (link-demand (lk) n)
      3 (link-demand (lk) n)
      4 (let [tag (.nextInt rng 3)] (link-realize (lk) tag v (if (= 1 tag) n 0)))
      5 (let [tag (.nextInt rng 3)] (link-realize (lk) tag v (if (= 1 tag) n 0)))
      6 (append* (pick streams) v n)
      7 (append* (pick streams) v n)
      8 (close* (pick streams) (* 2 (.nextInt rng 2)) v)
      9 (create-source-top root s/sk-stream 0 n)
      10 (create-source st s/sk-stream 0 n)
      11 (await* st [(lk)] s/am-one 1 n []))))

(deftest random-steps-c0
  (let [rng (java.util.Random. 20261115)
        accepted (atom {})]
    (dotimes [run 40]
      (loop [i 0 w (prefix-world)]
        (when (< i 50)
          (let [item (if (< (.nextInt rng 10) 4) (random-c0-item rng w) (random-item rng w))
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
    (testing "the C0 items were accepted"
      (is (every? #(pos? (get @accepted % 0)) [38 39 40 41 42 43])
          (pr-str (into (sorted-map) @accepted))))))

;; C0 (engine session 2026-11-16): T14 on a link's realizer clears the link's rtask (engine
;; link-cancelled!); T8 observe on a stream is refused (no edge, no item), as await/T22
(deftest c0-realizer-cancel-and-stream-observe
  (let [step (fn [w it] (let [o (en/world-step w it)] [(:accepted o) (:world o)]))
        w0 s/empty-world
        l (:next-id w0)
        [a1 w1] (step w0 (create-link-top root l))
        k (:next-id w1)
        [a2 w2] (step w1 (link-demand l k))
        r (:run (find-row w2 :tasks k))
        [a3 w3] (step w2 (cancel r))
        sx (:next-id w3)
        [a4 w4] (step w3 (create-source-top root s/sk-stream 0 sx))
        [a5 w5] (step w4 (observe sx 1 (:next-id w4)))]
    (is (= [true true true true false] [a1 a2 a3 a4 a5]))
    (is (= k (:rtask (find-row w2 :sources l))) "demand sets the realizer")
    (is (= 0 (:rtask (find-row w3 :sources l))) "the realizer's cancel clears rtask")
    (is (= w4 w5) "observe on a stream is refused")))

;; C0 (engine session, feat/v2-world-completion): a link owned by the root scope is created only
;; while the root scope is open, and no link is realized once it is closed (transition's `require-root-open`): with
;; the root scope closed (T21) an append is refused (the engine logs [:append s v 0] accepted false),
;; so are create-link-top and link-realize with every tag (the engine's link-done! realizes nothing)
(deftest c0-root-gate
  (let [step (fn [w i] (en/world-step w i))
        sx (:next-id s/empty-world)
        w1 (:world (step s/empty-world (create-source-top root s/sk-stream 0 sx)))
        l (:next-id w1)
        w2 (:world (step w1 (create-link-top root l)))
        shut (fn [w] (update w :scopes (fn [ss] (map #(if (= (:id %) root) (st/scope-close %) %) ss))))
        w3 (shut w2)
        acc (fn [w it] (:accepted (en/transition w it)))]
    (is (true? (st/scope-open-at w2 root)))
    (is (false? (st/scope-open-at w3 root)))
    (is (= [true true true true true]
           [(acc w2 (append* sx 5 (:next-id w2))) (acc w2 (link-realize l 1 5 (:next-id w2)))
            (acc w2 (link-realize l 0 0 0)) (acc w2 (link-realize l 2 9 0))
            (acc w2 (create-link-top root (:next-id w2)))]) "root scope open: accepted")
    (is (false? (acc w3 (append* sx 5 (:next-id w3)))) "append refused under a closed root scope")
    (is (= w3 (:world (en/transition w3 (append* sx 5 (:next-id w3))))) "and changes nothing")
    (is (false? (acc w3 (link-realize l 1 5 (:next-id w3)))) "no next link under a closed root scope")
    (is (false? (acc w3 (create-link-top root (:next-id w3)))))
    (doseq [it [(link-realize l 0 0 0) (link-realize l 2 9 0)]]
      (is (false? (acc w3 it)) (str "no realization under a closed root scope " (pr-str it)))
      (is (= w3 (:world (en/transition w3 it))) "and the world is unchanged"))))

;; ---------------------------------------------------------------------------
;; C1 (spec Z#67, T14, T21, B8 reduced; engine 823771c)

(defn- c1-steps [w0 fs]
  (reduce (fn [[w log] f] (let [it (f w) o (en/world-step w it)] [(:world o) (conj log [it (:accepted o)])]))
          [w0 []] fs))
(defn- task-run [w k] (:run (find-row w :tasks k)))

;; W1: complete = released, no unretired run (and no open child: layer 2); a run kept by an
;; outstanding resource keeps a released world incomplete until its acknowledgement (sample 27)
(deftest c1-completion
  (let [[w log] (c1-steps s/empty-world
                         [(fn [w] (spawn-top root 1 (:next-id w)))
                          (fn [w] (schedule (task-run w 3)))
                          (fn [w] (arm (stamp w (task-run w 3)) s/rk-offload 7 (:next-id w)))
                          (fn [w] (release-world))])
        z (:id (first (:res w)))
        [w2 log2] (c1-steps w [(fn [_] (resource-fire z 1 0)) (fn [_] (resource-ack z))])]
    (is (every? second log) (pr-str log))
    (is (= 1 (en/world-runs w)) "the cancelled run waits for its offload")
    (is (false? (en/world-quiet w)) "released, not complete")
    (is (= [false true] (mapv second log2)) "the cancelling offload's fire is refused, its ack accepted")
    (is (= 0 (en/world-runs w2)))
    (is (true? (en/world-quiet w2)) "complete after the acknowledgement retires the run")))

;; T14 (C1): a cancellation reaches the whole run-scope subtree in its item: the runs of the tasks
;; in the run's explicit scopes, nested ones included (sample 22)
(deftest c1-subtree-cancel
  (let [k (:next-id s/empty-world)
        [w log] (c1-steps s/empty-world
                         [(fn [w] (spawn-top root 1 (:next-id w)))
                          (fn [w] (schedule (task-run w k)))
                          (fn [w] (open-scope (stamp w (task-run w k)) (:next-id w)))
                          (fn [w] (spawn (stamp w (task-run w k)) 2 (:next-id w)))
                          (fn [w] (open-scope (stamp w (task-run w k)) (:next-id w)))
                          (fn [w] (spawn (stamp w (task-run w k)) 3 (:next-id w)))
                          (fn [w] (create-source (stamp w (task-run w k)) s/sk-deferred 0 (:next-id w)))
                          (fn [w] (await* (stamp w (task-run w k)) [(apply max (map :id (:sources w)))] s/am-one 1 (:next-id w) []))])
        kids (remove #{k} (map :id (:tasks w)))
        runs (fn [w] (map #(find-row w :runs (task-run w %)) kids))
        o (en/world-step w (cancel (task-run w k)))]
    (is (every? second log) (pr-str log))
    (is (= 2 (count kids)) "two child tasks, in nested explicit scopes")
    (is (every? #(= s/act-active (:act %)) (runs w)))
    (is (:accepted o))
    (is (every? #(or (nil? %) (= s/act-done (:act %))) (runs (:world o))) "both cancelled by the one cancel item")))

;; B8 reduced (C1): in a cancelled run's finally clause (its cleanup slice) every await and take is
;; refused, settled debtor or not (sample 25); the item is never logged
(deftest c1-finalizer-refusal
  (let [k (:next-id s/empty-world)
        [w log] (c1-steps s/empty-world
                         [(fn [w] (create-source-top root s/sk-signal 5 (:next-id w)))
                          (fn [w] (create-source-top root s/sk-mailbox 0 (:next-id w)))
                          (fn [w] (spawn-top root 1 (:next-id w)))
                          (fn [w] (schedule (task-run w (+ k 2))))
                          (fn [w] (finally-enter (stamp w (task-run w (+ k 2)))))
                          (fn [w] (create-source (stamp w (task-run w (+ k 2))) s/sk-deferred 0 (:next-id w)))
                          (fn [w] (await* (stamp w (task-run w (+ k 2))) [(dec (:next-id w))] s/am-one 1 (:next-id w) []))])
        r (task-run w (+ k 2))]
    (is (every? second log) (pr-str log))
    (let [w1 (:world (en/world-step w (cancel r)))
          o2 (en/world-step w1 (finalize r))
          w2 (:world o2)
          st (stamp w2 r)]
      (is (:accepted o2) "T14 schedules the head finalizer as a cleanup slice")
      (is (true? (en/in-cleanup w2 st)) "the cancelled run's cleanup slice")
      (is (false? (:accepted (en/world-step w2 (await* st [k] s/am-one 1 (:next-id w2) [])))) "await on a settled signal: refused")
      (is (false? (:accepted (en/world-step w2 (take* st (inc k) 1 (:next-id w2))))) "take: refused"))))

;; C1 A5 (B8 for normal runs): between `finally-exit` and `finally-leave` a normal run's suspending
;; effects are refused (an await on an unsettled debtor, a take with nothing to take, every arm);
;; settled awaits, writes and creations are accepted; completion waits for the clause's end
(deftest c1-normal-finally-clause
  (let [w s/empty-world
        sg (:next-id w)
        w (step! w (create-source-top root s/sk-signal 5 sg))
        d (:next-id w)
        w (step! w (create-source-top root s/sk-deferred 0 d))
        mb (:next-id w)
        w (step! w (create-source-top root s/sk-mailbox 0 mb))
        [k rk w] (task-with-slice w)
        st (stamp w rk)
        _ (step! w (finally-leave st) :refused)                          ; no clause
        w (step! w (finally-enter st))
        _ (is (false? (en/in-finally w st)) "a region is no clause")
        w (step! w (finally-exit st))
        _ (is (true? (en/in-finally w st)) "the clause runs")
        _ (step! w (await* st [d] s/am-one 1 (:next-id w) []) :refused)   ; would suspend
        _ (step! w (await* st [sg d] s/am-all 1 (:next-id w) []) :refused)
        _ (step! w (take* st mb 1 (:next-id w)) :refused)
        _ (step! w (arm st s/rk-timer 1 (:next-id w)) :refused)
        _ (step! w (complete st s/res-ok 1) :refused)                    ; the clause is open
        _ (step! w (finally-exit st) :refused)                           ; no region at the head
        _ (step! w (await* st [sg] s/am-one 1 (:next-id w) []))          ; settled: read at once
        _ (step! w (await* st [sg d] s/am-any 1 (:next-id w) []))
        w (step! w (write sg 6))
        w (step! w (finally-leave st))
        _ (is (false? (en/in-finally w st)))
        _ (is (empty? (:finalizers (find-row w :runs rk))))
        w (step! w (await* st [d] s/am-one 1 (:next-id w) []))]
    (is (= s/act-parked (:act (find-row w :runs rk))) "outside the clause the await parks")))

;; C1 Q5/Q8 (spindel #269): after T21 a cancelled run's cleanup slice still holds the slice, but a
;; released world takes no new root, handle or creation: observe, pin and host waits are refused there, so the world
;; is quiet once the slice exits and the computation cannot start (the former counterexample to
;; completion stability)
(deftest c1-no-roots-after-release
  (let [w0 s/empty-world
        c (:next-id w0)
        w (step! w0 (create-comp-top root c 1 1))
        w (step! w (observe c 1 (:next-id w)))
        w (step! w (start c (:next-id w)))
        r (:run (find-row w :comps c))
        w (step! w (schedule r))
        w (step! w (release-world))
        _ (is (true? (:slice (find-row w :runs r))) "the cancelled run still holds the slice")
        _ (is (= s/mode-unwinding (:mode (find-row w :runs r))))
        _ (step! w (observe c 1 (:next-id w)) :refused)
        _ (step! w (pin c) :refused)
        _ (step! w (host-await c (:next-id w)) :refused)
        _ (step! w (handle-new c) :refused)                             ; Q8: no new handle (admission) either
        _ (step! w (create-comp-top root (:next-id w) 1 1) :refused)
        _ (step! w (spawn-top root 1 (:next-id w)) :refused)
        w (step! w (slice-exit r))]
    (is (true? (en/world-quiet w)) "released, no run")
    (is (empty? (:pins w)))
    (is (nil? (find-row w :comps c)) "nothing retains the computation")
    (is (false? (:accepted (en/world-step w (start c (:next-id w))))) "it cannot start")))

;; E4 (C1): an unborn instance released before its activation only sets the flag: nothing in it
;; runs (sample 24); a done task run that holds no slice is still cancellable, with no row change
(deftest c1-unborn-release-and-done-cancel
  (let [w (:world (en/world-step (prefix-world) (release-world)))
        w0 (prefix-world)
        wu (en/release-unborn w0)]
    (is (true? (:released wu)))
    (is (= (dissoc w0 :released) (dissoc wu :released)) "the rows stay as copied")
    (is (pos? (en/world-runs wu)) "complete at once all the same (layer 2): its runs never run")
    (is (some? w)))
  (let [k (:next-id s/empty-world)
        [w log] (c1-steps s/empty-world
                         [(fn [w] (spawn-top root 1 (:next-id w)))
                          (fn [w] (schedule (task-run w k)))
                          (fn [w] (arm (stamp w (task-run w k)) s/rk-offload 7 (:next-id w)))])
        r (task-run w k)
        z (:id (first (:res w)))
        w1 (:world (en/world-step w (resource-fire z 1 0)))
        w2 (:world (en/world-step w1 (schedule r)))
        w3 (:world (en/world-step w2 (complete (stamp w2 r) 1 5)))]
    (is (every? second log))
    (when (find-row w3 :runs r)
      (is (= s/act-done (:act (find-row w3 :runs r))))
      (let [o (en/world-step w3 (cancel r))]
        (is (:accepted o) "accepted on a done run")
        (is (= (:world o) (:world (en/world-step w3 (cancel r)))))))))

;; C1 Q6 + engine session: handle-new on a tombstone is refused (the engine's handle! on an existing
;; row runs only through adoption, which finds the row through a reference; a tombstone has none)
(deftest c1-handle-new-tombstone-refused
  (let [w0 s/empty-world
        c (:next-id w0)
        w (step! w0 (create-comp-top root c 1 1))
        e (:next-id w)
        w (step! w (observe c 1 e))
        w (step! w (start c (:next-id w)))
        r (:run (find-row w :comps c))
        w (step! w (schedule r))
        w (step! w (handle-drop c))
        w (step! w (unobserve e))]
    (is (= {:idle false :tomb true :handles 0 :run r} (select-keys (find-row w :comps c) [:idle :tomb :handles :run]))
        "unobserved, no handle, no result, its run cancelled in its cleanup slice: a tombstone")
    (is (true? (:slice (find-row w :runs r))))
    (step! w (handle-new c) :refused)))

;; Z#69 (engine PR #272, task_test `detach-into-own-subtree-is-refused`): detach is refused into a
;; scope of the task's own run-scope subtree (re-parenting the run scope under it would close a cycle
;; of parents, and neither scope could ever be removed); into an outer open scope it is accepted.
;; `scope-cycle?` walks the parent fields directly (independent of the model's `scope-ancestors`).
(defn scope-cycle? [w]
  (let [par (into {} (map (juxt :id :parent) (:scopes w)))]
    (boolean (some (fn [s] (loop [x (par s) n 0]
                             (cond (or (nil? x) (zero? x)) false
                                   (= x s) true
                                   (> n (count par)) true
                                   :else (recur (par x) (inc n)))))
                   (keys par)))))

(deftest z69-detach-into-own-subtree-refused
  (let [w s/empty-world
        [k0 rk0 w] (task-with-slice w)                                      ; K0 holds the slice
        o (:next-id w)
        w (step! w (open-scope (stamp w rk0) o))                            ; K0 opens O
        j (:next-id w)
        rj (inc j)
        sj (+ j 2)
        w (step! w (spawn (stamp w rk0) 5 j))                               ; J, owned by O
        _ (is (= [o o] [(:owner (find-row w :tasks j)) (:parent (find-row w :scopes sj))]))
        y (:next-id w)
        w (step! w (create-source (stamp w rk0) s/sk-deferred 0 y))
        w (step! w (await* (stamp w rk0) [y] s/am-one 1 (:next-id w) []))  ; K0 parks
        w (step! w (schedule rj))
        s (:next-id w)
        w (step! w (open-scope (stamp w rj) s))                             ; J opens S below its run scope
        _ (is (= sj (:parent (find-row w :scopes s))))
        _ (is (false? (scope-cycle? w)))]
    (testing "refused into J's own subtree (S, or J's run scope itself); the world is unchanged"
      (step! w (detach j s) :refused)
      (step! w (detach j sj) :refused)
      (is (true? (en/scope-within w s sj)) "J's run scope is on S's parent chain")
      (is (true? (scope-cycle? (en/detach-move w j s sj)))
          "without the guard the move makes S and J's run scope each other's ancestor"))
    (testing "accepted into an outer open scope (the root scope): J and its run scope move there"
      (let [w2 (step! w (detach j root))]
        (is (= [root root] [(:owner (find-row w2 :tasks j)) (:parent (find-row w2 :scopes sj))]))
        (is (= sj (:parent (find-row w2 :scopes s))))
        (is (false? (scope-cycle? w2)))
        (is (true? (:open (find-row w2 :scopes o))) "O stays K0's open scope")))))

;; ---------------------------------------------------------------------------
;; C1c stage A (spec Z#70, engine 1aac850): completion is derived from the scope tree (spindel.v2.ledger).
;; A task is complete when done, its run retired and its run scope (k + 2) removed or never materialized; a scope
;; when its row is removed. The scenario of sample 30, with an offload for the grandchild's host work: P opens the
;; explicit scope E and spawns C in it; C spawns G in its run scope; G arms an offload. C completes (its retirement
;; cancels G, whose run stays in cleanup until the offload's acknowledgement), P closes E and completes. P and C are
;; done and retired but wait for their run scopes; G is done (cancelled) with its run unretired. G's retirement
;; completes everything: G's run scope was never materialized, the others are removed in the same step (Rule R).
(deftest c1c-completion-ledger
  (let [w s/empty-world
        d (:next-id w)
        w (step! w (create-source-top root s/sk-deferred 0 d))
        [p rp w] (task-with-slice w)
        e (:next-id w)
        w (step! w (open-scope (stamp w rp) e))
        c (:next-id w)
        rc (inc c)
        w (step! w (spawn (stamp w rp) 2 c))
        w (step! w (await* (stamp w rp) [d] s/am-one 1 (:next-id w) []))
        w (step! w (schedule rc))
        g (:next-id w)
        rg (inc g)
        w (step! w (spawn (stamp w rc) 3 g))
        w (step! w (await* (stamp w rc) [d] s/am-one 1 (:next-id w) []))
        w (step! w (schedule rg))
        z (:next-id w)
        w (step! w (arm (stamp w rg) s/rk-offload 7 z))
        tc (fn [w] (mapv #(lg/task-complete w %) [p c g]))
        sc (fn [w] (mapv #(lg/scope-complete w %) [(+ p 2) e (+ c 2)]))
        _ (testing "condition 1, not done: nothing complete while the three run"
            (is (= [e (+ p 2) (+ c 2)] (mapv #(:parent (find-row w :scopes %)) [(+ c 2) e (+ g 2)]))
                "the scope tree: P's run scope > E > C's run scope > G's run scope")
            (is (= [false false false] (tc w)))
            (is (= [false false false] (sc w))))
        w (step! w (deliver d 5))
        w (step! w (schedule rc))
        w (step! w (complete (stamp w rc) s/res-ok 1))
        _ (testing "C done and retired, its run scope still present (G is held): not complete"
            (is (= [true true] ((juxt #(= s/res-ok (:tag (:result %))) #(zero? (:run %))) (find-row w :tasks c))))
            (is (some? (find-row w :scopes (+ c 2))))
            (is (false? (lg/task-complete w c))))
        _ (testing "condition 2, G done (cancelled with C's run scope, Q10) but its run unretired: not complete"
            (is (not= s/res-none (:tag (:result (find-row w :tasks g)))))
            (is (pos? (:run (find-row w :tasks g))))
            (is (false? (lg/task-complete w g))))
        w (step! w (schedule rp))
        w (step! w (close-scope e))
        w (step! w (complete (stamp w rp) s/res-ok 2))
        _ (testing "condition 3, P done and retired, its run scope kept by the subtree: not complete"
            (is (= [true true] ((juxt #(= s/res-ok (:tag (:result %))) #(zero? (:run %))) (find-row w :tasks p))))
            (is (= [false false false] (tc w)))
            (is (= [false false false] (sc w)) "E closed, but its row stays (G's cleanup keeps its chain)")
            (is (false? (:open (find-row w :scopes e)))))
        w (step! w (resource-ack z))]
    (testing "G retires: every task and scope of the subtree is complete in that step"
      (is (= [true true true] (tc w)))
      (is (= [true true true] (sc w)))
      (is (true? (lg/scope-complete w (+ g 2))) "G's run scope, never materialized, went at G's retirement")
      (is (false? (lg/scope-complete w root)) "the root scope is never removed"))))
