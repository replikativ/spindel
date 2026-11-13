(ns spindel.v2.hm13-test
  "Independent manifest-first contracts and raw/post checkpoints; no normalized-step H3 claim."
  (:require [clojure.test :refer [deftest is testing]] [clojure.edn :as edn] [clojure.java.io :as io]
            [ansatz.core :as a] [ansatz.kernel.env :as env] [ansatz.surface.elaborate :as elab]
            [ansatz.kernel.tc :as tc] [spindel.v2.hm13]
            [spindel.v2.hm12-test :as prior] [spindel.v2.hm10-test :as fill]
            [spindel.v2.hm9-test :as wiring] [spindel.v2.hm8-test :as fixture]
            [spindel.v2.hm7-test :as closed] [spindel.v2.hm6-test :as certification]
            [spindel.v2.state :as s] [spindel.v2.step :as step] [spindel.v2.engine :as engine]
            [spindel.v2.rule :as rule] [spindel.v2.retain :as retain] [spindel.v2.hm6-base :as base]
            [spindel.v2.hm3 :as hm3] [spindel.v2.hmk :as hmk] [spindel.v2.hm6 :as hm6]
            [spindel.v2.i10 :as i10])
  (:import [ansatz.kernel ConstantInfo]))
(def manifest (edn/read-string (slurp "notes/hm13-contracts.edn")))
(def public-contracts (:public-contracts manifest))
(def dependency-contracts (:dependency-contracts manifest))
(def helper-definitions (:helpers manifest))
(defn declaration [name] (prior/declaration name))
(defn source-forms [] (prior/forms-at "spindel/v2/hm13.clj"))
(def theorems (mapv second (filter #(= 'a/theorem (first %)) (source-forms))))
(def expected-definitions
  '{any-resolved
 (a/defn
  any-resolved
  [w1 :- World a :- ActRow]
  Bool
  (Bool.and
   (Nat.beq (:mode a) am-any)
   (Bool.and
    (Bool.not (act-has w1 (:id a)))
    (Bool.and
     (opt-test run-alive (run-find w1 (:run a)))
     (opt-test (run-of-task w1) (run-find w1 (:run a))))))),
 cancel-losers
 (a/defn
  cancel-losers
  [w0 :- World w1 :- World]
  World
  (run-cascade
   w1
   (cancel-jobs
    (tbl-gather (any-resolved w1) (loser-runs w1) (:acts w0))))),
 g10r
 (a/defn g10r [w :- World] Bool (g10 (List.nil Nat) (List.nil Nat) w)),
 host-item
 (a/defn
  host-item
  [it :- Item]
  Bool
  (match
   it
   [(create-source st kind v fresh) false]
   [(create-source-top scope kind v fresh) true]
   [(write x v) true]
   [(track st x k fresh) false]
   [(observe d cb fresh) true]
   [(unobserve e) true]
   [(fire e tag val) false]
   [(resource-ack z) false]
   [(arm st kind k fresh) false]
   [(resource-fire z tag val) false]
   [(handle-drop x) true]
   [(pin x) true]
   [(unpin x) true]
   [(create-comp st c i b) false]
   [(create-comp-top sc c i b) true]
   [(spawn st b fresh ins) false]
   [(spawn-top sc b fresh ins) true]
   [(start c fresh) false]
   [(await st ds m k fresh mine) false]
   [(dispatch-comp c fresh) false]
   [(complete st tag val) false]
   [(schedule r) false]
   [(host-await d fresh) true]
   [(host-unawait e) true]
   [(handle-new x) true]
   [(deliver x v) true]
   [(post x v) true]
   [(take st x k fresh) false]
   [(release x) true]
   [(finalize r) false]
   [(cancel r) true]
   [(release-world) false]
   [(open-scope st s) false]
   [(close-scope s) true]
   [(detach k s) true]
   [(finally-enter st) false]
   [(finally-exit st) false]
   [(slice-exit r) false])),
 loser-task
 (a/defn
  loser-task
  [w1 :- World s :- Nat k :- Nat]
  Bool
  (Bool.and
   (tbl-all (no-debtor k) (:edges w1))
   (match
    (task-find w1 k)
    [none false]
    [(some t)
     (Bool.and
      (Nat.beq (:owner t) s)
      (opt-test run-alive (run-find w1 (:run t))))]))),
 post
 (a/defn
  post
  [w :- World o :- Outcome]
  Outcome
  (if (:accepted o) (accept (cancel-losers w (:world o))) o)),
 raw
 (a/defn raw [w :- World it :- Item] Outcome (post w (raw0g w it))),
 raw0g
 (a/defn
  raw0g
  [w :- World it :- Item]
  Outcome
  (if (host-shut w it) (refuse w) (raw0 w it)))}
)

(defn expanded-contract [contract]
  (list 'let (vec (mapcat (fn [n] (let [[_ _ parameters _ body] (get expected-definitions n)]
                                     [n (list 'fn parameters body)])) '[g10r raw0g post raw])) contract))

(deftest exact-manifest-and-safe-closed-contracts
  (is (= 5 (count public-contracts))) (is (empty? helper-definitions))
  (is (= (:source-inventory manifest) theorems))
  (is (= 6 (count (source-forms))))
  (is (empty? (filter #(= 'a/defn (first %)) (source-forms))))
  (doseq [{:keys [name type]} public-contracts]
    (let [^ConstantInfo d (certification/checked-declaration name)
          literal (elab/elaborate @a/ansatz-env type)
          expanded (elab/elaborate @a/ansatz-env (expanded-contract type))]
      (is (= (closed/type-form literal) (closed/type-form (.-type d))))
      (is (seq (closed/type-form expanded)))
      (is (tc/is-def-eq (tc/mk-tc-state @a/ansatz-env) (.-type d) expanded))))
  (doseq [[name type] dependency-contracts]
    (let [^ConstantInfo d (certification/checked-declaration name)]
      (is (= (closed/type-form (elab/elaborate @a/ansatz-env type))
             (closed/type-form (.-type d))) (str name " actual dependency")))))

(deftest actual-support-definitions-and-constructor
  (let [before @a/ansatz-env
        source (merge (into {} (map (juxt second identity) (filter seq? (prior/forms-at "spindel/v2/engine.clj"))))
                      (into {} (map (juxt second identity) (filter seq? (prior/forms-at "spindel/v2/i10.clj")))))]
    (doseq [[name [_ _ parameters result body :as expected]] expected-definitions]
      (let [^ConstantInfo d (declaration name)
            value (elab/elaborate @a/ansatz-env (list 'fn parameters body) (.-type d))]
        (is (= expected (get source name))) (is (= :def (env/ci-tag d))) (is (zero? (.-safety d)))
        (is (seq (closed/type-form (.value d))))
        (is (= (closed/type-form (elab/elaborate @a/ansatz-env (list 'forall parameters result)))
               (closed/type-form (.-type d))))
        (is (tc/is-def-eq (tc/mk-tc-state @a/ansatz-env) (.value d) value) (str name " actual value"))))
    (is (identical? before @a/ansatz-env) "read-only independent value elaboration")
    (let [^ConstantInfo d (declaration 'Item.await)]
      (is (= :ctor (env/ci-tag d))) (is (zero? (.-safety d)))
      (is (= (closed/type-form (elab/elaborate @a/ansatz-env prior/item-await-signature))
             (closed/type-form (.-type d)))))))

(defn row [w table id] (fixture/row w table id))
(defn check-support [w]
  (is (true? (hmk/hmk [] w))) (is (true? (i10/g10 [] [] w))) (is (true? (hm6/ekb w))))
(defn check-post [w0 outcome xm]
  (let [w1 (:world outcome), after (engine/post w0 outcome)]
    (check-support w1) (is (true? (hm3/h3 xm w1)))
    (is (true? (hm3/h3 xm (:world after))))
    (if (:accepted outcome)
      (is (= (step/->Outcome (engine/cancel-losers w0 w1) true) after))
      (is (= outcome after) "arbitrary refused Outcome itself is retained"))
    after))
(defn check-await [w st ds mode k fresh mine xm]
  (let [item [18 st ds mode k fresh mine], r0 (engine/raw0 w item)
        rg (engine/raw0g w item), actual (engine/raw w item)]
    (is (true? (base/p3la w))) (is (true? (hm3/h3 xm w)))
    (is (false? (engine/host-item item))) (is (false? (engine/host-shut w item)))
    (is (= r0 rg)) (check-support (:world rg))
    (is (true? (hm3/h3 xm (:world rg))))
    (is (= actual (check-post w rg xm)))
    (is (= (:accepted r0) (:accepted actual)))
    (if (:accepted r0)
      (is (= (step/->Outcome (engine/cancel-losers w (:world r0)) true) actual))
      (do (is (= w (:world rg) (:world actual))) (is (= (step/->Outcome w false) actual))))
    actual))

(deftest raw-await-modes-reused-edges-and-arbitrary-exemptions
  (doseq [kind [:comp :task]]
    (let [{:keys [w rid ready-comp pending-task completed-task delivered closed-source signal cell
                  pending-resource ready-resource fresh top deferred] :as f} (fill/comprehensive-fixture kind)
          st (:stamp (row w :runs rid))]
      (doseq [[ds mode] [[[ready-comp] s/am-one]
                         [[ready-comp ready-comp pending-task completed-task delivered closed-source signal cell
                           pending-resource ready-resource fresh top deferred] s/am-all]
                         [[signal delivered ready-comp top pending-task signal] s/am-any]]]
        (let [out (check-await w st ds mode 501 (:next-id w) [pending-task fresh pending-task] [])]
          (is (true? (:accepted out))) (fill/check-old-unexempt f (:world out) [])))))
  (let [{:keys [w rid reused-source second-source reused-edge fresh deferred] :as f} (wiring/reuse-fixture)
        out (check-await w (:stamp (row w :runs rid)) [reused-source second-source reused-source fresh deferred]
                         s/am-all 502 (:next-id w) [fresh reused-source fresh] [reused-edge])]
    (is (true? (:accepted out))) (fill/check-old-unexempt f (:world out) [reused-edge])))

(deftest raw-await-refusals-and-valid-noncurrent-distinction
  (doseq [kind [:comp :task]]
    (let [{:keys [w rid deferred leaf] :as f} (fixture/fixture kind), st (:stamp (row w :runs rid))]
      (doseq [[token ds mode allocation] [[999999 [deferred] s/am-one (:next-id w)]
                                         [st [deferred] s/am-one (inc (:next-id w))]
                                         [st [deferred] 99 (:next-id w)]
                                         [st [deferred leaf] s/am-one (:next-id w)]
                                         [st [] s/am-all (:next-id w)]
                                         [st [999999] s/am-one (:next-id w)]]]
        (is (false? (:accepted (check-await w token ds mode 503 allocation [leaf] [])))))
      (when (= kind :comp)
        (is (true? (engine/await-cycle w (row w :runs rid) [(:owner f) leaf])))
        (is (false? (:accepted (check-await w st [(:owner f) leaf] s/am-all 503 (:next-id w) [leaf] [])))))
      (let [after (fixture/accepted-step w [18 st [deferred] s/am-one 504 (:next-id w) []])]
        (is (nil? (step/tok-run after st)))
        (is (false? (:accepted (check-await after st [deferred] s/am-one 505 (:next-id after) [] [])))))))
  (let [{:keys [w rid signal ready-resource delivered pending-task] :as f} (fill/comprehensive-fixture :comp)
        w (fixture/accepted-step w [3 rid signal 506 (:next-id w)])
        w (fixture/accepted-step w [2 signal 99]), r (row w :runs rid)
        out (check-await w (:stamp r) [ready-resource delivered pending-task] s/am-all 507 (:next-id w) [signal] [])]
    (is (false? (fill/current-run? w rid))) (is (= [r] (step/tok-run w (:stamp r))))
    (is (true? (:accepted out))) (fill/check-old-unexempt f (:world out) [])))

(deftest actual-cleanup-and-consuming-d0-refusals
  (let [{:keys [w rid deferred]} (fixture/fixture :task), st (:stamp (row w :runs rid))
        w1 (fixture/accepted-step w [35 st])
        w2 (fixture/accepted-step w1 [18 st [deferred] s/am-one 508 (:next-id w1) []])
        w3 (fixture/accepted-step w2 [30 rid]), w4 (fixture/accepted-step w3 [29 rid])
        cleanup (row w4 :runs rid)]
    (is (= s/mode-unwinding (:mode cleanup))) (is (= [cleanup] (step/tok-run w4 st)))
    (is (false? (:accepted (check-await w4 st [deferred] s/am-one 509 (:next-id w4) [] [])))))
  (doseq [kind [:comp :task]]
    (let [{:keys [w rid consuming deferred]} (fixture/fixture kind), [w semaphore] (fixture/source w s/sk-semaphore 0)
          r (row w :runs rid), st (:stamp r)]
      (doseq [d [consuming semaphore], mode [s/am-one s/am-all s/am-any]
              :let [ds (if (= mode s/am-one) [d] [d deferred d])]]
        (is (true? (engine/await-ok w r ds mode (:next-id w))))
        (is (true? (engine/await-kind-bad w ds)))
        (is (true? (:accepted (engine/t6-await w st ds mode 510 (:next-id w) [d]))))
        (is (false? (:accepted (check-await w st ds mode 510 (:next-id w) [d] [])))))))
  (let [w (assoc s/empty-world :released true), it [18 999999 [] s/am-any 0 (:next-id w) []]]
    ;; Generic structural non-host control; not labelled an accepted trace.
    (is (false? (engine/host-item it))) (is (false? (engine/host-shut w it)))
    (is (= (engine/raw0 w it) (engine/raw0g w it)))))

(defn cancellation-input []
  (let [{:keys [w rid] :as f} (fixture/fixture :task), st (:stamp (row w :runs rid))
        k1 (:next-id w), w (fixture/accepted-step w [15 st 1 k1 []])
        k2 (:next-id w), w (fixture/accepted-step w [15 st 2 k2 []])
        a (:next-id w), w (fixture/accepted-step w [18 st [k1 k2] s/am-any 511 a [k1 k2]])
        w (fixture/accepted-step w [21 (inc k1)]), item [20 (:stamp (row w :runs (inc k1))) s/res-ok 1]]
    {:w w :f f :rid rid :k1 k1 :k2 k2 :a a :item item}))
(defn loser-jobs [w0 w1]
  (rule/cancel-jobs (vec (mapcat #(engine/loser-runs w1 %)
                               (filter #(engine/any-resolved w1 %) (:acts w0))))))
(defn completion-post-point [{:keys [w item] :as f}]
  (let [o (engine/raw0g w item), w1 (:world o)]
    (is (= 20 (first item)) "nonempty cascade is COMPLETE-triggered, not AWAIT-triggered")
    (is (true? (base/p3la w))) (is (true? (:accepted o)))
    (check-support w1) (is (true? (hm3/h3 [] w1)))
    (assoc f :before-post o :w1 w1)))

(deftest nonempty-completion-triggered-generic-post-cascade-not-await
  (let [{:keys [w w1 before-post rid k2 a f]} (completion-post-point (cancellation-input))
        old (row w :acts a), parent (row w1 :runs rid), loser (row w1 :tasks k2)
        jobs (loser-jobs w w1)]
    (is (= s/am-any (:mode old))) (is (nil? (row w1 :acts a)))
    (is (true? (retain/run-alive parent))) (is (some? (row w1 :tasks (:of parent))))
    (is (= (:scope parent) (:owner loser)))
    (is (true? (retain/run-alive (row w1 :runs (:run loser)))))
    (is (not-any? #(= k2 (:debtor %)) (:edges w1)))
    (is (true? (engine/any-resolved w1 old)))
    (is (true? (engine/loser-task w1 (:scope parent) k2)))
    (is (seq jobs))
    (is (= (engine/cancel-losers w w1) (rule/run-cascade w1 jobs)))
    (doseq [xm [[] [(inc a)] [a (inc a) a]]]
      (let [after (:world (check-post w before-post xm))]
        (is (not= w1 after) "actual cancellation changed this generic post input")
        (is (= [s/res-err rule/cancelled-code] ((juxt :tag :val) (:result (row after :tasks k2)))))
        (is (not-any? #(and (= (:run loser) (:id %)) (retain/run-alive %)) (:runs after)))
        (fill/check-old-unexempt f after xm)))
    (let [refused (step/->Outcome w1 false)]
      (is (not= w w1)) (is (= refused (check-post w refused [])))
      (is (not= w (:world (engine/post w refused))) "arbitrary refused post does not imply original-world identity"))))

(deftest no-loss-controls-retained-all-mode-shared-edge-wrong-owner
  (let [{:keys [w w1 before-post k2 a item] :as f} (completion-post-point (cancellation-input))
        old (row w :acts a), all-old (assoc old :mode s/am-all)
        all-world (update w :acts #(mapv (fn [x] (if (= a (:id x)) all-old x)) %))]
    ;; w0 has no theorem premise; altered old all-mode row is a generic input,
    ;; not a new accepted trace. w1's complete support/H3 are checked by check-post.
    (is (false? (engine/any-resolved w1 all-old)))
    (is (empty? (loser-jobs all-world w1)))
    (is (= before-post (check-post all-world before-post [])))
    (is (false? (engine/any-resolved w old)))
    (is (empty? (loser-jobs w w)))
    (is (= (step/->Outcome w true) (check-post w (step/->Outcome w true) [])))
    (let [edge (:next-id w), shared (fixture/accepted-step w [4 k2 512 edge])
          {:keys [w1 before-post]} (completion-post-point (assoc f :w shared))
          parent (row w1 :runs (:rid f))]
      (is (= k2 (:debtor (row w1 :edges edge))))
      (is (true? (engine/any-resolved w1 (row shared :acts a))))
      (is (false? (engine/loser-task w1 (:scope parent) k2)))
      (is (empty? (loser-jobs shared w1)))
      (is (= before-post (check-post shared before-post []))))
    (let [detached (fixture/accepted-step w [34 k2 s/root-scope-id])
          {:keys [w1 before-post]} (completion-post-point (assoc f :w detached))
          parent (row w1 :runs (:rid f))]
      (is (not= (:scope parent) (:owner (row w1 :tasks k2))))
      (is (true? (retain/run-alive (row w1 :runs (:run (row w1 :tasks k2))))))
      (is (false? (engine/loser-task w1 (:scope parent) k2)))
      (is (empty? (loser-jobs detached w1)))
      (is (= before-post (check-post detached before-post []))))))

(deftest dead-parent-dead-loser-and-non-task-parent-controls
  (let [{:keys [w w1 before-post rid k2 a item] :as f} (completion-post-point (cancellation-input))
        old (row w :acts a), after (:world (check-post w before-post []))
        parent (row after :runs rid)]
    (is (false? (engine/loser-task after (:scope parent) k2)))
    (is (not-any? #(= k2 (:debtor %)) (:edges after)))
    (is (not-any? #(and (= (:run (row after :tasks k2)) (:id %)) (retain/run-alive %)) (:runs after)))
    (let [normal (fixture/accepted-step w item), running (fixture/accepted-step normal [21 rid])
          ended (fixture/accepted-step running [20 (:stamp (row running :runs rid)) s/res-ok 0])]
      (is (nil? (row ended :runs rid)))
      (is (false? (engine/any-resolved ended old))))
    (let [{cw :w cr :rid} (fixture/fixture :comp), generic-old (assoc old :run cr)]
      ;; Generic old row with a valid output world; not an accepted await trace.
      (check-support cw) (is (true? (hm3/h3 [] cw)))
      (is (nil? (row cw :acts (:id generic-old))))
      (is (true? (retain/run-alive (row cw :runs cr))))
      (is (nil? (row cw :tasks (:of (row cw :runs cr)))))
      (is (false? (engine/any-resolved cw generic-old))))))
