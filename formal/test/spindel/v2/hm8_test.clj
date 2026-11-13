(ns spindel.v2.hm8-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [ansatz.surface.elaborate :as elab]
            [spindel.v2.state :as s]
            [spindel.v2.edits :as edits]
            [spindel.v2.step :as step]
            [spindel.v2.engine :as engine]
            [spindel.v2.idle :as idle]
            [spindel.v2.p3 :as p3]
            [spindel.v2.ar :as ar]
            [spindel.v2.i10 :as i10]
            [spindel.v2.hm :as hm]
            [spindel.v2.hmk :as hmk]
            [spindel.v2.hm3 :as hm3]
            [spindel.v2.hm6 :as hm6]
            [spindel.v2.hm6-base :as base]
            [spindel.v2.hm7 :as hm7]
            [spindel.v2.hm8]
            [spindel.v2.hm6-test :as certification]
            [spindel.v2.hm7-test :as fields])
  (:import [ansatz.kernel ConstantInfo]))

(def contracts
  '{h3-demand-reactive
    (forall [xm :- (List Nat), w :- World, d :- Nat]
      (=> (= (g7 w) true) (= (aha w) true) (= (h3 xm w) true)
          (= (h3 xm (demand-reactive w d)) true)))
    h3-demand-fold
    (forall [xm :- (List Nat), ds :- (List Nat), w :- World]
      (=> (= (g7 w) true) (= (aha w) true) (= (h3 xm w) true)
          (= (h3 xm (nat-fold demand-reactive w ds)) true)))
    h3-await-pre
    (forall [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (= (g10r w) true) (= (gd w) true) (= (g7 w) true) (= (aha w) true) (= (h3 xm w) true)
          (List.Mem r (:runs w)) (= (run-alive r) true) (= (h3 xm (await-pre w r ds mode k mine)) true)))
    h3-await-pre-p3la
    (forall [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (= (p3la w) true) (= (h3 xm w) true) (List.Mem r (:runs w)) (= (run-alive r) true)
          (= (h3 xm (await-pre w r ds mode k mine)) true)))
    h3-await-pre-token
    (forall [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat]
      (=> (= (p3la w) true) (= (h3 xm w) true) (= (tok-run w st) (Option.some RunRow r))
          (= (await-ok w r ds mode fresh) true) (= (h3 xm (await-pre w r ds mode k mine)) true)))
    g7-await-pre-p3la
    (forall [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (= (p3la w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (g7 (await-pre w r ds mode k mine)) true)))
    aha-await-pre-p3la
    (forall [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (= (p3la w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (aha (await-pre w r ds mode k mine)) true)))
    gd-await-pre-p3la
    (forall [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (= (p3la w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (gd (await-pre w r ds mode k mine)) true)))
    ar-await-pre-p3la
    (forall [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (= (p3la w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (ar (await-pre w r ds mode k mine)) true)))
    hmk-await-pre-p3la
    (forall [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (= (p3la w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (hmk (List.nil Nat) (await-pre w r ds mode k mine)) true)))
    ekb-await-pre-p3la
    (forall [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (= (p3la w) true) (List.Mem r (:runs w)) (= (run-alive r) true) (= (ekb (await-pre w r ds mode k mine)) true)))})

(def generated-contracts
  '{g7-demand-reactive (forall [w :- World, d :- Nat] (=> (= (g7 w) true) (= (g7 (demand-reactive w d)) true)))
    aha-demand-reactive (forall [w :- World, d :- Nat] (=> (= (aha w) true) (= (aha (demand-reactive w d)) true)))
    g7-await-pre
    (forall [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (= (g7 w) true) (= (g7 (await-pre w r ds mode k mine)) true)))
    aha-await-pre
    (forall [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (aha w) true) (= (aha (await-pre w r ds mode k mine)) true)))
    gd-await-pre
    (forall [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (= (g7 w) true) (= (gd w) true) (= (gd (await-pre w r ds mode k mine)) true)))
    ar-await-pre
    (forall [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (= (ar w) true) (= (ar (await-pre w r ds mode k mine)) true)))
    hmk-await-pre
    (forall [hxm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (= (hmk hxm w) true) (= (hmk hxm (await-pre w r ds mode k mine)) true)))
    ekb-await-pre
    (forall [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
      (=> (= (ekb w) true) (= (ekb (await-pre w r ds mode k mine)) true)))})

(def extraction-contracts
  '{p3la-g10r (forall [w :- World] (=> (= (p3la w) true) (= (g10r w) true)))
    p3la-gd (forall [w :- World] (=> (= (p3la w) true) (= (gd w) true)))
    p3la-hmk (forall [w :- World] (=> (= (p3la w) true) (= (hmk (List.nil Nat) w) true)))})

(def theorems (concat (keys contracts) (keys generated-contracts)
                     '[h3-await-empty-act h3-await-allocate p3la-g10r p3la-gd p3la-hmk]))

(deftest exact-safe-closed-kernel-contracts
  (is (= 11 (count contracts)))
  (is (= 8 (count generated-contracts)))
  (doseq [name theorems]
    (when-let [^ConstantInfo declaration (certification/checked-declaration name)]
      (is (seq (fields/type-form (.-type declaration))) (str name " closed type"))
      (when-let [contract (get (merge contracts generated-contracts extraction-contracts) name)]
        (is (= (fields/type-form (elab/elaborate @a/ansatz-env contract))
               (fields/type-form (.-type declaration))) (str name " exact actual contract"))))))

(defn row [w table id] (fields/row w table id))

(defn accepted-step
  "Deterministic accepted world-step trace; every resulting p3la premise is checked."
  [w item]
  (let [out (engine/world-step w item)]
    (is (true? (:accepted out)) (str "accepted trace item " item))
    (is (true? (base/p3la (:world out))) (str "reachable p3la after " item))
    (:world out)))

(defn source [w kind value]
  (let [id (:next-id w)] [(accepted-step w [1 2 kind value id]) id]))

(defn computation [w]
  (let [c (:next-id w), w (accepted-step w [14 2 c [1] 1])
        observer (:next-id w), w (accepted-step w [4 c 1 observer])
        rid (:next-id w), w (accepted-step w [17 c rid])
        w (accepted-step w [21 rid])]
    {:w w :c c :rid rid :observer observer}))

(defn fixture
  "Reachable input with an unrelated parked current activation, a two-idle
   result-bearing validity chain, a fresh idle comp, and a selected live run."
  [kind]
  (let [[w leaf] (source s/empty-world s/sk-signal 30)
        [w deferred] (source w s/sk-deferred 0)
        [w consuming] (source w s/sk-mailbox 0)
        bottom (computation w), w (accepted-step (:w bottom) [3 (:rid bottom) leaf 1 (:next-id (:w bottom))])
        w (accepted-step w [20 (:rid bottom) s/res-ok 60])
        top (computation w), w (accepted-step (:w top) [18 (:rid top) [(:c bottom)] s/am-one 2 (:next-id (:w top)) []])
        w (accepted-step w [20 (:rid top) s/res-ok 50])
        w (accepted-step w [5 (:observer top)])
        w (accepted-step w [5 (:observer bottom)])
        parked (computation w), act (:next-id (:w parked))
        w (accepted-step (:w parked) [18 (:rid parked) [deferred] s/am-one 77 act []])
        fresh (:next-id w), w (accepted-step w [14 2 fresh [2] 3])
        selected (if (= kind :comp)
                   (computation w)
                   (let [c (:next-id w), w (accepted-step w [16 2 7 c []]), rid (inc c)]
                     {:w (accepted-step w [21 rid]) :c c :rid rid}))]
    {:w (:w selected) :rid (:rid selected) :owner (:c selected) :kind kind
     :leaf leaf :deferred deferred :consuming consuming :bottom (:c bottom) :top (:c top)
     :old-owner (:c parked) :old-run (:rid parked) :old-act act :old-edge (inc act) :fresh fresh}))

(defn check-h3-fields [w]
  (is (true? (edits/inv-sample w)))
  (is (true? (fields/awake-fields? w)))
  (is (= (fields/awake-fields? w) (idle/g7-rest w)))
  (is (true? (fields/activation-runs? w)))
  (is (= (boolean (fields/activation-runs? w)) (p3/aha-rest w)))
  (is (true? (fields/member-fields? [] w)))
  (is (= (boolean (fields/member-fields? [] w)) (hm3/h3-rest [] w)))
  (is (true? (hm3/h3 [] w)))
  (is (true? (idle/g7 w)))
  (is (true? (p3/aha w))))

(defn check-supports [w]
  (doseq [[label predicate] [[:g7 idle/g7] [:aha p3/aha] [:gd hm/gd]
                            [:ar ar/ar] [:hmk #(hmk/hmk [] %)] [:ekb hm6/ekb]]]
    (is (true? (predicate w)) (str label " exported preparation support"))))

(defn check-input [fixture]
  (let [{:keys [w rid owner kind]} fixture, r (row w :runs rid)
        entity (row w (if (= kind :comp) :comps :tasks) owner)]
    (is (true? (base/p3la w)))
    (is (some #{r} (:runs w)))
    (is (fields/alive? r))
    (is (true? (engine/run-normal r)))
    (is (= rid (:run entity)))
    (when (= kind :comp)
      (is (= (:epoch r) (:epoch entity)))
      (is (< (:done-epoch entity) (:epoch entity))))
    (is (true? (i10/g10r w)))
    (is (true? (hm/gd w)))
    (check-h3-fields w)))

(defn check-old-obligation [fixture after]
  (let [{:keys [w old-act old-edge old-run old-owner deferred]} fixture
        act (row after :acts old-act), edge (row after :edges old-edge), comp (row after :comps old-owner)]
    (is (= (row w :acts old-act) act))
    (is (= (row w :edges old-edge) edge))
    (is (= (row w :runs old-run) (row after :runs old-run)))
    (is (= 1 (:remaining act)))
    (is (= s/res-none (:tag (first (:slots act)))))
    (is (= [(s/->Member old-edge 0)] (:members act)))
    (is (= [s/ph-armed old-owner deferred] ((juxt :phase :creditor :debtor) edge)))
    (is (= old-act (:id (first (filter #(some (fn [m] (= old-edge (:edge m))) (:members %)) (:acts after))))))
    (is (< (:done-epoch comp) (:epoch comp)))
    (is (= [s/sk-deferred true 0] ((juxt :kind :open :version) (row after :sources deferred))))
    (is (true? (fields/member-fields? [] after)))))

(defn stages [fixture ds mode k mine]
  (let [{:keys [w rid]} fixture, r (row w :runs rid)
        ticked (s/run-upd w rid step/run-tick)
        activation (s/->ActRow (:next-id w) rid mode nil (vec (repeat (count ds) (s/->RunResult s/res-none 0))) (count ds) k mine)
        inserted (s/act-ins ticked activation), bumped (s/bump inserted)]
    {:r r :activation activation :ticked ticked :inserted inserted :bumped bumped
     :after (engine/await-pre w r ds mode k mine)}))

(deftest reachable-comp-and-task-preparation-with-live-old-obligations
  (doseq [kind [:comp :task]]
    (let [{:keys [w rid top bottom fresh old-owner leaf] :as fixture} (fixture kind)
          ds [top top fresh old-owner leaf], mine [fresh top], k 901
          {:keys [r activation ticked inserted bumped after]} (stages fixture ds s/am-all k mine)
          aid (:next-id w), old-validity (into {} (map (fn [id] [id (:validity (row w :comps id))]) [top bottom]))]
      (check-input fixture)
      (is (= 2 (count (filter :idle (map #(row w :comps %) [top bottom])))))
      (is (every? seq (vals old-validity)))
      (is (true? (engine/valid-idle w (row w :comps top))))
      (is (true? (step/run-tok-ok w (:stamp r))))
      (is (true? (engine/await-ok w r ds s/am-all aid)))
      (is (= (inc (:effect-index r)) (:effect-index (row after :runs rid))))
      (is (= (dissoc r :effect-index) (dissoc (row after :runs rid) :effect-index)))
      (is (= activation (first (:acts after))))
      (is (empty? (:members (first (:acts after)))))
      (is (= [aid rid s/am-all nil (count ds) k mine]
             ((juxt :id :run :mode :members :remaining :cont :spawned) (first (:acts after)))))
      (is (= (count ds) (count (:slots (first (:acts after))))))
      (is (every? #(= s/res-none (:tag %)) (:slots (first (:acts after)))))
      (is (= (inc aid) (:next-id bumped)) "activation allocation is separate from reactive edges")
      (is (= (+ aid 3) (:next-id after)) "one activation plus two reconstructed dependency edges")
      (is (false? (edits/inv-sample inserted)) "pre-bump insertion does not have full inv-sample")
      (is (true? (hm3/h3-rest [] inserted)))
      (doseq [boundary [ticked bumped after]]
        (check-h3-fields boundary) (check-supports boundary) (check-old-obligation fixture boundary))
      (let [prefix (engine/react-loop [0] bumped [top])
            chain (engine/react-loop [0 0 0 0] bumped [top])]
        (is (false? (:idle (row prefix :comps top))))
        (is (true? (:idle (row prefix :comps bottom))))
        (is (false? (:idle (row chain :comps bottom))))
        (doseq [boundary [prefix chain]]
          (check-h3-fields boundary) (check-supports boundary) (check-old-obligation fixture boundary)))
      (loop [boundary bumped, debtors (distinct ds)]
        (when-let [d (first debtors)]
          (let [next-world (engine/demand-reactive boundary d)]
            (check-h3-fields next-world) (check-supports next-world)
            (check-old-obligation fixture next-world)
            (recur next-world (rest debtors)))))
      (check-supports after)
      (doseq [id [top bottom]]
        (let [before (row w :comps id), now (row after :comps id)]
          (is (:idle before)) (is (false? (:idle now))) (is (empty? (:validity now)))
          (is (= (:result before) (:result now)))
          (doseq [validity (get old-validity id)]
            (let [edge (first (filter #(and (= id (:creditor %)) (= (:debtor validity) (:debtor %))) (:edges after)))]
              (is (some? edge))
              (is (= [s/ek-dep s/ph-armed true (:version validity) true (:version validity)]
                     ((juxt :kind :phase :has-seen :seen :has-base :base-version) edge)))))))
      (is (= 1 (:epoch (row after :comps fresh))))
      (is (zero? (:done-epoch (row after :comps fresh))))
      (is (false? (:idle (row after :comps fresh))))
      (is (= 0 (:pending (row after :comps top))))
      (is (= 0 (:pending (row after :comps bottom)))))))

(deftest demand-branches-and-unrestricted-local-arguments
  (let [{:keys [w top fresh old-owner leaf rid] :as fixture} (fixture :comp)
        changed (accepted-step w [2 leaf 31]), invalid (row changed :comps top)
        demanded (engine/demand-reactive changed top)]
    (check-input fixture)
    (is (true? (base/p3la changed)))
    (check-h3-fields changed)
    (is (:idle invalid))
    (is (not= s/res-none (:tag (:result invalid))))
    (is (false? (engine/valid-idle changed invalid)))
    (is (= (inc (:epoch invalid)) (:epoch (row demanded :comps top))))
    (is (= (:done-epoch invalid) (:done-epoch (row demanded :comps top))))
    (is (false? (:idle (row demanded :comps top))))
    (is (= (:edges changed) (:edges demanded)))
    (check-h3-fields demanded)
    (doseq [d [old-owner leaf 999999]]
      (is (= w (engine/demand-reactive w d))))
    (let [fresh-result (engine/demand-reactive w fresh)]
      (is (= (:epoch (row w :comps fresh)) (:epoch (row fresh-result :comps fresh))))
      (is (zero? (:done-epoch (row fresh-result :comps fresh))))
      (is (false? (:idle (row fresh-result :comps fresh))))
      (check-h3-fields fresh-result))
    (let [folded (edits/nat-fold engine/demand-reactive w [top top fresh old-owner leaf 999999])]
      (check-h3-fields folded)
      (check-old-obligation fixture folded))
    (doseq [[ds mode mine] [[[] 99 [top fresh]] [[top top] 99 [fresh top fresh]]]]
      (let [result (engine/await-pre w (row w :runs rid) ds mode 321 mine)]
        (check-h3-fields result) (check-supports result)
        (is (= mine (:spawned (first (:acts result)))))
        (is (= (count ds) (:remaining (first (:acts result)))))))))

(defn refused-raw [w item]
  (let [out (engine/raw0 w item)]
    (is (false? (:accepted out)) (str "raw0 refuses " item))
    (is (= w (:world out)) (str "raw0 refusal is identity " item))))

(deftest actual-guarded-await-acceptance-and-refusals
  (let [{:keys [w rid deferred consuming] :as fixture} (fixture :task)
        r (row w :runs rid), st (:stamp r), fresh (:next-id w)
        item [18 st [deferred] s/am-one 7 fresh []]
        accepted (engine/raw0 w item)]
    (check-input fixture)
    (is (true? (engine/await-ok w r [deferred] s/am-one fresh)))
    (is (true? (:accepted accepted)) "finite accepted T6 positive control, distinct from await-pre proof")
    (is (= s/act-parked (:act (row (:world accepted) :runs rid))))
    (is (seq (:members (row (:world accepted) :acts fresh))))
    (is (false? (step/run-tok-ok w 999999)))
    (is (false? (step/run-tok-ok (:world accepted) st)))
    (refused-raw w [18 999999 [deferred] s/am-one 7 fresh []])
    (refused-raw (:world accepted) [18 st [deferred] s/am-one 7 (:next-id (:world accepted)) []])
    (refused-raw w [18 st [deferred] 99 7 fresh []])
    (refused-raw w [18 st [] s/am-one 7 fresh []])
    (is (true? (engine/await-ok w r [consuming] s/am-one fresh)) "local await-ok omits outer D0 source-kind guard")
    (is (true? (engine/await-kind-bad w [consuming])))
    (refused-raw w [18 st [consuming] s/am-one 7 fresh []])
    (testing "a real cancellation cleanup slice is non-normal and cannot await"
      (let [w1 (accepted-step w [35 st])
            w2 (accepted-step w1 [18 st [deferred] s/am-one 8 (:next-id w1) []])
            w3 (accepted-step w2 [30 rid])
            w4 (accepted-step w3 [29 rid]), cleanup (row w4 :runs rid)]
        (is (= s/mode-unwinding (:mode cleanup)))
        (is (:slice cleanup))
        (is (true? (engine/in-cleanup w4 st)))
        (is (false? (engine/run-normal cleanup)))
        (refused-raw w4 [18 st [deferred] s/am-one 7 (:next-id w4) []])))))
