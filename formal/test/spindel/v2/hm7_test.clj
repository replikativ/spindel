(ns spindel.v2.hm7-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [ansatz.surface.elaborate :as elab]
            [spindel.v2.state :as s]
            [spindel.v2.edits :as edits]
            [spindel.v2.step :as step]
            [spindel.v2.engine :as engine]
            [spindel.v2.idle :as idle]
            [spindel.v2.p3 :as p3]
            [spindel.v2.hm3 :as hm3]
            [spindel.v2.hm7]
            [spindel.v2.hm6-test :as certification])
  (:import [ansatz.kernel Expr ConstantInfo]))

(def contracts
  '{h3-comp-react
    (forall [xm :- (List Nat), w :- World, c :- CompRow]
      (=> (List.Mem c (:comps w)) (= (:idle c) true) (= (g7 w) true) (= (aha w) true)
          (= (h3 xm w) true) (= (h3 xm (comp-upd w (:id c) comp-react-row)) true)))
    h3-react-add
    (forall [xm :- (List Nat), w :- World, c :- Nat, v :- Valid]
      (=> (= (h3 xm w) true) (= (h3 xm (react-add w c v)) true)))
    h3-react-edges
    (forall [xm :- (List Nat), vs :- (List Valid), w :- World, c :- Nat]
      (=> (= (h3 xm w) true) (= (h3 xm (react-edges w c vs)) true)))
    h3-react-one
    (forall [xm :- (List Nat), w :- World, c :- CompRow]
      (=> (List.Mem c (:comps w)) (= (:idle c) true) (= (g7 w) true) (= (aha w) true)
          (= (h3 xm w) true) (= (h3 xm (react-one w c)) true)))
    h3-react-loop
    (forall [xm :- (List Nat), fuel :- (List Nat), w :- World, q :- (List Nat)]
      (=> (= (g7 w) true) (= (aha w) true) (= (h3 xm w) true) (= (h3 xm (react-loop fuel w q)) true)))
    h3-react-loop-p3la
    (forall [xm :- (List Nat), fuel :- (List Nat), w :- World, q :- (List Nat)]
      (=> (= (p3la w) true) (= (h3 xm w) true) (= (h3 xm (react-loop fuel w q)) true)))
    p3la-aha
    (forall [w :- World] (=> (= (p3la w) true) (= (aha w) true)))
    hm3-insert-edge-checked
    (forall [xm :- (List Nat), w :- World, e :- EdgeRow]
      (=> (= (h3 xm w) true) (= (h3 xm (insert-edge-checked w e)) true)))
    hm3-raise-for
    (forall [xm :- (List Nat), w :- World, c :- Nat, d :- Nat]
      (=> (= (h3 xm w) true) (= (h3 xm (raise-for w c d)) true)))
    aha-react-one
    (forall [w :- World, c :- CompRow]
      (=> (= (aha w) true) (= (aha (react-one w c)) true)))
    g7-react-one
    (forall [w :- World, c :- CompRow]
      (=> (= (g7 w) true) (= (g7 (react-one w c)) true)))})

(def theorems
  (concat (keys contracts) '[h3-react-act-off h3-react-wif h3-react-cs-off h3-react-r]))

(defn type-form
  "Closed structural kernel type; binder names are discarded for alpha equality.
   Open variables, metavariables and unsupported expression forms are fatal."
  ([expression] (type-form expression 0))
  ([^Expr expression depth]
   (let [tag (.-tag expression), x (.-o0 expression), y (.-o1 expression)
         z (.-o2 expression), extra (.-o3 expression)]
     (case (int tag)
       0 (let [index (.-longVal expression)]
           (assert (< -1 index depth) (str "open bound variable " index)) [:bvar index])
       1 [:sort (str x)]
       2 [:const (str x) (mapv str y)]
       3 [:app (type-form x depth) (type-form y depth)]
       4 [:lambda (type-form y depth) (type-form z (inc depth)) (str extra)]
       5 [:forall (type-form y depth) (type-form z (inc depth)) (str extra)]
       6 [:let (type-form y depth) (type-form z depth) (type-form extra (inc depth))]
       7 [:nat (str x)]
       8 [:string x]
       9 (type-form y depth)
       10 [:projection (str x) (.-longVal expression) (type-form y depth)]
       (throw (ex-info "Open or unsupported theorem type" {:tag tag}))))))

(deftest exact-closed-kernel-contracts
  (is (= 11 (count contracts)))
  (doseq [name theorems]
    (when-let [^ConstantInfo declaration (certification/checked-declaration name)]
      (is (seq (type-form (.-type declaration))) (str name " has a closed structural type"))
      (when-let [contract (get contracts name)]
        (is (= (type-form (elab/elaborate @a/ansatz-env contract))
               (type-form (.-type declaration)))
            (str name " has exactly the independently specified kernel contract"))))))

(defn row [w table id] (first (filter #(= id (:id %)) (get w table))))
(defn alive? [run] (not= s/act-done (:act run)))
(defn waiting? [comp]
  (and (not (:idle comp)) (or (< (:done-epoch comp) (:epoch comp)) (pos? (:pending comp)))))

(defn member-fields?
  "Host-side H3-rest checker, independently reads the field-level obligations."
  [exempt w]
  (let [exempt (set exempt)]
    (every?
     (fn [act]
       (and (< (:run act) (:next-id w))
            (every?
             (fn [run]
               (let [comps (filter #(= (:of run) (:id %)) (:comps w))]
                 (and (< (:of run) (:next-id w))
                      (every? #(<= (:epoch run) (:epoch %)) comps)
                      (or (exempt (:of run))
                          (not-any? #(<= (:epoch %) (:epoch run)) comps)
                          (and
                           (every? #(< (:done-epoch %) (:epoch %)) comps)
                           (every?
                            (fn [member]
                              (let [id (:edge member), edges (filter #(= id (:id %)) (:edges w))]
                                (or (exempt id)
                                    (and
                                     (seq edges)
                                     (every?
                                      (fn [edge]
                                        (and (= s/ph-armed (:phase edge))
                                             (= (:creditor edge) (if (= s/ek-dep (:kind edge)) (:of run) (:id act)))
                                             (= (:id act) (:id (first (filter #(some (fn [m] (= id (:edge m))) (:members %)) (:acts w)))))
                                             (or (exempt (:debtor edge))
                                                 (and
                                                  (every? (fn [task]
                                                            (some #(and (= (:run task) (:id %)) (alive? %)) (:runs w)))
                                                          (filter #(= (:debtor edge) (:id %)) (:tasks w)))
                                                  (let [debtors (filter #(= (:debtor edge) (:id %)) (:comps w))]
                                                    (or (empty? debtors)
                                                        (and (= s/ek-dep (:kind edge)) (every? waiting? debtors))))))))
                                      edges)))))
                            (:members act)))))))
             (filter #(= (:run act) (:id %)) (:runs w)))))
     (:acts w))))

(defn awake-fields? [w]
  (and
   (every? (fn [run] (or (not (alive? run))
                         (not-any? #(and (= (:of run) (:id %)) (:idle %)) (:comps w)))) (:runs w))
   (every? (fn [edge] (or (and (not= s/ek-dep (:kind edge)) (not (:marked edge)))
                          (not-any? #(and (= (:creditor edge) (:id %)) (:idle %)) (:comps w)))) (:edges w))
   (every? #(or (not (:idle %)) (and (zero? (:run %)) (empty? (:adopt-basis %)) (empty? (:adopt-baselines %)))) (:comps w))
   (every? #(or (not (and (:slice %) (= s/mode-normal (:mode %)))) (alive? %)) (:runs w))
   (every? #(or (not= s/ek-observe (:kind %)) (zero? (:creditor %))) (:edges w))))

(defn activation-runs? [w]
  (every? (fn [act] (let [runs (filter #(= (:run act) (:id %)) (:runs w))]
                    (and (seq runs) (every? alive? runs)))) (:acts w)))

;; Constructed conditional predicate instance, not a claimed reachable trace.
(defn reactivation-world []
  (let [none (s/->RunResult s/res-none 0)
        comp (fn [id epoch done rank version idle validity]
               (s/->CompRow id 2 [] 1 0 epoch done 0 rank version (s/->RunResult s/res-ok (+ 40 id)) idle validity [] [] [] 1))]
    (assoc s/empty-world
           :next-id 11
           :sources [(s/->SourceRow 3 2 s/sk-signal 30 8 true 1 [])
                     (s/->SourceRow 10 2 s/sk-deferred 0 0 true 1 [])]
           :comps [(assoc (comp 4 2 1 3 2 false []) :run 7 :result none)
                   (comp 5 1 1 2 10 true [(s/->Valid 6 11 0 1)])
                   (comp 6 1 1 1 11 true [(s/->Valid 3 8 0 0)])]
           :runs [(s/->RunRow 7 4 7 2 2 s/act-parked s/mode-normal false 1 [] [])]
           :acts [(s/->ActRow 8 7 s/am-one [(s/->Member 9 0)] [none] 1 77 [])]
           :edges [(s/->EdgeRow 9 s/ek-dep 4 10 77 0 s/ph-armed false false 0 false 0 0)])))

(defn check-world [w]
  (is (true? (edits/inv-sample w)))
  (is (true? (awake-fields? w)))
  (is (= (awake-fields? w) (idle/g7-rest w)))
  (is (true? (activation-runs? w)))
  (is (= (activation-runs? w) (p3/aha-rest w)))
  (is (true? (member-fields? [] w)))
  (is (= (boolean (member-fields? [] w)) (hm3/h3-rest [] w)))
  (is (true? (idle/g7 w)))
  (is (true? (p3/aha w)))
  (is (true? (hm3/h3 [] w))))

(defn check-held-member [before after]
  (is (= (:acts before) (:acts after)))
  (is (= (:runs before) (:runs after)))
  (is (= (row before :edges 9) (row after :edges 9)))
  (is (= [s/act-parked false] ((juxt :act :slice) (row after :runs 7))))
  (is (= [(s/->Member 9 0)] (:members (row after :acts 8))))
  (is (= s/res-none (:tag (first (:slots (row after :acts 8))))))
  (is (= [s/ph-armed 4 10] ((juxt :phase :creditor :debtor) (row after :edges 9))))
  (is (= 8 (:id (first (filter #(some (fn [m] (= 9 (:edge m))) (:members %)) (:acts after))))))
  (is (< (:done-epoch (row after :comps 4)) (:epoch (row after :comps 4))))
  (is (member-fields? [] after)))

(deftest nonempty-obligations-survive-two-real-reactivations
  (let [w (reactivation-world), prefix (engine/react-loop [0] w [5])
        full (engine/react-loop [0 0 0 0] w [5])]
    (is (= [8] (mapv :id (:acts w))))
    (is (= [s/sk-deferred true 0] ((juxt :kind :open :version) (row w :sources 10))))
    (is (= 1 (:remaining (row w :acts 8))))
    (is (not= s/res-none (:tag (:result (row w :comps 5)))))
    (is (not= s/res-none (:tag (:result (row w :comps 6)))))
    (is (= [true true] (mapv :idle (filter #(#{5 6} (:id %)) (:comps w)))))
    (doseq [world [w prefix full]] (check-world world) (check-held-member w world))
    (is (= [false true] (mapv #(:idle (row prefix :comps %)) [5 6])))
    (is (= [false false] (mapv #(:idle (row full :comps %)) [5 6])))
    (is (empty? (:validity (row prefix :comps 5))))
    (is (seq (:validity (row prefix :comps 6))))
    (doseq [id [5 6]]
      (let [c (row full :comps id)]
        (is (empty? (:validity c)))
        (is (= (:done-epoch c) (:epoch c)))
        (is (= (:result (row w :comps id)) (:result c)))
        (is (= (:run (row w :comps id)) (:run c)))))
    (is (= [6 11 true 11] ((juxt :debtor :seen :has-base :base-version) (row prefix :edges 11))))
    (is (= [3 8 true 8] ((juxt :debtor :seen :has-base :base-version) (row full :edges 12))))
    (is (= 13 (:next-id full)))
    (is (= full (engine/react-loop [0 0 0 0 0 0] w [5 5 9999 4 6])))))

(deftest bounded-and-refusal-branches
  (let [w (reactivation-world)]
    (is (= w (engine/react-loop [] w [5])))
    (is (= w (engine/react-loop [0] w [])))
    (is (= w (engine/react-loop [0 0] w [9999 4])))
    (is (= w (engine/react-edges w 5 [])))
    (let [c (row w :comps 5), row-world (s/comp-upd w 5 engine/comp-react-row)]
      (check-world row-world)
      (check-held-member w row-world)
      (is (= (engine/react-one w c) (engine/react-loop [0] w [5]))))
    (testing "checked insertion also transports an actual rank increase"
      (let [awake (s/comp-upd w 5 #(assoc % :idle false :validity [] :rank 0))
            validity (first (:validity (row w :comps 5)))
            after (engine/react-add awake 5 validity)]
        (check-world awake)
        (is (true? (engine/react-ok awake 5 validity)))
        (is (= 2 (:rank (row after :comps 5))))
        (is (= [s/ek-dep 5 6 s/ph-armed 11 11]
               ((juxt :kind :creditor :debtor :phase :seen :base-version) (row after :edges 11))))
        (check-world after)
        (check-held-member awake after)))
    (testing "a final debtor skips insertion and allocation"
      (let [final (update w :sources #(mapv (fn [src] (assoc src :kind s/sk-deferred :open false)) %))
            validity (s/->Valid 3 8 0 0)]
        (is (true? (step/deb-final final 3)))
        (is (false? (engine/react-ok final 5 validity)))
        (is (= final (engine/react-add final 5 validity)))))
    (testing "the checked cycle/raise refusal keeps its original world"
      (let [self (s/->Valid 5 10 0 2)]
        (is (false? (engine/react-ok w 5 self)))
        (is (= w (engine/react-add w 5 self)))))
    (testing "wrong saved version takes the failed-validation demand route"
      (let [bad (s/comp-upd w 5 #(assoc % :validity [(s/->Valid 6 999 0 1)]))
            c (row bad :comps 5), result (engine/demand-reactive bad 5)]
        (is (false? (engine/valid-idle bad c)))
        (is (false? (:idle (row result :comps 5))))
        (is (true? (:idle (row result :comps 6))))
        (is (= (:edges bad) (:edges result)))
        (is (= 2 (:epoch (row result :comps 5))))))))

(deftest independently-reject-malformed-preconditions
  (let [w (reactivation-world)]
    (testing "an idle owner of an alive activation run violates G7"
      (let [bad (s/comp-upd w 4 #(assoc % :idle true :run 0))]
        (is (false? (awake-fields? bad)))
        (is (false? (idle/g7 bad)))
        (is (activation-runs? bad))
        (is (true? (p3/aha bad)))))
    (testing "a dead matching run violates AHA"
      (let [bad (update w :runs #(mapv (fn [r] (assoc r :act s/act-done)) %))]
        (is (not (activation-runs? bad)))
        (is (false? (p3/aha bad)))))
    (testing "held-member phase, creditor, debtor and first holder are actual obligations"
      (doseq [bad [(update w :edges #(mapv (fn [e] (assoc e :phase s/ph-fired)) %))
                   (update w :edges #(mapv (fn [e] (assoc e :creditor 6)) %))
                   (update w :edges #(mapv (fn [e] (assoc e :debtor 6)) %))
                   (assoc w :next-id 12 :acts [(assoc (row w :acts 8) :id 11) (row w :acts 8)])]]
        (is (not (member-fields? [] bad)))
        (is (false? (hm3/h3-rest [] bad)))))))
