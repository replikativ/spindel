(ns spindel.v2.hm10-test
  "Independently confirmed HM10 literal manifest, committed before proofs.
   Plan SHA256 da2ae9e0c18525021e65bb9d2cbf4170f6b9d7108d7280d8cdaa867848cb143d."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [ansatz.core :as a]
            [ansatz.surface.elaborate :as elab]
            [ansatz.kernel.env :as kernel-env]
            [ansatz.kernel.tc :as tc]
            [spindel.v2.hm10 :as h10]
            [spindel.v2.hm9-test :as wiring]
            [spindel.v2.hm8-test :as fixture]
            [spindel.v2.state :as s]
            [spindel.v2.edits :as edits]
            [spindel.v2.step :as step]
            [spindel.v2.engine :as engine]
            [spindel.v2.idle :as idle]
            [spindel.v2.hm :as hm]
            [spindel.v2.hm3 :as hm3]
            [spindel.v2.hm6-base :as base]
            [spindel.v2.lit :as lit]
            [spindel.v2.hm6-test :as certification]
            [spindel.v2.hm7-test :as closed])
  (:import [ansatz.kernel ConstantInfo Env Name]
           [java.io PushbackReader]))

(def helper-definitions
  '[
(a/defn h10-install [a :- Nat, ds :- (List Nat), acc :- AwAcc] World
  (act-upd (:world acc) a
    (act-set-members (mk-members (:pairs acc) 0 ds))))

(a/defn h10-fill-prefix [a :- Nat, ds :- (List Nat), acc :- AwAcc,
                       pre :- (List Nat)] World
  (nat-fold (fast-fill (:pairs acc)) (h10-install a ds acc) pre))

(a/defn h10-pending-exempt [ps :- (List DE), tail :- (List Nat),
                          xm :- (List Nat)] (List Nat)
  (match tail
    [nil xm]
    [(cons d t) (List.cons Nat (pair-edge d ps)
                         (h10-pending-exempt ps t xm))]))
])

(def public-contracts
  '[
{:name h10-fast-not-ready-waiting
 :type (forall [w :- World, d :- Nat]
  (=> (= (gd w) true)
      (= (awake (:comps w) d) true)
      (= (fast-ready w d) false)
      (= (tbl-all (hk-wif d) (:comps w)) true)))}

{:name h10-await-debtor-awake
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat, d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (nat-mem d ds) true)
      (= (awake (:comps (:world (await-acc w r ds mode k mine))) d) true)))}

{:name h10-install-h3-exempt
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh)
      (let [C (await-acc w r ds mode k mine)]
        (= (h3 (h10-pending-exempt (:pairs C) (nat-distinct ds) xm)
               (h10-install (:next-id w) ds C)) true))))}

{:name h10-fill-prefix-h3
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat)]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (List.append Nat pre tail) (nat-distinct ds))
      (let [C (await-acc w r ds mode k mine)]
        (= (h3 (h10-pending-exempt (:pairs C) tail xm)
               (h10-fill-prefix (:next-id w) ds C pre)) true))))}

{:name h10-fast-fill-h3
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (h3 xm (h10-fill-prefix (:next-id w) ds
                  (await-acc w r ds mode k mine) (nat-distinct ds))) true)))}

{:name h10-park-h3
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (h3 xm
           (park-if
             (h10-fill-prefix (:next-id w) ds
               (await-acc w r ds mode k mine) (nat-distinct ds))
             (:next-id w) (:id r))) true)))}
])

(deftest frozen-hm10-manifest
  (is (= 3 (count helper-definitions)))
  (is (= 6 (count public-contracts)))
  (is (= 6 (count (set (map :name public-contracts))))))

(defn source-forms []
  (with-open [reader (PushbackReader. (io/reader (io/resource "spindel/v2/hm10.clj")))]
    (loop [forms []]
      (if-let [form (read {:eof nil} reader)] (recur (conj forms form)) forms))))

(def theorems
  (mapv second (filter #(and (seq? %) (= 'a/theorem (first %))) (source-forms))))

(defn declaration [name]
  (.lookup ^Env @a/ansatz-env (Name/fromString (str name))))

(defn expanded-independent-contract [contract]
  ;; Nonrecursive aliases are independently bound to the frozen meanings.
  ;; Kernel beta/delta/zeta equality performs expansion; recursive h10-pending-exempt
  ;; is retained and its exact source recursion is separately pinned below.
  (let [bindings (mapcat (fn [[_ name parameters _ body]]
                          (when-not (= name 'h10-pending-exempt)
                            [name (list 'fn parameters body)])) helper-definitions)]
    (list 'let (vec bindings) contract)))

(deftest actual-safe-closed-endpoint-contracts
  (is (= (set (map :name public-contracts))
         (set (filter (set (map :name public-contracts)) theorems))))
  (doseq [name theorems]
    (when-let [^ConstantInfo d (certification/checked-declaration name)]
      (is (seq (closed/type-form (.-type d))) (str name " closed actual type"))))
  (doseq [{:keys [name type]} public-contracts]
    (let [^ConstantInfo d (declaration name), expected (elab/elaborate @a/ansatz-env type)]
      (is (some? d) (str name " actual declaration"))
      (when d
        (is (= (closed/type-form expected) (closed/type-form (.-type d))) (str name " exact literal type"))
        (let [expanded (elab/elaborate @a/ansatz-env (expanded-independent-contract type))]
          (is (seq (closed/type-form expanded)))
          (is (tc/is-def-eq (tc/mk-tc-state @a/ansatz-env) (.-type d) expanded)
              (str name " actual type agrees with independently expanded helper meanings")))))))

(deftest actual-safe-helper-meanings
  (let [forms (into {} (map (juxt second identity)
                           (filter #(and (seq? %) (= 'a/defn (first %))) (source-forms))))]
    (is (= (set (map second helper-definitions)) (set (keys forms))) "exactly the three reviewed definitions")
    (doseq [[_ name parameters result body :as expected-source] helper-definitions]
      (let [^ConstantInfo d (declaration name)]
        (is (= expected-source (get forms name)) (str name " exact frozen source meaning"))
        (is (some? d))
        (when d
          (is (= :def (kernel-env/ci-tag d)) (str name " is a definition, not a theorem"))
          (is (zero? (.-safety d)))
          (is (seq (closed/type-form (.-type d))))
          (is (seq (closed/type-form (.value d))))
          (is (= (closed/type-form (elab/elaborate @a/ansatz-env (list 'forall parameters result)))
                 (closed/type-form (.-type d))) (str name " exact safe definition signature"))
          (if (= name 'h10-pending-exempt)
            (is (= '(match tail [nil xm] [(cons d t) (List.cons Nat (pair-edge d ps) (h10-pending-exempt ps t xm))]) body)
                "recursive body pinned without claiming evaluation of a symbolic list")
            (let [expected (elab/elaborate @a/ansatz-env (list 'fn parameters body) (.-type d))]
              (is (tc/is-def-eq (tc/mk-tc-state @a/ansatz-env) (.value d) expected)
                  (str name " actual value agrees with independently frozen body")))))))))


(def helper-equations
  '{h10-install.eq_1
    (forall [a :- Nat ds :- (List Nat) acc :- AwAcc]
      (= (h10-install a ds acc)
         (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds)))))
    h10-fill-prefix.eq_1
    (forall [a :- Nat ds :- (List Nat) acc :- AwAcc pre :- (List Nat)]
      (= (h10-fill-prefix a ds acc pre)
         (nat-fold (fast-fill (:pairs acc)) (h10-install a ds acc) pre)))
    h10-pending-exempt.eq_1
    (forall [ps :- (List DE) xm :- (List Nat)]
      (= (h10-pending-exempt ps (List.nil Nat) xm) xm))
    h10-pending-exempt.eq_2
    (forall [ps :- (List DE) xm :- (List Nat) d :- Nat tail :- (List Nat)]
      (= (h10-pending-exempt ps (List.cons Nat d tail) xm)
         (List.cons Nat (pair-edge d ps) (h10-pending-exempt ps tail xm))))})

(deftest actual-helper-equations-and-match-declaration
  (is (= 4 (count helper-equations)))
  (doseq [[name expected] helper-equations]
    (when-let [^ConstantInfo d (certification/checked-declaration name)]
      (is (= (closed/type-form (elab/elaborate @a/ansatz-env expected))
             (closed/type-form (.-type d))) (str name " exact independent equation"))))
  (let [^ConstantInfo d (declaration 'h10-pending-exempt.match_1)]
    (is (some? d))
    (is (= :def (kernel-env/ci-tag d)))
    (is (zero? (.-safety d)))
    (is (seq (closed/type-form (.-type d))))
    (is (seq (closed/type-form (.value d))))))

(def generated-contracts
  ;; Independent invariant schemas; neither copied forms nor registered types
  ;; are consulted to construct these expectations.
  (let [families [['h3 '[xm :- (List Nat)] '[xm] 'hm3-fast-fill 'nat-fold-h3]
                  ['gd [] [] 'gd-fast-fill 'nat-fold-gd]
                  ['gl [] [] 'gl-fast-fill 'nat-fold-gl]
                  ['awo '[awc :- Nat awr :- Nat] '[awc awr] 'awo-fast-fill 'nat-fold-awo]]
        predicate (fn [p args w] (apply list p (concat args [w])))
        truth (fn [p args w] (list '= (predicate p args w) true))
        fills (into {} (for [[p params args fill] families]
                         [fill (list 'forall (into (vec params) '[ps :- (List DE) w :- World d :- Nat])
                                     (list '=> (truth p args 'w) (truth p args '(fast-fill ps w d))))]))
        folds (into {} (for [[p params args _ fold] families]
                         [fold (list 'forall
                                     (into (vec params)
                                       ['f ':- '(=> World Nat World)
                                        'hf ':- (list 'forall '[w :- World x :- Nat]
                                                      (list '=> (truth p args 'w) (truth p args '(f w x))))
                                        'xs ':- '(List Nat) 'w ':- 'World])
                                     (list '=> (truth p args 'w) (truth p args '(nat-fold f w xs))))]))
        updates (into {} (for [[p params args] (rest families)]
                           [(symbol (str p "-act-upd"))
                            (list 'forall (into (vec params)
                                            '[w :- World x :- Nat f :- (=> ActRow ActRow)
                                              hf :- (forall [r :- ActRow] (= (act-id (f r)) (act-id r)))])
                                  (list '=> (truth p args 'w) (truth p args '(act-upd w x f))))]))]
    (merge fills folds updates
           {'awo-react-edges
            '(forall [awc :- Nat awr :- Nat vs :- (List Valid) w :- World c :- Nat]
               (=> (= (awo awc awr w) true) (= (awo awc awr (react-edges w c vs)) true)))
            'awo-react-loop
            '(forall [awc :- Nat awr :- Nat fuel :- (List Nat) w :- World q :- (List Nat)]
               (=> (= (awo awc awr w) true) (= (awo awc awr (react-loop fuel w q)) true)))
            'awo-demand-reactive
            '(forall [awc :- Nat awr :- Nat w :- World d :- Nat]
               (=> (= (awo awc awr w) true) (= (awo awc awr (demand-reactive w d)) true)))
            'awo-await-wire (get wiring/generated-contracts 'awo-await-wire)})))

(deftest exact-safe-generated-dependencies
  (is (= 15 (count generated-contracts)))
  (doseq [[name expected] generated-contracts]
    (when-let [^ConstantInfo d (certification/checked-declaration name)]
      (is (= (closed/type-form (elab/elaborate @a/ansatz-env expected))
             (closed/type-form (.-type d))) (str name " independently specified actual dependency type")))))

(defn row [w table id] (fixture/row w table id))
(defn current-run? [w rid]
  (when-let [r (row w :runs rid)]
    (if-let [c (row w :comps (:of r))] (= (:epoch r) (:epoch c)) true)))

(defn check-old-unexempt [f w exemptions]
  (let [{:keys [old-act old-edge old-run old-owner deferred]} f
        a (row w :acts old-act), e (row w :edges old-edge), c (row w :comps old-owner)]
    (is (= (row (:w f) :acts old-act) a))
    (is (= (row (:w f) :edges old-edge) e))
    (is (= (row (:w f) :runs old-run) (row w :runs old-run)))
    (is (= [(s/->Member old-edge 0)] (:members a)))
    (is (= [1 s/res-none] [(:remaining a) (:tag (first (:slots a)))]))
    (is (= [s/ek-dep old-owner deferred s/ph-armed]
           ((juxt :kind :creditor :debtor :phase) e)))
    (is (= old-act (:id (first (filter #(some (fn [m] (= old-edge (:edge m))) (:members %)) (:acts w))))))
    (is (< (:done-epoch c) (:epoch c)))
    (is (not-any? (set exemptions) [old-owner old-edge deferred]))
    (is (= [s/sk-deferred true 0] ((juxt :kind :open :version) (row w :sources deferred))))
    (is (true? (closed/member-fields? [] (assoc w :acts [a]))))
    (is (true? (hm3/h3-s (:acts w) a (hm3/rk3 (row w :runs old-run)) e)))))

(defn expected-result [w d]
  (cond
    (row w :comps d) (:result (row w :comps d))
    (row w :tasks d) (:result (row w :tasks d))
    (row w :sources d)
    (let [source (row w :sources d), valueless? (or (#{s/sk-mailbox s/sk-semaphore} (:kind source))
                                                  (and (= s/sk-deferred (:kind source)) (zero? (:version source))))]
      (if (and (not (:open source)) valueless?) (s/->RunResult s/res-err 2)
          (s/->RunResult s/res-ok (:state source))))
    :else (s/->RunResult s/res-ok 0)))

(defn checkpoint
  "Walk actual distinct fast-fill prefixes before fin-if-final. Expected member
   aliases, slots, counters and delivery/invalidation choices are read independently."
  [f ds mode k mine xm]
  (let [{:keys [w rid owner]} f, r (row w :runs rid), aid (:next-id w)
        _ (is (true? (base/p3la w))), _ (is (true? (hm3/h3 xm w)))
        _ (is (true? (closed/member-fields? xm w))), _ (is (= [r] (step/tok-run w (:stamp r))))
        _ (is (true? (engine/run-normal r))), _ (is (true? (engine/await-ok w r ds mode aid)))
        _ (is (false? (engine/await-kind-bad w ds)))
        acc (engine/await-acc w r ds mode k mine), pairs (into {} (map (juxt :deb :edge) (:pairs acc)))
        debtors (vec (distinct ds)), initial-members (mapv (fn [i d] (s/->Member (get pairs d) i)) (range) ds)
        installed (h10/h10-install aid ds acc)]
    (is (true? (:ok acc)))
    (is (= (set debtors) (set (keys pairs))))
    (is (= (count debtors) (count (set (vals pairs)))))
    (is (= initial-members (vec (:members (row installed :acts aid)))))
    (is (= mine (:spawned (row installed :acts aid))))
    (loop [i 0, W installed, slots (vec (repeat (count ds) (s/->RunResult s/res-none 0))), members initial-members, deliveries []]
      (let [pre (subvec debtors 0 i), tail (subvec debtors i)
            exemptions (vec (concat (map pairs tail) xm)), a (row W :acts aid)]
        (is (= W (h10/h10-fill-prefix aid ds acc pre)))
        (is (= exemptions (vec (h10/h10-pending-exempt (:pairs acc) tail xm))))
        (is (true? (edits/inv-sample W)))
        (is (true? (hm3/h3 exemptions W)))
        (is (true? (closed/member-fields? exemptions W)))
        (is (true? (hm/gd W)))
        (is (true? (lit/gl W)))
        (doseq [d debtors] (is (true? (idle/awake (:comps W) d))))
        (check-old-unexempt f W exemptions)
        (when a
          (is (= slots (vec (:slots a))))
          (is (= members (vec (:members a))))
          (is (= (count members) (:remaining a)))
          (is (= mine (:spawned a))))
        (if-let [d (first tail)]
          (let [eid (get pairs d), e (row W :edges eid), ready? (engine/fast-ready W d)
                current? (current-run? W rid), dep? (= s/ek-dep (:kind e))
                deliver? (and ready? a e (= s/ph-armed (:phase e)) current?)
                out (engine/fast-fill (:pairs acc) W d)
                value (expected-result W d)
                positions (keep-indexed (fn [j item] (when (= item d) j)) ds)
                next-slots (if deliver? (reduce #(assoc %1 %2 value) slots positions) slots)
                next-members (if deliver? (vec (remove #(= eid (:edge %)) members)) members)
                removed? (and deliver? (or (= mode s/am-any) (empty? next-members)))]
            (when (and ready? (row W :comps d))
              (is (false? (:idle (row W :comps d))))
              (is (true? (step/comp-live (row W :comps d)))))
            (cond
              (not ready?) (is (= W out))
              (nil? e) (is (= W out))
              deliver?
              (do
                (is (= (assoc a :slots (seq next-slots) :members (seq next-members) :remaining (count next-members))
                       (step/act-fill eid value a)))
                (is (= (count (filter #(= eid (:edge %)) members)) (count positions)))
                (if removed? (is (nil? (row out :acts aid)))
                    (is (= (step/act-fill eid value a) (row out :acts aid))))
                (if (and dep? (not (step/deb-final W d)))
                  (let [after-edge (row out :edges eid)]
                    (is (= [eid (:creditor e) d s/ph-armed true true]
                           ((juxt :id :creditor :debtor :phase :has-seen :has-base) after-edge))))
                  (when (and dep? (step/deb-final W d)) (is (nil? (row out :edges eid))))))
              dep?
              (do
                (is (= s/ph-fired (:phase (row out :edges eid))))
                (is (= (inc (:epoch (row W :comps owner))) (:epoch (row out :comps owner))))
                (is (false? (current-run? out rid)))
                (is (= a (row out :acts aid))))
              :else
              (do (is (= s/ph-fired (:phase (row out :edges eid))))
                  (is (= a (row out :acts aid)))))
            (recur (inc i) out next-slots next-members (cond-> deliveries deliver? (conj d))))
          (let [parked (engine/park-if W aid rid)]
            (is (true? (hm3/h3 xm W)))
            (is (true? (closed/member-fields? xm W)))
            (is (true? (hm3/h3 xm parked)))
            (is (true? (closed/member-fields? xm parked)))
            (check-old-unexempt f parked xm)
            (if a
              (is (= [s/act-parked false] ((juxt :act :slice) (row parked :runs rid))))
              (is (= W parked)))
            {:r r :acc acc :installed installed :filled W :parked parked :pairs pairs :deliveries deliveries}))))))

(defn comprehensive-fixture [kind]
  (let [f (fixture/fixture kind), w (fixture/accepted-step (:w f) [20 (:rid f) s/res-ok 77])
        ready (fixture/computation w), w (fixture/accepted-step (:w ready) [20 (:rid ready) s/res-ok 88])
        pending-task (:next-id w), w (fixture/accepted-step w [16 2 101 pending-task []]), pending-rid (inc pending-task)
        w (fixture/accepted-step w [21 pending-rid]), pending-resource (:next-id w)
        w (fixture/accepted-step w [8 pending-rid s/rk-timer 102 pending-resource])
        completed-task (:next-id w), w (fixture/accepted-step w [16 2 103 completed-task []]), completed-rid (inc completed-task)
        w (fixture/accepted-step w [21 completed-rid]), w (fixture/accepted-step w [20 completed-rid s/res-ok 89])
        resource-task (:next-id w), w (fixture/accepted-step w [16 2 104 resource-task []]), resource-rid (inc resource-task)
        w (fixture/accepted-step w [21 resource-rid]), ready-resource (:next-id w)
        w (fixture/accepted-step w [8 resource-rid s/rk-offload 105 ready-resource])
        w (fixture/accepted-step w [9 ready-resource s/res-ok 90])
        [w signal] (fixture/source w s/sk-signal 51), [w cell] (fixture/source w s/sk-cell 52)
        [w delivered] (fixture/source w s/sk-deferred 0), w (fixture/accepted-step w [25 delivered 53])
        scope-task (:next-id w), w (fixture/accepted-step w [16 2 106 scope-task []]), scope-rid (inc scope-task)
        w (fixture/accepted-step w [21 scope-rid]), scope (:next-id w)
        w (fixture/accepted-step w [32 scope-rid scope])
        closed-source (:next-id w), w (fixture/accepted-step w [1 scope s/sk-deferred 0 closed-source])
        w (fixture/accepted-step w [33 scope]), w (fixture/accepted-step w [20 scope-rid s/res-ok 0])
        selected (if (= kind :comp)
                   (let [w (fixture/accepted-step w [14 2 (:owner f) [9] 9]), rid (:next-id w)
                         w (fixture/accepted-step w [19 (:owner f) rid])]
                     {:w (fixture/accepted-step w [21 rid]) :rid rid :owner (:owner f)})
                   (let [owner (:next-id w), w (fixture/accepted-step w [16 2 107 owner []]), rid (inc owner)]
                     {:w (fixture/accepted-step w [21 rid]) :rid rid :owner owner}))]
    (is (false? (:open (row (:w selected) :sources closed-source))))
    (is (= 0 (:version (row (:w selected) :sources closed-source))))
    (merge f selected {:ready-comp (:c ready) :pending-task pending-task :completed-task completed-task
                       :pending-resource pending-resource :ready-resource ready-resource
                       :signal signal :cell cell :delivered delivered :closed-source closed-source})))


(deftest accepted-mixed-fill-prefixes-with-old-waiting-members
  (doseq [kind [:comp :task]]
    (let [{:keys [ready-comp pending-task completed-task delivered closed-source signal cell
                  pending-resource ready-resource fresh top deferred] :as f} (comprehensive-fixture kind)
          ds [ready-comp ready-comp pending-task completed-task delivered closed-source signal cell
              pending-resource ready-resource fresh top deferred]
          out (checkpoint f ds s/am-all 2001 [fresh top fresh] [])
          aid (:next-id (:w f)), installed (:installed out), filled (:filled out)
          a (row filled :acts aid)]
      (when (= kind :comp)
        (is (false? (hm3/h3 [] installed)) "live computation dep members really require temporary exemptions"))
      (is (true? (hm3/h3 [] filled)))
      (is (some? a) "pending computation, task, deferred and resource leave actual members")
      (is (= #{pending-task pending-resource fresh deferred}
             (set (keep (fn [[d eid]] (when (some #(= eid (:edge %)) (:members a)) d)) (:pairs out)))))
      (is (= (s/->RunResult s/res-ok 88) (nth (:slots a) 0) (nth (:slots a) 1)))
      (is (= (s/->RunResult s/res-ok 89) (nth (:slots a) 3)))
      (is (= (s/->RunResult s/res-ok 53) (nth (:slots a) 4)))
      (is (= (s/->RunResult s/res-err 2) (nth (:slots a) 5)))
      (is (= (s/->RunResult s/res-ok 51) (nth (:slots a) 6)))
      (is (= (s/->RunResult s/res-ok 52) (nth (:slots a) 7)))
      (is (= [s/act-parked false] ((juxt :act :slice) (row (:parked out) :runs (:rid f))))))))

(deftest accepted-all-fast-aliases-all-modes-and-early-resume
  (doseq [kind [:comp :task]]
    (let [{:keys [signal cell ready-comp delivered] :as f} (comprehensive-fixture kind)]
      (doseq [[ds mode] [[[ready-comp ready-comp signal delivered] s/am-all]
                         [[ready-comp] s/am-one]
                         [[signal cell ready-comp signal] s/am-any]]]
        (let [out (checkpoint f ds mode 2002 [ready-comp ready-comp] [])
              aid (:next-id (:w f)), after (:filled out), r (row after :runs (:rid f))]
          (is (nil? (row after :acts aid)))
          (is (= after (:parked out)))
          (if (= mode s/am-any)
            (do
              (is (= [signal] (:deliveries out)))
              (if (= kind :comp)
                (do
                  (is (= (+ 2 (:epoch (row (:w f) :comps (:owner f))))
                         (:epoch (row after :comps (:owner f)))))
                  (is (false? (current-run? after (:rid f))))
                  (doseq [d [cell ready-comp]]
                    (is (= s/ph-fired (:phase (row after :edges (get (:pairs out) d)))))))
                (doseq [d [cell ready-comp]]
                  (is (nil? (row after :edges (get (:pairs out) d)))))))
            (do (is (= (vec (distinct ds)) (:deliveries out)))
                (is (true? (current-run? after (:rid f)))))))))))

(deftest accepted-valid-invalid-and-fresh-idle-debtors
  (let [{:keys [w top bottom fresh leaf] :as f} (fixture/fixture :comp)
        valid-before (into {} (for [d [top bottom]] [d (:validity (row w :comps d))]))]
    (is (true? (engine/valid-idle w (row w :comps top))))
    (let [out (checkpoint f [top top fresh leaf] s/am-all 2003 [fresh] [])
          demanded (:world (:acc out))]
      (doseq [d [top bottom]]
        (is (seq (get valid-before d)))
        (is (false? (:idle (row demanded :comps d))))
        (is (= (:result (row w :comps d)) (:result (row demanded :comps d))))
        (doseq [v (get valid-before d)]
          (let [e (first (filter #(and (= d (:creditor %)) (= (:debtor v) (:debtor %))) (:edges demanded)))]
            (is (= [s/ek-dep true (:version v) true (:version v)]
                   ((juxt :kind :has-seen :seen :has-base :base-version) e))))))
      (is (false? (:idle (row demanded :comps fresh))))
      (is (= 0 (:done-epoch (row demanded :comps fresh)))))
    (let [changed (fixture/accepted-step w [2 leaf 31]), invalid (row changed :comps top)
          out (checkpoint (assoc f :w changed) [top top fresh] s/am-all 2004 [top] [])
          demanded (:world (:acc out))]
      (is (:idle invalid))
      (is (false? (engine/valid-idle changed invalid)))
      (is (= (inc (:epoch invalid)) (:epoch (row demanded :comps top))))
      (is (false? (:idle (row demanded :comps top))))
      (is (false? (engine/fast-ready demanded top))))))

(deftest accepted-reused-site-and-stale-current-token-distinction
  (let [{:keys [w rid owner reused-edge second-source reused-source deferred] :as f} (wiring/reuse-fixture)
        before (row w :edges reused-edge), records (:adopt-baselines (row w :comps owner))
        out (checkpoint f [reused-source second-source reused-source deferred] s/am-all 2005 [deferred] [])
        wired (:world (:acc out)), e (row wired :edges reused-edge), a (row (:filled out) :acts (:next-id w))]
    (is (= reused-edge (get (:pairs out) reused-source)))
    (is (= (dissoc before :phase :cont) (dissoc e :phase :cont)))
    (is (= 2 (count records)))
    (is (= 1 (count (:adopt-baselines (row wired :comps owner)))))
    (is (= (s/->RunResult s/res-ok 33) (nth (:slots a) 0) (nth (:slots a) 2)))
    (is (= 1 (:remaining a)))
    (let [stale-world (fixture/accepted-step w [2 reused-source 34]), stale (row stale-world :runs rid)
          out (checkpoint (assoc f :w stale-world) [deferred (:leaf f) reused-source] s/am-any 2006 [deferred] [])
          filled (:filled out), a (row filled :acts (:next-id stale-world))]
      (is (false? (current-run? stale-world rid)))
      (is (true? (:slice stale)))
      (is (= [stale] (step/tok-run stale-world (:stamp stale))))
      (is (empty? (:deliveries out)))
      (is (some? a))
      (is (= 3 (:remaining a)))
      (is (every? #(= s/res-none (:tag %)) (:slots a)))
      (is (= (+ 2 (:epoch (row stale-world :comps owner))) (:epoch (row filled :comps owner)))))))

(deftest accepted-stale-run-ready-resource-wait-does-not-deliver
  (let [{:keys [w rid signal pending-resource ready-resource delivered] :as f} (comprehensive-fixture :comp)
        w (fixture/accepted-step w [3 rid signal 2009 (:next-id w)])
        w (fixture/accepted-step w [2 signal 54]), r (row w :runs rid)
        out (checkpoint (assoc f :w w) [pending-resource ready-resource delivered] s/am-all 2010 [signal] [])
        filled (:filled out), resource-edge (row filled :edges (get (:pairs out) ready-resource))]
    (is (false? (current-run? w rid)))
    (is (= [r] (step/tok-run w (:stamp r))))
    (is (empty? (:deliveries out)))
    (is (= [s/ek-wait s/ph-fired] ((juxt :kind :phase) resource-edge)))
    (is (= 3 (:remaining (row filled :acts (:next-id w)))))
    (is (every? #(= s/res-none (:tag %)) (:slots (row filled :acts (:next-id w)))))))

(deftest overlapping-nonempty-exemptions-leave-a-real-old-obligation
  (let [{:keys [w rid ready-comp signal deferred] :as f} (comprehensive-fixture :comp)
        ds [ready-comp signal deferred], acc (engine/await-acc w (row w :runs rid) ds s/am-all 2007 [signal])
        overlap (get (into {} (map (juxt :deb :edge) (:pairs acc))) ready-comp)
        xm [overlap], out (checkpoint f ds s/am-all 2007 [signal] xm)]
    (is (pos? overlap))
    (is (not= overlap (:old-edge f)))
    (is (true? (hm3/h3 xm (:filled out))))
    (is (some? (row (:filled out) :acts (:next-id w))))
    (check-old-unexempt f (:filled out) xm)))

(deftest retained-raw0-refusals-have-real-outer-guards
  ;; The comprehensive predecessor suite independently covers sticky rank failure,
  ;; arbitrary checked insertion refusal, parked broad inputs and cleanup tokens.
  ;; Here the actual raw0 identity branches are exercised again at the checkpoint.
  (let [{:keys [w rid owner deferred consuming]} (fixture/fixture :comp)
        r (row w :runs rid), st (:stamp r), fresh (:next-id w)]
    (doseq [item [[18 999999 [deferred] s/am-one 2008 fresh []]
                  [18 st [deferred] s/am-one 2008 (inc fresh) []]
                  [18 st [deferred] 99 2008 fresh []]
                  [18 st [] s/am-all 2008 fresh []]
                  [18 st [999999] s/am-one 2008 fresh []]
                  [18 st [owner] s/am-one 2008 fresh []]]]
      (fixture/refused-raw w item))
    (is (true? (engine/await-ok w r [consuming] s/am-one fresh)))
    (is (true? (engine/await-kind-bad w [consuming])))
    (fixture/refused-raw w [18 st [consuming] s/am-one 2008 fresh []])
    (let [accepted (engine/raw0 w [18 st [deferred] s/am-one 2008 fresh []])]
      (is (true? (:accepted accepted)))
      (fixture/refused-raw (:world accepted) [18 st [deferred] s/am-one 2008 (:next-id (:world accepted)) []]))))
