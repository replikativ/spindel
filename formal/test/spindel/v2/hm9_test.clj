(ns spindel.v2.hm9-test
  "Independent literal HM9 contract manifest, frozen before proof implementation.
   Source: separately confirmed annex SHA256
   3e9e968a1648e1c75a48410e5f43b859ca3ad2cd79c9171310ad7bbfbe48b94d."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [ansatz.core :as a]
            [ansatz.surface.elaborate :as elab]
            [ansatz.kernel.env :as kernel-env]
            [ansatz.kernel.tc :as tc]
            [spindel.v2.hm9]
            [spindel.v2.hm8]
            [spindel.v2.hm8-test :as fixture]
            [spindel.v2.state :as s]
            [spindel.v2.edits :as edits]
            [spindel.v2.step :as step]
            [spindel.v2.engine :as engine]
            [spindel.v2.acts :as acts]
            [spindel.v2.idle :as idle]
            [spindel.v2.p3 :as p3]
            [spindel.v2.hm :as hm]
            [spindel.v2.hm3 :as hm3]
            [spindel.v2.hm6 :as hm6]
            [spindel.v2.hm6-base :as base]
            [spindel.v2.lit :as lit]
            [spindel.v2.i8 :as i8]
            [spindel.v2.rank-step :as rank]
            [spindel.v2.hm6-test :as certification]
            [spindel.v2.hm7-test :as closed])
  (:import [ansatz.kernel ConstantInfo Env Name]
           [java.io PushbackReader]))

(def helper-definitions
  '[
(a/defn h9-entry [xm :- (List Nat), w :- World, r :- RunRow,
                  ds :- (List Nat), mode :- Nat, st :- Nat, fresh :- Nat] Prop
  (And (= (p3la w) true)
   (And (= (h3 xm w) true)
    (And (= (tok-run w st) (Option.some RunRow r))
         (= (await-ok w r ds mode fresh) true)))))

(a/defn h9-act [w :- World, r :- RunRow, ds :- (List Nat),
                mode :- Nat, k :- Nat, mine :- (List Nat)] ActRow
  (ActRow.mk (:next-id w) (:id r) mode (List.nil Member)
             (none-slots ds) (nat-len ds) k mine))

(a/defn h9-prefix [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                   k :- Nat, mine :- (List Nat), pre :- (List Nat)] AwAcc
  (await-wire r (:next-id w) mode k
    (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) pre))

(a/defn h9-debtors [ps :- (List DE)] (List Nat)
  (match ps [nil (List.nil Nat)]
    [(cons p t) (List.cons Nat (:deb p) (h9-debtors t))]))

(a/defn h9-pairs [pre :- (List Nat), tail :- (List Nat), ps :- (List DE)] Prop
  (And (forall [d :- Nat]
         (Iff (= (de-has d ps) true) (= (nat-mem d pre) true)))
   (And (= (nat-len (h9-debtors ps)) (nat-len pre))
    (And (= (nat-nodup (h9-debtors ps)) true)
     (And (forall [d :- Nat]
            (=> (= (nat-mem d tail) true) (= (de-has d ps) false)))
          (forall [p :- DE, q :- DE]
            (=> (List.Mem p ps) (List.Mem q ps) (= (:edge p) (:edge q))
                (= (:deb p) (:deb q)))))))))

(a/defn h9-edge-fields [P :- World, r :- RunRow, a :- Nat, mode :- Nat,
                       k :- Nat, d :- Nat, e :- EdgeRow] Prop
  (And (= (:debtor e) d)
   (And (= (:at e) (:effect-index r))
    (And (= (:phase e) ph-armed)
     (And (= (:kind e) (if (as-dep P r d) ek-dep ek-wait))
      (And (= (:creditor e) (if (as-dep P r d) (:of r) a))
           (= (:cont e) (if (as-dep P r d) (await-cont r mode k) cont-restart))))))))

(a/defn h9-support [xm :- (List Nat), W :- World, r :- RunRow, a :- Nat] Prop
  (And (= (h3 xm W) true)
   (And (= (g7 W) true)
    (And (= (aha W) true)
     (And (= (gd W) true)
      (And (= (ar W) true)
       (And (= (hmk (List.nil Nat) W) true)
        (And (= (ekb W) true)
         (And (= (gl W) true)
          (And (= (ka (:id r) W) true)
           (And (= (awo (:of r) (:id r) W) true)
                (= (gx (Ex.mk (:id r) a) W) true))))))))))))

(a/defn h9-shape [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                  k :- Nat, mine :- (List Nat), W :- World] Prop
  (And (= (:acts W) (List.cons ActRow (h9-act w r ds mode k mine) (:acts w)))
   (And (= (:runs W) (:runs (run-upd w (:id r) run-tick)))
    (And (= (:tasks W) (:tasks w))
     (And (= (:sources W) (:sources w))
      (And (= (:res W) (:res w))
           (forall [x :- Nat] (= (comp-has W x) (comp-has w x)))))))))
])

(def public-contracts
  '
[
{:name h3-await-step
 :type (forall [xm :- (List Nat), r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (h3 xm (:world acc)) true)
      (= (h3 xm (:world (await-step r a mode k acc d))) true)))}

{:name h3-await-wire
 :type (forall [xm :- (List Nat), r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, ds :- (List Nat), acc :- AwAcc]
  (=> (= (h3 xm (:world acc)) true)
      (= (h3 xm (:world (await-wire r a mode k acc ds))) true)))}

{:name h3-await-acc-p3la
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (p3la w) true) (= (h3 xm w) true) (List.Mem r (:runs w)) (= (run-alive r) true)
      (= (h3 xm (:world (await-acc w r ds mode k mine))) true)))}

{:name h9-awo-of-run
 :type (forall [w :- World, r :- RunRow]
  (=> (= (g7 w) true) (List.Mem r (:runs w)) (= (run-alive r) true)
      (= (awo (:of r) (:id r) w) true)))}

{:name h9-prefix-support
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat)]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre tail) (nat-distinct ds))
      (h9-support xm (:world (h9-prefix w r ds mode k mine pre)) r (:next-id w))))}

{:name h9-prefix-shape
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat)]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre tail) (nat-distinct ds))
      (h9-shape w r ds mode k mine (:world (h9-prefix w r ds mode k mine pre)))))}

{:name h9-prefix-pairs
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat)]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre tail) (nat-distinct ds))
      (h9-pairs pre tail (:pairs (h9-prefix w r ds mode k mine pre)))))}

{:name h9-prefix-pair-edge
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat), d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre tail) (nat-distinct ds)) (= (nat-mem d pre) true)
      (let [C (h9-prefix w r ds mode k mine pre), W (:world C), x (pair-edge d (:pairs C))]
        (Exists (fn [e :- EdgeRow]
          (And (= (edge-find W x) (Option.some EdgeRow e))
           (And (= (:id e) x)
            (And (h9-edge-fields (await-pre w r ds mode k mine) r (:next-id w) mode k d e)
                 (forall [q :- EdgeRow]
                   (=> (List.Mem q (:edges W)) (= (:id q) x) (= q e)))))))))))}

{:name h9-next-edge-ok
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat), d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre (List.cons Nat d tail)) (nat-distinct ds))
      (let [W (:world (h9-prefix w r ds mode k mine pre))]
        (= (edge-ok-in W (await-edge W r (:next-id w) mode k d)) true))))}

{:name h9-prefix-reuse-free
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat), d :- Nat, e :- EdgeRow]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre (List.cons Nat d tail)) (nat-distinct ds))
      (= (as-dep (:world (h9-prefix w r ds mode k mine pre)) r d) true)
      (= (site-edge (:edges (:world (h9-prefix w r ds mode k mine pre))) (:of r) (:effect-index r) d)
         (Option.some EdgeRow e))
      (= (h3-free xm (:world (h9-prefix w r ds mode k mine pre)) (:id e)) true)))}

{:name h9-prefix-pair-free
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat), p :- DE]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre tail) (nat-distinct ds)) (List.Mem p (:pairs (h9-prefix w r ds mode k mine pre)))
      (= (h3-free xm (:world (h9-prefix w r ds mode k mine pre)) (:edge p)) true)))}

{:name h9-installed-first-holder
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (let [C (await-acc w r ds mode k mine), W (:world C), ps (:pairs C),
            M (mk-members ps 0 ds), b2 (act-set-members M (h9-act w r ds mode k mine)),
            I (act-upd W (:next-id w) (act-set-members M)), x (pair-edge d ps)]
        (Exists (fn [e :- EdgeRow]
          (And (= (edge-find W x) (Option.some EdgeRow e))
           (And (= (edge-find I x) (Option.some EdgeRow e))
            (And (= (act-with-member x (:acts I)) (Option.some ActRow b2))
                 (= (h3-s (:acts I) b2 (rk3 r) e) true)))))))))}

{:name h9-members-split
 :type (forall [ps :- (List DE), i :- Nat, left :- (List Nat), d :- Nat, right :- (List Nat)]
  (= (mk-members ps i (List.append Nat left (List.cons Nat d right)))
     (List.append Member (mk-members ps i left)
       (List.cons Member (Member.mk (pair-edge d ps) (+ i (nat-len left)))
         (mk-members ps (+ (+ i (nat-len left)) 1) right)))))}

{:name h9-member-count
 :type (forall [ps :- (List DE), i :- Nat, ds :- (List Nat)]
  (= (nat-len (member-edges (mk-members ps i ds))) (nat-len ds)))}

{:name h9-duplicate-slots
 :type (forall [ps :- (List DE), i :- Nat, left :- (List Nat), d :- Nat, middle :- (List Nat), right :- (List Nat)]
  (let [ds (List.append Nat left (List.cons Nat d (List.append Nat middle (List.cons Nat d right)))),
        j (+ i (nat-len left)), l (+ (+ j 1) (nat-len middle)),
        m1 (Member.mk (pair-edge d ps) j), m2 (Member.mk (pair-edge d ps) l)]
    (And (List.Mem m1 (mk-members ps i ds))
     (And (List.Mem m2 (mk-members ps i ds))
      (And (= (:edge m1) (:edge m2)) (= (Nat.blt (:idx m1) (:idx m2)) true))))))}

{:name h9-step-ok-false
 :type (forall [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (:ok acc) false) (= (:ok (await-step r a mode k acc d)) false)))}

{:name h9-wire-ok-false
 :type (forall [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, ds :- (List Nat)]
  (=> (= (:ok acc) false) (= (:ok (await-wire r a mode k acc ds)) false)))}

{:name h9-acc-rank
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (:ok (await-acc w r ds mode k mine)) true)
      (= (inv-rank (:world (await-acc w r ds mode k mine))) true)))}

{:name h9-step-reuse-frame
 :type (forall [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat, e :- EdgeRow]
  (=> (= (inv-sample (:world acc)) true) (= (as-dep (:world acc) r d) true)
      (= (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d) (Option.some EdgeRow e))
      (let [B (await-step r a mode k acc d)]
        (And (= (:next-id (:world B)) (:next-id (:world acc)))
         (And (= (:pairs B) (List.cons DE (DE.mk d (:id e)) (:pairs acc)))
          (And (= (:ok B) (:ok acc))
               (= (edge-find (:world B) (:id e))
                  (Option.some EdgeRow (edge-reawait (await-cont r mode k) e)))))))))}

{:name h9-step-fresh-frame
 :type (forall [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (inv-sample (:world acc)) true)
      (= (edge-ok-in (:world acc) (await-edge (:world acc) r a mode k d)) true)
      (Or (= (as-dep (:world acc) r d) false)
          (= (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d) (Option.none EdgeRow)))
      (let [B (await-step r a mode k acc d), n (:next-id (:world acc)),
            e (edge-set-marked false (edge-set-id n (await-edge (:world acc) r a mode k d)))]
        (And (= (:next-id (:world B)) (+ n 1))
         (And (= (:pairs B) (List.cons DE (DE.mk d n) (:pairs acc)))
          (And (= (edge-find (:world B) n) (Option.some EdgeRow e))
               (= (:ok B)
                  (if (as-dep (:world acc) r d)
                    (Bool.and (:ok acc) (:ok (await-new-dep (:world acc) r a mode k d)))
                    (:ok acc)))))))))}

{:name h9-step-adoption
 :type (forall [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat, c :- CompRow]
  (=> (= (inv-sample (:world acc)) true) (= (as-dep (:world acc) r d) true)
      (= (comp-find (:world acc) (:of r)) (Option.some CompRow c))
      (Exists (fn [c2 :- CompRow]
        (And (= (comp-find (:world (await-step r a mode k acc d)) (:of r)) (Option.some CompRow c2))
         (And (= (:adopt-baselines c2)
                 (tbl-filter (adopt-other (:effect-index r) d) (:adopt-baselines c)))
          (And (= (:adopt-basis c2) (:adopt-basis c)) (= (:basis c2) (:basis c)))))))))}
])

(deftest frozen-hm9-manifest
  (is (= 8 (count helper-definitions)))
  (is (= 21 (count public-contracts)))
  (is (= 21 (count (set (map :name public-contracts))))))


(defn source-forms []
  (with-open [reader (PushbackReader. (io/reader (io/resource "spindel/v2/hm9.clj")))]
    (loop [forms []]
      (if-let [form (read {:eof nil} reader)] (recur (conj forms form)) forms))))

(def theorems
  (mapv second (filter #(and (seq? %) (= 'a/theorem (first %))) (source-forms))))

(defn declaration [name]
  (.lookup ^Env @a/ansatz-env (Name/fromString (str name))))

(defn expanded-independent-contract [contract]
  ;; Nonrecursive aliases are independently bound to the frozen meanings.
  ;; Kernel beta/delta/zeta equality performs expansion; recursive h9-debtors
  ;; is retained and its exact source recursion is separately pinned below.
  (let [bindings (mapcat (fn [[_ name parameters _ body]]
                          (when-not (= name 'h9-debtors)
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
    (is (= (set (map second helper-definitions)) (set (keys forms))) "exactly the eight reviewed definitions")
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
          (if (= name 'h9-debtors)
            (is (= '(match ps [nil (List.nil Nat)] [(cons p t) (List.cons Nat (:deb p) (h9-debtors t))]) body)
                "recursive body pinned without claiming evaluation of a symbolic list")
            (let [expected (elab/elaborate @a/ansatz-env (list 'fn parameters body) (.-type d))]
              (is (tc/is-def-eq (tc/mk-tc-state @a/ansatz-env) (.value d) expected)
                  (str name " actual value agrees with independently frozen body")))))))))

(defn row [w table id] (fixture/row w table id))

(defn check-entry [f ds mode]
  (let [{:keys [w rid]} f, r (row w :runs rid)]
    (fixture/check-input f)
    (is (= [r] (step/tok-run w (:stamp r))))
    (is (true? (engine/await-ok w r ds mode (:next-id w))))
    (is (true? (idle/awo (:of r) (:id r) w)))
    (is (true? (i8/ka (:id r) w)))
    r))

(defn check-local-support [w r aid]
  (fixture/check-h3-fields w)
  (fixture/check-supports w)
  (is (true? (lit/gl w)))
  (is (true? (i8/ka (:id r) w)))
  (is (true? (idle/awo (:of r) (:id r) w)))
  (is (true? (acts/gx (acts/->Ex (:id r) aid) w)))
  ;; The distinguished activation still belongs to a live slice. GA is not
  ;; asserted at this boundary, and p3la is not an internal wiring premise.
  (doseq [a (:acts w), :when (not= aid (:id a))]
    (let [run (row w :runs (:run a))]
      (is (some? run))
      (is (= s/act-parked (:act run)))
      (is (false? (:slice run))))))

(defn check-shape [w r ds mode k mine out]
  (let [aid (:next-id w), a (first (:acts out))]
    (is (= (s/->ActRow aid (:id r) mode nil
                       (vec (repeat (count ds) (s/->RunResult s/res-none 0)))
                       (count ds) k mine) a))
    (is (= (:acts w) (rest (:acts out))))
    (is (= (:runs (s/run-upd w (:id r) step/run-tick)) (:runs out)))
    (doseq [table [:tasks :sources :res]] (is (= (table w) (table out))))
    (is (= (set (map :id (:comps w))) (set (map :id (:comps out)))))
  (is (= (:effect-index r) (dec (:effect-index (row out :runs (:id r))))))))

(defn independent-edge-fields [P r aid mode k d]
  (let [dep? (and (some #(= (:of r) (:id %)) (:comps P))
                  (not-any? #(= d (:id %)) (:res P)))
        continuation (if (and (= mode s/am-one) (empty? (:finalizers r)) (empty? (:resources r)))
                       k s/cont-restart)]
    {:debtor d :at (:effect-index r) :phase s/ph-armed
     :kind (if dep? s/ek-dep s/ek-wait)
     :creditor (if dep? (:of r) aid) :cont (if dep? continuation s/cont-restart)}))

(defn check-prefix [f r ds mode k mine pre tail acc]
  (let [{:keys [w]} f, aid (:next-id w), P (engine/await-pre w r ds mode k mine)
        W (:world acc), pairs (:pairs acc), by-debtor (into {} (map (juxt :deb :edge) pairs))]
    (is (= (vec (distinct ds)) (vec (concat pre tail))))
    (is (= (set pre) (set (map :deb pairs))))
    (is (= (count pre) (count pairs)))
    (is (= (count pairs) (count (set (map :deb pairs)))))
    (is (empty? (clojure.set/intersection (set tail) (set (map :deb pairs)))))
    (is (= (count pairs) (count (set (map :edge pairs)))))
    (check-shape w r ds mode k mine W)
    (check-local-support W r aid)
    (fixture/check-old-obligation f W)
    (doseq [[d eid] by-debtor]
      (let [matches (filter #(= eid (:id %)) (:edges W)), e (first matches)]
        (is (= 1 (count matches)))
        (is (= (independent-edge-fields P r aid mode k d)
               (select-keys e [:debtor :at :phase :kind :creditor :cont])))
        ;; First-holder freeness is an obligation check, independent of ok.
        (is (not-any? #(some (fn [m] (= eid (:edge m))) (:members %)) (:acts W)))))
    (doseq [d tail]
      (is (not (contains? by-debtor d)))
      (when-let [e (first (step/site-edge (:edges W) (:of r) (:effect-index r) d))]
        (is (not-any? #(some (fn [m] (= (:id e) (:edge m))) (:members %)) (:acts W)))))
    by-debtor))

(defn wire-prefixes [f ds mode k mine]
  (let [{:keys [w]} f, r (check-entry f ds mode), P (engine/await-pre w r ds mode k mine)
        debtors (vec (distinct ds))]
    (loop [i 0, acc (engine/->AwAcc P nil true), expected {}]
      (let [pre (subvec debtors 0 i), tail (subvec debtors i)]
        (is (= expected (check-prefix f r ds mode k mine pre tail acc)))
        (if-let [d (first tail)]
          (let [W (:world acc), old (when (= s/ek-dep (:kind (engine/await-edge W r (:next-id w) mode k d)))
                                    (first (step/site-edge (:edges W) (:of r) (:effect-index r) d)))
                eid (if old (:id old) (:next-id W)), out (engine/await-step r (:next-id w) mode k acc d)]
            (is (true? (edits/edge-ok-in W (engine/await-edge W r (:next-id w) mode k d))))
            (is (= (if old (:next-id W) (inc (:next-id W))) (:next-id (:world out))))
            (when old
              (is (= (dissoc old :phase :cont) (dissoc (row (:world out) :edges eid) :phase :cont))))
            (recur (inc i) out (assoc expected d eid)))
          (do (is (= acc (engine/await-acc w r ds mode k mine)))
              (is (true? (:ok acc)))
              (is (true? (rank/inv-rank (:world acc))))
              {:r r :P P :acc acc :pairs expected}))))))

(defn installed-slots [f ds mode k mine {:keys [r acc pairs]}]
  (let [{:keys [w]} f, aid (:next-id w), W (:world acc)
        expected (mapv (fn [i d] (s/->Member (get pairs d) i)) (range) ds)
        installed (s/act-upd W aid (engine/act-set-members expected))
        a (row installed :acts aid)]
    (is (= expected (vec (engine/mk-members (:pairs acc) 0 ds))))
    (is (= (count ds) (count (:members a))))
    (is (= (vec (range (count ds))) (mapv :idx (:members a))))
    (is (= (:acts w) (rest (:acts installed))))
    (is (= (count ds) (:remaining a)))
    (is (= mine (:spawned a)))
    (doseq [[i d] (map-indexed vector ds)]
      (let [member (nth expected i), e (row installed :edges (:edge member))
            holders (filter #(some (fn [m] (= (:id e) (:edge m))) (:members %)) (:acts installed))]
        (is (= d (:debtor e)))
        (is (= aid (:id (first holders))))
        (is (true? (hm3/h3-s (:acts installed) a (hm3/rk3 r) e)))))
    (doseq [i (range (count ds)), j (range (count ds))]
      (is (= (= (nth ds i) (nth ds j)) (= (:edge (nth expected i)) (:edge (nth expected j))))))
    installed))

(defn reuse-fixture
  "A finite accepted dispatch trace provides a reuse witness, not a T11 theorem."
  []
  (let [f (fixture/fixture :comp), [w leaf] (fixture/source (:w f) s/sk-signal 30)
        [w second-source] (fixture/source w s/sk-signal 40)
        rid (:rid f), old-edge (inc (:next-id w))
        w (fixture/accepted-step w [18 rid [leaf second-source] s/am-all 101 (:next-id w) []])
        w (fixture/accepted-step w [3 rid leaf 102 (:next-id w)])
        w (fixture/accepted-step w [20 rid s/res-ok 7])
        w (fixture/accepted-step w [2 leaf 33]), nr (:next-id w)
        w (fixture/accepted-step w [19 (:owner f) nr])
        w (fixture/accepted-step w [21 nr])]
    (assoc f :w w :rid nr :reused-edge old-edge :second-source second-source :reused-source leaf)))

(deftest accepted-reuse-and-mixed-fresh-wiring
  (let [{:keys [w rid owner leaf second-source reused-edge fresh top bottom] :as f} (reuse-fixture)
        original (row w :edges reused-edge), c (row w :comps owner)
        records (vec (:adopt-baselines c)), leaf (:reused-source f), k 990, mine [fresh top fresh]]
    (is (= 2 (count records)))
    (is (= #{[0 second-source] [1 leaf]} (set (map (juxt :site :source) records))))
    (is (= [true 0 true 30 0 false s/cont-restart]
           ((juxt :has-seen :seen :has-base :base-value :base-version :marked :cont) original)))
    (testing "reuse changes the restart continuation to a new one-shot continuation"
      (let [{:keys [acc pairs]} (wire-prefixes f [leaf] s/am-one k mine), after (:world acc)
            e (row after :edges reused-edge)]
        (is (= {leaf reused-edge} pairs))
        (is (= k (:cont e)))
        (is (= (dissoc original :phase :cont) (dissoc e :phase :cont)))
        (is (= (inc (:next-id w)) (:next-id after)))
        (is (= records (vec (:adopt-baselines (row after :comps owner)))))))
    (testing "fresh siblings consume matching adoption and repeated slots alias intentionally"
      (let [ds [leaf second-source leaf fresh top], result (wire-prefixes f ds s/am-all k mine)
            {:keys [P acc pairs]} result, after (:world acc), installed (installed-slots f ds s/am-all k mine result)]
        (is (= reused-edge (get pairs leaf)))
        (is (= (:next-id P) (get pairs second-source)))
        (is (= (+ (:next-id w) 3) (:next-id P)) "activation and two validity-chain edges precede member allocation")
        (is (= (+ 3 (:next-id P)) (:next-id after)))
        (is (= [(first (filter #(= 1 (:site %)) records))]
               (vec (:adopt-baselines (row after :comps owner)))))
        (doseq [field [:basis :adopt-basis]] (is (= (field c) (field (row after :comps owner)))))
        (is (> (:rank (row after :comps owner)) (:rank c)))
        (doseq [d [top bottom]]
          (is (:idle (row w :comps d)))
          (is (false? (:idle (row P :comps d))))
          (doseq [v (:validity (row w :comps d))]
            (let [e (first (filter #(and (= d (:creditor %)) (= (:debtor v) (:debtor %))) (:edges P)))]
              (is (some? e))
              (is (= [true (:version v) true (:version v)]
                     ((juxt :has-seen :seen :has-base :base-version) e))))))
        (is (true? (hm3/h3 [] after)))))))

(deftest accepted-task-and-resource-wait-branches
  (let [{:keys [deferred leaf top] :as f} (fixture/fixture :task)
        ds [deferred top deferred leaf], result (wire-prefixes f ds s/am-all 809 [top])]
    (doseq [eid (vals (:pairs result))]
      (is (= [s/ek-wait (:next-id (:w f)) s/cont-restart]
             ((juxt :kind :creditor :cont) (row (:world (:acc result)) :edges eid)))))
    (installed-slots f ds s/am-all 809 [top] result))
  (let [{:keys [w rid deferred] :as f} (fixture/fixture :comp), z (:next-id w)
        w (fixture/accepted-step w [8 rid s/rk-timer 701 z])
        w (fixture/accepted-step w [9 z s/res-ok 0])
        w (fixture/accepted-step w [21 rid]), f (assoc f :w w)
        result (wire-prefixes f [z deferred] s/am-all 810 [z]), after (:world (:acc result))]
    (is (some #{z} (:resources (:r result))))
    (is (= [s/ek-wait (:next-id w) s/cont-restart]
           ((juxt :kind :creditor :cont) (row after :edges (get (:pairs result) z)))))
    (is (= [s/ek-dep (:owner f)]
           ((juxt :kind :creditor) (row after :edges (get (:pairs result) deferred)))))))

(deftest ready-debtor-member-installation-is-only-structural
  (let [f (fixture/fixture :comp)
        w (fixture/accepted-step (:w f) [20 (:rid f) s/res-ok 77])
        ready (fixture/computation w)
        w (fixture/accepted-step (:w ready) [20 (:rid ready) s/res-ok 88])
        w (fixture/accepted-step w [14 2 (:owner f) [9] 9]), nr (:next-id w)
        w (fixture/accepted-step w [19 (:owner f) nr])
        w (fixture/accepted-step w [21 nr])
        f (assoc f :w w :rid nr), d (:c ready), ds [d d], mine [d]
        result (wire-prefixes f ds s/am-all 991 mine), acc (:acc result)
        installed (installed-slots f ds s/am-all 991 mine result)
        e (row installed :edges (get (:pairs result) d))]
    (is (true? (step/comp-live (row w :comps d))))
    (is (true? (engine/fast-ready (:world acc) d)))
    (is (false? (hm3/h3-m (:comps installed) (:tasks installed) (:runs installed) e)))
    (is (false? (hm3/h3 [] installed)))
    (is (true? (hm3/h3 [] (:world acc))))))

(deftest conditional-local-rank-failure-continues-wiring-and-consumes-adoption
  ;; Explicit conditional field instance: a self dependency violates Entry's
  ;; cycle guard, while the general local H3 contracts still apply.
  (let [{:keys [w rid owner leaf] :as f} (fixture/fixture :comp), r (row w :runs rid)
        ds [owner leaf], aid (:next-id w), P (engine/await-pre w r ds s/am-all 992 [owner])
        site (:effect-index r), records [(s/->AdoptBase site owner 11 2)
                                         (s/->AdoptBase site leaf 22 3)
                                         (s/->AdoptBase (inc site) leaf 33 4)]
        P (s/comp-upd P owner #(assoc % :adopt-baselines records
                                      :basis [(s/->Created leaf site)]
                                      :adopt-basis [(s/->Created owner (inc site))]))
        before (row P :comps owner), acc (engine/->AwAcc P nil true)
        first-step (engine/await-step r aid s/am-all 992 acc owner)
        second-step (engine/await-step r aid s/am-all 992 first-step leaf)
        wired (engine/await-wire r aid s/am-all 992 acc ds)]
    (fixture/check-input f)
    (is (true? (engine/await-cycle w r ds)))
    (is (false? (engine/await-ok w r ds s/am-all aid)))
    (is (false? (:ok first-step)))
    (is (false? (:ok second-step)))
    (is (= second-step wired))
    (is (= (+ 2 (:next-id P)) (:next-id (:world second-step))))
    (is (= #{owner leaf} (set (map :deb (:pairs second-step)))))
    (is (= (subvec records 1) (vec (:adopt-baselines (row (:world first-step) :comps owner)))))
    (is (= [(last records)] (vec (:adopt-baselines (row (:world second-step) :comps owner)))))
    (doseq [out [P (:world first-step) (:world second-step)]]
      (check-local-support out r aid)
      (fixture/check-old-obligation f out)
      (doseq [field [:basis :adopt-basis]] (is (= (field before) (field (row out :comps owner))))))
    (doseq [[d eid] [[owner (:next-id P)] [leaf (inc (:next-id P))]]]
      (is (= d (:debtor (row (:world second-step) :edges eid)))))
    (is (false? (rank/inv-rank (:world second-step))) "rank output requires final ok")))

(deftest arbitrary-local-checked-insertion-refusal-and-sticky-false
  (let [{:keys [w rid deferred] :as f} (fixture/fixture :task), r (row w :runs rid)
        a 999999, acc (engine/->AwAcc w nil false), e (engine/await-edge w r a s/am-one 993 deferred)
        out (engine/await-step r a s/am-one 993 acc deferred)
        wire (engine/await-wire r a s/am-one 993 acc [deferred (:leaf f)])]
    (fixture/check-input f)
    (is (false? (edits/edge-ok-in w e)))
    (is (= w (:world out)))
    (is (= [(engine/->DE deferred (:next-id w))] (:pairs out)))
    (is (nil? (row (:world out) :edges (:next-id w))))
    (is (false? (:ok out)))
    (is (false? (:ok wire)))
    (is (= w (:world wire)))
    (is (= 2 (count (:pairs wire))))
    (fixture/check-h3-fields (:world out))
    (fixture/check-h3-fields (:world wire))))

(deftest broad-parked-alive-input-is-distinct-from-entry-and-raw0-refusals
  (let [{:keys [w rid old-run deferred consuming] :as f} (fixture/fixture :task)
        r (row w :runs rid), st (:stamp r), fresh (:next-id w)
        parked (row w :runs old-run), parked-acc (engine/await-acc w parked [deferred] s/am-one 994 [])
        accepted (engine/raw0 w [18 st [deferred] s/am-one 994 fresh []])]
    (fixture/check-input f)
    (is (some #{parked} (:runs w)))
    (is (closed/alive? parked))
    (is (false? (:slice parked)))
    (is (nil? (step/tok-run w (:stamp parked))))
    (is (true? (hm3/h3 [] (:world parked-acc))) "broad alive-member H3 transport has no slice premise")
    (is (true? (:accepted accepted)) "finite full T6 positive regression observation")
    (is (= s/act-parked (:act (row (:world accepted) :runs rid))))
    (is (seq (:members (row (:world accepted) :acts fresh))))
    (is (nil? (step/tok-run w 999999)))
    (is (nil? (step/tok-run (:world accepted) st)))
    (doseq [[world token ds mode] [[w 999999 [deferred] s/am-one]
                                   [(:world accepted) st [deferred] s/am-one]
                                   [w st [deferred] 99] [w st [] s/am-one]
                                   [w st [999999] s/am-one]]]
      (fixture/refused-raw world [18 token ds mode 994 (:next-id world) []]))
    (is (true? (engine/await-ok w r [consuming] s/am-one fresh)))
    (is (true? (engine/await-kind-bad w [consuming])))
    (fixture/refused-raw w [18 st [consuming] s/am-one 994 fresh []])
    (let [w1 (fixture/accepted-step w [35 st])
          w2 (fixture/accepted-step w1 [18 st [deferred] s/am-one 995 (:next-id w1) []])
          w3 (fixture/accepted-step w2 [30 rid])
          w4 (fixture/accepted-step w3 [29 rid]), cleanup (row w4 :runs rid)]
      (is (= s/mode-unwinding (:mode cleanup)))
      (is (:slice cleanup))
      (is (true? (engine/in-cleanup w4 st)))
      (is (false? (engine/run-normal cleanup)))
      (fixture/refused-raw w4 [18 st [deferred] s/am-one 995 (:next-id w4) []]))))

(def generated-contracts
  ;; Independent invariant schemas specify the exported copier dependencies.
  ;; No copied source or registered kernel type is used to construct them.
  (let [families [['g7 [] []] ['aha [] []] ['gd [] []] ['ar [] []]
                  ['hmk '[hxm :- (List Nat)] '[hxm]] ['ekb [] []] ['gl [] []]
                  ['awo '[awc :- Nat awr :- Nat] '[awc awr]] ['ka '[k8a :- Nat] '[k8a]]]
        predicate (fn [p args w] (apply list p (concat args [w])))
        truth (fn [p args w] (list '= (predicate p args w) true))
        preparation
        (into {} (for [[p params args] families]
                   [(symbol (str p "-await-pre"))
                    (list 'forall (into (vec params) '[w :- World r :- RunRow ds :- (List Nat) mode :- Nat k :- Nat mine :- (List Nat)])
                          (apply list '=>
                                 (concat (case p
                                           aha '[(List.Mem r (:runs w)) (= (run-alive r) true)]
                                           gd '[(= (g7 w) true)] [])
                                         [(truth p args 'w) (truth p args '(await-pre w r ds mode k mine))])))]))
        wiring
        (into {} (for [[p params args] families]
                   [(symbol (str p "-await-wire"))
                    (list 'forall (into (vec params) '[r :- RunRow a :- Nat mode :- Nat k :- Nat ds :- (List Nat) acc :- AwAcc])
                          (apply list '=>
                                 (concat (when (= p 'g7) '[(= (awo (:of r) (:id r) (:world acc)) true)])
                                         [(truth p args '(:world acc))
                                          (truth p args '(:world (await-wire r a mode k acc ds)))])))]))]
    (merge preparation wiring
           {'hm3-await-step (:type (first public-contracts))
            'hm3-await-wire (:type (second public-contracts))
            'nat-fold-gx
            '(forall [ex :- Ex f :- (=> World Nat World)
                      hf :- (forall [w :- World x :- Nat]
                              (=> (= (gx ex w) true) (= (gx ex (f w x)) true)))
                      xs :- (List Nat) w :- World]
               (=> (= (gx ex w) true) (= (gx ex (nat-fold f w xs)) true)))
            'gx-demand-reactive
            '(forall [ex :- Ex w :- World d :- Nat]
               (=> (= (gx ex w) true) (= (gx ex (demand-reactive w d)) true)))
            'gx-await-wire
            '(forall [ex :- Ex r :- RunRow a :- Nat mode :- Nat k :- Nat ds :- (List Nat) acc :- AwAcc]
               (=> (= (gx ex (:world acc)) true)
                   (= (gx ex (:world (await-wire r a mode k acc ds))) true)))})))

(deftest exact-safe-exported-generated-dependencies
  (is (= 23 (count generated-contracts)))
  (doseq [[name contract] generated-contracts]
    (when-let [^ConstantInfo d (certification/checked-declaration name)]
      (is (= (closed/type-form (elab/elaborate @a/ansatz-env contract))
             (closed/type-form (.-type d))) (str name " independently specified actual exported type")))))
