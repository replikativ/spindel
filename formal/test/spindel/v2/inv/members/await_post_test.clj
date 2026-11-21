(ns spindel.v2.inv.members.await-post-test
  "Confirmed HM11 literal manifest, committed before proof implementation.
   Plan SHA256 66de8b612a34a69bc9e0b96a0e8c1394034e2bddb6edeb7e7f09543a5ec8b759."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [ansatz.core :as a]
            [ansatz.surface.elaborate :as elab]
            [ansatz.kernel.env :as kernel-env]
            [ansatz.kernel.tc :as tc]
            [spindel.v2.inv.members.await-post :as h11]
            [spindel.v2.inv.members.await-fill :as h10]
            [spindel.v2.inv.members.await-fill-test :as fill]
            [spindel.v2.inv.members.await-prep-test :as fixture]
            [spindel.v2.state :as s]
            [spindel.v2.edits :as edits]
            [spindel.v2.step :as step]
            [spindel.v2.engine :as engine]
            [spindel.v2.rule :as rule]
            [spindel.v2.inv.members.bundle :as hm3]
            [spindel.v2.inv.marks :as hmk]
            [spindel.v2.inv.members.cascade-test :as certification]
            [spindel.v2.inv.members.react-test :as closed])
  (:import [ansatz.kernel ConstantInfo Env Name]
           [java.io PushbackReader]))

(def helper-definitions
  '[
(a/defn current-members-parked [a :- Nat, rid :- Nat, ds :- (List Nat),
                    acc :- AwAcc] World
  (park-if (current-members-fill-prefix a ds acc (nat-distinct ds)) a rid))

(a/defn current-members-final-prefix [a :- Nat, rid :- Nat, ds :- (List Nat),
                         acc :- AwAcc, pre :- (List Nat)] World
  (nat-fold finalize-if-final (current-members-parked a rid ds acc) pre))
])

(def public-contracts
  '[
{:name current-members-park-marks-waiting
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat]
  (=> (current-members-entry xm w r ds mode st fresh)
      (= (marks-waiting (List.nil Nat)
           (current-members-parked (:next-id w) (:id r) ds
             (await-acc w r ds mode k mine))) true)))}

{:name current-members-fin-fold
 :type (forall [xm :- (List Nat), hx :- (List Nat), w :- World,
         ds :- (List Nat)]
  (=> (= (marks-waiting hx w) true)
      (= (current-members xm w) true)
      (And (= (marks-waiting hx (nat-fold finalize-if-final w ds)) true)
           (= (current-members xm (nat-fold finalize-if-final w ds)) true))))}

{:name current-members-final-prefix-invariants
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat)]
  (=> (current-members-entry xm w r ds mode st fresh)
      (= (List.append Nat pre tail) (nat-distinct ds))
      (let [W (current-members-final-prefix (:next-id w) (:id r) ds
                (await-acc w r ds mode k mine) pre)]
        (And (= (marks-waiting (List.nil Nat) W) true)
             (= (current-members xm W) true)))))}

{:name current-members-await-post
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat]
  (=> (current-members-entry xm w r ds mode st fresh)
      (= (current-members xm
           (await-post (:next-id w) (:id r) ds
             (await-acc w r ds mode k mine))) true)))}])

(deftest frozen-hm11-manifest
  (is (= 2 (count helper-definitions)))
  (is (= 4 (count public-contracts)))
  (is (= '[current-members-park-marks-waiting current-members-fin-fold current-members-final-prefix-invariants current-members-await-post]
         (mapv :name public-contracts))))


(defn source-forms []
  (with-open [reader (PushbackReader. (io/reader (io/resource "spindel/v2/inv/members/await_post.clj")))]
    (loop [forms []]
      (let [form (read {:eof ::end} reader)]
        (if (= ::end form) forms (recur (conj forms form)))))))

(def theorems (mapv second (filter #(and (seq? %) (= 'a/theorem (first %))) (source-forms))))
(defn declaration [name] (.lookup ^Env @a/ansatz-env (Name/fromString (str name))))
(defn expanded-independent-contract [contract]
  (list 'let (vec (mapcat (fn [[_ name parameters _ body]] [name (list 'fn parameters body)])
                         helper-definitions)) contract))

(deftest exact-safe-closed-public-contracts
  (is (= 5 (count theorems)))
  (doseq [name theorems]
    (when-let [^ConstantInfo d (certification/checked-declaration name)]
      (is (seq (closed/type-form (.-type d))))))
  (doseq [{:keys [name type]} public-contracts]
    (let [^ConstantInfo d (declaration name), literal (elab/elaborate @a/ansatz-env type)
          expanded (elab/elaborate @a/ansatz-env (expanded-independent-contract type))]
      (is (some? d))
      (is (= (closed/type-form literal) (closed/type-form (.-type d))) (str name " literal"))
      (is (seq (closed/type-form expanded)))
      (is (tc/is-def-eq (tc/mk-tc-state @a/ansatz-env) (.-type d) expanded) (str name " expanded meanings")))))

(deftest exact-safe-closed-helper-meanings
  (let [actual (vec (filter #(and (seq? %) (= 'a/defn (first %))) (source-forms)))]
    (is (= helper-definitions actual))
    (doseq [[_ name parameters result body] helper-definitions]
      (let [^ConstantInfo d (declaration name), signature (elab/elaborate @a/ansatz-env (list 'forall parameters result))
            expected (elab/elaborate @a/ansatz-env (list 'fn parameters body) (.-type d))]
        (is (= :def (kernel-env/ci-tag d)) "helpers are DEFs")
        (is (zero? (.-safety d)))
        (is (= (closed/type-form signature) (closed/type-form (.-type d))))
        (is (seq (closed/type-form (.value d))))
        (is (seq (closed/type-form expected)))
        (is (tc/is-def-eq (tc/mk-tc-state @a/ansatz-env) (.value d) expected))))))

(def helper-equations
  '{current-members-parked.eq_1
    (forall [a :- Nat rid :- Nat ds :- (List Nat) acc :- AwAcc]
      (= (current-members-parked a rid ds acc)
         (park-if (current-members-fill-prefix a ds acc (nat-distinct ds)) a rid)))
    current-members-final-prefix.eq_1
    (forall [a :- Nat rid :- Nat ds :- (List Nat) acc :- AwAcc pre :- (List Nat)]
      (= (current-members-final-prefix a rid ds acc pre)
         (nat-fold finalize-if-final (current-members-parked a rid ds acc) pre)))})

(def dependency-contracts
  '{marks-waiting-act-upd
    (forall [hxm :- (List Nat) w :- World x :- Nat f :- (=> ActRow ActRow)
             hf :- (forall [r :- ActRow] (= (act-id (f r)) (act-id r)))]
      (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (act-upd w x f)) true)))
    marks-waiting-fast-fill
    (forall [hxm :- (List Nat) ps :- (List DE) w :- World d :- Nat]
      (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (fast-fill ps w d)) true)))
    marks-waiting-nat-fold
    (forall [hxm :- (List Nat) f :- (=> World Nat World)
             hf :- (forall [w :- World x :- Nat] (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (f w x)) true)))
             xs :- (List Nat) w :- World]
      (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (nat-fold f w xs)) true)))
    marks-waiting-park-if
    (forall [hxm :- (List Nat) w :- World a :- Nat rid :- Nat]
      (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (park-if w a rid)) true)))
    marks-waiting-finalize-if-final
    (forall [hxm :- (List Nat) w :- World d :- Nat]
      (=> (= (marks-waiting hxm w) true) (= (marks-waiting hxm (finalize-if-final w d)) true)))
    current-members-finalize-if-final
    (forall [xm :- (List Nat) hx :- (List Nat) w :- World d :- Nat]
      (=> (= (marks-waiting hx w) true) (= (current-members xm w) true) (= (current-members xm (finalize-if-final w d)) true)))})

(def generated-contracts (dissoc dependency-contracts 'current-members-finalize-if-final))

(deftest exact-safe-equations-and-existing-dependencies
  (is (= 2 (count helper-equations)))
  (is (= 6 (count dependency-contracts)))
  (doseq [[name expected] (merge helper-equations dependency-contracts)]
    (when-let [^ConstantInfo d (certification/checked-declaration name)]
      (is (= (closed/type-form (elab/elaborate @a/ansatz-env expected))
             (closed/type-form (.-type d))) (str name " independent exact dependency/equation")))))

(defn row [w table id] (fixture/row w table id))
(defn physical-holder? [w eid]
  (boolean (some #(some (fn [m] (= eid (:edge m))) (:members %)) (:acts w))))
(defn final-debtor? [w d]
  (if-let [source (row w :sources d)]
    (or (not (:open source)) (and (= s/sk-deferred (:kind source)) (pos? (:version source))))
    (if-let [task (row w :tasks d)] (not= s/res-none (:tag (:result task))) false)))

(defn final-step-fields
  "Independent physical-membership filter for actual finalize-if-final. Does not use
   finalize-drops/finalize-keeps or H3 freeness as its deletion oracle."
  [f W d xm hx]
  (let [final? (final-debtor? W d)
        doomed (set (for [e (:edges W)
                          :when (and final? (= s/ek-dep (:kind e)) (= s/ph-armed (:phase e))
                                     (= d (:debtor e)) (not (physical-holder? W (:id e))))] (:id e)))
        expected (vec (remove #(contains? doomed (:id %)) (:edges W)))
        after (engine/finalize-if-final W d)]
    (is (= final? (step/deb-final W d)))
    (is (= expected (vec (:edges after))))
    (is (= doomed (set/difference (set (map :id (:edges W))) (set (map :id (:edges after))))))
    (is (= (dissoc W :edges) (dissoc after :edges)) "layer-1 finalization has no final computation worklist")
    (is (every? #(not (:marked %)) (filter #(contains? doomed (:id %)) (:edges W))))
    (when-not final? (is (= W after) "ready and final are different"))
    (is (true? (hmk/marks-waiting hx W)))
    (is (true? (hm3/current-members xm W)))
    (is (true? (closed/member-fields? xm W)))
    (is (true? (hmk/marks-waiting hx after)))
    (is (true? (hm3/current-members xm after)))
    (is (true? (closed/member-fields? xm after)))
    (fill/check-old-unexempt f after xm)
    after))

(defn await-final-prefixes [f ds mode k mine xm]
  (let [{:keys [w rid]} f, a (:next-id w), r (row w :runs rid)
        filled (fill/checkpoint f ds mode k mine xm), acc (:acc filled)
        parked (:parked filled), debtors (vec (distinct ds))]
    (is (= parked (h11/current-members-parked a rid ds acc)))
    (is (true? (hmk/marks-waiting [] parked)))
    (is (true? (hm3/current-members xm parked)))
    (loop [i 0, W parked]
      (let [pre (subvec debtors 0 i), tail (subvec debtors i)]
        (is (= debtors (vec (concat pre tail))))
        (is (= W (h11/current-members-final-prefix a rid ds acc pre)))
        (is (true? (hmk/marks-waiting [] W)))
        (is (true? (hm3/current-members xm W)))
        (is (true? (closed/member-fields? xm W)))
        (fill/check-old-unexempt f W xm)
        (if-let [d (first tail)]
          (recur (inc i) (final-step-fields f W d xm []))
          (do (is (= W (engine/await-post a rid ds acc)))
              (is (= W (h11/current-members-final-prefix a rid ds acc debtors)))
              (is (true? (hm3/current-members xm W)))
              (assoc filled :final W)))))))

(deftest accepted-full-await-post-prefixes-and-final-debtor-kinds
  (doseq [kind [:comp :task]]
    (let [{:keys [ready-comp pending-task completed-task delivered closed-source signal cell
                  pending-resource ready-resource fresh top deferred] :as f} (fill/comprehensive-fixture kind)
          ds [ready-comp ready-comp pending-task completed-task delivered closed-source signal cell
              pending-resource ready-resource fresh top deferred]
          out (await-final-prefixes f ds s/am-all 3001 [fresh top fresh] [])
          parked (:parked out)]
      (doseq [d [completed-task delivered closed-source]]
        (is (true? (final-debtor? parked d)))
        (when (= kind :comp)
          (is (nil? (row parked :edges (get (:pairs out) d)))
              "this removal happened in fast-fill delivery, before finalization")))
      (doseq [d [ready-comp pending-task signal cell pending-resource ready-resource fresh top deferred]]
        (is (false? (final-debtor? parked d))))
      (is (true? (engine/fast-ready parked ready-comp)))
      (is (= parked (engine/finalize-if-final parked ready-comp)))
      (is (= parked (:final out)) "accepted case needs no remaining final-debtor edge removal"))))

(deftest accepted-all-modes-and-early-resume-later-final-invalidation
  (doseq [kind [:comp :task]]
    (let [{:keys [signal delivered ready-comp] :as f} (fill/comprehensive-fixture kind)]
      (doseq [[ds mode] [[[ready-comp] s/am-one] [[ready-comp delivered ready-comp] s/am-all]
                         [[signal delivered ready-comp signal] s/am-any]]]
        (let [out (await-final-prefixes f ds mode 3002 [ready-comp] [])]
          (is (nil? (row (:final out) :acts (:next-id (:w f)))))
          (when (and (= kind :comp) (= mode s/am-any))
            ;; Z#61 / engine `await-group!`: after the winner the final debtor's edge fills
            ;; nothing; T10 removes it at once, and the run stays current
            (let [eid (get (:pairs out) delivered)]
              (is (= [s/ek-dep s/ph-armed delivered] ((juxt :kind :phase :debtor) (row (:parked out) :edges eid))))
              (is (nil? (row (:final out) :edges eid)) "T10 removes the unfilled edge on the final debtor")
              (is (true? (fill/current-run? (:final out) (:rid f)))))))))))

(deftest accepted-overlapping-xm-and-token-valid-stale-final-prefixes
  (let [{:keys [w rid signal delivered deferred] :as f} (fill/comprehensive-fixture :comp)
        ds [signal signal delivered deferred], acc (engine/await-acc w (row w :runs rid) ds s/am-all 3003 [signal])
        overlap (engine/pair-edge signal (:pairs acc)), out (await-final-prefixes f ds s/am-all 3003 [signal] [overlap])]
    (is (pos? overlap))
    (is (some? (row (:final out) :acts (:next-id w))))
    (fill/check-old-unexempt f (:final out) [overlap])
    (let [w (fixture/accepted-step w [3 rid signal 3004 (:next-id w)])
          w (fixture/accepted-step w [2 signal 55]), r (row w :runs rid)
          out (await-final-prefixes (assoc f :w w) [delivered signal deferred] s/am-all 3005 [signal] [])]
      (is (= [r] (step/tok-run w (:stamp r))))
      (is (false? (fill/current-run? w rid)))
      (is (empty? (:deliveries out)))
      (is (some? (row (:final out) :acts (:next-id w)))))))

(deftest generic-pre-t10-removes-only-unheld-armed-target-dependencies
  ;; Accepted finite construction ends before the source-upd below. That internal
  ;; pre-T10 world is a generic HMK/H3 witness, not an accepted world-step/Entry trace.
  (let [{:keys [w rid leaf] :as f} (fixture/fixture :comp)
        [w other] (fixture/source w s/sk-signal 44), removable (:next-id w)
        w (fixture/accepted-step w [3 rid leaf 3010 removable]), fired (:next-id w)
        w (fixture/accepted-step w [3 rid leaf 3011 fired]), wrong (:next-id w)
        w (fixture/accepted-step w [3 rid other 3012 wrong]), observer (:next-id w)
        w (fixture/accepted-step w [4 leaf 3013 observer])
        w (fixture/accepted-step w [6 fired s/res-ok 30])
        generic (s/source-upd w leaf rule/source-close-row), f (assoc f :w w)
        xm [fired], hx [(:fresh f)], after (final-step-fields f generic leaf xm hx)]
    (is (= [s/ek-dep s/ph-armed leaf] ((juxt :kind :phase :debtor) (row generic :edges removable))))
    (is (false? (physical-holder? generic removable)))
    (is (nil? (row after :edges removable)) "actual finalization-only removal, not a prior fast-fill")
    (doseq [eid [fired wrong observer (:old-edge f)]]
      (is (= (row generic :edges eid) (row after :edges eid))))
    (is (= s/ph-fired (:phase (row generic :edges fired))))
    (is (= other (:debtor (row generic :edges wrong))))
    (is (= s/ek-observe (:kind (row generic :edges observer))))
    (is (= generic (edits/nat-fold engine/finalize-if-final generic [])))
    (is (= after (edits/nat-fold engine/finalize-if-final generic [leaf leaf])))
    (doseq [W [generic after]]
      (is (true? (hmk/marks-waiting hx W))) (is (true? (hm3/current-members xm W))))))

(deftest generic-pre-t10-retains-physical-held-stale-and-exempt-edges
  ;; The pending holder itself comes from an accepted await. Only source-close-row
  ;; (and, for the stale case, comp-inc-epoch) is internal setup for the generic fold.
  (let [{:keys [w rid owner] :as f} (fixture/fixture :comp)
        [w d] (fixture/source w s/sk-deferred 0), aid (:next-id w)
        w (fixture/accepted-step w [18 rid [d] s/am-one 3020 aid []]), eid (inc aid)
        generic (s/source-upd w d rule/source-close-row)
        stale (s/comp-upd generic owner step/comp-inc-epoch), f (assoc f :w w)]
    (is (= [(s/->Member eid 0)] (:members (row generic :acts aid))))
    (is (true? (physical-holder? generic eid)))
    (is (true? (fill/current-run? generic rid)))
    (doseq [[W xm] [[generic []] [generic [eid]] [stale []] [stale [eid]]]]
      (is (true? (physical-holder? W eid)))
      (is (= (boolean (or (not (fill/current-run? W rid)) (some #{eid} xm)))
             (hm3/current-members-free xm W eid)) "currency/exemption changes freeness, while physical membership remains")
      (is (= s/ph-armed (:phase (row W :edges eid))))
      (is (true? (final-debtor? W d)))
      (let [after (final-step-fields f W d xm [(:fresh f)])]
        (is (= W after))
        (is (= (row W :edges eid) (row after :edges eid)))
        (is (= (row W :acts aid) (row after :acts aid)))
        (is (= after (edits/nat-fold engine/finalize-if-final W [d d])))))
    (is (false? (fill/current-run? stale rid)))))
