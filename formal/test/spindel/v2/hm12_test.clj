(ns spindel.v2.hm12-test
  "Confirmed HM12 literal manifest committed before implementation.
   Plan SHA256 4f22472d2b4e647bbafaee8858d3cb34d34b9a866818e2fb2acc53798851bf09."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io :as io]
            [ansatz.core :as a]
            [ansatz.surface.elaborate :as elab]
            [ansatz.kernel.env :as kernel-env]
            [ansatz.kernel.tc :as tc]
            [spindel.v2.hm12]
            [spindel.v2.hm11-test :as finalizing]
            [spindel.v2.hm10-test :as fill]
            [spindel.v2.hm9-test :as wiring]
            [spindel.v2.hm8-test :as fixture]
            [spindel.v2.hm6-base :as base]
            [spindel.v2.hm3 :as hm3]
            [spindel.v2.state :as s]
            [spindel.v2.step :as step]
            [spindel.v2.engine :as engine]
            [spindel.v2.hm6-test :as certification]
            [spindel.v2.hm7-test :as closed])
  (:import [ansatz.kernel ConstantInfo Env Name]
           [java.io PushbackReader]))

(def helper-definitions '[])

(def public-contracts
  '[
{:name h12-await-raw-h3
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (h3 xm (await-raw w r ds mode k mine)) true)))}

{:name h12-t6-accepted
 :type (forall [xm :- (List Nat), w :- World, r :- RunRow,
         st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat,
         fresh :- Nat, mine :- (List Nat)]
  (=> (= (p3la w) true)
      (= (h3 xm w) true)
      (= (tok-run w st) (Option.some RunRow r))
      (= (:accepted (t6-await w st ds mode k fresh mine)) true)
      (And (= (t6-await w st ds mode k fresh mine)
              (accept (await-raw w r ds mode k mine)))
           (= (h3 xm (:world (t6-await w st ds mode k fresh mine))) true))))}

{:name h12-t6-outcome
 :type (forall [xm :- (List Nat), w :- World, st :- Nat,
         ds :- (List Nat), mode :- Nat, k :- Nat,
         fresh :- Nat, mine :- (List Nat)]
  (=> (= (p3la w) true)
      (= (h3 xm w) true)
      (And (= (h3 xm (:world (t6-await w st ds mode k fresh mine))) true)
           (=> (= (:accepted (t6-await w st ds mode k fresh mine)) false)
               (= (:world (t6-await w st ds mode k fresh mine)) w)))))}

{:name h12-raw0-await-outcome
 :type (forall [xm :- (List Nat), w :- World, st :- Nat,
         ds :- (List Nat), mode :- Nat, k :- Nat,
         fresh :- Nat, mine :- (List Nat)]
  (=> (= (p3la w) true)
      (= (h3 xm w) true)
      (And (= (h3 xm
                (:world (raw0 w (Item.await st ds mode k fresh mine)))) true)
           (=> (= (:accepted (raw0 w (Item.await st ds mode k fresh mine))) false)
               (= (:world (raw0 w (Item.await st ds mode k fresh mine))) w)))))}])

(deftest frozen-hm12-manifest
  (is (empty? helper-definitions))
  (is (= 4 (count public-contracts)))
  (is (= '[h12-await-raw-h3 h12-t6-accepted h12-t6-outcome h12-raw0-await-outcome]
         (mapv :name public-contracts))))


(defn forms-at [path]
  (with-open [reader (PushbackReader. (io/reader (io/resource path)))]
    (loop [forms []]
      (let [form (read {:eof ::end} reader)]
        (if (= ::end form) forms (recur (conj forms form)))))))
(defn source-forms [] (forms-at "spindel/v2/hm12.clj"))
(def theorems (mapv second (filter #(and (seq? %) (= 'a/theorem (first %))) (source-forms))))
(defn declaration [name] (.lookup ^Env @a/ansatz-env (Name/fromString (str name))))

(def expected-wrappers
  '{h9-entry
    (a/defn h9-entry [xm :- (List Nat) w :- World r :- RunRow ds :- (List Nat)
                     mode :- Nat st :- Nat fresh :- Nat] Prop
      (And (= (p3la w) true)
        (And (= (h3 xm w) true)
          (And (= (tok-run w st) (Option.some RunRow r))
               (= (await-ok w r ds mode fresh) true)))))
    await-raw
    (a/defn await-raw [w :- World r :- RunRow ds :- (List Nat) mode :- Nat k :- Nat mine :- (List Nat)] World
      (await-post (:next-id w) (:id r) ds (await-acc w r ds mode k mine)))})

(defn expanded-independent-contract [contract]
  (list 'let
        (vec (mapcat (fn [name]
                       (let [[_ _ parameters _ body] (get expected-wrappers name)]
                         [name (list 'fn parameters body)])) '[h9-entry await-raw]))
        contract))

(def dependency-contracts
  '{h11-await-post-h3
    (forall [xm :- (List Nat) w :- World r :- RunRow ds :- (List Nat) mode :- Nat k :- Nat
             mine :- (List Nat) st :- Nat fresh :- Nat]
      (=> (h9-entry xm w r ds mode st fresh)
          (= (h3 xm (await-post (:next-id w) (:id r) ds (await-acc w r ds mode k mine))) true)))
    t6-refuse
    (forall [w :- World st :- Nat ds :- (List Nat) mode :- Nat k :- Nat fresh :- Nat mine :- (List Nat)]
      (=> (= (:accepted (t6-await w st ds mode k fresh mine)) false)
          (= (:world (t6-await w st ds mode k fresh mine)) w)))
    raw0-refuse
    (forall [w :- World it :- Item]
      (=> (= (:accepted (raw0 w it)) false) (= (:world (raw0 w it)) w)))})

(def item-await-signature
  '(forall [st :- Nat ds :- (List Nat) mode :- Nat k :- Nat fresh :- Nat mine :- (List Nat)] Item))
(def expected-t6
  '(a/defn t6-await [w :- World st :- Nat ds :- (List Nat) mode :- Nat k :- Nat fresh :- Nat mine :- (List Nat)] Outcome
     (match (tok-run w st)
       [none (refuse w)]
       [(some r) (if (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine)))
                   (accept (await-raw w r ds mode k mine)) (refuse w))])))
(def expected-raw0-await-branch
  '[(await st ds m k fresh mine)
    (if (await-kind-bad w ds) (refuse w) (t6-await w st ds m k fresh mine))])

(deftest actual-safe-closed-exact-endpoints-and-dependencies
  (is (= 4 (count theorems)))
  (is (= (set (map :name public-contracts)) (set theorems)))
  (is (empty? (filter #(and (seq? %) (= 'a/defn (first %))) (source-forms))))
  (doseq [name (concat theorems (keys dependency-contracts))]
    (when-let [^ConstantInfo d (certification/checked-declaration name)]
      (is (seq (closed/type-form (.-type d))))))
  (doseq [{:keys [name type]} public-contracts]
    (let [^ConstantInfo d (declaration name), literal (elab/elaborate @a/ansatz-env type)
          expanded (elab/elaborate @a/ansatz-env (expanded-independent-contract type))]
      (is (= (closed/type-form literal) (closed/type-form (.-type d))) (str name " literal"))
      (is (seq (closed/type-form expanded)))
      (is (tc/is-def-eq (tc/mk-tc-state @a/ansatz-env) (.-type d) expanded) (str name " expanded wrappers"))))
  (doseq [[name expected] dependency-contracts]
    (is (= (closed/type-form (elab/elaborate @a/ansatz-env expected))
           (closed/type-form (.-type ^ConstantInfo (declaration name)))) (str name " exact actual dependency"))))

(deftest actual-constructor-wrapper-values-and-branch-identities
  (let [engine-forms (into {} (map (juxt second identity) (filter seq? (forms-at "spindel/v2/engine.clj"))))
        hm9-forms (into {} (map (juxt second identity) (filter seq? (forms-at "spindel/v2/hm9.clj"))))
        step-forms (forms-at "spindel/v2/step.clj"), item (first (filter #(= '(a/inductive Item) (take 2 %)) step-forms))
        constructor (first (filter #(and (seq? %) (= 'await (first %))) (drop 3 item)))
        ^ConstantInfo d (declaration 'Item.await)]
    (is (= '(await [st Nat] [ds (List Nat)] [mode Nat] [k Nat] [fresh Nat] [mine (List Nat)]) constructor))
    (is (= :ctor (kernel-env/ci-tag d)))
    (is (zero? (.-safety d)))
    (is (= (closed/type-form (elab/elaborate @a/ansatz-env item-await-signature))
           (closed/type-form (.-type d))))
    (doseq [[name [_ _ parameters result body :as expected]] expected-wrappers]
      (let [actual-source (get (if (= name 'h9-entry) hm9-forms engine-forms) name)
            ^ConstantInfo d (declaration name)
            expected-value (elab/elaborate @a/ansatz-env (list 'fn parameters body) (.-type d))]
        (is (= expected actual-source))
        (is (= :def (kernel-env/ci-tag d)))
        (is (zero? (.-safety d)))
        (is (seq (closed/type-form (.value d))))
        (is (= (closed/type-form (elab/elaborate @a/ansatz-env (list 'forall parameters result)))
               (closed/type-form (.-type d))))
        (is (tc/is-def-eq (tc/mk-tc-state @a/ansatz-env) (.value d) expected-value))))
    (is (= expected-t6 (get engine-forms 't6-await)))
    (let [raw0-body (nth (get engine-forms 'raw0) 4), branch (first (filter #(= 'await (ffirst %)) (drop 2 raw0-body)))]
      (is (= expected-raw0-await-branch branch)))))

(defn row [w table id] (fixture/row w table id))
(defn check-input [f xm]
  (is (true? (base/p3la (:w f))))
  (is (true? (hm3/h3 xm (:w f))))
  (is (true? (closed/member-fields? xm (:w f)))))

(defn positive-outcomes [f ds mode k mine xm]
  (let [{:keys [w rid]} f, r (row w :runs rid), st (:stamp r), fresh (:next-id w)
        staged (finalizing/await-final-prefixes f ds mode k mine xm)
        acc (engine/await-acc w r ds mode k mine), raw (engine/await-raw w r ds mode k mine)
        direct (engine/t6-await w st ds mode k fresh mine), outer (engine/raw0 w [18 st ds mode k fresh mine])]
    (check-input f xm)
    (is (= [r] (step/tok-run w st)))
    (is (true? (engine/await-ok w r ds mode fresh)))
    (is (true? (:ok acc)))
    (is (= (:final staged) raw))
    (is (= (step/->Outcome raw true) direct))
    (is (false? (engine/await-kind-bad w ds)))
    (is (= direct outer))
    (is (true? (hm3/h3 xm (:world direct))))
    (is (true? (closed/member-fields? xm (:world direct))))
    (fill/check-old-unexempt f (:world direct) xm)
    {:staged staged :acc acc :raw raw :direct direct :outer outer}))

(defn refused-outcomes [w st ds mode k fresh mine xm]
  (let [direct (engine/t6-await w st ds mode k fresh mine), outer (engine/raw0 w [18 st ds mode k fresh mine])]
    (is (true? (base/p3la w)))
    (is (true? (hm3/h3 xm w)))
    (doseq [[label out] [[:direct direct] [:raw0 outer]]]
      (is (false? (:accepted out)) (str label " actual refusal"))
      (is (= w (:world out)) (str label " ENTIRE original World, not speculative accumulator"))
      (is (= (step/->Outcome w false) out))
      (is (true? (hm3/h3 xm (:world out)))))))

(deftest accepted-direct-and-raw0-outcomes-across-actual-modes-and-kinds
  (doseq [kind [:comp :task]]
    (let [{:keys [ready-comp pending-task completed-task delivered closed-source signal cell
                  pending-resource ready-resource fresh top deferred] :as f} (fill/comprehensive-fixture kind)]
      (doseq [[ds mode] [[[ready-comp] s/am-one]
                         [[ready-comp ready-comp pending-task completed-task delivered closed-source signal cell
                           pending-resource ready-resource fresh top deferred] s/am-all]
                         [[signal delivered ready-comp top pending-task signal] s/am-any]]]
        (let [out (positive-outcomes f ds mode 4001 [pending-task fresh pending-task] [])]
          (is (true? (:accepted (:direct out))))
          (is (= (:direct out) (:outer out)))
          (when (= mode s/am-any)
            (is (nil? (row (:raw out) :acts (:next-id (:w f)))))
            (when (= kind :comp)
              (is (false? (fill/current-run? (:raw out) (:rid f)))))))))))

(deftest accepted-reused-edges-duplicates-and-overlapping-exemptions
  (let [{:keys [w reused-source second-source reused-edge fresh deferred] :as f} (wiring/reuse-fixture)
        ds [reused-source second-source reused-source fresh deferred]
        out (positive-outcomes f ds s/am-all 4002 [fresh reused-source fresh] [reused-edge])
        pairs (get-in out [:staged :pairs])]
    (is (= reused-edge (get pairs reused-source)))
    (is (= (count (distinct ds)) (count pairs)))
    (is (= 2 (:remaining (row (:raw out) :acts (:next-id w))))
        "fresh computation and deferred both remain pending")
    (fill/check-old-unexempt f (:raw out) [reused-edge])))

(deftest token-valid-noncurrent-input-is-inspected-independently
  (let [{:keys [w rid signal ready-resource delivered pending-task] :as f} (fill/comprehensive-fixture :comp)
        w (fixture/accepted-step w [3 rid signal 4003 (:next-id w)])
        w (fixture/accepted-step w [2 signal 56]), r (row w :runs rid)
        out (positive-outcomes (assoc f :w w) [ready-resource delivered pending-task] s/am-all 4004 [signal] [])]
    (is (false? (fill/current-run? w rid)))
    (is (= [r] (step/tok-run w (:stamp r))))
    (is (true? (:accepted (:direct out))) "currency alone is not a T6 refusal guard")
    (is (not= w (:world (:direct out))))
    (is (empty? (get-in out [:staged :deliveries])))))

(deftest actual-refusals-preserve-the-entire-original-world
  (doseq [kind [:comp :task]]
    (let [{:keys [w rid deferred leaf] :as f} (fixture/fixture kind), r (row w :runs rid), st (:stamp r), fresh (:next-id w)]
      (check-input f [])
      (doseq [[token ds mode allocation] [[999999 [deferred] s/am-one fresh]
                                          [st [deferred] s/am-one (inc fresh)]
                                          [st [deferred] 99 fresh]
                                          [st [deferred leaf] s/am-one fresh]
                                          [st [] s/am-all fresh]
                                          [st [999999] s/am-one fresh]]]
        (refused-outcomes w token ds mode 4005 allocation [leaf] []))
      (let [after (fixture/accepted-step w [18 st [deferred] s/am-one 4006 fresh []])]
        (is (nil? (step/tok-run after st)) "genuine previous await invalidates slice token")
        (refused-outcomes after st [deferred] s/am-one 4007 (:next-id after) [] [])))))

(deftest actual-cleanup-token-is-valid-but-run-normal-refuses-await
  (let [{:keys [w rid deferred] :as f} (fixture/fixture :task), st (:stamp (row w :runs rid))
        w1 (fixture/accepted-step w [35 st])
        w2 (fixture/accepted-step w1 [18 st [deferred] s/am-one 4008 (:next-id w1) []])
        w3 (fixture/accepted-step w2 [30 rid])
        w4 (fixture/accepted-step w3 [29 rid]), cleanup (row w4 :runs rid)]
    (is (= s/mode-unwinding (:mode cleanup)))
    (is (true? (:slice cleanup)))
    (is (= [cleanup] (step/tok-run w4 st)))
    (is (false? (engine/run-normal cleanup)))
    (is (false? (engine/await-ok w4 cleanup [deferred] s/am-one (:next-id w4))))
    (refused-outcomes w4 st [deferred] s/am-one 4009 (:next-id w4) [] [])
    (fill/check-old-unexempt f w4 [])))

(deftest outer-d0-consuming-refusal-is-distinct-from-direct-t6
  (doseq [kind [:comp :task]]
    (let [{:keys [w rid deferred consuming] :as f} (fixture/fixture kind)
          [w semaphore] (fixture/source w s/sk-semaphore 0), f (assoc f :w w)
          r (row w :runs rid), st (:stamp r), fresh (:next-id w)]
      (doseq [d [consuming semaphore], mode [s/am-one s/am-all s/am-any]]
        (let [ds (if (= mode s/am-one) [d] [d deferred d]), mine [d d]
              acc (engine/await-acc w r ds mode 4010 mine)
              direct (engine/t6-await w st ds mode 4010 fresh mine)
              outer (engine/raw0 w [18 st ds mode 4010 fresh mine])]
          (check-input f [])
          (is (= [r] (step/tok-run w st)))
          (is (true? (engine/await-ok w r ds mode fresh)))
          (is (true? (:ok acc)))
          (is (true? (engine/await-kind-bad w ds)))
          (is (true? (:accepted direct)) "inspect direct T6 independently of the outer guard")
          (is (= (step/->Outcome (engine/await-raw w r ds mode 4010 mine) true) direct))
          (is (true? (hm3/h3 [] (:world direct))))
          (is (= (:sources w) (:sources (:world direct))) "await does not consume mailbox/semaphore")
          (is (= (step/->Outcome w false) outer))
          (is (= w (:world outer)) "whole raw0 refusal world, including allocator/tentative rows")
          (fill/check-old-unexempt f (:world direct) []))))))

(deftest actual-cycle-guard-discards-real-speculative-wiring
  ;; This is an actual refused input with await-ok=false, NOT an Entry witness
  ;; whose only failed condition is accumulator ok. No false-ok Entry is invented.
  (let [{:keys [w rid owner leaf] :as f} (fixture/fixture :comp), r (row w :runs rid), ds [owner leaf]
        acc (engine/await-acc w r ds s/am-all 4011 [leaf])]
    (check-input f [])
    (is (= [r] (step/tok-run w (:stamp r))))
    (is (true? (engine/await-cycle w r ds)))
    (is (false? (engine/await-ok w r ds s/am-all (:next-id w))))
    (is (false? (:ok acc)))
    (is (not= w (:world acc)))
    (is (> (:next-id (:world acc)) (:next-id w)))
    (is (= #{owner leaf} (set (map :deb (:pairs acc)))) "wiring continues after the failed raise")
    (refused-outcomes w (:stamp r) ds s/am-all 4011 (:next-id w) [leaf] [])))
