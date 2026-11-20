(ns spindel.v2.pres.tree-test
  "The generic tree (spindel.v2.pres.tree): every lemma of the step's closure that calls others has
  its shared generic lemma; a part gets its own (pres-x@part) only on its context paths; a gate gives
  a part's continuations its fact; raw0 is cut by item; the parts converted to the tree (gl, g9, g8) have no copier overrides
  or patches left."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.inv.copier :as c]
            [spindel.v2.inv.i10-task]
            [spindel.v2.inv.i9-res]
            [spindel.v2.inv.i8 :as i8]
            [spindel.v2.inv.idle :as idle]
            [spindel.v2.inv.comp-facts :as cf]
            [spindel.v2.inv.marks :as mk]
            [spindel.v2.inv.marks-step]
            [spindel.v2.inv.tomb :as tomb]
            [spindel.v2.inv.acyclic :as acy]
            [spindel.v2.inv.i1-scopes :as i1s]
            [spindel.v2.inv.i11 :as i11]
            [spindel.v2.inv.base :as base]
            [spindel.v2.inv.i10 :as i10]
            [spindel.v2.inv.i5 :as i5]
            [spindel.v2.inv.i1-owners :as i1o]
            [spindel.v2.inv.i1-runs :as i1r]
            [spindel.v2.completion.open-scopes :as os]
            [spindel.v2.inv.i14 :as i14]
            [spindel.v2.progress.measures :as ms]
            [spindel.v2.pres.tree :as tree]))

(defn- declared? [s] (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str s)))))

(deftest every-node-has-its-generic-lemma
  (is (< 150 (count (:nodes @tree/tree))))
  (doseq [x (:nodes @tree/tree)] (is (declared? (tree/pres-name x)) (str x))))

(deftest part-lemmas-only-on-context-paths
  ;; gl takes T12's guard and passes it to complete-raw; g9 takes T17's and passes it to arm-park
  (is (tree/variant? c/GL 't12-inv))
  (is (declared? (tree/pres-name c/GL 't12-inv)))   ; pres-t12@gl
  (is (not (tree/variant? c/GL 't17-inv)))
  (is (tree/variant? c/G9 't17-inv))
  (is (not (tree/variant? c/G9 't12-inv)))
  (is (not (tree/variant? c/G9 'inv-dispatch-raw)))
  (is (= 10 (count (filter #(and (tree/variant? (if (= 'gl (first %)) c/GL c/G9) (second %)))
                           (for [p '[gl g9] x (:nodes @tree/tree)] [p x]))))))

(deftest raw0-is-cut-by-item
  ;; one lemma per item, each checked for inv-sample; raw0-inv dispatches to them, and a part that
  ;; passes into one transition gets that branch's lemma, not the dispatcher's
  (is (= 49 (count (filter #(re-matches #"raw0-.+-inv" (name %)) (:nodes @tree/tree)))))
  (is (declared? 'raw0-complete-inv))
  (doseq [B [c/GL c/G9]] (is (not (tree/variant? B 'raw0-inv))))
  (is (tree/variant? c/GL 'raw0-complete-inv))
  (is (tree/variant? c/G9 'raw0-arm-inv))
  (is (not (tree/variant? c/G9 'raw0-complete-inv))))

(deftest a-gate-gives-the-continuation-its-fact
  ;; a part taking C0's gate: raw0's continuations receive root-ok-if (checked for any Q); only the
  ;; branches of raw0 that call the gate get the part's lemma, not the dispatcher
  (let [B (c/mk-bundle 'tgate [] "tgate-" {})]
    (tree/part! B :gates '{c0-gate-inv hc0})
    (is (= '#{c0-gate-inv raw0-append-inv raw0-create-link-inv raw0-create-link-top-inv
              raw0-create-source-inv raw0-create-source-top-inv raw0-link-realize-inv}
           (set (filter #(tree/variant? B %) (:nodes @tree/tree)))))
    (doseq [x '[c0-gate-inv raw0-create-source-inv]]
      (when-not (declared? (tree/pres-name B x)) (@#'tree/ev (tree/pres-form B x)))
      (is (declared? (tree/pres-name B x)) (str x)))
    (swap! tree/parts dissoc 'tgate)))

(deftest gl-is-not-copied
  (is (empty? @(:overrides c/GL)))
  (is (empty? @(:patches c/GL)))
  (is (= '{inv-cancel-run-local gl-cancel-run-local-o, inv-complete-raw gl-complete-raw-o,
           inv-retire-local gl-retire-local-o, inv-spawn-rows gl-spawn-rows-o,
           inv-start-raw gl-start-raw, inv-new-run-of gl-new-run-of}
         (get-in @tree/parts ['gl :over]))))

(deftest g9-is-not-copied
  (is (empty? @(:overrides c/G9)))
  (is (empty? @(:patches c/G9)))
  (is (= '{inv-cancel-run-local g9-cancel-run-local, inv-ack-raw g9-ack-raw-o, inv-arm-park g9-arm-park}
         (get-in @tree/parts ['g9 :over]))))

(deftest g8-is-not-copied
  (is (empty? @(:overrides i8/G8)))
  (is (empty? @(:patches i8/G8)))
  ;; the companion ga reaches the cascades from raw (raw -> raw0g -> raw0 -> the transitions)
  (doseq [x '[raw-inv raw0g-inv raw0-inv t15-full-inv inv-complete-raw inv-cancel-pred]]
    (is (tree/variant? i8/G8 x) (str x)))
  (is (not (tree/variant? i8/G8 'inv-job-apply)))
  ;; raw0, raw0g, T14, ... only forward ga: inferred, not declared
  (is (not (contains? (:own (get @tree/parts 'g8)) 'raw0-inv)))
  (is (= '[(= (ga w) true)] (vec (take-nth 2 (rest (get (tree/table-own i8/G8) 'raw0-inv)))))))

(deftest g7-is-not-copied
  ;; g7 and its companions awo (awc awr) and kdb (kc0 kl0 kd0): parameterised parts, Q := (B p)
  (doseq [B [idle/G7 idle/AWO idle/KDB]]
    (is (empty? @(:overrides B)) (str (:pred B)))
    (is (empty? @(:patches B)) (str (:pred B))))
  ;; a computation edit is one site per row function, generic in its arguments
  (is (some #{'(comp-start-row rid)} (tree/site-keys 'inv-comp-upd)))
  (is (contains? (get-in @tree/parts ['awo :sites]) '[inv-comp-upd (comp-cut-row h k bs)]))
  ;; T6, T-take, T17, T11, schedule, finalize: plumbing in the table, not g7's own proofs
  (doseq [x '[t6-inv t-take-inv t17-inv t11-inv sched-inv t-finalize-inv inv-take-park inv-arm-park]]
    (is (tree/variant? idle/G7 x) (str x))))

(deftest gd-is-not-copied
  (doseq [B [cf/GD cf/HKW]]
    (is (empty? @(:overrides B)) (str (:pred B)))
    (is (empty? @(:patches B)) (str (:pred B))))
  ;; g7 and g10r from the step's input reach T6, T22, T8 and T12 through raw: declared at raw, raw0g,
  ;; raw0, inferred at raw0's branches
  (is (= '[(= (g7 w) true) (= (g10r w) true)] (vec (take-nth 2 (rest (get (tree/table-own cf/GD) 'raw0-inv))))))
  (doseq [x '[raw0-await-inv raw0-host-await-inv raw0-complete-inv raw0-observe-inv t6-inv t22-inv]]
    (is (tree/variant? cf/GD x) (str x))))

(deftest hmk-is-not-copied
  (doseq [B [mk/HMK mk/HSW]]
    (is (empty? @(:overrides B)) (str (:pred B)))
    (is (empty? @(:patches B)) (str (:pred B))))
  ;; "not a computation id": the source and link chain takes it as a fact, from the transitions
  (doseq [x '[t-close-inv inv-close-raw inv-close-source inv-close-source0 t-append-inv inv-append-raw
              t-link-realize-inv link-realize-raw-inv inv-realize-link inv-deliver-res inv-resume inv-fill-slot]]
    (is (tree/variant? mk/HMK x) (str x))))

(deftest scope-and-tomb-parts-are-not-copied
  (doseq [B [tomb/GY acy/GCY i1s/G1 i11/GW]]
    (is (empty? @(:overrides B)) (str (:pred B)))
    (is (empty? @(:patches B)) (str (:pred B))))
  ;; gy takes g7 from the step's input at T7 and T6; g1 and gcy take "the parent is a scope" where a
  ;; run joins a scope
  (is (tree/variant? tomb/GY 'raw0-track-inv))
  (doseq [x '[t7-inv t6-inv]] (is (contains? (get-in @tree/parts ['gy :ctx]) x) (str x)))
  (doseq [p '[g1 gcy]] (is (contains? (get-in @tree/parts [p :ctx]) 'inv-add-run-scope) (str p))))

(deftest base-parts-are-not-copied
  (doseq [B [base/MDB base/ESB base/NA base/AHA base/SVB]]
    (is (empty? @(:overrides B)) (str (:pred B)))
    (is (empty? @(:patches B)) (str (:pred B))))
  ;; an activation edit and a cleanup edit are sites per row function (na's and aha's extra argument
  ;; is rfl only at a concrete row function; esb proves cleanup-drop by its own lemma)
  (is (seq (tree/site-keys 'inv-act-upd)))
  (is (some #(and (seq? %) (= 'cleanup-drop (first %))) (tree/site-keys 'inv-cleanup-upd)))
  (is (contains? (get-in @tree/parts ['esb :sites]) ['inv-cleanup-upd (first (tree/site-keys 'inv-cleanup-upd))]))
  ;; esb takes "the computation exists" at T5's start and T11's dispatch, "the run is a row" at T14
  (doseq [x '[t5-inv t11-inv inv-job-apply]] (is (tree/variant? base/ESB x) (str x)))
  ;; aha takes ga from the step's input down to T12, and "the run is an alive row" at the parks; svb
  ;; takes "the edge is the world's" (kx) where an edge fires; an edge edit is a site per row function
  (doseq [x '[raw-inv raw0-complete-inv t12-inv t6-inv t-take-inv t17-inv inv-arm-park inv-retire-one]]
    (is (tree/variant? base/AHA x) (str x)))
  (doseq [x '[inv-fire-edge inv-fire-dep inv-settle-edge t8-full-inv]] (is (tree/variant? base/SVB x) (str x)))
  (is (= 5 (count (tree/site-keys 'inv-edge-upd)))))

(deftest g10-is-not-copied
  (doseq [B [i10/G10 i10/NQ i10/G10R]]
    (is (empty? @(:overrides B)) (str (:pred B)))
    (is (empty? @(:patches B)) (str (:pred B))))
  ;; g10's job condition names its exempt lists: the part lemmas of a parameterised part take the
  ;; part's parameters after Q
  (doseq [x '[t16-inv t15-full-inv t-slice-exit-inv t-release-world-inv inv-retire-one t12-inv t11-inv]]
    (is (tree/variant? i10/G10 x) (str x)))
  (is (= '[Q :- (=> World Bool) gxz :- (List Nat) gkz :- (List Nat)] (vec (take 9 (nth (tree/pres-form i10/G10 't16-inv) 2)))))
  ;; g10r is g10 at empty exempt lists; only T5's start is its own
  (is (tree/variant? i10/G10R 't5-inv))
  (is (declared? 't-cancel-g10-r)))

(deftest g5-and-the-owner-parts-are-not-copied
  (doseq [B [i5/G5 i1o/NZ i1o/GSO]]
    (is (empty? @(:overrides B)) (str (:pred B)))
    (is (empty? @(:patches B)) (str (:pred B))))
  ;; g5 and gso take an extra argument at an inserted source or task row and at a phase edit: sites
  (is (= 1 ('inv-source-ins-fresh tree/dispatched)))
  (is (= 1 ('inv-task-ins-fresh tree/dispatched)))
  (is (some '#{ph-fired} (tree/site-keys 'inv-edge-set-phase)))
  ;; the fired edge is the world's: g5 passes it at the two callers of fire-dep, which forwards it
  (doseq [x '[inv-fire-edge inv-settle-edge inv-fire-dep t7-inv]] (is (tree/variant? i5/G5 x) (str x)))
  (doseq [x '[t1-full-inv t1-stream-inv]] (is (tree/variant? i1o/GSO x) (str x)))
  (is (not-any? #(tree/variant? i1o/NZ %) '[inv-normalize inv-norm-round inv-detach])))

(deftest the-run-parts-are-not-copied
  (doseq [B [i1r/GRX i1r/GR0 i1r/KRB i1r/NEB]]
    (is (empty? @(:overrides B)) (str (:pred B)))
    (is (empty? @(:patches B)) (str (:pred B))))
  ;; gr0 is grx at the empty list: its cell for a lemma grx has is grx's, at that argument
  (is (= 'grx-cancel-run-local (get @(:renames i1r/GR0) 'inv-cancel-run-local)))
  (is (= '[(List.nil Nat) 0] (get (:extra-args i1r/GR0) 'inv-cancel-run-local)))
  ;; the companion ga goes from the step's input down to T12
  (doseq [x '[raw-inv raw0g-inv t12-inv t5-inv t11-inv t17-inv]] (is (tree/variant? i1r/GR0 x) (str x)))
  (is (tree/variant? i1r/GRX 'inv-job-apply)))

(deftest open-scopes-i14-and-the-measure-are-not-copied
  (doseq [B [os/GOX os/GOS i14/VQ i14/VR ms/MB]]
    (is (empty? @(:overrides B)) (str (:pred B)))
    (is (empty? @(:patches B)) (str (:pred B))))
  ;; mb's hypothesis "the parking run is not the tracked one" goes from the await and the take
  ;; down to the park, as an own fact
  (doseq [x '[inv-await-raw inv-await-post inv-take-park raw0-arm-inv]] (is (tree/variant? ms/MB x) (str x)))
  (is (tree/variant? os/GOS 'inv-job-apply))
  (is (= 1 ('inv-run-ins-fresh tree/dispatched))))
