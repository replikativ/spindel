(ns spindel.v2.pres.tree-test
  "The generic tree (spindel.v2.pres.tree): every lemma of the step's closure that calls others has
  its shared generic lemma; a part gets its own (pres-x@part) only on its context paths; a gate gives
  a part's continuations its fact; transition is cut by item; every part is on the tree and the copier is gone."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.inv.acts :as acts]
            [spindel.v2.inv.copier :as c]
            [spindel.v2.pres.part :as part]
            [spindel.v2.inv.i10-task]
            [spindel.v2.inv.i9-res]
            [spindel.v2.inv.i8 :as i8]
            [spindel.v2.inv.idle :as idle]
            [spindel.v2.inv.comp-facts :as cf]
            [spindel.v2.inv.alive-runs :as ar]
            [spindel.v2.inv.members.bundle :as mb]
            [spindel.v2.inv.members.cascade :as mc]
            [spindel.v2.inv.members.step :as mst]
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
            [spindel.v2.completion.quiet :as quiet]
            [spindel.v2.completion.quiet-world :as qw]
            [spindel.v2.completion.stable :as stable]
            [spindel.v2.pres.tree :as tree]))

(defn- declared? [s] (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str s)))))

(deftest every-node-has-its-generic-lemma
  (is (< 150 (count (:nodes @tree/tree))))
  (doseq [x (:nodes @tree/tree)] (is (declared? (tree/pres-name x)) (str x))))

(deftest part-lemmas-only-on-context-paths
  ;; i10-task takes T12's guard and passes it to complete-raw; i9-res takes T17's and passes it to arm-park
  (is (tree/variant? c/GL 'well-formed-t12-complete))
  (is (declared? (tree/pres-name c/GL 'well-formed-t12-complete)))   ; pres-t12-complete@i10-task
  (is (not (tree/variant? c/GL 'well-formed-t17-arm)))
  (is (tree/variant? c/G9 'well-formed-t17-arm))
  (is (not (tree/variant? c/G9 'well-formed-t12-complete)))
  (is (not (tree/variant? c/G9 'well-formed-dispatch-raw)))
  (is (= 10 (count (filter #(and (tree/variant? (if (= 'i10-task (first %)) c/GL c/G9) (second %)))
                           (for [p '[i10-task i9-res] x (:nodes @tree/tree)] [p x]))))))

(deftest raw0-is-cut-by-item
  ;; one lemma per item, each checked for well-formed; well-formed-transition dispatches to them, and a part that
  ;; passes into one transition gets that branch's lemma, not the dispatcher's
  (is (= 49 (count (filter #(re-matches #"raw0-.+-inv" (name %)) (:nodes @tree/tree)))))
  (is (declared? 'well-formed-transition-complete))
  (doseq [B [c/GL c/G9]] (is (not (tree/variant? B 'well-formed-transition))))
  (is (tree/variant? c/GL 'well-formed-transition-complete))
  (is (tree/variant? c/G9 'well-formed-transition-arm))
  (is (not (tree/variant? c/G9 'well-formed-transition-complete))))

(deftest a-gate-gives-the-continuation-its-fact
  ;; a part taking C0's gate: raw0's continuations receive root-open-if (checked for any Q); only the
  ;; branches of transition that call the gate get the part's lemma, not the dispatcher
  (let [B (part/mk-bundle 'tgate [] "tgate-" {})]
    (tree/part! B :gates '{well-formed-require-root-open hc0})
    (is (= '#{well-formed-require-root-open well-formed-transition-append well-formed-transition-create-link well-formed-transition-create-link-top
              well-formed-transition-create-source well-formed-transition-create-source-top well-formed-transition-link-realize}
           (set (filter #(tree/variant? B %) (:nodes @tree/tree)))))
    (doseq [x '[well-formed-require-root-open well-formed-transition-create-source]]
      (when-not (declared? (tree/pres-name B x)) (@#'tree/ev (tree/pres-form B x)))
      (is (declared? (tree/pres-name B x)) (str x)))
    (swap! tree/parts dissoc 'tgate)))

(deftest gl-is-not-copied
  (is (= '{well-formed-cancel-run-local i10-task-cancel-run-local-hand, well-formed-complete-raw i10-task-complete-raw-hand,
           well-formed-retire-run i10-task-retire-run-hand, well-formed-spawn-rows i10-task-spawn-rows-hand,
           well-formed-start-raw i10-task-start-raw, well-formed-new-run-of i10-task-new-run-of}
         (get-in @tree/parts ['i10-task :over]))))

(deftest g9-is-not-copied
  (is (= '{well-formed-cancel-run-local i9-res-cancel-run-local, well-formed-ack-raw i9-res-ack-raw-hand, well-formed-arm-park i9-res-arm-park}
         (get-in @tree/parts ['i9-res :over]))))

(deftest g8-is-not-copied
  ;; the companion acts-parked reaches the cascades from raw (raw -> host-guarded-transition -> transition -> the transitions)
  (doseq [x '[well-formed-raw well-formed-host-guarded-transition well-formed-transition well-formed-t15-resource-ack well-formed-complete-raw well-formed-cancel-pred]]
    (is (tree/variant? i8/G8 x) (str x)))
  (is (not (tree/variant? i8/G8 'well-formed-job-apply)))
  ;; transition, host-guarded-transition, T14, ... only forward acts-parked: inferred, not declared
  (is (not (contains? (:own (get @tree/parts 'i8-closed)) 'well-formed-transition)))
  (is (= '[(= (acts-parked w) true)] (vec (take-nth 2 (rest (get (tree/table-own i8/G8) 'well-formed-transition)))))))

(deftest g7-is-not-copied
  ;; i7-idle and its companions comp-awake-owns-run (awc awr) and alive-runs-listed (kc0 kl0 kd0): parameterised parts, Q := (B p)
  ;; a computation edit is one site per row function, generic in its arguments
  (is (some #{'(comp-start-row rid)} (tree/site-keys 'well-formed-comp-upd)))
  (is (contains? (get-in @tree/parts ['comp-awake-owns-run :sites]) '[well-formed-comp-upd (comp-cut-row h k bs)]))
  ;; T6, T-take, T17, T11, schedule, finalize: plumbing in the table, not g7's own proofs
  (doseq [x '[well-formed-t6-await well-formed-t-take well-formed-t17-arm well-formed-t11-dispatch well-formed-t-schedule well-formed-t-finalize well-formed-take-park well-formed-arm-park]]
    (is (tree/variant? idle/G7 x) (str x))))

(deftest gd-is-not-copied
  ;; i7-idle and i10-current from the step's input reach T6, T22, T8 and T12 through raw: declared at raw, host-guarded-transition,
  ;; transition, inferred at raw0's branches
  (is (= '[(= (i7-idle w) true) (= (i10-current w) true)] (vec (take-nth 2 (rest (get (tree/table-own cf/GD) 'well-formed-transition))))))
  (doseq [x '[well-formed-transition-await well-formed-transition-host-await well-formed-transition-complete well-formed-transition-observe well-formed-t6-await well-formed-t22-host-await]]
    (is (tree/variant? cf/GD x) (str x))))

(deftest hmk-is-not-copied
  ;; "not a computation id": the source and link chain takes it as a fact, from the transitions
  (doseq [x '[well-formed-t-close well-formed-close-raw well-formed-close-source well-formed-close-source-ended well-formed-t-append well-formed-append-raw
              well-formed-t-link-realize well-formed-link-realize-raw well-formed-realize-link well-formed-deliver-res well-formed-resume well-formed-fill-slot]]
    (is (tree/variant? mk/HMK x) (str x))))

(deftest scope-and-tomb-parts-are-not-copied
  ;; tombs-dormant takes i7-idle from the step's input at T7 and T6; i1-scopes and scope-parents-acyclic take "the parent is a scope" where a
  ;; run joins a scope
  (is (tree/variant? tomb/GY 'well-formed-transition-track))
  (doseq [x '[well-formed-t7-track well-formed-t6-await]] (is (contains? (get-in @tree/parts ['tombs-dormant :ctx]) x) (str x)))
  (doseq [p '[i1-scopes scope-parents-acyclic]] (is (contains? (get-in @tree/parts [p :ctx]) 'well-formed-add-run-scope) (str p))))

(deftest base-parts-are-not-copied
  ;; an activation edit and a cleanup edit are sites per row function (na's and aha's extra argument
  ;; is rfl only at a concrete row function; refs-not-edges proves cleanup-drop by its own lemma)
  (is (seq (tree/site-keys 'well-formed-act-upd)))
  (is (some #(and (seq? %) (= 'cleanup-drop (first %))) (tree/site-keys 'well-formed-cleanup-upd)))
  (is (contains? (get-in @tree/parts ['refs-not-edges :sites]) ['well-formed-cleanup-upd (first (tree/site-keys 'well-formed-cleanup-upd))]))
  ;; refs-not-edges takes "the computation exists" at T5's start and T11's dispatch, "the run is a row" at T14
  (doseq [x '[well-formed-t5-start well-formed-t11-dispatch well-formed-job-apply]] (is (tree/variant? base/ESB x) (str x)))
  ;; act-runs-alive takes acts-parked from the step's input down to T12, and "the run is an alive row" at the parks; i5-seen
  ;; takes "the edge is the world's" (edge-debtor-kept) where an edge fires; an edge edit is a site per row function
  (doseq [x '[well-formed-raw well-formed-transition-complete well-formed-t12-complete well-formed-t6-await well-formed-t-take well-formed-t17-arm well-formed-arm-park well-formed-retire-one]]
    (is (tree/variant? base/AHA x) (str x)))
  (doseq [x '[well-formed-fire-edge well-formed-fire-dep well-formed-settle-edge well-formed-t8-observe-any-kind]] (is (tree/variant? base/SVB x) (str x)))
  (is (= 5 (count (tree/site-keys 'well-formed-edge-upd)))))

(deftest g10-is-not-copied
  ;; g10's job condition names its exempt lists: the part lemmas of a parameterised part take the
  ;; part's parameters after Q
  (doseq [x '[well-formed-t16-close-scope well-formed-t15-resource-ack well-formed-t-slice-exit well-formed-t21-release-world well-formed-retire-one well-formed-t12-complete well-formed-t11-dispatch]]
    (is (tree/variant? i10/G10 x) (str x)))
  (is (= '[Q :- (=> World Bool) gxz :- (List Nat) gkz :- (List Nat)] (vec (take 9 (nth (tree/pres-form i10/G10 'well-formed-t16-close-scope) 2)))))
  ;; i10-current is i10-current-exempt at empty exempt lists; only T5's start is its own
  (is (tree/variant? i10/G10R 'well-formed-t5-start))
  (is (declared? 'i10-current-exempt-t14-host-cancel-r)))

(deftest g5-and-the-owner-parts-are-not-copied
  ;; i5-dep-final and i1-detached-closed take an extra argument at an inserted source or task row and at a phase edit: sites
  (is (= 1 ('well-formed-source-ins-fresh tree/dispatched)))
  (is (= 1 ('well-formed-task-ins-fresh tree/dispatched)))
  (is (some '#{ph-fired} (tree/site-keys 'well-formed-edge-set-phase)))
  ;; the fired edge is the world's: i5-dep-final passes it at the two callers of fire-dep, which forwards it
  (doseq [x '[well-formed-fire-edge well-formed-settle-edge well-formed-fire-dep well-formed-t7-track]] (is (tree/variant? i5/G5 x) (str x)))
  (doseq [x '[well-formed-t1-create-nonstream well-formed-t1-create-stream]] (is (tree/variant? i1o/GSO x) (str x)))
  (is (not-any? #(tree/variant? i1o/NZ %) '[well-formed-normalize well-formed-normalize-round well-formed-detach])))

(deftest the-run-parts-are-not-copied
  ;; i1-runs is i1-runs-exempt at the empty list: its cell for a lemma i1-runs-exempt has is grx's, at that argument
  (is (= 'i1-runs-exempt-cancel-run-local (get @(:renames i1r/GR0) 'well-formed-cancel-run-local)))
  (is (= '[(List.nil Nat) 0] (get (:extra-args i1r/GR0) 'well-formed-cancel-run-local)))
  ;; the companion acts-parked goes from the step's input down to T12
  (doseq [x '[well-formed-raw well-formed-host-guarded-transition well-formed-t12-complete well-formed-t5-start well-formed-t11-dispatch well-formed-t17-arm]] (is (tree/variant? i1r/GR0 x) (str x)))
  (is (tree/variant? i1r/GRX 'well-formed-job-apply)))

(deftest open-scopes-i14-and-the-measure-are-not-copied
  ;; mb's hypothesis "the parking run is not the tracked one" goes from the await and the take
  ;; down to the park, as an own fact
  (doseq [x '[well-formed-await-raw well-formed-await-post well-formed-take-park well-formed-transition-arm]] (is (tree/variant? ms/MB x) (str x)))
  (is (tree/variant? os/GOS 'well-formed-job-apply))
  (is (= 1 ('well-formed-run-ins-fresh tree/dispatched))))

(deftest grel-gc-and-gst-are-not-copied
  ;; task-unheld-scope-absent: T12 writes a result; the fact comes from raw0's complete arm
  (is (tree/variant? stable/GST 'well-formed-transition-complete))
  (is (not-any? #(tree/variant? qw/GC %) '[well-formed-raw well-formed-normalize well-formed-t14-cancel])))

(deftest gk-takes-the-guard-from-raw0
  ;; a creation has handles 1 only while not released: the fact goes from raw0's arm down to the row
  (doseq [x '[well-formed-transition-create-comp well-formed-t3-create well-formed-create-comp-raw well-formed-transition-handle-new well-formed-t-handle-new
              well-formed-new-task-handle well-formed-new-source-handle well-formed-append-raw well-formed-stream-rows]]
    (is (tree/variant? quiet/GK x) (str x)))
  (is (= '[(= (world-released w) false)] (vec (take-nth 2 (rest (get (tree/table-own quiet/GK) 'well-formed-t3-create))))))
  ;; it stops at transition: the dispatcher and the step are the shared lemmas
  (is (not-any? #(tree/variant? quiet/GK %) '[well-formed-transition well-formed-host-guarded-transition well-formed-raw well-formed-normalize])))

(deftest ga-gx-ch-and-ka-are-not-copied
  ;; ga's own proofs take their facts from their own callers, which are own proofs too: no node
  ;; takes or passes a fact
  (is (not-any? #(tree/variant? acts/GA %) (:nodes @tree/tree)))
  (is (= 21 (count (:over (get @tree/parts 'acts-parked)))))
  (is (= 4 (count (:over (get @tree/parts 'acts-parked-exempt))))))

(deftest ar-is-not-copied
  ;; i7-idle and acts-parked come from the step's input; transition hands each to one branch (T5, T11) and to no other
  (is (= '[(= (i7-idle w) true)] (vec (take-nth 2 (rest (get (tree/table-own ar/AR) 'well-formed-transition-start))))))
  (is (= '[(= (acts-parked w) true)] (vec (take-nth 2 (rest (get (tree/table-own ar/AR) 'well-formed-transition-dispatch-comp))))))
  (is (= '[well-formed-transition-dispatch-comp well-formed-transition well-formed-transition-start]
         (sort (filter #(and (re-find #"^raw0-" (name %)) (tree/variant? ar/AR %)) (:nodes @tree/tree)))))
  ;; the retired run is dead: from the job down to the clear, forwarded
  (doseq [x '[well-formed-job-apply well-formed-retire-run well-formed-t13-retire-with-subtree]] (is (tree/variant? ar/AR x) (str x))))

(deftest h3-ekb-and-fb-are-not-copied
  (doseq [B [mb/H3 mc/EKB mst/FB]]
    ;; sites only: none of them takes a fact from the path
    (is (not-any? #(tree/variant? B %) (:nodes @tree/tree)) (str (:pred B))))
  ;; ekb's only site: the await's edge, whose kind is not closed at the insertion
  (is (= 1 (count (:sites (get @tree/parts 'edge-kinds))))))

(deftest the-copier-is-gone
  (doseq [v '[lcopy! override! patch! closure copy-one-form source-of subst-forms]]
    (is (nil? (ns-resolve 'spindel.v2.pres.part v)) (str v)))
  (is (= #{:pred :params :prefix :extra-args :renames :copied} (set (keys c/GL)))))
