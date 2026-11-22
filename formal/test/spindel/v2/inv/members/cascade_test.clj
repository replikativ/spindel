(ns spindel.v2.inv.members.cascade-test
  "Fresh test discovery loads and kernel-checks HM6. Conditional cascade
   lemmas retain their hypotheses; arbitrary-step current-members remains a later proof."
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io]
            [ansatz.core :as a]
            [spindel.v2.inv.members.cascade])
  (:import [ansatz.kernel ConstantInfo Env Name]
           [java.io PushbackReader]))

(def theorems
  '[edge-kinds-well-formed edge-kinds-rest-of edge-kinds-intro edge-kinds-parts edge-kinds-pres edge-kinds-unmark edge-kinds-mark1 edge-kinds-new edge-kinds-mark-edge-r
    edge-kinds-insert-edge-fresh edge-kinds-insert-edge-checked edge-kinds-await-edge edge-kinds-rule-r-round edge-kinds-rule-r-loop edge-kinds-rule-r
    step-edge-kinds edge-kinds-empty fm-mk fm-acts-of fm-runs-of fm-cur-of fm-ab-refl fm-ab-trans fm-refl fm-trans fm-free
    fm-frame fm-same fm-rkq-congr fm-run-upd fm-act-del fm-me-filter fm-ab-fill fm-act-fill fm-comp-upd
    fm-nat-fold fm-edge-upd fm-remove-edge fm-drop-act fm-resume fm-fill-slot fm-invalidate fm-dep-consumed
    fm-deliver-dep fm-fire-dep fm-fire-wait-act fm-fire-wait fm-fire-observe fm-fire-edge fm-drop-edges
    fm-finalize-loop fm-t10-finalize-debtor fm-fire-fold fm-fire-task-cancelled fm-task-upd fm-cancel-acts
    fm-cancel-res fm-cleanup-set current-members-m-rel-x current-members-eok-rel-x current-members-x-rel-x current-members-r-rel-x current-members-a-rel-x current-members-rest-rel-x
    current-members-rest-rs-x current-members-rest-run-kill current-members-run-kill current-members-undo-d tsq-refl tsq-trans tsq-remove-edge tsq-fill-slot
    tsq-dep-consumed tsq-fire-dep tsq-fire-wait tsq-fire-edge tsq-final qk-of1 qk-cons-ne qk-del qk-same
    qk-upd qk-filter qk-fill-slot qk-remove-edge qk-uniq qk-keep qk-upd-e qk-q1-fired qk-q1-fired-any
    qk-q1-fired-tt qk-q1-dne qk-q1-obs qk-inval qk-fdep qk-fwait qk-fobs qk-fire qk-sub qk-nil qk-fold
    all-finalize-loop all-t10-finalize-debtor task-cancel-result-run current-members-cancel-mid marks-waiting-cancel-mid cmid-has
    fm-cancel-mid fold-tasks fold-sources cmid-tsq tbl-find-upd-same tcr-tag tcr-final current-members-cancel-task
    current-members-dx-of current-members-cancel-task-x current-members-tof-g current-members-cancel-run-local-g current-members-t13-retire-with-subtree current-members-retire-run
    current-members-close-scope-local current-members-job-apply-g current-members-cascade-g i10-current-exempt-gk-mono-g ncw-all-g jok-all-g current-members-run-cascade-g
    current-members-t14-cancel current-members-t14-host-cancel current-members-t16-close-scope current-members-t-close-scope current-members-t15-resource-ack current-members-t-slice-exit current-members-cancel-losers
    current-members-remove-if-empty])

(defn checked-declaration [name]
  (let [^ConstantInfo declaration (.lookup ^Env @a/ansatz-env (Name/fromString (str name)))]
    (is (some? declaration) (str name " is installed by fresh kernel loading"))
    (when declaration
      (is (= ConstantInfo/THM (.-tag declaration)) (str name " is a theorem"))
      (is (zero? (.-safety declaration)) (str name " is safe"))
      (is (some? (.-type declaration)) (str name " has a checked statement")))
    declaration))

(defn source-statement [resource name]
  (with-open [reader (PushbackReader. (io/reader (io/resource resource)))]
    (loop []
      (when-let [form (read {:eof nil} reader)]
        (if (and (seq? form) (= 'a/theorem (first form)) (= name (second form)))
          {:parameters (nth form 2) :statement (nth form 3)}
          (recur))))))

(deftest theorems-kernel-checked
  (is (= 136 (count theorems)))
  (doseq [name theorems] (checked-declaration name)))

(deftest cascade-hypotheses-remain-explicit
  (is (= {:parameters '[xm :- (List Nat), hx :- (List Nat), gx :- (List Nat), gk :- (List Nat), w :- World, js :- (List Job)]
          :statement '(=> (= (i10-current-exempt gx gk w) true) (= (marks-waiting hx w) true) (= (edge-kinds w) true) (= (current-members xm w) true)
                          (= (current-members xm (run-cascade w js)) true))}
         (source-statement "spindel/v2/inv/members/cascade.clj" 'current-members-run-cascade-g)))
  (is (= {:parameters '[w :- World, it :- Item]
          :statement '(=> (= (edge-kinds w) true) (= (rule-r-safe (:world (raw w it))) true)
                          (= (edge-kinds (:world (world-step w it))) true))}
         (source-statement "spindel/v2/inv/members/cascade.clj" 'step-edge-kinds))))
