(ns spindel.v2.hm6-test
  "Fresh test discovery loads and kernel-checks HM6. Conditional cascade
   lemmas retain their hypotheses; arbitrary-step h3 remains a later proof."
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io]
            [ansatz.core :as a]
            [spindel.v2.hm6])
  (:import [ansatz.kernel ConstantInfo Env Name]
           [java.io PushbackReader]))

(def theorems
  '[ekb-sample ekb-rest-of ekb-intro ekb-parts ekb-pres ekb-unmark ekb-mark1 ekb-new ekb-mark-edge-r
    ekb-insert-edge-fresh ekb-insert-edge-checked ekb-await-edge ekb-rule-r-round ekb-rr-loop ekb-rule-r
    step-ekb ekb-empty fm-mk fm-acts-of fm-runs-of fm-cur-of fm-ab-refl fm-ab-trans fm-refl fm-trans fm-free
    fm-frame fm-same fm-rkq-congr fm-run-upd fm-act-del fm-me-filter fm-ab-fill fm-act-fill fm-comp-upd
    fm-nat-fold fm-edge-upd fm-remove-edge fm-drop-act fm-resume fm-fill-slot fm-invalidate fm-dep-consumed
    fm-deliver-dep fm-fire-dep fm-fire-wait-act fm-fire-wait fm-fire-observe fm-fire-edge fm-drop-edges
    fm-fin-loop fm-finalize-debtor fm-fire-fold fm-fire-task-cancelled fm-task-upd fm-cancel-acts
    fm-cancel-res fm-cleanup-set h3-m-rel-x h3-eok-rel-x h3-x-rel-x h3-r-rel-x h3-a-rel-x h3-rest-rel-x
    h3r-rs-x h3r-run-kill h3-run-kill h3-undo-d tsq-refl tsq-trans tsq-remove-edge tsq-fill-slot
    tsq-dep-consumed tsq-fire-dep tsq-fire-wait tsq-fire-edge tsq-final qk-of1 qk-cons-ne qk-del qk-same
    qk-upd qk-filter qk-fill-slot qk-remove-edge qk-uniq qk-keep qk-upd-e qk-q1-fired qk-q1-fired-any
    qk-q1-fired-tt qk-q1-dne qk-q1-obs qk-inval qk-fdep qk-fwait qk-fobs qk-fire qk-sub qk-nil qk-fold
    all-fin-loop all-finalize-debtor task-cancel-result-run h3-cancel-mid hmk-cancel-mid cmid-has
    fm-cancel-mid fold-tasks fold-sources cmid-tsq tbl-find-upd-same tcr-tag tcr-final h3-cancel-task
    h3-dx-of h3-cancel-task-x h3-tof-g h3-cancel-run-local-g h3-retire-with h3-retire-local
    h3-close-scope-local h3-job-apply-g h3-cascade-g g10-gk-mono-g ncw-all-g jok-all-g h3-run-cascade-g
    t14-h3 t-cancel-h3 t16-h3 t-close-scope-h3 t15-full-h3 t-slice-exit-h3 h3-cancel-losers
    hm3-remove-if-empty])

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
          :statement '(=> (= (g10 gx gk w) true) (= (hmk hx w) true) (= (ekb w) true) (= (h3 xm w) true)
                          (= (h3 xm (run-cascade w js)) true))}
         (source-statement "spindel/v2/hm6.clj" 'h3-run-cascade-g)))
  (is (= {:parameters '[w :- World, it :- Item]
          :statement '(=> (= (ekb w) true) (= (rule-r-safe (:world (raw w it))) true)
                          (= (ekb (:world (world-step w it))) true))}
         (source-statement "spindel/v2/hm6.clj" 'step-ekb))))
