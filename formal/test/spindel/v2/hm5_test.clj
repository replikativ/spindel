(ns spindel.v2.hm5-test
  "Loading spindel.v2.hm5 kernel-checks the next h-mem2 overrides of the h3 copier (notes/PLAN.md, branch hm5):
  T7 track (the removed site edge is held by no obliged activation: AR + ga), take and T17 arm (a new activation
  whose member is exempt until its wait edge exists), T14's cancel-acts, T10 finalize and its callers (with hmk),
  T13's run-pointer clears. The step theorem for h3 is still open; the tripwire is hm3_test."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.hm5]))

(def theorems
  '[h3-free-by h3-ob-has h3-free-noedge h3-free-ins-fresh h3-free-edge-upd h3-site-p h3-track-fin h3-track-raw h3-ga-good h3-good-alive h3-ar-run h3-tok-alive h3-t7-free t7-h3 h3-g10-run h3-gd-cs h3-r-new h3-r-acts-g h3-a-acts-g h3r-act-ins h3-undo-g h3-src-not-task h3-fa-congr h3-fa-use h3-fa-run-upd h3-r-new2 h3-mem-single h3-rm-head2 h3-take-a h3-take-eok h3-take-park h3-take-a-g h3-take-park-g h3-task-next h3-rk3-eq h3-run-uniq t-take-h3 h3-arm-eok h3-arm-park t17-h3 h3-fold-noc h3-drop-act-nc h3-cancel-acts h3-finalize-one h3-fin-loop h3-finalize-debtor h3-close-source h3-fold-noc2 h3-close-local h3-fire-task-cancelled h3-fin-if-final t-deliver-h3 h3-clear-task-run h3-clear-comp-run ])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
