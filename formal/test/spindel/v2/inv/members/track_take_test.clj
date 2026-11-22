(ns spindel.v2.inv.members.track-take-test
  "Loading spindel.v2.inv.members.track-take kernel-checks the next h-mem2 overrides of the current-members copier (notes/history/PLAN.md, branch hm5):
  T7 track (the removed site edge is held by no obliged activation: AR + acts-parked), take and T17 arm (a new activation
  whose member is exempt until its wait edge exists), T14's cancel-acts, T10 finalize and its callers (with marks-waiting),
  T13's run-pointer clears. The step theorem for current-members is still open; the tripwire is hm3_test."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.inv.members.track-take]))

(def theorems
  '[current-members-free-by current-members-ob-has current-members-free-noedge current-members-free-ins-fresh current-members-free-edge-upd current-members-site-p current-members-track-fin current-members-track-raw current-members-acts-parked-good current-members-good-alive current-members-alive-run-latest-run current-members-tok-alive current-members-t7-track-free current-members-t7-track current-members-i10-current-run current-members-comp-facts-cs current-members-r-new current-members-r-acts-g current-members-a-acts-g current-members-rest-act-ins current-members-undo-g current-members-source-not-task current-members-fa-congr current-members-fa-use current-members-fa-run-upd current-members-r-new2 current-members-mem-single current-members-rm-head2 current-members-take-a current-members-take-eok current-members-take-park current-members-take-a-g current-members-take-park-g current-members-task-next current-members-run-key-eq current-members-run-uniq current-members-t-take current-members-arm-eok current-members-arm-park current-members-t17-arm current-members-fold-noc current-members-drop-act-nc current-members-cancel-acts current-members-finalize-one current-members-finalize-loop current-members-t10-finalize-debtor current-members-close-source current-members-fold-noc2 current-members-close-local current-members-fire-task-cancelled current-members-finalize-if-final current-members-t-deliver current-members-clear-task-run current-members-clear-comp-run ])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
