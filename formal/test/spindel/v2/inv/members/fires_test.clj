(ns spindel.v2.inv.members.fires-test
  "Loading spindel.v2.inv.members.fires kernel-checks the h-mem2 bundle's fires (`current-members-fire-edge`: a delivery to a final debtor
  exempts the member id while its edge goes, the fill takes it out of its only obliged holder, then the
  exemption is undone), the host-edge removals (T8 unobserve, T22 unawait), invalidate-dependents, and the
  bundle copies of T2, T9, T18 and the fire folds (wake-closed, settle-host, fast-fill, deliver-fire). The
  step theorem for current-members is still open (notes/history/PLAN.md, branch hm4); the tripwire is hm3_test."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.inv.members.fires]))

(def theorems
  '[current-members-fill-contrib-act current-members-freeb-of current-members-freeb-frame current-members-free-fill current-members-edge-not-comp current-members-edge-not-debtor current-members-free-self current-members-xm-cons
    hk-safe-nocomp current-members-cs-use current-members-cur-run-current current-members-freeb-cred current-members-free-of-freeb current-members-fa-ncur current-members-undo-fill current-members-deliver-safe
    current-members-deliver-dep current-members-fire-dep current-members-phase-free current-members-fire-wait-act current-members-act-id-pos current-members-fire-wait current-members-fire-edge current-members-remove-host
    current-members-t22-host-unawait current-members-t8-unobserve current-members-inval-id current-members-inval-fold current-members-kds-scan current-members-invalidate-dependents
    current-members-t2-write current-members-t9-fire current-members-t18-resource-fire current-members-wake-closed current-members-settle-host current-members-fast-fill current-members-deliver-fire])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
