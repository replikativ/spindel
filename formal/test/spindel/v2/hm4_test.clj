(ns spindel.v2.hm4-test
  "Loading spindel.v2.hm4 kernel-checks the h-mem2 bundle's fires (`h3-fire-edge`: a delivery to a final debtor
  exempts the member id while its edge goes, the fill takes it out of its only obliged holder, then the
  exemption is undone), the host-edge removals (T8 unobserve, T22 unawait), invalidate-dependents, and the
  bundle copies of T2, T9, T18 and the fire folds (wake-closed, settle-host, fast-fill, deliver-fire). The
  step theorem for h3 is still open (notes/PLAN.md, branch hm4); the tripwire is hm3_test."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.hm4]))

(def theorems
  '[h3-fill-contrib-act h3-freeb-of h3-freeb-frame h3-free-fill h3-edge-not-comp h3-edge-not-debtor h3-free-self h3-xm-cons
    hk-safe-nocomp h3-cs-use h3-cur-run-current h3-freeb-cred h3-free-of-freeb h3-fa-ncur h3-undo-fill h3-deliver-safe
    h3-deliver-dep h3-fire-dep h3-phase-free h3-fire-wait-act h3-act-id-pos h3-fire-wait h3-fire-edge h3-remove-host
    t22-un-hm3 t8-unobserve-hm3 h3-inval-id h3-inval-fold h3-kds-scan hm3-invalidate-dependents
    t2-h3 t9-h3 t18-h3 hm3-wake-closed hm3-settle-host hm3-fast-fill hm3-deliver-fire])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))
