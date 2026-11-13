(ns spindel.v2.rank-step-test
  "Loading spindel.v2.rank-step kernel-checks P5: the bundle inv-rank (inv-sample and I12
  ranks-ok) is preserved by every step (`step-rank`), including every copied composite lemma
  (`rank-copied`). ranks-ok itself stays a runtime tripwire in engine-test and the oracle."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.rank-step :as rs]))

(def theorems
  '[rk-sample rk-ranks rk-intro rk-parts rank-edge-ok-shrink ranks-shrink same-comps-within
    rank-edge-ok-nondep crank-upd-same comp-upd-within ranks-comp-upd ranks-edge-upd ranks-edge-del
    ranks-set-edges-filter ranks-mark-edge ranks-unmark-edge ranks-remove-edge ranks-drop-cred
    ranks-insert-edge-fresh ranks-insert-edge-checked crank-resync ranks-drop-edges has-del-self
    crank-del-ne ranks-comp-del ranks-filter-world ne-of-mem-ids edge-fresh-of-ok rank-edge-ok-comp-ins
    ranks-comp-ins-fresh nodup-app-disjoint comp-not-source rk-comp-upd rk-drop-act insert-edge-fresh-rk
    rk-insert-edge-checked await-step-ranks await-wire-ranks
    rk-track-raw rk-react-add rk-host-await-raw rk-take-park t8-full-rk rk-await-raw t6-rk
    step-rank inv-rank-empty step-ranks])

(defn- present? [t] (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))))

(deftest theorems-kernel-checked
  (doseq [t theorems] (is (present? t) (str t)))
  (is (< 100 (count @rs/rank-copied)))
  (doseq [t @rs/rank-copied] (is (present? t) (str t))))

(deftest inv-rank-runs
  (is (true? (rs/inv-rank spindel.v2.state/empty-world))))
