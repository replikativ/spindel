(ns spindel.v2.inv.rank-step-test
  "Loading spindel.v2.inv.rank-step kernel-checks P5: the bundle i12-ranks (well-formed and I12
  ranks-ok) is preserved by every step (`step-rank`), including every copied composite lemma
  (`rank-copied`). ranks-ok itself stays a runtime tripwire in engine-test and the oracle."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.inv.rank-step :as rs]))

(def theorems
  '[i12-ranks-well-formed i12-ranks-ranks i12-ranks-intro i12-ranks-parts rank-edge-ok-shrink ranks-shrink same-comps-within
    rank-edge-ok-nondep crank-upd-same comp-upd-within ranks-comp-upd ranks-edge-upd ranks-edge-del
    ranks-set-edges-filter ranks-mark-edge ranks-unmark-edge ranks-remove-edge ranks-drop-cred
    ranks-insert-edge-fresh ranks-insert-edge-checked crank-resync ranks-drop-edges has-del-self
    crank-del-ne ranks-comp-del ranks-filter-world ne-of-mem-ids edge-fresh-of-ok rank-edge-ok-comp-ins
    ranks-comp-ins-fresh nodup-app-disjoint comp-not-source i12-ranks-comp-upd i12-ranks-drop-act i12-ranks-insert-edge-fresh
    i12-ranks-insert-edge-checked await-step-ranks await-wire-ranks
    i12-ranks-track-raw i12-ranks-react-add i12-ranks-host-await-raw i12-ranks-take-park i12-ranks-t8-observe-any-kind i12-ranks-await-raw i12-ranks-t6-await
    step-rank i12-ranks-empty step-ranks])

(defn- present? [t] (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))))

(deftest theorems-kernel-checked
  (doseq [t theorems] (is (present? t) (str t)))
  (is (< 100 (count @rs/rank-copied)))
  (doseq [t @rs/rank-copied] (is (present? t) (str t))))

(deftest inv-rank-runs
  (is (true? (rs/i12-ranks spindel.v2.state/empty-world))))
