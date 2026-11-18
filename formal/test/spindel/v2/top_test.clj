(ns spindel.v2.top-test
  "The headline statements (spindel.v2.top, spindel.v2.systop) are kernel constants, and the top
  invariant `inv` holds, evaluated, on the empty world and on every world of some engine sample
  replays (non-vacuity)."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.top :as top]
            [spindel.v2.systop]
            [spindel.v2.oracle :as o]))

(def theorems '[inv-top-parts inv-p3m inv-p3l inv-empty inv-step Reach1 reach-inv sysinv sysinv-mk SysReach sys-reach-inv])

(deftest headline-constants
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

(deftest inv-on-replayed-worlds
  (is (true? (top/inv s/empty-world)))
  (doseq [n [4 5 13]]
    (let [ws (:worlds (o/replay (o/read-log (str "test/spindel/v2/oracle/log-sample-" n ".edn")) :worlds? true))]
      (is (seq ws))
      (is (every? #(true? (top/inv %)) ws) (str "sample " n)))))
