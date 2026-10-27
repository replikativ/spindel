(ns org.replikativ.spindel.lifetime.lockstep-stamp-test
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.lifetime.lockstep :as l]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.yggdrasil :as ygg]))

(deftest stamp-probe-observes-failure-and-recovery
  (let [probe (l/stamp-probe)]
    (is (= 1 (:pending-stamps probe)))
    (is (= 0 (:pending-stamps-after-recovery probe)))
    (is (= 2 (:stamp-calls probe)))))

(deftest stamp-index-layouts
  (doseq [[state path expected]
          [[{::ygg/pending-stamps {:old :plan}} [::ygg/pending-stamps] 1]
           [{:world/ephemeral {::ygg/pending-stamps {:new :plan}}}
            [:world/ephemeral ::ygg/pending-stamps] 1]
           ;; Presence, rather than non-emptiness, selects A2's layout.
           [{::ygg/pending-stamps {:old :stale}
             :world/ephemeral {::ygg/pending-stamps {}}}
            [:world/ephemeral ::ygg/pending-stamps] 0]]]
    (with-redefs [rtp/get-state (fn [_ p] (get-in state p))]
      (let [index (l/pending-stamp-index ::runtime)]
        (is (= path (:path index)))
        (is (= expected (count (:entries index))))))))
