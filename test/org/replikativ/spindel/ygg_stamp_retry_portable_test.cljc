(ns org.replikativ.spindel.ygg-stamp-retry-portable-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.yggdrasil :as ygg]))

(deftest retry-index-is-never-inherited-or-snapshotted
  (let [parent (context/create-execution-context)
        calls (atom 0)
        plan {:parent-ctx parent :retry #(swap! calls inc)}]
    (try
      (rtp/swap-state! parent [:world/ephemeral ::ygg/pending-stamps] (constantly {:retry plan}))
      (let [children (mapv #(context/fork-context parent :mode %) [:following :frozen])
            snapshot (context/snapshot-context parent :clean-in-flight? false)
            restored (context/restore-snapshot snapshot :drain-events? false)]
        (doseq [ctx (conj children restored)]
          (is (empty? (rtp/get-state ctx [:world/ephemeral ::ygg/pending-stamps])))
          (is (= [] (ygg/retry-stamps! ctx))))
        (is (zero? @calls))
        (is (= [:retry] (ygg/retry-stamps! parent)))
        (is (= 1 @calls))
        (doseq [ctx (conj children snapshot)]
          (is (empty? (get (rtp/get-state ctx []) :world/ephemeral)))))
      (finally (context/close-context! parent)))))

(deftest explicit-retry-context-refuses-a-foreign-plan
  (let [parent (context/create-execution-context)
        calls (atom 0)
        entry {:retry {:parent-ctx parent :retry #(swap! calls inc)}}]
    (try
      (rtp/swap-state! parent [:world/ephemeral ::ygg/pending-stamps] (constantly entry))
      ;; Even an explicitly installed foreign entry cannot execute in this world.
      (let [foreign (context/fork-context parent :state-updates {:world/ephemeral {::ygg/pending-stamps entry}})]
        (is (= [] (ygg/retry-stamps! foreign)))
        (is (zero? @calls))
        (rtp/swap-state! foreign [:world/ephemeral ::ygg/pending-stamps] (constantly nil)))
      (is (= [:retry] (ygg/retry-stamps! parent)))
      (is (= 1 @calls))
      (finally (context/close-context! parent)))))

(deftest serialized-world-drops-executable-state-and-preserves-unrelated-data
  (let [parent (context/create-execution-context)
        calls (atom 0)]
    (try
      (rtp/swap-state! parent [:roundtrip/marker] (constantly {:keep [1 2 3]}))
      (rtp/swap-state! parent [:world/ephemeral]
                       (constantly {::ygg/pending-stamps
                                    {:retry {:parent-ctx parent :retry #(swap! calls inc)}}
                                    ::other-executable #(swap! calls inc)}))
      (let [serialized (context/serialize-context parent)]
        (is (not (re-find #"world/ephemeral|pending-stamps|#object|#function" serialized)))
        (let [decoded (context/deserialize-context serialized (:executor parent))
              restored (context/restore-snapshot decoded :drain-events? false)]
          (doseq [ctx [decoded restored]]
            (is (= {:keep [1 2 3]} (rtp/get-state ctx [:roundtrip/marker])))
            (is (nil? (rtp/get-state ctx [:world/ephemeral]))))
          (is (= [] (ygg/retry-stamps! restored)))
          (is (zero? @calls))))
      (is (= [:retry] (ygg/retry-stamps! parent)))
      (is (= 1 @calls))
      (finally (context/close-context! parent)))))
