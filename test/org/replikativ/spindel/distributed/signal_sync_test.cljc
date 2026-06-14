(ns org.replikativ.spindel.distributed.signal-sync-test
  "merge-fn on SignalSyncStrategy: a convergent ygg-signal JOINS an incoming
   remote value with the local one (so concurrent local + remote updates
   converge) instead of clobbering it under blind LWW. nil merge-fn = the
   LWW-reset default."
  (:require #?(:clj  [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [clojure.set :as set]
            [kabel.pubsub.protocol :as proto]
            [org.replikativ.spindel.distributed.signal-sync :as ss]))

(deftest merge-fn-joins-instead-of-resetting
  (testing "with merge-fn, an incoming remote value is JOINED with the local one"
    (let [a     (atom #{:x})
          strat (ss/->SignalSyncStrategy a nil set/union)]
      (proto/-apply-publish strat {:value #{:y}})
      (is (= #{:x :y} @a) "convergent publish: local :x survives the remote :y")
      (proto/-apply-handshake-item strat {:value #{:z}})
      (is (= #{:x :y :z} @a) "convergent handshake adopt also joins"))))

(deftest no-merge-fn-is-lww-reset
  (testing "without merge-fn, an incoming value overwrites local (LWW — default)"
    (let [a     (atom #{:x})
          strat (ss/->SignalSyncStrategy a nil nil)]
      (proto/-apply-publish strat {:value #{:y}})
      (is (= #{:y} @a) "LWW: remote replaces local"))))
