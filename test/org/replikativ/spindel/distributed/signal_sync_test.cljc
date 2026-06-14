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
          strat (ss/->SignalSyncStrategy a nil set/union nil true)]
      (proto/-apply-publish strat {:value #{:y}})
      (is (= #{:x :y} @a) "convergent publish: local :x survives the remote :y")
      (proto/-apply-handshake-item strat {:value #{:z}})
      (is (= #{:x :y :z} @a) "convergent handshake adopt also joins"))))

(deftest no-merge-fn-is-lww-reset
  (testing "without merge-fn, an incoming value overwrites local (LWW — default)"
    (let [a     (atom #{:x})
          strat (ss/->SignalSyncStrategy a nil nil nil nil)]
      (proto/-apply-publish strat {:value #{:y}})
      (is (= #{:y} @a) "LWW: remote replaces local"))))

(deftest async-merge-joins-after-suspension
  (testing "with merge-fn + :sync? false (a CPS-returning join, as a durable :sync? false
            ygg-signal yields), the incoming value is committed only once the join
            resolves — proving the convergent join can SUSPEND on IO before commit"
    (let [a          (atom #{:x})
          ;; A deferred CPS join: captures `resolve` so the test can fire it
          ;; later, modelling a konserve-backed `c/-join` that suspends on IO.
          fire       (atom nil)
          await-join (fn [cur incoming]
                       (fn [resolve _reject]
                         (reset! fire #(resolve (set/union (or cur #{}) incoming)))))
          ;; ONE merge-fn, :sync? false (the default — async) → signal-sync awaits
          ;; the CPS before commit
          strat      (ss/->SignalSyncStrategy a nil await-join nil false)]
      (proto/-apply-publish strat {:value #{:y}})
      (is (= #{:x} @a) "not yet joined — the async join is suspended awaiting IO")
      (@fire)
      (is (= #{:x :y} @a) "joined after the async resolve fires (local :x survives)"))))
