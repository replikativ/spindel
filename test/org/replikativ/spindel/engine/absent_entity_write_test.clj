(ns org.replikativ.spindel.engine.absent-entity-write-test
  "An update fn that keeps an absent entity absent creates no entry. The engine
  writes a node with `#(when % …)`. A nil entry under `:nodes` has no owner,
  and no sweep removes it."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.state-backend :as backend]))

(def ^:private deleted @#'backend/deleted)

(defn- touch-present
  "A node update fn in the engine style: it changes a present node and keeps
  an absent node absent."
  [node]
  (when node (assoc node :seen? true)))

(deftest an-atom-backend-keeps-an-absent-node-absent
  (let [b (backend/create-atom-backend {:nodes {:a {:v 1}}})]
    (testing "a node write on an absent node creates no entry"
      (is (nil? (backend/backend-write! b [:nodes :x] touch-present)))
      (is (not (contains? (:nodes (backend/backend-deref b)) :x))))
    (testing "a field write under an absent node creates no entity"
      (backend/backend-write! b [:nodes :y :owned] (constantly nil))
      (is (not (contains? (:nodes (backend/backend-deref b)) :y))))
    (testing "a node write on a present node applies the fn"
      (is (= {:v 1 :seen? true} (backend/backend-write! b [:nodes :a] touch-present))))
    (testing "a value written to an absent path still lands"
      (is (= {:v 2} (backend/backend-write! b [:nodes :z] (constantly {:v 2}))))
      (is (= {:v 2} (backend/backend-read b [:nodes :z]))))))

(deftest an-overlay-backend-keeps-an-absent-node-absent
  (let [ov (backend/create-overlay-backend
            (backend/create-atom-backend {:nodes {:a {:v 1}}}))]
    (testing "a node write on a node absent in the fork and the parent creates no entry"
      (is (nil? (backend/backend-write! ov [:nodes :x] touch-present)))
      (is (= {} @(:overlay-atom ov)))
      (is (not (contains? (backend/backend-read ov [:nodes]) :x))))
    (testing "a field write under an absent node creates no entity"
      (backend/backend-write! ov [:nodes :y :owned] (constantly nil))
      (is (= {} @(:overlay-atom ov))))
    (testing "a node write on an inherited node copies the node and applies the fn"
      (is (= {:v 1 :seen? true} (backend/backend-write! ov [:nodes :a] touch-present))))
    (testing "a tombstoned node stays a tombstone"
      (backend/backend-write! ov [] #(update % :nodes dissoc :a))
      (is (nil? (backend/backend-write! ov [:nodes :a] touch-present)))
      (is (= deleted (get-in @(:overlay-atom ov) [:nodes :a]))))))
