(ns org.replikativ.spindel.engine.overlay-whole-state-test
  "A whole-state transaction on an OverlayBackend writes only what the update
  fn changed. An untouched top-level map stays out of the overlay, a changed
  entity lands in it, and a removed inherited entity becomes a tombstone."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.state-backend :as backend]))

(def ^:private deleted @#'backend/deleted)

(defn- fork-of [parent-state]
  (backend/create-overlay-backend (backend/create-atom-backend parent-state)))

(def ^:private parent-state
  {:nodes         {:a {:v 1} :b {:v 2} :c {:v 3}}
   :atoms {:s1 #{:a} :s2 #{:b}}
   :flag          true})

(deftest a-whole-state-transaction-writes-only-the-changes
  (testing "an untouched top-level map stays out of the overlay"
    (let [ov (fork-of parent-state)]
      (backend/backend-write! ov [] #(assoc-in % [:nodes :a :v] 10))
      (is (= {:nodes {:a {:v 10}}} @(:overlay-atom ov)))
      (is (= {:a {:v 10} :b {:v 2} :c {:v 3}} (backend/backend-read ov [:nodes])))))
  (testing "a removed inherited entity becomes a tombstone and stays hidden"
    (let [ov (fork-of parent-state)]
      (backend/backend-write! ov [] #(update % :atoms dissoc :s1))
      (is (= deleted (get-in @(:overlay-atom ov) [:atoms :s1])))
      (is (= {:s2 #{:b}} (backend/backend-read ov [:atoms])))
      (is (nil? (backend/backend-read ov [:atoms :s1])))))
  (testing "an entity equal to the parent's is not copied"
    (let [ov (fork-of parent-state)]
      (backend/backend-write! ov [] #(assoc-in % [:nodes :b] {:v 2}))
      (is (= {} @(:overlay-atom ov)))))
  (testing "a removed top-level key hides the parent's value"
    (let [ov (fork-of parent-state)]
      (backend/backend-write! ov [] #(dissoc % :flag))
      (is (= deleted (:flag @(:overlay-atom ov))))
      (is (nil? (backend/backend-read ov [:flag])))
      (is (not (contains? (backend/backend-deref ov) :flag)))))
  (testing "a new top-level value lands in the overlay"
    (let [ov (fork-of parent-state)]
      (backend/backend-write! ov [] #(assoc % :extra {:x 1}))
      (is (= {:x 1} (backend/backend-read ov [:extra])))
      (is (= parent-state (dissoc (backend/backend-deref ov) :extra)))))
  (testing "the transaction returns the new state"
    (let [ov (fork-of parent-state)]
      (is (= 10 (get-in (backend/backend-write! ov [] #(assoc-in % [:nodes :a :v] 10))
                        [:nodes :a :v]))))))
