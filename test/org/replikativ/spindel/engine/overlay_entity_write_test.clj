(ns org.replikativ.spindel.engine.overlay-entity-write-test
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.state-backend :as backend]))

(defrecord Entity [value])

(deftest entity-writes-preserve-the-logical-state
  (let [initial {:nodes (with-meta
                          (sorted-map :a (->Entity 1) :b {:nested {:value 2}})
                          {:collection :nodes})}
        parent (backend/create-atom-backend initial)
        overlay (backend/create-overlay-backend parent)
        reference (backend/create-atom-backend initial)]
    (doseq [[path f] [[[:nodes :a :value] inc]
                      [[:nodes :b :nested :value] inc]
                      [[:nodes :b :missing] (constantly nil)]
                      [[:nodes :c :missing] (constantly nil)]
                      [[:nodes :c] (constantly (->Entity 4))]
                      [[:nodes :a] #(assoc % :extra false)]
                      [[:nodes :nil] (constantly nil)]
                      [[:nodes :nil :value] (constantly false)]]]
      (is (= (backend/backend-write! reference path f)
             (backend/backend-write! overlay path f)))
      (is (= (backend/backend-deref reference)
             (backend/backend-deref overlay))))
    (is (instance? Entity (backend/backend-read overlay [:nodes :a])))
    (is (= initial (backend/backend-deref parent))))
  (testing "copy-on-write preserves entity collection metadata and ordering"
    (let [entities (with-meta (sorted-map :a (->Entity 1)) {:tag :entities})
          overlay (backend/create-overlay-backend nil {:nodes entities})]
      (backend/backend-write! overlay [:nodes :a :value] inc)
      (is (sorted? (:nodes @(:overlay-atom overlay))))
      (is (= {:tag :entities} (meta (:nodes @(:overlay-atom overlay))))))))

(deftest entity-writes-respect-full-replacements-and-tombstones
  (let [parent (backend/create-atom-backend {:nodes {:a {:value 1} :b {:value 2}}})
        overlay (backend/create-overlay-backend parent)]
    (backend/backend-write! overlay [:nodes] (constantly {:a {:value 3}}))
    (backend/backend-write! overlay [:nodes :b :value] (fnil inc 0))
    (is (= {:a {:value 3} :b {:value 1}} (backend/backend-read overlay [:nodes])))
    (backend/backend-write! overlay [] #(update % :nodes dissoc :a))
    (is (nil? (backend/backend-write! overlay [:nodes :a] identity)))
    (is (nil? (backend/backend-read overlay [:nodes :a])))
    (backend/backend-write! overlay [:nodes :a :nested :value] (constantly 9))
    (is (= {:nested {:value 9}} (backend/backend-read overlay [:nodes :a])))))

(deftest concurrent-entity-writes-do-not-lose-updates
  (let [parent (backend/create-atom-backend {:nodes {:a {:value 0}}})
        overlay (backend/create-overlay-backend parent)
        gate (promise)
        writers (doall (repeatedly 4 #(future @gate
                                              (dotimes [_ 250]
                                                (backend/backend-write! overlay [:nodes :a :value] inc)))))]
    (deliver gate true)
    (doseq [writer writers] @writer)
    (is (= 1000 (backend/backend-read overlay [:nodes :a :value])))
    (is (= 0 (backend/backend-read parent [:nodes :a :value])))))

(deftest an-unchanged-write-is-skipped-only-where-nothing-can-tell
  (let [v {:k 1}
        state {:spin-tracking {:s v}}]
    (testing "over a parent that can still change, an inherited entity must be copied to stop following"
      (let [overlay (backend/create-overlay-backend (backend/create-atom-backend state))
            unchanged? (backend/unchanged-write? overlay)]
        (is (not (unchanged? :spin-tracking :s (backend/backend-read overlay [:spin-tracking :s]) v)))))
    (testing "over a frozen (immutable) parent, following it is owning it"
      (let [overlay (backend/create-overlay-backend (backend/create-immutable-backend state))
            unchanged? (backend/unchanged-write? overlay)]
        (is (unchanged? :spin-tracking :s (backend/backend-read overlay [:spin-tracking :s]) v))
        (is (not (unchanged? :spin-tracking :s v {:k 1})) "equal is not identical")))
    (testing "an entity the overlay already holds"
      (let [overlay (backend/create-overlay-backend (backend/create-atom-backend {}))
            _ (backend/backend-write! overlay [:spin-tracking :s] (constantly v))
            unchanged? (backend/unchanged-write? overlay)]
        (is (unchanged? :spin-tracking :s (backend/backend-read overlay [:spin-tracking :s]) v))))
    (testing "a plain atom backend"
      (is ((backend/unchanged-write? (backend/create-atom-backend state)) :spin-tracking :s v v)))))
