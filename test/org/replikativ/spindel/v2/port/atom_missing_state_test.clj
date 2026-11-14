(ns org.replikativ.spindel.v2.port.atom-missing-state-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture]]))

(use-fixtures :each checked-fixture)

(deftest rebinding-within-the-lineage-is-silent
  (let [a (v2/atom 1) child (v2/fork! v2/*world*) grandchild (v2/fork! child)]
    (try
      (binding [v2/*world* grandchild] (is (= 1 @a)) (swap! a inc) (is (= 2 @a)))
      (is (= 1 @a))
      (let [d (v2/deferred) m (v2/mailbox)
            ;; Sources created after a fork belong to a later basis: fork now.
            fresh-child (v2/fork! v2/*world*)]
        (try
          (is (= :v (v2/deliver! (v2/in-world fresh-child d) :v)))
          (let [cm (v2/in-world fresh-child m)]
            (is (nil? (v2/post! cm :msg))) (is (nil? (cm :msg))))
          (finally (v2/release-world! fresh-child))))
      (finally (v2/release-world! grandchild) (v2/release-world! child)))))

(deftest access-from-outside-the-lineage-is-signalled
  (let [root v2/*world* left (v2/fork! root) right (v2/fork! root)
        a (binding [v2/*world* left] (v2/atom 0))
        d (v2/deferred left) m (v2/mailbox left)]
    (try
      (doseq [w [right root]]
        (binding [v2/*world* w]
          (is (thrown? Exception (deref a)))
          (is (thrown? Exception (swap! a inc)))
          (is (thrown? Exception (v2/deliver! (v2/in-world w d) :v)))
          (is (thrown? Exception (v2/post! (v2/in-world w m) :msg)))
          (is (thrown? Exception ((v2/in-world w m) :msg)))))
      (binding [v2/*world* left]
        (is (= 0 @a)) (is (= :v (v2/deliver! d :v))) (is (nil? (m :msg))))
      (finally (v2/release-world! left) (v2/release-world! right)))))

;; dropped: the old default :warn missing-state mode. v2 always throws
;; {:spindel/missing-state id} (design R6); both consumers' tests already ran
;; with -Dspindel.missing-state=throw.