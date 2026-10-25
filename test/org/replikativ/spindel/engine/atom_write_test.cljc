(ns org.replikativ.spindel.engine.atom-write-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.state-backend :as backend]
            [org.replikativ.spindel.incremental.deltaable.map :as dm]
            [org.replikativ.spindel.incremental.deltaable.protocols :as delta]))

(defrecord WriteRecord [value])

(deftest unchanged-leaves-preserve-ancestor-deltas
  (let [initial {:data (dm/deltaable-map {:a {:v 1}})}
        path [:data :a :v]
        expected (update-in initial path identity)
        b (backend/create-atom-backend initial)]
    (is (= 1 (backend/backend-write! b path identity)))
    (is (= [{:delta :update :path [:a] :value {:v 1} :old-value {:v 1}}]
           (delta/get-deltas (:data (backend/backend-deref b)))))
    (is (= (delta/get-deltas (:data expected))
           (delta/get-deltas (:data (backend/backend-deref b)))))))

(deftest deeply-absent-nil-writes-do-not-descend-recursively
  (let [b (backend/create-atom-backend {})
        path (vec (repeat 100000 :missing))
        calls (atom [])]
    (try
      (is (nil? (backend/backend-write! b path
                                        (fn [old] (swap! calls conj old) nil))))
      (catch #?(:clj Throwable :cljs :default) e
        (is false (str "Absent nil write must not overflow: "
                       #?(:clj (.getName (class e)) :cljs (.-name e))))))
    (is (= [nil] @calls))
    (is (= {} (backend/backend-deref b)))))

(deftest absent-and-present-writes
  (doseq [[initial path expected]
          [[{} [:nodes :missing :value] {}]
           [{:nodes nil} [:nodes :missing :value] {:nodes nil}]
           [{:nodes {:missing nil}} [:nodes :missing :value] {:nodes {:missing nil}}]
           [{:nodes {:present {:value nil}}} [:nodes :present :value]
            {:nodes {:present {:value nil}}}]
           [{:nodes {:present {:value false}}} [:nodes :present :value]
            {:nodes {:present {:value nil}}}]
           [{:values [nil]} [:values 0] {:values [nil]}]
           [{:values []} [:values 0] {:values []}]]]
    (testing (str "nil write at " path " in " initial)
      (let [b (backend/create-atom-backend initial)
            calls (atom [])]
        (is (nil? (backend/backend-write! b path
                                          (fn [old] (swap! calls conj old) nil))))
        (is (= [(get-in initial path)] @calls))
        (is (= expected (backend/backend-deref b)))))))

(deftest updates-preserve-container-types-and-return-the-target
  (let [b (backend/create-atom-backend
           {:node (->WriteRecord 1) :values [false]})]
    (is (= 2 (backend/backend-write! b [:node :value] inc)))
    (is (instance? WriteRecord (backend/backend-read b [:node])))
    (is (true? (backend/backend-write! b [:values 0] not)))
    (is (= [true] (backend/backend-read b [:values])))
    (is (= :created (backend/backend-write! b [:new :deep :leaf] (constantly :created))))
    (is (= {:deep {:leaf :created}} (backend/backend-read b [:new])))
    (is (= {:replacement true}
           (backend/backend-write! b [] (constantly {:replacement true}))))
    (is (= {:replacement true} (backend/backend-deref b)))))

(deftest throwing-update-does-not-publish-a-partial-path
  (let [initial {:nodes {}}
        b (backend/create-atom-backend initial)]
    (try
      (backend/backend-write! b [:nodes :missing :value]
                              (fn [_] (throw (ex-info "update failed" {}))))
      (is false "the update must throw")
      (catch #?(:clj Exception :cljs :default) e
        (is (= "update failed" (ex-message e)))))
    (is (= initial (backend/backend-deref b)))))
