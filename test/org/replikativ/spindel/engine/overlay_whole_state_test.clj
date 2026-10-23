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

(deftest materialized-views-follow-both-parent-and-overlay-revisions
  (let [parent (backend/create-atom-backend parent-state)
        ov (backend/create-overlay-backend parent)
        nested (backend/create-overlay-backend ov)]
    (backend/backend-write! ov [:nodes :a :v] (constantly 10))
    (let [first-view (backend/backend-deref nested)]
      (is (identical? first-view (backend/backend-deref nested)))
      (backend/backend-write! parent [:nodes :b :v] (constantly 20))
      (is (= {:a {:v 10} :b {:v 20} :c {:v 3}}
             (:nodes (backend/backend-deref nested)))))
    (let [frozen (backend/create-overlay-backend
                  (backend/create-immutable-backend (backend/backend-deref ov)))]
      (backend/backend-write! ov [] #(update % :nodes dissoc :a))
      (is (nil? (get-in (backend/backend-deref nested) [:nodes :a])))
      (is (= 10 (backend/backend-read frozen [:nodes :a :v])))
      (backend/backend-write-2! ov [:nodes :b :v] [:nodes :c :v]
                                (fn [b c] [(inc b) (inc c)]))
      (is (= {:b {:v 21} :c {:v 4}} (:nodes (backend/backend-deref nested))))
      (backend/backend-write! ov [:nodes :a :v] (constantly 30))
      (is (= 30 (get-in (backend/backend-deref nested) [:nodes :a :v]))))))

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

(def ^:private full-replacement? @#'backend/full-replacement-map?)

(defn- frozen-fork-of [parent-state]
  (backend/create-overlay-backend (backend/create-immutable-backend parent-state)))

(deftest over-a-frozen-parent-a-changed-map-is-written-whole
  (testing "a whole-state transaction replaces the changed map instead of diffing its entities"
    (let [ov (frozen-fork-of parent-state)]
      (backend/backend-write! ov [] #(assoc-in % [:nodes :a :v] 10))
      (is (full-replacement? (:nodes @(:overlay-atom ov))))
      (is (not (contains? @(:overlay-atom ov) :atoms)) "an untouched map stays out")
      (is (= {:a {:v 10} :b {:v 2} :c {:v 3}} (backend/backend-read ov [:nodes])))))
  (testing "a removed entity needs no tombstone: the replacement does not hold it"
    (let [ov (frozen-fork-of parent-state)]
      (backend/backend-write! ov [] #(update % :atoms dissoc :s1))
      (is (= {:s2 #{:b}} (backend/backend-read ov [:atoms])))
      (is (nil? (backend/backend-read ov [:atoms :s1])))
      (is (not (#'backend/tombstones? @(:overlay-atom ov))))))
  (testing "an entity write takes the parent's map as its base"
    (let [ov (frozen-fork-of parent-state)]
      (backend/backend-write! ov [:nodes :b :v] inc)
      (is (full-replacement? (:nodes @(:overlay-atom ov))))
      (is (= {:a {:v 1} :b {:v 3} :c {:v 3}} (backend/backend-read ov [:nodes])))
      (is (= {:v 1} (backend/backend-read ov [:nodes :a])))))
  (testing "a fork following a live parent keeps entity granularity and sees the parent's later writes"
    (let [parent (backend/create-atom-backend parent-state)
          ov (backend/create-overlay-backend parent)]
      (backend/backend-write! ov [] #(assoc-in % [:nodes :a :v] 10))
      (backend/backend-write! ov [:nodes :b :w] (constantly 0))
      (is (not (full-replacement? (:nodes @(:overlay-atom ov)))))
      (backend/backend-write! parent [:nodes :c :v] (constantly 30))
      (is (= {:a {:v 10} :b {:v 2 :w 0} :c {:v 30}} (backend/backend-read ov [:nodes]))))))

(deftest fork-local-maps-are-held-whole-and-read-without-the-marker
  (let [ov (backend/create-overlay-backend (backend/create-atom-backend parent-state)
                                           {:await-conts {:s {:k 1}}})
        seen (atom nil)]
    (is (full-replacement? (:await-conts @(:overlay-atom ov))))
    (is (= {:s {:k 1}} (backend/backend-read ov [:await-conts])))
    (is (nil? (meta (backend/backend-read ov [:await-conts]))))
    (let [returned (backend/backend-write! ov [:await-conts] #(do (reset! seen %) (assoc % :t {:k 2})))]
      (is (nil? (meta @seen)) "f sees the logical value")
      (is (nil? (meta returned)) "so does the caller")
      (is (full-replacement? (:await-conts @(:overlay-atom ov)))))
    (backend/backend-write! ov [:await-conts :u] (constantly {:k 3}))
    (is (full-replacement? (:await-conts @(:overlay-atom ov))))
    (backend/backend-write! ov [] #(update % :await-conts dissoc :s))
    (is (= {:t {:k 2} :u {:k 3}} (backend/backend-read ov [:await-conts])))
    (is (= {:t {:k 2} :u {:k 3}} (:await-conts (backend/backend-deref ov))))))

(deftest overlays-agree-with-a-plain-backend-on-any-sequence-of-writes
  ;; The same seeded writes against an atom backend (the reference), a fork
  ;; following a live parent, and a fork over a frozen parent, all starting
  ;; from one state: their logical states agree after every write.
  (let [r (java.util.Random. 42)
        pick (fn [xs] (nth xs (.nextInt r (count xs))))
        ids [:a :b :c :d :e]
        tops [:nodes :atoms :await-conts]
        start (assoc parent-state :await-conts {:a {:k 0}})
        write (fn []
                (case (int (.nextInt r 6))
                  0 (let [t (pick tops) id (pick ids) v (.nextInt r 9)]
                      [[] #(assoc-in % [t id] {:v v})])
                  1 (let [t (pick tops) id (pick ids)]
                      [[] #(update % t dissoc id)])
                  2 (let [t (pick tops) id (pick ids)]
                      [[t id :v] (fnil inc 0)])
                  3 (let [t (pick tops) id (pick ids)]
                      [[t id] (constantly nil)])
                  4 (let [t (pick tops) id (pick ids)]
                      [[t] #(dissoc % id)])
                  5 (let [t (pick tops)]
                      [[] #(update % t (fn [m] (into {} (take 2) (sort-by key m))))])))]
    (doseq [seed-run (range 20)]
      (let [reference (backend/create-atom-backend start)
            following (backend/create-overlay-backend (backend/create-atom-backend start)
                                                      (select-keys start [:await-conts]))
            frozen (backend/create-overlay-backend (backend/create-immutable-backend
                                                    (dissoc start :await-conts))
                                                   (select-keys start [:await-conts]))]
        (dotimes [step 40]
          (let [[path f] (write)]
            (doseq [b [reference following frozen]] (backend/backend-write! b path f))
            (let [expected (backend/backend-deref reference)
                  ;; an entity written nil reads as absent: compare reads
                  logical (fn [state]
                            (into {} (keep (fn [[k v]]
                                             (cond (nil? v) nil
                                                   (and (map? v) (not (record? v)))
                                                   [k (into {} (remove (comp nil? val)) v)]
                                                   :else [k v])))
                                  state))]
              (is (= (logical expected) (logical (backend/backend-deref following)))
                  (str "following, run " seed-run " step " step " " path))
              (is (= (logical expected) (logical (backend/backend-deref frozen)))
                  (str "frozen, run " seed-run " step " step " " path))
              (doseq [t tops id ids]
                (is (= (get-in expected [t id]) (backend/backend-read frozen [t id])))
                (is (= (get-in expected [t id]) (backend/backend-read following [t id])))))))))))
