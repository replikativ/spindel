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

(deftest an-owned-map-keeps-inherited-entities-the-parents
  ;; GC asks `entity-locality` whether a node is this world's to release; a
  ;; map taken whole from a frozen parent must not make its inherited
  ;; entries this world's own.
  (let [ov (frozen-fork-of parent-state)
        local? #((backend/entity-locality ov) :nodes %)]
    (is (not (local? :a)))
    (backend/backend-write! ov [:nodes :c :v] inc)
    (is (full-replacement? (:nodes @(:overlay-atom ov))))
    (is (local? :c) "written by this world")
    (is (not (local? :a)) "still the parent's")
    (backend/backend-write! ov [] #(assoc-in % [:nodes :b :v] 20))
    (is (local? :b))
    (is (not (local? :a)))
    (is (not (local? :z)) "absent")
    (backend/backend-write! ov [] #(dissoc % :atoms))
    (is ((backend/entity-locality ov) :atoms :s1) "a removed map is this world's")))

(deftest a-removed-map-revived-by-an-entity-write-hides-the-parents
  (doseq [ov [(fork-of parent-state) (frozen-fork-of parent-state)]]
    (backend/backend-write! ov [] #(dissoc % :nodes))
    (backend/backend-write! ov [:nodes :d :v] (constantly 4))
    (is (= {:d {:v 4}} (backend/backend-read ov [:nodes])))
    (is (nil? (backend/backend-read ov [:nodes :a])))))

(deftest overlays-agree-with-a-plain-backend-on-any-sequence-of-writes
  ;; The same seeded writes against an atom backend (the reference) and
  ;; overlays starting from the same state: a fork following a live parent
  ;; and a fork over a frozen parent; halfway, the frozen fork stops taking
  ;; writes and forks of it carry on: one following it, one over a frozen
  ;; snapshot of it, each with its fork-local maps copied as `fork-context`
  ;; copies them. After every write their logical states and entity reads
  ;; agree.
  (let [r (java.util.Random. 42)
        pick (fn [xs] (nth xs (.nextInt r (count xs))))
        ids [:a :b :c :d :e]
        tops [:nodes :atoms :await-conts]
        start (assoc parent-state :await-conts {:a {:k 0}})
        fork-local #(select-keys % [:await-conts])
        write (fn []
                (case (int (.nextInt r 9))
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
                      [[] #(update % t (fn [m] (into {} (take 2) (sort-by key (remove (comp nil? val) m)))))])
                  6 (let [t (pick tops)]
                      [[] #(dissoc % t)])
                  7 (let [t (pick tops) id (pick ids)]
                      [[t id :w] (constantly :w)])
                  8 (let [[pa pb] (repeatedly 2 #(vector (pick tops) (pick ids)))]
                      (when (not= pa pb)
                        [:pair pa pb (fn [a b] [{:v (inc (or (:v a) 0))} b])]))))
        apply! (fn [b [path f & more]]
                 (if (= :pair path)
                   (backend/backend-write-2! b f (first more) (second more))
                   (backend/backend-write! b path f)))
        ;; an entity written nil reads as absent, and so does a map holding
        ;; only such entities: compare what reads return
        logical (fn [state]
                  (into {} (keep (fn [[k v]]
                                   (cond (nil? v) nil
                                         (and (map? v) (not (record? v)))
                                         (when-let [m (not-empty (into {} (remove (comp nil? val)) v))]
                                           [k m])
                                         :else [k v])))
                        state))]
    (doseq [run (range 20)]
      (let [reference (backend/create-atom-backend start)
            following (backend/create-overlay-backend (backend/create-atom-backend start)
                                                      (fork-local start))
            frozen (backend/create-overlay-backend (backend/create-immutable-backend
                                                    (dissoc start :await-conts))
                                                   (fork-local start))
            nested (atom nil)]
        (dotimes [step 60]
          (when (= step 30)
            (let [view (backend/backend-deref frozen)]
              (reset! nested
                      {"following a fork" (backend/create-overlay-backend frozen (fork-local view))
                       "over a frozen fork" (backend/create-overlay-backend
                                             (backend/create-immutable-backend view)
                                             (fork-local view))})))
          (when-let [op (write)]
            (let [overlays (merge {"following" following}
                                  (or @nested {"frozen" frozen}))]
              (apply! reference op)
              (doseq [b (vals overlays)] (apply! b op))
              (let [expected (backend/backend-deref reference)]
                (doseq [[label b] overlays]
                  (is (= (logical expected) (logical (backend/backend-deref b)))
                      (str label ", run " run " step " step))
                  (doseq [t tops id ids]
                    (is (= (get-in expected [t id]) (backend/backend-read b [t id]))
                        (str label ", run " run " step " step " " [t id]))
                    ;; a following fork reads a field its entity lacks
                    ;; through from the parent (addressing cursors rely on
                    ;; it); over a frozen parent the entity is owned whole
                    (when (#{"frozen" "over a frozen fork"} label)
                      (is (= (get-in expected [t id :v]) (backend/backend-read b [t id :v]))
                          (str label ", run " run " step " step " " [t id :v])))))))))))))

(deftest an-initial-entity-is-a-whole-entity
  ;; `fork-context` :state-updates entities replace the parent's; a frozen
  ;; fork that owns the map keeps them whole, whatever else it writes there
  (let [ov (backend/create-overlay-backend
            (backend/create-immutable-backend parent-state)
            {:nodes {:a {:snapshot 99}}})]
    (is (= {:snapshot 99} (backend/backend-read ov [:nodes :a])))
    (backend/backend-write! ov [:nodes :b :v] inc)
    (is (= {:snapshot 99} (backend/backend-read ov [:nodes :a])))
    (is (nil? (backend/backend-read ov [:nodes :a :v])))
    (is (= {:v 3} (backend/backend-read ov [:nodes :b])))))

(deftest a-following-fork-sees-its-parents-later-writes
  (let [parent (backend/create-atom-backend parent-state)
        ov (backend/create-overlay-backend parent {:await-conts {}})]
    (backend/backend-write! ov [] #(assoc-in % [:nodes :a :v] 10))
    (backend/backend-write! ov [:await-conts :k] (constantly 1))
    (backend/backend-write! parent [] #(-> %
                                           (assoc-in [:nodes :b :v] 20)
                                           (assoc-in [:nodes :d] {:v 4})
                                           (assoc-in [:atoms :s3] #{:c})))
    (is (= {:a {:v 10} :b {:v 20} :c {:v 3} :d {:v 4}} (backend/backend-read ov [:nodes])))
    (is (= 20 (backend/backend-read ov [:nodes :b :v])))
    (is (= #{:c} (backend/backend-read ov [:atoms :s3])))
    (is (= {:k 1} (backend/backend-read ov [:await-conts])))
    (is (= (get-in (backend/backend-deref parent) [:nodes :d])
           (get-in (backend/backend-deref ov) [:nodes :d])))))
