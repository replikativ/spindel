(ns org.replikativ.spindel.v2.yggdrasil-transfer-test
  "Transfer and partition of a settlement record (F3; simmis proposals), on
   forks whose runtime has ended. Ports of the dvergr adoption cases
   (peer_bus_review_test, fork_retention_test, settlement_truth_test) and
   of the old layer's partition tests, at the layer's level: room fences,
   durable rows and compensation stay dvergr's (decision D1: the caller
   persists and compensates around the call; leaf ids are deterministic)."
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.ygg-support :as s
             :refer [caught close-world! dh-system done! eventually put! root st val-in with-stores]]
            [org.replikativ.spindel.v2.yggdrasil :as ygg]))

(defn- reviewed-fork
  "A fork of `w` that wrote `:x` in each system, closed (a Run world after
   its join)."
  [w sids & [opts]]
  (let [f (ygg/fork! w (or opts {}))]
    (doseq [sid sids] (put! (ygg/system (:world f) sid) :x (str "child-" sid)))
    (close-world! (:world f))
    f))

(defmacro with-manual-executor
  "Runs `body` with the layer's lifecycle work queued in `q` (run it with
   `run-queued!`), so a test can observe the state before it runs."
  [q & body]
  `(let [~q (atom [])]
     (ygg/set-executor! (fn [f#] (swap! ~q conj f#)))
     (try ~@body
          (finally (ygg/set-executor! (fn [f#] (future-call f#) nil))))))

(defn- run-queued! [q]
  (let [[fs _] (swap-vals! q (constantly []))]
    (doseq [f fs] (f))))

(deftest a-transfer-moves-the-authority-affinely
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          rows (atom [])
          f (reviewed-fork w ["kb"] {:meta {:room :fork} :journal #(swap! rows conj %)})
          settled (atom [])]
      (is (identical? f (ygg/transfer! f :proposal {:on-settled #(swap! settled conj %)})))
      (is (= [:transferred :transferred :proposal] ((juxt :event :status :owner) (last @rows)))
          "the journal sees the move")
      (is (= [:transferred :proposal {:room :fork}] ((juxt :status :owner :meta) (ygg/describe f))))
      (is (identical? f (ygg/transfer! f :proposal {})) "repeating the transfer is a no-op")
      (testing "only the owner settles it"
        (is (= ::ygg/not-owner (caught #(ygg/merge! f {}))) "NEGATIVE: the old authority merged")
        (is (= ::ygg/not-owner (caught #(ygg/discard! f {:owner :intruder}))))
        (is (= ::ygg/not-owner (caught #(ygg/transfer! f :other {}))))
        (is (= :transferred (st f)))
        (is (= :merged (:status (ygg/merge! f {:owner :proposal}))))
        (is (= "child-kb" (val-in kb :x)))
        (is (= [{:fork/id (:id f) :status :merged :reason nil}] @settled) "the standing hook heard the outcome"))
      (is (= ::ygg/invalid-owner (caught #(ygg/transfer! (reviewed-fork w ["kb"]) nil {}))))
      (done! w))))

(deftest a-transfer-needs-an-ended-runtime
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          f (ygg/fork! w {})]
      (is (= ::ygg/runtime-live (caught #(ygg/transfer! f :owner {}))))
      (is (= ::ygg/runtime-live (caught #(ygg/partition! f {:all #{"kb"}} {}))))
      (is (= [:open nil] ((juxt :status :owner) (ygg/status f))))
      (close-world! (:world f))
      (ygg/transfer! f :owner {})
      (is (= :transferred (st f)))
      (ygg/discard! f {:owner :owner})
      (done! w))))

(deftest the-claim-fences-the-fork-while-settling
  (with-stores
    (let [w (root [(dh-system "kb")])
          f (reviewed-fork w ["kb"])
          seen (atom nil)]
      (is (= ::ygg/refused
             (caught #(ygg/merge! f {:precheck (fn [_]
                                                 (reset! seen
                                                         {:discard (caught (fn [] (ygg/discard! f {})))
                                                          :transfer (caught (fn [] (ygg/transfer! f :other {})))
                                                          :partition (caught (fn [] (ygg/partition! f {:a #{"kb"}} {})))
                                                          :fork (caught (fn [] (ygg/fork! (:world f) {})))
                                                          :register (caught (fn [] (ygg/register! (:world f) (dh-system "late") {})))})
                                                 false)}))))
      (is (= {:discard ::ygg/settling :transfer ::ygg/settling :partition ::ygg/settling
              :fork ::ygg/fork-not-open :register ::ygg/fork-not-open}
             @seen))
      (is (= :open (st f)) "the refused merge let go of the claim")
      (ygg/discard! f {})
      (done! w))))

(deftest concurrent-transfers-have-one-winner
  (with-stores
    (let [w (root [(dh-system "kb")])
          f (reviewed-fork w ["kb"])
          start (java.util.concurrent.CountDownLatch. 1)
          go (fn [owner] (future (.await start)
                                 (try (ygg/transfer! f owner {}) owner
                                      (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
          rs [(go :a) (go :b)]]
      (.countDown start)
      (let [rs (mapv #(deref % 5000 ::timeout) rs)
            winners (filter #{:a :b} rs)]
        (is (= 1 (count winners)))
        (is (every? #{::ygg/settling ::ygg/not-owner} (remove #{:a :b} rs)))
        (is (= (first winners) (:owner (ygg/status f))))
        (ygg/discard! f {:owner (first winners)}))
      (done! w))))

(deftest a-transfer-after-the-parent-ended-is-refused-and-discarded
  (with-stores
    (with-manual-executor q
      (let [w (root [(dh-system "kb")])
            hook (atom nil)
            f (reviewed-fork w ["kb"] {:on-discard #(reset! hook %)})]
        (done! w)
        (let [e (try (ygg/transfer! f :owner {}) nil (catch clojure.lang.ExceptionInfo e e))]
          (is (= [::ygg/refused :parent-ended] ((juxt :type :reason) (ex-data e)))))
        (is (= :open (st f)) "the caller compensates its own row; the record is as before")
        (run-queued! q)
        (run-queued! q)
        (is (= :discarded (st f)))
        (is (= :parent-ended (:reason @hook)))))))

(deftest a-governed-settlement-is-decided-once
  (with-stores
    (let [w (root [(dh-system "kb")])
          f (reviewed-fork w ["kb"])
          _ (ygg/transfer! f :governance {})
          start (java.util.concurrent.CountDownLatch. 1)
          prechecks (atom 0)
          decide (fn [op]
                   (future
                     (.await start)
                     (try (case op
                            :merge (ygg/merge! f {:owner :governance :precheck (fn [_] (swap! prechecks inc) true)})
                            :discard (ygg/discard! f {:owner :governance}))
                          (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
          results [(decide :merge) (decide :discard)]]
      (.countDown start)
      (let [rs (mapv #(deref % 5000 ::timeout) results)
            winners (filter map? rs)
            losers (remove map? rs)]
        (is (= 1 (count winners)))
        (is (every? #{::ygg/settling ::ygg/settled} losers))
        (is (<= @prechecks 1))
        (is (#{:merged :discarded} (st f))))
      (done! w))))

(deftest a-failed-settlement-hook-keeps-the-outcome
  (with-stores
    (let [w (root [(dh-system "kb")])
          f (reviewed-fork w ["kb"])
          calls (atom 0)
          settled (atom 0)]
      (ygg/transfer! f :governance {:on-settled (fn [_] (swap! settled inc))})
      (let [res (ygg/discard! f {:owner :governance
                                 :on-discard (fn [_] (when (= 1 (swap! calls inc))
                                                       (throw (ex-info "terminal store unavailable" {}))))})]
        (is (= [:discarded :failed] ((juxt :status :hook-status) res)))
        (is (zero? @settled) "the standing hook waits for the one before it"))
      (is (= ::ygg/settled (caught #(ygg/merge! f {:owner :governance}))))
      (is (= ::ygg/not-owner (caught #(ygg/recover! f))))
      (is (= [:discarded :completed] ((juxt :status :hook-status) (ygg/recover! f {:owner :governance}))))
      (is (= [2 1] [@calls @settled]) "each hook completed once")
      (done! w))))

(deftest a-refused-governed-merge-stays-with-its-owner
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          f (reviewed-fork w ["kb"])]
      (ygg/transfer! f :governance {})
      (is (= ::ygg/refused (caught #(ygg/merge! f {:owner :governance :precheck (constantly false)}))))
      (is (= [:transferred :governance] ((juxt :status :owner) (ygg/status f))))
      (is (nil? (val-in kb :x)))
      (is (= ::ygg/not-owner (caught #(ygg/discard! f {}))))
      (is (= :discarded (:status (ygg/discard! f {:owner :governance}))))
      (done! w))))

(deftest a-parent-with-unsettled-forks-cannot-transfer
  (with-stores
    (with-manual-executor q
      (let [w (root [(dh-system "kb")])
            f1 (ygg/fork! w {})
            f2 (ygg/fork! (:world f1) {})]
        (close-world! (:world f1))
        (is (= :open (st f2)) "the parent-ended discard has not run yet")
        (is (= ::ygg/open-children (caught #(ygg/transfer! f1 :owner {}))))
        (is (= :open (st f1)))
        (run-queued! q)
        (is (= :discarded (st f2)))
        (ygg/transfer! f1 :owner {})
        (is (= :transferred (st f1)))
        (ygg/discard! f1 {:owner :owner})
        (done! w)
        (run-queued! q)))))

(deftest a-transferred-fork-blocks-its-parent-until-settled
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          f1 (ygg/fork! w {})
          f2 (reviewed-fork (:world f1) ["kb"])]
      (ygg/transfer! f2 :child-owner {})
      (is (= ::ygg/open-children (caught #(ygg/merge! f1 {}))))
      (testing "the owner hands it on; the old owner is stale"
        (ygg/transfer! f2 :successor {:owner :child-owner})
        (is (= ::ygg/not-owner (caught #(ygg/discard! f2 {:owner :child-owner}))))
        (is (= :merged (:status (ygg/merge! f2 {:owner :successor})))))
      (is (= "child-kb" (val-in (ygg/system (:world f1) "kb") :x)))
      (is (= :merged (:status (ygg/merge! f1 {}))))
      (is (= "child-kb" (val-in kb :x)))
      (done! w))))

(deftest an-incomplete-fork-cannot-transfer
  (with-stores
    (let [w (root [(dh-system "one") {:meta {:merge-rank 0}}] [(dh-system "two") {:meta {:merge-rank 1}}])
          f (reviewed-fork w ["one" "two"])
          late? (atom true)]
      (is (= ::ygg/incomplete
             (caught #(ygg/merge! f {:guard (fn [sid _] (when (and @late? (= "two" sid)) (throw (ex-info "late" {}))))}))))
      (is (= ::ygg/fork-not-open (caught #(ygg/transfer! f :review {}))))
      (is (= ::ygg/fork-not-open (caught #(ygg/partition! f {:a #{"one" "two"}} {}))))
      (is (= :incomplete (st f)))
      (reset! late? false)
      (is (= :merged (:status (ygg/recover! f))))
      (done! w))))

(deftest a-transferred-fork-keeps-its-stores-until-settled
  (doseq [op [:merge :discard]]
    (testing (name op)
      (with-stores
        (let [w (root [(dh-system "kb")])
              f (reviewed-fork w ["kb"])]
          (ygg/transfer! f :owner {})
          (is (some? (ygg/fork-of (:world f))) "a transfer keeps the fork's holder")
          (is (= #{"kb"} (set (keys (ygg/diff f)))))
          (case op
            :merge (ygg/merge! f {:owner :owner})
            :discard (ygg/discard! f {:owner :owner}))
          (is (nil? (ygg/fork-of (:world f))) "NEGATIVE: the settled fork's holder remains")
          (done! w))))))

(deftest a-partition-splits-into-named-exhaustive-leaves-that-settle-once
  (with-stores
    (let [kb (dh-system "kb")
          data (dh-system "data")
          w (root [kb] [data])
          rows (atom [])
          f (reviewed-fork w ["kb" "data"] {:meta {:room :proposal} :journal #(swap! rows conj %)})
          spec {:accepted #{"kb"} :dismissed #{"data"}}]
      (ygg/transfer! f :proposal {})
      (let [{:keys [accepted dismissed] :as leaves} (ygg/partition! f spec {:owner :proposal})]
        (is (= (ygg/leaf-id (:id f) :accepted) (:id accepted)) "the caller can name a leaf before the split")
        (is (= #{(:id accepted) (:id dismissed)} (:leaves (ygg/describe f))))
        (is (= #{[:created (:id accepted)] [:created (:id dismissed)]}
               (set (keep #(when (:partition-of %) [(:event %) (:fork/id %)]) @rows))))
        (is (= :partitioned (st f)))
        (is (= ::ygg/partitioned (caught #(ygg/merge! f {:owner :proposal}))))
        (is (every? #(and (= :transferred (st %)) (identical? (:world f) (:world %))) (vals leaves))
            "each leaf is a Fork of the same world with the owner's authority")
        (testing "a retried split returns the same leaves; another split is refused"
          (is (= (into {} (map (fn [[k v]] [k (:id v)])) leaves)
                 (into {} (map (fn [[k v]] [k (:id v)])) (ygg/partition! f spec {:owner :proposal}))))
          (is (= ::ygg/not-owner (caught #(ygg/partition! f spec {}))))
          (is (= ::ygg/partitioned (caught #(ygg/partition! f {:all #{"kb" "data"}} {:owner :proposal})))))
        (is (= #{"kb"} (set (keys (ygg/diff accepted)))) "a leaf sees its systems only")
        (is (= ::ygg/not-owner (caught #(ygg/merge! accepted {}))))
        (is (= :merged (:status (ygg/merge! accepted {:owner :proposal}))))
        (is (= "child-kb" (val-in kb :x)))
        (is (nil? (val-in data :x)) "NEGATIVE: settling a leaf merged a sibling's system")
        (is (= ::ygg/settled (caught #(ygg/discard! accepted {:owner :proposal}))))
        (is (= :merged (st (:accepted (ygg/partition! f spec {:owner :proposal}))))
            "a retry after a leaf settled returns it as settled")
        (is (some? (ygg/fork-of (:world f))) "an open sibling keeps the world's stores")
        (is (= #{"data"} (set (keys (ygg/diff dismissed)))))
        (is (= :discarded (:status (ygg/discard! dismissed {:owner :proposal}))))
        (is (nil? (val-in data :x)))
        (is (nil? (ygg/fork-of (:world f))) "every leaf settled: the record and holder go"))
      (done! w))))

(deftest invalid-partitions-change-nothing
  (with-stores
    (let [w (root [(dh-system "kb")] [(dh-system "data")])
          f (reviewed-fork w ["kb" "data"])]
      (is (= ::ygg/overlapping-partition (caught #(ygg/partition! f {:a #{"kb"} :b #{"kb" "data"}} {}))))
      (is (= ::ygg/incomplete-partition (caught #(ygg/partition! f {:a #{"kb"} :b #{:unknown}} {}))))
      (is (= ::ygg/incomplete-partition (caught #(ygg/partition! f {:a #{"kb"}} {}))))
      (is (= ::ygg/invalid-partition (caught #(ygg/partition! f {:a #{"kb" "data"} :b #{}} {}))))
      (is (= ::ygg/invalid-partition (caught #(ygg/partition! f {} {}))))
      (is (= :open (st f)))
      (testing "a single exhaustive leaf is a split too"
        (let [{:keys [all]} (ygg/partition! f {:all #{"kb" "data"}} {})]
          (is (= :partitioned (st f)))
          (is (= :open (st all)))
          (ygg/discard! all {})))
      (done! w))))

(deftest a-leaf-can-be-transferred-and-partitioned-again
  (with-stores
    (let [w (root [(dh-system "a")] [(dh-system "b")] [(dh-system "c")])
          f (reviewed-fork w ["a" "b" "c"])
          {:keys [ab c]} (ygg/partition! f {:ab #{"a" "b"} :c #{"c"}} {})]
      (ygg/transfer! ab :reviewer {})
      (let [{:keys [a b]} (ygg/partition! ab {:a #{"a"} :b #{"b"}} {:owner :reviewer})]
        (is (= (ygg/leaf-id (:id ab) :a) (:id a)))
        (is (= ::ygg/incomplete-partition (caught #(ygg/partition! c {:x #{"a" "c"}} {}))))
        (ygg/merge! a {:owner :reviewer})
        (ygg/discard! b {:owner :reviewer})
        (is (= :partitioned (st ab)))
        (is (some? (ygg/fork-of (:world f))) "the leaf c is unsettled")
        (ygg/discard! c {})
        (is (nil? (ygg/fork-of (:world f)))))
      (done! w))))

(deftest the-descriptor-is-plain-data
  (with-stores
    (let [w (root [(dh-system "kb")] [(dh-system "data")])
          f (reviewed-fork w ["kb"] {:meta {:room "r" :run 7}})
          _ (ygg/transfer! f :proposal {})
          {:keys [a]} (ygg/partition! f {:a #{"kb"} :b #{"data"}} {:owner :proposal})]
      (doseq [x [f a]]
        (let [d (ygg/describe x)]
          (is (= d (edn/read-string (pr-str d))) "round-trips as EDN")
          (is (= [(v2/world-id w) (v2/world-id (:world f))] ((juxt :parent-world-id :child-world-id) d)))
          (is (= {:room "r" :run 7} (:meta d)))))
      (is (= [(:id f) :a #{"kb"} :proposal] ((juxt :partition-of :leaf :systems :owner) (ygg/describe a))))
      (is (= {:a #{"kb"} :b #{"data"}} (:leaf-spec (ygg/describe f))))
      (is (keyword? (get-in (ygg/describe a) [:locators "kb" :branch])))
      (done! w))))

(deftest the-end-of-the-parents-world-dismisses-adopted-records
  (with-stores
    (let [w (root [(dh-system "kb")] [(dh-system "data")])
          dismissed (atom #{})
          settled (atom #{})
          hook (fn [tag] #(swap! dismissed conj [tag (:reason %)]))
          note (fn [tag] #(swap! settled conj [tag (:status %) (:reason %) (:leaf %)]))
          t (reviewed-fork w ["kb"])
          p (reviewed-fork w ["kb" "data"])
          _ (ygg/transfer! t :proposal {:on-discard (hook :transferred) :on-settled (note :transferred)})
          {:keys [a b]} (ygg/partition! p {:a #{"kb"} :b #{"data"}} {:on-discard (hook :leaf) :on-settled (note :leaf)})]
      (ygg/merge! a {})
      (done! w)
      (is (eventually #(and (= :discarded (st t)) (= :discarded (st b)))))
      (is (= #{[:transferred :parent-ended] [:leaf :parent-ended]} (eventually #(when (= 2 (count @dismissed)) @dismissed))))
      (is (= #{[:transferred :discarded :parent-ended nil] [:leaf :merged nil :a] [:leaf :discarded :parent-ended :b]}
             (eventually #(when (= 3 (count @settled)) @settled)))
          "NEGATIVE: the owner was not told of the parent-ended discard (P2)")
      (is (= :merged (st a)))
      (is (eventually #(nil? (ygg/fork-of (:world p))))))))
