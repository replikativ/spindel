(ns org.replikativ.spindel.distributed.workspace-peer-test
  "Tests for the workspace-peer pure gate + re-seat state machine.
   CLJ-only: exercises a real execution context (ec/swap-state! / get-state)."
  #?(:clj
     (:require [clojure.test :refer [deftest testing is]]
               [org.replikativ.spindel.engine.context :as ctx]
               [org.replikativ.spindel.distributed.workspace-peer :as wp])
     :cljs
     (:require [cljs.test :refer-macros [deftest testing is]])))

#?(:clj
   (do
     (defn- descriptor [branch sys->head]
       {:branch branch
        :systems (into {} (map (fn [[sid head]]
                                 [sid {:store-id sid :branch branch :head head}]))
                       sys->head)})

     ;; resolve-system-fn: a branch-scoped sub-system stand-in we can assert on.
     (defn- resolve-sys [sid branch] {:sid sid :branch branch})

     ;; ----------------------------------------------------------------------
     ;; Pure gate
     ;; ----------------------------------------------------------------------

     (deftest test-gate-not-ready-until-all-heads-reached
       (let [desc (descriptor :main {"kb" "c1" "msgs" "c2"})]
         (testing "no heads synced → not ready, both pending"
           (let [g (wp/gate desc {})]
             (is (not (:ready? g)))
             (is (= #{"kb" "msgs"} (:pending g)))))
         (testing "one head synced → still not ready"
           (let [hs (wp/merge-head-update {} "kb" :main "c1")
                 g (wp/gate desc hs)]
             (is (not (:ready? g)))
             (is (= #{"msgs"} (:pending g)))
             (is (true? (get-in g [:statuses "kb" :reached?])))))
         (testing "both heads synced → ready"
           (let [hs (-> {}
                        (wp/merge-head-update "kb" :main "c1")
                        (wp/merge-head-update "msgs" :main "c2"))
                 g (wp/gate desc hs)]
             (is (:ready? g))
             (is (empty? (:pending g)))))
         (testing "stale head on the wrong branch does NOT satisfy the gate"
           (let [hs (wp/merge-head-update {} "kb" :other "c1")
                 g (wp/gate desc hs)]
             (is (= #{"kb" "msgs"} (:pending g)))))
         (testing "empty descriptor is never ready (nothing to expose)"
           (is (not (:ready? (wp/gate {:systems {}} {})))))))

     ;; ----------------------------------------------------------------------
     ;; Peer re-seat
     ;; ----------------------------------------------------------------------

     (deftest test-peer-reseats-only-when-gated
       (let [ctx (ctx/create-execution-context)
             reseats (atom [])
             peer (wp/make-workspace-peer
                   {:ctx ctx
                    :resolve-system-fn resolve-sys
                    :on-reseat (fn [ws desc] (swap! reseats conj [ws desc]))})
             desc (descriptor :main {"kb" "c1" "msgs" "c2"})]
         (testing "setting the descriptor with no heads does not seat the workspace"
           (let [g (wp/set-descriptor! peer desc)]
             (is (false? (:reseated? g)))
             (is (nil? (wp/current-workspace peer)))))
         (testing "first head arriving is not enough"
           (let [g (wp/apply-head-update! peer "kb" :main "c1")]
             (is (false? (:reseated? g)))
             (is (nil? (wp/current-workspace peer)))))
         (testing "second head completes the gate → workspace seated, branch-correct"
           (let [g (wp/apply-head-update! peer "msgs" :main "c2")]
             (is (true? (:reseated? g)))
             (is (= {"kb" {:sid "kb" :branch :main}
                     "msgs" {:sid "msgs" :branch :main}}
                    (wp/current-workspace peer)))
             (is (= 1 (count @reseats)))))
         (testing "no spurious re-seat when an already-seated head re-fires"
           (let [g (wp/apply-head-update! peer "kb" :main "c1")]
             (is (false? (:reseated? g)))
             (is (= 1 (count @reseats)))))))

     ;; ----------------------------------------------------------------------
     ;; Single-writer lease
     ;; ----------------------------------------------------------------------

     (deftest test-single-writer-lease
       (testing "writable? only for the descriptor's :owner"
         (is (true? (wp/writable? {:owner :peer-a} :peer-a)))
         (is (false? (wp/writable? {:owner :peer-a} :peer-b))))
       (testing "no :owner ⇒ read-only for everyone (fork to write)"
         (is (false? (wp/writable? {} :peer-a)))
         (is (false? (wp/writable? {:owner :peer-a} nil))))
       (testing "claim stamps the owner; peer-writable? reads through the peer"
         (let [d (wp/claim (descriptor :fork {"kb" "c1"}) :peer-a)]
           (is (= :peer-a (:owner d)))
           (let [peer (wp/make-workspace-peer
                       {:ctx (ctx/create-execution-context)
                        :resolve-system-fn resolve-sys})]
             (wp/set-descriptor! peer d)
             (is (true? (wp/peer-writable? peer :peer-a)))
             (is (false? (wp/peer-writable? peer :peer-b)))))))

     ;; ----------------------------------------------------------------------
     ;; Fork lineage (pure descriptor algebra)
     ;; ----------------------------------------------------------------------

     (deftest test-fork-descriptor
       (testing "fork-descriptor re-points systems to the fork branch, claims the
                 owner, and anchors :fork-of to the parent's per-system heads"
         (let [parent (-> (descriptor :main {"kb" "c1" "msgs" "c2"})
                          (assoc :descriptor-topic :room/foo)
                          (assoc-in [:systems "kb" :topic] :room/foo-kb)
                          (assoc-in [:systems "msgs" :topic] :room/foo-msgs))
               fork   (wp/fork-descriptor parent :fork-1 :peer-a)]
           (is (= :fork-1 (:branch fork)))
           (is (= :peer-a (:owner fork)))
           (testing ":fork-of anchors the parent branch + per-system base heads (LCA)"
             (is (= {:branch :main :heads {"kb" "c1" "msgs" "c2"}} (:fork-of fork))))
           (testing "each system re-pointed to the fork branch; head + store topic carried over"
             (is (= :fork-1 (get-in fork [:systems "kb" :branch])))
             (is (= "c1" (get-in fork [:systems "kb" :head]))
                 "head stays at the parent (the fork starts there — structural sharing)")
             (is (= :room/foo-kb (get-in fork [:systems "kb" :topic])) "store topic preserved"))
           (testing "descriptor-topic preserved"
             (is (= :room/foo (:descriptor-topic fork))))
           (testing "a peer seated on the fork descriptor is writable only by the claimed owner"
             (let [peer (wp/make-workspace-peer
                         {:ctx (ctx/create-execution-context) :resolve-system-fn resolve-sys})]
               (wp/set-descriptor! peer fork)
               (is (true? (wp/peer-writable? peer :peer-a)))
               (is (false? (wp/peer-writable? peer :peer-b))))))))

     (deftest test-peer-swaps-to-fork-snapshot-isolated
       (testing "server forks the room → client re-seats to the fork branch only
                 once the fork's heads are local (the coordinated-fork swap)"
         (let [ctx (ctx/create-execution-context)
               peer (wp/make-workspace-peer
                     {:ctx ctx :resolve-system-fn resolve-sys})]
           ;; start seated on :main
           (wp/set-descriptor! peer (descriptor :main {"kb" "c1" "msgs" "c2"}))
           (wp/apply-head-update! peer "kb" :main "c1")
           (wp/apply-head-update! peer "msgs" :main "c2")
           (is (= :main (get-in (wp/current-workspace peer) ["kb" :branch])))

           ;; server forks → new descriptor names :fork at new heads
           (let [g (wp/set-descriptor! peer (descriptor :fork {"kb" "f1" "msgs" "f2"}))]
             (testing "fork blocks not yet synced → workspace stays on :main"
               (is (false? (:reseated? g)))
               (is (= :main (get-in (wp/current-workspace peer) ["kb" :branch])))))

           ;; fork heads land (key-sort-fn gated: blocks-then-pointer)
           (wp/apply-head-update! peer "kb" :fork "f1")
           (let [g (wp/apply-head-update! peer "msgs" :fork "f2")]
             (testing "both fork heads local → swap to the fork, isolated"
               (is (true? (:reseated? g)))
               (is (= {"kb" {:sid "kb" :branch :fork}
                       "msgs" {:sid "msgs" :branch :fork}}
                      (wp/current-workspace peer))))))))))
