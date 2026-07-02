(ns org.replikativ.spindel.distributed.workspace-fork-e2e-test
  "End-to-end coverage for the cross-system fork lifecycle against a REAL yggdrasil
   datahike system (`branch!` / `checkout` / `merge!` / `conflicts`) — the
   real-semantics the mock unit tests cannot exercise. (It was exactly this test's
   territory that caught `merge-fork-remote!` passing a system where yggdrasil's
   `merge!` wants a branch keyword.)

   Single-process: the fork/branch/merge is local to one datahike conn; the
   two-peer FOLLOW-over-kabel path is a separate concern (workspace_peer reseat +
   wire-topology!). JVM-only: datahike.

   Layered on the workspace primitives:
     fork-remote!         → ygg/branch! a fresh writable branch + reseat the peer
     (write on the fork)  → isolated from the parent branch
     merge-fork-remote!   → checkout parent, ygg/merge! the fork branch back in"
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.core.async :refer [<!!]]
            [datahike.api :as d]
            [yggdrasil.adapters.datahike :as dha]
            [yggdrasil.protocols :as p]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.distributed.workspace-peer :as wp]
            [org.replikativ.spindel.distributed.workspace-peer-sync :as sync]))

(defn- item-names
  "All :item/name values currently visible on a datahike conn."
  [conn]
  (set (map first (d/q '[:find ?n :where [?e :item/name ?n]] @conn))))

(deftest test-fork-remote-write-merge-real-datahike
  (testing "fork-remote! branches a real datahike system; edits land on the fork in
            isolation; merge-fork-remote! folds them back into the parent branch"
    (let [cfg {:store {:backend :memory :id (random-uuid)}
               :keep-history?      true
               :schema-flexibility :read}]
      (d/create-database cfg)
      (let [conn (d/connect cfg)
            ctx  (ctx/create-execution-context)]
        (try
          (d/transact conn [{:db/ident :item/name :db/valueType :db.type/string
                             :db/cardinality :db.cardinality/one}])
          (d/transact conn [{:item/name "trunk"}])
          (let [sys           (dha/create conn {:system-name "kb"})
                parent-branch (p/current-branch sys)        ; :db (datahike default)
                parent-head   (p/snapshot-id sys)
                lookup        (fn [_sid] sys)               ; one system in this room
                peer          (wp/make-workspace-peer
                               {:ctx ctx
                                :resolve-system-fn (fn [_sid branch] (p/checkout sys branch))})
                parent-desc   {:branch  parent-branch
                               :owner   :server
                               :systems {"kb" {:branch parent-branch :head parent-head}}}]

            ;; ---- FORK: create :fork-1 locally + re-seat the peer onto it ----
            (let [fork-desc (<!! (sync/fork-remote! peer parent-desc :fork-1 :client lookup))]
              (is (= :fork-1 (:branch fork-desc)))
              (is (= {:branch parent-branch :heads {"kb" parent-head}} (:fork-of fork-desc))
                  ":fork-of anchors the parent branch + head (the merge-base/LCA)")
              (testing "peer re-seated onto the REAL fork branch"
                (is (= :fork-1 (p/current-branch (get (wp/current-workspace peer) "kb")))))

              ;; ---- WRITE on the fork branch — isolated from the parent ----
              (d/transact (:conn (p/checkout sys :fork-1)) [{:item/name "fork-edit"}])
              (testing "the edit is isolated: fork sees both, parent still trunk-only"
                (is (= #{"trunk" "fork-edit"} (item-names (:conn (p/checkout sys :fork-1)))))
                (is (= #{"trunk"} (item-names (:conn (p/checkout sys parent-branch))))))

              ;; ---- MERGE the fork back into the parent branch ----
              (let [res (<!! (sync/merge-fork-remote! fork-desc lookup))]
                (testing "no conflicts; the parent branch now carries the fork's edit"
                  (is (empty? (:conflicts res)))
                  (is (contains? (:merged res) "kb"))
                  (is (= #{"trunk" "fork-edit"}
                         (item-names (:conn (get-in res [:merged "kb"]))))
                      "the merged parent system holds both")
                  (is (= #{"trunk" "fork-edit"}
                         (item-names (:conn (p/checkout sys parent-branch))))
                      "a fresh checkout of the parent branch sees the merge")))))
          (finally
            (ctx/stop-context! ctx)
            (d/release conn)
            (d/delete-database cfg)))))))
