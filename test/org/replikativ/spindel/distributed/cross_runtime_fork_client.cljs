(ns org.replikativ.spindel.distributed.cross-runtime-fork-client
  "cljs(node) side of the cross-runtime FORK/MERGE proof. Connects to the JVM server,
   then runs the FULL async lifecycle on a REAL local datahike (memory) system:
     create+seed (\"trunk\") → fork-remote! :fork-1 → write \"fork-edit\" on the fork
     → merge-fork-remote! → assert the merged parent carries #{trunk fork-edit}.
   The merge runs the async-cljs datahike-adapter `merge!` (writer promise-chan) over a
   live peer connection. On success it publishes the merged item-names over a synced
   G-Set so the JVM server OBSERVES the cljs merge result (client->server). Exits 0 iff
   the cljs merge converged to #{trunk fork-edit}.

   Async style: plain `clojure.core.async/go` driver; superv `<?` for the kabel connect
   (matches the G-Set client), `<?-` for the async datahike ops, and `<!` for the
   fork-remote!/merge-fork-remote! channels (clojure.core.async go-blocks)."
  (:require [kabel.peer :as peer]
            [kabel.pubsub :as pubsub]
            [org.replikativ.spindel.distributed.cross-runtime-fork-common :as c]
            [org.replikativ.spindel.distributed.workspace-peer :as wp]
            [org.replikativ.spindel.distributed.workspace-peer-sync :as fsync]
            [is.simm.partial-cps.core-async :as cps]
            [org.replikativ.spindel.engine.context :as ctx]
            [datahike.api :as d]
            [yggdrasil.adapters.datahike :as dha]
            [yggdrasil.protocols :as p]
            [superv.async :refer [S] :refer-macros [<? <?-]]
            ;; clojure.core.async (NOT cljs.core.async) — superv's macros + datahike's
            ;; channels are clojure.core.async; see cross_runtime_client for the why.
            [clojure.core.async :refer [<! timeout go] :include-macros true]))

(defn- exit! [code msg] (println msg) (js/process.exit code))

(defn- item-names [conn]
  (set (map first (d/q '[:find ?n :where [_ :item/name ?n]] @conn))))

(defn -main [& _]
  (go
    (try
      (let [client (peer/client-peer S c/client-id
                                     (pubsub/make-pubsub-peer-middleware {}) (c/wire-middleware))]
        (<? S (peer/connect S client c/url))
        (<! (timeout 800))
        (let [items-sig (atom (c/mem-gset "client"))]
          (c/sync-items! client items-sig false)
          ;; ---- a REAL local datahike (memory) system ----
          (let [cfg {:store {:backend :memory :id (random-uuid)}
                     :keep-history? true :schema-flexibility :read}]
            (<?- (d/create-database cfg))
            (let [conn (<?- (d/connect cfg {:sync? false}))]
              (<?- (d/transact! conn {:tx-data [{:db/ident :item/name
                                                 :db/valueType :db.type/string
                                                 :db/cardinality :db.cardinality/one}]}))
              (<?- (d/transact! conn {:tx-data [{:item/name "trunk"}]}))
              (let [sys           (dha/create conn {:system-name "kb"})
                    ec            (ctx/create-execution-context)
                    parent-branch (p/current-branch sys)
                    parent-head   (p/snapshot-id sys)
                    lookup        (fn [_sid] sys)
                    peer          (wp/make-workspace-peer
                                   {:ctx ec
                                    :resolve-system-fn (fn [_sid branch] (p/checkout sys branch))})
                    parent-desc   {:branch  parent-branch
                                   :owner   :server
                                   :systems {"kb" {:branch parent-branch :head parent-head}}}
                    ;; ---- FORK locally (async go-block channel) ----
                    fork-desc     (<! (fsync/fork-remote! peer parent-desc :fork-1 :client lookup))]
                (when (instance? js/Error fork-desc)
                  (exit! 4 (str "CLIENT-FAIL fork-remote! threw: " (.-message fork-desc))))
                (println "CLIENT-FORK-DESC-BRANCH" (pr-str (:branch fork-desc)))
                ;; ---- WRITE on the fork (async transact!) ----
                ;; checkout is now async on cljs (partial-cps CPS) → bridge via cps/->chan
                (let [fork-sys (cps/unwrap-result (<! (cps/->chan (p/checkout sys :fork-1))))]
                  (<?- (d/transact! (:conn fork-sys)
                                    {:tx-data [{:item/name "fork-edit"}]})))
                ;; ---- MERGE the fork back (the async-cljs merge! writer path) ----
                (let [res        (<! (fsync/merge-fork-remote! fork-desc lookup))
                      merged-sys (get-in res [:merged "kb"])
                      names      (when merged-sys (item-names (:conn merged-sys)))]
                  (when (:error res) (println "CLIENT-MERGE-ERROR" (str (:error res))))
                  (println "CLIENT-MERGE-CONFLICTS" (pr-str (:conflicts res)))
                  (println "CLIENT-MERGED-NAMES" (pr-str names))
                  (if (= #{"trunk" "fork-edit"} names)
                    (do
                      ;; publish the merged names so the JVM peer observes the cljs result
                      (doseq [n names] (c/add-item! items-sig n))
                      (<! (timeout 1500))
                      (exit! 0 "CLIENT-OK fork+write+merge converged-to-trunk+fork-edit"))
                    (exit! 1 (str "CLIENT-FAIL merged-names=" (pr-str names))))))))))
      (catch :default e
        (println "CLIENT-ERROR" (str e))
        (println "STACK" (.-stack e))
        (js/process.exit 3)))))
