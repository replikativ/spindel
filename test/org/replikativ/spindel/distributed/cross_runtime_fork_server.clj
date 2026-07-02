(ns org.replikativ.spindel.distributed.cross-runtime-fork-server
  "JVM side of the cross-runtime FORK/MERGE proof: a kabel pubsub server that owns the
   merged-item-names G-Set. It does NO datahike work itself — it just observes, over
   the wire, the item-names the cljs(node) peer produced by running fork-remote! →
   write → merge-fork-remote! against its own local datahike. `-main` exits 0 the
   moment the server's G-Set carries BOTH \"trunk\" and \"fork-edit\" (proving the cljs
   fork/merge lifecycle ran and its result reached the JVM peer), or 2 on timeout."
  (:require [kabel.peer :as peer]
            [kabel.http-kit :as http-kit]
            [kabel.pubsub :as pubsub]
            [org.replikativ.spindel.distributed.cross-runtime-fork-common :as c]
            [superv.async :refer [S <??]]))

(defonce state (atom nil))

(defn start! []
  (let [handler (http-kit/create-http-kit-handler! S c/url c/server-id)
        server  (peer/server-peer S handler c/server-id
                                  (pubsub/make-pubsub-peer-middleware {}) (c/wire-middleware))
        sig     (atom (c/mem-gset "server"))]
    (<?? S (peer/start server))
    (c/sync-items! server sig true)
    (reset! state {:server server :sig sig})
    server))

(defn items [] (when-let [{:keys [sig]} @state] (c/items sig)))

(defn stop! []
  (when-let [{:keys [server]} @state] (<?? S (peer/stop server)))
  (reset! state nil))

(defn -main [& _]
  (start!)
  (println "CROSS-RUNTIME-FORK-SERVER-UP" c/url)
  (flush)
  (loop [n 0]
    (let [els (items)]
      (cond
        (and (contains? els "trunk") (contains? els "fork-edit"))
        (do (println "SERVER-GOT-MERGE" (pr-str els)) (flush) (stop!) (System/exit 0))

        (> n 90)
        (do (println "SERVER-TIMEOUT" (pr-str els)) (flush) (stop!) (System/exit 2))

        :else
        (do (Thread/sleep 500) (recur (inc n)))))))
