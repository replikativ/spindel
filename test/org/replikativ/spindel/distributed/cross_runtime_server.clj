(ns org.replikativ.spindel.distributed.cross-runtime-server
  "JVM side of the cross-runtime bidirectional sync proof: a kabel server holding a
   G-Set (contributing :jvm), synced as the topic owner. `-main` runs it, polls its
   own G-Set, and exits 0 the moment the cljs(node) client's :cljs arrives over the
   wire (proving client->server), or 2 on timeout."
  (:require [kabel.peer :as peer]
            [kabel.http-kit :as http-kit]
            [kabel.pubsub :as pubsub]
            [org.replikativ.spindel.distributed.cross-runtime-common :as c]
            [yggdrasil.convergent.gset :as g]
            [superv.async :refer [S <??]]))

(defonce state (atom nil))

(defn start! []
  (let [handler (http-kit/create-http-kit-handler! S c/url c/server-id)
        server  (peer/server-peer S handler c/server-id
                                  (pubsub/make-pubsub-peer-middleware {}) (c/wire-middleware))
        sig     (atom (c/mem-gset "server"))]
    (<?? S (peer/start server))
    (c/sync-gset! server sig true)
    (c/add! sig :jvm)                        ; the JVM peer contributes :jvm
    (reset! state {:server server :sig sig})
    server))

(defn elements [] (when-let [{:keys [sig]} @state] (c/els sig)))

(defn stop! []
  (when-let [{:keys [server]} @state] (<?? S (peer/stop server)))
  (reset! state nil))

(defn -main [& _]
  (start!)
  (println "CROSS-RUNTIME-SERVER-UP" c/url)
  (flush)
  (loop [n 0]
    (let [els (elements)]
      (cond
        (contains? els :cljs)
        (do (println "SERVER-GOT-CLJS" (pr-str els)) (flush) (stop!) (System/exit 0))

        (> n 60)
        (do (println "SERVER-TIMEOUT" (pr-str els)) (flush) (stop!) (System/exit 2))

        :else
        (do (Thread/sleep 500) (recur (inc n)))))))
