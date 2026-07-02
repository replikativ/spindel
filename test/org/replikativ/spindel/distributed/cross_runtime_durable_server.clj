(ns org.replikativ.spindel.distributed.cross-runtime-durable-server
  "JVM side of the DURABLE cross-runtime proof: a kabel server holding a FILE-backed
   G-Set `#{:alpha :beta}`, exposing its NODES over konserve-sync + its VALUE (the CRDT
   root, `ygg/system`) over signal-sync, on ONE fressian serializer. `-main` starts it
   and stays up until killed; the node client does the asserting + cold restart."
  (:require [clojure.java.io :as io]
            [kabel.peer :as peer]
            [kabel.http-kit :as http-kit]
            [kabel.pubsub :as pubsub]
            [konserve-sync.core :as ks]
            [org.replikativ.spindel.distributed.signal-sync :as ss]
            [org.replikativ.spindel.distributed.cross-runtime-durable-common :as c]
            [superv.async :refer [S <??]]
            [yggdrasil.convergent.gset :as g]))

(defn- rm-rf [path]
  (let [d (io/file path)]
    (when (.exists d) (doseq [f (reverse (file-seq d))] (.delete f)))))

(defn -main [& _]
  (rm-rf c/server-path)
  ;; conj AUTO-FLUSHES → the G-Set is committed to its file store (sendable root).
  (let [s-gset  (-> (g/gset c/gid {:store-config {:backend :file :path c/server-path :id (random-uuid)}} {:sync? true})
                    (g/conj :alpha) (g/conj :beta))
        s-store (:kv-store s-gset)
        s-sig   (atom s-gset)
        handler (http-kit/create-http-kit-handler! S c/url c/server-id)
        server  (peer/server-peer S handler c/server-id
                                  (pubsub/make-pubsub-peer-middleware {})
                                  (c/wire-middleware (:storage s-gset)))]
    (<?? S (peer/start server))
    (ks/register-store! server c/store-topic s-store c/nodes-only-opts)  ; NODES
    (ss/export-signal! server c/value-topic s-sig)                       ; VALUE (ygg/system)
    (println "XRT-DUR-SERVER-UP" c/url (pr-str (g/elements s-gset)))
    (flush)
    (loop [] (Thread/sleep 1000) (recur))))
