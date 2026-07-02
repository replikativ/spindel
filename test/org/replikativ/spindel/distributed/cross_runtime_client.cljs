(ns org.replikativ.spindel.distributed.cross-runtime-client
  "cljs(node) side of the cross-runtime bidirectional sync proof: a kabel node client
   (kabel.client.cljs over the `websocket` npm package) connects to the JVM server,
   receives :jvm via the convergent handshake (proving server->client), contributes
   :cljs (which the server applies — proving client->server), and exits 0 iff its own
   G-Set converged to #{:jvm :cljs}. The convergent apply runs `:sync? false` (async
   over konserve's core.async memory store) — the genuine cljs async path."
  (:require [kabel.peer :as peer]
            [kabel.pubsub :as pubsub]
            [org.replikativ.spindel.distributed.cross-runtime-common :as c]
            [yggdrasil.convergent.gset :as g]
            [superv.async :refer [S] :refer-macros [<?]]
            ;; clojure.core.async (NOT cljs.core.async) — the superv.async `<?` macro
            ;; expands to clojure.core.async/alts!, so this module must require that ns.
            [clojure.core.async :refer [<! timeout go] :include-macros true]))

(defn- exit! [code msg]
  (println msg)
  (js/process.exit code))

(defn -main [& _]
  (go
    (try
      (let [client (peer/client-peer S c/client-id
                                     (pubsub/make-pubsub-peer-middleware {}) (c/wire-middleware))]
        (<? S (peer/connect S client c/url))
        (<! (timeout 800))
        (let [sig (atom (c/mem-gset "client"))]
          (c/sync-gset! client sig false)
          (<! (timeout 800))        ; convergent handshake delivers the server's :jvm
          (c/add! sig :cljs)        ; the cljs peer contributes :cljs
          (<! (timeout 1500))       ; let both deltas cross the wire
          (let [els (c/els sig)]
            (println "CLIENT-ELEMENTS" (pr-str els))
            (if (= #{:jvm :cljs} els)
              (exit! 0 "CLIENT-OK converged-to-jvm+cljs")
              (exit! 1 (str "CLIENT-FAIL " (pr-str els)))))))
      (catch :default e
        (println "CLIENT-ERROR" (str e))
        (println "STACK" (.-stack e))
        (js/process.exit 3)))))
