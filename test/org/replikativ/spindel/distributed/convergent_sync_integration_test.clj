(ns org.replikativ.spindel.distributed.convergent-sync-integration-test
  "Server→client sync of a yggdrasil CONVERGENT CRDT over a REAL kabel websocket
   via signal_sync's OP path. JVM↔JVM — but the client runs the identical `.cljc`
   path a browser would, so this is the server↔browser convergence proof at the
   transport level.

   It proves the composition the in-process unit tests (signal_sync_test,
   ygg_signal_test) do not: real peers + transit serialization + SignalSyncStrategy
   + the yggdrasil δ hooks actually converge two independent replicas over the wire,
   and the clear-after-send keeps the shipped δ bounded end-to-end.

   KEY CONSTRAINT — why the OP path, not the STATE path:
   a convergent CRDT *value* is NOT wire-serializable. A durable G-Set record carries
   konserve stores + a comparator fn; an LWW-register's ConflictFreeSystem carries its
   join fn. Transit/fressian cannot encode those. Only the δ (a plain set/map) crosses
   cleanly. So:
     • the server signal starts `nil` — the subscribe handshake ships no snapshot of a
       non-serializable value (handshake is STATE-path; it would fail to serialize);
     • every mutation propagates as a δ (`delta-fn`) that the client applies
       (`apply-delta-fn`) into its OWN locally-constructed empty replica.
   This is the server-authoritative → browser-reflects direction. The BIDIRECTIONAL
   counterpart is `signal-sync/sync-signal!` (both peers publish + apply on a shared
   atom; the kabel hub relays) — see bidirectional-sync-test."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.core.async :refer [timeout]]
            [kabel.peer :as peer]
            [kabel.http-kit :as http-kit]
            [kabel.middleware.transit :refer [transit]]
            [kabel.pubsub :as pubsub]
            [org.replikativ.spindel.distributed.signal-sync :as ss]
            [org.replikativ.spindel.ygg-signal :as ys]
            [yggdrasil.convergent.gset :as g]
            [superv.async :refer [S <??]]
            [hasch.core :refer [uuid]])
  (:import (java.net ServerSocket)))

(defn- free-port []
  (with-open [^ServerSocket ss (ServerSocket. 0)] (.getLocalPort ss)))

(defn- mem-gset [id]
  (g/gset id {:store-config {:backend :memory :id (random-uuid)}}))

(deftest server-to-client-gset-op-sync
  (testing "a server-side G-Set's ops propagate as δ over a real websocket; the
            client's independent replica converges, and the shipped δ is cleared"
    (let [port    (free-port)
          url     (str "ws://localhost:" port)
          sid     (uuid :conv-srv)
          cid     (uuid :conv-cli)
          topic   :conv/gset
          handler (http-kit/create-http-kit-handler! S url sid)
          ;; pub/sub middleware + transit serializer = the minimal wire for signal_sync
          server  (peer/server-peer S handler sid (pubsub/make-pubsub-peer-middleware {}) transit)]
      (<?? S (peer/start server))
      (try
        (let [;; server signal starts nil → the handshake ships no (non-serializable) snapshot
              server-sig (atom nil)
              _ (ss/export-signal! server topic server-sig
                                   :delta-fn       ys/ygg-delta-fn
                                   :clear-delta-fn ys/ygg-clear-delta-fn
                                   :sync?          true)
              client (peer/client-peer S cid (pubsub/make-pubsub-peer-middleware {}) transit)
              _ (<?? S (peer/connect S client url))
              _ (<?? S (timeout 800))
              ;; the client holds its OWN empty replica; OP-path subscribe (apply-delta-fn)
              client-sig (atom (mem-gset "client"))
              _ (<?? S (pubsub/subscribe! client #{topic}
                                          {:strategies {topic (ss/->SignalSyncStrategy
                                                               client-sig nil nil ys/ygg-apply-delta-fn true nil)}}))
              _ (<?? S (timeout 500))]

          ;; first op: nil → G-Set #{:x}; the δ #{:x} crosses the wire
          (reset! server-sig (g/conj (mem-gset "server") :x))
          (<?? S (timeout 1000))
          (is (= #{:x} (g/elements @client-sig))
              "client converged on :x from a δ shipped over the wire")
          (is (nil? (ys/ygg-delta-fn @server-sig))
              "server δ cleared after send — bounded, won't re-ship")

          ;; second op: δ #{:y}; client converges to the union from the δ ALONE
          (swap! server-sig (fn [s] (g/conj s :y)))
          (<?? S (timeout 1000))
          (is (= #{:x :y} (g/elements @client-sig))
              "client converged on #{:x :y} from the second δ alone (no full state crossed)")
          (is (nil? (ys/ygg-delta-fn @server-sig))
              "δ cleared again — bounded across successive ops")

          (<?? S (peer/stop client)))
        (finally
          (<?? S (peer/stop server)))))))
