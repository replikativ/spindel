(ns org.replikativ.spindel.distributed.workspace-wire-topology-e2e-test
  "End-to-end over a REAL kabel websocket: `wire-topology!` drives the CLIENT side
   of the sync mesh purely from a (data) descriptor. JVM↔JVM in one process; the
   client runs the identical `.cljc` path a browser would, so this is the
   server↔browser proxy at the transport level.

   Covered here: the `:bidirectional` role — a descriptor marking a system
   `:role :bidirectional` makes `wire-topology!` convergent-sync it (`sync-system!`
   over the ygg-signal δ-path), so both peers' replicas converge over the wire.

   The `:subscriber` store-follow path (datahike store → fetch-gate → reseat over
   kabel) is the heavier integration — its store sync is proven by
   `cross_system_sync_test`, its gate/reseat by the `workspace_peer` tests — and is
   a natural next rung (it needs the datahike KabelWriter client plumbing)."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.core.async :refer [timeout]]
            [kabel.peer :as peer]
            [kabel.http-kit :as http-kit]
            [kabel.pubsub :as pubsub]
            [kabel.middleware.transit :refer [transit]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.distributed.workspace-peer :as wp]
            [org.replikativ.spindel.distributed.workspace-peer-sync :as sync]
            [yggdrasil.convergent.gset :as g]
            [superv.async :refer [S <??]]
            [hasch.core :refer [uuid]])
  (:import (java.net ServerSocket)))

(defn- free-port []
  (with-open [^ServerSocket ss (ServerSocket. 0)] (.getLocalPort ss)))

(defn- mem-gset [id]
  (g/gset id {:store-config {:backend :memory :id (random-uuid)}}))

(deftest wire-topology-bidirectional-role-over-kabel
  (testing "a descriptor marking a system :role :bidirectional drives the client's
            wire-topology! to convergent-sync it (sync-system!); concurrent writes
            on BOTH peers cross the wire and both replicas converge to the union"
    (let [port    (free-port)
          url     (str "ws://localhost:" port)
          sid     (uuid :wt-srv)
          cid     (uuid :wt-cli)
          topic   :wt/gset
          handler (http-kit/create-http-kit-handler! S url sid)
          server  (peer/server-peer S handler sid (pubsub/make-pubsub-peer-middleware {}) transit)]
      (<?? S (peer/start server))
      (try
        (let [server-sig (atom (mem-gset "server"))
              ;; SERVER (owner/hub): sync-system! directly, with the serializable
              ;; connect-handshake projection (g/elements).
              _          (sync/sync-system! server topic server-sig
                                            :owner? true :sync? true :state-fn g/elements)
              client     (peer/client-peer S cid (pubsub/make-pubsub-peer-middleware {}) transit)
              _          (<?? S (peer/connect S client url))
              _          (<?? S (timeout 800))
              client-sig (atom (mem-gset "client"))
              ctx        (ctx/create-execution-context)
              wpeer      (wp/make-workspace-peer
                          {:ctx ctx :resolve-system-fn (fn [_ _] nil)})
              ;; CLIENT: wired ENTIRELY from the descriptor through wire-topology!
              desc       {:systems {"set" {:topic topic :role :bidirectional}}}
              wired      (sync/wire-topology!
                          wpeer client desc
                          (fn [_sid] nil)                       ; store-lookup (unused here)
                          :signal-lookup (fn [_sid] client-sig)
                          :sync? true)
              _          (<?? S (timeout 500))]
          (is (contains? (:synced wired) "set")
              "wire-topology! reports the :bidirectional system under :synced")

          ;; concurrent writes — server adds :x, client adds :y
          (swap! server-sig (fn [s] (g/conj s :x)))
          (swap! client-sig (fn [s] (g/conj s :y)))
          (<?? S (timeout 1200))

          (is (= #{:x :y} (g/elements @server-sig))
              "server converged on the union — it received the client's δ over the wire")
          (is (= #{:x :y} (g/elements @client-sig))
              "client converged on the union — it received the server's δ over the wire")

          ;; a second round from each side still converges (channel stays open)
          (swap! server-sig (fn [s] (g/conj s :s2)))
          (swap! client-sig (fn [s] (g/conj s :c2)))
          (<?? S (timeout 1200))
          (is (= #{:x :y :s2 :c2} (g/elements @server-sig)) "server has both second-round adds")
          (is (= #{:x :y :s2 :c2} (g/elements @client-sig)) "client has both second-round adds")

          (ctx/stop-context! ctx)
          (<?? S (peer/stop client)))
        (finally
          (<?? S (peer/stop server)))))))
