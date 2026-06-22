(ns org.replikativ.spindel.distributed.bidirectional-sync-test
  "BIDIRECTIONAL convergent sync over a real kabel websocket — the replikativ p2p
   property in the spindel+yggdrasil signal setup. Both peers hold their OWN replica
   of a convergent CRDT in a signal and both `sync-signal!` it on one topic; each
   peer publishes its local δ AND applies the other's. The kabel pub/sub hub relays:
   a client's δ reaches the server, which applies it locally AND re-fans it to the
   other subscribers (`kabel.pubsub` `-apply-publish` + forward).

   Anti-echo (no runaway in a mutually-synced network) is inherited from the
   convergent layer: an apply that adds nothing returns the receiver `identical?`
   (skip reset!/republish), an integrated remote value carries no δ (`delta-fn` →
   nil → nothing to publish), and `clear-delta-fn` bounds the shipped δ.

   JVM↔JVM, but the client runs the identical `.cljc` path a browser would, so this
   is the server↔browser BIDIRECTIONAL convergence proof at the transport level."
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

;; Both peers wire the SAME convergent hooks; only :owner? differs (the topic owner
;; is the relay hub). state-fn = g/elements ships the plain element set for the
;; connect handshake (the CRDT record itself is not wire-serializable).
(defn- sync-gset! [peer topic sig owner?]
  (ss/sync-signal! peer topic sig
                   :owner?         owner?
                   :delta-fn       ys/ygg-delta-fn
                   :clear-delta-fn ys/ygg-clear-delta-fn
                   :apply-delta-fn ys/ygg-apply-delta-fn
                   :state-fn       g/elements
                   :sync?          true))

(deftest bidirectional-two-writer-convergence
  (testing "two peers each write to their own G-Set replica; both δs cross the wire
            (client→hub→ relay) and both replicas converge to the union"
    (let [port    (free-port)
          url     (str "ws://localhost:" port)
          sid     (uuid :bidi-srv)
          cid     (uuid :bidi-cli)
          topic   :bidi/gset
          handler (http-kit/create-http-kit-handler! S url sid)
          server  (peer/server-peer S handler sid (pubsub/make-pubsub-peer-middleware {}) transit)]
      (<?? S (peer/start server))
      (try
        (let [server-sig (atom (mem-gset "server"))
              _          (sync-gset! server topic server-sig true)   ; owner = hub
              client     (peer/client-peer S cid (pubsub/make-pubsub-peer-middleware {}) transit)
              _          (<?? S (peer/connect S client url))
              _          (<?? S (timeout 800))
              client-sig (atom (mem-gset "client"))
              _          (sync-gset! client topic client-sig false)
              _          (<?? S (timeout 500))]

          ;; concurrent writes: server adds :x, client adds :y
          (swap! server-sig (fn [s] (g/conj s :x)))
          (swap! client-sig (fn [s] (g/conj s :y)))
          (<?? S (timeout 1200))

          (is (= #{:x :y} (g/elements @server-sig))
              "server converged on the union — it received the client's δ over the wire")
          (is (= #{:x :y} (g/elements @client-sig))
              "client converged on the union — it received the server's δ over the wire")
          (is (nil? (ys/ygg-delta-fn @server-sig)) "server δ cleared/empty after integrate — no re-ship")
          (is (nil? (ys/ygg-delta-fn @client-sig)) "client δ cleared/empty after integrate — no re-ship")

          ;; a second round from EACH side still converges (the channel stays open both ways)
          (swap! server-sig (fn [s] (g/conj s :s2)))
          (swap! client-sig (fn [s] (g/conj s :c2)))
          (<?? S (timeout 1200))
          (is (= #{:x :y :s2 :c2} (g/elements @server-sig)) "server has both second-round adds")
          (is (= #{:x :y :s2 :c2} (g/elements @client-sig)) "client has both second-round adds")
          (is (= (g/elements @server-sig) (g/elements @client-sig)) "strong eventual consistency")

          (<?? S (peer/stop client)))
        (finally
          (<?? S (peer/stop server)))))))

(deftest three-peer-fan-in-through-the-hub
  (testing "three peers (1 owner hub + 2 subscribers) each write; every δ reaches
            every other peer — a subscriber's δ travels client→hub→OTHER subscriber
            (the hub re-fans an applied publish to all subscribers but the sender)"
    (let [port    (free-port)
          url     (str "ws://localhost:" port)
          sid     (uuid :fan-srv)
          topic   :fan/gset
          handler (http-kit/create-http-kit-handler! S url sid)
          server  (peer/server-peer S handler sid (pubsub/make-pubsub-peer-middleware {}) transit)]
      (<?? S (peer/start server))
      (try
        (let [server-sig (atom (mem-gset "server"))
              _   (sync-gset! server topic server-sig true)
              c1  (peer/client-peer S (uuid :fan-c1) (pubsub/make-pubsub-peer-middleware {}) transit)
              c2  (peer/client-peer S (uuid :fan-c2) (pubsub/make-pubsub-peer-middleware {}) transit)
              _   (<?? S (peer/connect S c1 url))
              _   (<?? S (peer/connect S c2 url))
              _   (<?? S (timeout 800))
              c1-sig (atom (mem-gset "c1"))
              c2-sig (atom (mem-gset "c2"))
              _   (sync-gset! c1 topic c1-sig false)
              _   (sync-gset! c2 topic c2-sig false)
              _   (<?? S (timeout 500))]
          (swap! server-sig (fn [s] (g/conj s :srv)))
          (swap! c1-sig      (fn [s] (g/conj s :c1)))
          (swap! c2-sig      (fn [s] (g/conj s :c2)))
          (<?? S (timeout 1500))
          (let [expected #{:srv :c1 :c2}]
            (is (= expected (g/elements @server-sig)) "hub has every peer's write")
            (is (= expected (g/elements @c1-sig)) "c1 received the hub's AND c2's writes (relayed)")
            (is (= expected (g/elements @c2-sig)) "c2 received the hub's AND c1's writes (relayed)"))
          (<?? S (peer/stop c1))
          (<?? S (peer/stop c2)))
        (finally
          (<?? S (peer/stop server)))))))

(deftest late-joiner-catches-up-via-handshake
  (testing "a peer that connects AFTER state already exists is caught up by the
            plain-data handshake — state-fn ships g/elements (serializable), not the
            non-serializable CRDT record. This is also the partition→reconnect path:
            a returning peer re-handshakes and converges on what it missed."
    (let [port    (free-port)
          url     (str "ws://localhost:" port)
          sid     (uuid :lj-srv)
          topic   :lj/gset
          handler (http-kit/create-http-kit-handler! S url sid)
          server  (peer/server-peer S handler sid (pubsub/make-pubsub-peer-middleware {}) transit)]
      (<?? S (peer/start server))
      (try
        (let [server-sig (atom (mem-gset "server"))
              _ (sync-gset! server topic server-sig true)]
          ;; build up state with NO subscriber connected yet
          (swap! server-sig (fn [s] (-> s (g/conj :a) (g/conj :b) (g/conj :c))))
          (is (= #{:a :b :c} (g/elements @server-sig)))
          ;; the late joiner connects only now
          (let [client     (peer/client-peer S (uuid :lj-cli) (pubsub/make-pubsub-peer-middleware {}) transit)
                _          (<?? S (peer/connect S client url))
                _          (<?? S (timeout 800))
                client-sig (atom (mem-gset "late"))
                _          (sync-gset! client topic client-sig false)
                _          (<?? S (timeout 1200))]
            (is (= #{:a :b :c} (g/elements @client-sig))
                "late joiner caught up to pre-existing state via the handshake snapshot")
            ;; and live sync still flows after catch-up
            (swap! server-sig (fn [s] (g/conj s :d)))
            (<?? S (timeout 1000))
            (is (= #{:a :b :c :d} (g/elements @client-sig)) "live δ after catch-up still applies")
            (<?? S (peer/stop client))))
        (finally
          (<?? S (peer/stop server)))))))
