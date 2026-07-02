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
            [clojure.java.io :as io]
            [kabel.peer :as peer]
            [kabel.http-kit :as http-kit]
            [kabel.middleware.fressian :refer [fressian]]
            [kabel.pubsub :as pubsub]
            [yggdrasil.wire :as wire]
            [org.replikativ.spindel.distributed.signal-sync :as ss]
            [org.replikativ.spindel.ygg-signal :as ys]
            [yggdrasil.convergent.gset :as g]
            [yggdrasil.convergent.cdvcs :as cd]
            [superv.async :refer [S <??]]
            [hasch.core :refer [uuid]])
  (:import (java.net ServerSocket)))

(defn- free-port []
  (with-open [^ServerSocket ss (ServerSocket. 0)] (.getLocalPort ss)))

(defn- mem-gset [id]
  (g/gset id {:store-config {:backend :memory :id (random-uuid)}}))

(defn- temp-dir [prefix]
  (.getAbsolutePath (io/file (System/getProperty "java.io.tmpdir")
                             (str prefix "-" (System/currentTimeMillis) "-" (rand-int 100000)))))

(defn- rm-rf [path]
  (let [d (io/file path)]
    (when (.exists d) (doseq [f (reverse (file-seq d))] (.delete f)))))

(defn- file-gset [id path]
  (g/gset id {:store-config {:backend :file :path path :id (random-uuid)}} {:sync? true}))

;; ONE fressian serializer per peer: PSS nodes/roots + ygg/system values (the CRDT record
;; ships as its projection), resolving a received value against this peer's storage. Replaces
;; bare transit, which cannot serialize a yggdrasil system value.
(defn- wire-middleware [storage]
  (fn [peer-config]
    (fressian (atom (wire/read-handlers {:resolve-storage (constantly storage)}))
              (atom (wire/write-handlers))
              peer-config)))

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

(defn- mem-cdvcs [author]
  (cd/cdvcs "doc" {:author author :store-config {:backend :memory :id (random-uuid)}} {:sync? true}))

;; CDVCS uses the SAME convergent hooks as the G-Set — its δ is a set of full,
;; self-contained commits (no blob fetch). No state-fn here: both peers start from
;; the shared content-addressed base, so no handshake snapshot is needed.
(defn- sync-cdvcs! [peer topic sig owner?]
  (ss/sync-signal! peer topic sig
                   :owner?         owner?
                   :delta-fn       ys/ygg-delta-fn
                   :clear-delta-fn ys/ygg-clear-delta-fn
                   :apply-delta-fn ys/ygg-apply-delta-fn
                   ;; full-delta = the serializable plain-data projection for the
                   ;; connect handshake. WITHOUT it the handshake ships the raw
                   ;; (non-serializable) CDVCS record and transit throws inside
                   ;; kabel's send loop, killing the owner→subscriber direction.
                   :state-fn       cd/full-delta
                   :sync?          true))

(deftest bidirectional-two-writer-convergence
  (testing "two peers each write to their own G-Set replica; both δs cross the wire
            (client→hub→ relay) and both replicas converge to the union"
    (let [port    (free-port)
          url     (str "ws://localhost:" port)
          sid     (uuid :bidi-srv)
          cid     (uuid :bidi-cli)
          topic   :bidi/gset
          server-sig (atom (mem-gset "server"))
          handler (http-kit/create-http-kit-handler! S url sid)
          server  (peer/server-peer S handler sid (pubsub/make-pubsub-peer-middleware {})
                                    (wire-middleware (:storage @server-sig)))]
      (<?? S (peer/start server))
      (try
        (let [_          (sync-gset! server topic server-sig true)   ; owner = hub
              client-sig (atom (mem-gset "client"))
              client     (peer/client-peer S cid (pubsub/make-pubsub-peer-middleware {})
                                           (wire-middleware (:storage @client-sig)))
              _          (<?? S (peer/connect S client url))
              _          (<?? S (timeout 800))
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
          server-sig (atom (mem-gset "server"))
          handler (http-kit/create-http-kit-handler! S url sid)
          server  (peer/server-peer S handler sid (pubsub/make-pubsub-peer-middleware {})
                                    (wire-middleware (:storage @server-sig)))]
      (<?? S (peer/start server))
      (try
        (let [_   (sync-gset! server topic server-sig true)
              c1-sig (atom (mem-gset "c1"))
              c2-sig (atom (mem-gset "c2"))
              c1  (peer/client-peer S (uuid :fan-c1) (pubsub/make-pubsub-peer-middleware {})
                                    (wire-middleware (:storage @c1-sig)))
              c2  (peer/client-peer S (uuid :fan-c2) (pubsub/make-pubsub-peer-middleware {})
                                    (wire-middleware (:storage @c2-sig)))
              _   (<?? S (peer/connect S c1 url))
              _   (<?? S (peer/connect S c2 url))
              _   (<?? S (timeout 800))
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
          server-sig (atom (mem-gset "server"))
          handler (http-kit/create-http-kit-handler! S url sid)
          server  (peer/server-peer S handler sid (pubsub/make-pubsub-peer-middleware {})
                                    (wire-middleware (:storage @server-sig)))]
      (<?? S (peer/start server))
      (try
        (let [_ (sync-gset! server topic server-sig true)]
          ;; build up state with NO subscriber connected yet
          (swap! server-sig (fn [s] (-> s (g/conj :a) (g/conj :b) (g/conj :c))))
          (is (= #{:a :b :c} (g/elements @server-sig)))
          ;; the late joiner connects only now
          (let [client-sig (atom (mem-gset "late"))
                client     (peer/client-peer S (uuid :lj-cli) (pubsub/make-pubsub-peer-middleware {})
                                             (wire-middleware (:storage @client-sig)))
                _          (<?? S (peer/connect S client url))
                _          (<?? S (timeout 800))
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

(deftest both-peers-prior-writes-reconcile-on-connect
  (testing "SYMMETRIC handshake: two peers EACH holding prior writes (made BEFORE
            connecting) converge to the union on connect, with NO post-connect write.
            The connecting peer's state now reaches the owner too — not just
            owner→joiner. Under the old one-way handshake the owner would stay missing
            the joiner's :b until some later write triggered a publish."
    (let [port    (free-port)
          url     (str "ws://localhost:" port)
          sid     (uuid :sym-srv)
          topic   :sym/gset
          server-sig (atom (-> (mem-gset "server") (g/conj :a)))   ; owner's prior write
          handler (http-kit/create-http-kit-handler! S url sid)
          server  (peer/server-peer S handler sid (pubsub/make-pubsub-peer-middleware {})
                                    (wire-middleware (:storage @server-sig)))]
      (<?? S (peer/start server))
      (try
        (let [_   (sync-gset! server topic server-sig true)
              client-sig (atom (-> (mem-gset "client") (g/conj :b)))  ; joiner's prior write
              client (peer/client-peer S (uuid :sym-cli) (pubsub/make-pubsub-peer-middleware {})
                                       (wire-middleware (:storage @client-sig)))
              _   (<?? S (peer/connect S client url))
              _   (<?? S (timeout 800))]
          ;; subscribe → handshake fires; deliberately NO post-connect writes
          (sync-gset! client topic client-sig false)
          (<?? S (timeout 1200))
          (is (= #{:a :b} (g/elements @client-sig))
              "joiner caught up to the owner's :a (owner→joiner, as before)")
          (is (= #{:a :b} (g/elements @server-sig))
              "owner ALSO caught up to the joiner's :b ON CONNECT — the symmetric direction")
          (<?? S (peer/stop client)))
        (finally
          (<?? S (peer/stop server)))))))

(deftest durable-gset-bidirectional-and-persists
  (testing "bidirectional convergence for a DURABLE (file-backed) G-Set: the δ is
            plain data (elements), so each peer re-materializes the SAME
            content-addressed PSS nodes from it (content-address dedup gives node
            sharing for free — no separate node-push channel needed for a G-Set).
            After convergence each peer's store is independently durable."
    (let [port    (free-port)
          url     (str "ws://localhost:" port)
          sid     (uuid :dur-srv)
          topic   :dur/gset
          s-path  (temp-dir "bidi-sygg")
          c-path  (temp-dir "bidi-cygg")
          server-sig (atom (file-gset "server" s-path))
          handler (http-kit/create-http-kit-handler! S url sid)
          server  (peer/server-peer S handler sid (pubsub/make-pubsub-peer-middleware {})
                                    (wire-middleware (:storage @server-sig)))]
      (<?? S (peer/start server))
      (try
        (let [_   (sync-gset! server topic server-sig true)
              client-sig (atom (file-gset "client" c-path))
              client (peer/client-peer S (uuid :dur-cli) (pubsub/make-pubsub-peer-middleware {})
                                       (wire-middleware (:storage @client-sig)))
              _   (<?? S (peer/connect S client url))
              _   (<?? S (timeout 800))
              _   (sync-gset! client topic client-sig false)
              _   (<?? S (timeout 500))]
          (swap! server-sig (fn [s] (g/conj s :sx)))
          (swap! client-sig (fn [s] (g/conj s :cy)))
          (<?? S (timeout 1500))
          (is (= #{:sx :cy} (g/elements @server-sig)) "durable server converged on the union")
          (is (= #{:sx :cy} (g/elements @client-sig)) "durable client converged on the union")
          ;; persist + reopen each store independently → the converged value survives
          (g/flush! @server-sig)
          (g/flush! @client-sig)
          (is (= #{:sx :cy} (g/elements (file-gset "server" s-path))) "server store is durable")
          (is (= #{:sx :cy} (g/elements (file-gset "client" c-path))) "client store is durable")
          (<?? S (peer/stop client)))
        (finally
          (<?? S (peer/stop server))
          (rm-rf s-path) (rm-rf c-path))))))

(deftest cdvcs-bidirectional-converges-and-resolves
  (testing "two CDVCS peers commit on the shared base; their δs (sets of FULL,
            self-contained commits) cross the wire both ways and the peers CONVERGE
            to the same frontier — whatever the delivery order (a correct CRDT is
            order-independent: if a peer observes the other's commit first the lineage
            is linear, else it lifts a 2-head conflict; either way SEC holds). When a
            conflict is lifted, an authored merge δ resolves both to one head.
            replikativ CDVCS over the wire, carried by signal-sync alone."
    (let [port    (free-port)
          url     (str "ws://localhost:" port)
          sid     (uuid :cd-srv)
          topic   :cd/doc
          server-sig (atom (mem-cdvcs "server"))
          handler (http-kit/create-http-kit-handler! S url sid)
          server  (peer/server-peer S handler sid (pubsub/make-pubsub-peer-middleware {})
                                    (wire-middleware (:storage @server-sig)))]
      (<?? S (peer/start server))
      (try
        (let [_   (sync-cdvcs! server topic server-sig true)
              client-sig (atom (mem-cdvcs "client"))
              client (peer/client-peer S (uuid :cd-cli) (pubsub/make-pubsub-peer-middleware {})
                                       (wire-middleware (:storage @client-sig)))
              _   (<?? S (peer/connect S client url))
              _   (<?? S (timeout 800))
              _   (sync-cdvcs! client topic client-sig false)
              _   (<?? S (timeout 500))]
          (swap! server-sig (fn [c] (cd/commit c "server" [[:assoc :s 1]])))
          (swap! client-sig (fn [c] (cd/commit c "client" [[:assoc :c 1]])))
          (<?? S (timeout 1500))
          ;; the CRDT property — convergence, regardless of who saw whose commit first
          (is (= (cd/heads @server-sig) (cd/heads @client-sig))
              "both peers converged to the same frontier (order-independent SEC)")
          ;; if the writes genuinely diverged, an authored merge resolves + propagates
          (when (cd/multiple-heads? @server-sig)
            (swap! server-sig (fn [c] (cd/merge c "server" c)))
            (<?? S (timeout 1500))
            (is (= 1 (count (cd/heads @server-sig))) "merge resolved the server to one head")
            (is (= (cd/heads @server-sig) (cd/heads @client-sig))
                "the merge δ propagated — the client resolved to the same head"))
          (<?? S (peer/stop client)))
        (finally
          (<?? S (peer/stop server)))))))

(deftest server-to-client-op-path-via-export-signal
  (testing "server-authoritative OP path (the one-directional complement to the bidirectional
            tests above): `export-signal!` is publish-only; the server signal starts nil so the
            subscribe handshake ships no (non-serializable) STATE snapshot; each mutation crosses
            as a δ the client applies into its OWN empty replica, and the shipped δ is cleared
            after send (bounded end-to-end)."
    (let [port    (free-port)
          url     (str "ws://localhost:" port)
          sid     (uuid :conv-srv)
          cid     (uuid :conv-cli)
          topic   :conv/gset
          handler (http-kit/create-http-kit-handler! S url sid)
          ;; server ships only δ (plain data) → its wire needs no storage resolver
          server  (peer/server-peer S handler sid (pubsub/make-pubsub-peer-middleware {})
                                    (wire-middleware nil))]
      (<?? S (peer/start server))
      (try
        (let [server-sig (atom nil)   ; nil → handshake ships no non-serializable snapshot
              _ (ss/export-signal! server topic server-sig
                                   :delta-fn       ys/ygg-delta-fn
                                   :clear-delta-fn ys/ygg-clear-delta-fn
                                   :sync?          true)
              client-sig (atom (mem-gset "client"))  ; the client's OWN empty replica
              client (peer/client-peer S cid (pubsub/make-pubsub-peer-middleware {})
                                       (wire-middleware (:storage @client-sig)))
              _ (<?? S (peer/connect S client url))
              _ (<?? S (timeout 800))
              _ (<?? S (pubsub/subscribe! client #{topic}
                                          {:strategies {topic (ss/->SignalSyncStrategy
                                                               client-sig nil nil ys/ygg-apply-delta-fn true nil)}}))
              _ (<?? S (timeout 500))]
          (reset! server-sig (g/conj (mem-gset "server") :x))
          (<?? S (timeout 1000))
          (is (= #{:x} (g/elements @client-sig)) "client converged on :x from a δ over the wire")
          (is (nil? (ys/ygg-delta-fn @server-sig)) "server δ cleared after send — bounded")
          (swap! server-sig (fn [s] (g/conj s :y)))
          (<?? S (timeout 1000))
          (is (= #{:x :y} (g/elements @client-sig)) "client converged on the union from the δ alone")
          (is (nil? (ys/ygg-delta-fn @server-sig)) "δ cleared again — bounded across successive ops")
          (<?? S (peer/stop client)))
        (finally
          (<?? S (peer/stop server)))))))
