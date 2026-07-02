(ns org.replikativ.spindel.distributed.bidirectional-value-mesh-test
  "The 2-peer bidirectional VALUE/NODE mesh — the unified model, both directions, no
   kabel change. Two peers each hold a file-backed G-Set with DIFFERENT prior writes,
   and converge to the union on connect:

     - NODES ride konserve-sync, both ways, into each peer's OWN store. The walker ships
       nodes ONLY (`pointer-keys #{}`), so a peer's `:crdt/roots` head cell is never
       clobbered by the other's — content-addressed nodes dedup and coexist.
     - the VALUE rides signal-sync as `ygg/system` (the CRDT ROOT + wrapper). Each peer
       reconstructs the other's value against its OWN (now node-complete) store and
       `-join`s it — a same-store join, no cross-store dance.

   kabel.pubsub's middleware is symmetric (owner = whoever `register-topic!`d, not the
   ws-server), so in a 2-peer setup each peer owns its node topic and the other
   subscribes — mutual sync with NO kabel change. ONE fressian serializer per peer.

   Then a COLD RESTART on each side: flush, reopen from the path, assert the converged
   union persisted locally."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.java.io :as io]
            [clojure.core.async :refer [<!!]]
            [kabel.peer :as peer]
            [kabel.http-kit :as http-kit]
            [kabel.middleware.fressian :refer [fressian]]
            [kabel.pubsub :as pubsub]
            [konserve.core :as k]
            [konserve-sync.core :as sync]
            [konserve-sync.walkers.pss :as ks-pss]
            [org.replikativ.spindel.distributed.signal-sync :as ss]
            [org.replikativ.spindel.ygg-signal :as ys]
            [superv.async :refer [<?? S]]
            [yggdrasil.convergent.gset :as g]
            [yggdrasil.convergent.durable :as durable]
            [yggdrasil.storage :as ygg-storage]
            [yggdrasil.wire :as wire])
  (:import (java.net ServerSocket)))

(defn- free-port []
  (with-open [^ServerSocket ss (ServerSocket. 0)] (.getLocalPort ss)))

(defn- temp-dir [prefix]
  (.getAbsolutePath (io/file (System/getProperty "java.io.tmpdir")
                             (str prefix "-" (System/currentTimeMillis) "-" (rand-int 100000)))))

(defn- rm-rf [path]
  (let [d (io/file path)]
    (when (.exists d) (doseq [f (reverse (file-seq d))] (.delete f)))))

(defn- wire-middleware [storage]
  (fn [peer-config]
    (fressian (atom (wire/read-handlers {:resolve-storage (constantly storage)}))
              (atom (wire/write-handlers))
              peer-config)))

;; NODE-ONLY konserve-sync opts: walk from :crdt/roots but ship no pointer keys, so the
;; receiver gets the content-addressed nodes WITHOUT the sender's :crdt/roots cell
;; (which would clobber its own). The head arrives via the signal-sync value instead.
(def ^:private nodes-only-opts
  (ks-pss/make-pss-sync-opts :crdt/branches ks-pss/default-head-key false ygg-storage/node-child-addresses))

(defn- poll-until [pred timeout-ms]
  (let [deadline (+ (System/currentTimeMillis) timeout-ms)]
    (loop [] (cond (pred) true
                   (> (System/currentTimeMillis) deadline) false
                   :else (do (Thread/sleep 100) (recur))))))

;; both peers sync the SAME value topic bidirectionally: ship the value via ygg/system
;; (no delta-fn/state-fn), JOIN incoming with -join (merge-fn). The symmetric handshake
;; exchanges each peer's prior value on connect.
(defn- sync-value! [peer topic sig owner?]
  (ss/sync-signal! peer topic sig
                   :owner?   owner?
                   :merge-fn (ys/ygg-merge-fn true)
                   :sync?    true))

(deftest two-peers-prior-writes-converge-via-value-and-nodes
  (testing "each peer's PRIOR durable write reaches the other (nodes over konserve-sync,
            value over signal-sync), both converge to the union, and it persists"
    (let [port     (free-port)
          url      (str "ws://localhost:" port)
          aid      #uuid "e0000000-0000-0000-0000-0000000000a1"
          bid      #uuid "e0000000-0000-0000-0000-0000000000b2"
          gid      "mesh-gset"
          a-topic  :nodes/a          ; A owns its node topic; B subscribes
          b-topic  :nodes/b          ; B owns its node topic; A subscribes
          v-topic  :mesh/value
          a-path   (temp-dir "mesh-a")
          b-path   (temp-dir "mesh-b")
          a-cfg    {:backend :file :path a-path :id (random-uuid)}
          b-cfg    {:backend :file :path b-path :id (random-uuid)}]
      (try
        (let [;; prior writes: A={:a}, B={:b} — `conj` AUTO-FLUSHES, so each is already
              ;; committed to its own store (a durable, sendable root).
              a-g0   (-> (g/gset gid {:store-config a-cfg} {:sync? true}) (g/conj :a))
              b-g0   (-> (g/gset gid {:store-config b-cfg} {:sync? true}) (g/conj :b))
              a-store (:kv-store a-g0)  a-storage (:storage a-g0)
              b-store (:kv-store b-g0)  b-storage (:storage b-g0)
              a-sig  (atom a-g0)
              b-sig  (atom b-g0)

              handler (http-kit/create-http-kit-handler! S url aid)
              a-peer  (peer/server-peer S handler aid
                                        (pubsub/make-pubsub-peer-middleware {})
                                        (wire-middleware a-storage))
              _ (<?? S (peer/start a-peer))
              b-peer  (peer/client-peer S bid
                                        (pubsub/make-pubsub-peer-middleware {})
                                        (wire-middleware b-storage))
              _ (<?? S (peer/connect S b-peer url))

              ;; mutual NODE sync: each owns its store topic, the other subscribes.
              _ (sync/register-store! a-peer a-topic a-store nodes-only-opts)
              _ (sync/register-store! b-peer b-topic b-store nodes-only-opts)
              _ (<?? S (sync/subscribe-store! b-peer a-topic b-store nodes-only-opts)) ; A's nodes -> b-store
              _ (<?? S (sync/subscribe-store! a-peer b-topic a-store nodes-only-opts)) ; B's nodes -> a-store
              ;; give the node handshakes a moment to land before the value exchange
              _ (<?? S (clojure.core.async/timeout 800))

              ;; bidirectional VALUE sync — symmetric handshake exchanges prior values
              _ (sync-value! a-peer v-topic a-sig true)
              _ (sync-value! b-peer v-topic b-sig false)]

          (is (poll-until #(= #{:a :b} (try (g/elements @a-sig) (catch Throwable _ nil))) 12000)
              "peer A converged to the union (received B's :b value + nodes)")
          (is (poll-until #(= #{:a :b} (try (g/elements @b-sig) (catch Throwable _ nil))) 12000)
              "peer B converged to the union (received A's :a value + nodes)")

          ;; COLD RESTART each side: reopen from path, read back. No manual flush! — the
          ;; receive-side `-join` AUTO-FLUSHED the converged value (durable-after-apply),
          ;; so the union is already on disk.
          (ss/unsync-signal! a-peer v-topic a-sig :owner? true)
          (ss/unsync-signal! b-peer v-topic b-sig)
          (sync/unsubscribe-store! b-peer a-topic)
          (sync/unsubscribe-store! a-peer b-topic)
          (<?? S (peer/stop b-peer))
          (<?? S (peer/stop a-peer))
          (is (= #{:a :b} (g/elements (g/gset gid {:store-config a-cfg} {:sync? true})))
              "A's converged union persisted — a fresh handle reopened from disk reads it")
          (is (= #{:a :b} (g/elements (g/gset gid {:store-config b-cfg} {:sync? true})))
              "B's converged union persisted — a fresh handle reopened from disk reads it"))
        (finally
          (rm-rf a-path) (rm-rf b-path))))))
