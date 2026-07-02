(ns org.replikativ.spindel.distributed.ygg-value-wire-test
  "PROOF of the unified sync model over ONE fressian serializer: a yggdrasil CRDT
   lives in a signal, and its **current value ships as the CRDT ROOT** (via the
   `ygg/system` value codec — plain fields + each PSS field's content-addressed root
   address), while **konserve-sync ships the nodes** (the state elements). The
   receiver reconstructs the SAME G-Set value against its local, node-synced store.

   This is the capability the cljc `yggdrasil.fressian` port + `yggdrasil.wire` unlock:
   before it, a CRDT value was not wire-serializable, so signal-sync had to project to
   a plain-data `state-fn` (`g/elements`). Now the data structure serializes itself —
   the same canonical PSS codec datahike uses — so there is ONE way to sync: nodes over
   konserve-sync, the value/δ over signal-sync, `-join` the only per-CRDT bit.

   ONE kabel.pubsub middleware carries BOTH konserve-sync store topics and signal-sync
   value topics; ONE fressian serializer (yggdrasil.wire) serializes PSS nodes/roots
   AND `ygg/system` values."
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

;; The wire serializer: PSS nodes/roots + ygg/system values (yggdrasil.wire), with a
;; lexical resolve-storage (this peer's single store) — a received value reconstructs
;; against the store konserve-sync fed. One serializer for BOTH message families.
(defn- wire-middleware [storage]
  (fn [peer-config]
    (fressian (atom (wire/read-handlers {:resolve-storage (constantly storage)}))
              (atom (wire/write-handlers))
              peer-config)))

;; konserve-sync walker for a durable-CRDT PSS store (reachability from :crdt/roots +
;; the root-last fetch-gate), same as cross_system_sync_test.
(def ^:private ygg-sync-opts
  (ks-pss/make-pss-sync-opts :crdt/branches ks-pss/default-head-key true
                             ygg-storage/node-child-addresses))

(defn- poll-until [pred timeout-ms]
  (let [deadline (+ (System/currentTimeMillis) timeout-ms)]
    (loop []
      (cond (pred) true
            (> (System/currentTimeMillis) deadline) false
            :else (do (Thread/sleep 100) (recur))))))

(deftest gset-value-and-nodes-over-one-fressian-wire
  (testing "a durable G-Set's VALUE ships over signal-sync (ygg/system) and its NODES
            over konserve-sync, on ONE fressian serializer; the client reconstructs the
            identical G-Set value from the synced nodes"
    (let [port       (free-port)
          url        (str "ws://localhost:" port)
          sid        #uuid "a0000000-0000-0000-0000-0000000000f1"
          cid        #uuid "b0000000-0000-0000-0000-0000000000f2"
          ygg-id     #uuid "c0000000-0000-0000-0000-0000000000f3"
          store-topic ygg-id
          val-topic  :ygg/value
          s-path     (temp-dir "vw-s")
          c-path     (temp-dir "vw-c")
          s-cfg      {:backend :file :path s-path :id (random-uuid)}
          c-cfg      {:backend :file :path c-path :id (random-uuid)}]
      (try
        (let [;; SERVER: a durable G-Set with prior writes — `conj` AUTO-FLUSHES, so the
              ;; roots are realized + committed (a sendable value) with no explicit flush.
              s-gset  (-> (g/gset (str ygg-id) {:store-config s-cfg} {:sync? true})
                          (g/conj :alpha) (g/conj :beta))
              s-store (:kv-store s-gset)
              s-sig   (atom s-gset)
              _ (is (= #{:alpha :beta} (g/elements s-gset)) "server holds both elements")

              handler (http-kit/create-http-kit-handler! S url sid)
              server  (peer/server-peer S handler sid
                                        (pubsub/make-pubsub-peer-middleware {})
                                        (wire-middleware (:storage s-gset)))
              _ (<?? S (peer/start server))
              ;; nodes over konserve-sync; the VALUE over signal-sync (owner = relay)
              _ (sync/register-store! server store-topic s-store ygg-sync-opts)
              _ (ss/export-signal! server val-topic s-sig)

              ;; CLIENT: a local store the nodes sync into; reconstruct against it.
              c-store   (:kv-store (durable/open c-cfg {} {:sync? true}))
              c-storage (ygg-storage/create-storage c-store)
              client    (peer/client-peer S cid
                                          (pubsub/make-pubsub-peer-middleware {})
                                          (wire-middleware c-storage))
              _ (<?? S (peer/connect S client url))
              _ (<?? S (sync/subscribe-store! client store-topic c-store ygg-sync-opts))
              ;; the received VALUE is a reconstructed G-Set (over c-store); hold it.
              c-val (ss/subscribe-signal! client val-topic)]

          ;; the nodes land (konserve-sync), then the VALUE reconstructs + reads.
          (is (poll-until #(seq (<!! (k/get c-store :crdt.head/main))) 10000)
              "the G-Set's nodes + :crdt/roots cell synced to the client store")
          (is (poll-until
               #(= #{:alpha :beta}
                   (try (when-let [v @c-val] (g/elements v)) (catch Throwable _ nil)))
               10000)
              "the client RECONSTRUCTED the G-Set VALUE received over signal-sync
               (ygg/system) from the konserve-sync'd nodes — one fressian wire")

          (ss/unsubscribe-signal! client val-topic)
          (sync/unsubscribe-store! client store-topic)
          (<?? S (peer/stop client))
          (ss/unexport-signal! server val-topic s-sig)
          (sync/unregister-store! server store-topic)
          (<?? S (peer/stop server)))
        (finally
          (rm-rf s-path) (rm-rf c-path))))))
