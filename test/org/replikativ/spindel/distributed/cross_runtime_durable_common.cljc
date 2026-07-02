(ns org.replikativ.spindel.distributed.cross-runtime-durable-common
  "Shared wiring for the DURABLE cross-RUNTIME proof: a JVM kabel server holding a
   FILE-backed G-Set replicates it to a cljs(node) client over ONE real websocket +
   ONE fressian serializer — the unified model across runtimes. NODES ride konserve-sync
   (into the node client's konserve node-filestore), the VALUE (the CRDT root) rides
   signal-sync via the `ygg/system` codec; the client reconstructs the identical G-Set
   from the synced nodes, then proves it PERSISTED across a cold restart (reopen from
   the node-filestore path).

   The JVM runs `:sync? true` (blocking); the node client runs `:sync? false` (genuine
   async over the node-filestore + core.async) — so this exercises the real cljs async
   durable path + the cljc `yggdrasil.fressian` value codec on a browser-like runtime."
  (:require [kabel.middleware.fressian :refer [fressian]]
            [konserve-sync.walkers.pss :as ks-pss]
            [yggdrasil.storage :as ygg-storage]
            [yggdrasil.wire :as wire]))

(def port 47401)
(def url (str "ws://localhost:" port))
(def server-id #uuid "dddddddd-0000-0000-0000-000000000001")
(def client-id #uuid "dddddddd-0000-0000-0000-000000000002")
(def store-topic :xrt-dur/nodes)   ; konserve-sync store topic (the server owns it)
(def value-topic :xrt-dur/value)   ; signal-sync value topic (the server owns it)
(def gid "xrt-dur-gset")

;; fixed file paths (same machine, separate stores) — the script cleans them.
(def server-path "/tmp/xrt-dur-server")
(def client-path "/tmp/xrt-dur-client")
;; the client store's id is FIXED so the cold-restart reopen resolves the same store.
(def client-store-id #uuid "dddddddd-0000-0000-0000-0000000000c1")

;; ONE fressian serializer per peer: PSS nodes/roots + ygg/system values, resolving a
;; received value's storage against this peer's local (node-synced) store.
(defn wire-middleware [storage]
  (fn [peer-config]
    (fressian (atom (wire/read-handlers {:resolve-storage (constantly storage)}))
              (atom (wire/write-handlers))
              peer-config)))

;; NODE-ONLY konserve-sync opts: ship the content-addressed nodes, not the sender's
;; `:crdt/roots` cell (the head arrives via the signal-sync value instead).
(def nodes-only-opts
  (ks-pss/make-pss-sync-opts :crdt/branches ks-pss/default-head-key false ygg-storage/node-child-addresses))
