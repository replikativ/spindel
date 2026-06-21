(ns org.replikativ.spindel.distributed.cross-system-sync-test
  "DECISIVE proof that datahike + yggdrasil replicate over ONE kabel wire through
   ONE serializer — the canonical PSS codec shared by both systems.

   A single peer pair carries datahike's fressian middleware (canonical PSS
   node/root handlers + Datom/DB). That SAME serializer ships, over the SAME
   socket (one message order = causal ordering across systems):

     - a datahike store (DB roots + Datom elements), via datahike's KabelWriter +
       konserve-sync (register-store-for-remote-access!), and
     - a yggdrasil durable G-Set store (canonical PSS leaf/branch nodes + the
       :crdt/roots cell), via konserve-sync's GENERIC register/subscribe + the
       PSS reachability walker.

   Both replicate to the client; the client reconstructs both — the datahike DB
   resolves its storage by :pss/storage-id, the yggdrasil G-Set restores its root
   from the synced nodes. This is the replikativ p2p vision: heterogeneous
   databases over one wire, deserialized by one canonical PSS codec.

   yggdrasil sends only NODES + the roots cell (addresses are plain strings); the
   root is reconstructed locally via restore-set — so datahike's node handlers
   (pss/leaf, pss/branch) are all the serializer needs for the yggdrasil side."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.java.io :as io]
            [clojure.core.async :refer [<!!]]
            [datahike.api :as d]
            [datahike.connector :refer [release]]
            [datahike.kabel.connector]
            [datahike.kabel.handlers :as handlers]
            [datahike.kabel.fressian-handlers :as fh]
            [kabel.peer :as peer]
            [kabel.http-kit :refer [create-http-kit-handler!]]
            [kabel.middleware.fressian :refer [fressian]]
            [konserve.core :as k]
            [konserve-sync.core :as sync]
            [konserve-sync.walkers.pss :as ks-pss]
            [is.simm.distributed-scope :as ds]
            [superv.async :refer [<?? S]]
            [yggdrasil.convergent.gset :as g]
            [yggdrasil.convergent.durable :as durable]))

(def server-id #uuid "10000000-0000-0000-0000-0000000000c1")
(def client-id #uuid "20000000-0000-0000-0000-0000000000c2")

(defn- get-free-port []
  (let [s (java.net.ServerSocket. 0)] (try (.getLocalPort s) (finally (.close s)))))

(defn- temp-dir [prefix]
  (.getAbsolutePath (io/file (System/getProperty "java.io.tmpdir")
                             (str prefix "-" (System/currentTimeMillis) "-" (rand-int 100000)))))

(defn- rm-rf [path]
  (let [d (io/file path)]
    (when (.exists d) (doseq [f (reverse (file-seq d))] (.delete f)))))

(defn- datahike-fressian-middleware [peer-config]
  (fressian (atom fh/read-handlers) (atom fh/write-handlers) peer-config))

(def schema [{:db/ident :item/name :db/valueType :db.type/string
              :db/cardinality :db.cardinality/one}])

(defn- poll-until [pred timeout-ms]
  (let [deadline (+ (System/currentTimeMillis) timeout-ms)]
    (loop []
      (cond (pred) true
            (> (System/currentTimeMillis) deadline) false
            :else (do (Thread/sleep 100) (recur))))))

;; konserve-sync opts for a durable-CRDT PSS store: reachability walker rooted at
;; the :crdt/roots cell (+ the freed pointer) + the root-last fetch-gate ordering.
(def ^:private ygg-sync-opts
  (ks-pss/make-pss-sync-opts :crdt/roots #{:crdt/roots :crdt/freed}))

(defn- dh-item-names
  "Read all :item/name values from a datahike conn (empty if none / not yet synced)."
  [conn]
  (try (set (map first (d/q '[:find ?n :where [?e :item/name ?n]] @conn)))
       (catch Throwable _ #{})))

(deftest test-datahike-and-yggdrasil-sync-over-one-wire
  (testing "one peer pair + one canonical serializer replicates BOTH a datahike
            store AND a yggdrasil durable G-Set store to the client"
    (let [port (get-free-port)
          url (str "ws://localhost:" port)
          dh-id #uuid "7e570000-0000-0000-0000-0000000000d1"
          ygg-id #uuid "7e570000-0000-0000-0000-0000000000d2"
          ygg-topic ygg-id
          base {:schema-flexibility :write :keep-history? true :branch-history? true}
          s-dh-path (temp-dir "xs-sdh")   c-dh-path (temp-dir "xs-cdh")
          s-ygg-path (temp-dir "xs-sygg") c-ygg-path (temp-dir "xs-cygg")
          s-dh-cfg (assoc base :store {:backend :file :path s-dh-path :id dh-id})
          s-ygg-cfg {:backend :file :path s-ygg-path :id ygg-id}
          c-ygg-cfg {:backend :file :path c-ygg-path :id ygg-id}]
      (try
        ;; ---- SERVER: a datahike store with trunk data ----
        (d/create-database s-dh-cfg)
        (let [s-dh (d/connect s-dh-cfg)]
          (d/transact s-dh schema)
          (d/transact s-dh [{:item/name "dh-trunk"}])
          ;; ---- SERVER: a yggdrasil durable G-Set, persisted to its file store ----
          (let [s-ygg0 (g/gset (str ygg-id) {:store-config s-ygg-cfg :sync? true})
                s-ygg1 (-> s-ygg0 (g/conj :alpha) (g/conj :beta))
                s-ygg  (g/flush! s-ygg1)            ; write nodes + :crdt/roots to the store
                s-ygg-store (:kv-store s-ygg)
                _ (is (= #{:alpha :beta} (g/elements s-ygg)) "server G-Set holds both elements")

                handler (create-http-kit-handler! S url server-id)
                server-peer (peer/server-peer S handler server-id
                                              (comp (sync/server-middleware) ds/remote-middleware)
                                              datahike-fressian-middleware)
                _ (<?? S (peer/start server-peer))
                _ (ds/invoke-on-peer server-peer)
                _ (handlers/register-global-handlers! server-peer)
                ;; datahike store over konserve-sync (datahike's own walk)
                _ (handlers/register-store-for-remote-access! dh-id s-dh server-peer)
                ;; yggdrasil durable store over konserve-sync (generic PSS walker)
                _ (sync/register-store! server-peer ygg-topic s-ygg-store ygg-sync-opts)

                ;; ---- CLIENT: peer + datahike KabelWriter conn (real konserve-sync) ----
                client-peer (peer/client-peer S client-id
                                              (comp (sync/client-middleware) ds/remote-middleware)
                                              datahike-fressian-middleware)
                _ (ds/invoke-on-peer client-peer)
                _ (<?? S (peer/connect S client-peer url))
                c-dh-cfg (assoc base :store {:backend :file :path c-dh-path :id dh-id}
                                :index :datahike.index/persistent-set
                                :writer {:backend :kabel :peer-id server-id :local-peer client-peer})
                c-dh (<!! (d/connect c-dh-cfg {:sync? false}))

                ;; ---- CLIENT: a local yggdrasil store; subscribe it to the remote ----
                c-ygg-store (:kv-store (durable/open c-ygg-cfg {:sync? true}))
                _ (<?? S (sync/subscribe-store! client-peer ygg-topic c-ygg-store ygg-sync-opts))]

            ;; ---- datahike replicates: the trunk datom lands on the client ----
            (is (poll-until #(= #{"dh-trunk"} (dh-item-names c-dh)) 10000)
                "datahike trunk replicated to client over the canonical serializer")

            ;; ---- yggdrasil replicates: the :crdt/roots cell + all nodes land,
            ;; and the client reconstructs the SAME G-Set value from synced nodes.
            (is (poll-until #(seq (<!! (k/get c-ygg-store :crdt/roots))) 10000)
                "yggdrasil :crdt/roots cell replicated to client")
            (is (poll-until
                 #(= #{:alpha :beta}
                     (try (g/elements (g/gset (str ygg-id) {:kv-store c-ygg-store :sync? true}))
                          (catch Throwable _ #{})))
                 10000)
                "client reconstructs the yggdrasil G-Set from nodes synced via the
                 SAME canonical PSS codec that carries datahike")

            ;; ---- a LIVE update on each system also propagates over the one wire ----
            (d/transact s-dh [{:item/name "dh-live"}])
            (let [s-ygg' (g/flush! (g/conj s-ygg :gamma))]
              (is (= #{:alpha :beta :gamma} (g/elements s-ygg')) "server G-Set advanced")
              (is (poll-until #(= #{"dh-trunk" "dh-live"} (dh-item-names c-dh)) 10000)
                  "datahike live update replicated")
              (is (poll-until
                   #(= #{:alpha :beta :gamma}
                       (try (g/elements (g/gset (str ygg-id) {:kv-store c-ygg-store :sync? true}))
                            (catch Throwable _ #{})))
                   10000)
                  "yggdrasil live update replicated over the same wire"))

            ;; cleanup
            (release c-dh)
            (sync/unsubscribe-store! client-peer ygg-topic)
            (<?? S (peer/stop client-peer))
            (handlers/unregister-store-for-remote-access! dh-id server-peer)
            (sync/unregister-store! server-peer ygg-topic)
            (<?? S (peer/stop server-peer)))
          (release s-dh))
        (finally
          (d/delete-database s-dh-cfg)
          (rm-rf s-dh-path) (rm-rf c-dh-path)
          (rm-rf s-ygg-path) (rm-rf c-ygg-path))))))
