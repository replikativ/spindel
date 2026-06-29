(ns org.replikativ.spindel.distributed.workspace-follow-e2e-test
  "End-to-end FOLLOW over a REAL kabel websocket: a system's konserve store
   replicates server→client; `wire-topology!`'s `:subscriber` path
   (`attach-store!`) feeds branch-head updates into the workspace-peer gate, which
   re-seats once the local replica catches up to the descriptor's head. This is the
   server-authoritative reflection half (the complement of `fork-remote!`).

   Uses a yggdrasil durable G-Set store synced via the generic PSS walker (the
   `cross_system_sync_test` harness). The descriptor is set LOCALLY here — the
   descriptor-over-`signal_sync` channel is covered by `signal_sync_test`, and
   composing konserve-sync + pubsub middleware on one peer is the dvergr-level
   integration. The DATAHIKE-branch variant (commit-id head tokens via datahike's
   kabel connector) is likewise the dvergr pinning; here the head token is the
   content-addressed `:crdt/roots`, which is stable across the wire for the same
   reason a commit-id is. JVM-only."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.java.io :as io]
            [clojure.core.async :refer [<!!]]
            [kabel.peer :as peer]
            [kabel.http-kit :refer [create-http-kit-handler!]]
            [kabel.middleware.fressian :refer [fressian]]
            [datahike.kabel.fressian-handlers :as fh]
            [konserve.core :as k]
            [konserve-sync.core :as sync]
            [konserve-sync.walkers.pss :as ks-pss]
            [is.simm.distributed-scope :as ds]
            [superv.async :refer [<?? S]]
            [yggdrasil.convergent.gset :as g]
            [yggdrasil.convergent.durable :as durable]
            [yggdrasil.storage :as ygg-storage]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.distributed.workspace-peer :as wp]
            [org.replikativ.spindel.distributed.workspace-peer-sync :as wps]))

(defn- get-free-port []
  (let [s (java.net.ServerSocket. 0)] (try (.getLocalPort s) (finally (.close s)))))

(defn- temp-dir [prefix]
  (.getAbsolutePath (io/file (System/getProperty "java.io.tmpdir")
                             (str prefix "-" (System/currentTimeMillis) "-" (rand-int 100000)))))

(defn- rm-rf [path]
  (let [d (io/file path)]
    (when (.exists d) (doseq [f (reverse (file-seq d))] (.delete f)))))

(defn- poll-until [pred timeout-ms]
  (let [deadline (+ (System/currentTimeMillis) timeout-ms)]
    (loop []
      (cond (pred) true
            (> (System/currentTimeMillis) deadline) false
            :else (do (Thread/sleep 100) (recur))))))

(defn- datahike-fressian-middleware [peer-config]
  (fressian (atom fh/read-handlers) (atom fh/write-handlers) peer-config))

(def ^:private ygg-sync-opts
  (ks-pss/make-pss-sync-opts :crdt/roots #{:crdt/roots :crdt/freed}
                             ygg-storage/node-child-addresses))

(def ^:private server-id #uuid "30000000-0000-0000-0000-0000000000f1")
(def ^:private client-id #uuid "30000000-0000-0000-0000-0000000000f2")

;; content-addressed roots → normalize to a stable comparable token
(defn- roots-token [roots] (set (map str roots)))

(deftest wire-topology-subscriber-follow-over-kabel
  (testing "the G-Set store replicates over kabel; wire-topology!'s :subscriber path
            drives the gate, and the workspace-peer re-seats onto the synced system
            once its head catches up to the descriptor"
    (let [port    (get-free-port)
          url     (str "ws://localhost:" port)
          ygg-id  #uuid "30000000-0000-0000-0000-0000000000d2"
          ygg-topic ygg-id
          s-path  (temp-dir "wt-sygg")
          c-path  (temp-dir "wt-cygg")
          s-cfg   {:backend :file :path s-path :id ygg-id}
          c-cfg   {:backend :file :path c-path :id ygg-id}]
      (try
        (let [s-ygg        (g/flush! (-> (g/gset (str ygg-id) {:store-config s-cfg} {:sync? true})
                                         (g/conj :alpha) (g/conj :beta)))
              s-store      (:kv-store s-ygg)
              target-head  (roots-token (<!! (k/get s-store :crdt/roots)))
              handler      (create-http-kit-handler! S url server-id)
              server-peer  (peer/server-peer S handler server-id
                                             (comp (sync/server-middleware) ds/remote-middleware)
                                             datahike-fressian-middleware)
              _            (<?? S (peer/start server-peer))
              _            (ds/invoke-on-peer server-peer)
              _            (sync/register-store! server-peer ygg-topic s-store ygg-sync-opts)
              client-peer  (peer/client-peer S client-id
                                             (comp (sync/client-middleware) ds/remote-middleware)
                                             datahike-fressian-middleware)
              _            (ds/invoke-on-peer client-peer)
              _            (<?? S (peer/connect S client-peer url))
              c-store      (:kv-store (durable/open c-cfg {} {:sync? true}))
              ctx          (ctx/create-execution-context)
              wpeer        (wp/make-workspace-peer
                            {:ctx ctx
                             :resolve-system-fn (fn [_sid _branch]
                                                  (g/gset (str ygg-id) {:kv-store c-store} {:sync? true}))})
              descriptor   {:branch  :crdt/roots
                            :owner   :server
                            :systems {"set" {:branch :crdt/roots :head target-head :topic ygg-topic}}}]
          ;; local checkout intent (in dvergr this rides signal_sync; see ns docstring)
          (wp/set-descriptor! wpeer descriptor)
          ;; FOLLOW: wire the :subscriber store subscription through wire-topology!
          (let [wired (wps/wire-topology!
                       wpeer client-peer descriptor
                       (fn [_sid] c-store)                                  ; store-lookup
                       :subscribe-fn (fn [cp topic store opts]
                                       (<?? S (sync/subscribe-store! cp topic store opts)))
                       :sync-opts-lookup (constantly ygg-sync-opts)
                       :head-token-fn roots-token
                       :branch-key? #{:crdt/roots})]
            (is (contains? (:stores wired) "set") "the :subscriber system was store-wired"))

          (is (poll-until #(some? (wp/current-workspace wpeer)) 15000)
              "client re-seats once the synced G-Set head reaches the descriptor head")
          (is (= #{:alpha :beta}
                 (g/elements (get (wp/current-workspace wpeer) "set")))
              "the re-seated system reflects the G-Set replicated over the wire")

          (ctx/stop-context! ctx)
          (sync/unsubscribe-store! client-peer ygg-topic)
          (<?? S (peer/stop client-peer))
          (sync/unregister-store! server-peer ygg-topic)
          (<?? S (peer/stop server-peer)))
        (finally
          (rm-rf s-path) (rm-rf c-path))))))
