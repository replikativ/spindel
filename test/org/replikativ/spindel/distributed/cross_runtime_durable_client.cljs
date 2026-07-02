(ns org.replikativ.spindel.distributed.cross-runtime-durable-client
  "cljs(node) side of the DURABLE cross-runtime proof: a kabel node client with a
   konserve **node-filestore** G-Set connects to the JVM server, receives the server's
   NODES over konserve-sync + its VALUE (the CRDT root, `ygg/system`) over signal-sync
   on ONE fressian serializer, `-join`s the value into its own local G-Set (which
   AUTO-FLUSHES → the head persists to the node-filestore), and then proves it survived
   a COLD RESTART (reopen the node-filestore from the path). Exits 0 iff both the live
   convergence AND the reopened value are `#{:alpha :beta}`.

   The convergent ops run `:sync? false` — the genuine cljs async durable path. yggdrasil
   ops return partial-cps CPS values (not core.async channels), so this bridges them to
   core.async via `is.simm.partial-cps.core-async` (`->chan`/`unwrap-result`), exactly as
   the cross-runtime FORK client does."
  (:require [kabel.peer :as peer]
            [kabel.pubsub :as pubsub]
            [konserve.node-filestore]           ; registers the :file backend on node
            [konserve-sync.core :as ks]
            [org.replikativ.spindel.distributed.signal-sync :as ss]
            [org.replikativ.spindel.ygg-signal :as ys]
            [org.replikativ.spindel.distributed.cross-runtime-durable-common :as c]
            [is.simm.partial-cps.core-async :as cps]
            [yggdrasil.convergent.gset :as g]
            [superv.async :refer [S] :refer-macros [<?]]
            [clojure.core.async :refer [<! timeout go] :include-macros true]))

;; open (or reopen) the client's node-filestore G-Set — bridge the partial-cps CPS.
(defn- open-gset []
  (cps/->chan (g/gset c/gid {:store-config {:backend :file :path c/client-path :id c/client-store-id}}
                      {:sync? false})))

(defn- elements-ch [gset]
  (cps/->chan (g/elements gset {:sync? false})))

(defn -main [& _]
  (go
    (try
      (let [c-gset    (cps/unwrap-result (<! (open-gset)))
            c-store   (:kv-store c-gset)
            c-storage (:storage c-gset)
            c-sig     (atom c-gset)             ; local G-Set; incoming value -joins into it
            client    (peer/client-peer S c/client-id
                                        (pubsub/make-pubsub-peer-middleware {})
                                        (c/wire-middleware c-storage))]
        (<? S (peer/connect S client c/url))
        (<! (timeout 800))
        ;; NODES first (konserve-sync), so the received value's root resolves locally.
        (<? S (ks/subscribe-store! client c/store-topic c-store c/nodes-only-opts))
        (<! (timeout 1500))
        ;; VALUE: -join incoming into c-sig (merge-fn); the join AUTO-FLUSHES → head persists.
        (ss/subscribe-signal! client c/value-topic
                              :atom c-sig :merge-fn (ys/ygg-merge-fn false) :sync? false)
        (<! (timeout 2500))
        (let [els (cps/unwrap-result (<! (elements-ch @c-sig)))]
          (println "XRT-DUR-CLIENT-CONVERGED" (pr-str els))
          (if (not= #{:alpha :beta} els)
            (do (println "CLIENT-FAIL not-converged" (pr-str els)) (js/process.exit 1))
            ;; COLD RESTART: reopen the node-filestore from the path (fresh handle).
            (let [reopened (cps/unwrap-result (<! (open-gset)))
                  rels     (cps/unwrap-result (<! (elements-ch reopened)))]
              (println "XRT-DUR-CLIENT-RESTART" (pr-str rels))
              (if (= #{:alpha :beta} rels)
                (do (println "XRT-DUR-CLIENT-OK persisted-across-cold-restart") (js/process.exit 0))
                (do (println "CLIENT-FAIL not-persisted" (pr-str rels)) (js/process.exit 1)))))))
      (catch :default e
        (println "CLIENT-ERROR" (str e))
        (when (.-stack e) (println "STACK" (.-stack e)))
        (js/process.exit 3)))))
