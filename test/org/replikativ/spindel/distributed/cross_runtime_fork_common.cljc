(ns org.replikativ.spindel.distributed.cross-runtime-fork-common
  "Shared wiring for the cross-RUNTIME FORK/MERGE proof: a cljs(node) peer runs the
   full async `fork-remote!` → write-on-fork → `merge-fork-remote!` lifecycle against
   a REAL local datahike (memory) system, while connected over one live websocket to
   a JVM server peer. The merged item-names are then published over a synced G-Set so
   the JVM peer OBSERVES the cljs merge result — i.e. the cljs fork/merge lifecycle
   (incl. the async-cljs datahike-adapter `merge!` writer-channel fix) really ran.

   Scope note: the datahike STORE is local to the cljs peer (memory) — syncing a
   datahike store's nodes over kabel is dvergr's multi-middleware job, out of scope
   here. What crosses the wire is the merge RESULT (plain item-names via the proven
   G-Set transport), which is enough to prove the lifecycle executed on the cljs peer."
  (:require [org.replikativ.spindel.distributed.signal-sync :as ss]
            [org.replikativ.spindel.ygg-signal :as ys]
            [kabel.middleware.fressian :refer [fressian]]
            [yggdrasil.wire :as wire]
            [yggdrasil.convergent.gset :as g]))

(def port 47398)                                  ; distinct from the G-Set proof (47399)
(def url (str "ws://localhost:" port))
(def server-id #uuid "dddddddd-0000-0000-0000-000000000001")
(def client-id #uuid "dddddddd-0000-0000-0000-000000000002")
(def items-topic :cross-runtime/fork-items)

(defn wire-middleware
  "fressian serializer with the yggdrasil.wire CRDT handlers (replaces bare transit). Ships
   plain data (state-fn + δ), so `resolve-storage` is never called — a nil resolver is safe."
  ([] (wire-middleware nil))
  ([storage]
   (fn [peer-config]
     (fressian (atom (wire/read-handlers {:resolve-storage (constantly storage)}))
               (atom (wire/write-handlers))
               peer-config))))

(defn mem-gset
  "In-memory result G-Set, `:sync? true` on both platforms (memory ops are sync even
   on cljs). Carries the merged datahike item-names across the wire."
  [id]
  (g/gset id {:store-config {:backend :memory :id (random-uuid)}} {:sync? true}))

(defn sync-items!
  "Bidirectional convergent sync of the merged-item-names G-Set `sig` over
   `items-topic`. `owner?` = the kabel pubsub hub (the JVM server)."
  [peer sig owner?]
  (ss/sync-signal! peer items-topic sig
                   :owner?         owner?
                   :delta-fn       ys/ygg-delta-fn
                   :clear-delta-fn ys/ygg-clear-delta-fn
                   :apply-delta-fn (ys/ygg-apply-delta-fn true)
                   :state-fn       (fn [v] (g/elements v {:sync? true}))
                   :sync?          true))

(defn add-item! [sig x] (swap! sig (fn [s] (g/conj s x {:sync? true}))))
(defn items [sig] (g/elements @sig {:sync? true}))
