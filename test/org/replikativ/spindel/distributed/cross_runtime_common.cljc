(ns org.replikativ.spindel.distributed.cross-runtime-common
  "Shared wiring for the cross-RUNTIME bidirectional sync proof: a JVM kabel server
   and a cljs(node) kabel client converge a durable G-Set over one real websocket.
   The convergent ops run `:sync? true` on the JVM (blocking) and `:sync? false` on
   cljs (async over konserve's core.async memory store) — so the node client exercises
   the genuine async convergent path, not a JVM-sync shortcut."
  (:require [org.replikativ.spindel.distributed.signal-sync :as ss]
            [org.replikativ.spindel.ygg-signal :as ys]
            [kabel.middleware.fressian :refer [fressian]]
            [yggdrasil.wire :as wire]
            [yggdrasil.convergent.gset :as g]))

(def port 47399)
(def url (str "ws://localhost:" port))
(def server-id #uuid "cccccccc-0000-0000-0000-000000000001")
(def client-id #uuid "cccccccc-0000-0000-0000-000000000002")
(def topic :cross-runtime/gset)

(defn wire-middleware
  "fressian serializer with the yggdrasil.wire CRDT handlers (replaces bare transit). These
   flows ship PLAIN DATA (state-fn `g/elements` + δ sets), so no system record crosses and
   `resolve-storage` is never called — a nil resolver is safe."
  ([] (wire-middleware nil))
  ([storage]
   (fn [peer-config]
     (fressian (atom (wire/read-handlers {:resolve-storage (constantly storage)}))
               (atom (wire/write-handlers))
               peer-config))))

(defn mem-gset [id]
  ;; IN-MEMORY store, :sync? true on BOTH platforms — memory ops are synchronous even
  ;; on cljs (no IO), so g/conj / g/elements stay sync. The cross-runtime async surface
  ;; that matters here is the kabel TRANSPORT (superv.async), not the CRDT storage.
  (g/gset id {:store-config {:backend :memory :id (random-uuid)}} {:sync? true}))

(defn sync-gset!
  "Bidirectional convergent sync of a G-Set signal `sig` over the shared topic.
   `owner?` = the kabel pubsub hub (the JVM server)."
  [peer sig owner?]
  (ss/sync-signal! peer topic sig
                   :owner?         owner?
                   :delta-fn       ys/ygg-delta-fn
                   :clear-delta-fn ys/ygg-clear-delta-fn
                   ;; force the sync apply variant (cljs convergent ops default async)
                   :apply-delta-fn (ys/ygg-apply-delta-fn true)
                   :state-fn       (fn [v] (g/elements v {:sync? true}))
                   :sync?          true))

(defn add!
  "Add element x to the G-Set signal (sync conj — cljs gset ops default async)."
  [sig x]
  (swap! sig (fn [s] (g/conj s x {:sync? true}))))

(defn els
  "Read the G-Set signal's elements synchronously."
  [sig]
  (g/elements @sig {:sync? true}))
