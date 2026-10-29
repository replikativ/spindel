(ns org.replikativ.spindel.engine.owned-store
  "Internal row storage for the transition kernel. Rows are immutable values.
  Only engine transition code runs inside transact!; user code runs afterward.
  A transaction provides exclusive access across all worlds in this store.")

(defprotocol ^:private PTable
  (-read-row [table id absent])
  (-put! [table id value])
  (-delete! [table id])
  (-freeze! [table]))

(deftype Table [#?(:clj ^:unsynchronized-mutable rows :cljs ^:mutable rows)]
  PTable
  (-read-row [_ id absent] (get rows id absent))
  (-put! [_ id value] (set! rows (assoc! rows id value)))
  (-delete! [_ id] (set! rows (dissoc! rows id)))
  (-freeze! [_]
    (let [basis (persistent! rows)]
      (set! rows (transient basis))
      basis)))

(defn- table [rows] (Table. (transient rows)))
(def ^:private absent #?(:clj (Object.) :cljs (js-obj)))

(defrecord Store [gate worlds active])
(defrecord Transaction [store undo active owner])

(defn create-store
  "Create a store from world-id -> table-name -> immutable row map."
  ([] (create-store {}))
  ([worlds]
   (->Store #?(:clj (Object.) :cljs nil)
            (volatile!
             (reduce-kv (fn [result w tables]
                          (assoc result w
                                 (reduce-kv (fn [result name rows]
                                              (assoc result name (table rows)))
                                            {} tables)))
                        {} worlds))
            (volatile! false))))

(defn- check-active! [tx]
  (when-not (and @(:active tx)
                 #?(:clj (identical? (:owner tx) (Thread/currentThread))
                    :cljs true))
    (throw (ex-info "Transaction has ended" {}))))

(defn- lookup-table [tx world name]
  (get-in @(:worlds (:store tx)) [world name]))

(defn read-row
  "Read inside transact!. Internal table objects never escape."
  ([tx world name id] (read-row tx world name id nil))
  ([tx world name id not-found]
   (check-active! tx)
   (if-let [t (lookup-table tx world name)]
     (-read-row t id not-found)
     not-found)))

(defn- writable-table! [tx world name]
  (or (lookup-table tx world name)
      (let [t (table {})]
        (vswap! (:worlds (:store tx)) assoc-in [world name] t)
        t)))

(defn table-view
  "Seal one table for an explicit sweep or diagnostic. Ordinary transitions
  use row indexes; this view rotates the table's edit token."
  [tx world name]
  (check-active! tx)
  (if-let [t (lookup-table tx world name)] (-freeze! t) {}))

(defn put-row! [tx world name id value]
  (check-active! tx)
  (let [t (writable-table! tx world name)]
    (vswap! (:undo tx) conj [t id (-read-row t id absent)])
    (-put! t id value))
  value)

(defn delete-row! [tx world name id]
  (check-active! tx)
  (when-let [t (lookup-table tx world name)]
    (let [old (-read-row t id absent)]
      (when-not (identical? absent old)
        (vswap! (:undo tx) conj [t id old])
        (-delete! t id))))
  nil)

(defn- run-transaction! [store f]
  (when @(:active store)
    (throw (ex-info "Nested engine transaction" {})))
  (let [before @(:worlds store)
        tx (->Transaction store (volatile! []) (volatile! true)
                          #?(:clj (Thread/currentThread) :cljs nil))]
    (vreset! (:active store) true)
    (try
      (f tx)
      (catch #?(:clj Throwable :cljs :default) error
        (doseq [[t id old] (rseq @(:undo tx))]
          (if (identical? absent old) (-delete! t id) (-put! t id old)))
        (vreset! (:worlds store) before)
        (throw error))
      (finally
        (vreset! (:active tx) false)
        (vreset! (:active store) false)))))

(defn transact!
  "Atomically run an engine transition, rolling back all row edits on refusal.
  A transition must not call user code, fork, snapshot, or transact! recursively."
  [store f]
  #?(:clj (locking (:gate store) (run-transaction! store f))
     :cljs (run-transaction! store f)))

(defn- freeze-store! [store]
  (when @(:active store)
    (throw (ex-info "Snapshot inside engine transaction" {})))
  (reduce-kv (fn [worlds w tables]
               (assoc worlds w
                      (reduce-kv (fn [tables name t]
                                   (assoc tables name (-freeze! t)))
                                 {} tables)))
             {} @(:worlds store)))

(defn snapshot
  "Return immutable rows and rotate each table's edit token. Cost follows the
  number of tables, independent of their row count. Never call inside transact!."
  [store]
  #?(:clj (locking (:gate store) (freeze-store! store))
     :cljs (freeze-store! store)))
