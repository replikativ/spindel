(ns org.replikativ.spindel.engine.owned-store
  "Internal row storage for the transition kernel. Rows are immutable values.
  Only engine transition code runs inside transact!; user code runs afterward.
  A transaction provides exclusive access across all worlds in this store."
  (:require [org.replikativ.spindel.engine.owned-rows :as cells]))

(defprotocol ^:private PTable
  (-read-row [table id absent])
  (-put! [table id value])
  (-delete! [table id])
  (-edit-owner [table])
  (-cell-layout [table])
  (-freeze! [table]))

(deftype Table [#?(:clj ^:unsynchronized-mutable rows :cljs ^:mutable rows)
                #?(:clj ^:unsynchronized-mutable owner :cljs ^:mutable owner)
                layout]
  PTable
  (-read-row [_ id absent] (get rows id absent))
  (-put! [_ id value]
    (set! rows (assoc! rows id (if (and layout (map? value) (not (cells/row? value)))
                                 (cells/create owner layout value) value))))
  (-delete! [_ id] (set! rows (dissoc! rows id)))
  (-edit-owner [_] owner)
  (-cell-layout [_] layout)
  (-freeze! [_]
    (let [basis (persistent! rows)]
      (set! rows (transient basis))
      (when layout (set! owner #?(:clj (Object.) :cljs (js-obj))))
      basis)))

(defn- table [rows layout pinned?]
  (let [wrap? (and layout (not pinned?))
        t (Table. (transient (if wrap? {} rows)) #?(:clj (Object.) :cljs (js-obj)) layout)]
    (when wrap? (doseq [[id row] rows] (-put! t id row)))
    t))
(def ^:private absent #?(:clj (Object.) :cljs (js-obj)))

(defrecord Store [gate worlds active journal layouts options])
(defrecord Transaction [store undo active owner])

(defn create-store
  "Create a store from world-id -> table-name -> immutable row map."
  ([] (create-store {}))
  ([worlds] (create-store worlds {}))
  ([worlds {:keys [cell-tables pinned?] :as options}]
   (let [layouts (select-keys cells/layouts cell-tables)]
     (->Store #?(:clj (Object.) :cljs nil)
              (volatile!
               (reduce-kv (fn [result w tables]
                            (assoc result w
                                   (reduce-kv (fn [result name rows]
                                                (assoc result name (table rows (get layouts name) pinned?)))
                                              {} tables)))
                          {} worlds))
              (volatile! false)
              #?(:clj (java.util.ArrayList.) :cljs (array))
              layouts options))))

(defn options [store] (:options store))

(defn- check-active! [tx]
  (when-not (and @(:active tx)
                 #?(:clj (identical? (:owner tx) (Thread/currentThread))
                    :cljs true))
    (throw (ex-info "Transaction has ended" {}))))

(defn- lookup-table [tx world name]
  (get (get @(:worlds (:store tx)) world) name))

(defn read-live-row
  "Kernel-only borrowed row. Valid only inside the transaction, until its
  next edit. Use read-row when retaining a before-image or returning to a host."
  ([tx world name id] (read-live-row tx world name id nil))
  ([tx world name id not-found]
   (check-active! tx)
   (if-let [t (lookup-table tx world name)]
     (-read-row t id not-found)
     not-found)))

(defn read-row
  ([tx world name id] (read-row tx world name id nil))
  ([tx world name id not-found]
   (cells/value (read-live-row tx world name id not-found))))

(defn- writable-table! [tx world name]
  (or (lookup-table tx world name)
      (let [t (table {} (get (:layouts (:store tx)) name) false)]
        (vswap! (:worlds (:store tx)) assoc-in [world name] t)
        t)))

(defn table-view
  "Seal one table for an explicit sweep or diagnostic. Ordinary transitions
  use row indexes; this view rotates the table's edit token."
  [tx world name]
  (check-active! tx)
  (if-let [t (lookup-table tx world name)] (-freeze! t) {}))

(defn- remember! [tx t id old]
  (let [journal (:undo tx)]
    #?(:clj (let [^java.util.ArrayList journal journal]
              (.add journal t)
              (.add journal id)
              (.add journal old))
       :cljs (.push journal t id old))))

(defn write-field!
  "Kernel-only field edit. A shared cell is copied before changing it; every
  pointer and field edit is journalled for rollback."
  [tx world name id key value]
  (check-active! tx)
  (let [t (lookup-table tx world name)
        old (-read-row t id nil)
        token (-edit-owner t)]
    (if (cells/row? old)
      (let [row (if (identical? token (cells/owner old)) old
                    (let [row (cells/copy old token)]
                      (remember! tx t id old)
                      (-put! t id row)
                      row))
            before (get row key absent)]
        (when-not (identical? before value)
          (remember! tx row key before)
          (cells/set-field! row token key value true)))
      (do (remember! tx t id old)
          (-put! t id (assoc old key value)))))
  value)

(defn put-row! [tx world name id value]
  (check-active! tx)
  (let [t (writable-table! tx world name)]
    (remember! tx t id (-read-row t id absent))
    (-put! t id value))
  value)

(defn delete-row! [tx world name id]
  (check-active! tx)
  (when-let [t (lookup-table tx world name)]
    (let [old (-read-row t id absent)]
      (when-not (identical? absent old)
        (remember! tx t id old)
        (-delete! t id))))
  nil)

(defn- run-transaction! [store f]
  (when @(:active store)
    (throw (ex-info "Nested engine transaction" {})))
  (let [before @(:worlds store)
        tx (->Transaction store (:journal store) (volatile! true)
                          #?(:clj (Thread/currentThread) :cljs nil))]
    (vreset! (:active store) true)
    (try
      (f tx)
      (catch #?(:clj Throwable :cljs :default) error
        (let [journal (:undo tx)]
          (loop [i (- #?(:clj (.size ^java.util.ArrayList journal) :cljs (.-length journal)) 3)]
            (when (>= i 0)
              (let [t #?(:clj (.get ^java.util.ArrayList journal i) :cljs (aget journal i))
                    id #?(:clj (.get ^java.util.ArrayList journal (inc i)) :cljs (aget journal (inc i)))
                    old #?(:clj (.get ^java.util.ArrayList journal (+ i 2)) :cljs (aget journal (+ i 2)))]
                (if (cells/row? t)
                  (cells/set-field! t (cells/owner t) id old (not (identical? absent old)))
                  (if (identical? absent old) (-delete! t id) (-put! t id old)))
                (recur (- i 3))))))
        (vreset! (:worlds store) before)
        (throw error))
      (finally
        #?(:clj (.clear ^java.util.ArrayList (:undo tx))
           :cljs (set! (.-length (:undo tx)) 0))
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
                                   (let [basis (-freeze! t)]
                                     (assoc tables name
                                            (if (-cell-layout t)
                                              (into {} (map (fn [[id row]] [id (cells/value row)])) basis)
                                              basis))))
                                 {} tables)))
             {} @(:worlds store)))

(defn snapshot
  "Return immutable rows and rotate each table's edit token. Cost follows the
  number of tables for immutable rows; owned cells are materialized for this
  diagnostic export. Physical fork attachment uses pin-world. Never call inside transact!."
  [store]
  #?(:clj (locking (:gate store) (freeze-store! store))
     :cljs (freeze-store! store)))

(defn pin-world
  "Pin a world's table roots for physical sharing without materializing its
  row cells. A child store edits shared cells only after copying them."
  [store world]
  (let [pin (fn []
              (when @(:active store)
                (throw (ex-info "Pin inside engine transaction" {})))
              (reduce-kv (fn [tables name t] (assoc tables name (-freeze! t)))
                         {} (get @(:worlds store) world)))]
    #?(:clj (locking (:gate store) (pin)) :cljs (pin))))
