(ns org.replikativ.spindel.distributed.inspector
  "Remote object inspector with reactive delta-based navigation and editing.

  Provides a protocol-driven reflection system that works across Kabel peers
  via SignalSyncStrategy. Objects are reflected one level deep, navigation
  drills into fields lazily, and edits produce transactions that propagate
  reactively.

  Server-side:
    (def insp (create-inspector my-datahike-entity conn))
    (export-signal! peer :inspect/entity (:signal insp))
    ;; Navigate: ((:navigate! insp) [:team 0])
    ;; Edit:     ((:edit! insp) [:team 0] :name \"New Name\")

  Client-side:
    (def view (subscribe-signal! peer :inspect/entity))
    ;; @view => {:op :expand :path [...] :node {...fields...}}
    ;; Client accumulates nodes into a tree, renders incrementally.

  Design:
    - Each navigation step sends ONE node over the wire (~200-1500 bytes)
    - Object cache (UUID → JVM object) holds non-serializable values server-side
    - Editable protocol enables write-back for Datahike entities, atoms, etc.
    - All updates flow through signals → reactive propagation to all clients"
  (:require [clojure.datafy :as d]
            [clojure.core.protocols :as cp]))

;; =============================================================================
;; Object Cache
;; =============================================================================

(def ^:private object-cache
  "UUID → JVM object. Holds non-serializable values server-side.
  Clients reference them by UUID; navigation resolves via cache."
  (atom {}))

(defn- cache!
  "Store object in cache, return UUID reference."
  [obj]
  (let [id (java.util.UUID/randomUUID)]
    (swap! object-cache assoc id obj)
    id))

(defn- cached
  "Retrieve object from cache by UUID."
  [id]
  (get @object-cache id))

(defn clear-cache!
  "Clear the object cache. Call when inspector sessions are disposed."
  []
  (reset! object-cache {}))

;; =============================================================================
;; Protocols
;; =============================================================================

(defprotocol Reflectable
  "Produce a serializable one-level-deep description of a value.
  Implementations should return a map with:
    :label    - human-readable string
    :class    - fully-qualified class name
    :fields   - [{:key k :summary {...} :editable? bool :entity-id eid :attribute attr}]
    :truncated? - true if fields were cut off"
  (reflect [this]
    "Return a serializable node description. Fields contain summaries,
    not full values — navigable fields have :ref UUIDs into the cache."))

(defprotocol Editable
  "Write back a field change. Returns Datahike tx-data (vector of tx forms)
  or nil if the edit was applied directly (e.g., atom swap)."
  (edit-field [this field-key new-value]
    "Apply an edit to field-key. Returns tx-data or nil."))

;; =============================================================================
;; Summarize: one value → serializable description
;; =============================================================================

(defn summarize
  "Produce a short serializable summary of a value.
  Large/complex values get a cache ref instead of full content."
  [v max-length]
  (cond
    (nil? v)     {:type :nil :value nil :nav? false}
    (string? v)  {:type :string :nav? false
                  :value (if (> (count v) max-length)
                           (str (subs v 0 max-length) "...")
                           v)}
    (number? v)  {:type :number :value v :nav? false}
    (boolean? v) {:type :boolean :value v :nav? false}
    (keyword? v) {:type :keyword :value v :nav? false}
    (symbol? v)  {:type :symbol :value (str v) :nav? false}
    (fn? v)      {:type :fn :ref (cache! v) :nav? false :value "<fn>"}
    (map? v)     {:type :map :count (count v) :nav? true :ref (cache! v)
                  :preview (binding [*print-length* 3 *print-level* 1] (pr-str v))}
    (or (vector? v) (sequential? v))
                 {:type :seq :count (bounded-count 1000 v) :nav? true :ref (cache! v)
                  :preview (binding [*print-length* 3 *print-level* 1] (pr-str v))}
    (set? v)     {:type :set :count (count v) :nav? true :ref (cache! v)
                  :preview (binding [*print-length* 3 *print-level* 1] (pr-str v))}
    :else        {:type :object :class (.getSimpleName (class v)) :nav? true
                  :ref (cache! v)
                  :value (try (binding [*print-length* 3 *print-level* 1] (pr-str v))
                              (catch Exception _ (.getSimpleName (class v))))}))

;; =============================================================================
;; Default Reflectable implementations
;; =============================================================================

(defn- reflect-map
  "Reflect a map (including datafied objects) with optional entity metadata."
  [original datafied & {:keys [entity-id]}]
  {:label (if (= original datafied)
            (str (count datafied) "-entry map")
            (.getSimpleName (class original)))
   :class (.getName (class original))
   :fields (mapv (fn [[k v]]
                   (cond-> {:key (if (or (keyword? k) (string? k) (number? k))
                                   k (pr-str k))
                            :summary (summarize v 100)}
                     entity-id (assoc :editable? true
                                      :entity-id entity-id
                                      :attribute k)))
                 (take 50 datafied))
   :truncated? (> (count datafied) 50)})

(defn- reflect-sequential [v datafied]
  {:label (str (.getSimpleName (class v)) " [" (bounded-count 1000 datafied) "]")
   :class (.getName (class v))
   :fields (vec (map-indexed (fn [i val] {:key i :summary (summarize val 100)})
                             (take 50 datafied)))
   :truncated? (> (bounded-count 51 datafied) 50)})

(defn- reflect-java-object
  "Reflect a Java object via field access + zero-arg method listing."
  [v]
  (let [cls (class v)
        fields (try
                 (->> (.getDeclaredFields cls)
                      (mapv (fn [f]
                              (.setAccessible f true)
                              {:key (str (.getName f))
                               :summary (summarize
                                          (try (.get f v)
                                               (catch Exception _ :inaccessible))
                                          100)
                               :editable? (not (java.lang.reflect.Modifier/isFinal
                                                 (.getModifiers f)))
                               :java-field (.getName f)})))
                 (catch Exception _ []))
        methods (->> (.getMethods cls)
                     (filter #(zero? (.getParameterCount %)))
                     (remove #(#{"wait" "notify" "notifyAll" "getClass"} (.getName %)))
                     (take 20)
                     (mapv (fn [m]
                             {:key (str "." (.getName m) "()")
                              :summary {:type :method
                                        :return (.getSimpleName (.getReturnType m))
                                        :nav? true
                                        :ref (cache! (fn [] (.invoke m v (into-array Object []))))}})))]
    {:label (.getSimpleName cls)
     :class (.getName cls)
     :fields (vec (concat fields methods))}))

(defn reflect-value
  "Reflect any value. Uses datafy protocol, falls back to Java reflection.
  If entity-id is provided, marks map fields as editable.
  Atoms are deref'd and their contents reflected with :editable? true."
  [v & {:keys [entity-id atom-source?]}]
  (cond
    ;; Atoms: deref and reflect contents, mark fields as editable
    (instance? clojure.lang.Atom v)
    (let [inner @v
          datafied (try (d/datafy inner) (catch Exception _ inner))]
      (if (map? datafied)
        (-> (reflect-map inner datafied)
            (assoc :label (str "Atom<" (.getSimpleName (class inner)) ">"))
            (update :fields (fn [fields]
                              (mapv #(assoc % :editable? true :atom-backed? true) fields))))
        (reflect-value inner)))

    :else
    (let [datafied (try (d/datafy v) (catch Exception _ v))]
      (cond
        (map? datafied)        (reflect-map v datafied :entity-id entity-id)
        (sequential? datafied) (reflect-sequential v datafied)
        (set? datafied)        (reflect-sequential v (vec datafied))
        :else                  (reflect-java-object v)))))

;; Default Reflectable implementations via extend-protocol
(extend-protocol Reflectable
  clojure.lang.IPersistentMap
  (reflect [m] (reflect-value m))

  clojure.lang.IPersistentVector
  (reflect [v] (reflect-value v))

  clojure.lang.IPersistentSet
  (reflect [s] (reflect-value s))

  clojure.lang.ISeq
  (reflect [s] (reflect-value s))

  Object
  (reflect [o] (reflect-value o)))

;; Default Editable implementations
(extend-protocol Editable
  clojure.lang.Atom
  (edit-field [a field-key new-value]
    (swap! a assoc field-key new-value)
    nil)

  clojure.lang.IPersistentMap
  (edit-field [_m _field-key _new-value]
    ;; Immutable maps can't be edited in place.
    ;; For Datahike entities, use the entity-id based tx path instead.
    nil)

  Object
  (edit-field [_o _field-key _new-value]
    nil))

;; =============================================================================
;; Inspector Session
;; =============================================================================

(defn create-inspector
  "Create an inspector session for an object.

  Args:
    root-obj - The object to inspect
    opts     - Optional map:
               :conn      - Datahike connection (enables entity editing)
               :entity-id - If root is a Datahike entity, its :db/id

  Returns map with:
    :signal    - atom holding latest delta (for SignalSyncStrategy)
    :tree      - atom holding accumulated {path → node}
    :navigate! - (fn [path]) drill into a field
    :collapse! - (fn [path]) remove expanded subtree
    :edit!     - (fn [path field-key new-value]) update a field
    :refresh!  - (fn [path]) re-reflect node at path"
  [root-obj & {:keys [conn entity-id]}]
  (let [tree (atom {})
        signal (atom nil)
        ;; Map path → source object for edit-back
        path-objects (atom {})
        root-node (reflect-value root-obj :entity-id entity-id)]

    ;; Initialize root
    (swap! tree assoc [] root-node)
    (swap! path-objects assoc [] root-obj)
    (reset! signal {:op :set-root :path [] :node root-node})

    {:signal signal
     :tree tree

     :navigate!
     (fn navigate! [path]
       (let [parent-path (vec (butlast path))
             field-key (last path)
             parent-node (get @tree parent-path)]
         (when parent-node
           (let [field (first (filter #(= field-key (:key %)) (:fields parent-node)))
                 summary (:summary field)]
             (when (and summary (:nav? summary))
               (let [ref-id (:ref summary)
                     obj (when ref-id
                           (let [c (cached ref-id)]
                             (if (fn? c) (c) c)))]
                 (when obj
                   (let [;; If parent was a Datahike entity and this is a ref,
                         ;; the child might also be an entity
                         child-eid (when (and conn (map? obj) (:db/id obj))
                                     (:db/id obj))
                         node (reflect-value obj :entity-id child-eid)
                         ;; If parent is atom-backed, propagate editability
                         parent-atom? (or (:atom-backed? field)
                                          (instance? clojure.lang.Atom
                                                     (get @path-objects parent-path)))
                         node (if (and parent-atom? (map? obj))
                                (update node :fields
                                        (fn [fs] (mapv #(assoc % :editable? true
                                                                :atom-backed? true) fs)))
                                node)]
                     (swap! tree assoc path node)
                     (swap! path-objects assoc path obj)
                     (reset! signal {:op :expand :path path :node node})
                     node))))))))

     :collapse!
     (fn collapse! [path]
       (let [remove-prefix (fn [m prefix]
                             (into {} (remove (fn [[k _]]
                                                (and (>= (count k) (count prefix))
                                                     (= prefix (vec (take (count prefix) k))))))
                                   m))]
         (swap! tree remove-prefix path)
         (swap! path-objects remove-prefix path)
         (reset! signal {:op :collapse :path path})))

     :edit!
     (fn edit! [path field-key new-value]
       (let [node (get @tree path)
             obj (get @path-objects path)
             field (when node
                     (first (filter #(= field-key (:key %)) (:fields node))))]
         (when (and field (:editable? field))
           (cond
             ;; Datahike entity: transact via conn
             (and conn (:entity-id field))
             (let [eid (:entity-id field)
                   attr (:attribute field)
                   tx-data [[:db/add eid attr new-value]]]
               @(conn tx-data)  ;; d/transact returns future-like
               ;; Re-reflect the entity
               (let [updated (into {} (d/datafy (d/nav obj attr new-value)))
                     ;; For entity, re-fetch from conn
                     fresh-obj (if entity-id obj updated)
                     fresh-node (reflect-value fresh-obj :entity-id (:entity-id field))]
                 (swap! tree assoc path fresh-node)
                 (swap! path-objects assoc path fresh-obj)
                 (reset! signal {:op :update :path path :node fresh-node})
                 tx-data))

             ;; Atom-backed field: swap the atom
             (or (instance? clojure.lang.Atom obj)
                 (:atom-backed? field))
             (let [;; Walk up to find the atom source
                   [the-atom atom-path]
                   (loop [p path]
                     (let [o (get @path-objects p)]
                       (cond
                         (instance? clojure.lang.Atom o) [o p]
                         (empty? p) [nil nil]
                         :else (recur (vec (butlast p))))))
                   ;; Build the nested path from atom root to this field
                   ;; path=[:config] atom-path=[] → nested-keys=[:config field-key]
                   ;; path=[:team 0] atom-path=[] → nested-keys=[:team 0 field-key]
                   nested-keys (vec (concat (drop (count atom-path) path)
                                           [field-key]))]
               (when the-atom
                 (swap! the-atom assoc-in nested-keys new-value)
                 ;; Re-reflect the current node from the updated atom value
                 (let [updated-val (get-in @the-atom (drop (count atom-path) path))
                       fresh-node (if (= path atom-path)
                                    (reflect-value the-atom)
                                    (reflect-value updated-val))
                       ;; Mark fields editable for atom-backed nodes
                       fresh-node (update fresh-node :fields
                                         (fn [fields]
                                           (mapv #(assoc % :editable? true
                                                          :atom-backed? true) fields)))]
                   (swap! tree assoc path fresh-node)
                   (reset! signal {:op :update :path path :node fresh-node})
                   nil)))

             ;; Mutable Java field
             (and (:java-field field) (not (nil? obj)))
             (try
               (let [f (.getDeclaredField (class obj) (:java-field field))]
                 (.setAccessible f true)
                 (.set f obj new-value)
                 (let [fresh-node (reflect-value obj)]
                   (swap! tree assoc path fresh-node)
                   (reset! signal {:op :update :path path :node fresh-node})
                   nil))
               (catch Exception e
                 (reset! signal {:op :error :path path
                                 :error (str "Edit failed: " (.getMessage e))})
                 nil))

             :else nil))))

     :refresh!
     (fn refresh! [path]
       (let [obj (get @path-objects path)]
         (when obj
           (let [eid (when (and conn (map? obj) (:db/id obj)) (:db/id obj))
                 node (reflect-value obj :entity-id eid)]
             (swap! tree assoc path node)
             (reset! signal {:op :update :path path :node node})
             node))))}))

;; =============================================================================
;; Batch edit support
;; =============================================================================

(defn batch-edit!
  "Apply multiple field edits as a single Datahike transaction.

  Args:
    inspector - Inspector session map
    path      - Path to the node being edited
    edits     - Map of {field-key → new-value}

  Returns: tx-data vector or nil"
  [{:keys [tree signal] :as _inspector} conn path edits]
  (let [node (get @tree path)]
    (when node
      (let [tx-data (->> edits
                         (keep (fn [[field-key new-value]]
                                 (let [field (first (filter #(= field-key (:key %))
                                                           (:fields node)))]
                                   (when (and field (:editable? field) (:entity-id field))
                                     [:db/add (:entity-id field)
                                              (:attribute field) new-value]))))
                         vec)]
        (when (seq tx-data)
          @(conn tx-data)
          ;; Refresh the node
          ((:refresh! _inspector) path)
          tx-data)))))
