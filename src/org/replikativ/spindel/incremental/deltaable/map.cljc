(ns org.replikativ.spindel.incremental.deltaable.map
  "DeltaableMap - map with top-level delta tracking.

   Tracks assoc, dissoc, and other top-level map operations as deltas.
   Inner values are stored as-is (no deep wrapping)."
  (:require [org.replikativ.spindel.incremental.deltaable.protocols :as proto]))

#?(:clj
   (deftype DeltaableMap [m deltas _meta]
     ;; NO path field - always top-level
     ;; NO nested wrapping - inner values are plain

     proto/PDeltaable
     (get-deltas [_]
       "Returns sequence of deltas from this operation"
       deltas)
     (deltaable? [_]
       "DeltaableMap is a deltaable collection"
       true)

     clojure.lang.IPersistentCollection
     (cons [this o]
       "Add key-value pair to map"
       (if (map-entry? o)
         (.assoc this (key o) (val o))
         (throw (IllegalArgumentException. "cons on map expects MapEntry"))))

     (empty [_]
       "Return empty deltaable map"
       (DeltaableMap. {} [] _meta))

     (equiv [this other]
       "DeltaableMap only equals other DeltaableMap with same value + deltas"
       (or (identical? this other)
           (and (instance? DeltaableMap other)
                (= m (.-m other))
                (= deltas (.-deltas other)))))

     ;; IPersistentMap
     clojure.lang.IPersistentMap
     (assoc [this k v]
       "Associate key with value (records top-level delta only)"
       (let [is-update? (contains? m k)
             old-value (when is-update? (get m k))
             new-delta (if is-update?
                        {:delta :update
                         :path [k]
                         :value v
                         :old-value old-value}
                        {:delta :add
                         :path [k]
                         :value v})]
         (DeltaableMap. (assoc m k v) (conj deltas new-delta) _meta)))

     (without [this k]
       "Remove key from map (records top-level delta only)"
       (if (contains? m k)
         (let [old-value (get m k)
               new-delta {:delta :remove
                         :path [k]
                         :old-value old-value}]
           (DeltaableMap. (dissoc m k) (conj deltas new-delta) _meta))
         this))

     ;; ILookup
     clojure.lang.ILookup
     (valAt [this k]
       (get m k))
     (valAt [this k not-found]
       (get m k not-found))

     ;; Seqable
     clojure.lang.Seqable
     (seq [_] (seq m))

     ;; Associative
     clojure.lang.Associative
     (containsKey [this k]
       (contains? m k))
     (entryAt [this k]
       (when (contains? m k)
         (clojure.lang.MapEntry. k (get m k))))

     ;; Counted
     clojure.lang.Counted
     (count [_] (count m))

     ;; IObj
     clojure.lang.IObj
     (meta [_] _meta)
     (withMeta [this new-meta]
       (DeltaableMap. m deltas new-meta))

     ;; IDeref - convenience for unwrapping
     clojure.lang.IDeref
     (deref [_]
       "Unwrap to plain map"
       m)

     ;; IFn - enable (map :key) syntax
     clojure.lang.IFn
     (invoke [this k]
       (get m k))
     (invoke [this k not-found]
       (get m k not-found))

     ;; Iterable - needed for keys, vals, reduce, etc.
     java.lang.Iterable
     (iterator [_]
       (.iterator m))

     ;; IMapIterable - enables efficient keyIterator/valIterator
     clojure.lang.IMapIterable
     (keyIterator [_]
       (clojure.lang.RT/iter (keys m)))
     (valIterator [_]
       (clojure.lang.RT/iter (vals m)))

     ;; Object
     Object
     (toString [_]
       (str m))
     (hashCode [_]
       (.hashCode m))
     (equals [this other]
       "DeltaableMap equals other DeltaableMap if both value and deltas match.
        Use (= plain (->plain deltaable)) for plain collection comparison."
       (or (identical? this other)
           (and (instance? DeltaableMap other)
                (= m (.-m other))
                (= deltas (.-deltas other))))))

   :cljs
   (deftype DeltaableMap [m deltas _meta]
     ;; NO nested wrapping - inner values are plain

     proto/PDeltaable
     (get-deltas [_]
       deltas)
     (deltaable? [_]
       "DeltaableMap is a deltaable collection"
       true)

     ICollection
     (-conj [this entry]
       (if (map-entry? entry)
         (-assoc this (key entry) (val entry))
         (throw (js/Error. "conj on map expects MapEntry"))))

     IEmptyableCollection
     (-empty [_]
       (DeltaableMap. {} [] _meta))

     IEquiv
     (-equiv [this other]
       (or (identical? this other)
           (and (map? other)
                (= (count m) (count other))
                (let [other-m (if (instance? DeltaableMap other)
                                (.-m other)
                                other)]
                  (= m other-m)))))

     IAssociative
     (-assoc [this k v]
       "Associate key with value (records top-level delta only)"
       (let [is-update? (contains? m k)
             old-value (when is-update? (get m k))
             new-delta (if is-update?
                        {:delta :update
                         :path [k]
                         :value v
                         :old-value old-value}
                        {:delta :add
                         :path [k]
                         :value v})]
         (DeltaableMap. (assoc m k v) (conj deltas new-delta) _meta)))
     (-contains-key? [this k]
       (contains? m k))

     IMap
     (-dissoc [this k]
       "Remove key from map (records top-level delta only)"
       (if (contains? m k)
         (let [old-value (get m k)
               new-delta {:delta :remove
                         :path [k]
                         :old-value old-value}]
           (DeltaableMap. (dissoc m k) (conj deltas new-delta) _meta))
         this))

     ILookup
     (-lookup [this k]
       (get m k))
     (-lookup [this k not-found]
       (get m k not-found))

     ISeqable
     (-seq [_] (seq m))

     ICounted
     (-count [_] (count m))

     IMeta
     (-meta [_] _meta)

     IWithMeta
     (-with-meta [this new-meta]
       (DeltaableMap. m deltas new-meta))

     IDeref
     (-deref [_] m)

     IFn
     (-invoke [this k]
       (get m k))
     (-invoke [this k not-found]
       (get m k not-found))

     Object
     (toString [_]
       (str m))))

(defn deltaable-map
  "Create a DeltaableMap that tracks all assoc/dissoc operations as deltas (NO deep wrapping).

   Values are stored as-is without wrapping nested collections.
   Only top-level key operations are tracked as deltas.

   Example:
     (deltaable-map {:a 1 :b 2})
     (deltaable-map {:users [{:name \"Alice\"}]})  ; Nested vectors/maps NOT wrapped"
  [coll]
  (DeltaableMap. (into {} coll) [] nil))

(defn deltaable-map-with-deltas
  "Create a DeltaableMap with pre-computed deltas.

   This is used when you've already computed the deltas (e.g., from attribute
   reconciliation) and want to create a DeltaableMap that carries those deltas.

   Args:
     m - The map value
     deltas - Vector of delta maps (or nil for no deltas)

   Example:
     (deltaable-map-with-deltas {:a 1} [{:delta :update :path [:a] :value 1 :old-value 0}])"
  [m deltas]
  (DeltaableMap. (into {} m) (or deltas []) nil))
