(ns org.replikativ.spindel.incremental.deltaable
  "Deltaable collections for incremental computation with SHALLOW wrapping.

   This namespace provides collections that track TOP-LEVEL changes as deltas:
   - IDeltaable: Protocol for delta tracking
   - IUnwrapDeltaable: Protocol for unwrapping deltaables to plain collections
   - DeltaableVector/Map/Set: Top-level wrappers with delta tracking
   - DeltaableValue: Simple value wrapper (no structural deltas)

   **IMPORTANT**: Deltaables only track TOP-LEVEL operations!
   - Nested collections remain plain (no deep wrapping)
   - For fine-grained tracking, use separate signals

   Note: This namespace defines delta transducer functions (map, filter, etc.)
   that shadow clojure.core functions. These are intended to transform delta
   streams, not regular collections. Use with namespace qualification: (d/map f)

   Usage:

   (let [dm (deltaable-map {:a 1 :users []})]
     (-> dm
         (assoc :b 2)              ; :add delta for :b
         (update :users conj \"Alice\"))  ; :update delta for :users (NOT for conj)
     (get-deltas dm))  ; => [{:delta :add :path [:b] :value 2}
                       ;;     {:delta :update :path [:users] :value [\"Alice\"] :old-value []}]"
  (:refer-clojure :exclude [map filter remove keep transduce]))

;; Protocol: Collection-Level Structural Deltas

(defprotocol PDeltaable
  "Protocol for collections that track structural changes as deltas.

   Collections implementing this protocol record operations (conj, assoc, dissoc)
   and make them available as a sequence of deltas.

   Delta format:
   {:delta :add/:remove/:update
    :path [:users 0 :name]
    :value new-value
    :old-value old-value}  ; For :update only"
  (get-deltas [this]
    "Returns sequence of deltas since last reset, or nil if no structural deltas.

     For simple values (numbers, strings, keywords): returns nil
     For collections (vectors, maps, sets): returns [{:delta ...} ...]")
  (deltaable? [this]
    "Returns true if this is a deltaable collection (DeltaableVector/Map/Set).
     Returns false for plain values and non-deltaable collections."))

;; Protocol: Wrapping Custom Types as Deltaable (for extensibility)

(defprotocol PWrapDeltaable
  "Protocol for wrapping custom types as deltaable collections.

   Extend this protocol to add deltaable tracking to your custom types.
   This enables signals to contain custom types with delta tracking.

   Note: With shallow wrapping, this only wraps the TOP-LEVEL.
   Nested values remain plain collections."
  (wrap-deltaable [x]
    "Wrap x as a top-level deltaable collection.

     - For already-deltaable collections: returns unchanged
     - For plain vectors/maps/sets: wraps as DeltaableVector/Map/Set
     - For custom types: define your own implementation
     - For other values: returns unchanged (treated as leaf values)"))

;; Protocol: Unwrapping Deltaables to Plain Collections

(defprotocol PUnwrapDeltaable
  "Protocol for unwrapping deltaable collections to plain collections.

   Symmetric counterpart to IWrapDeltaable. Extend this protocol to provide
   custom unwrapping behavior for your types."
  (unwrap-deltaable [x]
    "Recursively unwrap deltaable collections to plain collections.

     - For deltaable collections: recursively unwraps to plain vectors/maps/sets
     - For plain values: returns unchanged
     - For nil: returns nil

     This is the explicit way to compare deltaable collections with plain ones,
     since deltaables only equal other deltaables with matching value + deltas."))

;; =============================================================================
;; Simple Value Wrapper (No Structural Deltas)
;; =============================================================================

#?(:clj
   (defrecord DeltaableValue [v]
     PDeltaable
     (get-deltas [_]
       "Simple values have no structural deltas"
       nil)
     (deltaable? [_]
       "DeltaableValue is not a deltaable collection"
       false)

     clojure.lang.IDeref
     (deref [_]
       "Deref returns the wrapped value"
       v))

   :cljs
   (defrecord DeltaableValue [v]
     PDeltaable
     (get-deltas [_]
       "Simple values have no structural deltas"
       nil)
     (deltaable? [_]
       "DeltaableValue is not a deltaable collection"
       false)

     IDeref
     (-deref [_]
       "Deref returns the wrapped value"
       v)))

(defn deltaable-value
  "Create a DeltaableValue wrapper for simple values.

   This is used for numbers, strings, keywords, etc. that don't have
   structural deltas but need to be treated uniformly with collections."
  [v]
  (->DeltaableValue v))

;; Extend protocol to everything for uniform interface

(extend-protocol PDeltaable
  #?(:clj Object :cljs default)
  (get-deltas [_]
    "Non-deltaable values return nil (no structural changes)"
    nil)
  (deltaable? [_]
    "Default: not a deltaable collection"
    false)

  nil
  (get-deltas [_]
    "nil has no deltas"
    nil)
  (deltaable? [_]
    "nil is not deltaable"
    false))

;; Helper Functions

(defn has-deltas?
  "Returns true if value has non-empty structural deltas.

   Returns false for:
   - nil
   - Non-deltaable values
   - Deltaable values with empty delta vector"
  [x]
  (seq (get-deltas x)))

(defn unwrap
  "Unwrap a deltaable value to get the raw value.

   For DeltaableValue: returns the wrapped value
   For DeltaableVector/Map/Set: returns the collection itself
   For other values: returns as-is

  Note: SignalDeltaView unwrapping is handled by signal.cljc"
  [x]
  (cond
    (instance? DeltaableValue x) (.-v x)
    :else x))

;; =============================================================================
;; DeltaableVector - Tracks TOP-LEVEL structural operations only
;; =============================================================================

#?(:clj
   (deftype DeltaableVector [v deltas _meta]
     ;; NO path field - always top-level
     ;; NO nested wrapping - inner values are plain

     PDeltaable
     (get-deltas [_]
       "Returns sequence of deltas from this operation"
       deltas)
     (deltaable? [_]
       "DeltaableVector is a deltaable collection"
       true)

     ;; IPersistentCollection
     clojure.lang.IPersistentCollection
     (count [_] (count v))

     (cons [this x]
       "Add element to end of vector (records top-level delta only)"
       (let [new-delta {:delta :add
                       :path [(count v)]
                       :value x}
             new-deltas (conj deltas new-delta)]
         (DeltaableVector. (conj v x) new-deltas _meta)))

     (empty [_]
       "Return empty deltaable vector"
       (DeltaableVector. [] [] _meta))

     (equiv [this other]
       "DeltaableVector only equals other DeltaableVector with same value + deltas"
       (or (identical? this other)
           (and (instance? DeltaableVector other)
                (= v (.-v other))
                (= deltas (.-deltas other)))))

     ;; IPersistentVector
     clojure.lang.IPersistentVector
     (assocN [this i x]
       "Update element at index i or add new element (records top-level delta only)"
       (let [is-update? (< i (count v))
             old-value (when is-update? (nth v i))
             new-delta (if is-update?
                        {:delta :update
                         :path [i]
                         :value x
                         :old-value old-value}
                        {:delta :add
                         :path [i]
                         :value x})]
         (DeltaableVector. (assoc v i x) (conj deltas new-delta) _meta)))

     (length [_] (count v))

     ;; IPersistentStack
     clojure.lang.IPersistentStack
     (peek [_]
       (peek v))

     (pop [this]
       "Remove last element from vector (records :remove delta)"
       (if (empty? v)
         (throw (IllegalStateException. "Can't pop empty vector"))
         (let [idx (dec (count v))
               old-value (nth v idx)
               new-delta {:delta :remove
                          :path [idx]
                          :old-value old-value}]
           (DeltaableVector. (pop v) (conj deltas new-delta) _meta))))

     ;; Indexed
     clojure.lang.Indexed
     (nth [this i]
       (nth v i))

     (nth [this i not-found]
       (if (< i (count v))
         (.nth this i)
         not-found))

     ;; ILookup
     clojure.lang.ILookup
     (valAt [this k]
       (when (and (integer? k) (>= k 0) (< k (count v)))
         (.nth this k)))
     (valAt [this k not-found]
       (if (and (integer? k) (>= k 0) (< k (count v)))
         (.nth this k)
         not-found))

     ;; Seqable
     clojure.lang.Seqable
     (seq [_] (seq v))

     ;; Associative
     clojure.lang.Associative
     (containsKey [this k]
       (and (integer? k) (>= k 0) (< k (count v))))
     (entryAt [this k]
       (when (.containsKey this k)
         (clojure.lang.MapEntry. k (.nth this k))))
     (assoc [this k x] (.assocN this k x))

     ;; IObj
     clojure.lang.IObj
     (meta [_] _meta)
     (withMeta [this new-meta]
       (DeltaableVector. v deltas new-meta))

     ;; IDeref - convenience for unwrapping
     clojure.lang.IDeref
     (deref [_]
       "Deref returns the underlying vector"
       v)

     ;; Java Object
     Object
     (toString [_] (str v))
     (hashCode [_] (.hashCode v))
     (equals [this other]
       "DeltaableVector equals other DeltaableVector if both value and deltas match.
        Use (= plain (->plain deltaable)) for plain collection comparison."
       (or (identical? this other)
           (and (instance? DeltaableVector other)
                (= v (.-v other))
                (= deltas (.-deltas other))))))

   :cljs
   (deftype DeltaableVector [v deltas _meta]
     ;; NO path field - always top-level
     ;; NO nested wrapping - inner values are plain

     PDeltaable
     (get-deltas [_]
       "Returns sequence of deltas from this operation"
       deltas)
     (deltaable? [_]
       "DeltaableVector is a deltaable collection"
       true)

     ICollection
     (-conj [this x]
       "Add element to end of vector (records top-level delta only)"
       (let [new-delta {:delta :add
                       :path [(count v)]
                       :value x}
             new-deltas (conj deltas new-delta)]
         (DeltaableVector. (conj v x) new-deltas _meta)))

     IEmptyableCollection
     (-empty [_]
       "Return empty deltaable vector"
       (DeltaableVector. [] [] _meta))

     IVector
     (-assoc-n [this i x]
       "Update element at index i or add new element (records top-level delta only)"
       (let [is-update? (< i (count v))
             old-value (when is-update? (nth v i))
             new-delta (if is-update?
                        {:delta :update
                         :path [i]
                         :value x
                         :old-value old-value}
                        {:delta :add
                         :path [i]
                         :value x})]
         (DeltaableVector. (assoc v i x) (conj deltas new-delta) _meta)))

     IStack
     (-peek [_]
       (peek v))

     (-pop [_]
       "Remove last element from vector (records :remove delta)"
       (if (empty? v)
         (throw (js/Error. "Can't pop empty vector"))
         (let [idx (dec (count v))
               old-value (nth v idx)
               new-delta {:delta :remove
                          :path [idx]
                          :old-value old-value}]
           (DeltaableVector. (pop v) (conj deltas new-delta) _meta))))

     IIndexed
     (-nth [_ i]
       (nth v i))

     (-nth [_ i not-found]
       (if (< i (count v))
         (nth v i)
         not-found))

     ILookup
     (-lookup [this k]
       (when (and (integer? k) (>= k 0) (< k (count v)))
         (-nth this k)))
     (-lookup [this k not-found]
       (if (and (integer? k) (>= k 0) (< k (count v)))
         (-nth this k)
         not-found))

     ISeqable
     (-seq [_] (seq v))

     IAssociative
     (-contains-key? [this k]
       (and (integer? k) (>= k 0) (< k (count v))))
     (-assoc [this k x] (-assoc-n this k x))

     IMeta
     (-meta [_] _meta)

     IWithMeta
     (-with-meta [this new-meta]
       (DeltaableVector. v deltas new-meta))

     IDeref
     (-deref [_]
       "Deref returns the underlying vector"
       v)

     ICounted
     (-count [_] (count v))

     IHash
     (-hash [_] (hash v))

     IEquiv
     (-equiv [this other]
       (or (identical? this other)
           (and (vector? other)
                (let [other-v (if (instance? DeltaableVector other)
                               (.-v other)
                               other)]
                  (= v other-v)))))))

(defn deltaable-vector
  "Create a DeltaableVector with initial values (NO deep wrapping).

   Values are stored as-is without wrapping nested collections.
   Only top-level operations are tracked as deltas.

   Example:
     (deltaable-vector [1 2 3])
     (deltaable-vector [{:a 1} {:b 2}])  ; Maps inside are NOT wrapped"
  [coll]
  (DeltaableVector. (vec coll) [] nil))

(defn remove-at
  "Remove element at index from a DeltaableVector, recording a :remove delta.

   Returns a new DeltaableVector with the element removed and delta tracked.
   This is the proper way to remove elements from vectors (not just pop).

   Example:
     (remove-at dv 2)  ; Remove element at index 2"
  [dv idx]
  (let [v (.-v dv)
        deltas (.-deltas dv)
        meta-val (.-_meta dv)]
    (if (and (>= idx 0) (< idx (count v)))
      (let [old-value (nth v idx)
            new-v (into (subvec v 0 idx) (subvec v (inc idx)))
            new-delta {:delta :remove
                       :path [idx]
                       :old-value old-value}]
        (DeltaableVector. new-v (conj deltas new-delta) meta-val))
      (throw (#?(:clj IllegalArgumentException. :cljs js/Error.)
              (str "Index out of bounds: " idx))))))

(defn insert-at
  "Insert element at index in a DeltaableVector, recording an :add delta.

   Returns a new DeltaableVector with the element inserted and delta tracked.
   Elements at and after the index are shifted right.

   Args:
     dv - DeltaableVector to modify
     idx - Index at which to insert (0 to count inclusive)
     value - Element to insert

   Example:
     (insert-at dv 2 :new)  ; Insert :new at index 2
     ; [a b c] -> [a b :new c]

   Delta format:
     {:delta :add
      :path [idx]
      :value element}"
  [dv idx value]
  (let [v (.-v dv)
        deltas (.-deltas dv)
        meta-val (.-_meta dv)
        n (count v)]
    (if (and (>= idx 0) (<= idx n))  ; idx can be 0 to n (append at end)
      (let [new-v (into (conj (subvec v 0 idx) value)
                        (subvec v idx))
            new-delta {:delta :add
                       :path [idx]
                       :value value}]
        (DeltaableVector. new-v (conj deltas new-delta) meta-val))
      (throw (#?(:clj IllegalArgumentException. :cljs js/Error.)
              (str "Index out of bounds: " idx " (count=" n ")"))))))

(defn move-to
  "Move element from one index to another in a DeltaableVector, recording a :move delta.

   Returns a new DeltaableVector with the element moved and delta tracked.
   The :move delta enables efficient DOM reordering without remove+add.

   Args:
     dv - DeltaableVector to modify
     from-idx - Current index of the element to move
     to-idx - Target index (after removal, before insertion)

   The to-idx is interpreted as the position in the resulting vector,
   accounting for the removal of the element at from-idx.

   Example:
     (move-to dv 0 2)  ; Move first element to position 2
     ; [a b c d] -> [b c a d]  (a moves from 0 to 2)

   Delta format:
     {:delta :move
      :from-path [from-idx]
      :to-path [to-idx]
      :value element}"
  [dv from-idx to-idx]
  (let [v (.-v dv)
        deltas (.-deltas dv)
        meta-val (.-_meta dv)
        n (count v)]
    (if (and (>= from-idx 0) (< from-idx n)
             (>= to-idx 0) (<= to-idx (dec n)))  ; to-idx can be at most n-1 (last position)
      (let [element (nth v from-idx)
            ;; Remove from original position
            without-elem (into (subvec v 0 from-idx) (subvec v (inc from-idx)))
            ;; Insert at new position
            new-v (into (conj (subvec without-elem 0 to-idx) element)
                        (subvec without-elem to-idx))
            new-delta {:delta :move
                       :from-path [from-idx]
                       :to-path [to-idx]
                       :value element}]
        (DeltaableVector. new-v (conj deltas new-delta) meta-val))
      (throw (#?(:clj IllegalArgumentException. :cljs js/Error.)
              (str "Index out of bounds: from=" from-idx " to=" to-idx " count=" n))))))

(defn filter-vec
  "Filter a DeltaableVector, recording :remove deltas for filtered-out elements.

   Returns a new DeltaableVector with only items matching pred.
   Each removed item generates a :remove delta.

   Example:
     (filter-vec #(not (:done %)) todos)  ; Remove completed todos"
  [pred dv]
  (let [v (.-v dv)
        deltas (.-deltas dv)
        meta-val (.-_meta dv)
        ;; Collect indices to remove (in reverse order to maintain correct indices)
        remove-indices (keep-indexed #(when (not (pred %2)) %1) v)
        ;; Build remove deltas
        remove-deltas (mapv (fn [idx]
                              {:delta :remove
                               :path [idx]
                               :old-value (nth v idx)})
                            remove-indices)
        ;; Filter the vector
        new-v (vec (clojure.core/filter pred v))]
    (DeltaableVector. new-v (into deltas remove-deltas) meta-val)))

(defn find-index
  "Find index of first item matching predicate in a collection.

   Returns the index (0-based) or nil if not found.
   Works with any indexed collection (vectors, DeltaableVector).

   Example:
     (find-index #(= (:id %) 42) todos)  ; => 3 or nil"
  [pred coll]
  (first (keep-indexed #(when (pred %2) %1) coll)))

(defn update-first-where
  "Update first item matching pred in a DeltaableVector.

   Applies (f item & args) to the first item where (pred item) is truthy.
   Records an :update delta for the changed item.
   Returns unchanged vector if no match found.

   This preserves DeltaableVector and generates proper deltas, unlike mapv.

   Example:
     ;; Toggle done status for item with id 42
     (update-first-where todos #(= (:id %) 42) update :done not)

     ;; Set content of block
     (update-first-where blocks #(= (:id %) block-id) assoc :content \"new\")"
  [dv pred f & args]
  (if-let [idx (find-index pred dv)]
    (let [old-value (nth dv idx)
          new-value (apply f old-value args)]
      (assoc dv idx new-value))
    dv))

(defn update-by-key
  "Update item in DeltaableVector where (key-fn item) equals target-key.

   Convenience wrapper around update-first-where for common key-based lookups.
   Records an :update delta for the changed item.
   Returns unchanged vector if no match found.

   Example:
     ;; Update block with id 42
     (update-by-key blocks :id 42 assoc :content \"new\")

     ;; Toggle todo with specific id
     (update-by-key todos :id todo-id update :done not)"
  [dv key-fn target-key f & args]
  (apply update-first-where dv #(= (key-fn %) target-key) f args))

;; =============================================================================
;; DeltaableMap - Map with delta tracking
;; =============================================================================

#?(:clj
   (deftype DeltaableMap [m deltas _meta]
     ;; NO path field - always top-level
     ;; NO nested wrapping - inner values are plain

     PDeltaable
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

     PDeltaable
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

;; =============================================================================
;; DeltaableSet - Set with delta tracking
;; =============================================================================

#?(:clj
   (deftype DeltaableSet [s deltas _meta]
     ;; NO nested wrapping - inner values are plain

     PDeltaable
     (get-deltas [_]
       "Returns sequence of deltas from this operation"
       deltas)
     (deltaable? [_]
       "DeltaableSet is a deltaable collection"
       true)

     clojure.lang.IPersistentCollection
     (cons [this x]
       "Add element to set (records top-level delta only)"
       (if (contains? s x)
         this
         (let [new-delta {:delta :add
                         :path [x]
                         :value x}]
           (DeltaableSet. (conj s x) (conj deltas new-delta) _meta))))

     (empty [_]
       "Return empty deltaable set"
       (DeltaableSet. #{} [] _meta))

     (equiv [this other]
       "DeltaableSet only equals other DeltaableSet with same value + deltas"
       (or (identical? this other)
           (and (instance? DeltaableSet other)
                (= s (.-s other))
                (= deltas (.-deltas other)))))

     ;; IPersistentSet
     clojure.lang.IPersistentSet
     (disjoin [this x]
       "Remove element from set (records top-level delta only)"
       (if (contains? s x)
         (let [new-delta {:delta :remove
                         :path [x]
                         :old-value x}]
           (DeltaableSet. (disj s x) (conj deltas new-delta) _meta))
         this))

     (contains [this x]
       (contains? s x))

     (get [this x]
       (get s x))

     ;; Seqable
     clojure.lang.Seqable
     (seq [_] (seq s))

     ;; Counted
     clojure.lang.Counted
     (count [_] (count s))

     ;; IObj
     clojure.lang.IObj
     (meta [_] _meta)
     (withMeta [this new-meta]
       (DeltaableSet. s deltas new-meta))

     ;; IDeref - convenience for unwrapping
     clojure.lang.IDeref
     (deref [_]
       "Unwrap to plain set"
       s)

     ;; IFn - enable (set val) syntax
     clojure.lang.IFn
     (invoke [this x]
       (get s x))

     ;; Object
     Object
     (toString [_]
       (str s))
     (hashCode [_]
       (.hashCode s))
     (equals [this other]
       "DeltaableSet equals other DeltaableSet if both value and deltas match.
        Use (= plain (->plain deltaable)) for plain collection comparison."
       (or (identical? this other)
           (and (instance? DeltaableSet other)
                (= s (.-s other))
                (= deltas (.-deltas other))))))

   :cljs
   (deftype DeltaableSet [s deltas _meta]
     ;; NO nested wrapping - inner values are plain

     PDeltaable
     (get-deltas [_]
       deltas)
     (deltaable? [_]
       "DeltaableSet is a deltaable collection"
       true)

     ICollection
     (-conj [this x]
       "Add element to set (records top-level delta only)"
       (if (contains? s x)
         this
         (let [new-delta {:delta :add
                         :path [x]
                         :value x}]
           (DeltaableSet. (conj s x) (conj deltas new-delta) _meta))))

     IEmptyableCollection
     (-empty [_]
       (DeltaableSet. #{} [] _meta))

     IEquiv
     (-equiv [this other]
       (or (identical? this other)
           (and (set? other)
                (= (count s) (count other))
                (let [other-s (if (instance? DeltaableSet other)
                                (.-s other)
                                other)]
                  (= s other-s)))))

     ISet
     (-disjoin [this x]
       "Remove element from set (records top-level delta only)"
       (if (contains? s x)
         (let [new-delta {:delta :remove
                         :path [x]
                         :old-value x}]
           (DeltaableSet. (disj s x) (conj deltas new-delta) _meta))
         this))

     ILookup
     (-lookup [this x]
       (get s x))
     (-lookup [this x not-found]
       (get s x not-found))

     ISeqable
     (-seq [_] (seq s))

     ICounted
     (-count [_] (count s))

     IMeta
     (-meta [_] _meta)

     IWithMeta
     (-with-meta [this new-meta]
       (DeltaableSet. s deltas new-meta))

     IDeref
     (-deref [_] s)

     IFn
     (-invoke [this x]
       (get s x))

     Object
     (toString [_]
       (str s))))

(defn deltaable-set
  "Create a DeltaableSet that tracks all conj/disj operations as deltas (NO deep wrapping).

   Values are stored as-is without wrapping nested collections.
   Only top-level element operations are tracked as deltas.

   Example:
     (deltaable-set #{1 2 3})
     (deltaable-set #{{:name \"Alice\"} {:name \"Bob\"}})  ; Nested maps NOT wrapped"
  [coll]
  (DeltaableSet. (into #{} coll) [] nil))

;; =============================================================================
;; Print methods - avoid multimethod dispatch ambiguity
;; =============================================================================

#?(:clj
   (do
     (defmethod print-method org.replikativ.spindel.incremental.deltaable.DeltaableVector [dv ^java.io.Writer w]
       (.write w (str (.-v dv))))
     (defmethod print-method org.replikativ.spindel.incremental.deltaable.DeltaableMap [dm ^java.io.Writer w]
       (.write w (str (.-m dm))))
     (defmethod print-method org.replikativ.spindel.incremental.deltaable.DeltaableSet [ds ^java.io.Writer w]
       (.write w (str (.-s ds))))))

;; =============================================================================
;; wrap-nested - Recursive wrapping of nested collections
;; =============================================================================

;; Extend IWrapDeltaable for all types

(extend-protocol PWrapDeltaable
  ;; Deltaable collections return themselves unchanged
  DeltaableVector
  (wrap-deltaable [x] x)

  DeltaableMap
  (wrap-deltaable [x] x)

  DeltaableSet
  (wrap-deltaable [x] x)

  #?@(:clj
      [;; Records: pass through unchanged (they may implement custom protocols)
       ;; IMPORTANT: This must come before IPersistentMap since records implement it
       clojure.lang.IRecord
       (wrap-deltaable [x] x)

       ;; Plain vectors: wrap shallowly (NO nested wrapping)
       clojure.lang.IPersistentVector
       (wrap-deltaable [x]
         (DeltaableVector. x [] nil))

       ;; Plain maps: wrap shallowly (NO nested wrapping)
       ;; Note: Records don't match this due to IRecord extension above
       clojure.lang.IPersistentMap
       (wrap-deltaable [x]
         (DeltaableMap. x [] nil))

       ;; Plain sets: wrap shallowly (NO nested wrapping)
       clojure.lang.IPersistentSet
       (wrap-deltaable [x]
         (DeltaableSet. x [] nil))]

      :cljs
      [;; Plain vectors: wrap shallowly (NO nested wrapping)
       cljs.core/PersistentVector
       (wrap-deltaable [x]
         (DeltaableVector. x [] nil))

       ;; Plain maps: wrap shallowly (NO nested wrapping)
       cljs.core/PersistentArrayMap
       (wrap-deltaable [x]
         (DeltaableMap. x [] nil))

       cljs.core/PersistentHashMap
       (wrap-deltaable [x]
         (DeltaableMap. x [] nil))

       ;; Plain sets: wrap shallowly (NO nested wrapping)
       cljs.core/PersistentHashSet
       (wrap-deltaable [x]
         (DeltaableSet. x [] nil))])

  ;; Default: return unchanged (scalars, records, etc.)
  #?(:clj Object :cljs default)
  (wrap-deltaable [x] x)

  nil
  (wrap-deltaable [_] nil))

(defn wrap-nested
  "DEPRECATED: Shallow wrapping doesn't need wrap-nested anymore.

   This function is kept for backwards compatibility but now just
   calls wrap-deltaable without path parameter.

   With shallow wrapping architecture, nested collections are NOT wrapped.
   Only use this if you explicitly want to wrap a value as top-level deltaable."
  [x path]
  (wrap-deltaable x))

(defn clear-deltas
  "Return a copy of deltaable collection with deltas cleared (O(1) operation).

   This creates a new deltaable with the same inner value but empty delta vector.
   Since we use shallow wrapping, this is O(1) - just creates new wrapper.
   Used by the runtime after propagating deltas to observers."
  [deltaable]
  (cond
    (instance? #?(:clj DeltaableVector :cljs DeltaableVector) deltaable)
    (DeltaableVector. (.-v deltaable) [] (.-_meta deltaable))

    (instance? #?(:clj DeltaableMap :cljs DeltaableMap) deltaable)
    (DeltaableMap. (.-m deltaable) [] (.-_meta deltaable))

    (instance? #?(:clj DeltaableSet :cljs DeltaableSet) deltaable)
    (DeltaableSet. (.-s deltaable) [] (.-_meta deltaable))

    :else
    deltaable))

;; =============================================================================
;; IUnwrapDeltaable Protocol Implementations
;; =============================================================================

;; Deltaable collections unwrap recursively
(extend-protocol PUnwrapDeltaable
  #?(:clj DeltaableVector :cljs DeltaableVector)
  (unwrap-deltaable [x]
    (mapv unwrap-deltaable #?(:clj (.deref x) :cljs (-deref x))))

  #?(:clj DeltaableMap :cljs DeltaableMap)
  (unwrap-deltaable [x]
    (into {} (clojure.core/map (fn [[k v]] [k (unwrap-deltaable v)]))
          #?(:clj (.deref x) :cljs (-deref x))))

  #?(:clj DeltaableSet :cljs DeltaableSet)
  (unwrap-deltaable [x]
    (into #{} (clojure.core/map unwrap-deltaable)
          #?(:clj (.deref x) :cljs (-deref x))))

  ;; Default: plain values pass through unchanged
  #?(:clj Object :cljs default)
  (unwrap-deltaable [x] x)

  ;; Handle nil explicitly
  nil
  (unwrap-deltaable [_] nil))

;; =============================================================================
;; Delta Transducers - Transform delta streams
;; =============================================================================

(defn map
  "Delta transducer that transforms values in deltas.

   Applies f to:
   - :add delta: transforms :value
   - :update delta: transforms both :value and :old-value
   - :remove delta: passes through unchanged (no value to transform)

   Works with standard transducer composition:
     (transduce (comp (d/map inc) (d/filter even?)) ...)

   Example:
     (d/map inc) transforms:
     {:delta :add :path [0] :value 1}
     => {:delta :add :path [0] :value 2}"
  [f]
  (fn [rf]
    (fn
      ([] (rf))
      ([result] (rf result))
      ([result delta]
       (rf result
           (case (:delta delta)
             :add (update delta :value f)
             :update (-> delta
                        (update :value f)
                        (update :old-value f))
             :remove delta))))))

(defn filter
  "Delta transducer that filters deltas with enter/exit semantics.

   Uses :old-value to determine if items entered or exited the filter:
   - Old passed, new passed: :update (stay in)
   - Old didn't pass, new passed: :add (entered)
   - Old passed, new didn't pass: :remove (exited)
   - Neither passed: filter out entirely

   For :add deltas (no old-value): treat as entering if pred passes
   For :remove deltas: treat as exiting if value would have passed

   Example with (d/filter even?):
     {:delta :update :value 4 :old-value 3}
     => {:delta :add :value 4}  ; entered the filter

     {:delta :update :value 3 :old-value 4}
     => {:delta :remove :value 4}  ; exited the filter

     {:delta :update :value 6 :old-value 4}
     => {:delta :update :value 6 :old-value 4}  ; stayed in"
  [pred]
  (fn [rf]
    (fn
      ([] (rf))
      ([result] (rf result))
      ([result delta]
       (case (:delta delta)
         :add
         (if (pred (:value delta))
           (rf result delta)
           result)

         :remove
         ;; For remove, we don't have access to the value
         ;; Pass through - caller needs to handle
         (rf result delta)

         :update
         (let [old-pass? (pred (:old-value delta))
               new-pass? (pred (:value delta))]
           (cond
             ;; Both pass: update (stay in filter)
             (and old-pass? new-pass?)
             (rf result delta)

             ;; Entered filter: change to :add
             (and (not old-pass?) new-pass?)
             (rf result (-> delta
                           (assoc :delta :add)
                           (dissoc :old-value)))

             ;; Exited filter: change to :remove
             (and old-pass? (not new-pass?))
             (rf result (-> delta
                           (assoc :delta :remove)
                           (dissoc :old-value)))

             ;; Neither pass: filter out
             :else
             result)))))))

(defn remove
  "Delta transducer that removes deltas - inverse of filter.

   Equivalent to (d/filter (complement pred))

   Example:
     (d/remove odd?) removes odd numbers from the delta stream"
  [pred]
  (filter (complement pred)))

(defn keep
  "Delta transducer that transforms and filters in one step.

   Applies f to values, keeps only non-nil results.
   Similar semantics to filter but with transformation.

   Example:
     (d/keep #(when (even? %) (* 2 %)))
     Keeps only even numbers and doubles them"
  [f]
  (fn [rf]
    (fn
      ([] (rf))
      ([result] (rf result))
      ([result delta]
       (case (:delta delta)
         :add
         (let [new-val (f (:value delta))]
           (if (some? new-val)
             (rf result (assoc delta :value new-val))
             result))

         :update
         (let [old-val (f (:old-value delta))
               new-val (f (:value delta))
               old-some? (some? old-val)
               new-some? (some? new-val)]
           (cond
             ;; Both some: update
             (and old-some? new-some?)
             (rf result (-> delta
                           (assoc :value new-val)
                           (assoc :old-value old-val)))

             ;; Entered: change to :add
             (and (not old-some?) new-some?)
             (rf result (-> delta
                           (assoc :delta :add)
                           (assoc :value new-val)
                           (dissoc :old-value)))

             ;; Exited: change to :remove
             (and old-some? (not new-some?))
             (rf result (-> delta
                           (assoc :delta :remove)
                           (dissoc :old-value)))

             ;; Neither: filter out
             :else
             result))

         :remove
         (rf result delta))))))

;; =============================================================================
;; Delta Application - Apply deltas to collections
;; =============================================================================

(defn apply-delta
  "Reducing function that applies a delta to a collection.

   Supports:
   - Plain collections (vectors, maps, sets)
   - DeltaableVector/Map/Set (preserves delta tracking)
   - Nested paths (uses assoc-in/update-in semantics)

   Delta formats:
   {:delta :add/:remove/:update
    :path [0] or [:users 0 :name]
    :value new-value
    :old-value old-value}  ; For :update/:remove

   {:delta :move
    :from-path [from-idx]
    :to-path [to-idx]
    :value element}  ; For vector reordering

   Example:
     (reduce d/apply-delta [] deltas)
     (reduce d/apply-delta (d/deltaable-vector []) deltas)"
  ([] [])  ; 0-arity: init
  ([coll] coll)  ; 1-arity: completion (identity)
  ([coll delta]  ; 2-arity: step
  (let [path (:path delta)
        value (:value delta)]
    (case (:delta delta)
      :add
      (if (empty? path)
        ;; Top-level add (conj)
        (conj coll value)
        ;; Nested add
        (if (= 1 (count path))
          ;; Single level
          (let [k (first path)]
            (if (vector? coll)
              ;; Vector: always add at end (conj), ignore path index
              ;; (path is just metadata from source, not target position)
              (conj coll value)
              ;; Map/Set: use key from path
              (assoc coll k value)))
          ;; Multi-level: use assoc-in
          (assoc-in coll path value)))

      :update
      (if (empty? path)
        ;; Top-level update (replace entire collection)
        value
        ;; Nested update
        (if (= 1 (count path))
          ;; Single level: use assoc
          (assoc coll (first path) value)
          ;; Multi-level: use assoc-in
          (assoc-in coll path value)))

      :remove
      (if (empty? path)
        ;; Top-level remove (clear collection)
        (empty coll)
        ;; Nested remove
        (if (= 1 (count path))
          ;; Single level: remove by index/key
          (cond
            (vector? coll)
            ;; Vector: remove by creating new vector without item
            (vec (concat (subvec coll 0 (first path))
                         (subvec coll (inc (first path)))))

            (map? coll)
            (dissoc coll (first path))

            (set? coll)
            (disj coll (first path))

            :else coll)
          ;; Multi-level: use update-in with recursive remove
          (update-in coll (butlast path)
                     (fn [parent]
                       (let [k (last path)]
                         (cond
                           (vector? parent)
                           (vec (concat (subvec parent 0 k)
                                        (subvec parent (inc k))))
                           (map? parent) (dissoc parent k)
                           (set? parent) (disj parent k)
                           :else parent))))))

      :move
      ;; Move element within a vector from from-path to to-path
      (let [from-idx (first (:from-path delta))
            to-idx (first (:to-path delta))]
        (if (vector? coll)
          (let [element (nth coll from-idx)
                ;; Remove from original position
                without-elem (into (subvec coll 0 from-idx) (subvec coll (inc from-idx)))
                ;; Insert at new position
                result (into (conj (subvec without-elem 0 to-idx) element)
                             (subvec without-elem to-idx))]
            result)
          ;; Non-vector: ignore move (doesn't make sense for maps/sets)
          coll))

      ;; Unknown delta type - return unchanged
      coll))))  ; Close 2-arity body

(defn transduce
  "Transduce deltas through xf and apply to initial collection.

   Like clojure.core/transduce but specialized for delta streams:
   - xf: delta transducer (d/map, d/filter, etc.)
   - init: initial collection (plain or deltaable)
   - deltas: sequence of delta maps

   Example:
     ;; Process only completed todos
     (d/transduce (d/filter :completed) [] deltas)

     ;; Transform and filter
     (d/transduce (comp (d/map inc) (d/filter even?))
                  []
                  deltas)"
  ([xf init deltas]
   (clojure.core/transduce xf apply-delta init deltas))
  ([xf init]
   (fn [deltas]
     (transduce xf init deltas))))

(defn merge-deltas
  "Merge multiple delta sequences into one.

   Concatenates delta sequences in order. Useful for combining
   deltas from multiple sources or time periods.

   Example:
     (d/merge-deltas deltas1 deltas2 deltas3)"
  [& delta-seqs]
  (apply concat delta-seqs))

(defn compact-deltas
  "Compact a sequence of deltas by removing redundant operations.

   Optimizations:
   - Multiple updates to same path: keep only last
   - Add followed by remove: cancel out
   - Remove followed by add: convert to update

   Note: Preserves order within non-redundant operations.

   Example:
     [{:delta :add :path [0] :value 1}
      {:delta :update :path [0] :value 2}
      {:delta :update :path [0] :value 3}]
     =>
     [{:delta :add :path [0] :value 3}]"
  [deltas]
  (let [;; Group by path
        by-path (group-by :path deltas)]
    ;; For each path, compact the operations
    (vec
     (mapcat
      (fn [[path ops]]
        (loop [result []
               [op & rest] ops]
          (if-not op
            result
            (let [last-op (peek result)]
              (cond
                ;; First operation for this path
                (nil? last-op)
                (recur (conj result op) rest)

                ;; add + remove = cancel
                (and (= :add (:delta last-op))
                     (= :remove (:delta op)))
                (recur (pop result) rest)

                ;; remove + add = update
                (and (= :remove (:delta last-op))
                     (= :add (:delta op)))
                (recur (conj (pop result)
                             (assoc op :delta :update
                                    :old-value nil))
                       rest)

                ;; Multiple updates = keep last
                (and (= :update (:delta last-op))
                     (= :update (:delta op)))
                (recur (conj (pop result)
                             (assoc op :old-value (:old-value last-op)))
                       rest)

                ;; add + update = add with new value
                (and (= :add (:delta last-op))
                     (= :update (:delta op)))
                (recur (conj (pop result)
                             (assoc last-op :value (:value op)))
                       rest)

                ;; update + remove = remove
                (and (= :update (:delta last-op))
                     (= :remove (:delta op)))
                (recur (conj (pop result) op) rest)

                ;; Otherwise keep both
                :else
                (recur (conj result op) rest))))))
      by-path))))
