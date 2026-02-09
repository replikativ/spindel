(ns org.replikativ.spindel.incremental.deltaable.vector
  "DeltaableVector - vector with top-level delta tracking.

   Tracks conj, assoc, pop, and other top-level vector operations as deltas.
   Inner values are stored as-is (no deep wrapping)."
  (:require [org.replikativ.spindel.incremental.deltaable.protocols :as proto]))

#?(:clj
   (deftype DeltaableVector [v deltas _meta]
     ;; NO path field - always top-level
     ;; NO nested wrapping - inner values are plain

     proto/PDeltaable
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

     proto/PDeltaable
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
        new-v (vec (filter pred v))]
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
