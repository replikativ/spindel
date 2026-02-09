(ns org.replikativ.spindel.incremental.deltaable.set
  "DeltaableSet - set with top-level delta tracking.

   Tracks conj and disj operations as deltas.
   Inner values are stored as-is (no deep wrapping)."
  (:require [org.replikativ.spindel.incremental.deltaable.protocols :as proto]))

#?(:clj
   (deftype DeltaableSet [s deltas _meta]
     ;; NO nested wrapping - inner values are plain

     proto/PDeltaable
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

     proto/PDeltaable
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
